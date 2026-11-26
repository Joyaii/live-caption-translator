"""实时字幕翻译 - 读取 Windows 实时辅助字幕，翻译成中文并显示悬浮窗。

数据源：LiveCaptions 的 CaptionsTextBlock（UI Automation）
翻译：  Bing（cn.bing.com，免费无配额）→ 失败降级 MyMemory
"""

import ctypes
import difflib
import hashlib
import json
import os
import queue
import re
import subprocess
import sys
import threading
import time
import tkinter as tk
import urllib.parse
import urllib.request
import winreg
import http.cookiejar

import uiautomation as auto

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36")

POLL_MS = 150          # 字幕轮询间隔
SETTLE_SEC = 0.75      # 最后一句要稳定这么久才认定说完
MAX_PAIRS = 4          # 窗口里保留几组
MIN_LEN = 8            # 太短的碎片不翻
SIM_RATIO = 0.72       # 相似度阈值，超过视为同一句
ALPHA_LEVELS = (0.95, 0.86, 0.75, 0.66, 0.55)   # 右键菜单循环切换
ALPHA = 0.75           # 默认不透明度
PAIR_TTL = 8.0         # 每条字幕在屏幕上停留多久
MIN_EMPTY_H = 28       # 没有字幕时的最小高度（窗口永不隐藏）
EVENT_NAME = "Local\\LiveCaptionTranslatorWakeup"   # 第二次启动用它唤醒已有实例
# PyInstaller onefile 模式下 __file__ 指向临时解压目录，
# 配置和日志必须落在 exe 旁边，否则每次重启都会丢
BASE_DIR = (os.path.dirname(sys.executable) if getattr(sys, "frozen", False)
            else os.path.dirname(os.path.abspath(__file__)))
LOG_FILE = os.path.join(BASE_DIR, "error.log")
SETTINGS_FILE = os.path.join(BASE_DIR, "settings.json")


def load_settings():
    try:
        with open(SETTINGS_FILE, encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, dict) else {}
    except Exception:
        return {}


def save_settings(data):
    try:
        with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
    except Exception:
        pass


def _ci(value, lo, hi, default):
    """转整数并夹到区间内，坏数据就退回默认值。"""
    try:
        return max(lo, min(hi, int(value)))
    except Exception:
        return default


def _cf(value, lo, hi, default):
    try:
        return max(lo, min(hi, float(value)))
    except Exception:
        return default


# Windows 实时辅助字幕支持的识别语言（22H2 起）
LANGUAGES = [
    ("en-US", "英语（美国）"),
    ("en-GB", "英语（英国）"),
    ("en-AU", "英语（澳大利亚）"),
    ("en-CA", "英语（加拿大）"),
    ("en-IN", "英语（印度）"),
    ("en-NZ", "英语（新西兰）"),
    ("zh-CN", "中文（简体）"),
    ("zh-TW", "中文（繁体）"),
    ("ja-JP", "日语"),
    ("ko-KR", "韩语"),
    ("fr-FR", "法语（法国）"),
    ("fr-CA", "法语（加拿大）"),
    ("de-DE", "德语"),
    ("it-IT", "意大利语"),
    ("es-ES", "西班牙语（西班牙）"),
    ("es-MX", "西班牙语（墨西哥）"),
    ("pt-BR", "葡萄牙语（巴西）"),
    ("pt-PT", "葡萄牙语（葡萄牙）"),
    ("da-DK", "丹麦语"),
]
LANG_NAMES = dict(LANGUAGES)

CAPTION_KEY = r"Software\Microsoft\LiveCaptions\UI"
# 识别语言决定翻译的源语言，改了要同步
_SRC = {"lang": "en"}

# 翻译引擎配置，跟着 settings.json 走
CFG = {"engine": "bing", "baidu_appid": "", "baidu_key": "", "baidu_apikey": ""}

# 程序内部用两位语言码，百度用的是另一套（日语 jp、韩语 kor、法语 fra…）
BAIDU_LANG = {"en": "en", "zh": "zh", "ja": "jp", "ko": "kor",
              "fr": "fra", "de": "de", "es": "spa", "it": "it",
              "pt": "pt", "da": "dan"}

BAIDU_ERR = {
    "52001": "请求超时，重试",
    "52002": "系统错误",
    "52003": "appid 或密钥不对，或未开通该服务",
    "54000": "参数错误",
    "54001": "签名错误（检查密钥）",
    "54003": "调用频率超限（免费版 QPS=1）",
    "54004": "账户余额不足",
    "54005": "长文本请求频繁",
    "58000": "IP 不在白名单（后台设置里关掉或加上本机 IP）",
    "58001": "语言方向不支持",
    "58002": "服务已关闭",
    "53001": "请求体格式错误",
}

# 大模型翻译的语境指令。不加的话 position 会翻成「姿势」、rotate 翻成「轮换」
BAIDU_REFERENCE = ("这是FPS射击游戏的队友语音，翻译成简洁口语化的中文。"
                   "注意：position 指位置/阵地（不是姿势），rotate 指转移/换点，"
                   "flank 指侧翼/绕后，callout 用游戏通用说法。")


class BaiduTranslator:
    """百度翻译。支持大模型翻译（llm）和传统机器翻译（nmt）。

    两条链路参数格式不一样：
    - 通用接口走 GET，salt 是字符串
    - 大模型接口走 POST JSON，salt 必须是数字（传字符串会报 53001）
    """

    GENERAL_URL = "https://fanyi-api.baidu.com/api/trans/vip/translate"
    LLM_URL = "https://fanyi-api.baidu.com/ait/api/aiTextTranslate"

    def __init__(self, appid, key, apikey=""):
        self.appid = (appid or "").strip()
        self.key = (key or "").strip()
        self.apikey = (apikey or "").strip()
        self.sess = None
        try:
            import requests
            self.sess = requests.Session()
        except Exception:
            self.sess = None
        self.cj = http.cookiejar.CookieJar()
        self.opener = urllib.request.build_opener(
            urllib.request.HTTPCookieProcessor(self.cj))
        self.opener.addheaders = [("User-Agent", UA)]

    @property
    def ready(self):
        # 大模型接口有 API Key 就够；通用接口只能用密钥算签名
        return bool(self.appid) and (bool(self.apikey) or bool(self.key))

    def _sign(self, text, salt):
        raw = self.appid + text + str(salt) + self.key
        return hashlib.md5(raw.encode("utf-8")).hexdigest()

    def translate(self, text, frm="en", to="zh", model="llm"):
        if not self.ready:
            raise RuntimeError("未配置百度 appid / 密钥")
        if model == "llm":
            return self._llm(text, frm, to)
        return self._general(text, frm, to)

    def _llm(self, text, frm, to):
        salt = int(time.time() * 1000)
        body = {
            "appid": self.appid,
            "q": text,
            "from": BAIDU_LANG.get(frm, frm),
            "to": to,
            "salt": salt,
            "model_type": "llm",
            "reference": BAIDU_REFERENCE,
        }
        headers = {"Content-Type": "application/json"}
        if self.apikey:
            # API Key 鉴权：不用算签名，百度推荐这种方式
            headers["Authorization"] = f"Bearer {self.apikey}"
        else:
            body["sign"] = self._sign(text, salt)

        if self.sess is not None:
            data = self.sess.post(self.LLM_URL, json=body, headers=headers,
                                  timeout=20).json()
        else:
            req = urllib.request.Request(
                self.LLM_URL, data=json.dumps(body).encode("utf-8"),
                headers=headers)
            raw = self.opener.open(req, timeout=20).read().decode("utf-8", "ignore")
            data = json.loads(raw)

        code = str(data.get("error_code", ""))
        if code in ("0", "52000", ""):
            # 实测大模型接口的 trans_result 在顶层，和通用接口一致；
            # 但文档示例里也有包在 data 下的情况，两处都兜一下
            tr = data.get("trans_result")
            if tr is None:
                d = data.get("data") or {}
                tr = d.get("trans_result") or d.get("result") or d.get("dst") or ""
            if isinstance(tr, list):
                return "".join(x.get("dst", "") for x in tr)
            return str(tr)
        msg = BAIDU_ERR.get(code) or data.get("error_msg") or code
        raise RuntimeError(f"百度大模型翻译失败：{msg}（{code}）")

    def _general(self, text, frm, to):
        salt = str(int(time.time() * 1000))
        params = {"q": text, "from": BAIDU_LANG.get(frm, frm), "to": to,
                  "appid": self.appid, "salt": salt,
                  "sign": self._sign(text, salt)}
        if self.sess is not None:
            data = self.sess.get(self.GENERAL_URL, params=params, timeout=10).json()
        else:
            qs = urllib.parse.urlencode(params)
            raw = self.opener.open(f"{self.GENERAL_URL}?{qs}", timeout=10)
            data = json.loads(raw.read().decode("utf-8", "ignore"))

        if "trans_result" in data:
            return "".join(i.get("dst", "") for i in data["trans_result"])
        code = str(data.get("error_code", ""))
        msg = BAIDU_ERR.get(code) or data.get("error_msg") or code
        raise RuntimeError(f"百度翻译失败：{msg}（{code}）")


def read_caption_lang():
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, CAPTION_KEY) as k:
            return winreg.QueryValueEx(k, "CaptionLanguage")[0]
    except Exception:
        return "en-US"


def write_caption_lang(code):
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, CAPTION_KEY, 0,
                            winreg.KEY_SET_VALUE) as k:
            winreg.SetValueEx(k, "CaptionLanguage", 0, winreg.REG_SZ, code)
        return True
    except Exception as exc:
        log_error(exc)
        return False


def log_error(exc):
    """异常记账。轮询绝不能因为一次异常就停掉，但也不能完全无声。"""
    try:
        if os.path.exists(LOG_FILE) and os.path.getsize(LOG_FILE) > 100_000:
            open(LOG_FILE, "w", encoding="utf-8").close()
        with open(LOG_FILE, "a", encoding="utf-8") as f:
            f.write(f"{time.strftime('%m-%d %H:%M:%S')} "
                    f"{type(exc).__name__}: {exc}\n")
    except Exception:
        pass


# ---------------------------------------------------------------- 翻译引擎
class BingTranslator:
    """Bing 网页接口。优先用 requests.Session 复用连接。

    实测 urllib 每次新建 TLS 连接约 1.27s，复用连接约 1.05s，
    省下的 200ms 全是握手开销。
    """

    def __init__(self):
        self.sess = None
        try:
            import requests
            self.sess = requests.Session()
            self.sess.headers.update({
                "User-Agent": UA,
                "Accept-Language": "zh-CN,zh;q=0.9",
                "Referer": "https://cn.bing.com/translator",
            })
        except Exception:
            self.sess = None

        self.cj = http.cookiejar.CookieJar()
        self.opener = urllib.request.build_opener(
            urllib.request.HTTPCookieProcessor(self.cj))
        self.opener.addheaders = [
            ("User-Agent", UA),
            ("Accept-Language", "zh-CN,zh;q=0.9"),
        ]
        self.ig = self.iid = self.key = self.token = None
        self.stamp = 0.0

    def _refresh(self):
        if self.sess is not None:
            html = self.sess.get("https://cn.bing.com/translator",
                                 timeout=12).text
        else:
            html = self.opener.open(
                "https://cn.bing.com/translator", timeout=12
            ).read().decode("utf-8", "ignore")
        self.ig = re.search(r'IG:"([^"]+)"', html).group(1)
        m = re.search(r'params_AbusePreventionHelper\s*=\s*\[(\d+),"([^"]+)"', html)
        self.key, self.token = m.group(1), m.group(2)
        iids = re.findall(r'data-iid="(translator\.\d+)"', html)
        self.iid = iids[-1] if iids else "translator.5028"
        self.stamp = time.time()

    def _post(self, text):
        payload = {"fromLang": _SRC["lang"], "to": "zh-Hans",
                   "text": text, "token": self.token, "key": self.key}
        params = {"isVertical": "1", "IG": self.ig, "IID": f"{self.iid}.1"}
        url = "https://cn.bing.com/ttranslatev3"

        if self.sess is not None:
            resp = self.sess.post(url, params=params, data=payload, timeout=12)
            return resp.json()[0]["translations"][0]["text"]

        qs = urllib.parse.urlencode(params)
        data = urllib.parse.urlencode(payload).encode("utf-8")
        req = urllib.request.Request(
            f"{url}?{qs}", data=data,
            headers={"Content-Type": "application/x-www-form-urlencoded",
                     "Referer": "https://cn.bing.com/translator"})
        raw = self.opener.open(req, timeout=12).read().decode("utf-8", "ignore")
        return json.loads(raw)[0]["translations"][0]["text"]

    def translate(self, text):
        if not self.token or time.time() - self.stamp > 3000:
            self._refresh()
        try:
            return self._post(text)
        except Exception:
            self._refresh()
            return self._post(text)

    def warmup(self):
        """启动时预取 token，省掉第一句的 0.46 秒。"""
        try:
            self._refresh()
        except Exception:
            pass


def mymemory(text):
    q = urllib.parse.quote(text)
    url = (f"https://api.mymemory.translated.net/get?q={q}"
           f"&langpair={_SRC['lang']}|zh-CN")
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    raw = urllib.request.urlopen(req, timeout=10).read().decode("utf-8")
    return json.loads(raw)["responseData"]["translatedText"]


ENGINE = BingTranslator()


_CACHE = {}
_CACHE_MAX = 512
_BAIDU = {"t": None}


def get_baidu():
    """配置变了就重建，避免每次翻译新建 session。"""
    t = _BAIDU["t"]
    if (t is None or t.appid != CFG["baidu_appid"]
            or t.key != CFG["baidu_key"]
            or t.apikey != CFG["baidu_apikey"]):
        t = BaiduTranslator(CFG["baidu_appid"], CFG["baidu_key"],
                            CFG["baidu_apikey"])
        _BAIDU["t"] = t
    return t


def translate(text):
    """带缓存的翻译。引擎可在 Bing / 百度之间切换，百度失败会自动退回 Bing。"""
    if _SRC["lang"] == "zh":          # 识别语言本来就是中文，不用翻
        return text

    key = f"{CFG['engine']}|{_SRC['lang']}|{text.strip().lower()}"
    hit = _CACHE.get(key)
    if hit is not None:
        return hit

    def remember(out):
        if len(_CACHE) >= _CACHE_MAX:
            _CACHE.pop(next(iter(_CACHE)))      # FIFO 淘汰
        _CACHE[key] = out
        return out

    if CFG["engine"].startswith("baidu"):
        bt = get_baidu()
        if bt.ready:
            model = "llm" if CFG["engine"] == "baidu_llm" else "nmt"
            try:
                out = bt.translate(text, _SRC["lang"], "zh", model).strip()
                if out:
                    return remember(out)
            except Exception as exc:
                log_error(exc)      # 失败就往下走 Bing，别让字幕空着

    for fn in (ENGINE.translate, mymemory):
        try:
            out = fn(text).strip()
            if out and out.lower() != text.lower():
                return remember(out)
        except Exception:
            continue
    return "（翻译失败）"


# ---------------------------------------------------------------- 字幕读取
def find_caption_window():
    try:
        w = auto.WindowControl(searchDepth=2, ClassName="LiveCaptionsDesktopWindow")
        if w.Exists(1):
            return w
    except Exception:
        pass
    for w in auto.GetRootControl().GetChildren():
        try:
            if w.ClassName == "LiveCaptionsDesktopWindow":
                return w
        except Exception:
            pass
    return None


def launch_live_captions():
    """拉起 Windows 实时字幕。

    实测直接运行 LiveCaptions.exe 就能起，比模拟 Win+Ctrl+L 可靠
    （模拟按键对实时字幕无效，会被系统忽略）。
    """
    try:
        # 不能用 DETACHED_PROCESS：实时字幕需要交互式桌面上下文，会直接退出
        subprocess.Popen([r"C:\Windows\System32\LiveCaptions.exe"])
        return True
    except Exception:
        return False


def close_live_captions():
    """关掉 Windows 实时字幕，失败就重试，别留个窗口在屏幕上。"""
    for _ in range(3):
        try:
            subprocess.run(
                ["taskkill", "/F", "/IM", "LiveCaptions.exe"],
                capture_output=True, creationflags=0x08000000)   # CREATE_NO_WINDOW
        except Exception:
            pass
        time.sleep(0.3)
        if find_caption_window() is None:
            return


def read_text(win, cache):
    """返回 (字幕全文, 新的 cache 控件)。"""
    try:
        if cache[0] is not None:
            return cache[0].Name or "", cache
    except Exception:
        cache[0] = None
    try:
        block = win.TextControl(AutomationId="CaptionsTextBlock")
        if block.Exists(0.5):
            cache[0] = block
            return block.Name or "", cache
    except Exception:
        pass
    return "", cache


def similar(a, b):
    """LiveCaptions 会反复修订同一句，用相似度挡住同一句的不同版本。"""
    return difflib.SequenceMatcher(None, a.lower(), b.lower()).ratio() > SIM_RATIO


def redundant(s, recent):
    """挡住「把前面翻过的几句拼在一起又输出一遍」的情况。

    这种句子与任何单句的相似度都不高，但会完整包含它们，
    所以用子串包含来判断，比相似度可靠。
    """
    low = s.lower()
    for d in recent:
        stem = d.rstrip(".!? ").lower()
        if len(stem) >= 12 and stem in low:
            return True
    return False


class _RECT(ctypes.Structure):
    _fields_ = [("left", ctypes.c_long), ("top", ctypes.c_long),
                ("right", ctypes.c_long), ("bottom", ctypes.c_long)]


class CaptionHider:
    """把实时字幕窗口挪到屏幕外。

    UIA 读取不依赖窗口可见性，实测最小化 / 移出屏幕 / 缩成 1x1 都能正常读，
    所以可以让英文字幕窗消失，只留中文悬浮窗。

    窗口原位置会存到 .caption_pos.json：万一进程被强杀没来得及恢复，
    下次启动还能把窗口拉回屏内。
    """

    SWP_FLAGS = 0x0004 | 0x0010          # SWP_NOZORDER | SWP_NOACTIVATE
    OFFSCREEN = -32000
    POS_FILE = os.path.join(
        BASE_DIR, ".caption_pos.json")

    def __init__(self):
        self.user32 = ctypes.windll.user32
        self.hwnd = None
        self.orig = None
        self.enabled = True

    def _rect(self, hwnd):
        r = _RECT()
        self.user32.GetWindowRect(hwnd, ctypes.byref(r))
        return (r.left, r.top, r.right - r.left, r.bottom - r.top)

    def _save(self, pos):
        try:
            with open(self.POS_FILE, "w", encoding="utf-8") as f:
                json.dump(list(pos), f)
        except Exception:
            pass

    def _load(self):
        try:
            with open(self.POS_FILE, encoding="utf-8") as f:
                d = json.load(f)
            return tuple(d) if len(d) == 4 else None
        except Exception:
            return None

    def hide(self, win):
        hwnd = getattr(win, "NativeWindowHandle", None)
        if not hwnd:
            return
        self.hwnd = hwnd
        cur = self._rect(hwnd)
        if cur[0] < -10000:
            # 上次没恢复干净，用存档位置，别再记一次屏幕外坐标
            sh = self.user32.GetSystemMetrics(1)
            self.orig = self._load() or (60, sh - 480, cur[2], cur[3])
        else:
            self.orig = cur
            self._save(self.orig)
        self.user32.SetWindowPos(
            hwnd, 0, self.OFFSCREEN, self.OFFSCREEN,
            self.orig[2], self.orig[3], self.SWP_FLAGS)

    def is_hidden(self, win):
        hwnd = getattr(win, "NativeWindowHandle", None)
        if not hwnd:
            return False
        return self._rect(hwnd)[0] < -10000

    def restore(self):
        if self.hwnd and self.orig:
            self.user32.SetWindowPos(
                self.hwnd, 0, self.orig[0], self.orig[1],
                self.orig[2], self.orig[3], self.SWP_FLAGS)


SENT_RE = re.compile(r"[^.!?]+[.!?]+")


def split_complete(text):
    """把整屏字幕压平后按标点切句，只返回已经说完的。

    LiveCaptions 会把连续多句塞进同一行，句号只是行内分隔，
    所以不能按行处理，只能按标点。
    """
    flat = " ".join(x.strip() for x in text.split("\n") if x.strip())
    return [m.group(0).strip() for m in SENT_RE.finditer(flat)]


class SentenceTracker:
    """挑出真正说完的句子。

    两个判据：
    1. 句子已经不是最后一句 —— 后面还有内容，说明肯定说完了，直接翻；
    2. 是最后一句 —— 先挂着，等它连续 SETTLE_SEC 秒没再变长才翻。
       如果下一帧它从句子列表里消失，说明被 LiveCaptions 改写（比如
       "pushing." 变成 "pushing through"），作废，绝不翻中间态。
    """

    def __init__(self):
        self.done = set()
        self.tail = ""
        self.tail_since = 0.0
        self.recent = []
        self.ready = False

    def reset(self):
        """切换识别语言后字幕会重启，历史全部作废。"""
        self.done = set()
        self.tail = ""
        self.tail_since = 0.0
        self.recent = []
        self.ready = False

    def feed(self, text):
        sents = split_complete(text)
        if not sents:
            return []

        now = time.time()
        if not self.ready:                      # 首帧当基线，历史内容不翻
            self.done = set(sents)
            self.ready = True
            return []

        if self.tail and self.tail not in sents:
            self.done.add(self.tail)            # 被改写了，作废
            self.tail = ""
            self.tail_since = 0.0

        out = []
        last = len(sents) - 1
        for i, s in enumerate(sents):
            if s in self.done:
                continue
            if len(s.rstrip(".!? ")) < MIN_LEN:
                self.done.add(s)
                continue

            is_last = i == last
            if is_last:
                if s != self.tail:
                    self.tail = s
                    self.tail_since = now
                    continue
                if now - self.tail_since < SETTLE_SEC:
                    continue

            if redundant(s, self.recent) or any(similar(s, d) for d in self.recent):
                self.done.add(s)
                if s == self.tail:
                    self.tail = ""
                continue

            self.done.add(s)
            if s == self.tail:
                self.tail = ""
            self.recent = (self.recent + [s])[-14:]
            out.append(s)

        if len(self.done) > 1200:
            self.done = set()
        return out


# ---------------------------------------------------------------- 悬浮窗
class Overlay:
    def __init__(self, root, on_toggle_caption=None, on_lang_change=None):
        self.root = root
        self.pairs = []
        self.paused = False
        self.bg = "#141414"
        self._hint_key = None
        self.on_toggle_caption = on_toggle_caption
        self.on_lang_change = on_lang_change
        self.lang_var = tk.StringVar(value=read_caption_lang())

        cfg = load_settings()
        self.font_cn = _ci(cfg.get("font_cn"), 12, 44, 20)
        self.alpha = _cf(cfg.get("alpha"), 0.3, 1.0, ALPHA)
        CFG["engine"] = cfg.get("engine", "bing")
        if CFG["engine"] not in ("bing", "baidu_llm", "baidu_nmt"):
            CFG["engine"] = "bing"
        CFG["baidu_appid"] = str(cfg.get("baidu_appid", "") or "")
        CFG["baidu_key"] = str(cfg.get("baidu_key", "") or "")
        CFG["baidu_apikey"] = str(cfg.get("baidu_apikey", "") or "")

        sw = root.winfo_screenwidth()
        sh = root.winfo_screenheight()
        self.w = _ci(cfg.get("width"), 360, int(sw * 0.8), int(sw * 0.40))
        pos = cfg.get("pos")
        if isinstance(pos, list) and len(pos) == 2:
            x = _ci(pos[0], 0, max(0, sw - 120), (sw - self.w) // 2)
            y = _ci(pos[1], 0, max(0, sh - 60), 80)
        else:
            x, y = (sw - self.w) // 2, 80

        root.overrideredirect(True)
        root.attributes("-topmost", True)
        root.attributes("-alpha", self.alpha)
        root.configure(bg=self.bg)
        self._last_activity = time.time()
        self._hidden = False
        self._pos = [x, y]

        root.geometry(f"{self.w}x110+{x}+{y}")

        self.wrap = tk.Frame(root, bg=self.bg, padx=18, pady=12)
        self.wrap.pack(fill="both", expand=True)

        self._build_menu()
        self._build_grip()
        self.show_hint("等待字幕…（右键调字号 / 退出）")
        self.root.after(600, self._expire_tick)

    def _save(self):
        """把当前外观写盘，下次启动直接复用。"""
        try:
            save_settings({
                "alpha": round(self.alpha, 3),
                "font_cn": self.font_cn,
                "width": self.w,
                "pos": list(self._pos),
                "engine": CFG["engine"],
                "baidu_appid": CFG["baidu_appid"],
                "baidu_key": CFG["baidu_key"],
                "baidu_apikey": CFG["baidu_apikey"],
            })
        except Exception as exc:
            log_error(exc)

    # ---- 逐条老化
    def _expire_tick(self):
        """到期的句子逐条移除，窗口高度随之收缩。

        全部过期后窗口缩到最小高度但**不隐藏**——窗口始终在屏幕上。
        """
        try:
            now = time.time()
            keep = [p for p in self.pairs if now - p[2] < PAIR_TTL]
            if len(keep) != len(self.pairs):
                self.pairs = keep
                self.redraw()
        except Exception as exc:
            log_error(exc)
        finally:
            self.root.after(400, self._expire_tick)

    def _wake(self):
        """确保窗口可见。正常情况下它本来就一直在，这里只是兜底。"""
        self._last_activity = time.time()
        try:
            self.root.attributes("-alpha", self.alpha)
            if self._hidden:
                self.root.deiconify()
                self._hidden = False
        except Exception as exc:
            log_error(exc)
            self._hidden = False

    # ---- 右下角缩放
    def _build_grip(self):
        self.grip = tk.Label(self.root, text="◢", bg=self.bg, fg="#6f7780",
                             font=("Segoe UI", 10), cursor="size_nw_se")
        self.grip.place(relx=1.0, rely=1.0, x=-5, y=-3, anchor="se")
        self.grip.bind("<Button-1>", self._resize_start)
        self.grip.bind("<B1-Motion>", self._resize_move)
        self.grip.bind("<ButtonRelease-1>", self._on_release)

    def _resize_start(self, e):
        self._rs_w = self.w
        self._rs_font = self.font_cn
        self._rs_x = e.x_root
        return "break"          # 别让事件继续冒泡成窗口拖动

    def _resize_move(self, e):
        sw = self.root.winfo_screenwidth()
        new_w = int(min(max(360, self._rs_w + (e.x_root - self._rs_x)), sw * 0.8))
        ratio = new_w / self._rs_w
        new_font = int(min(44, max(12, round(self._rs_font * ratio))))
        if new_w != self.w or new_font != self.font_cn:
            self.w = new_w
            self.font_cn = new_font
            self.redraw()
        return "break"

    # ---- 拖动 / 右键
    def _press(self, e):
        self._dx = e.x_root - self.root.winfo_x()
        self._dy = e.y_root - self.root.winfo_y()

    def _drag(self, e):
        self._pos = [e.x_root - self._dx, e.y_root - self._dy]
        self.root.geometry(f"+{self._pos[0]}+{self._pos[1]}")

    def _build_menu(self):
        self.menu = tk.Menu(self.root, tearoff=0)
        self.menu.add_command(label="放大字号", command=lambda: self.zoom(+2))
        self.menu.add_command(label="缩小字号", command=lambda: self.zoom(-2))
        self.menu.add_command(label=f"背景透明度 {int(self.alpha * 100)}%",
                              command=self._cycle_alpha)
        self._alpha_idx = self.menu.index("end")

        self.lang_menu = tk.Menu(self.menu, tearoff=0)
        for code, name in LANGUAGES:
            self.lang_menu.add_radiobutton(
                label=name, value=code, variable=self.lang_var,
                command=lambda c=code: self._pick_lang(c))
        self.menu.add_cascade(label="识别语言", menu=self.lang_menu)

        self.engine_var = tk.StringVar(value=CFG["engine"])
        eng_menu = tk.Menu(self.menu, tearoff=0)
        eng_menu.add_radiobutton(label="Bing（免注册）", value="bing",
                                 variable=self.engine_var,
                                 command=self._set_engine)
        eng_menu.add_radiobutton(label="百度·大模型（需 appid）", value="baidu_llm",
                                 variable=self.engine_var,
                                 command=self._set_engine)
        eng_menu.add_radiobutton(label="百度·机器翻译", value="baidu_nmt",
                                 variable=self.engine_var,
                                 command=self._set_engine)
        self.menu.add_cascade(label="翻译引擎", menu=eng_menu)
        self.menu.add_command(label="百度密钥…", command=self._baidu_dialog)
        self.menu.add_separator()
        self.menu.add_command(label="显示英文字幕窗", command=self._toggle_caption)
        self._cap_idx = self.menu.index("end")
        self.menu.add_separator()
        self.menu.add_command(label="暂停 / 继续", command=self.toggle)
        self.menu.add_command(label="清空", command=self.clear)
        self.menu.add_separator()
        self.menu.add_command(label="退出", command=self._quit)

    def _quit(self):
        """延迟一拍再真正退出。

        直接在菜单 command 里 withdraw/destroy 的话，右键菜单会失去父窗口
        变成孤儿窗口挂在屏幕上——就是「点了退出那个小菜单还在」的现象。
        先让 Tk 把这一次事件处理完、菜单自己 unpost，再动手。
        """
        self.root.after(40, self._real_quit)

    def _real_quit(self):
        self._save()
        try:
            self.menu.unpost()
        except Exception:
            pass
        try:
            self.root.withdraw()
        except Exception:
            pass

        def finish():
            # 先 quit 停掉 mainloop 再 destroy。残留的 after 任务在 destroy 后
            # 可能报 invalid command name，但那是 Tcl 打到 stderr 的，pythonw
            # 下看不到，也不影响功能——不必为它冒险取消整个队列。
            for fn in (self.root.quit, self.root.destroy):
                try:
                    fn()
                except Exception:
                    pass

        self.root.after(120, finish)

    def _cycle_alpha(self):
        """在预设档位间循环，让背景更透一点或更实一点。"""
        try:
            i = ALPHA_LEVELS.index(self.alpha)
        except ValueError:
            i = 1
        self.alpha = ALPHA_LEVELS[(i + 1) % len(ALPHA_LEVELS)]
        try:
            self.root.attributes("-alpha", self.alpha)
            self.menu.entryconfigure(
                self._alpha_idx, label=f"背景透明度 {int(self.alpha * 100)}%")
        except Exception as exc:
            log_error(exc)
        self._save()

    def _pick_lang(self, code):
        self.lang_var.set(code)      # 程序调用时 Tk 不会自动更新变量
        if self.on_lang_change:
            self.on_lang_change(code)

    def _set_engine(self):
        CFG["engine"] = self.engine_var.get()
        _CACHE.clear()
        self._save()
        if CFG["engine"].startswith("baidu") and not get_baidu().ready:
            self.show_hint("百度引擎还没填 appid/密钥，右键「百度密钥…」设置",
                           key="baidu_nokey")

    def _baidu_dialog(self):
        win = tk.Toplevel(self.root)
        win.title("百度翻译 API 配置")
        win.configure(bg=self.bg)
        win.attributes("-topmost", True)
        win.resizable(False, False)
        win.geometry(f"490x350+{self._pos[0]}+{self._pos[1] + 90}")

        tk.Label(win,
                 text="在 fanyi-api.baidu.com 注册后创建应用。\n"
                      "API Key 和「密钥」二选一即可，推荐 API Key。\n"
                      "大模型翻译需在控制台单独开通。",
                 font=("Microsoft YaHei UI", 9), fg="#9aa0a6", bg=self.bg,
                 justify="left").pack(anchor="w", padx=18, pady=(14, 12))

        fields = {}
        for label, val, fkey, secret in (
                ("APP ID", CFG["baidu_appid"], "appid", False),
                ("API Key", CFG["baidu_apikey"], "apikey", True),
                ("密钥", CFG["baidu_key"], "key", True)):
            row = tk.Frame(win, bg=self.bg)
            row.pack(fill="x", padx=18, pady=4)
            tk.Label(row, text=label, width=9, anchor="w",
                     fg="#d0d0d0", bg=self.bg,
                     font=("Microsoft YaHei UI", 9)).pack(side="left")
            ent = tk.Entry(row, bg="#1f1f1f", fg="#e6e6e6",
                           insertbackground="#e6e6e6", relief="flat",
                           show="*" if secret else "")
            ent.insert(0, val)
            ent.pack(side="left", fill="x", expand=True, ipady=4)
            fields[fkey] = ent

        msg = tk.Label(win, text="", fg="#ff8080", bg=self.bg,
                       font=("Microsoft YaHei UI", 9))
        msg.pack(anchor="w", padx=18, pady=(8, 0))

        def save():
            CFG["baidu_appid"] = fields["appid"].get().strip()
            CFG["baidu_apikey"] = fields["apikey"].get().strip()
            CFG["baidu_key"] = fields["key"].get().strip()
            _CACHE.clear()
            _BAIDU["t"] = None
            if not get_baidu().ready:
                msg.config(text="APP ID 必填，API Key 和密钥至少填一个")
                return
            self.engine_var.set("baidu_llm")
            CFG["engine"] = "baidu_llm"
            self._save()
            win.destroy()
            self.show_hint("已启用百度翻译", key="baidu_on")

        def open_site():
            import webbrowser
            webbrowser.open("https://fanyi-api.baidu.com/manage/developer")

        btns = tk.Frame(win, bg=self.bg)
        btns.pack(pady=18)
        tk.Button(btns, text="保存并启用", command=save,
                  width=12).pack(side="left", padx=6)
        tk.Button(btns, text="打开注册页", command=open_site,
                  width=10).pack(side="left", padx=6)
        tk.Button(btns, text="取消", command=win.destroy,
                  width=8).pack(side="left", padx=6)

        win.focus_force()
        fields["appid"].focus_set()

    def _toggle_caption(self):
        if not self.on_toggle_caption:
            return
        hidden = self.on_toggle_caption()
        self.menu.entryconfigure(
            self._cap_idx,
            label="显示英文字幕窗" if hidden else "隐藏英文字幕窗")

    def _bind_all(self):
        targets = [self.root, self.wrap] + list(self.wrap.winfo_children())
        for w in targets:
            w.bind("<Button-1>", self._press)
            w.bind("<B1-Motion>", self._drag)
            w.bind("<ButtonRelease-1>", self._on_release)
            w.bind("<Button-3>", lambda e: self.menu.tk_popup(e.x_root, e.y_root))

    def _on_release(self, e=None):
        """拖完（移动或缩放）才写盘，避免拖动过程中频繁落盘。"""
        self._save()

    # ---- 内容
    def _clear(self):
        for w in self.wrap.winfo_children():
            w.destroy()

    def _ceiling(self):
        """窗口底边的硬上限：屏幕竖直中点。"""
        return int(self.root.winfo_screenheight() * 0.5) - self.root.winfo_y()

    def _fit(self):
        """按内容实际高度调整窗口，但底边绝不超过屏幕竖直中点。

        注意：Frame 清空子控件后 winfo_reqheight 不会重算（返回旧缓存），
        所以「一条都没有」要单独处理，否则窗口会卡在之前的厚度上。
        """
        limit = max(48, self._ceiling())
        x, y = self._pos
        if not self.wrap.winfo_children():
            self.root.geometry(f"{self.w}x{MIN_EMPTY_H}+{x}+{y}")
            return
        for _ in range(2):
            self.root.update_idletasks()
            h = min(max(56, self.wrap.winfo_reqheight() + 8), limit)
            self.root.geometry(f"{self.w}x{h}+{x}+{y}")

    def show_hint(self, text, key=None):
        if key is not None and key == self._hint_key:
            return
        self._hint_key = key
        self._wake()
        self._clear()
        tk.Label(self.wrap, text=text, font=("Microsoft YaHei UI", 12),
                 fg="#6b7280", bg=self.bg, anchor="w", justify="left",
                 wraplength=self.w - 40).pack(fill="x")
        self._bind_all()
        self._fit()

    def add(self, en, cn):
        self._hint_key = None
        self._wake()
        self.pairs.append((en, cn, time.time()))
        self.pairs = self.pairs[-MAX_PAIRS:]
        self.redraw()

    def zoom(self, d):
        self.font_cn = max(12, min(44, self.font_cn + d))
        self.redraw()
        self._save()

    def toggle(self):
        self.paused = not self.paused
        if self.paused:
            self.show_hint("已暂停", key="paused")
        else:
            self.show_hint("继续监听…", key="resume")

    def clear(self):
        self.pairs.clear()
        self.show_hint("已清空", key="clear")

    def _make_row(self, en, cn, wrap_len):
        tk.Label(self.wrap, text=cn,
                 font=("Microsoft YaHei UI", self.font_cn),
                 fg="#ffffff", bg=self.bg, anchor="w", justify="left",
                 wraplength=wrap_len).pack(fill="x", pady=(2, 0))
        tk.Label(self.wrap, text=en,
                 font=("Segoe UI", max(10, self.font_cn - 8)),
                 fg="#8b949e", bg=self.bg, anchor="w", justify="left",
                 wraplength=wrap_len).pack(fill="x", pady=(0, 8))

    def redraw(self):
        """内容超出中线就从最旧的开始丢，保证整句完整显示而不是被切掉。"""
        wrap_len = self.w - 40
        pairs = list(self.pairs)
        while True:
            self._clear()
            for en, cn, _ in pairs:
                self._make_row(en, cn, wrap_len)
            self.wrap.update_idletasks()
            if len(pairs) <= 1 or self.wrap.winfo_reqheight() <= self._ceiling():
                break
            pairs.pop(0)
        self.pairs = pairs
        self._bind_all()
        self._fit()


# ---------------------------------------------------------------- 主流程
_MUTEX = None


def acquire_single_instance():
    """只允许一个实例，避免重复双击叠出多个悬浮窗。"""
    global _MUTEX
    kernel32 = ctypes.windll.kernel32
    kernel32.CreateMutexW.restype = ctypes.c_void_p
    kernel32.CreateMutexW.argtypes = [ctypes.c_void_p, ctypes.c_bool,
                                      ctypes.c_wchar_p]
    _MUTEX = kernel32.CreateMutexW(None, False, "Local\\LiveCaptionTranslator")
    if kernel32.GetLastError() == 183:          # ERROR_ALREADY_EXISTS
        # 已有实例在跑：先叫它把窗口亮出来，用户双击本来多半就是想找窗口
        kernel32.OpenEventW.restype = ctypes.c_void_p
        kernel32.OpenEventW.argtypes = [ctypes.c_uint, ctypes.c_bool,
                                        ctypes.c_wchar_p]
        ev = kernel32.OpenEventW(0x0002, False, EVENT_NAME)   # EVENT_MODIFY_STATE
        if ev:
            kernel32.SetEvent(ctypes.c_void_p(ev))
            kernel32.CloseHandle(ctypes.c_void_p(ev))
        return False
    return True


def main():
    if not acquire_single_instance():
        return
    root = tk.Tk()
    state = {"win": None, "cache": [None], "tries": 0, "last_try": 0.0}
    hider = CaptionHider()
    tracker = SentenceTracker()
    _SRC["lang"] = read_caption_lang()[:2]

    def toggle_caption():
        """返回 True 表示当前处于隐藏状态。"""
        if hider.enabled:
            hider.enabled = False
            hider.restore()
            return False
        hider.enabled = True
        if state["win"] is not None:
            hider.hide(state["win"])
        return True

    def change_lang(code):
        """切换识别语言：写注册表 → 重启实时字幕 → 作废历史识别状态。"""
        if not write_caption_lang(code):
            ui.lang_var.set(read_caption_lang())    # 失败就回滚到真实值
            ui.show_hint("切换语言失败（注册表写入被拒绝）", key="langfail")
            return
        _SRC["lang"] = code[:2]
        _CACHE.clear()
        tracker.reset()
        state["win"] = None
        state["cache"][0] = None
        state["tries"] = 0
        state["last_try"] = 0.0
        ui.show_hint(
            f"已切换到 {LANG_NAMES.get(code, code)}，正在重启字幕…",
            key=f"lang{code}")

        def restart():
            close_live_captions()
            time.sleep(0.4)
            launch_live_captions()

        threading.Thread(target=restart, daemon=True).start()

    ui = Overlay(root, toggle_caption, change_lang)

    out_q = queue.Queue()
    jobs = queue.Queue()

    def worker():
        while True:
            item = jobs.get()
            if item is None:
                return
            tag, text = item
            out_q.put((tag, text, translate(text)))

    threading.Thread(target=ENGINE.warmup, daemon=True).start()
    threading.Thread(target=worker, daemon=True).start()

    # 监听「第二次双击」发来的唤醒信号
    kernel32 = ctypes.windll.kernel32
    kernel32.CreateEventW.restype = ctypes.c_void_p
    kernel32.CreateEventW.argtypes = [ctypes.c_void_p, ctypes.c_bool,
                                      ctypes.c_bool, ctypes.c_wchar_p]
    wake_ev = kernel32.CreateEventW(None, False, False, EVENT_NAME)
    wake_q = queue.Queue(16)

    def watch_wakeup():
        while True:
            kernel32.WaitForSingleObject(ctypes.c_void_p(wake_ev), 0xFFFFFFFF)
            try:
                wake_q.put_nowait(1)
            except queue.Full:
                pass

    if wake_ev:
        threading.Thread(target=watch_wakeup, daemon=True).start()

    def poll():
        try:
            try:
                while True:
                    wake_q.get_nowait()
                    ui._wake()
            except queue.Empty:
                pass

            if not ui.paused:
                win = state["win"]
                if win is not None:
                    # UIA 对象失效时 Exists() 会抛 COMError，不是返回 False，
                    # 之前直接调会导致每轮 poll 都写一条日志
                    try:
                        alive = win.Exists(0)
                    except Exception:
                        alive = False
                    if not alive:
                        win = None
                if win is None:
                    win = find_caption_window()
                    state["win"] = win
                    state["cache"][0] = None
                if win is None:
                    now = time.time()
                    if state["tries"] < 2 and now - state["last_try"] > 10:
                        # 字幕没开就自己拉起来，省得用户按快捷键
                        state["tries"] += 1
                        state["last_try"] = now
                        ok = launch_live_captions()
                        ui.show_hint(
                            "正在启动实时字幕…" if ok else "无法启动 —— 请按 Win + Ctrl + L",
                            key=f"launch{state['tries']}")
                    elif state["tries"] >= 2 and now - state["last_try"] > 10:
                        ui.show_hint("未检测到实时字幕 —— 请按 Win + Ctrl + L 手动打开",
                                     key="nolc")
                else:
                    if hider.enabled and not hider.is_hidden(win):
                        hider.hide(win)
                    try:
                        cur, state["cache"] = read_text(win, state["cache"])
                    except Exception:
                        cur = ""
                        state["cache"][0] = None
                    if cur:
                        was_ready = tracker.ready
                        for ln in tracker.feed(cur):
                            jobs.put(("s", ln))
                        if tracker.ready and not was_ready:
                            ui.show_hint("已连接实时字幕，等待新语音…", key="ready")
                    else:
                        # 窗口在，但还没有识别结果——没声音进来时会这样
                        ui.show_hint("已连接实时字幕，等待声音…", key="idle")
        except Exception as exc:
            log_error(exc)          # 任何异常都不许让轮询断掉
        finally:
            root.after(POLL_MS, poll)

    def drain():
        try:
            while True:
                _, en, cn = out_q.get_nowait()
                ui.add(en, cn)
        except queue.Empty:
            pass
        root.after(120, drain)

    root.after(300, poll)
    root.after(150, drain)
    try:
        root.mainloop()
    finally:
        jobs.put(None)
        # 先放回屏内，否则 Windows 会记住屏幕外坐标，下次开启字幕会开在看不见的地方
        hider.restore()
        time.sleep(0.25)
        close_live_captions()


if __name__ == "__main__":
    main()
