# LIFESPAN: permanent
"""PC receiver for the Typeferry phone app: the fast path. The phone sends its keyboard state over USB or Wi-Fi; this turns it into real key presses (SendInput).

Why: the phone's Bluetooth keyboard mode is held to about ONE key per second by its Bluetooth stack (measured 2026-10-17). A TCP stream has no such limit. Bluetooth stays as the fallback (it works at the
Windows sign-in screen, which a program in the user session cannot reach).

DIRECTION: the phone LISTENS (port 8777) and THIS program connects OUT to it, so Windows Firewall never prompts. To find the phone it tries, in order: 127.0.0.1 (USB: it keeps `adb forward tcp:8777 tcp:8777`
set while exactly one phone is plugged in), the phone's own advertised addresses on networks this PC is on right now (newest first), the last phone address, the tethering gateway addresses, then a scan of every
network's /24. While one link carries the keys a watcher looks every two seconds for a better one (adb, then a USB cable network, then anything else) and hands over make-before-break: the phone accepts the new
connection and drops the old one, and the new link goes to exactly one owner (serve() while it runs, otherwise the main loop through take_late_link), never closed.

SECURITY (protocol v2, see linkcrypto.py): the 16 character pairing code (token.txt, shown by `--pair`) never crosses the network. Each side proves it knows it with fresh nonces, and THIS program verifies the
phone's proof before it sends or trusts anything, so a stranger's listener on port 8777 learns nothing and can type nothing. Every frame is encrypted and authenticated with a counter (a bad tag ends the
connection). A heartbeat in both directions detects a dead link; if the phone goes quiet for 5 seconds every key is released.

Frames from the phone (8 bytes, sealed to 16): [1, mods, key1..key6] full keyboard state (a HID boot report); [2, lo, hi] one media key; [4] heartbeat; [5, lo, hi] one Unicode character; [6, buttons, dx, dy,
wheel, hwheel] the trackpad (signed bytes); [8, on] report (or stop reporting) the program in front; [9, kind, a, b, c, d] one of the phone's own addresses (kind 1 cable, 2 Wi-Fi, 3 hotspot). Frames to the phone:
[3, lock-key bits, status] (Caps, Num, Scroll Lock, status bit 0 locked or a security prompt, bit 1 Filter Keys; sent on change and every 2 s) and [7, six bytes] the program in front as a hash of its file name.
Keys are sent as fixed scan codes in one SendInput call per frame, so the key is the same on any layout and a chord is never interleaved.
Limits: it cannot type into an elevated (administrator) window or a UAC prompt, and nothing here runs before sign-in.

THE PROGRAM THE PERSON SEES: no console, but a tray icon (its tooltip says the state; a left click opens the status window; a right click gives Status, Pair another phone, Remove from startup, Quit) and a status window (the phone, the link,
how long since the last signal, whether Windows is refusing input or Filter Keys is on, the version). Opening the program again shows that window (the second start posts a message to the running one's hidden tray window). Closing the
window hides it to the tray; Quit ends the link loop, which lifts every key and button (the same release path as a dropped link), and removes the tray icon. final_cleanup runs once however the program ends. The windows share one dark theme
(Theme) that matches the phone app. All of this is the person-facing layer: the protocol, the security and the input code above and below it are untouched.

Run: pythonw typeferry_receiver.pyw (headless, in Windows Startup). `--pair` opens the pairing window (a number to type on the phone, then the number the phone shows to type here; the code itself sits behind a button). `--push-code` sends the code to a USB-connected phone (run with python.exe). Log: receiver.log. Test switches: TYPEFERRY_UI_SCALE (draw the windows at a fixed scale, such as 1.5), TYPEFERRY_TEST_AUTOYES (see autoyes_enabled).
"""
import atexit
import base64
import concurrent.futures
import ctypes
import hmac
import ipaddress
import os
import queue
import re
import secrets
import select
import shutil
import socket
import struct
import subprocess
import sys
import tempfile
import threading
import unicodedata
import time
import traceback
import zlib
from ctypes import wintypes as wt

try:
    import tkinter as tk
    import tkinter.font as tkfont
except ImportError:                                                 # a Python without Tk: the receiver still types, it just has no windows
    tk = tkfont = None

FROZEN = getattr(sys, "frozen", False)                         # True when this is the packaged TypeferryReceiver.exe: no Python needed on the PC
HERE = os.path.dirname(os.path.abspath(sys.executable if FROZEN else __file__))
if not FROZEN:
    sys.path.insert(0, HERE)          # the packaged program imports its own bundled copy: its folder (often Downloads) must never be searched first
import linkcrypto as LC  # noqa: E402

# The packaged program unpacks itself to a temporary folder, so its code, log and pairing state live in a permanent per-user folder instead (the script keeps them beside itself).
DATA = os.environ.get("TYPEFERRY_DATA") or (os.path.join(os.environ.get("LOCALAPPDATA", HERE), "Typeferry") if FROZEN else HERE)          # TYPEFERRY_DATA: a test points a receiver at a throw-away folder
try:
    os.makedirs(DATA, exist_ok=True)
except OSError:
    DATA = HERE
PORT = int(os.environ.get("TYPEFERRY_PORT", "8777"))
CODE_FILE = os.path.join(DATA, "token.txt")
LAST_FILE = os.path.join(DATA, "last_phone.txt")
AUTOSTART_OFF_FILE = os.path.join(DATA, "no_autostart.txt")          # present when the person removed the start with Windows entry: the receiver never puts it back on its own
PAIRED_FILE = os.path.join(DATA, "paired.txt")                 # touched on every successful connection: until it exists the pairing window opens by itself
LOG_FILE = os.path.join(DATA, "receiver.log")
STARTED_FILE = os.path.join(DATA, "started.txt")                 # when the running receiver started: a second start within DUPLICATE_START_S of it is a duplicate login start, not a person asking for the window
DUPLICATE_START_S = 90.0
RECEIVER_VERSION = "5.5"                                          # the app version this receiver belongs to (test_receiver_maps checks it against version.txt, build_receiver_exe.ps1 refuses a mismatch)
def isolated_run(environ):
    """True for a test or a second instance: it has its own data folder or its own instance name."""
    return bool(environ.get("TYPEFERRY_DATA") or environ.get("TYPEFERRY_INSTANCE"))


ISOLATED_RUN = isolated_run(os.environ)          # a test that REPLACES the registry with a fake sets this False for its own duration
INSTANCE = os.environ.get("TYPEFERRY_INSTANCE", "")                 # test only: a second, separate receiver (its own mutex, tray window and note) can run beside a real one; empty in every normal run
MUTEX_NAME = "Local\\PhoneKbReceiver" + INSTANCE
RUNNING_FILE = os.path.join(tempfile.gettempdir(), "phonekb_running" + INSTANCE + ".txt")          # who holds the receiver's mutex: its data folder, its version and when it started, so a second start can say something true
PAIR_DECIDE_S = 300.0                                         # how long one prompt waits for the person (the phone waits a little longer for it)
AUTOYES_GO = os.environ.get("TYPEFERRY_AUTOYES_GO") or os.path.join(DATA, "autoyes_go.txt")              # test only: the auto-yes switch types the second number when this file appears (after the test typed the first on the phone)
PAIR_WINDOW_S = 300.0                                         # how long the pairing window looks for a phone before it gives up
QUIET_S = 5.0                                                 # no VALID frame (a heartbeat comes every second) for this long, by the monotonic clock: the phone is gone, release every key
HANDSHAKE_S = 3.0             # one deadline for a whole link handshake: a host that answers a byte at a time cannot hold the search (each recv has its own timeout, so only a total stops a drip)
PAIR_EXCHANGE_S = 8.0         # the same for the first exchange of pairing (hello, the phone's 272 byte answer) and, below, for the phone's K after the person's entry
PAIR_K_S = 15.0
SCAN_MAX_HOSTS = 40           # how many hosts with the port open one sweep tries to handshake with (the phone is often not the lowest address)
SCAN_BUDGET_S = 20.0          # and the most time one sweep spends on those handshakes
REFUSAL_LOG_GAP_S = 1.0       # a refused SendInput is logged at most this often: a trackpad sends hundreds of frames a second and would otherwise push the history out of the log
SCAN_EVERY_S = 30.0
SCAN_MAX_S = 120.0          # while no phone is found the scan of every network slows from 30 seconds to this (a phone that rebooted or changed address is found within two minutes), and starts again at once when an adapter appears or a phone is found
user32 = ctypes.WinDLL("user32", use_last_error=True)
kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
ULONG_PTR = ctypes.c_size_t
KEYUP, EXTENDED, SCANCODE = 0x0002, 0x0001, 0x0008
APP_NAME = "Typeferry"
QUIT = threading.Event()          # set by Quit: the main loop and the link loop end (the link loop lifts every key and button on its way out)
MAIN_DONE = threading.Event()     # set when the main loop has finished, so Quit can tell that everything was released
QUIT_WAIT_S = 3.0                 # how long Quit waits for the main loop before it releases everything itself and leaves
_ever_served = [False]            # a link has carried keys in this run: final_cleanup then lifts every key once more, whatever happened


class LinkInfo:
    """What the status window and the tray say about the link: the one place the receiver's threads write and the windows read. Plain values under a lock, copied out by snapshot()."""

    def __init__(self):
        self.lock = threading.Lock()
        self.how = ""                  # "" while no phone is connected, else the text find_phone built ("Wi-Fi (192.168.1.20)", "USB")
        self.since = 0.0
        self.last_frame = 0.0          # when the phone last sent anything (a heartbeat comes every second)
        self.usb_name = ""             # the model name adb reports for the one phone on the cable

    def connect(self, how, now=None):
        with self.lock:
            self.how = how
            self.since = time.monotonic() if now is None else now
            self.last_frame = self.since

    def disconnect(self):
        with self.lock:
            self.how = ""

    def touch(self, now=None):
        self.last_frame = time.monotonic() if now is None else now

    def snapshot(self):
        with self.lock:
            return {"how": self.how, "since": self.since, "last_frame": self.last_frame, "usb_name": self.usb_name}


LINK = LinkInfo()


def log(msg):
    """One line to receiver.log (never the pairing code)."""
    try:
        if os.path.exists(LOG_FILE) and os.path.getsize(LOG_FILE) > 200000:
            os.replace(LOG_FILE, LOG_FILE + ".old")
        with open(LOG_FILE, "a", encoding="utf-8") as f:
            f.write(time.strftime("%Y-%m-%d %H:%M:%S ") + msg + "\n")
    except OSError:
        pass


_last_logged = {}


def log_limited(key, msg, gap=None):
    """log(), but at most once per `gap` seconds for the same key (the monotonic clock): the same refusal repeated for every frame must not erase the pairing and connect history."""
    now = time.monotonic()
    if now - _last_logged.get(key, -1e9) < (REFUSAL_LOG_GAP_S if gap is None else gap):
        return
    _last_logged[key] = now
    log(msg)


def write_code_file(code):
    """The code on disk, written whole and moved into place: a receiver reading the file mid-write must never see an empty code, and a power cut must not leave one."""
    tmp = CODE_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(code)
        f.flush()
        os.fsync(f.fileno())
    for attempt in range(3):                                          # an antivirus scan can hold the file for a moment
        try:
            os.replace(tmp, CODE_FILE)
            return
        except OSError:
            time.sleep(0.2)
    try:
        with open(CODE_FILE, "w", encoding="utf-8") as f:
            f.write(code)
    finally:
        try:
            os.remove(tmp)
        except OSError:
            pass


def create_code_file(code, path=None):
    """Create token.txt ONLY when it does not exist yet: True when this call made it, False when another start got there first (its code stands). Two first starts at once minted two codes and the last one
    written won, so the receiver that started first kept a key the file no longer held. The code is written whole to a temporary name and hard-linked into place, which fails when the file exists."""
    target = path or CODE_FILE
    tmp = "%s.new%d" % (target, os.getpid())
    with open(tmp, "w", encoding="utf-8") as f:
        f.write(code)
        f.flush()
        os.fsync(f.fileno())
    try:
        try:
            os.link(tmp, target)
            return True
        except FileExistsError:
            return False
        except OSError:                                               # a volume with no hard links: the check and the move are two steps there, but still far narrower than a blind replace
            if os.path.exists(target):
                return False
            os.replace(tmp, target)
            return True
    finally:
        try:
            os.remove(tmp)
        except OSError:
            pass


def forget_pairing(key_path=None):
    """Remove paired.txt beside the key file (this receiver's own folder when key_path is None): until it exists again the status says Not paired yet and the pairing window opens by itself. Nothing else is touched."""
    target = PAIRED_FILE if key_path is None else os.path.join(os.path.dirname(os.path.abspath(key_path)), os.path.basename(PAIRED_FILE))
    try:
        os.remove(target)
    except OSError:
        pass


_code_problem = [""]          # what is wrong with token.txt, in words for the person, when load_code gave up: main shows it (a receiver that stops with only a log line looks like a program that does nothing)


def load_code():
    """The pairing code from token.txt, created on first run. Never silently replaces a file that holds something else (it logs, says why in _code_problem and gives up); the old 7 character token is replaced once."""
    _code_problem[0] = ""
    raw, e = None, None
    for attempt in range(3):                                          # an antivirus scan or a sync client can hold the file for a moment, most often at sign-in
        try:
            raw = open(CODE_FILE, encoding="utf-8-sig").read()
            e = None
            break
        except FileNotFoundError:
            raw, e = None, None
            break
        except OSError as err:
            e = err
            if attempt < 2:
                time.sleep(0.3)
        except ValueError as err:
            e = err
            break
    if e is not None:                                                 # a locked or odd file is not a missing one: writing a new code over it would break a working pairing
        log("token.txt could not be read (%s): leaving it alone. Not starting." % e)
        _code_problem[0] = "The pairing code file could not be read (%s), so the receiver did not start. Close any program that has it open, then start the receiver again. The file is token.txt in %s." % (e, DATA)
        return None
    if raw is not None and not raw.strip():                           # a file that exists but is empty is a damaged code (a crash while it was written), not a missing one: a new code would silently break the pairing
        log("token.txt is empty: delete it to make a new code (the phone must then be paired again). Not starting.")
        _code_problem[0] = "The pairing code file is empty, so the receiver did not start. Delete token.txt in %s, start the receiver again, and pair the phone again." % DATA
        return None
    code = LC.normalize(raw or "")
    if code:
        return code
    old = (raw or "").strip()
    if old and not re.fullmatch(r"[a-z0-9]{7}", old):
        log("token.txt holds something that is not a pairing code: fix or delete it. Not starting.")
        _code_problem[0] = "The pairing code file holds something that is not a pairing code, so the receiver did not start. Delete token.txt in %s, start the receiver again, and pair the phone again." % DATA
        return None
    code = "".join(secrets.choice(LC.ALPHABET) for _ in range(LC.CODE_LEN))
    if old:
        write_code_file(code)                                         # the old 7 character token is replaced once, on purpose
    elif not create_code_file(code):                                  # another start made the file first: use ITS code, never a second one
        other = read_code_quiet()
        if other:
            return other
        log("token.txt appeared while it was being created and is not a valid code. Not starting.")
        _code_problem[0] = "The pairing code file is not valid, so the receiver did not start. Delete token.txt in %s and start the receiver again." % DATA
        return None
    forget_pairing()                                                  # a NEW code pairs nobody: a record of the old pairing (token.txt deleted while the receiver was stopped) must not say Paired, and the pairing window opens as on a first run
    log("created a new pairing code" + (" (the old 7 character token is retired)" if old else ""))
    return code


def code_signature(path=None):
    """(modified time in ns, size) of token.txt, or None when it cannot be read: any change to the file shows up here, even a rewrite inside the clock's granularity."""
    try:
        st = os.stat(path or CODE_FILE)
        return (st.st_mtime_ns, st.st_size)
    except OSError:
        return None


def read_code_quiet(path=None):
    """The valid pairing code in token.txt, or None (missing, unreadable, empty or not a code). Never creates, replaces or logs anything: load_code is the only one that may do that, once, at start."""
    try:
        return LC.normalize(open(path or CODE_FILE, encoding="utf-8-sig").read()) or None
    except (OSError, ValueError):
        return None


CODE_GONE_GRACE_S = 10.0          # token.txt must be missing this long before the running receiver treats it as deleted (an atomic rewrite, a sync client or a scan can hide it for a moment)


def code_file_gone(path=None):
    """True only when token.txt is DEFINITELY not there (FileNotFoundError): a locked file, a permission error or a slow disk is never a deleted one."""
    try:
        os.stat(path or CODE_FILE)
        return False
    except FileNotFoundError:
        return True
    except OSError:
        return False


class KeyStore:
    """The link key for the pairing code on disk RIGHT NOW. The pairing window is a separate process that rewrites token.txt while this one keeps running, so every search for the phone (the main loop AND the watcher that looks for a better link while one is up) asks here instead of holding the key it started with: a receiver left running for hours would otherwise keep answering a re-paired phone with the old key ('a device answered but does not know this pairing code'). A change that does not hold a valid code keeps the old key and is looked at again on the next ask."""

    def __init__(self, code, path=None, on_change=None):
        self.path = path
        self.lock = threading.Lock()
        self.sig = code_signature(path)                               # the file's signature FIRST, then its content: a rewrite between the two shows up as a changed signature at the next ask and heals itself
        self.key = LC.derive_key(read_code_quiet(path) or code)
        self.on_change = on_change
        self.gone_since = None
        self.revoked = 0          # counts the times the pairing was deleted: a link that started before ends at its next frame

    def get(self):
        sig = code_signature(self.path)
        with self.lock:
            if sig is not None and sig != self.sig:
                fresh = read_code_quiet(self.path)
                if fresh:
                    new = LC.derive_key(fresh)
                    self.sig = sig
                    if new != self.key:
                        self.key = new
                        self.revoked += 1          # a live link was made with the OLD code: it ends at its next frame (a new pairing replaces the old one, so an old or lost phone stops working, round 14)
                        if self.on_change:
                            self.on_change()
            if sig is not None:
                self.gone_since = None
            elif self.sig is not None and code_file_gone(self.path):          # he deleted the pairing: the receiver that is running forgets it too, with a new code, so a lost or old phone stops working (the policy says deleting token.txt forgets the pairing)
                now = time.monotonic()
                if self.gone_since is None:
                    self.gone_since = now
                elif now - self.gone_since >= CODE_GONE_GRACE_S:
                    fresh = "".join(secrets.choice(LC.ALPHABET) for _ in range(LC.CODE_LEN))
                    try:
                        made = create_code_file(fresh, self.path)
                    except OSError:
                        made = False
                    if made:
                        self.key = LC.derive_key(fresh)
                        self.sig = code_signature(self.path)
                        self.gone_since = None
                        self.revoked += 1
                        forget_pairing(self.path)          # the status and the tray say Not paired yet (round 14); beside THIS key file only, never another folder's record (a store made with no path is the running receiver's own folder)
                        log("token.txt was deleted: made a new pairing code, the phone must be paired again")
                        if self.on_change:
                            self.on_change()
            return self.key


KEYS = [None]          # the running receiver's KeyStore (set in main)


class KEYBDINPUT(ctypes.Structure):
    _fields_ = [("wVk", wt.WORD), ("wScan", wt.WORD), ("dwFlags", wt.DWORD), ("time", wt.DWORD), ("dwExtraInfo", ULONG_PTR)]


class MOUSEINPUT(ctypes.Structure):
    _fields_ = [("dx", wt.LONG), ("dy", wt.LONG), ("mouseData", wt.DWORD), ("dwFlags", wt.DWORD), ("time", wt.DWORD), ("dwExtraInfo", ULONG_PTR)]


class _U(ctypes.Union):
    _fields_ = [("ki", KEYBDINPUT), ("mi", MOUSEINPUT)]


class INPUT(ctypes.Structure):
    _anonymous_ = ("u",)
    _fields_ = [("type", wt.DWORD), ("u", _U)]


user32.SendInput.argtypes = (wt.UINT, ctypes.POINTER(INPUT), ctypes.c_int)
user32.SendInput.restype = wt.UINT

# HID usage -> (scan code set 1, extended). Position based, so the same key on any layout, and numpad keys are real numpad keys (NumLock decides what they do).
SCAN = {}
for i, sc in enumerate((0x1E, 0x30, 0x2E, 0x20, 0x12, 0x21, 0x22, 0x23, 0x17, 0x24, 0x25, 0x26, 0x32, 0x31, 0x18, 0x19, 0x10, 0x13, 0x1F, 0x14, 0x16, 0x2F, 0x11, 0x2D, 0x15, 0x2C)):
    SCAN[0x04 + i] = (sc, 0)                                   # a to z
for i in range(10):
    SCAN[0x1E + i] = (0x02 + i, 0)                             # 1 to 9, 0 (0x27 is 0)
SCAN.update({0x28: (0x1C, 0), 0x29: (0x01, 0), 0x2A: (0x0E, 0), 0x2B: (0x0F, 0), 0x2C: (0x39, 0), 0x2D: (0x0C, 0), 0x2E: (0x0D, 0), 0x2F: (0x1A, 0), 0x30: (0x1B, 0), 0x31: (0x2B, 0),
             0x33: (0x27, 0), 0x34: (0x28, 0), 0x35: (0x29, 0), 0x36: (0x33, 0), 0x37: (0x34, 0), 0x38: (0x35, 0), 0x39: (0x3A, 0)})
for i in range(10):
    SCAN[0x3A + i] = (0x3B + i, 0)                             # F1 to F10
SCAN.update({0x44: (0x57, 0), 0x45: (0x58, 0)})                # F11, F12
for i in range(11):
    SCAN[0x68 + i] = (0x64 + i, 0)                             # F13 to F23
SCAN[0x73] = (0x76, 0)                                         # F24
SCAN.update({0x46: (0x37, 1), 0x47: (0x46, 0), 0x49: (0x52, 1), 0x4A: (0x47, 1), 0x4B: (0x49, 1), 0x4C: (0x53, 1), 0x4D: (0x4F, 1), 0x4E: (0x51, 1), 0x4F: (0x4D, 1), 0x50: (0x4B, 1),
             0x51: (0x50, 1), 0x52: (0x48, 1), 0x65: (0x5D, 1)})                                         # PrtSc ScrLk Ins Home PgUp Del End PgDn arrows Menu
SCAN.update({0x53: (0x45, 0), 0x54: (0x35, 1), 0x55: (0x37, 0), 0x56: (0x4A, 0), 0x57: (0x4E, 0), 0x58: (0x1C, 1), 0x62: (0x52, 0), 0x63: (0x53, 0)})          # NumLock keypad / * - + Enter 0 .
for i, sc in enumerate((0x4F, 0x50, 0x51, 0x4B, 0x4C, 0x4D, 0x47, 0x48, 0x49)):
    SCAN[0x59 + i] = (sc, 0)                                   # keypad 1 to 9
# Keys of non-US boards, from Microsoft's scan code table: ISO extra keys (Non-US # and \), keypad =, keypad comma, and the Japanese and Korean language keys. Without these a keystroke was silently dropped.
SCAN.update({0x32: (0x2B, 0), 0x64: (0x56, 0), 0x67: (0x59, 0), 0x85: (0x7E, 0), 0x87: (0x73, 0), 0x88: (0x70, 0), 0x89: (0x7D, 0), 0x8A: (0x79, 0), 0x8B: (0x7B, 0), 0x90: (0x72, 0), 0x91: (0x71, 0)})
PAUSE = 0x48                                                   # Pause has no single scan code: it goes as VK_PAUSE
MODS = ((0x01, (0x1D, 0)), (0x02, (0x2A, 0)), (0x04, (0x38, 0)), (0x08, (0x5B, 1)),                  # left ctrl, shift, alt, windows
        (0x10, (0x1D, 1)), (0x20, (0x36, 0)), (0x40, (0x38, 1)), (0x80, (0x5C, 1)))                  # right ctrl, shift, alt, windows
CONSUMER = {0xE9: 0xAF, 0xEA: 0xAE, 0xE2: 0xAD, 0xCD: 0xB3, 0xB5: 0xB0, 0xB6: 0xB1,                      # volume up and down, mute, play/pause, next, previous
            0xB7: 0xB2, 0x18A: 0xB4, 0x192: 0xB7, 0x183: 0xB5,                                        # stop, mail, calculator, media select
            0x223: 0xAC, 0x224: 0xA6, 0x225: 0xA7, 0x227: 0xA8, 0x221: 0xAA, 0x22A: 0xAB}             # browser home, back, forward, refresh, search, favorites


KEYEVENTF_UNICODE = 0x0004
EXTRA_TAG = 0x504B4252                                         # "PKBR": on every event this program injects, so a hook on this PC can tell it from a physical key
ES_SYSTEM_REQUIRED = 0x00000001


def make_input(scan, ext, vk, up, uni=0):
    """One keyboard event. uni is a UTF-16 code unit: the character is delivered as itself (any layout, any language), not as a key position."""
    if uni:
        return INPUT(type=1, ki=KEYBDINPUT(wVk=0, wScan=uni, dwFlags=KEYEVENTF_UNICODE | (KEYUP if up else 0), time=0, dwExtraInfo=EXTRA_TAG))
    flags = (KEYUP if up else 0) | ((SCANCODE | (EXTENDED if ext else 0)) if scan else 0)
    return INPUT(type=1, ki=KEYBDINPUT(wVk=vk, wScan=scan, dwFlags=flags, time=0, dwExtraInfo=EXTRA_TAG))


def send_events(events):
    """Send (scan, ext, vk, up[, unicode]) events in ONE SendInput call so a chord cannot be interleaved with other input. Returns how many went in."""
    if not events:
        return 0
    arr = (INPUT * len(events))(*[make_input(*e) for e in events])
    try:
        kernel32.SetThreadExecutionState(ES_SYSTEM_REQUIRED)       # typing from the phone counts as activity: the PC does not go to sleep mid-sentence
    except OSError:
        pass
    return user32.SendInput(len(events), arr, ctypes.sizeof(INPUT))


MOUSEEVENTF_MOVE, MOUSEEVENTF_WHEEL, MOUSEEVENTF_HWHEEL = 0x0001, 0x0800, 0x1000
MOUSE_BUTTONS = ((1, 0x0002, 0x0004, 0), (2, 0x0008, 0x0010, 0), (4, 0x0020, 0x0040, 0), (8, 0x0080, 0x0100, 1), (16, 0x0080, 0x0100, 2))          # phone bit, down flag, up flag, mouseData: left, right, middle, back (XBUTTON1), forward (XBUTTON2)
MOUSE_MASK = 31          # the bits above: a frame bit outside them is ignored


def make_mouse(dx, dy, data, flags):
    return INPUT(type=0, mi=MOUSEINPUT(dx=dx, dy=dy, mouseData=data & 0xFFFFFFFF, dwFlags=flags, time=0, dwExtraInfo=EXTRA_TAG))


def send_mouse(events):
    """Send (dx, dy, mouseData, flags) mouse events in one call. Returns how many went in."""
    if not events:
        return 0
    arr = (INPUT * len(events))(*[make_mouse(*e) for e in events])
    try:
        kernel32.SetThreadExecutionState(ES_SYSTEM_REQUIRED)
    except OSError:
        pass
    return user32.SendInput(len(events), arr, ctypes.sizeof(INPUT))


def to_i8(b):
    return b - 256 if b > 127 else b


class Mouse:
    """The trackpad: relative moves, buttons held while the phone says so, and wheel notches. A frame carries the whole button state, so a lost finger-up can never leave a button stuck (release_all lifts them)."""

    def __init__(self):
        self.btn = 0

    def events(self, btn, dx, dy, wheel, hwheel):
        ev = []
        if dx or dy:
            ev.append((dx, dy, 0, MOUSEEVENTF_MOVE))
        for bit, down, up, data in MOUSE_BUTTONS:
            if btn & bit and not self.btn & bit:
                ev.append((0, 0, data, down))
            elif self.btn & bit and not btn & bit:
                ev.append((0, 0, data, up))
        if wheel:
            ev.append((0, 0, wheel * 120, MOUSEEVENTF_WHEEL))
        if hwheel:
            ev.append((0, 0, hwheel * 120, MOUSEEVENTF_HWHEEL))
        return ev

    def apply(self, btn, dx, dy, wheel, hwheel):
        ev = self.events(btn & MOUSE_MASK, dx, dy, wheel, hwheel)
        took = send_mouse(ev) if ev else 0
        if ev and took < len(ev):
            log_limited("mouse-refused", "Windows refused some mouse input (a lock screen or a security prompt?)")
            if took:
                self.btn |= btn & MOUSE_MASK                         # a button may be down although the frame said so only in part: the release that follows must cover it
            return
        self.btn = btn & MOUSE_MASK

    def release_all(self):
        self.apply(0, 0, 0, 0, 0)


class State:
    def __init__(self):
        self.mods, self.keys = 0, set()
        self.refused_at = -1e9                                          # when Windows last refused our input (a secure desktop, the lock screen): the phone is told

    def type_unicode(self, cp):
        """Type one UTF-16 code unit as the character itself, on any layout. Modifiers the phone is holding are lifted for it and put back, so a held Ctrl does not turn text into shortcuts."""
        if not 0 < cp <= 0xFFFF:
            return
        ev = [(sc, ext, 0, True) for bit, (sc, ext) in MODS if self.mods & bit]
        ev.append((0, 0, 0, False, cp))
        ev.append((0, 0, 0, True, cp))
        ev += [(sc, ext, 0, False) for bit, (sc, ext) in MODS if self.mods & bit]
        if send_events(ev) < len(ev):
            self.refused_at = time.monotonic()
            log_limited("char-refused", "Windows refused a typed character (a lock screen or a security prompt?)")

    def apply(self, mods, usages):
        new = {u for u in usages if u in SCAN or u == PAUSE}
        ev = []
        for bit, (sc, ext) in MODS:                                  # modifiers go down before the keys and up after them
            if mods & bit and not self.mods & bit:
                ev.append((sc, ext, 0, False))
        for u in sorted(self.keys - new):
            ev.append((0, 0, 0x13, True) if u == PAUSE else (*SCAN[u], 0, True))
        for u in sorted(new - self.keys):
            ev.append((0, 0, 0x13, False) if u == PAUSE else (*SCAN[u], 0, False))
        for bit, (sc, ext) in MODS:
            if not mods & bit and self.mods & bit:
                ev.append((sc, ext, 0, True))
        if ev:
            took = send_events(ev)
            if took < len(ev):
                self.refused_at = time.monotonic()
                if took == 0:
                    log_limited("keys-refused", "Windows refused the input. Trying again on the next key.")
                    return                                           # nothing went in: keep the old state so the next frame tries again
                log_limited("keys-partial", "Windows took only part of the input, so every key is released to be safe.")
                self.mods, self.keys = self.mods | mods, self.keys | new          # some of it is down and we cannot tell which: the release that follows must cover it all
                return
        self.mods, self.keys = mods, new

    def release_all(self):
        self.apply(0, [])


def media_key(usage):
    vk = CONSUMER.get(usage)
    if vk:
        send_events([(0, 0, vk, False), (0, 0, vk, True)])


_stuck = [False]          # set when a link ended while Windows refused the release (a locked screen, a UAC prompt): the main loop keeps trying until Windows takes it
_stuck_items = {"mods": 0, "keys": set(), "btn": 0}          # WHAT was still down, so the next link can lift exactly those (a new link starts with an empty State and would never know about them)


def note_stuck(st, ms):
    if not _stuck[0]:                                             # no flag means nothing is remembered: whatever the memory holds is left from a flag someone cleared directly
        _stuck_items.update({"mods": 0, "keys": set(), "btn": 0})
    _stuck_items["mods"] |= getattr(st, "mods", 0)
    _stuck_items["keys"] |= set(getattr(st, "keys", ()) or ())
    _stuck_items["btn"] |= getattr(ms, "btn", 0)
    _stuck[0] = True


def release_stuck():
    """Lift only what an earlier link left down, now that a new link is up: True when nothing is left. Never lifts what the phone holds on THIS link (release_everything would)."""
    if not _stuck[0]:
        return True
    kev = [(sc, ext, 0, True) for bit, (sc, ext) in MODS if _stuck_items["mods"] & bit] + [(0, 0, 0x13, True) if u == PAUSE else (*SCAN[u], 0, True) for u in sorted(_stuck_items["keys"]) if u in SCAN or u == PAUSE]
    mev = [(0, 0, data, up) for bit, _, up, data in MOUSE_BUTTONS if _stuck_items["btn"] & bit]
    if (send_events(kev) >= len(kev) if kev else True) and (send_mouse(mev) >= len(mev) if mev else True):
        _stuck_items.update({"mods": 0, "keys": set(), "btn": 0})
        _stuck[0] = False
        return True
    return False


def release_everything():
    """Best effort: lift every modifier, every key and every mouse button. True when Windows took all of it."""
    kev = [(sc, ext, 0, True) for _, (sc, ext) in MODS] + [(*SCAN[u], 0, True) for u in sorted(SCAN)] + [(0, 0, 0x13, True)]          # Pause has no scan code (it goes as VK_PAUSE), so it is not in SCAN: lift it by name
    mev = [(0, 0, data, up) for _, _, up, data in MOUSE_BUTTONS]
    took = send_events(kev) >= len(kev) and send_mouse(mev) >= len(mev)
    if took:
        _stuck_items.update({"mods": 0, "keys": set(), "btn": 0})
    return took


def release_stale_modifiers():
    """At start: lift every modifier, in case a previous run died with one held."""
    send_events([(sc, ext, 0, True) for _, (sc, ext) in MODS])


def recv_exact(s, n, deadline=None):
    """n bytes, or OSError. deadline (a time.monotonic() value) is a TOTAL: each recv waits at most the time left, so a peer that sends a byte at a time cannot hold this for the sum of its pauses."""
    b = b""
    cap = s.gettimeout()
    try:
        while len(b) < n:
            if deadline is not None:
                left = deadline - time.monotonic()
                if left <= 0:
                    raise OSError("too slow")
                s.settimeout(max(0.05, min(left, cap) if cap else left))
            c = s.recv(n - len(b))
            if not c:
                raise OSError("closed")
            b += c
    finally:
        if deadline is not None:
            try:
                s.settimeout(cap)
            except OSError:
                pass
    return b


_hs_logged = {}
_dial_notes = {}          # address -> why the latest dial of it failed, for the one line the main loop writes while it looks for the phone
DIAL_LOG_GAP_S = 60.0     # the "looking for the phone" line is written at most this often (and at once after a link ends)


def dial_reason(e):
    """Why a connection attempt failed, in words a person reading the log understands."""
    if isinstance(e, (socket.timeout, TimeoutError)):
        return "no answer (timed out)"
    if isinstance(e, ConnectionRefusedError):
        return "refused (nothing is listening there)"
    if isinstance(e, ConnectionResetError):
        return "reset by the other side"
    if getattr(e, "winerror", None) in (10051, 10065):
        return "no route (that network is not reachable)"
    return "failed (%s)" % type(e).__name__


def note_dial(host, why):
    if len(_dial_notes) > 32 and host not in _dial_notes:          # a scan of a whole network must not grow this without end
        return
    _dial_notes[host] = why


def dial_summary(limit=4):
    """One line for the log from the latest failed dials, then forgotten: 'looking for the phone: 192.168.1.20 no answer (timed out); 127.0.0.1 refused (nothing is listening there)'."""
    items = list(_dial_notes.items())
    _dial_notes.clear()
    if not items:
        return "looking for the phone: no address to try yet (this PC has no private network, or the phone has not been seen)"
    shown = "; ".join("%s %s" % (h, w) for h, w in items[:limit])
    return "looking for the phone: " + shown + ("; and %d more" % (len(items) - limit) if len(items) > limit else "")


def handshake(host, timeout, key):
    """Connect and authenticate in both directions. Returns (socket, Session) or None. The pairing code is never sent; a peer that cannot prove it knows it is dropped before anything else happens."""
    try:
        s = socket.create_connection((host, PORT), timeout=timeout)
    except OSError as e:
        note_dial(host, dial_reason(e))
        return None
    try:
        s.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        s.settimeout(2.0)
        by = time.monotonic() + HANDSHAKE_S
        nc = os.urandom(16)
        s.sendall(b"\x7e" + nc)
        resp = recv_exact(s, 48, by)
        ns, proof = resp[:16], resp[16:]
        if not hmac.compare_digest(proof, LC.proof_phone(key, nc, ns)):
            now = time.monotonic()
            if now - _hs_logged.get(host, -1e9) > 600:                   # something answered like a phone but does not know our code (a different phone, an old code): say so, once
                _hs_logged[host] = now
                log("a device at %s answered but does not know this pairing code (a different phone, or an old code): pair again" % host)
            note_dial(host, "answered but does not know this pairing code")
            s.close()
            return None
        s.sendall(LC.proof_pc(key, nc, ns))
        if recv_exact(s, 1, by) != b"K":
            note_dial(host, "did not accept this PC's proof")
            s.close()
            return None
        s.settimeout(None)
        return s, LC.Session(key, nc, ns, False)
    except OSError as e:
        note_dial(host, "connected, then the check of the code failed: " + dial_reason(e))
    s.close()
    return None


def lan_prefix():
    try:
        u = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        u.connect(("192.0.2.1", 9))                           # no packet is sent; this only picks the outgoing interface
        ip = u.getsockname()[0]
        u.close()
        return ".".join(ip.split(".")[:3]) + ".", ip
    except OSError:
        return None, None


_last_scan = [-1e9]          # the monotonic time of the last sweep: -1e9 means a sweep is due at once (the PC clock stepping back must not stop the scanning)
_scan_gap = [SCAN_EVERY_S]


def grow_scan_gap(gap):
    """The next scan interval after a scan that found nothing: doubled, never above SCAN_MAX_S."""
    return min(gap * 2, SCAN_MAX_S)
_seen_ips = [set()]
# Android's tethering networks: the phone is the gateway. USB tethering 192.168.42.x (the phone is .129), a Wi-Fi hotspot 192.168.43.x (.1), an iPhone-style hotspot 172.20.10.x (.1).
TETHER_NETS = (("192.168.42.", "USB tethering"), ("192.168.43.", "phone hotspot"), ("172.20.10.", "phone hotspot"))
PHONE_GATEWAY_HOSTS = (129, 1)


def link_kind(ip):
    """Which kind of link an address on this PC's networks came over."""
    for prefix, name in TETHER_NETS:
        if ip.startswith(prefix):
            return name
    return "Wi-Fi or network"


def local_ipv4s():
    """Every IPv4 address this PC has right now, on every adapter (not only the one with the default route: a USB-tethered phone is a separate adapter)."""
    ips = set()
    try:
        for r in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET):
            ips.add(r[4][0])
    except OSError:
        pass
    ips.add(lan_prefix()[1] or "")
    return sorted(i for i in ips if i and not i.startswith(("127.", "169.254.", "0.")))


def scannable(ip):
    """Only a private network (a home or office LAN, a tether, carrier-grade NAT) is ever probed for the phone: never a network with a public address, which would be a port scan of somebody else's range."""
    try:
        a = ipaddress.ip_address(ip)
    except ValueError:
        return False
    return a.is_private or a in ipaddress.ip_network("100.64.0.0/10")


MAX_PREFIXES_TOTAL = 6          # over ALL networks: a PC with several virtual adapters (Hyper-V, WSL, a VPN) must not sweep thousands of addresses every few seconds
MAX_PREFIXES_PER_NET = 4          # a /22 (1,022 hosts): a wider network is searched around this PC's own /24 only this far


class IP_ADDR_STRING(ctypes.Structure):
    pass


IP_ADDR_STRING._fields_ = [("Next", ctypes.POINTER(IP_ADDR_STRING)), ("IpAddress", ctypes.c_char * 16), ("IpMask", ctypes.c_char * 16), ("Context", wt.DWORD)]


class IP_ADAPTER_INFO(ctypes.Structure):
    pass


IP_ADAPTER_INFO._fields_ = [("Next", ctypes.POINTER(IP_ADAPTER_INFO)), ("ComboIndex", wt.DWORD), ("AdapterName", ctypes.c_char * 260), ("Description", ctypes.c_char * 132), ("AddressLength", wt.UINT),
                            ("Address", ctypes.c_ubyte * 8), ("Index", wt.DWORD), ("Type", wt.UINT), ("DhcpEnabled", wt.UINT), ("CurrentIpAddress", ctypes.POINTER(IP_ADDR_STRING)), ("IpAddressList", IP_ADDR_STRING)]


def local_masks():
    """{this PC's IPv4 address: its netmask} from the adapters (Windows GetAdaptersInfo), so a /23 or /22 is searched as the network it is and not only the /24 the PC happens to sit in. {} when it cannot be read."""
    out = {}
    try:
        size = wt.ULONG(0)
        lib = ctypes.windll.iphlpapi
        lib.GetAdaptersInfo(None, ctypes.byref(size))
        if not size.value or size.value > 1 << 20:
            return out
        buf = ctypes.create_string_buffer(size.value)
        if lib.GetAdaptersInfo(buf, ctypes.byref(size)) != 0:
            return out
        node = ctypes.cast(buf, ctypes.POINTER(IP_ADAPTER_INFO))
        for _ in range(64):
            if not node:
                break
            item = ctypes.pointer(node.contents.IpAddressList)
            for _j in range(32):
                if not item:
                    break
                ip, mask = item.contents.IpAddress.decode("ascii", "ignore"), item.contents.IpMask.decode("ascii", "ignore")
                if ip and mask and ip != "0.0.0.0":
                    out[ip] = mask
                item = item.contents.Next
            node = node.contents.Next
    except (OSError, AttributeError, ValueError):
        return {}
    return out


def scan_prefixes(ips, masks=None, primary=None):
    """The /24 networks to search, tethering networks first (a cable is the likeliest thing someone just plugged in), then the one with the default route (`primary`, this PC's address on it: the Wi-Fi or cable it is really on, so
    a PC with many virtual adapters still sweeps it), each once. With the netmask of an address (`masks`: address -> mask) a network wider than a /24 contributes the other /24s inside it too, this PC's own first, at
    most MAX_PREFIXES_PER_NET of them, and only ones that are themselves private (a mask must never lead the sweep onto a public range)."""
    owns, neighbours = [], []
    for ip in sorted((i for i in ips if scannable(i)), key=lambda i: 0 if link_kind(i) != "Wi-Fi or network" else 1 if i == primary else 2):
        own = ".".join(ip.split(".")[:3]) + "."
        group = []
        mask = (masks or {}).get(ip)
        if mask:
            try:
                net = ipaddress.ip_network("%s/%s" % (ip, mask), strict=False)
                if net.prefixlen >= 31:
                    continue          # a host route (a VPN's /32, a point-to-point /31) has no neighbours and is not a network to sweep
                if net.prefixlen < 24:
                    base = int(net.network_address)
                    own_k = (int(ipaddress.ip_address(own + "0")) - base) // 256
                    near = sorted(range(max(0, own_k - 8), min(net.num_addresses // 256, own_k + 9)), key=lambda k: abs(k - own_k))          # the /24s closest to this PC's own, in the network's own numbering
                    others = [".".join(str(ipaddress.ip_address(base + 256 * k)).split(".")[:3]) + "." for k in near]
                    group += [p for p in others if p != own and scannable(p + "1")][:MAX_PREFIXES_PER_NET - 1]
            except ValueError:
                pass
        owns.append(own)
        neighbours += group
    return list(dict.fromkeys(owns + neighbours))[:MAX_PREFIXES_TOTAL]          # every network's own /24 first, then the neighbours inside a wider network, at most MAX_PREFIXES_TOTAL


def read_last():
    try:
        t = open(LAST_FILE, encoding="utf-8").read().strip()
        return str(ipaddress.IPv4Address(t))
    except (OSError, ValueError):
        return ""


NO_ADB = os.environ.get("TYPEFERRY_NO_ADB", "").strip().lower() in ("1", "true", "yes")          # test switch: never use the adb forward, so the network paths can be exercised while a cable is plugged in ("0" or "false" leaves it off)
KNOWN_FILE = os.path.join(DATA, "known_phones.txt")
KIND_NAMES = {1: "USB cable", 2: "Wi-Fi", 3: "phone hotspot"}
MAX_KNOWN = 8


def read_known():
    """[(ip, kind, seen_at)], newest first: the addresses the phone says it has (it tells the PC over the link), so when a link dies the PC can try the others at once instead of scanning."""
    out = []
    try:
        for line in open(KNOWN_FILE, encoding="utf-8").read().splitlines():
            p = line.split()
            if len(p) == 3:
                try:
                    out.append((str(ipaddress.IPv4Address(p[0])), int(p[1]), float(p[2])))
                except ValueError:
                    pass
    except OSError:
        pass
    return sorted(out, key=lambda x: -x[2])


def remember_known(ip, kind, now=None):
    """Note one of the phone's addresses (kind 1 USB cable, 2 Wi-Fi, 3 phone hotspot). Loopback, link-local, multicast, a public address (the receiver only ever probes private networks), an unknown kind and nonsense are ignored; the list keeps the eight newest."""
    try:
        a = ipaddress.IPv4Address(ip)
    except ValueError:
        return
    if a.is_loopback or a.is_link_local or a.is_unspecified or a.is_multicast or not scannable(str(a)):
        return
    if kind not in KIND_NAMES:          # a frame from a peer that holds the code but is not this app: the kind is 1, 2 or 3 and nothing else
        return
    now = time.time() if now is None else now
    kept = [x for x in read_known() if x[0] != str(a)]
    now = max([now] + [x[2] + 1 for x in kept])          # the report just received is the newest by definition: a clock that stepped back (or one that was wrong once and is right now) must not leave stored stamps ahead of it that push the new address out
    items = sorted(kept + [(str(a), int(kind), now)], key=lambda x: -x[2])[:MAX_KNOWN]
    tmp = KNOWN_FILE + ".tmp"
    try:
        with open(tmp, "w", encoding="utf-8") as f:
            f.write("".join("%s %d %.0f\n" % x for x in items))
        os.replace(tmp, KNOWN_FILE)
    except OSError:
        pass


def prefix_of(ip):
    return ".".join(str(ip).split(".")[:3]) + "."


def reachable_known(mine_all, masks=None, primary=None):
    """The known phone addresses on a network this PC is on right now (its own /24s, and with `masks` the /24s inside a wider network, the same set the sweep uses). An address on a network that is gone (a cable that was
    unplugged) is not tried."""
    prefixes = set(scan_prefixes(mine_all, masks, primary)) if masks is not None else {prefix_of(i) for i in mine_all}
    return [(ip, kind) for ip, kind, _ in read_known() if prefix_of(ip) in prefixes]


def kind_of(ip):
    for k_ip, kind, _ in read_known():
        if k_ip == ip:
            return kind
    return 0


def link_rank(how):
    """Lower is better: the adb cable 0, a USB cable network 1, anything else 2."""
    return 0 if how == "USB" else 1 if how.startswith(("USB cable", "USB tethering")) else 2


def find_better(how, key, handshake_fn=None, port_fn=None, locals_fn=None):
    """While one link carries the keys, see whether a better one has appeared (the cable plugged in). Returns an authenticated (socket, session, how) on it, or None. Make-before-break: the phone accepts the second connection and drops the first, so no keys are lost in between."""
    handshake_fn = handshake_fn or handshake
    port_fn = port_fn or port_open
    locals_fn = locals_fn or local_ipv4s
    rank = link_rank(how)
    if rank > 0 and not NO_ADB and port_fn("127.0.0.1", 0.15):
        r = handshake_fn("127.0.0.1", 0.5, key)
        if r:
            return r[0], r[1], "USB"
    if rank > 1:
        for ip, kind in reachable_known(locals_fn(), local_masks(), lan_prefix()[1]):
            if kind == 1 and ip not in how:
                r = handshake_fn(ip, 0.6, key)
                if r:
                    return found(r, ip)
    return None


def find_phone(key):
    """A connected, authenticated (socket, session, how) to the phone, or None: the USB forward first, then the phone's known addresses on networks this PC is on (newest first), the last address, then a scan of every network at most every SCAN_EVERY_S seconds."""
    if not NO_ADB:
        r = handshake("127.0.0.1", 0.3, key)
        if r:
            return r[0], r[1], "USB"
    mine_all = local_ipv4s()
    masks = local_masks()
    primary = lan_prefix()[1]
    prefixes = scan_prefixes(mine_all, masks, primary)
    tried = set()
    for ip, kind in reachable_known(mine_all, masks, primary):
        tried.add(ip)
        r = handshake(ip, 0.5, key)
        if r:
            return found(r, ip)
    last = read_last()
    if last and last not in tried and prefix_of(last) in prefixes:          # the last address only on a network this PC is on now: the policy says it looks for the phone only there
        r = handshake(last, 0.6, key)
        if r:
            return found(r, last)
    if set(mine_all) != _seen_ips[0]:          # a network adapter appeared or went (a USB cable with tethering plugged in): look at once instead of waiting out the timer
        _seen_ips[0] = set(mine_all)
        _last_scan[0] = -1e9
        _scan_gap[0] = SCAN_EVERY_S
    own_prefixes = {prefix_of(i) for i in mine_all}
    for prefix in prefixes:                    # a phone that shares its connection is the gateway of that network, at a few well-known addresses: ask those first (two quick connects per tethering network, so the scan's backoff never holds them back; other networks wait for the backed-off sweep)
        if prefix not in own_prefixes or link_kind(prefix + "1") == "Wi-Fi or network":          # judged by an address this PC HAS: a neighbour inside an office /22 that looks like a tether range is not one
            continue
        for host in PHONE_GATEWAY_HOSTS:
            ip = prefix + str(host)
            if ip in mine_all or ip == last:
                continue
            r = handshake(ip, 0.5, key)
            if r:
                return found(r, ip)
    if time.monotonic() - _last_scan[0] < _scan_gap[0]:
        return None
    _last_scan[0] = time.monotonic()

    def probe(ip):
        try:
            socket.create_connection((ip, PORT), timeout=0.35).close()
            return ip
        except OSError:
            return None
    cands = [prefix + str(i) for prefix in prefixes for i in range(1, 255) if prefix + str(i) not in mine_all and prefix + str(i) != last]
    with concurrent.futures.ThreadPoolExecutor(max_workers=64) as ex:
        openhosts = [ip for ip in ex.map(probe, cands) if ip][:SCAN_MAX_HOSTS]
    budget = time.monotonic() + SCAN_BUDGET_S
    for ip in openhosts:
        if time.monotonic() > budget:
            break
        r = handshake(ip, 0.8, key)
        if r:
            return found(r, ip)
    _scan_gap[0] = grow_scan_gap(_scan_gap[0])                        # nothing there: look less often, so an idle PC on a work or guest network is not probed every half minute for ever
    return None


def found(r, ip):
    """Remember the address of the phone that answered and name the kind of link it came over (USB tethering, a phone hotspot, or ordinary Wi-Fi)."""
    _scan_gap[0] = SCAN_EVERY_S
    try:
        open(LAST_FILE, "w", encoding="utf-8").write(ip)
    except OSError:
        pass
    return r[0], r[1], "%s (%s)" % (KIND_NAMES.get(kind_of(ip)) or link_kind(ip), ip)


def led_bits():
    """Caps, Num and Scroll Lock as bits 0, 1, 2 (the toggle state Windows keeps)."""
    g = user32.GetKeyState
    return (1 if g(0x14) & 1 else 0) | (2 if g(0x90) & 1 else 0) | (4 if g(0x91) & 1 else 0)


user32.OpenInputDesktop.restype = ctypes.c_void_p
user32.OpenInputDesktop.argtypes = (wt.DWORD, wt.BOOL, wt.DWORD)
user32.CloseDesktop.argtypes = (ctypes.c_void_p,)


def input_blocked():
    """True when this program cannot type right now because the input desktop is not ours: the lock screen, the sign-in screen or a UAC prompt (the secure desktop). The phone is told, so it can say so instead of typing into nothing."""
    try:
        h = user32.OpenInputDesktop(0, False, 0x0100)                  # DESKTOP_SWITCHDESKTOP
    except OSError:
        return False
    if h:
        user32.CloseDesktop(h)
        return False
    return True


class FILTERKEYS(ctypes.Structure):
    _fields_ = [("cbSize", wt.UINT), ("dwFlags", wt.DWORD), ("iWaitMSec", wt.DWORD), ("iDelayMSec", wt.DWORD), ("iRepeatMSec", wt.DWORD), ("iBounceMSec", wt.DWORD)]


def filter_keys_on():
    """True when Windows Filter Keys is on: it can drop very short key taps, which a phone sends."""
    try:
        fk = FILTERKEYS(cbSize=ctypes.sizeof(FILTERKEYS))
        return bool(user32.SystemParametersInfoW(0x0032, ctypes.sizeof(FILTERKEYS), ctypes.byref(fk), 0) and fk.dwFlags & 1)          # SPI_GETFILTERKEYS, FKF_FILTERKEYSON
    except OSError:
        return False


STATUS_BLOCKED, STATUS_FILTERKEYS = 1, 2


def compute_status(refused_at, now, blocked, filterkeys):
    """The status byte sent to the phone: bit 0 input is blocked (locked, sign-in, UAC, or Windows just refused our keys), bit 1 Filter Keys is on."""
    return (STATUS_BLOCKED if blocked or now - refused_at < 3.0 else 0) | (STATUS_FILTERKEYS if filterkeys else 0)


def app_hash(exe):
    """Six bytes that stand for a program name (FNV-1a over the lower-case name, low 48 bits): the phone matches a profile to the program in front without the program's name or window title ever being sent."""
    h = 0xCBF29CE484222325
    for b in exe.strip().lower().encode("utf-8"):
        h = ((h ^ b) * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return (h & 0xFFFFFFFFFFFF).to_bytes(6, "big")


user32.GetForegroundWindow.restype = ctypes.c_void_p
user32.GetWindowThreadProcessId.argtypes = (ctypes.c_void_p, ctypes.POINTER(wt.DWORD))
kernel32.OpenProcess.restype = ctypes.c_void_p
kernel32.OpenProcess.argtypes = (wt.DWORD, wt.BOOL, wt.DWORD)
kernel32.QueryFullProcessImageNameW.argtypes = (ctypes.c_void_p, wt.DWORD, wt.LPWSTR, ctypes.POINTER(wt.DWORD))
kernel32.CloseHandle.argtypes = (ctypes.c_void_p,)


def foreground_exe():
    """The file name of the program whose window is in front ('' when it cannot be read: an elevated program, the secure desktop)."""
    try:
        hwnd = user32.GetForegroundWindow()
        if not hwnd:
            return ""
        pid = wt.DWORD(0)
        user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
        h = kernel32.OpenProcess(0x1000, False, pid.value)               # PROCESS_QUERY_LIMITED_INFORMATION
        if not h:
            return ""
        try:
            buf = ctypes.create_unicode_buffer(520)
            n = wt.DWORD(520)
            if kernel32.QueryFullProcessImageNameW(h, 0, buf, ctypes.byref(n)):
                return os.path.basename(buf.value).lower()
        finally:
            kernel32.CloseHandle(h)
    except OSError:
        pass
    return ""


def led_sender(sock, sess, stop, st, shared):
    """Tell the phone the lock-key state and the input status when they change and every 2 s (that is also the heartbeat the phone listens for), and, only while the phone has asked for it, which program is in front."""
    last, at, app_last, app_at = None, 0.0, None, 0.0
    while not stop.is_set():
        now = time.monotonic()
        cur = (led_bits(), compute_status(st.refused_at, now, input_blocked(), filter_keys_on()))
        if cur != last or now - at >= 2.0:
            try:
                sock.sendall(sess.seal(bytes([3, cur[0], cur[1], 0, 0, 0, 0, 0])))
            except OSError:
                return
            last, at = cur, now
        if shared.get("watch"):
            app = app_hash(foreground_exe())
            if app != app_last or now - app_at >= 3.0:
                try:
                    sock.sendall(sess.seal(bytes([7]) + app + bytes([0])))
                except OSError:
                    return
                app_last, app_at = app, now
        else:
            app_last = None
        stop.wait(0.25)


_handoff = threading.Lock()
_late_link = [None]
_late_event = threading.Event()          # set when a link is parked: the main loop's pause ends at once instead of after its full two seconds


def park_late_link(link):
    """A better link was found just after the link it was looking beside had ended. The phone has already dropped that old link in its favour, so this one is the live link: keep it for the main loop (take_late_link) and never close it. One parking place; an older parked link, if any, is closed."""
    with _handoff:
        old, _late_link[0] = _late_link[0], link
        _late_event.set()
    if old is not None:
        try:
            old[0].close()
        except OSError:
            pass


def take_late_link():
    with _handoff:
        link, _late_link[0] = _late_link[0], None
        _late_event.clear()
    return link


def watch_better(how, key, stop, shared):
    """Every couple of seconds, off the typing path, look for a better link than the one in use. The link found goes to exactly one owner, decided under shared['lock']: serve() while it is still running (through shared['better']), or the main loop once serve() has finished (park_late_link). Never closed, so the phone, which has already dropped the old link for it, is never left with nothing. (A connection attempt can take half a second: it must never run in the loop that receives keys.)"""
    while not stop.wait(2.0):
        try:
            better = find_better(how, key() if callable(key) else key)          # asked every time: a code changed by the pairing window must be used by the very next look
        except Exception:
            better = None
        if better:
            with shared["lock"]:
                if not shared["done"]:
                    shared["better"] = better
                    return
            park_late_link(better)                                    # serve() has already finished
            return


def serve(sock, sess, how="", key=None):
    """Carry the phone's keys until the link ends. Returns None then, or, when a better link appeared meanwhile (the cable plugged in), the authenticated (socket, session, how) of that link so the caller carries on there."""
    st = State()
    ms = Mouse()
    shared = {"watch": False, "lock": threading.Lock(), "done": False}
    stop = threading.Event()
    upgrade = None
    late = None
    rx = {"buf": b"", "at": time.monotonic()}
    revoked0 = KEYS[0].revoked if KEYS[0] is not None else 0
    link_key = getattr(sess, "key", None)                             # the key this link was made with (a fake session in a test has none)
    checked = [-1e9]

    def revoked():
        """True when this link was made with a code that is no longer the one on disk, or the pairing was deleted while it was up. The store is asked itself (one stat, at most every half second), so a code changed between the handshake and this
        point, or while a scan or a better-link handshake was running, ends the link at its first frame and not only at the watcher's next look."""
        ks = KEYS[0]
        if ks is None:
            return False
        now = time.monotonic()
        if now - checked[0] >= 0.5:
            checked[0] = now
            ks.get()
        return ks.revoked != revoked0 or (link_key is not None and ks.key != link_key)

    def pump(chunk):
        """Frames out of what arrived: whole 16 byte frames are opened and applied, a partial one waits for the rest."""
        if revoked():
            log("the pairing was deleted or changed while this link was up: connection closed")
            raise OSError("pairing deleted")                          # the old or lost phone stops working, as the policy says: this link ends through the cleanup below
        buf = rx["buf"] + chunk
        if _stuck[0]:
            release_stuck()                                           # what an earlier link left down goes up before this link's first key (a Wi-Fi blip while the PC was locked)
        while len(buf) >= 16:
            wire, buf = buf[:16], buf[16:]
            f = sess.open(wire)
            if f is None:
                rx["buf"] = buf
                log("a frame failed its check: connection closed")
                raise OSError("bad frame")                           # ends this link through the cleanup below, which still hands over a better link found meanwhile
            rx["at"] = time.monotonic()                              # only a frame that verified counts as the phone being there: loose bytes (a relay dripping one at a time) must not keep a key held
            LINK.touch(time.monotonic())
            if f[0] == 1:
                st.apply(f[1], [b for b in f[2:8] if b])
            elif f[0] == 2:
                media_key(f[1] | (f[2] << 8))
            elif f[0] == 5:
                st.type_unicode(f[1] | (f[2] << 8))
            elif f[0] == 6:
                ms.apply(f[1], to_i8(f[2]), to_i8(f[3]), to_i8(f[4]), to_i8(f[5]))
            elif f[0] == 8:
                shared["watch"] = bool(f[1])
            elif f[0] == 9:
                remember_known("%d.%d.%d.%d" % (f[2], f[3], f[4], f[5]), f[1])          # one of the phone's own addresses: kept for the next time a link dies
        rx["buf"] = buf

    _ever_served[0] = True
    try:
        threading.Thread(target=led_sender, args=(sock, sess, stop, st, shared), daemon=True).start()
        if key is not None:
            threading.Thread(target=watch_better, args=(how, key, stop, shared), daemon=True).start()          # key may be a function (the main loop passes KEYS.get)
        sock.settimeout(1.0)
        while not QUIT.is_set():                                      # Quit ends the link here (within the socket's one second timeout), and the finally below lifts every key and button
            better = shared.get("better")
            if better:
                upgrade = better
                log("a better link appeared: switching to " + better[2])
                sock.settimeout(0.3)                                  # the phone is closing this link: take what it still had to say (text, media keys) before leaving it
                end = time.monotonic() + 0.5
                while time.monotonic() < end:
                    try:
                        chunk = sock.recv(256)
                    except (socket.timeout, OSError):
                        break
                    if not chunk:
                        break
                    pump(chunk)
                break
            try:
                chunk = sock.recv(256)
            except socket.timeout:
                if time.monotonic() - rx["at"] > QUIET_S:
                    log("the phone went quiet: every key released")
                    break
                if revoked():
                    log("the pairing was deleted or changed while this link was up: connection closed")
                    break
                continue
            if not chunk:
                break
            pump(chunk)
    except OSError:
        pass
    except Exception:
        log("error in the link: " + traceback.format_exc().replace("\n", " | "))
    finally:
        stop.set()
        with shared["lock"]:                                          # from here a link the watcher finds is parked for the main loop; one it stored before this point is taken just below
            shared["done"] = True
            late = shared.get("better")
        try:
            st.release_all()
            ms.release_all()
            if getattr(st, "mods", 0) or getattr(st, "keys", None) or getattr(ms, "btn", 0):                          # Windows refused the release: do not forget it with the link
                note_stuck(st, ms)
        finally:
            sock.close()
    if late and upgrade is None:                                      # the phone drops the old link the moment it accepts the better one, so this link can end BEFORE the loop above notices the better one: carry on there, never close it (closing it made the link flap)
        upgrade = late
        log("a better link appeared as the old one ended: switching to " + late[2])
    return upgrade


def adb_run(path, *args):
    return subprocess.run([path, *args], capture_output=True, text=True, timeout=8, creationflags=0x08000000).stdout


def adb_devices(path):
    out = adb_run(path, "devices").splitlines()[1:]
    return [ln.split()[0] for ln in out if len(ln.split()) >= 2 and ln.split()[1] == "device"]


def adb_forward_keeper():
    """While exactly one phone is plugged in, keep `adb forward` pointing this PC's 127.0.0.1:PORT at the phone's PORT (no console window). Parses the list exactly; with two phones it does nothing."""
    path = shutil.which("adb")
    if not path:
        return
    named = ""
    while True:
        try:
            devs = adb_devices(path)
            if len(devs) == 1:
                if devs[0] != named:                                   # the phone's model name, for the status window, asked once per phone
                    named = devs[0]
                    LINK.usb_name = clean_name(adb_run(path, "-s", named, "shell", "getprop", "ro.product.model"))
                want = "tcp:%d" % PORT
                fl = [ln.split() for ln in adb_run(path, "forward", "--list").splitlines()]
                if not any(len(p) >= 3 and p[0] == devs[0] and p[1] == want and p[2] == want for p in fl):
                    adb_run(path, "-s", devs[0], "forward", want, want)
        except (OSError, subprocess.SubprocessError):
            pass
        time.sleep(15)


def push_code(code):
    """--push-code: hand the pairing code to the one USB-connected phone (the app takes it from this broadcast, so nobody types it)."""
    path = shutil.which("adb")
    devs = adb_devices(path) if path else []
    if len(devs) != 1:
        print("Need exactly one phone connected over USB with USB debugging on (found %d)." % len(devs))
        return 1
    out = adb_run(path, "-s", devs[0], "shell", "am", "broadcast", "-n", "io.github.exalt24.phonekb/.TestReceiver", "-a", "io.github.exalt24.phonekb.TEST", "--es", "token", code)
    print("sent" if "Broadcast completed" in out else out)
    return 0


def install_own_copy(exe, data):
    """The path to register for starting with Windows: the program's own copy inside its data folder, made now if it is not there (the download, usually in Downloads, may be deleted or moved at any time, which would silently end the receiver and with it the person's only way to type). If the copy cannot be made the running file's own path is used, or an earlier copy that is in use."""
    target = os.path.join(data, "TypeferryReceiver.exe")
    if os.path.normcase(os.path.abspath(exe)) == os.path.normcase(os.path.abspath(target)):
        return target
    try:
        os.makedirs(data, exist_ok=True)
        tmp = target + ".new"
        shutil.copy2(exe, tmp)
        os.replace(tmp, target)
        log("copied the program to %s so starting with Windows does not depend on where it was downloaded" % target)
        return target
    except OSError as e:
        log("could not copy the program into its own folder (%s)" % e)
        try:
            os.remove(target + ".new")
        except OSError:
            pass
        return target if os.path.exists(target) else exe


def ensure_autostart():
    """The packaged program starts with Windows (a per-user Run entry, no administrator needed), so the person installs it once and never thinks about it again. The script form keeps its own Startup shortcut."""
    if not FROZEN or os.path.exists(AUTOSTART_OFF_FILE):          # a person who removed it keeps that choice (the receiver starts again by hand, and the entry stays off)
        return
    if ISOLATED_RUN:          # a test or second instance (its own data folder or instance name) must never touch the person's per-user Run key: a smoke run of the exe once pointed the real startup entry at a throw-away copy that was then deleted (2026-10-19)
        return
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Windows\CurrentVersion\Run", 0, winreg.KEY_SET_VALUE | winreg.KEY_QUERY_VALUE) as k:
            want = '"%s"' % install_own_copy(sys.executable, DATA)
            try:
                if winreg.QueryValueEx(k, "TypeferryReceiver")[0] == want:
                    return
            except OSError:
                pass
            winreg.SetValueEx(k, "TypeferryReceiver", 0, winreg.REG_SZ, want)
            log("registered to start with Windows")
    except OSError:
        log("could not register to start with Windows")


def autoyes_enabled(environ=None, frozen=None):
    """The test switch that types the second number for the person: only unfrozen, only for 1, true or yes, and only when a test also named the signal file it waits for (TYPEFERRY_AUTOYES_GO), so a stray variable in a normal run does nothing."""
    environ = os.environ if environ is None else environ
    frozen = getattr(sys, "frozen", False) if frozen is None else frozen
    return environ.get("TYPEFERRY_TEST_AUTOYES", "").strip().lower() in ("1", "true", "yes") and bool(environ.get("TYPEFERRY_AUTOYES_GO")) and not frozen


def startup_registered():
    """True when the packaged program is set to start with Windows (its per-user Run entry exists)."""
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Windows\CurrentVersion\Run", 0, winreg.KEY_QUERY_VALUE) as k:
            winreg.QueryValueEx(k, "TypeferryReceiver")
            return True
    except OSError:
        return False


def remove_startup():
    """Delete the Run entry. True when there was one to delete."""
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, r"Software\Microsoft\Windows\CurrentVersion\Run", 0, winreg.KEY_SET_VALUE) as k:
            winreg.DeleteValue(k, "TypeferryReceiver")
            return True
    except OSError:
        return False


def remember_startup_off():
    """Write the file that keeps the start with Windows entry off: the receiver never puts it back on its own (the tray's Remove from startup and --uninstall both leave it)."""
    try:
        with open(AUTOSTART_OFF_FILE, "w", encoding="utf-8") as f:
            f.write(time.strftime("%Y-%m-%d %H:%M:%S"))
    except OSError:
        pass


def uninstall():
    """--uninstall: stop the receiver starting with Windows (the one thing the program set up outside its own folder) and say how to finish removing it."""
    removed = remove_startup()
    remember_startup_off()          # the next start must not register it again: the dialog below says it will no longer start with Windows
    text = ("The receiver will no longer start with Windows." if removed else "The receiver was not set to start with Windows.") + (
        "\n\nTo stop it now, choose Quit in its tray icon menu. To remove it completely, delete the program and the folder " + DATA + ".")
    try:
        ctypes.windll.user32.MessageBoxW(None, text, APP_NAME, 0x40)
    except (AttributeError, OSError):
        pass
    log("uninstall: " + ("removed the start with Windows entry" if removed else "nothing to remove"))
    return 0


def duplicate_start_action(running, my_data, my_version, now):
    """What a second start does when another receiver already holds the mutex. running is (data folder, version, started) of the one that holds it, or None when that is not known.
    Returns ("silent", None), ("window", None) or ("message", text): a copy from another folder or another version must never exit without a word (the person would believe the new program is the one running)."""
    if running is None:
        return ("window", None)
    data, version, started = running
    if os.path.normcase(os.path.abspath(data)) != os.path.normcase(os.path.abspath(my_data)):
        return ("message", "Another copy runs from a different folder (%s). Quit it, then open this one again." % data)
    if version != my_version:
        return ("replace", "The receiver is already running and is version %s; this one is version %s. Replace the running one with this one?" % (version, my_version))
    elapsed = now - started
    if elapsed < 0 or elapsed > DUPLICATE_START_S:                    # running for a while: the person opened it again on purpose, which is how they find the pairing window they lost
        return ("window", None)
    return ("silent", None)                                           # two things starting it at login within the same minute


def running_pid():
    """The process id of the receiver that holds the mutex (4th line of the note), or 0."""
    try:
        return int(open(RUNNING_FILE, encoding="utf-8").read().split("\n")[3])
    except (OSError, ValueError, IndexError):
        return 0


def pid_is_receiver(pid):
    """True only when pid is really a receiver (a stale note must never make us end some other program)."""
    if pid <= 0:
        return False
    try:
        out = subprocess.run(["tasklist", "/FI", "PID eq %d" % pid, "/FO", "CSV", "/NH"], capture_output=True, text=True, timeout=15, creationflags=0x08000000).stdout.lower()
    except (OSError, subprocess.SubprocessError):
        return False
    return any(name in out for name in ("typeferryreceiver.exe", "pythonw.exe", "python.exe"))


def ask_person(text):
    """A yes or no box for a windowless program."""
    try:
        return ctypes.windll.user32.MessageBoxW(0, text, APP_NAME, 0x24 | 0x40000) == 6
    except (AttributeError, OSError):
        return False


def read_running():
    """(data folder, version, started) written by the receiver that holds the mutex, or None."""
    try:
        data, version, started = open(RUNNING_FILE, encoding="utf-8").read().split("\n")[:3]
        return data, version, float(started)
    except (OSError, ValueError):
        return None


def tell_person(text):
    """A message box (the receiver has no window of its own): the only way a windowless program can say something."""
    try:
        ctypes.windll.user32.MessageBoxW(0, text, APP_NAME, 0x40 | 0x40000)
    except (AttributeError, OSError):
        log("could not show a message: " + text)


def open_pair_window():
    """Show the pairing code in its own window (a child process, so it never blocks the receiver). Used when no phone has ever connected: the person has nowhere else to find the code."""
    try:
        cmd = [sys.executable, "--pair"] if FROZEN else [sys.executable, os.path.abspath(__file__), "--pair"]
        env = dict(os.environ, PYINSTALLER_RESET_ENVIRONMENT="1")          # a one-file exe's child would otherwise share the parent's temporary folder, which the parent deletes when it exits a moment later: the window would lose its Tk files
        subprocess.Popen(cmd, creationflags=0x00000008 | 0x00000200, env=env)          # detached, new process group
    except OSError:
        log("could not open the pairing window")


def port_open(host, timeout):
    try:
        socket.create_connection((host, PORT), timeout=timeout).close()
        return True
    except OSError:
        return False


def open_hosts():
    """Every host on any of this PC's networks that has the keyboard port open, likeliest first: the USB forward, the last address, then each adapter's whole /24 (Wi-Fi, a USB tethering network, a phone hotspot)."""
    mine = local_ipv4s()
    prefixes = scan_prefixes(mine, local_masks(), lan_prefix()[1])
    last = read_last()
    last = last if last and prefix_of(last) in prefixes else ""          # the last address only on a network this PC is on now (the rule find_phone follows): a stale one may belong to another device by now
    hosts = [h for h in ("127.0.0.1", last) if h and port_open(h, 0.3)]
    cands = [p + str(i) for p in prefixes for i in range(1, 255) if p + str(i) not in mine and p + str(i) not in hosts]

    def probe(ip):
        return ip if port_open(ip, 0.35) else None
    with concurrent.futures.ThreadPoolExecutor(max_workers=64) as ex:
        hosts += [ip for ip in ex.map(probe, cands) if ip]
    return hosts


def check_matches(typed, expected):
    """True when what the person typed (spaces, dashes and other marks ignored) is exactly the six digits expected."""
    digits = "".join(str(unicodedata.digit(ch)) for ch in typed if unicodedata.category(ch) == "Nd")
    return len(digits) == 6 and hmac.compare_digest(digits.encode(), expected.encode())


def phone_said_no(s):
    """True when the phone has already hung up or sent a 'no' (looked at without taking the bytes), so a prompt waiting for the person can stop at once."""
    try:
        readable, _, _ = select.select([s], [], [], 0)
        if not readable:
            return False
        return s.recv(1, socket.MSG_PEEK) != b"Y"
    except OSError:
        return True


def pair_with(host, decide, on_probe=None):
    """Pair with the phone at host by typed numbers (protocol in linkcrypto.py). decide(sas, check) is called with the first six digits (the person types them on the phone) and the second six digits (the phone shows
    them only after a right entry; the person types them here): it returns True only when the person typed the second number correctly. on_probe(f), when given, receives a function that says whether the phone has already said no.
    Returns the new 16 character code, the string 'declined' when either side said no, or None when that host is not a phone that is asking to pair (the normal answer from everything else)."""
    try:
        s = socket.create_connection((host, PORT), timeout=1.5)
    except OSError:
        return None
    try:
        s.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        s.settimeout(4.0)
        priv, pub = LC.dh_keypair()
        nc = os.urandom(16)
        pcb = LC.pub_bytes(pub)
        s.sendall(bytes([LC.PAIR_HELLO]) + LC.pair_commit(pcb, nc))
        by = time.monotonic() + PAIR_EXCHANGE_S                        # one deadline for the whole first exchange: a host that answers a byte at a time does not hold the pairing window
        resp = recv_exact(s, LC.PUB_LEN + 16, by)                      # a phone that is not asking to pair closes the connection here
        phb, ns = resp[:LC.PUB_LEN], resp[LC.PUB_LEN:]
        peer = int.from_bytes(phb, "big")
        if not LC.valid_pub(peer):
            return None
        s.sendall(pcb + nc)
        kz = LC.pair_secret(priv, peer)
        t = LC.pair_transcript(pcb, nc, phb, ns)
        if on_probe:
            on_probe(lambda: phone_said_no(s))
        same = bool(decide(LC.pair_sas(kz, t), LC.pair_check(kz, t)))
        s.sendall((b"Y" + LC.pair_confirm(kz, b"pc", t)) if same else (b"N" + bytes(32)))
        if not same:
            return "declined"
        s.settimeout(135.0)
        theirs = recv_exact(s, 33, time.monotonic() + 135.0)
        if theirs[:1] == b"Y" and hmac.compare_digest(theirs[1:], LC.pair_confirm(kz, b"phone", t)):
            s.settimeout(PAIR_K_S)
            if recv_exact(s, 1, time.monotonic() + PAIR_K_S) != b"K":                              # the phone says K once it has stored the new code: until then a phone that was cancelled or went away must not leave this PC alone holding a code
                return "declined"
            return LC.pair_code(kz, t)
        return "declined"
    except OSError:
        return None
    finally:
        try:                                                          # closing with the phone's bytes unread would reset the connection and could throw our answer away before the phone reads it
            s.shutdown(socket.SHUT_WR)
            s.settimeout(0.5)
            end_drain = time.monotonic() + 1.0                        # a host that keeps streaming must not hold the pairing window
            while time.monotonic() < end_drain and s.recv(256):
                pass
        except OSError:
            pass
        s.close()


def save_new_code(code, host):
    """The code both sides derived becomes the code the ordinary link uses; remember the phone's address so the receiver reaches it at once."""
    write_code_file(code)          # written whole and moved into place: a receiver reading the file mid-write must never see an empty code (it would invent a new one and break the pairing)
    try:
        open(LAST_FILE, "w", encoding="utf-8").write(host if host != "127.0.0.1" else "")
    except OSError:
        pass
    log("paired with a phone by comparing a number")


# ----------------------------------------------------------------------------------------------------------------------------------------------------------------
# THE PERSON-FACING LAYER. What the status window and the tray say (pure functions first, so a test can read them), the shared theme, the tray icon, the status window and
# the pairing window. Nothing below changes how a key is typed or how a phone is trusted.
# ----------------------------------------------------------------------------------------------------------------------------------------------------------------

PALETTE = {"bg": "#0e1115", "card": "#161b23", "chip": "#1f2631", "blue": "#2563eb", "text": "#ffffff", "muted": "#9aa6b8", "good": "#4ade80", "warn": "#fbbf24", "bad": "#f87171",          # the phone app's colors
           "line": "#262e3a", "chip_hover": "#2b3544", "chip_press": "#364255", "blue_hover": "#3b78f0", "blue_press": "#1d4fcf", "off": "#5d6a7e", "chip_off": "#181d26", "ring": "#8fb0ff"}


def tone_color(tone):
    """A palette color from a tone name (good, warn, bad, muted, text, blue...) or a color already."""
    return PALETTE.get(tone, tone)


def clean_name(text):
    """A phone model name read from adb: printable characters only, at most 40 of them, empty when there is nothing usable."""
    return "".join(ch for ch in (text or "")[:200] if ch.isprintable()).strip()[:40]


def ago_text(seconds):
    """How long ago, as a person reads it at a glance. None (never happened) is 'Never'; a clock that ran backwards is 'Just now'."""
    if seconds is None:
        return "Never"
    s = int(max(0, seconds))
    if s < 2:
        return "Just now"
    if s < 60:
        return "%d seconds ago" % s
    m = s // 60
    if m < 60:
        return "%d minute%s ago" % (m, "" if m == 1 else "s")
    h = m // 60
    if h < 48:
        return "%d hour%s ago" % (h, "" if h == 1 else "s")
    return "%d days ago" % (h // 24)


LINK_LABELS = {"usb": "USB cable", "usb cable": "USB cable", "usb tethering": "USB tethering", "wi-fi": "Wi-Fi", "wi-fi or network": "Wi-Fi", "phone hotspot": "Phone hotspot"}


def link_parts(how):
    """(kind, address) from the text find_phone builds: 'Wi-Fi (192.168.1.20)' -> ('Wi-Fi', '192.168.1.20'), 'USB' -> ('USB cable', ''), '' (no link) -> ('', '')."""
    if not how:
        return "", ""
    head, sep, tail = how.partition(" (")
    addr = tail[:-1] if sep and tail.endswith(")") else ""
    name = head.strip()
    return LINK_LABELS.get(name.lower(), name[:30]), addr[:45]


def status_view(snap, now):
    """What the status window and the tray show, from a snapshot: {state, head, tone, hint, hint_tone, kind, rows}. state is blocked, connected, unpaired or waiting; every row is (label, value, tone).
    snap holds how, last_frame, usb_name, blocked, filterkeys and paired."""
    how = snap.get("how") or ""
    connected = bool(how)
    kind, addr = link_parts(how)
    blocked, fkeys = bool(snap.get("blocked")), bool(snap.get("filterkeys"))
    last = snap.get("last_frame") or 0.0
    if connected and blocked:
        state, head, tone = "blocked", "Windows is blocking input", "bad"
        hint, hint_tone = "The lock screen or a security prompt is open. Typing resumes when it closes.", "muted"
    elif connected:
        state, head, tone = "connected", "Connected", "good"
        hint, hint_tone = ("Filter Keys is on and can drop quick taps.", "warn") if fkeys else ("Typing from your phone works.", "muted")
    elif not snap.get("paired"):
        state, head, tone, hint, hint_tone = "unpaired", "Not paired yet", "warn", "Press Pair a phone, then follow the steps on both screens.", "muted"
    else:
        state, head, tone, hint, hint_tone = "waiting", "Looking for your phone", "warn", "It connects by itself when the phone is in reach.", "muted"
    if connected:
        usb = how == "USB" or kind.startswith("USB")
        if how == "USB" and snap.get("usb_name"):
            phone = snap["usb_name"]
        elif addr and addr != "127.0.0.1":
            phone = addr
        else:
            phone = "Phone on the cable" if usb else "Unknown address"
    else:
        phone = "Not connected"
    since = ago_text(now - last) if last else ago_text(None)
    rows = [("Phone", phone, "text" if connected else "muted"),
            ("Link", kind or "None", "good" if connected else "muted"),
            ("Last signal", since, "warn" if connected and last and now - last > 3.0 else "text"),
            ("Windows input", "Blocked right now" if blocked else "Ready", "bad" if blocked else "good"),
            ("Filter Keys", "On" if fkeys else "Off", "warn" if fkeys else "text")]
    return {"state": state, "head": head, "tone": tone, "hint": hint, "hint_tone": hint_tone, "kind": kind, "rows": rows}


def tray_tip(view):
    """The tray icon's tooltip: the program name and the state, short enough for Windows (127 characters)."""
    text = APP_NAME + ": " + view["head"] + (", " + view["kind"] if view["state"] in ("connected", "blocked") and view["kind"] else "")
    return text[:127]


def startup_item(startup_on, can_start):
    """(label, enabled) of the start with Windows button: Remove while it is on; Start again only for the packaged program, which is the one that can register itself."""
    if startup_on:
        return "Remove from startup", True
    return ("Start with Windows", True) if can_start else ("Not in startup", False)


def tray_menu_model(startup_on, can_start, paired=True):
    """The right click menu as data: (id, label, enabled) items, None for a separator. The first item is the default one (bold, what a left click does)."""
    label, enabled = startup_item(startup_on, can_start)
    return [("status", "Status", True), ("pair", "Pair another phone" if paired else "Pair a phone", True), None, ("startup", label, enabled), None, ("quit", "Quit", True)]


def _in_rr(x, y, x0, y0, x1, y1, r):
    if x < x0 or x > x1 or y < y0 or y > y1:
        return False
    cx, cy = min(max(x, x0 + r), x1 - r), min(max(y, y0 + r), y1 - r)
    return (x - cx) ** 2 + (y - cy) ** 2 <= r * r


ICON_DOT = (0.74, 0.74)          # the state badge sits in the rounded corner, the way a notification dot does
ICON_DARK = (0x0E, 0x11, 0x15)          # the gap ring and the arrow, the brand's background color
# The Typeferry mark (brand/typeferry-mark.svg) in the keycap's own unit square: the keycap, a gap ring, the raised top face and a mouse pointer cut out of it. Numbers are the master's, divided by its 432 wide keycap.
KEYCAP_HOLE = (0.0556, 0.0463, 0.9444, 0.9074, 0.1667)          # x0, y0, x1, y1, radius: the gap ring, thicker at the bottom so the keycap has a lip
KEYCAP_FACE = (0.1019, 0.0926, 0.8981, 0.8611, 0.1204)
CURSOR = ((0.3299, 0.1910), (0.3299, 0.6875), (0.4442, 0.5792), (0.5225, 0.7627), (0.5917, 0.7357), (0.5155, 0.5551), (0.6690, 0.5551))          # the pointer polygon: tip, down the left edge, notch, tail, back up to the right wing


def _in_arrow(u, v):
    """Point in the pointer polygon (even-odd ray casting); the name stays _in_arrow for the callers."""
    inside = False
    n = len(CURSOR)
    for k in range(n):
        x1, y1 = CURSOR[k]
        x2, y2 = CURSOR[(k + 1) % n]
        if (y1 > v) != (y2 > v) and u < (x2 - x1) * (v - y1) / (y2 - y1) + x1:
            inside = not inside
    return inside


def render_icon(size, dot=None):
    """The program's icon as RGBA bytes, top row first: the Typeferry keycap with a mouse pointer cut out of its top face, and when dot is a (r, g, b) color a state badge in the corner. Drawn by sampling 4x4 points per pixel, so any size is smooth."""
    ss = 4
    out = bytearray(size * size * 4)
    for py in range(size):
        for px in range(size):
            ar = ag = ab = aa = 0.0
            for j in range(ss):
                for i in range(ss):
                    x, y = (px + (i + 0.5) / ss) / size, (py + (j + 0.5) / ss) / size
                    c = None
                    u, v = (x - 0.03) / 0.94, (y - 0.03) / 0.94          # the keycap fills the square with a 3 percent margin
                    if _in_rr(u, v, 0.0, 0.0, 1.0, 1.0, 0.2222):
                        c = (0x25, 0x63, 0xEB)
                        if _in_rr(u, v, *KEYCAP_HOLE):
                            c = ICON_DARK
                            if _in_rr(u, v, *KEYCAP_FACE):
                                c = (0x25, 0x63, 0xEB)
                                if _in_arrow(u, v):
                                    c = ICON_DARK
                    if dot is not None:
                        d = ((x - ICON_DOT[0]) ** 2 + (y - ICON_DOT[1]) ** 2) ** 0.5
                        if d <= 0.225:
                            c = dot if d <= 0.155 else (0x0E, 0x11, 0x15)
                    if c is not None:
                        ar, ag, ab, aa = ar + c[0], ag + c[1], ab + c[2], aa + 1.0
            o = (py * size + px) * 4
            if aa:
                out[o:o + 4] = bytes((round(ar / aa), round(ag / aa), round(ab / aa), round(255 * aa / (ss * ss))))
    return bytes(out)


def _hex_rgb(h):
    return tuple(int(h[i:i + 2], 16) for i in (1, 3, 5))


TONE_DOT = {"good": _hex_rgb(PALETTE["good"]), "warn": _hex_rgb(PALETTE["warn"]), "bad": _hex_rgb(PALETTE["bad"])}
_icon_cache = {}


def icon_rgba(size, tone=None):
    """render_icon, kept (the tray redraws only when the state changes, but a window asks at every start)."""
    key = (size, tone)
    if key not in _icon_cache:
        _icon_cache[key] = render_icon(size, TONE_DOT.get(tone))
    return _icon_cache[key]


def icon_png(size, tone=None):
    """The icon as a PNG file's bytes (what a Tk window takes as its icon)."""
    rgba = icon_rgba(size, tone)
    raw = b"".join(b"\x00" + rgba[y * size * 4:(y + 1) * size * 4] for y in range(size))

    def chunk(kind, data):
        return struct.pack(">I", len(data)) + kind + data + struct.pack(">I", zlib.crc32(kind + data) & 0xFFFFFFFF)
    return b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", size, size, 8, 6, 0, 0, 0)) + chunk(b"IDAT", zlib.compress(raw, 9)) + chunk(b"IEND", b"")


def icon_dib(size, tone=None):
    """The icon as the bytes Windows builds an icon handle from: a bitmap header, the pixels as BGRA from the bottom row up, then an all-zero mask (the alpha channel does the cutting)."""
    rgba = icon_rgba(size, tone)
    bgra = bytearray(rgba)
    bgra[0::4], bgra[2::4] = rgba[2::4], rgba[0::4]
    rows = b"".join(bytes(bgra[y * size * 4:(y + 1) * size * 4]) for y in range(size - 1, -1, -1))
    return struct.pack("<IiiHHIIiiII", 40, size, size * 2, 1, 32, 0, 0, 0, 0, 0, 0) + rows + bytes(((size + 31) // 32 * 4) * size)


def current_snapshot():
    """The link as the program knows it right now, with the two things Windows decides (is input blocked, is Filter Keys on) and whether a phone has ever paired."""
    s = LINK.snapshot()
    s["blocked"] = input_blocked()
    s["filterkeys"] = filter_keys_on()
    s["paired"] = os.path.exists(PAIRED_FILE)
    return s


def current_view():
    return status_view(current_snapshot(), time.monotonic())


def current_code_text():
    """The pairing code as shown to a person (groups of four), or '' when the file has none. Read when asked, never kept."""
    try:
        code = LC.normalize(open(CODE_FILE, encoding="utf-8-sig").read())
    except (OSError, ValueError):
        return ""
    return LC.pretty(code) if code else ""


def set_dpi_aware():
    """Per-monitor aware: sharp text on a scaled screen instead of a blurry stretched window (and a crisp tray menu)."""
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
    except (AttributeError, OSError):
        pass


# --- the Windows calls the tray and the dark title bar need, on their own library handles so the typing code's declarations stay as they are ---
WM_APP = 0x8000
WM_TRAY, WM_SHOW, WM_QUITREQ, WM_REFRESH = WM_APP + 1, WM_APP + 2, WM_APP + 3, WM_APP + 4
TRAY_CLASS = "PhoneKbReceiverTray" + INSTANCE
WNDPROC = ctypes.WINFUNCTYPE(ctypes.c_ssize_t, ctypes.c_void_p, ctypes.c_uint, ctypes.c_size_t, ctypes.c_ssize_t)


class WNDCLASSW(ctypes.Structure):
    _fields_ = [("style", wt.UINT), ("lpfnWndProc", WNDPROC), ("cbClsExtra", ctypes.c_int), ("cbWndExtra", ctypes.c_int), ("hInstance", ctypes.c_void_p), ("hIcon", ctypes.c_void_p),
                ("hCursor", ctypes.c_void_p), ("hbrBackground", ctypes.c_void_p), ("lpszMenuName", wt.LPCWSTR), ("lpszClassName", wt.LPCWSTR)]


class NOTIFYICONDATAW(ctypes.Structure):
    _fields_ = [("cbSize", wt.DWORD), ("hWnd", ctypes.c_void_p), ("uID", wt.UINT), ("uFlags", wt.UINT), ("uCallbackMessage", wt.UINT), ("hIcon", ctypes.c_void_p), ("szTip", wt.WCHAR * 128),
                ("dwState", wt.DWORD), ("dwStateMask", wt.DWORD), ("szInfo", wt.WCHAR * 256), ("uVersion", wt.UINT), ("szInfoTitle", wt.WCHAR * 64), ("dwInfoFlags", wt.DWORD),
                ("guidItem", ctypes.c_ubyte * 16), ("hBalloonIcon", ctypes.c_void_p)]


_u = ctypes.WinDLL("user32", use_last_error=True)
_sh = ctypes.WinDLL("shell32", use_last_error=True)
_k = ctypes.WinDLL("kernel32", use_last_error=True)
_vp, _ui_, _sz, _ss = ctypes.c_void_p, ctypes.c_uint, ctypes.c_size_t, ctypes.c_ssize_t
_u.RegisterClassW.argtypes, _u.RegisterClassW.restype = (ctypes.POINTER(WNDCLASSW),), wt.ATOM
_u.CreateWindowExW.argtypes, _u.CreateWindowExW.restype = (wt.DWORD, wt.LPCWSTR, wt.LPCWSTR, wt.DWORD, ctypes.c_int, ctypes.c_int, ctypes.c_int, ctypes.c_int, _vp, _vp, _vp, _vp), _vp
_u.DefWindowProcW.argtypes, _u.DefWindowProcW.restype = (_vp, _ui_, _sz, _ss), _ss
_u.GetMessageW.argtypes, _u.GetMessageW.restype = (ctypes.POINTER(wt.MSG), _vp, _ui_, _ui_), ctypes.c_int
_u.TranslateMessage.argtypes = (ctypes.POINTER(wt.MSG),)
_u.DispatchMessageW.argtypes, _u.DispatchMessageW.restype = (ctypes.POINTER(wt.MSG),), _ss
_u.PostMessageW.argtypes, _u.PostMessageW.restype = (_vp, _ui_, _sz, _ss), wt.BOOL
_u.PostQuitMessage.argtypes = (ctypes.c_int,)
_u.DestroyWindow.argtypes = (_vp,)
_u.CreatePopupMenu.restype = _vp
_u.AppendMenuW.argtypes = (_vp, _ui_, _sz, wt.LPCWSTR)
_u.TrackPopupMenu.argtypes, _u.TrackPopupMenu.restype = (_vp, _ui_, ctypes.c_int, ctypes.c_int, ctypes.c_int, _vp, _vp), wt.BOOL
_u.DestroyMenu.argtypes = (_vp,)
_u.SetMenuDefaultItem.argtypes = (_vp, _ui_, _ui_)
_u.SetForegroundWindow.argtypes = (_vp,)
_u.RegisterWindowMessageW.argtypes, _u.RegisterWindowMessageW.restype = (wt.LPCWSTR,), _ui_
_u.SetTimer.argtypes, _u.SetTimer.restype = (_vp, _sz, _ui_, _vp), _sz
_u.FindWindowW.argtypes, _u.FindWindowW.restype = (wt.LPCWSTR, wt.LPCWSTR), _vp
_u.GetCursorPos.argtypes = (ctypes.POINTER(wt.POINT),)
_u.GetSystemMetrics.argtypes, _u.GetSystemMetrics.restype = (ctypes.c_int,), ctypes.c_int
_u.CreateIconFromResourceEx.argtypes, _u.CreateIconFromResourceEx.restype = (ctypes.c_char_p, wt.DWORD, wt.BOOL, wt.DWORD, ctypes.c_int, ctypes.c_int, _ui_), _vp
_u.DestroyIcon.argtypes = (_vp,)
_u.GetParent.argtypes, _u.GetParent.restype = (_vp,), _vp
_sh.Shell_NotifyIconW.argtypes, _sh.Shell_NotifyIconW.restype = (wt.DWORD, ctypes.POINTER(NOTIFYICONDATAW)), wt.BOOL
_k.GetModuleHandleW.argtypes, _k.GetModuleHandleW.restype = (wt.LPCWSTR,), _vp


def dark_title_bar(win):
    """Windows draws the title bar dark (and, on Windows 11, in the window's own color) when asked. Old Windows ignores it: the bar stays light and nothing breaks."""
    try:
        win.update_idletasks()
        hwnd = _u.GetParent(win.winfo_id()) or win.winfo_id()
        dwm = ctypes.WinDLL("dwmapi")
        dwm.DwmSetWindowAttribute.argtypes = (_vp, wt.DWORD, _vp, wt.DWORD)

        def put(attr, value):
            v = ctypes.c_int(value)
            return dwm.DwmSetWindowAttribute(hwnd, attr, ctypes.byref(v), 4)
        if put(20, 1) != 0:                                          # DWMWA_USE_IMMERSIVE_DARK_MODE (the first Windows 10 builds knew it as 19)
            put(19, 1)
        h = PALETTE["bg"]
        put(35, int(h[5:7] + h[3:5] + h[1:3], 16))                   # DWMWA_CAPTION_COLOR, a COLORREF (blue, green, red)
        put(36, 0xFFFFFF)                                            # DWMWA_TEXT_COLOR
        put(34, int(PALETTE["line"][5:7] + PALETTE["line"][3:5] + PALETTE["line"][1:3], 16))          # DWMWA_BORDER_COLOR
    except (OSError, AttributeError, ValueError):
        pass


def allow_dark_menus():
    """Let the tray's right click menu follow Windows' dark mode (an undocumented but long stable call; the menu stays light when it is missing)."""
    try:
        ux = ctypes.WinDLL("uxtheme")
        set_mode = ux[135]                                           # SetPreferredAppMode
        set_mode.argtypes = (ctypes.c_int,)
        set_mode(1)                                                  # AllowDark: follow the system setting
        ux[136]()                                                    # FlushMenuThemes
    except (OSError, AttributeError, ValueError):
        pass


class Tray:
    """The tray icon: a hidden window with its own message loop thread. The tooltip and the corner badge follow the state; a left click opens the status window, a right click shows the menu. Everything Windows tells it
    arrives in _wndproc; the callbacks in `actions` (status, pair, startup, quit) run on their own threads so a slow one never stalls the loop."""

    def __init__(self, get_view, actions):
        self.get_view, self.actions = get_view, actions
        self.hwnd = None
        self.ready = threading.Event()
        self.thread = None
        self.nid = None
        self.added = False
        self.closed = False
        self.v4 = False
        self.state, self.tip = None, ""
        self.icons = {}
        self.taskbar_msg = 0
        self.last_select = 0.0
        self.proc = WNDPROC(self._wndproc)                           # must stay referenced for as long as the window lives

    def start(self):
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()
        self.ready.wait(5.0)

    def _run(self):
        try:
            hinst = _k.GetModuleHandleW(None)
            wc = WNDCLASSW()
            wc.lpfnWndProc, wc.hInstance, wc.lpszClassName = self.proc, hinst, TRAY_CLASS
            if not _u.RegisterClassW(ctypes.byref(wc)) and ctypes.get_last_error() != 1410:          # 1410: the class exists already
                raise OSError("could not register the tray window class (%d)" % ctypes.get_last_error())
            self.hwnd = _u.CreateWindowExW(0x80, TRAY_CLASS, APP_NAME, 0, 0, 0, 0, 0, None, None, hinst, None)          # a window that is never shown (WS_EX_TOOLWINDOW)
            if not self.hwnd:
                raise OSError("could not create the tray window (%d)" % ctypes.get_last_error())
            self.taskbar_msg = _u.RegisterWindowMessageW("TaskbarCreated")          # Explorer restarted: its tray is empty, so the icon is added again
            allow_dark_menus()
            self._add()
            _u.SetTimer(self.hwnd, 1, 2000, None)
        except Exception:
            log("no tray icon: " + traceback.format_exc().replace("\n", " | "))
            self.ready.set()
            return
        self.ready.set()
        msg = wt.MSG()
        while _u.GetMessageW(ctypes.byref(msg), None, 0, 0) > 0:
            _u.TranslateMessage(ctypes.byref(msg))
            _u.DispatchMessageW(ctypes.byref(msg))
        self.remove_icon()

    def _hicon(self, tone):
        size = _u.GetSystemMetrics(49) or 16                        # SM_CXSMICON: 16 at 100 percent, 24 at 150, 32 at 200
        key = (size, tone)
        if key not in self.icons:
            dib = icon_dib(size, tone)
            self.icons[key] = _u.CreateIconFromResourceEx(dib, len(dib), True, 0x00030000, size, size, 0)
        return self.icons[key]

    def _fill(self, flags):
        view = self.get_view()
        self.state, self.tip = view["tone"], tray_tip(view)
        nid = NOTIFYICONDATAW()
        nid.cbSize = ctypes.sizeof(NOTIFYICONDATAW)
        nid.hWnd, nid.uID, nid.uFlags, nid.uCallbackMessage = self.hwnd, 1, flags, WM_TRAY
        nid.hIcon = self._hicon(self.state)
        nid.szTip = self.tip
        self.nid = nid

    def _add(self):
        if self.closed or not self.hwnd:
            return
        self._fill(0x1 | 0x2 | 0x4)                                  # NIF_MESSAGE | NIF_ICON | NIF_TIP
        self.added = bool(_sh.Shell_NotifyIconW(0, ctypes.byref(self.nid)))          # NIM_ADD (fails while Explorer's tray does not exist yet: the timer and TaskbarCreated try again)
        if self.added:
            self.nid.uVersion = 4
            self.v4 = bool(_sh.Shell_NotifyIconW(4, ctypes.byref(self.nid)))        # NIM_SETVERSION: version 4 reports the keyboard and gives the menu's position

    def _refresh(self):
        if self.closed:
            return
        if not self.added:
            self._add()
            return
        old = (self.state, self.tip)
        view = self.get_view()
        if (view["tone"], tray_tip(view)) != old:
            self._fill(0x1 | 0x2 | 0x4)
            _sh.Shell_NotifyIconW(1, ctypes.byref(self.nid))        # NIM_MODIFY

    def remove_icon(self):
        """Take the icon out of the tray. Safe from any thread and any number of times."""
        self.closed = True
        if self.added and self.nid is not None:
            self.added = False
            return bool(_sh.Shell_NotifyIconW(2, ctypes.byref(self.nid)))        # NIM_DELETE
        return False

    def stop(self):
        if self.hwnd:
            _u.PostMessageW(self.hwnd, 0x0010, 0, 0)                 # WM_CLOSE: the window goes, the loop ends, the icon is removed

    def _fire(self, name):
        fn = self.actions.get(name)
        if fn:
            threading.Thread(target=fn, daemon=True).start()

    def _select(self):
        now = time.monotonic()
        if now - self.last_select > 0.4:                             # a click can arrive as two events
            self.last_select = now
            self._fire("status")

    def _menu(self, x, y):
        items = tray_menu_model(startup_registered(), FROZEN, os.path.exists(PAIRED_FILE))
        menu = _u.CreatePopupMenu()
        ids = {}
        for n, item in enumerate(items, 1):
            if item is None:
                _u.AppendMenuW(menu, 0x800, 0, None)                  # MF_SEPARATOR
            else:
                _u.AppendMenuW(menu, 0 if item[2] else 0x1, n, item[1])          # MF_STRING, or MF_GRAYED
                ids[n] = item[0]
        _u.SetMenuDefaultItem(menu, 0, 1)
        _u.SetForegroundWindow(self.hwnd)                            # without this the menu does not close when the person clicks elsewhere
        cmd = _u.TrackPopupMenu(menu, 0x0100 | 0x0002, x, y, 0, self.hwnd, None)          # TPM_RETURNCMD | TPM_RIGHTBUTTON
        _u.PostMessageW(self.hwnd, 0, 0, 0)
        _u.DestroyMenu(menu)
        if cmd in ids:
            self._fire(ids[cmd])

    def _wndproc(self, hwnd, msg, wparam, lparam):
        try:
            if msg == WM_TRAY:
                ev = lparam & 0xFFFF
                if self.v4:
                    if ev in (0x400, 0x401):                         # NIN_SELECT, NIN_KEYSELECT
                        self._select()
                    elif ev == 0x7B:                                 # WM_CONTEXTMENU: wparam holds where
                        self._menu(ctypes.c_short(wparam & 0xFFFF).value, ctypes.c_short((wparam >> 16) & 0xFFFF).value)
                elif ev == 0x202:                                    # WM_LBUTTONUP
                    self._select()
                elif ev == 0x205:                                    # WM_RBUTTONUP
                    pt = wt.POINT()
                    _u.GetCursorPos(ctypes.byref(pt))
                    self._menu(pt.x, pt.y)
                return 0
            if msg == WM_SHOW:
                self._fire("status")
                return 0
            if msg == WM_QUITREQ:
                self._fire("quit")
                return 0
            if msg in (WM_REFRESH, 0x0113):                          # WM_TIMER
                self._refresh()
                return 0
            if self.taskbar_msg and msg == self.taskbar_msg:
                self.added = False
                self._add()
                return 0
            if msg == 0x0016 and wparam:                             # WM_ENDSESSION: Windows is signing out or shutting down
                final_cleanup()
                return 0
            if msg == 0x0002:                                        # WM_DESTROY
                _u.PostQuitMessage(0)
                return 0
        except Exception:
            log("tray: " + traceback.format_exc().replace("\n", " | "))
        return _u.DefWindowProcW(hwnd, msg, wparam, lparam)


def find_running_window():
    """The hidden tray window of a receiver that is running (0 when none is)."""
    return _u.FindWindowW(TRAY_CLASS, None) or 0


def poke_running(message):
    hwnd = find_running_window()
    return bool(hwnd and _u.PostMessageW(hwnd, message, 0, 0))


def show_running_status():
    """Ask the running receiver to show its status window. False when there is none to ask (the caller then opens the pairing window, as before)."""
    return poke_running(WM_SHOW)


def ask_running_to_quit(wait_s):
    """Ask the running receiver to quit (it lifts every key and removes its icon) and wait until its window is gone. True when it went."""
    if not poke_running(WM_QUITREQ):
        return False
    end = time.monotonic() + wait_s
    while time.monotonic() < end:
        if not find_running_window():
            return True
        time.sleep(0.2)
    return not find_running_window()


_cleaned = [False]
_cleanup_lock = threading.Lock()          # a second caller waits for the first to finish: the one that exits the process must not cut the other short
_tray = [None]
_ui_started = [False]


def final_cleanup():
    """Runs once however the program ends (Quit, sign out, an error): lifts every key and mouse button when a link ever carried keys, and removes the tray icon."""
    with _cleanup_lock:
        if _cleaned[0]:
            return
        _cleaned[0] = True
        try:
            if _ever_served[0]:
                release_everything()
        except Exception:
            log("final release failed: " + traceback.format_exc().replace("\n", " | "))
        if _tray[0] is not None:
            try:
                gone = _tray[0].remove_icon()
            except Exception:
                gone = False
            log("receiver stopped, tray icon " + ("removed" if gone else "was not there"))


def quit_program():
    """Quit: the main loop and the link loop end (the link loop lifts every key and button on its way out), the tray icon goes, the program exits. If the loop is slow to stop, everything is released here instead."""
    if QUIT.is_set():
        return
    log("quit chosen")
    QUIT.set()
    _late_event.set()
    if not MAIN_DONE.wait(QUIT_WAIT_S):
        log("the main loop did not stop in time: releasing everything here")
    final_cleanup()
    os._exit(0)                                                      # a window thread's Tk must not be torn down by the interpreter's own exit


def toggle_startup():
    """Remove the start with Windows entry, or put it back (the packaged program only)."""
    if startup_registered():
        remove_startup()
        remember_startup_off()
        log("removed from Windows startup")
    elif FROZEN:
        try:
            os.remove(AUTOSTART_OFF_FILE)
        except OSError:
            pass
        ensure_autostart()


# --- the theme: one dark look for both windows, matching the phone app ---
class Theme:
    """Sizes in pixels at 100 percent scaled to this screen, the fonts, and the widgets both windows are made of."""

    def __init__(self, root):
        self.root = root
        try:
            forced = float(os.environ.get("TYPEFERRY_UI_SCALE", "") or 0)
        except ValueError:
            forced = 0.0
        detected = max(1.0, root.winfo_fpixels("1i") / 96.0)
        self.scale = min(4.0, max(0.75, forced)) if forced else detected
        if forced:
            root.tk.call("tk", "scaling", 96.0 * self.scale / 72.0)
        families = set(tkfont.families(root))
        self.sans = "Segoe UI Variable Text" if "Segoe UI Variable Text" in families else "Segoe UI"
        self.mono = "Cascadia Mono" if "Cascadia Mono" in families else "Consolas"

    def px(self, n):
        return int(round(n * self.scale))

    def font(self, size, bold=False, mono=False):
        return (self.mono if mono else self.sans, size, "bold" if bold else "normal")

    def window(self, win, title):
        """The look of a top level window: dark, fixed size, titled, with the program's icon."""
        win.title(title)
        win.configure(bg=PALETTE["bg"])
        win.resizable(False, False)
        dark_title_bar(win)
        try:
            win._icons = [tk.PhotoImage(data=base64.b64encode(icon_png(s)).decode("ascii")) for s in (32, 64)]          # kept on the window: Tk drops an image nothing refers to
            win.iconphoto(True, *win._icons)
        except tk.TclError:
            pass

    def center(self, win):
        win.update_idletasks()
        w, h = win.winfo_reqwidth(), win.winfo_reqheight()
        win.geometry("+%d+%d" % (max(0, (win.winfo_screenwidth() - w) // 2), max(0, (win.winfo_screenheight() - h) // 2 - self.px(30))))

    def label(self, parent, text="", size=10, bold=False, fg="text", bg=None, wrap=0, anchor="w", justify="left", mono=False):
        return tk.Label(parent, text=text, font=self.font(size, bold, mono), fg=tone_color(fg), bg=tone_color(bg or parent.cget("bg")), wraplength=self.px(wrap) if wrap else 0, anchor=anchor, justify=justify, bd=0, padx=0, pady=0)

    def card(self, parent, **kw):
        return tk.Frame(parent, bg=PALETTE["card"], highlightthickness=1, highlightbackground=PALETTE["line"], highlightcolor=PALETTE["line"], **kw)

    def entry(self, parent):
        return tk.Entry(parent, font=self.font(22, False, True), width=9, justify="center", bg=PALETTE["chip"], fg=PALETTE["text"], insertbackground=PALETTE["text"], relief="flat", bd=0,
                        highlightthickness=2, highlightbackground=PALETTE["chip"], highlightcolor=PALETTE["blue"], disabledbackground=PALETTE["chip"], disabledforeground=PALETTE["muted"])

    def button(self, parent, text, command=None, kind="secondary", w=0, h=40, size=10):
        return Btn(parent, self, text, command, kind, w, h, size)


def rr_points(x0, y0, x1, y1, r):
    """The corner points of a rounded rectangle, for a smoothed Tk polygon."""
    return [x0 + r, y0, x1 - r, y0, x1, y0, x1, y0 + r, x1, y1 - r, x1, y1, x1 - r, y1, x0 + r, y1, x0, y1, x0, y1 - r, x0, y0 + r, x0, y0]


if tk is not None:
    class Btn(tk.Canvas):
        """A flat rounded button: hover, pressed, focused (keyboard) and disabled looks. kind is primary (blue), secondary (a chip) or ghost (text only, for a quiet action). invoke() and config(text=, state=)
        work like a Tk button's, which the pairing window's test hook relies on."""

        def __init__(self, parent, th, text, command, kind, w, h, size):
            self.th, self.text, self.command, self.kind, self.size = th, text, command, kind, size
            self._st = "normal"
            self._hover = self._press = self._focus = False
            super().__init__(parent, width=th.px(w), height=th.px(h), bg=parent.cget("bg"), highlightthickness=0, bd=0, takefocus=1, cursor="hand2")
            for seq, fn in (("<Enter>", self._enter), ("<Leave>", self._leave), ("<ButtonPress-1>", self._down), ("<ButtonRelease-1>", self._up), ("<Configure>", lambda e: self._draw()),
                            ("<FocusIn>", self._focus_in), ("<FocusOut>", self._focus_out), ("<Return>", lambda e: self.invoke()), ("<space>", lambda e: self.invoke())):
                self.bind(seq, fn)
            self._draw()

        def _enter(self, e):
            self._hover = True
            self._draw()

        def _leave(self, e):
            self._hover = self._press = False
            self._draw()

        def _down(self, e):
            if self._st == "normal":
                self._press = True
                self._draw()

        def _up(self, e):
            was = self._press
            self._press = False
            self._draw()
            if was and 0 <= e.x <= self.winfo_width() and 0 <= e.y <= self.winfo_height():
                self.invoke()

        def _focus_in(self, e):
            self._focus = True
            self._draw()

        def _focus_out(self, e):
            self._focus = False
            self._draw()

        def _colors(self):
            """(fill, text) for the current look."""
            if self._st != "normal":
                return PALETTE["chip_off"], PALETTE["off"]
            if self.kind == "primary":
                return (PALETTE["blue_press"] if self._press else PALETTE["blue_hover"] if self._hover else PALETTE["blue"]), PALETTE["text"]
            if self.kind == "ghost":
                return (PALETTE["chip_press"] if self._press else PALETTE["chip"] if self._hover else self.cget("bg")), (PALETTE["text"] if self._hover else PALETTE["muted"])
            return (PALETTE["chip_press"] if self._press else PALETTE["chip_hover"] if self._hover else PALETTE["chip"]), PALETTE["text"]

        def _draw(self):
            self.delete("all")
            w, h = max(self.winfo_width(), int(self.cget("width"))), max(self.winfo_height(), int(self.cget("height")))
            fill, fg = self._colors()
            ring = self._focus and self._st == "normal"
            self.create_polygon(rr_points(1, 1, w - 1, h - 1, self.th.px(8)), smooth=True, fill=fill, outline=PALETTE["ring"] if ring else fill, width=2 if ring else 1)
            self.create_text(w / 2, h / 2, text=self.text, fill=fg, font=self.th.font(self.size, self.kind != "ghost"))

        def invoke(self):
            if self._st == "normal" and self.command:
                self.command()

        def configure(self, cnf=None, **kw):
            if isinstance(cnf, dict):
                kw, cnf = dict(cnf, **kw), None
            changed = False
            for name, attr in (("text", "text"), ("state", "_st"), ("command", "command")):
                if name in kw:
                    setattr(self, attr, kw.pop(name))
                    changed = True
            result = tk.Canvas.configure(self, cnf, **kw) if (kw or cnf) else None
            if changed:
                self._draw()
            return result

        config = configure


class StatusWindow:
    """The status window: the state in one line, the facts in a card, four buttons. Built on the Tk root it is given (hidden until show()); closing it hides it. snapshot_fn is the link as a dict (current_snapshot), so a test can show any state."""

    ROW_NAMES = ("Phone", "Link", "Last signal", "Windows input", "Filter Keys")

    def __init__(self, root, snapshot_fn=None, actions=None):
        self.root = root
        self.snapshot_fn = snapshot_fn or current_snapshot
        self.act = {"pair": open_pair_window, "startup": toggle_startup, "quit": lambda: threading.Thread(target=quit_program, daemon=True).start()}
        self.act.update(actions or {})
        self.placed = False
        self.code_until = 0.0
        th = self.th = Theme(root)
        th.window(root, APP_NAME)
        root.protocol("WM_DELETE_WINDOW", self.hide)
        root.bind("<Escape>", lambda e: self.hide())
        wrap = 392
        page = tk.Frame(root, bg=PALETTE["bg"], padx=th.px(28), pady=th.px(26))
        page.pack()
        top = tk.Frame(page, bg=PALETTE["bg"])
        top.pack(fill="x")
        self.dot = tk.Canvas(top, width=th.px(14), height=th.px(14), bg=PALETTE["bg"], highlightthickness=0, bd=0)
        self.dot.pack(side="left", pady=(th.px(3), 0))
        self.dot_id = self.dot.create_oval(1, 1, th.px(14) - 1, th.px(14) - 1, fill=PALETTE["warn"], outline="")
        self.head = th.label(top, "", 18, True)
        self.head.pack(side="left", padx=(th.px(10), 0))
        self.hint = th.label(page, "", 10, False, "muted", wrap=wrap)
        self.hint.pack(fill="x", pady=(th.px(6), th.px(18)))
        card = self.facts = th.card(page)
        card.pack(fill="x")
        inner = tk.Frame(card, bg=PALETTE["card"], padx=th.px(18), pady=th.px(6))
        inner.pack(fill="x")
        inner.columnconfigure(1, weight=1)
        self.vals = []
        for n, name in enumerate(self.ROW_NAMES):
            if n:
                tk.Frame(inner, height=1, bg=PALETTE["line"]).grid(row=n * 2 - 1, column=0, columnspan=2, sticky="ew")
            th.label(inner, name, 10, False, "muted").grid(row=n * 2, column=0, sticky="w", pady=th.px(10))
            value = th.label(inner, "", 11, False, "text", anchor="e", justify="right")
            value.grid(row=n * 2, column=1, sticky="e", padx=(th.px(16), 0))
            self.vals.append(value)
        self.code_card = th.card(page)                                # hidden until the person asks for the code
        code_in = tk.Frame(self.code_card, bg=PALETTE["card"], padx=th.px(18), pady=th.px(14))
        code_in.pack(fill="x")
        th.label(code_in, "Type this code on the phone", 10, False, "muted").pack(anchor="w")
        self.code_text = th.label(code_in, "", 15, True, "text", mono=True)
        self.code_text.pack(anchor="w", pady=(th.px(6), 0))
        grid = tk.Frame(page, bg=PALETTE["bg"])
        grid.pack(fill="x", pady=(th.px(18), 0))
        grid.columnconfigure(0, weight=1, uniform="b")
        grid.columnconfigure(1, weight=1, uniform="b")
        gap = th.px(5)
        self.pair_btn = th.button(grid, "Pair another phone", lambda: self.act["pair"](), "primary", 190)
        self.code_btn = th.button(grid, "Show code", self.toggle_code, "secondary", 190)
        self.startup_btn = th.button(grid, "Remove from startup", self._startup, "secondary", 190)
        self.quit_btn = th.button(grid, "Quit", lambda: self.act["quit"](), "secondary", 190)
        self.pair_btn.grid(row=0, column=0, sticky="ew", padx=(0, gap), pady=(0, gap))
        self.code_btn.grid(row=0, column=1, sticky="ew", padx=(gap, 0), pady=(0, gap))
        self.startup_btn.grid(row=1, column=0, sticky="ew", padx=(0, gap), pady=(gap, 0))
        self.quit_btn.grid(row=1, column=1, sticky="ew", padx=(gap, 0), pady=(gap, 0))
        th.label(page, "Version " + RECEIVER_VERSION, 9, False, "off").pack(anchor="w", pady=(th.px(16), 0))
        self.update()
        root.after(1000, self._tick)

    def _startup(self):
        self.act["startup"]()
        self.update()

    def toggle_code(self):
        if self.code_until:
            self.code_until = 0.0
        else:
            text = current_code_text()
            self.code_text.config(text=text or "No code yet. Pair a phone first.")
            self.code_until = time.monotonic() + 30.0                     # the code is the one long lived secret: it hides itself again
        self.update()

    def update(self):
        try:
            snap = self.snapshot_fn()
        except Exception:
            return
        v = status_view(snap, time.monotonic())
        self.dot.itemconfigure(self.dot_id, fill=tone_color(v["tone"]))
        self.head.config(text=v["head"], fg=tone_color(v["tone"]))
        self.hint.config(text=v["hint"], fg=tone_color(v["hint_tone"]))
        for label, (name, value, tone) in zip(self.vals, v["rows"]):
            label.config(text=value, fg=tone_color(tone))
        self.pair_btn.config(text="Pair another phone" if snap.get("paired") else "Pair a phone")
        label, enabled = startup_item(startup_registered(), FROZEN)
        self.startup_btn.config(text=label, state="normal" if enabled else "disabled")
        if self.code_until and time.monotonic() > self.code_until:
            self.code_until = 0.0
        if self.code_until:
            self.code_card.pack(fill="x", pady=(self.th.px(14), 0), after=self.facts)
            self.code_btn.config(text="Hide code")
        else:
            self.code_card.pack_forget()
            self.code_btn.config(text="Show code")

    def _tick(self):
        if self.root.state() == "normal":
            self.update()
        self.root.after(1000, self._tick)

    def hide(self):
        self.root.withdraw()

    def show(self):
        self.update()
        if not self.placed:
            self.th.center(self.root)
            self.placed = True
        self.root.deiconify()
        dark_title_bar(self.root)
        self.root.lift()
        self.root.attributes("-topmost", True)                       # in front of the window the person was using, then back to normal
        self.root.after(400, lambda: self.root.attributes("-topmost", False))
        self.root.focus_force()


class StatusUi:
    """Runs the status window on a thread of its own (Tk belongs to one thread), created the first time it is asked for. show() is safe to call from any thread."""

    def __init__(self):
        self.q = queue.Queue()
        self.thread = None
        self.lock = threading.Lock()

    def show(self):
        if tk is None:
            open_pair_window()                                       # a Python without Tk has no status window: the old behaviour
            return
        with self.lock:
            if self.thread is None or not self.thread.is_alive():
                self.thread = threading.Thread(target=self._run, daemon=True)
                self.thread.start()
        self.q.put("show")

    def _run(self):
        _ui_started[0] = True
        try:
            set_dpi_aware()
            root = tk.Tk()
            root.withdraw()
            win = StatusWindow(root)

            def poll():
                try:
                    while True:
                        if self.q.get_nowait() == "show":
                            win.show()
                except queue.Empty:
                    pass
                root.after(100, poll)
            poll()
            root.mainloop()
        except Exception:
            log("status window: " + traceback.format_exc().replace("\n", " | "))


def start_companion():
    """The tray icon and the status window, started with the receiver. A failure to make either is logged and never stops the typing."""
    ui = StatusUi()
    tray = Tray(current_view, {"status": ui.show, "pair": open_pair_window, "startup": toggle_startup, "quit": quit_program})
    _tray[0] = tray
    atexit.register(final_cleanup)
    tray.start()


PAIR_MUTEX_NAME = "Local\\PhoneKbPairWindow" + INSTANCE
PAIR_EVENT_NAME = "Local\\PhoneKbPairWindowWake" + INSTANCE
_pair_handles = {}


def pair_window_singleton():
    """True when this process is now THE pairing window; False when one is already open, which is then woken (brought forward, and restarted if it had given up). Every tray click, status button and first start spawns a
    pairing window, and each one sweeps the whole network with 64 threads: two at once double the load and show the person two prompts for one phone."""
    kernel32.CreateMutexW.restype = wt.HANDLE
    kernel32.CreateEventW.restype = wt.HANDLE
    kernel32.OpenEventW.restype = wt.HANDLE
    kernel32.SetEvent.argtypes = [wt.HANDLE]
    kernel32.CloseHandle.argtypes = [wt.HANDLE]
    kernel32.WaitForSingleObject.argtypes = [wt.HANDLE, wt.DWORD]
    h = kernel32.CreateMutexW(None, False, PAIR_MUTEX_NAME)
    if not h:
        return True                                                   # no mutex to be had: carry on rather than refuse the person a window
    if ctypes.get_last_error() == 183:
        ev = kernel32.OpenEventW(0x0002, False, PAIR_EVENT_NAME)      # EVENT_MODIFY_STATE
        if ev:
            kernel32.SetEvent(ev)
            kernel32.CloseHandle(ev)
        kernel32.CloseHandle(h)
        return False
    _pair_handles["mutex"] = h                                        # held for the life of the window
    _pair_handles["wake"] = kernel32.CreateEventW(None, False, False, PAIR_EVENT_NAME)          # auto-reset: one wake-up is read once
    return True


def pair_window_wake_requested():
    """True once for each time another start asked this window to come forward."""
    ev = _pair_handles.get("wake")
    return bool(ev) and kernel32.WaitForSingleObject(ev, 0) == 0


def pair_search(hosts_fn, pair_fn, emit, stop, answer, window_s=None, pause=time.sleep):
    """The pairing window's search, apart from its widgets so it is tested: sweep the hosts that have the port open, try each with pair_fn(host) (which returns a code, 'declined' or None), and report what happened through
    emit(kind, value). A device the person cancelled is left alone for the rest of the window and the search goes on (a stranger found first cannot block the real phone); the window gives up after window_s
    (PAIR_WINDOW_S), inside a sweep as well as between sweeps. Returns 'paired', 'expired', 'error' or None when stopped."""
    emit("looking")
    deadline = time.monotonic() + (PAIR_WINDOW_S if window_s is None else window_s)
    skipped = set()
    while not stop.is_set():
        if time.monotonic() > deadline:                                    # the phone only answers for a few minutes anyway: stop sweeping the network
            emit("expired")
            return "expired"
        for host in hosts_fn():
            if host in skipped:
                continue
            if time.monotonic() > deadline:                                # the sweep itself can take a while: the window must not say it is looking past its time
                break
            answer["prompted"] = False
            answer["cancel"] = False
            try:
                r = pair_fn(host)
            except Exception as e:                                    # one odd host must not leave the window stuck on "Looking"
                log("pairing window: %s: %s" % (type(e).__name__, e))
                r = None
            answer["probe"] = None
            if r is None and answer["prompted"]:
                emit("lost")
                pause(3.0)
                emit("looking")
            if r and r != "declined":
                try:
                    save_new_code(r, host)
                except OSError as e:
                    log("could not save the new pairing code: %s" % e)
                    emit("error")
                    return "error"
                emit("done")
                return "paired"
            if r == "declined" and answer["cancel"]:
                skipped.add(host)
                emit("cancelled")
                pause(3.0)
                emit("looking")
                continue
            if r == "declined":
                emit("declined")
                pause(3.0)
                emit("looking")
            if stop.is_set():
                return None
        stop.wait(2.0)
    return None


def show_pair(code):
    """--pair: the pairing window. It looks for a phone that is asking to pair and shows a six digit number that the person types on the phone. A right entry makes the phone show a second number, which the person types in this window and confirms with Pair: a device that is not a real phone in front of the person cannot show it, so it cannot pair. The old typed code stays underneath as a fallback."""
    if not pair_window_singleton():
        log("a pairing window is already open: it was asked to come forward")
        return 0
    set_dpi_aware()                                                   # per-monitor aware: sharp text on a scaled screen instead of a blurry stretched window
    root = tk.Tk()
    th = Theme(root)
    th.window(root, "Typeferry pairing")
    root.attributes("-topmost", True)                                 # it must not hide behind the window the person was using
    wrap = 400
    root.minsize(th.px(456), 1)                                       # the same width in every state, so the window does not jump sideways
    page = tk.Frame(root, bg=PALETTE["bg"], padx=th.px(28), pady=th.px(26))
    page.pack(fill="both", expand=True)
    th.label(page, "Pair your phone", 18, True).pack(anchor="w")
    head = th.label(page, "", 12, True, "warn", wrap=wrap)
    head.pack(fill="x", pady=(th.px(16), th.px(2)))
    sub = th.label(page, "", 10, False, "muted", wrap=wrap)
    sub.pack(fill="x", pady=(0, th.px(16)))
    answer = {"v": None, "check": "", "probe": None, "prompted": False, "cancel": False}
    gate = threading.Event()
    q = queue.Queue()
    stop = threading.Event()

    def say(headline, detail="", tone="warn"):
        head.config(text=headline, fg=tone_color(tone))
        sub.config(text=detail)

    card = th.card(page)
    inner = tk.Frame(card, bg=PALETTE["card"], padx=th.px(20), pady=th.px(16))
    inner.pack()
    th.label(inner, "Number for the phone", 10, False, "muted", bg="card", anchor="center").pack()
    big = th.label(inner, "", 40, True, "text", bg="card", anchor="center", mono=True)
    big.pack(pady=(th.px(2), th.px(14)))
    th.label(inner, "Number from the phone", 10, False, "muted", bg="card", anchor="center").pack()
    entry = th.entry(inner)
    entry.pack(pady=(th.px(6), th.px(14)), ipady=th.px(6))
    keypad = tk.Frame(inner, bg=PALETTE["card"])                      # clickable digits: no keyboard of any kind is needed to finish pairing
    keypad.pack()
    for i, label in enumerate("1234567890"):
        th.button(keypad, label, lambda d=label: entry.insert("end", d) if entry.cget("state") == "normal" else None, "secondary", 52, 38, 11).grid(row=i // 5, column=i % 5, padx=th.px(3), pady=th.px(3))
    th.button(keypad, "Delete", lambda: entry.delete(max(0, len(entry.get()) - 1), "end") if entry.cget("state") == "normal" else None, "secondary", 52, 34, 10).grid(row=2, column=0, columnspan=5, sticky="ew", padx=th.px(3), pady=(th.px(3), 0))
    th.label(inner, "No keyboard? Click the digits to type with the mouse.", 9, False, "muted", bg="card", anchor="center").pack(pady=(th.px(10), 0))

    def respond(v):
        answer["v"] = v
        yes_btn.config(state="disabled")
        no_btn.config(state="disabled")
        entry.config(state="disabled")
        say("Checking with the phone..." if v else "Cancelled", "", "warn" if v else "bad")
        gate.set()

    def submit():
        typed = entry.get()
        if sum(1 for ch in typed if unicodedata.category(ch) == "Nd") != 6:
            say("Six digits needed", "Type the six digits the phone shows, then press Pair this phone.", "bad")
            return
        respond(check_matches(typed, answer["check"]))          # a wrong number ends this attempt: nothing is paired
    entry.bind("<Return>", lambda e: submit())
    row = tk.Frame(page, bg=PALETTE["bg"])
    row.columnconfigure(0, weight=1, uniform="b")
    row.columnconfigure(1, weight=1, uniform="b")
    no_btn = th.button(row, "Cancel", lambda: (answer.__setitem__("cancel", True), respond(False)), "secondary", 150, 42, 10)
    yes_btn = th.button(row, "Pair this phone", submit, "primary", 150, 42, 10)
    no_btn.grid(row=0, column=0, sticky="ew", padx=(0, th.px(5)))
    yes_btn.grid(row=0, column=1, sticky="ew", padx=(th.px(5), 0))
    tail = tk.Frame(page, bg=PALETTE["bg"])
    tail.pack(fill="x")

    def reveal():
        fallback.pack_forget()
        shown.pack(fill="x", pady=(th.px(16), 0))
        recenter()
    fallback = th.button(tail, "Show code instead", reveal, "ghost", 160, 34, 9)          # the code is the one long lived secret: it is not shown beside a screen share until the person asks
    fallback.pack(pady=(th.px(14), 0))
    shown = tk.Frame(tail, bg=PALETTE["bg"])
    th.label(shown, "Type this code on the phone", 10, False, "muted", anchor="center", justify="center").pack(fill="x")
    th.label(shown, LC.pretty(code), 15, True, "text", anchor="center", justify="center", mono=True).pack(fill="x", pady=(th.px(4), 0))

    def recenter():
        th.center(root)

    def decide(sas, check, host=""):
        gate.clear()
        answer["v"] = None
        answer["check"] = check
        answer["prompted"] = True
        q.put(("compare", (sas, host, check)))
        end = time.monotonic() + PAIR_DECIDE_S
        while not gate.wait(0.5):
            probe = answer["probe"]
            if stop.is_set() or time.monotonic() > end or (probe is not None and probe()):          # closed, out of time, or the phone already said no
                return False
        return answer["v"]

    alive = {"on": False, "paired": False}

    def worker():
        def try_host(host):
            return pair_with(host, lambda sas, check, h=host: decide(sas, check, h), lambda probe: answer.__setitem__("probe", probe))
        if pair_search(open_hosts, try_host, lambda kind, val=None: q.put((kind, val)), stop, answer) == "paired":
            alive["paired"] = True

    AGAIN = "Open the program again, then use its Pair button."

    def run_worker():
        alive["on"] = True
        try:
            worker()
        finally:
            alive["on"] = False

    def pump():
        if pair_window_wake_requested():                              # another start asked for the window: bring this one forward, and look again if it had given up
            try:
                root.deiconify()
                root.lift()
                root.attributes("-topmost", True)
            except tk.TclError:
                pass
            if not alive["on"] and not alive["paired"] and not stop.is_set():
                threading.Thread(target=run_worker, daemon=True).start()
        try:
            while True:
                kind, val = q.get_nowait()
                if kind != "compare":
                    card.pack_forget()
                    row.pack_forget()
                    big.config(text="")
                    yes_btn.config(state="normal")
                    no_btn.config(state="normal")
                if kind == "looking":
                    say("Looking for your phone", "On the phone, open Setup guide and go to Pair with your PC.", "warn")
                elif kind == "compare":
                    sas, peer, check = val
                    entry.config(state="normal")
                    entry.delete(0, "end")
                    card.pack(before=tail, fill="x")
                    row.pack(before=tail, fill="x", pady=(th.px(16), 0))
                    big.config(text=sas[:3] + " " + sas[3:])
                    yes_btn.config(state="normal")
                    no_btn.config(state="normal")
                    say("Type this number on the phone", ("Phone found at %s. " % peer if peer else "") + "Then type the number it shows below.", "text")
                    entry.focus_set()
                    if autoyes_enabled():             # test only, never in the packaged program (it would defeat the person's own decision)
                        log("test: the window shows " + sas)
                        log("test: the window expects " + check)

                        def autoyes_poll():
                            if os.path.exists(AUTOYES_GO):
                                try:
                                    os.remove(AUTOYES_GO)
                                except OSError:
                                    pass
                                entry.insert(0, check)
                                yes_btn.invoke()
                            elif not stop.is_set():
                                root.after(300, autoyes_poll)
                        autoyes_poll()
                elif kind == "lost":
                    say("The phone stopped answering", "Looking again...", "warn")
                elif kind == "expired":
                    say("Time is up", AGAIN, "bad")
                elif kind == "error":
                    say("Could not save the code", "The phone accepted. " + AGAIN, "bad")
                elif kind == "cancelled":
                    say("Skipped that device", "Still looking for your phone. Close this window to stop.", "warn")
                elif kind == "declined":
                    say("Not paired", "The numbers did not match, or one side said no.", "bad")
                elif kind == "done":
                    fallback.pack_forget()
                    shown.pack_forget()
                    say("Paired", "This window closes by itself.", "good")
                    root.after(2500, root.destroy)
                recenter()
        except queue.Empty:
            pass
        root.after(150, pump)
    root.protocol("WM_DELETE_WINDOW", lambda: (stop.set(), gate.set(), root.destroy()))
    th.center(root)
    threading.Thread(target=run_worker, daemon=True).start()
    root.after(150, pump)
    root.mainloop()
    stop.set()
    return 0


def main():
    args = sys.argv[1:]
    if "--uninstall" in args:
        return uninstall()
    code = load_code()
    if not code:
        tell_person(_code_problem[0] or "The pairing code file could not be used, so the receiver did not start.")          # the log line alone left the tray icon missing and the Pair button doing nothing
        return 1
    if "--pair" in args:
        return show_pair(code)
    if "--push-code" in args:
        return push_code(code)
    mutex = kernel32.CreateMutexW(None, False, MUTEX_NAME)          # one receiver per user session; the handle must stay alive
    if ctypes.get_last_error() == 183 or not mutex:
        running = read_running()
        if running is None:                                           # a receiver from before this file existed: judge by the start time in our own folder
            try:
                running = (DATA, RECEIVER_VERSION, float(open(STARTED_FILE, encoding="utf-8").read().strip()))
            except (OSError, ValueError):
                running = (DATA, RECEIVER_VERSION, 0.0)
        action, text = duplicate_start_action(running, DATA, RECEIVER_VERSION, time.time())
        if action == "window":
            if not show_running_status():                             # the running receiver's status window is the way back; a receiver with no tray window to ask gets the pairing window, as before
                open_pair_window()
        elif action == "message":
            log("second start refused: " + text)
            tell_person(text)
        elif action == "replace":
            pid = running_pid()
            if not (ask_person(text) and pid_is_receiver(pid)):
                return 0
            log("replacing the running receiver (process %d) with version %s" % (pid, RECEIVER_VERSION))
            ask_running_to_quit(4.0)                                  # a version with a tray icon lifts its keys and removes its icon itself; an older one has no window to ask
            subprocess.run(["taskkill", "/F", "/T", "/PID", str(pid)], capture_output=True, timeout=30, creationflags=0x08000000)
            kernel32.CloseHandle(mutex)                               # our handle keeps the mutex alive: let go of it before asking again
            end = time.monotonic() + 6.0
            while time.monotonic() < end:
                mutex = kernel32.CreateMutexW(None, False, MUTEX_NAME)
                if ctypes.get_last_error() != 183 and mutex:
                    break
                kernel32.CloseHandle(mutex)
                time.sleep(0.3)
            else:
                tell_person("The running receiver did not end. Quit it, then open this one again.")
                return 0
        else:
            return 0
        if action != "replace":
            return 0
    try:
        with open(STARTED_FILE, "w", encoding="utf-8") as f:
            f.write("%.0f" % time.time())
    except OSError:
        pass
    try:
        with open(RUNNING_FILE, "w", encoding="utf-8") as f:
            f.write("%s\n%s\n%.0f\n%d\n" % (DATA, RECEIVER_VERSION, time.time(), os.getpid()))
    except OSError:
        pass
    KEYS[0] = KeyStore(code, on_change=lambda: (log("the pairing code changed: using the new one"), _last_scan.__setitem__(0, -1e9)))
    if not NO_ADB:
        threading.Thread(target=adb_forward_keeper, daemon=True).start()
    try:
        release_stale_modifiers()
    except OSError:
        pass
    log("receiver started")
    ensure_autostart()
    set_dpi_aware()                                                   # before any window exists (the tray's menu is drawn by this process)
    start_companion()
    if not os.path.exists(PAIRED_FILE):
        open_pair_window()
    try:
        while not QUIT.is_set():
            if _stuck[0]:
                _stuck[0] = not release_everything()                  # a link ended while Windows refused the release: keep trying until Windows takes it
            try:
                key = KEYS[0].get()                                   # the pairing window just stored a new code: use it from now on, no restart needed
                r = take_late_link() or find_phone(key)               # a better link found just after its predecessor ended is already the live one: use it before looking again
                while r and not QUIT.is_set():                        # a better link (the cable plugged in) hands over to the next pass of this loop with no gap
                    sock, sess, how = r
                    log("phone connected via " + how)
                    LINK.connect(how)
                    try:
                        open(PAIRED_FILE, "w", encoding="utf-8").write(time.strftime("%Y-%m-%d %H:%M:%S"))
                    except OSError:
                        pass
                    r = serve(sock, sess, how, KEYS[0].get)               # the function, not the key: the watcher inside serve() must see a code changed while this link is up
                    if r is None:
                        LINK.disconnect()
                        log("phone disconnected")
                        _last_logged.pop("looking", None)             # the next failed look is written at once, so the log says why the phone is not coming back
                if r:                                                 # Quit arrived while a better link was being handed over: that link is not wanted either
                    r[0].close()
                else:
                    log_limited("looking", dial_summary(), DIAL_LOG_GAP_S)          # while no phone answers: one short line saying why, at most once a minute
            except Exception:
                log("error: " + traceback.format_exc().replace("\n", " | "))
                QUIT.wait(3.0)
            _late_event.wait(2.0)                                     # two seconds between looks, cut short the moment a late better link is parked
    finally:
        LINK.disconnect()
        MAIN_DONE.set()
    return 0


if __name__ == "__main__":
    rc = 1
    try:
        rc = main()
    finally:
        final_cleanup()
    if _tray[0] is not None or _ui_started[0]:
        os._exit(rc or 0)                                             # a window thread's Tk must not be torn down by the interpreter's own exit
    sys.exit(rc)
