"""
Telegram musiqa boti (aiogram 3.x) — To'liq Tuzatilgan Yakuniy Versiya.
- 10 talik ro'yxat va sahifalash (⬅️ ❌ ➡️)
- YouTube Shorts / Reels / TikTok / Voice -> FFmpeg WAV -> Shazam -> 10 talik variantlar
- YouTube (Flat Search + Anti-Bot) + SoundCloud qidiruv va Avto-Fallback zanjiri
- Slowed, Bass, 8D audio effektlar (FFmpeg)
- Qo'shiq matni (LRCLIB + Gemini AI), Pleylist (/my), Top (/top)
- Admin panel va statistika (/stat, /channels, /addch, /delch, /broadcast, /setcookies)
"""

import asyncio
import difflib
import hashlib
import html
import io
import json
import logging
import math
import os
import re
import secrets
import shutil
import sqlite3
import tempfile
import time
import urllib.parse
import urllib.request
from collections import OrderedDict
from concurrent.futures import ThreadPoolExecutor
from contextlib import asynccontextmanager, contextmanager

from dotenv import load_dotenv

load_dotenv()

from aiogram import BaseMiddleware, Bot, Dispatcher, F
from aiogram.client.session.aiohttp import AiohttpSession
from aiogram.exceptions import TelegramBadRequest, TelegramForbiddenError, TelegramRetryAfter
from aiogram.filters import Command, CommandObject, CommandStart
from aiogram.types import (
    BotCommand,
    CallbackQuery,
    FSInputFile,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Message,
)

import yt_dlp

try:
    from shazamio import Shazam
except ImportError:
    Shazam = None

try:
    from google import genai
except ImportError:
    genai = None

# ==================== SOZLAMALAR ====================
BOT_TOKEN = os.getenv("BOT_TOKEN", "")
ADMIN_ID = int(os.getenv("ADMIN_ID", "0") or 0)
GEMINI_API_KEY = os.getenv("GEMINI_API_KEY", "")
GEMINI_MODEL = "gemini-2.5-flash"

DB_PATH = os.getenv("DB_PATH", "/data/music_database.db")
COOKIES_FILE = os.getenv("COOKIES_FILE", "/data/cookies.txt")
HEAVY_WORKERS = max(1, int(os.getenv("HEAVY_WORKERS", "4") or 4))
DROP_PENDING = os.getenv("DROP_PENDING", "1") != "0"

MAX_AUDIO_DURATION_SEC = 900
MIN_AUDIO_DURATION_SEC = 30
MAX_DOWNLOAD_BYTES = 48 * 1024 * 1024
TELEGRAM_UPLOAD_LIMIT = 49 * 1024 * 1024
PLAYLIST_PAGE_SIZE = 10
SEARCH_RESULTS_LIMIT = 30
BROADCAST_DELAY_SEC = 0.05
HEAVY_COOLDOWN_SEC = 1.0
MAX_LYRICS_MESSAGES = 4
FFMPEG_TIMEOUT_SEC = 180
SUB_CACHE_TTL_SEC = 300

SOCIAL_HOSTS = ("instagram.com", "tiktok.com", "vt.tiktok.com", "vm.tiktok.com")
MUSIC_HOSTS = ("youtube.com", "youtu.be", "music.youtube.com", "soundcloud.com", "on.soundcloud.com")
AUDIO_EXTS = {".mp3", ".m4a", ".ogg", ".opus", ".webm", ".wav", ".aac", ".flac"}

FFMPEG_PATH = shutil.which("ffmpeg")
FFPROBE_PATH = shutil.which("ffprobe")

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s: %(message)s")
log = logging.getLogger("musicbot")

if not BOT_TOKEN:
    raise SystemExit("BOT_TOKEN topilmadi: .env fayliga BOT_TOKEN=... qatorini qo'shing.")

bot = Bot(token=BOT_TOKEN, session=AiohttpSession(timeout=300))
dp = Dispatcher()
gemini_client = genai.Client(api_key=GEMINI_API_KEY) if (genai and GEMINI_API_KEY) else None

HEAVY_POOL = ThreadPoolExecutor(max_workers=HEAVY_WORKERS, thread_name_prefix="heavy")
FFMPEG_SEM = asyncio.Semaphore(2)

BOT_USERNAME = ""
BOT_ID = 0


# ==================== KICHIK YORDAMCHI SINFLAR ====================
class TTLCache:
    def __init__(self, ttl: float, max_items: int):
        self.ttl = ttl
        self.max_items = max_items
        self._data: "OrderedDict[object, tuple[float, object]]" = OrderedDict()

    def set(self, key, value) -> None:
        now = time.monotonic()
        self._data[key] = (now, value)
        self._data.move_to_end(key)
        self._evict(now)

    def get(self, key, default=None):
        item = self._data.get(key)
        if item is None:
            return default
        ts, value = item
        if time.monotonic() - ts > self.ttl:
            self._data.pop(key, None)
            return default
        return value

    def pop(self, key) -> None:
        self._data.pop(key, None)

    def clear(self) -> None:
        self._data.clear()

    def _evict(self, now: float) -> None:
        while self._data:
            oldest_key = next(iter(self._data))
            ts, _ = self._data[oldest_key]
            if len(self._data) > self.max_items or now - ts > self.ttl:
                self._data.popitem(last=False)
            else:
                break


class KeyedLocks:
    def __init__(self):
        self._locks: dict[str, list] = {}

    @asynccontextmanager
    async def acquire(self, key: str):
        entry = self._locks.get(key)
        if entry is None:
            entry = [asyncio.Lock(), 0]
            self._locks[key] = entry
        entry[1] += 1
        try:
            async with entry[0]:
                yield
        finally:
            entry[1] -= 1
            if entry[1] <= 0 and self._locks.get(key) is entry:
                del self._locks[key]


search_cache = TTLCache(ttl=3600, max_items=5000)
sub_ok_cache = TTLCache(ttl=SUB_CACHE_TTL_SEC, max_items=100_000)
_last_heavy = TTLCache(ttl=120, max_items=100_000)
_busy_users: set[int] = set()
keyed_locks = KeyedLocks()


# ==================== MATN VA VAQT YORDAMCHILARI ====================
_UZ_CYR_TO_LAT = {
    "а": "a", "б": "b", "в": "v", "г": "g", "д": "d", "е": "e", "ё": "yo", "ж": "j", "з": "z",
    "и": "i", "й": "y", "к": "k", "л": "l", "м": "m", "н": "n", "о": "o", "п": "p", "р": "r",
    "с": "s", "т": "t", "у": "u", "ф": "f", "х": "x", "ц": "s", "ч": "ch", "ш": "sh", "щ": "sh",
    "ъ": "", "ы": "i", "ь": "", "э": "e", "ю": "yu", "я": "ya",
    "ў": "o", "қ": "q", "ғ": "g", "ҳ": "h",
}
_APOSTROPHES = "'`´ʻʼ‘’′ʹ"
_APOS_RE = re.compile("[" + re.escape(_APOSTROPHES) + "]")


def normalize_text(s: str) -> str:
    s = (s or "").lower()
    s = "".join(_UZ_CYR_TO_LAT.get(ch, ch) for ch in s)
    s = _APOS_RE.sub("", s)
    s = re.sub(r"[\W_]+", " ", s)
    return s.strip()


def format_duration(seconds: int | float | None) -> str:
    sec = int(seconds or 0)
    if sec <= 0:
        return ""
    mins, rem = divmod(sec, 60)
    return f"{mins}:{rem:02d}"


def text_similarity(a: str, b: str) -> float:
    a, b = normalize_text(a), normalize_text(b)
    if not a or not b:
        return 0.0
    if a == b:
        return 1.0
    ratio = difflib.SequenceMatcher(None, a, b).ratio()
    if (a in b or b in a) and min(len(a), len(b)) >= 4:
        ratio = max(ratio, 0.85)
    return ratio


def split_text(text: str, limit: int = 3600) -> list[str]:
    parts: list[str] = []
    current = ""
    for line in text.splitlines(keepends=True):
        while len(line) > limit:
            if current:
                parts.append(current)
                current = ""
            parts.append(line[:limit])
            line = line[limit:]
        if len(current) + len(line) > limit:
            parts.append(current)
            current = ""
        current += line
    if current:
        parts.append(current)
    return parts


def host_in(host: str, domains: tuple[str, ...]) -> bool:
    host = (host or "").lower()
    return any(host == d or host.endswith("." + d) for d in domains)


def is_short_video_url(url: str) -> bool:
    parsed = urllib.parse.urlparse(url)
    host = (parsed.hostname or "").lower()
    path = (parsed.path or "").lower()
    if host_in(host, SOCIAL_HOSTS):
        return True
    if host_in(host, ("youtube.com", "youtu.be")) and "/shorts/" in path:
        return True
    return False


_URL_RE = re.compile(r"https?://[^\s<>\"']+", re.IGNORECASE)
_BARE_DOMAIN_RE = re.compile(
    r"(?<![\w@./-])(?:[\w-]+\.)*(?:instagram\.com|tiktok\.com|youtu\.be|youtube\.com|soundcloud\.com)(?:/[^\s<>\"']*)?",
    re.IGNORECASE,
)


def extract_url(text: str) -> str | None:
    m = _URL_RE.search(text)
    if m:
        return m.group(0).rstrip(").,;]>")
    m = _BARE_DOMAIN_RE.search(text)
    if m:
        return "https://" + m.group(0).rstrip(").,;]>")
    return None


def safe_filename(performer: str, title: str, ext: str = "mp3") -> str:
    base = re.sub(r'[\\/*?:"<>|]', "", f"{performer or ''} - {title or ''}").strip()[:60] or "track"
    return f"{base}.{ext}"


# ==================== MA'LUMOTLAR BAZASI ====================
@contextmanager
def db_conn():
    conn = sqlite3.connect(DB_PATH, timeout=15)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA synchronous=NORMAL")
    try:
        with conn:
            yield conn
    finally:
        conn.close()


def ensure_column(conn: sqlite3.Connection, table: str, column: str, ddl: str) -> None:
    cols = {r["name"] for r in conn.execute(f"PRAGMA table_info({table})").fetchall()}
    if column not in cols:
        conn.execute(f"ALTER TABLE {table} ADD COLUMN {column} {ddl}")


def init_db() -> None:
    dirname = os.path.dirname(DB_PATH)
    if dirname:
        os.makedirs(dirname, exist_ok=True)
    with db_conn() as conn:
        try:
            conn.execute("PRAGMA journal_mode=WAL")
        except sqlite3.DatabaseError:
            pass

        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS users (
                user_id INTEGER PRIMARY KEY,
                gender TEXT DEFAULT NULL,
                joined_ts REAL DEFAULT 0,
                last_active_ts REAL DEFAULT 0,
                searches_count INTEGER DEFAULT 0,
                gender_prompted INTEGER DEFAULT 0,
                blocked INTEGER DEFAULT 0
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS tracks (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                source_id TEXT UNIQUE,
                title TEXT,
                performer TEXT,
                duration INTEGER DEFAULT 0,
                file_id TEXT,
                webpage_url TEXT,
                lyrics TEXT DEFAULT NULL,
                likes INTEGER DEFAULT 0,
                downloads INTEGER DEFAULT 1,
                search_text TEXT DEFAULT NULL,
                created_ts REAL DEFAULT 0
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS favorites (
                user_id INTEGER,
                track_id INTEGER,
                added_ts REAL,
                PRIMARY KEY (user_id, track_id)
            )
            """
        )
        conn.execute(
            """
            CREATE TABLE IF NOT EXISTS channels (
                channel_id TEXT PRIMARY KEY,
                title TEXT,
                invite_link TEXT
            )
            """
        )

        ensure_column(conn, "users", "gender_prompted", "INTEGER DEFAULT 0")
        ensure_column(conn, "users", "blocked", "INTEGER DEFAULT 0")
        ensure_column(conn, "tracks", "search_text", "TEXT DEFAULT NULL")


def register_or_touch_user(user_id: int, inc_search: bool = False) -> sqlite3.Row:
    now = time.time()
    with db_conn() as conn:
        conn.execute(
            """
            INSERT INTO users (user_id, joined_ts, last_active_ts, searches_count)
            VALUES (?, ?, ?, ?)
            ON CONFLICT(user_id) DO UPDATE SET
                last_active_ts = excluded.last_active_ts,
                searches_count = searches_count + excluded.searches_count,
                blocked = 0
            """,
            (user_id, now, now, 1 if inc_search else 0),
        )
        return conn.execute("SELECT * FROM users WHERE user_id = ?", (user_id,)).fetchone()


def get_track_by_id(track_id: int) -> sqlite3.Row | None:
    with db_conn() as conn:
        return conn.execute("SELECT * FROM tracks WHERE id = ?", (track_id,)).fetchone()


def get_track_by_source(source_id: str) -> sqlite3.Row | None:
    with db_conn() as conn:
        return conn.execute("SELECT * FROM tracks WHERE source_id = ?", (source_id,)).fetchone()


def save_or_update_track(source_id: str, title: str, performer: str, duration: int, file_id: str, webpage_url: str) -> int:
    search_text = normalize_text(f"{performer or ''} {title or ''}")
    with db_conn() as conn:
        conn.execute(
            """
            INSERT INTO tracks (source_id, title, performer, duration, file_id, webpage_url, search_text, created_ts)
            VALUES (?, ?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(source_id) DO UPDATE SET
                file_id = excluded.file_id,
                downloads = downloads + 1
            """,
            (source_id, title, performer, duration, file_id, webpage_url, search_text, time.time()),
        )
        return conn.execute("SELECT id FROM tracks WHERE source_id = ?", (source_id,)).fetchone()[0]


def bump_downloads(track_id: int) -> None:
    with db_conn() as conn:
        conn.execute("UPDATE tracks SET downloads = downloads + 1 WHERE id = ?", (track_id,))


def save_lyrics(track_id: int, lyrics: str) -> None:
    with db_conn() as conn:
        conn.execute("UPDATE tracks SET lyrics = ? WHERE id = ?", (lyrics, track_id))


def add_favorite(user_id: int, track_id: int) -> bool:
    with db_conn() as conn:
        cur = conn.execute(
            "INSERT OR IGNORE INTO favorites (user_id, track_id, added_ts) VALUES (?, ?, ?)",
            (user_id, track_id, time.time()),
        )
        if cur.rowcount == 0:
            return False
        conn.execute("UPDATE tracks SET likes = likes + 1 WHERE id = ?", (track_id,))
        return True


def remove_favorite(user_id: int, track_id: int) -> bool:
    with db_conn() as conn:
        cur = conn.execute("DELETE FROM favorites WHERE user_id = ? AND track_id = ?", (user_id, track_id))
        if cur.rowcount > 0:
            conn.execute("UPDATE tracks SET likes = MAX(likes - 1, 0) WHERE id = ?", (track_id,))
            return True
        return False


def get_user_favorites(user_id: int) -> list[sqlite3.Row]:
    with db_conn() as conn:
        return conn.execute(
            """
            SELECT t.* FROM tracks t
            JOIN favorites f ON f.track_id = t.id
            WHERE f.user_id = ?
            ORDER BY f.added_ts DESC
            """,
            (user_id,),
        ).fetchall()


def get_top_tracks(limit: int = 10) -> list[sqlite3.Row]:
    with db_conn() as conn:
        return conn.execute(
            "SELECT * FROM tracks WHERE file_id IS NOT NULL ORDER BY likes DESC, downloads DESC LIMIT ?",
            (limit,),
        ).fetchall()


def get_channels() -> list[sqlite3.Row]:
    with db_conn() as conn:
        return conn.execute("SELECT * FROM channels").fetchall()


def add_channel(channel_id: str, title: str, invite_link: str) -> None:
    with db_conn() as conn:
        conn.execute(
            "INSERT OR REPLACE INTO channels (channel_id, title, invite_link) VALUES (?, ?, ?)",
            (channel_id, title, invite_link),
        )


def del_channel(channel_id: str) -> None:
    with db_conn() as conn:
        conn.execute("DELETE FROM channels WHERE channel_id = ?", (channel_id,))


def get_stats() -> dict:
    now = time.time()
    with db_conn() as conn:
        def scalar(sql: str, *params) -> int:
            return conn.execute(sql, params).fetchone()[0]

        return {
            "total": scalar("SELECT COUNT(*) FROM users"),
            "active_24h": scalar("SELECT COUNT(*) FROM users WHERE last_active_ts >= ?", now - 86400),
            "active_7d": scalar("SELECT COUNT(*) FROM users WHERE last_active_ts >= ?", now - 7 * 86400),
            "active_30d": scalar("SELECT COUNT(*) FROM users WHERE last_active_ts >= ?", now - 30 * 86400),
            "blocked": scalar("SELECT COUNT(*) FROM users WHERE blocked = 1"),
            "tracks": scalar("SELECT COUNT(*) FROM tracks"),
            "downloads": scalar("SELECT COALESCE(SUM(downloads), 0) FROM tracks"),
            "favs": scalar("SELECT COUNT(*) FROM favorites"),
        }


def get_broadcast_user_ids() -> list[int]:
    with db_conn() as conn:
        return [r["user_id"] for r in conn.execute("SELECT user_id FROM users WHERE blocked = 0").fetchall()]


def mark_blocked(user_ids: list[int]) -> None:
    if not user_ids:
        return
    with db_conn() as conn:
        conn.executemany("UPDATE users SET blocked = 1 WHERE user_id = ?", [(u,) for u in user_ids])


# ==================== XATO TURLARI ====================
class AudioError(Exception):
    pass


class AudioTooLong(AudioError):
    pass


class AudioTooBig(AudioError):
    pass


# ==================== QIDIRUV VA YUKLASH (YOUTUBE + COOKIES + SOUNDCLOUD) ====================
_JUNK_RE = re.compile(
    r"\s*[\(\[](?:official|audio|video|music|lyrics|hd|4k|karaoke|clip|klip|prem\w*).*?[\)\]]",
    re.IGNORECASE,
)


def parse_artist_title(raw_title: str, uploader: str = "") -> tuple[str, str]:
    clean = _JUNK_RE.sub("", raw_title or "").strip()
    for sep in (" — ", " – ", " - "):
        if sep in clean:
            left, right = clean.split(sep, 1)
            return left.strip(), right.strip()
    clean_up = re.sub(r"\s*(?:- topic|official|music|tv|vevo)\b", "", uploader or "", flags=re.I).strip()
    return (clean_up or "Ijrochi").strip(), clean or (raw_title or "Qo'shiq")


def build_ydl_opts(**extra) -> dict:
    opts = {
        "quiet": True,
        "no_warnings": True,
        "socket_timeout": 20,
        "retries": 3,
        "geo_bypass": True,
        "nocheckcertificate": True,
        "extractor_args": {
            "youtube": {
                "player_client": ["tv", "ios", "android", "web"],
            }
        },
        "http_headers": {
            "User-Agent": (
                "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
                "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36"
            )
        },
    }
    if COOKIES_FILE and os.path.isfile(COOKIES_FILE) and os.path.getsize(COOKIES_FILE) > 0:
        opts["cookiefile"] = COOKIES_FILE
    opts.update(extra)
    return opts


def search_music_sync(query: str, max_results: int = SEARCH_RESULTS_LIMIT) -> list[dict]:
    # MUHIM: extract_flat="in_playlist" YouTube bot-blokirovkasini oldini oladi va 10 barobar tez ishlaydi!
    opts = build_ydl_opts(extract_flat="in_playlist", skip_download=True)
    results: list[dict] = []
    seen: set = set()

    # 1. YouTube qidiruvi
    try:
        with yt_dlp.YoutubeDL(opts) as ydl:
            info = ydl.extract_info(f"ytsearch{max_results}:{query}", download=False)
            entries = (info or {}).get("entries", []) if info else []
            for e in entries:
                if not e:
                    continue
                eid = e.get("id")
                if not eid or eid in seen:
                    continue
                dur = int(e.get("duration") or 0)
                if dur and (dur > MAX_AUDIO_DURATION_SEC or dur < MIN_AUDIO_DURATION_SEC):
                    continue
                url = e.get("url") or f"https://www.youtube.com/watch?v={eid}"
                if not url.startswith("http"):
                    url = f"https://www.youtube.com/watch?v={eid}"
                artist, title = parse_artist_title(
                    e.get("title") or query, e.get("uploader") or e.get("channel") or ""
                )
                seen.add(eid)
                results.append(
                    {
                        "source_id": f"yt_{eid}",
                        "title": title,
                        "performer": artist,
                        "duration": dur,
                        "url": url,
                    }
                )
    except Exception as ex:
        log.warning("YouTube qidiruv xatosi: %s", ex)

    # 2. SoundCloud qidiruvi (zaxira yoki to'ldiruvchi sifatida)
    if len(results) < max_results:
        need = max_results - len(results)
        try:
            with yt_dlp.YoutubeDL(opts) as ydl:
                info = ydl.extract_info(f"scsearch{need}:{query}", download=False)
                for e in ((info or {}).get("entries") or []):
                    if not e:
                        continue
                    eid = str(e.get("id") or "")
                    url = e.get("url") or e.get("webpage_url")
                    if not url or eid in seen:
                        continue
                    dur = int(e.get("duration") or 0)
                    if dur and (dur > MAX_AUDIO_DURATION_SEC or dur < MIN_AUDIO_DURATION_SEC):
                        continue
                    artist, title = parse_artist_title(e.get("title") or query, e.get("uploader") or "")
                    seen.add(eid or url)
                    results.append(
                        {
                            "source_id": f"sc_{eid or hashlib.md5(url.encode()).hexdigest()[:10]}",
                            "title": title,
                            "performer": artist,
                            "duration": dur,
                            "url": url,
                        }
                    )
        except Exception as ex:
            log.warning("SoundCloud qidiruv xatosi: %s", ex)

    return results[:max_results]


def download_media_sync(url: str, outdir: str, is_short: bool = False) -> tuple[str, dict, str]:
    fmt = (
        "bestaudio[ext=m4a]/bestaudio[ext=mp3]/bestaudio/best"
        if not is_short
        else "bestaudio/best[filesize<40M]/best"
    )
    opts = build_ydl_opts(
        format=fmt,
        outtmpl=os.path.join(outdir, "media.%(ext)s"),
        noplaylist=True,
        playlistend=1,
        max_filesize=MAX_DOWNLOAD_BYTES,
    )
    # ffprobe va ffmpeg ikkalasi ham bo'lsagina yt-dlp postprocessor ishlatamiz
    if FFMPEG_PATH and FFPROBE_PATH and not is_short:
        opts["postprocessors"] = [
            {"key": "FFmpegExtractAudio", "preferredcodec": "mp3", "preferredquality": "192"}
        ]

    with yt_dlp.YoutubeDL(opts) as ydl:
        info = ydl.extract_info(url, download=True)

    info = info or {}
    if info.get("_type") == "playlist":
        entries = [e for e in (info.get("entries") or []) if e]
        info = entries[0] if entries else {}

    files = [
        os.path.join(outdir, f)
        for f in os.listdir(outdir)
        if os.path.isfile(os.path.join(outdir, f)) and not f.endswith(".part")
    ]
    if not files:
        raise AudioError("Media faylni yuklab bo'lmadi.")

    path = max(files, key=os.path.getsize)
    ext = os.path.splitext(path)[1].lstrip(".").lower()
    return path, info, ext


async def ensure_mp3_or_m4a(path: str, ext: str) -> tuple[str, str]:
    """Agar yuklangan fayl .webm, .ogg yoki .mp4 bo'lsa, FFmpeg yordamida .mp3 ga o'giradi."""
    if ext in ("mp3", "m4a"):
        return path, ext
    if not FFMPEG_PATH:
        return path, ext

    out_path = os.path.splitext(path)[0] + "_conv.mp3"
    async with FFMPEG_SEM:
        proc = await asyncio.create_subprocess_exec(
            FFMPEG_PATH, "-y", "-i", path, "-vn", "-acodec", "libmp3lame", "-q:a", "4", out_path,
            stdout=asyncio.subprocess.DEVNULL,
            stderr=asyncio.subprocess.DEVNULL,
        )
        try:
            await asyncio.wait_for(proc.wait(), timeout=FFMPEG_TIMEOUT_SEC)
        except asyncio.TimeoutError:
            proc.kill()
            return path, ext

    if os.path.isfile(out_path) and os.path.getsize(out_path) > 1024:
        return out_path, "mp3"
    return path, ext


async def run_heavy(func, *args):
    return await asyncio.get_running_loop().run_in_executor(HEAVY_POOL, func, *args)


@asynccontextmanager
async def downloaded_audio(url: str, is_short: bool = False):
    outdir = tempfile.mkdtemp(prefix="musicbot_")
    try:
        path, info, ext = await run_heavy(download_media_sync, url, outdir, is_short)
        if not is_short:
            path, ext = await ensure_mp3_or_m4a(path, ext)
        yield path, info, ext
    finally:
        await asyncio.to_thread(shutil.rmtree, outdir, True)


# ==================== AUDIO EFFEKTLAR (SLOWED, BASS, 8D) ====================
FX_FILTERS = {
    "slowed": ("🌙 Slowed", "asetrate=44100*0.85,aresample=44100,atempo=0.95,aecho=0.8:0.88:60:0.4"),
    "bass": ("🔥 Bass Boosted", "bass=g=14:f=110:w=0.6,dynaudnorm"),
    "8d": ("🎧 8D Audio", "apulsator=hz=0.125,aecho=0.8:0.88:40:0.3"),
}


async def apply_audio_fx(input_path: str, output_path: str, fx_key: str) -> bool:
    if not FFMPEG_PATH or fx_key not in FX_FILTERS:
        return False
    _, af_filter = FX_FILTERS[fx_key]
    async with FFMPEG_SEM:
        proc = await asyncio.create_subprocess_exec(
            FFMPEG_PATH, "-y", "-i", input_path,
            "-vn", "-af", af_filter,
            "-acodec", "libmp3lame", "-b:a", "192k", output_path,
            stdout=asyncio.subprocess.DEVNULL,
            stderr=asyncio.subprocess.DEVNULL,
        )
        try:
            await asyncio.wait_for(proc.wait(), timeout=FFMPEG_TIMEOUT_SEC)
        except asyncio.TimeoutError:
            proc.kill()
            return False
    return os.path.isfile(output_path) and os.path.getsize(output_path) > 1024


# ==================== QO'SHIQ MATNI VA SHAZAM ====================
def fetch_lyrics_sync(performer: str, title: str) -> str | None:
    query = urllib.parse.quote(f"{performer} {title}")
    url = f"https://lrclib.net/api/search?q={query}"
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "TelegramMusicBot/2.0"})
        with urllib.request.urlopen(req, timeout=8) as resp:
            data = json.loads(resp.read().decode("utf-8"))
    except Exception:
        return None
    if not isinstance(data, list):
        return None

    best: str | None = None
    best_score = 0.0
    for item in data:
        plain = (item.get("plainLyrics") or "").strip()
        if len(plain) <= 20:
            continue
        name_score = text_similarity(item.get("trackName") or item.get("name") or "", title)
        if name_score < 0.65:
            continue
        artist = item.get("artistName") or ""
        artist_score = text_similarity(artist, performer)
        score = name_score + artist_score
        if score > best_score:
            best, best_score = plain, score
    return best


async def ai_lyrics(performer: str, title: str) -> str | None:
    if not gemini_client:
        return None
    try:
        res = await asyncio.wait_for(
            gemini_client.aio.models.generate_content(
                model=GEMINI_MODEL,
                contents=f"'{performer} - {title}' qo'shig'ining to'liq matnini (lyrics) yozib ber. Topilmasa faqat 'TOPILMADI' deb yoz.",
            ),
            timeout=20,
        )
    except Exception:
        return None
    text = (res.text or "").strip()
    if not text or "TOPILMADI" in text.upper():
        return None
    return text


async def prepare_wav_for_shazam(raw_bytes: bytes, start_sec: int = 0, duration_sec: int = 12) -> bytes:
    """Har qanday video/voice/audio faylni Shazam bexato o'qishi uchun 16kHz Mono WAV ga o'giradi."""
    if not FFMPEG_PATH:
        return raw_bytes
    with tempfile.TemporaryDirectory(prefix="shz_") as tmpdir:
        in_p = os.path.join(tmpdir, "in.media")
        out_p = os.path.join(tmpdir, "out.wav")
        with open(in_p, "wb") as f:
            f.write(raw_bytes)

        cmd = [FFMPEG_PATH, "-y"]
        if start_sec > 0:
            cmd += ["-ss", str(start_sec)]
        cmd += [
            "-i", in_p,
            "-t", str(duration_sec),
            "-vn", "-ac", "1", "-ar", "16000", "-f", "wav", out_p,
        ]
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            stdout=asyncio.subprocess.DEVNULL,
            stderr=asyncio.subprocess.DEVNULL,
        )
        try:
            await asyncio.wait_for(proc.wait(), timeout=25)
        except asyncio.TimeoutError:
            proc.kill()
            return raw_bytes

        if os.path.isfile(out_p) and os.path.getsize(out_p) > 1000:
            with open(out_p, "rb") as f:
                return f.read()
    return raw_bytes


async def recognize_with_shazam(media_bytes: bytes) -> str | None:
    if Shazam is None:
        return None
    shazam = Shazam()
    # Videoning boshidan (0s) va o'rtarog'idan (5s) sinab ko'ramiz
    for offset in (0, 5):
        try:
            wav_bytes = await prepare_wav_for_shazam(media_bytes, start_sec=offset, duration_sec=12)
            out = await asyncio.wait_for(shazam.recognize(wav_bytes), timeout=25)
            track = (out or {}).get("track")
            if track:
                title = (track.get("title") or "").strip()
                subtitle = (track.get("subtitle") or "").strip()
                if title or subtitle:
                    return f"{subtitle} - {title}".strip(" -")
        except Exception as e:
            log.warning("Shazam xatosi (offset=%s): %s", offset, e)
    return None


# ==================== TELEGRAM YORDAMCHILARI ====================
SUB_PROMPT = "Botdan foydalanish uchun quyidagi kanallarga obuna bo'ling:"
WELCOME_TEXT = (
    "👋 <b>Salom! Musiqa izlash uchun menga yuboring:</b>\n\n"
    "🎵 Qo'shiq yoki ijrochi nomi\n"
    "🎤 Ovozli xabar, audio yoki video (Shazam)\n"
    "🔗 Instagram, TikTok, YouTube yoki Shorts havolasi\n\n"
    "📂 /my — Pleylistingiz\n"
    "🔥 /top — Top musiqalar"
)

CLOSE_KB = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="❌", callback_data="delete_msg")]])


async def safe_delete(chat_id: int, message_id: int) -> None:
    try:
        await bot.delete_message(chat_id, message_id)
    except Exception:
        pass


async def chat_action(chat_id: int, action: str) -> None:
    try:
        await bot.send_chat_action(chat_id, action)
    except Exception:
        pass


def cb_chat_id(callback: CallbackQuery) -> int | None:
    return callback.message.chat.id if callback.message else None


@asynccontextmanager
async def heavy_slot(user_id: int):
    if user_id in _busy_users:
        yield "⏳ Oldingi so'rovingiz bajarilmoqda, biroz kuting."
        return
    last = _last_heavy.get(user_id)
    if last is not None:
        wait = HEAVY_COOLDOWN_SEC - (time.monotonic() - last)
        if wait > 0:
            yield f"⏳ {math.ceil(wait)} soniya kuting."
            return
    _busy_users.add(user_id)
    try:
        yield None
    finally:
        _busy_users.discard(user_id)
        _last_heavy.set(user_id, time.monotonic())


# ==================== KLAVIATURALAR ====================
def get_audio_caption(extra: str = "") -> str:
    prefix = f"{extra}\n" if extra else ""
    return f'{prefix}🔊 <a href="https://t.me/{BOT_USERNAME}">Musiqa topish</a>'


def get_track_keyboard(track_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="❤️", callback_data=f"fav_add:{track_id}"),
                InlineKeyboardButton(text="💔", callback_data=f"fav_del:{track_id}"),
                InlineKeyboardButton(text="🎤 Matn", callback_data=f"lyrics:{track_id}"),
                InlineKeyboardButton(text="❌", callback_data="delete_msg"),
            ],
            [
                InlineKeyboardButton(text="🌙 Slowed", callback_data=f"fx:slowed:{track_id}"),
                InlineKeyboardButton(text="🔥 Bass", callback_data=f"fx:bass:{track_id}"),
                InlineKeyboardButton(text="🎧 8D", callback_data=f"fx:8d:{track_id}"),
            ],
        ]
    )


def get_sub_keyboard(not_joined: list[sqlite3.Row]) -> InlineKeyboardMarkup:
    buttons = [[InlineKeyboardButton(text=f"➕ {ch['title']}", url=ch["invite_link"])] for ch in not_joined]
    buttons.append([InlineKeyboardButton(text="✅ Tasdiqlash", callback_data="check_subs")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)


def build_numbered_keyboard(
    item_callbacks: list[str],
    page: int = 0,
    total_items: int = 0,
    page_prefix: str | None = None,
) -> InlineKeyboardMarkup:
    rows = []
    current_row = []
    for i, cb in enumerate(item_callbacks, start=1):
        current_row.append(InlineKeyboardButton(text=str(i), callback_data=cb))
        if len(current_row) == 5:
            rows.append(current_row)
            current_row = []
    if current_row:
        rows.append(current_row)

    nav_row = []
    if page_prefix and page > 0:
        nav_row.append(InlineKeyboardButton(text="⬅️", callback_data=f"{page_prefix}:{page - 1}"))
    nav_row.append(InlineKeyboardButton(text="❌", callback_data="delete_msg"))
    if page_prefix and (page + 1) * PLAYLIST_PAGE_SIZE < total_items:
        nav_row.append(InlineKeyboardButton(text="➡️", callback_data=f"{page_prefix}:{page + 1}"))
    rows.append(nav_row)

    return InlineKeyboardMarkup(inline_keyboard=rows)


# ==================== MAJBURIY OBUNA ====================
async def check_user_subscriptions(user_id: int) -> list[sqlite3.Row]:
    if user_id == ADMIN_ID:
        return []
    if sub_ok_cache.get(user_id):
        return []
    channels = await asyncio.to_thread(get_channels)
    not_joined = []
    for ch in channels:
        try:
            member = await bot.get_chat_member(chat_id=ch["channel_id"], user_id=user_id)
            if member.status in ("left", "kicked"):
                not_joined.append(ch)
        except Exception:
            pass
    if not not_joined:
        sub_ok_cache.set(user_id, True)
    return not_joined


class SubscriptionMiddleware(BaseMiddleware):
    async def __call__(self, handler, event, data):
        user = getattr(event, "from_user", None)
        if user is None or user.is_bot:
            return await handler(event, data)
        if isinstance(event, Message) and (event.text or "").startswith("/start"):
            return await handler(event, data)
        if isinstance(event, CallbackQuery) and event.data in ("check_subs", "delete_msg"):
            return await handler(event, data)

        not_joined = await check_user_subscriptions(user.id)
        if not not_joined:
            return await handler(event, data)

        keyboard = get_sub_keyboard(not_joined)
        if isinstance(event, Message):
            await event.answer(SUB_PROMPT, reply_markup=keyboard)
        elif isinstance(event, CallbackQuery):
            await event.answer()
            if event.message:
                await bot.send_message(event.message.chat.id, SUB_PROMPT, reply_markup=keyboard)
        return None


dp.message.outer_middleware(SubscriptionMiddleware())
dp.callback_query.outer_middleware(SubscriptionMiddleware())


@dp.callback_query(F.data == "check_subs")
async def cb_check_subs(callback: CallbackQuery):
    sub_ok_cache.pop(callback.from_user.id)
    not_joined = await check_user_subscriptions(callback.from_user.id)
    if not_joined:
        await callback.answer("❌ Hali barcha kanallarga obuna bo'lmadingiz!", show_alert=True)
    else:
        await callback.answer("✅ Obuna tasdiqlandi!")
        if callback.message:
            await safe_delete(callback.message.chat.id, callback.message.message_id)
            await bot.send_message(callback.message.chat.id, WELCOME_TEXT, parse_mode="HTML")


# ==================== TREK YUBORISH ====================
def resolve_meta(item: dict, info: dict) -> tuple[str, str, int]:
    performer = item.get("performer")
    title = item.get("title")
    if not performer or not title:
        p, t = parse_artist_title(info.get("title") or "", info.get("uploader") or info.get("channel") or "")
        performer = performer or p
        title = title or t
    duration = int(item.get("duration") or info.get("duration") or 0)
    return (performer or "Musiqa")[:100], (title or "Trek")[:100], duration


async def send_cached_track(chat_id: int, source_id: str) -> bool:
    cached = await asyncio.to_thread(get_track_by_source, source_id)
    if not (cached and cached["file_id"]):
        return False
    try:
        await bot.send_audio(
            chat_id=chat_id,
            audio=cached["file_id"],
            caption=get_audio_caption(),
            parse_mode="HTML",
            reply_markup=get_track_keyboard(cached["id"]),
        )
    except Exception:
        return False
    await asyncio.to_thread(bump_downloads, cached["id"])
    return True


async def deliver_audio(chat_id: int, item: dict, path: str, info: dict, ext: str) -> None:
    performer, title, dur = resolve_meta(item, info)
    if os.path.getsize(path) > TELEGRAM_UPLOAD_LIMIT:
        raise AudioTooBig("Fayl hajmi 50 MB dan katta.")

    await chat_action(chat_id, "upload_voice")
    sent = await bot.send_audio(
        chat_id=chat_id,
        audio=FSInputFile(path, filename=safe_filename(performer, title, ext)),
        title=title,
        performer=performer,
        duration=dur if dur > 0 else None,
        caption=get_audio_caption(),
        parse_mode="HTML",
    )
    track_id = await asyncio.to_thread(
        save_or_update_track, item["source_id"], title, performer, dur, sent.audio.file_id, item["url"]
    )
    await sent.edit_reply_markup(reply_markup=get_track_keyboard(track_id))


async def send_track_to_user(chat_id: int, item: dict, fallback_candidates: list[dict] | None = None) -> None:
    source_id = item["source_id"]
    if await send_cached_track(chat_id, source_id):
        return

    async with keyed_locks.acquire(source_id):
        if await send_cached_track(chat_id, source_id):
            return
        wait_msg = await bot.send_message(chat_id, "⏳ Yuklanmoqda...")
        try:
            try:
                async with downloaded_audio(item["url"]) as (path, info, ext):
                    await deliver_audio(chat_id, item, path, info, ext)
                    return
            except Exception as primary_err:
                log.warning("Asosiy variant yuklanmadi (%s): %s", item["url"], primary_err)
                # Agar DRM yoki blok bo'lsa, zaxira variantlardan birini yuklab beramiz
                if fallback_candidates:
                    for alt in fallback_candidates:
                        if alt["source_id"] == source_id:
                            continue
                        try:
                            async with downloaded_audio(alt["url"]) as (path, info, ext):
                                await deliver_audio(chat_id, alt, path, info, ext)
                                return
                        except Exception:
                            continue
                raise primary_err
        finally:
            await safe_delete(chat_id, wait_msg.message_id)


# ==================== RO'YXATLI QIDIRUV ====================
async def render_search_results(chat_id: int, search_id: str, page: int = 0, edit_message_id: int | None = None) -> None:
    entry = search_cache.get(search_id)
    if not entry:
        txt = "⏳ Qidiruv natijalari eskirgan. Qaytadan yozing."
        if edit_message_id:
            try:
                await bot.edit_message_text(txt, chat_id=chat_id, message_id=edit_message_id)
            except Exception:
                pass
        else:
            await bot.send_message(chat_id, txt)
        return

    results = entry["results"]
    query = entry.get("query", "Qidiruv")
    total = len(results)
    last_page = max(0, (total - 1) // PLAYLIST_PAGE_SIZE)
    page = max(0, min(page, last_page))

    start = page * PLAYLIST_PAGE_SIZE
    chunk = results[start : start + PLAYLIST_PAGE_SIZE]
    end = start + len(chunk)

    lines = [f"🔎 <b>{html.escape(query)}</b>", f"<b>Natijalar {start + 1}-{end} / {total}</b>\n"]
    for idx, item in enumerate(chunk, start=1):
        dur_str = format_duration(item.get("duration"))
        lines.append(f"{idx}. {html.escape(item['performer'] or '')} — {html.escape(item['title'] or '')} <i>{dur_str}</i>")

    callbacks = [f"sr:{search_id}:{start + i}" for i in range(len(chunk))]
    kb = build_numbered_keyboard(callbacks, page=page, total_items=total, page_prefix=f"sr_pg:{search_id}")
    text = "\n".join(lines)

    if edit_message_id:
        try:
            await bot.edit_message_text(text, chat_id=chat_id, message_id=edit_message_id, parse_mode="HTML", reply_markup=kb)
        except Exception:
            pass
    else:
        await bot.send_message(chat_id, text, parse_mode="HTML", reply_markup=kb)


async def process_music_query(message: Message, query: str) -> None:
    user_id = message.from_user.id
    chat_id = message.chat.id
    await asyncio.to_thread(register_or_touch_user, user_id, True)
    await chat_action(chat_id, "typing")

    wait_msg = await message.answer("🔎 Qidirilmoqda...")
    try:
        results = await run_heavy(search_music_sync, query, SEARCH_RESULTS_LIMIT)
    except Exception as e:
        log.warning("Qidiruvda xatolik: %s", e)
        results = []
    finally:
        await safe_delete(chat_id, wait_msg.message_id)

    if not results:
        await message.answer("😔 Hech narsa topilmadi. Boshqacharoq yozib ko'ring.")
        return

    search_id = secrets.token_hex(4)
    search_cache.set(search_id, {"user_id": user_id, "results": results, "query": query})
    await render_search_results(chat_id, search_id, page=0)


async def process_short_video_link(message: Message, item: dict) -> None:
    chat_id = message.chat.id
    wait_msg = await message.answer("🎧 Video yuklanib, musiqa aniqlanmoqda (Shazam)...")
    found = None
    fallback_query = None

    try:
        async with downloaded_audio(item["url"], is_short=True) as (path, info, ext):
            raw_title = (info.get("track") or info.get("title") or "").strip()
            if raw_title and not any(w in raw_title.lower() for w in ("video by", "instagram", "tiktok", "reel")):
                fallback_query = raw_title

            if Shazam is not None:
                with open(path, "rb") as f:
                    media_bytes = f.read()
                found = await recognize_with_shazam(media_bytes)

            # Agar Shazam topolmasa, videoning o'zini MP3 qilib foydalanuvchiga tashlab beramiz
            if not found:
                mp3_path, mp3_ext = await ensure_mp3_or_m4a(path, ext)
                await deliver_audio(chat_id, item, mp3_path, info, mp3_ext)
                if not fallback_query:
                    await message.answer("ℹ️ Qo'shiq nomini Shazam aniqlay olmadi, videodagi original audio yuborildi.")
    except Exception as e:
        log.warning("Short video xatosi (%s): %s", item["url"], e)
        await message.answer("⚠️ Ushbu havoladan videoni yuklab bo'lmadi (yopiq profil yoki bloklangan).")
        return
    finally:
        await safe_delete(chat_id, wait_msg.message_id)

    search_q = found or fallback_query
    if search_q:
        await message.answer(f"🎶 Topildi: <b>{html.escape(search_q)}</b>", parse_mode="HTML")
        await process_music_query(message, search_q)


async def process_link(message: Message, url: str) -> None:
    chat_id = message.chat.id
    host = (urllib.parse.urlparse(url).hostname or "").lower()
    if not (host_in(host, SOCIAL_HOSTS) or host_in(host, MUSIC_HOSTS)):
        await message.answer("⚠️ Faqat Instagram, TikTok, YouTube va SoundCloud havolalari qo'llab-quvvatlanadi.")
        return

    is_short = is_short_video_url(url)
    source_id = "url_" + hashlib.sha1(url.encode("utf-8")).hexdigest()[:16]
    item = {"source_id": source_id, "title": None, "performer": None, "duration": 0, "url": url}

    try:
        if is_short:
            await process_short_video_link(message, item)
        else:
            await send_track_to_user(chat_id, item)
    except AudioError as e:
        await message.answer(f"⚠️ {e}")
    except Exception as e:
        log.warning("Link ishlash xatosi: %s", e)
        await message.answer("⚠️ Havoladan audio olib bo'lmadi.")


# ==================== FOYDALANUVCHI HANDLERLARI ====================
@dp.message(CommandStart())
async def cmd_start(message: Message):
    await asyncio.to_thread(register_or_touch_user, message.from_user.id)
    await message.answer(WELCOME_TEXT, parse_mode="HTML")


@dp.callback_query(F.data == "delete_msg")
async def cb_delete_msg(callback: CallbackQuery):
    await callback.answer()
    if callback.message:
        await safe_delete(callback.message.chat.id, callback.message.message_id)


@dp.message(Command("my"))
async def cmd_my(message: Message):
    await render_playlist_page(message.chat.id, message.from_user.id, page=0)


async def render_playlist_page(chat_id: int, user_id: int, page: int = 0, edit_message_id: int | None = None) -> None:
    favs = await asyncio.to_thread(get_user_favorites, user_id)
    if not favs:
        txt = "📭 Pleylistingiz bo'sh. Qo'shiq ostidagi ❤️ tugmasini bosing!"
        if edit_message_id:
            try:
                await bot.edit_message_text(txt, chat_id=chat_id, message_id=edit_message_id)
            except Exception:
                pass
        else:
            await bot.send_message(chat_id, txt)
        return

    last_page = (len(favs) - 1) // PLAYLIST_PAGE_SIZE
    page = max(0, min(page, last_page))
    start = page * PLAYLIST_PAGE_SIZE
    chunk = favs[start : start + PLAYLIST_PAGE_SIZE]

    lines = [f"❤️ <b>Pleylistingiz</b> ({page + 1}/{last_page + 1}):\n"]
    for idx, tr in enumerate(chunk, start=1):
        lines.append(f"{idx}. {html.escape(tr['performer'] or '')} — {html.escape(tr['title'] or '')}")
    kb = build_numbered_keyboard(
        [f"play:{tr['id']}" for tr in chunk], page=page, total_items=len(favs), page_prefix="my_page"
    )
    text = "\n".join(lines)
    if edit_message_id:
        try:
            await bot.edit_message_text(text, chat_id=chat_id, message_id=edit_message_id, parse_mode="HTML", reply_markup=kb)
        except Exception:
            pass
    else:
        await bot.send_message(chat_id, text, parse_mode="HTML", reply_markup=kb)


@dp.callback_query(F.data.startswith("my_page:"))
async def cb_my_page(callback: CallbackQuery):
    try:
        page = int(callback.data.split(":")[1])
    except ValueError:
        return await callback.answer()
    await callback.answer()
    if callback.message:
        await render_playlist_page(
            callback.message.chat.id, callback.from_user.id, page=page, edit_message_id=callback.message.message_id
        )


@dp.callback_query(F.data.startswith("play:"))
async def cb_play_track(callback: CallbackQuery):
    try:
        track_id = int(callback.data.split(":")[1])
    except ValueError:
        return await callback.answer()
    chat_id = cb_chat_id(callback)
    tr = await asyncio.to_thread(get_track_by_id, track_id)
    if chat_id is None or not tr or not tr["file_id"]:
        return await callback.answer("Topilmadi", show_alert=True)
    await callback.answer()
    try:
        await bot.send_audio(
            chat_id=chat_id,
            audio=tr["file_id"],
            caption=get_audio_caption(),
            parse_mode="HTML",
            reply_markup=get_track_keyboard(tr["id"]),
        )
    except Exception:
        pass


@dp.message(Command("top"))
async def cmd_top(message: Message):
    top = await asyncio.to_thread(get_top_tracks, 10)
    if not top:
        return await message.answer("🔥 Top musiqalar hali yo'q!")
    lines = ["🔥 <b>Top 10 musiqalar:</b>\n"]
    for idx, tr in enumerate(top, start=1):
        lines.append(f"{idx}. {html.escape(tr['performer'] or '')} — {html.escape(tr['title'] or '')}")
    kb = build_numbered_keyboard([f"play:{tr['id']}" for tr in top])
    await message.answer("\n".join(lines), parse_mode="HTML", reply_markup=kb)


@dp.callback_query(F.data.startswith("fav_add:"))
async def cb_fav_add(callback: CallbackQuery):
    added = await asyncio.to_thread(add_favorite, callback.from_user.id, int(callback.data.split(":")[1]))
    await callback.answer("❤️ Pleylistga qo'shildi!" if added else "ℹ️ Allaqachon pleylistda bor")


@dp.callback_query(F.data.startswith("fav_del:"))
async def cb_fav_del(callback: CallbackQuery):
    removed = await asyncio.to_thread(remove_favorite, callback.from_user.id, int(callback.data.split(":")[1]))
    await callback.answer("💔 Pleylistdan o'chirildi" if removed else "ℹ️ Pleylistda yo'q edi")


# ==================== QO'SHIQ MATNI (LYRICS) HANDLERI ====================
@dp.callback_query(F.data.startswith("lyrics:"))
async def cb_lyrics(callback: CallbackQuery):
    try:
        track_id = int(callback.data.split(":")[1])
    except ValueError:
        return await callback.answer()

    chat_id = cb_chat_id(callback)
    tr = await asyncio.to_thread(get_track_by_id, track_id)
    if not tr or chat_id is None:
        return await callback.answer("Qo'shiq topilmadi", show_alert=True)

    await callback.answer("🎤 Qo'shiq matni qidirilmoqda...")
    lyrics = tr["lyrics"]
    if not lyrics:
        lyrics = await run_heavy(fetch_lyrics_sync, tr["performer"] or "", tr["title"] or "")
        if not lyrics:
            lyrics = await ai_lyrics(tr["performer"] or "", tr["title"] or "")
        if lyrics:
            await asyncio.to_thread(save_lyrics, track_id, lyrics)

    if not lyrics:
        await bot.send_message(chat_id, "😔 Ushbu qo'shiq matni topilmadi.", reply_markup=CLOSE_KB)
        return

    header = f"🎤 <b>{html.escape(tr['performer'] or '')} — {html.escape(tr['title'] or '')}</b>\n\n"
    chunks = split_text(lyrics, 3500)[:MAX_LYRICS_MESSAGES]
    for i, part in enumerate(chunks):
        prefix = header if i == 0 else ""
        await bot.send_message(
            chat_id,
            f"{prefix}{html.escape(part)}",
            parse_mode="HTML",
            reply_markup=CLOSE_KB if i == len(chunks) - 1 else None,
        )


# ==================== SLOWED / BASS / 8D HANDLERI ====================
@dp.callback_query(F.data.startswith("fx:"))
async def cb_audio_fx(callback: CallbackQuery):
    try:
        _, fx_key, track_id_str = callback.data.split(":")
        track_id = int(track_id_str)
    except ValueError:
        return await callback.answer()

    if fx_key not in FX_FILTERS:
        return await callback.answer("Noma'lum effekt", show_alert=True)
    if not FFMPEG_PATH:
        return await callback.answer("⚠️ Serverda FFmpeg o'rnatilmagan!", show_alert=True)

    chat_id = cb_chat_id(callback)
    tr = await asyncio.to_thread(get_track_by_id, track_id)
    if not tr or not tr["file_id"] or chat_id is None:
        return await callback.answer("Audio topilmadi", show_alert=True)

    fx_label, _ = FX_FILTERS[fx_key]
    fx_source_id = f"fx_{fx_key}_{tr['id']}"

    # Agar avval shu effekt tayyorlangan bo'lsa, keshdan yuboramiz
    if await send_cached_track(chat_id, fx_source_id):
        await callback.answer()
        return

    async with heavy_slot(callback.from_user.id) as refusal:
        if refusal:
            return await callback.answer(refusal, show_alert=True)

        await callback.answer(f"{fx_label} tayyorlanmoqda...")
        wait_msg = await bot.send_message(chat_id, f"🎛 <b>{fx_label}</b> tayyorlanmoqda, kuting...", parse_mode="HTML")
        try:
            with tempfile.TemporaryDirectory(prefix="fx_") as tmpdir:
                in_path = os.path.join(tmpdir, "input.mp3")
                out_path = os.path.join(tmpdir, "output.mp3")

                tg_file = await bot.get_file(tr["file_id"])
                await bot.download_file(tg_file.file_path, destination=in_path)

                ok = await apply_audio_fx(in_path, out_path, fx_key)
                if not ok:
                    await bot.send_message(chat_id, "⚠️ Audio qayta ishlashda xatolik yuz berdi.")
                    return

                new_title = f"{tr['title']} ({fx_key.upper()})"
                performer = tr["performer"] or "Musiqa"
                await chat_action(chat_id, "upload_voice")
                sent = await bot.send_audio(
                    chat_id=chat_id,
                    audio=FSInputFile(out_path, filename=safe_filename(performer, new_title, "mp3")),
                    title=new_title,
                    performer=performer,
                    caption=get_audio_caption(fx_label),
                    parse_mode="HTML",
                )
                new_id = await asyncio.to_thread(
                    save_or_update_track,
                    fx_source_id,
                    new_title,
                    performer,
                    int(sent.audio.duration or 0),
                    sent.audio.file_id,
                    tr["webpage_url"] or "",
                )
                await sent.edit_reply_markup(reply_markup=get_track_keyboard(new_id))
        except Exception as e:
            log.warning("FX xatosi: %s", e)
            await bot.send_message(chat_id, "⚠️ Fayl hajmi katta yoki xatolik yuz berdi.")
        finally:
            await safe_delete(chat_id, wait_msg.message_id)


# ==================== ADMIN VA STATISTIKA HANDLERLARI ====================
@dp.message(Command("stat", "stats"))
async def cmd_stat(message: Message):
    st = await asyncio.to_thread(get_stats)
    text = (
        "📊 <b>Bot Statistikasi:</b>\n\n"
        f"👥 Jami foydalanuvchilar: <b>{st['total']}</b>\n"
        f"🟢 Faol (24 soat): <b>{st['active_24h']}</b>\n"
        f"📅 Faol (7 kun): <b>{st['active_7d']}</b>\n"
        f"🗓 Faol (30 kun): <b>{st['active_30d']}</b>\n"
        f"🚫 Bloklaganlar: <b>{st['blocked']}</b>\n\n"
        f"🎵 Bazadagi qo'shiqlar: <b>{st['tracks']}</b>\n"
        f"📥 Jami yuklashlar: <b>{st['downloads']}</b>\n"
        f"❤️ Sevimlilar (Likes): <b>{st['favs']}</b>"
    )
    await message.answer(text, parse_mode="HTML", reply_markup=CLOSE_KB)


@dp.message(Command("channels"))
async def cmd_channels(message: Message):
    if message.from_user.id != ADMIN_ID:
        return
    chs = await asyncio.to_thread(get_channels)
    if not chs:
        return await message.answer(
            "📭 Majburiy obuna kanallari yo'q.\n\n"
            "Qo'shish: <code>/addch -100123456789 https://t.me/kanal Kanal Nomi</code>\n"
            "O'chirish: <code>/delch -100123456789</code>",
            parse_mode="HTML",
        )
    lines = ["📢 <b>Majburiy obuna kanallari:</b>\n"]
    for c in chs:
        lines.append(f"• <code>{c['channel_id']}</code> — <a href=\"{c['invite_link']}\">{html.escape(c['title'])}</a>")
    await message.answer("\n".join(lines), parse_mode="HTML", disable_web_page_preview=True)


@dp.message(Command("addch"))
async def cmd_addch(message: Message, command: CommandObject):
    if message.from_user.id != ADMIN_ID:
        return
    args = (command.args or "").split(maxsplit=2)
    if len(args) < 3:
        return await message.answer(
            "⚠️ Format: <code>/addch @kanal_yoki_id https://t.me/havola Kanal Nomi</code>",
            parse_mode="HTML",
        )
    ch_id, link, title = args[0], args[1], args[2]
    await asyncio.to_thread(add_channel, ch_id, title, link)
    sub_ok_cache.clear()
    await message.answer(f"✅ Kanal qo'shildi: <b>{html.escape(title)}</b>", parse_mode="HTML")


@dp.message(Command("delch"))
async def cmd_delch(message: Message, command: CommandObject):
    if message.from_user.id != ADMIN_ID:
        return
    ch_id = (command.args or "").strip()
    if not ch_id:
        return await message.answer("⚠️ Format: <code>/delch @kanal_yoki_id</code>", parse_mode="HTML")
    await asyncio.to_thread(del_channel, ch_id)
    sub_ok_cache.clear()
    await message.answer(f"🗑 Kanal o'chirildi: <code>{html.escape(ch_id)}</code>", parse_mode="HTML")


@dp.message(Command("broadcast", "send"))
async def cmd_broadcast(message: Message):
    if message.from_user.id != ADMIN_ID:
        return
    if not message.reply_to_message:
        return await message.answer("⚠️ Xabar yuborish uchun biror postga <b>Reply</b> qilib <code>/broadcast</code> yozing.", parse_mode="HTML")

    users = await asyncio.to_thread(get_broadcast_user_ids)
    status = await message.answer(f"📤 Tarqatish boshlandi: {len(users)} ta foydalanuvchi...")
    sent_ok = 0
    blocked_ids = []

    for uid in users:
        try:
            await message.reply_to_message.copy_to(uid)
            sent_ok += 1
        except TelegramRetryAfter as e:
            await asyncio.sleep(e.retry_after)
            try:
                await message.reply_to_message.copy_to(uid)
                sent_ok += 1
            except Exception:
                pass
        except (TelegramForbiddenError, TelegramBadRequest):
            blocked_ids.append(uid)
        except Exception:
            pass
        await asyncio.sleep(BROADCAST_DELAY_SEC)

    await asyncio.to_thread(mark_blocked, blocked_ids)
    await status.edit_text(f"✅ Tarqatish yakunlandi!\n\nYetkazildi: <b>{sent_ok}</b>\nBloklagan: <b>{len(blocked_ids)}</b>", parse_mode="HTML")


@dp.message(F.document & F.caption.startswith("/setcookies"))
async def cmd_set_cookies(message: Message):
    if message.from_user.id != ADMIN_ID:
        return
    target = COOKIES_FILE or "/data/cookies.txt"
    os.makedirs(os.path.dirname(target), exist_ok=True)
    tg_file = await bot.get_file(message.document.file_id)
    await bot.download_file(tg_file.file_path, destination=target)
    await message.answer(f"✅ Cookies saqlandi: {target}")
    await safe_delete(message.chat.id, message.message_id)


# ==================== MEDIA VA MATN QIDIRUV HANDLERLARI ====================
@dp.message(F.voice | F.video | F.video_note | F.audio)
async def handle_media_shazam(message: Message):
    media = message.voice or message.video or message.video_note or message.audio
    if Shazam is None:
        return await message.answer("⚠️ Serverda shazamio kutubxonasi o'rnatilmagan.")

    if getattr(media, "file_size", 0) and media.file_size > 20 * 1024 * 1024:
        return await message.answer("⚠️ Fayl hajmi 20 MB dan kichik bo'lishi kerak.")

    async with heavy_slot(message.from_user.id) as refusal:
        if refusal:
            return await message.answer(refusal)

        wait_msg = await message.answer("🎧 Musiqa aniqlanmoqda (Shazam)...")
        try:
            tg_file = await bot.get_file(media.file_id)
            buf = io.BytesIO()
            await bot.download_file(tg_file.file_path, buf)
            found = await recognize_with_shazam(buf.getvalue())
        except Exception as e:
            log.warning("Media shazam xatosi: %s", e)
            found = None
        finally:
            await safe_delete(message.chat.id, wait_msg.message_id)

        if not found:
            return await message.answer("😔 Musiqani aniqlab bo'lmadi. Boshqa qismini yuboring yoki nomini yozing.")

        await message.answer(f"🎶 Topildi: <b>{html.escape(found)}</b>", parse_mode="HTML")
        await process_music_query(message, found)


@dp.message(F.text & ~F.text.startswith("/"))
async def handle_text_search(message: Message):
    text = message.text.strip()
    url = extract_url(text)
    async with heavy_slot(message.from_user.id) as refusal:
        if refusal:
            return await message.answer(refusal)
        if url:
            await process_link(message, url)
        else:
            await process_music_query(message, text)


@dp.callback_query(F.data.startswith("sr_pg:"))
async def cb_search_page(callback: CallbackQuery):
    try:
        _, search_id, page_str = callback.data.split(":")
        page = int(page_str)
    except ValueError:
        return await callback.answer()
    await callback.answer()
    if callback.message:
        await render_search_results(callback.message.chat.id, search_id, page, callback.message.message_id)


@dp.callback_query(F.data.startswith("sr:"))
async def cb_search_play(callback: CallbackQuery):
    try:
        _, search_id, idx_str = callback.data.split(":")
        idx = int(idx_str)
    except ValueError:
        return await callback.answer("Xato", show_alert=True)
    entry = search_cache.get(search_id)
    chat_id = cb_chat_id(callback)
    if not entry or chat_id is None or not (0 <= idx < len(entry["results"])):
        return await callback.answer("⏳ Qidiruv eskirgan, qaytadan yozing", show_alert=True)

    async with heavy_slot(callback.from_user.id) as refusal:
        if refusal:
            return await callback.answer(refusal, show_alert=True)
        await callback.answer("⏳ Yuklanmoqda...")
        results = entry["results"]
        chosen = results[idx]
        try:
            await send_track_to_user(chat_id, chosen, fallback_candidates=results[:5])
        except Exception as e:
            log.warning("Variant yuklanmadi: %s", e)
            await bot.send_message(chat_id, "⚠️ Bu variantni yuklab bo'lmadi (DRM yoki blok). Boshqa raqamni tanlang.")


# ==================== MAIN ====================
async def main():
    global BOT_USERNAME, BOT_ID
    init_db()
    me = await bot.get_me()
    BOT_USERNAME, BOT_ID = me.username, me.id

    await bot.set_my_commands([
        BotCommand(command="start", description="🚀 Boshlash"),
        BotCommand(command="my", description="❤️ Pleylistim"),
        BotCommand(command="top", description="🔥 Top musiqalar"),
        BotCommand(command="stat", description="📊 Statistika"),
    ])
    await bot.delete_webhook(drop_pending_updates=DROP_PENDING)
    log.info("Bot ishga tushdi: @%s (FFmpeg=%s, FFprobe=%s)", BOT_USERNAME, bool(FFMPEG_PATH), bool(FFPROBE_PATH))
    try:
        await dp.start_polling(bot)
    finally:
        HEAVY_POOL.shutdown(wait=False, cancel_futures=True)


if __name__ == "__main__":
    asyncio.run(main())
