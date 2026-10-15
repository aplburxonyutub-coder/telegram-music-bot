"""
Telegram musiqa boti (aiogram 3.x) — Yakuniy Versiya.
- 10 talik ro'yxat va sahifalash (⬅️ ❌ ➡️)
- YouTube Shorts / Reels / TikTok -> Shazam -> 10 talik variantlar
- YouTube + SoundCloud qidiruv zanjiri
- Cookies va bot blokirovkasiga qarshi himoya
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
    InlineQuery,
    InlineQueryResultCachedAudio,
    InlineQueryResultsButton,
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
COOKIES_FILE = os.getenv("COOKIES_FILE", "")
HEAVY_WORKERS = max(1, int(os.getenv("HEAVY_WORKERS", "3") or 3))
DROP_PENDING = os.getenv("DROP_PENDING", "1") != "0"

MAX_AUDIO_DURATION_SEC = 900
MIN_AUDIO_DURATION_SEC = 40
MAX_DOWNLOAD_BYTES = 45 * 1024 * 1024
TELEGRAM_UPLOAD_LIMIT = 49 * 1024 * 1024
TELEGRAM_DOWNLOAD_LIMIT = 20 * 1024 * 1024
PLAYLIST_PAGE_SIZE = 10
SEARCH_RESULTS_LIMIT = 30
BROADCAST_DELAY_SEC = 0.05
HEAVY_COOLDOWN_SEC = 1.5
MAX_LYRICS_MESSAGES = 4
FFMPEG_TIMEOUT_SEC = 180
SUB_CACHE_TTL_SEC = 300

SOCIAL_HOSTS = ("instagram.com", "tiktok.com")
MUSIC_HOSTS = ("youtube.com", "youtu.be", "soundcloud.com")
AUDIO_EXTS = {".mp3", ".m4a"}

FFMPEG_PATH = shutil.which("ffmpeg")

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


def set_user_gender(user_id: int, gender: str) -> None:
    with db_conn() as conn:
        conn.execute("UPDATE users SET gender = ? WHERE user_id = ?", (gender, user_id))


def mark_gender_prompted(user_id: int) -> None:
    with db_conn() as conn:
        conn.execute("UPDATE users SET gender_prompted = 1 WHERE user_id = ?", (user_id,))


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


def search_cached_tracks(query: str, limit: int = 15) -> list[sqlite3.Row]:
    tokens = normalize_text(query).split()[:6]
    if not tokens:
        return []
    where = " AND ".join("search_text LIKE ?" for _ in tokens)
    params: list = [f"%{t}%" for t in tokens] + [limit]
    with db_conn() as conn:
        return conn.execute(
            f"SELECT * FROM tracks WHERE file_id IS NOT NULL AND {where} ORDER BY downloads DESC LIMIT ?",
            params,
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
            "active_30d": scalar("SELECT COUNT(*) FROM users WHERE last_active_ts >= ?", now - 30 * 86400),
            "boys": scalar("SELECT COUNT(*) FROM users WHERE gender = 'male'"),
            "girls": scalar("SELECT COUNT(*) FROM users WHERE gender = 'female'"),
            "blocked": scalar("SELECT COUNT(*) FROM users WHERE blocked = 1"),
            "tracks": scalar("SELECT COUNT(*) FROM tracks"),
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


class FFmpegMissing(AudioError):
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
    return (clean_up or "Noma'lum ijrochi").strip(), clean or (raw_title or "")


def build_ydl_opts(**extra) -> dict:
    opts = {
        "quiet": True,
        "no_warnings": True,
        "socket_timeout": 20,
        "retries": 3,
        "extractor_args": {"youtube": {"player_client": ["android", "web"]}},
        "http_headers": {
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
        },
    }
    if COOKIES_FILE and os.path.isfile(COOKIES_FILE):
        opts["cookiefile"] = COOKIES_FILE
    opts.update(extra)
    return opts


def search_music_sync(query: str, max_results: int = SEARCH_RESULTS_LIMIT) -> list[dict]:
    opts = build_ydl_opts(extract_flat=False, skip_download=True)
    results: list[dict] = []
    seen: set = set()

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
                url = f"https://www.youtube.com/watch?v={eid}"
                artist, title = parse_artist_title(e.get("title") or query, e.get("uploader") or e.get("channel") or "")
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

    if len(results) < max_results:
        need = max_results - len(results)
        try:
            sc_opts = build_ydl_opts(extract_flat=True, skip_download=True)
            with yt_dlp.YoutubeDL(sc_opts) as ydl:
                info = ydl.extract_info(f"scsearch{need}:{query}", download=False)
                for e in ((info or {}).get("entries") or []):
                    if not e:
                        continue
                    eid = e.get("id")
                    if not eid or eid in seen:
                        continue
                    dur = int(e.get("duration") or 0)
                    url = e.get("url") or e.get("webpage_url")
                    if not url:
                        continue
                    artist, title = parse_artist_title(e.get("title") or query, e.get("uploader") or "")
                    seen.add(eid)
                    results.append(
                        {
                            "source_id": f"sc_{eid}",
                            "title": title,
                            "performer": artist,
                            "duration": dur,
                            "url": url,
                        }
                    )
        except Exception as ex:
            log.warning("SoundCloud qidiruv xatosi: %s", ex)

    return results[:max_results]


def download_audio_sync(url: str, outdir: str) -> tuple[str, dict, str]:
    opts = build_ydl_opts(
        format="bestaudio/best" if FFMPEG_PATH else "bestaudio[ext=m4a]/bestaudio[ext=mp3]/best[ext=m4a]/best[ext=mp3]",
        outtmpl=os.path.join(outdir, "track.%(ext)s"),
        noplaylist=True,
        playlistend=1,
        max_filesize=MAX_DOWNLOAD_BYTES,
    )
    if FFMPEG_PATH:
        opts["postprocessors"] = [
            {"key": "FFmpegExtractAudio", "preferredcodec": "mp3", "preferredquality": "192"}
        ]

    with yt_dlp.YoutubeDL(opts) as ydl:
        info = ydl.extract_info(url, download=True)

    info = info or {}
    if info.get("_type") == "playlist":
        entries = [e for e in (info.get("entries") or []) if e]
        info = entries[0] if entries else {}

    path = None
    for rd in info.get("requested_downloads") or []:
        fp = rd.get("filepath")
        if fp and os.path.isfile(fp) and os.path.splitext(fp)[1].lower() in AUDIO_EXTS:
            path = fp
            break
    if path is None:
        candidates = [
            os.path.join(outdir, f)
            for f in os.listdir(outdir)
            if os.path.splitext(f)[1].lower() in AUDIO_EXTS
        ]
        if candidates:
            path = max(candidates, key=os.path.getsize)

    if path is None:
        if (info.get("duration") or 0) > MAX_AUDIO_DURATION_SEC:
            raise AudioTooLong(f"Audio {MAX_AUDIO_DURATION_SEC // 60} daqiqadan uzun.")
        raise AudioError("Audioni yuklab bo'lmadi (YouTube blokirovkasi yoki xatolik).")

    ext = os.path.splitext(path)[1].lstrip(".").lower()
    return path, info, ext


async def run_heavy(func, *args):
    return await asyncio.get_running_loop().run_in_executor(HEAVY_POOL, func, *args)


@asynccontextmanager
async def downloaded_audio(url: str):
    outdir = tempfile.mkdtemp(prefix="musicbot_")
    try:
        path, info, ext = await run_heavy(download_audio_sync, url, outdir)
        yield path, info, ext
    finally:
        await asyncio.to_thread(shutil.rmtree, outdir, True)


# ==================== QO'SHIQ MATNI VA SHAZAM ====================
def fetch_lyrics_sync(performer: str, title: str) -> str | None:
    query = urllib.parse.quote(f"{performer} {title}")
    url = f"https://lrclib.net/api/search?q={query}"
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "TelegramMusicBot/1.0"})
        with urllib.request.urlopen(req, timeout=8) as resp:
            data = json.loads(resp.read().decode("utf-8"))
    except Exception:
        return None
    if not isinstance(data, list):
        return None

    combined = normalize_text(f"{performer} {title}")
    best: str | None = None
    best_score = 0.0
    for item in data:
        plain = (item.get("plainLyrics") or "").strip()
        if len(plain) <= 20:
            continue
        name_score = text_similarity(item.get("trackName") or item.get("name") or "", title)
        if name_score < 0.8:
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
                contents=f"'{performer} - {title}' qo'shig'ining to'liq matnini yozib ber. Topilmasa 'TOPILMADI' deb yoz.",
            ),
            timeout=20,
        )
    except Exception:
        return None
    text = (res.text or "").strip()
    if not text or "TOPILMADI" in text.upper():
        return None
    return text


async def recognize_with_shazam(media_bytes: bytes) -> str | None:
    if Shazam is None:
        return None
    try:
        shazam = Shazam()
        out = await asyncio.wait_for(shazam.recognize(media_bytes), timeout=40)
        track = (out or {}).get("track")
        if track:
            title = track.get("title", "")
            subtitle = track.get("subtitle", "")
            if title or subtitle:
                return f"{subtitle} - {title}".strip(" -")
    except Exception as e:
        log.warning("Shazam xatosi: %s", e)
    return None


# ==================== TELEGRAM YORDAMCHILARI ====================
SUB_PROMPT = "Botdan foydalanish uchun quyidagi kanallarga obuna bo'ling:"
WELCOME_TEXT = (
    "👋 <b>Salom! Musiqa izlash uchun menga yuboring:</b>\n\n"
    "🎵 Qo'shiq yoki ijrochi nomi\n"
    "🎤 Ovozli xabar yoki video (Shazam)\n"
    "🔗 Instagram, TikTok, YouTube Shorts havolasi\n\n"
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
        yield "⏳ Oldingi so'rovingiz bajarilmoqda, kuting."
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
def get_audio_caption() -> str:
    return f'🔊 <a href="https://t.me/{BOT_USERNAME}">Musiqa topish</a>'


def get_track_keyboard(track_id: int) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [
                InlineKeyboardButton(text="❤️", callback_data=f"fav_add:{track_id}"),
                InlineKeyboardButton(text="💔", callback_data=f"fav_del:{track_id}"),
                InlineKeyboardButton(text="🎤", callback_data=f"lyrics:{track_id}"),
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
        if len(current_row) == 4:
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


async def send_track_to_user(chat_id: int, item: dict) -> None:
    source_id = item["source_id"]
    if await send_cached_track(chat_id, source_id):
        return

    async with keyed_locks.acquire(source_id):
        if await send_cached_track(chat_id, source_id):
            return
        wait_msg = await bot.send_message(chat_id, "⏳ Yuklanmoqda...")
        try:
            async with downloaded_audio(item["url"]) as (path, info, ext):
                await deliver_audio(chat_id, item, path, info, ext)
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
    register_or_touch_user(user_id, True)
    await chat_action(chat_id, "typing")

    wait_msg = await message.answer("🔎 Qidirilmoqda...")
    try:
        results = await run_heavy(search_music_sync, query, SEARCH_RESULTS_LIMIT)
    except Exception:
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
    wait_msg = await message.answer("🎧 Musiqa aniqlanmoqda (Shazam)...")
    found = None
    try:
        async with downloaded_audio(item["url"]) as (path, info, ext):
            if Shazam is not None:
                with open(path, "rb") as f:
                    found = await recognize_with_shazam(f.read())
            if not found:
                await deliver_audio(chat_id, item, path, info, ext)
                await message.answer("ℹ️ Musiqani Shazam topa olmadi, videodagi audio yuborildi.")
    except Exception:
        await message.answer("⚠️ Videoni yuklab bo'lmadi.")
    finally:
        await safe_delete(chat_id, wait_msg.message_id)

    if found:
        await message.answer(f"🎶 Topildi: <b>{html.escape(found)}</b>", parse_mode="HTML")
        await process_music_query(message, found)


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
    except Exception:
        await message.answer("⚠️ Havoladan audio olib bo'lmadi.")


# ==================== HANDLERLAR ====================
@dp.message(CommandStart())
async def cmd_start(message: Message):
    register_or_touch_user(message.from_user.id)
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
        txt = "📭 Pleylistingiz bo'sh. ❤️ tugmasini bosing!"
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

    lines = [f"<b>Pleylistingiz</b> ({page + 1}/{last_page + 1}):\n"]
    for idx, tr in enumerate(chunk, start=1):
        lines.append(f"{idx}. {html.escape(tr['performer'] or '')} — {html.escape(tr['title'] or '')}")
    kb = build_numbered_keyboard([f"play:{tr['id']}" for tr in chunk], page=page, total_items=len(favs), page_prefix="my_page")
    text = "\n".join(lines)
    if edit_message_id:
        try:
            await bot.edit_message_text(text, chat_id=chat_id, message_id=edit_message_id, parse_mode="HTML", reply_markup=kb)
        except Exception:
            pass
    else:
        await bot.send_message(chat_id, text, parse_mode="HTML", reply_markup=kb)


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
        await bot.send_audio(chat_id=chat_id, audio=tr["file_id"], caption=get_audio_caption(), parse_mode="HTML", reply_markup=get_track_keyboard(tr["id"]))
    except Exception:
        pass


@dp.message(Command("top"))
async def cmd_top(message: Message):
    top = await asyncio.to_thread(get_top_tracks, 10)
    if not top:
        return await message.answer("🔥 Top musiqalar hali yo'q!")
    lines = ["🔥 <b>Top musiqalar:</b>\n"]
    for idx, tr in enumerate(top, start=1):
        lines.append(f"{idx}. {html.escape(tr['performer'] or '')} — {html.escape(tr['title'] or '')}")
    kb = build_numbered_keyboard([f"play:{tr['id']}" for tr in top])
    await message.answer("\n".join(lines), parse_mode="HTML", reply_markup=kb)


@dp.callback_query(F.data.startswith("fav_add:"))
async def cb_fav_add(callback: CallbackQuery):
    add_favorite(callback.from_user.id, int(callback.data.split(":")[1]))
    await callback.answer("❤️ Pleylistga qo'shildi!")


@dp.callback_query(F.data.startswith("fav_del:"))
async def cb_fav_del(callback: CallbackQuery):
    remove_favorite(callback.from_user.id, int(callback.data.split(":")[1]))
    await callback.answer("💔 Pleylistdan o'chirildi")


@dp.message(F.voice | F.video | F.video_note | F.audio)
async def handle_media_shazam(message: Message):
    media = message.voice or message.video or message.video_note or message.audio
    if Shazam is None:
        return await message.answer("⚠️ Shazam ishlamaydi.")

    async with heavy_slot(message.from_user.id) as refusal:
        if refusal:
            return await message.answer(refusal)

        wait_msg = await message.answer("🎧 Musiqa aniqlanmoqda (Shazam)...")
        try:
            tg_file = await bot.get_file(media.file_id)
            buf = io.BytesIO()
            await bot.download_file(tg_file.file_path, buf)
            found = await recognize_with_shazam(buf.getvalue())
        except Exception:
            found = None
        finally:
            await safe_delete(message.chat.id, wait_msg.message_id)

        if not found:
            return await message.answer("😔 Musiqani aniqlab bo'lmadi. Qo'shiq nomini matn ko'rinishida yozib yuboring.")

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
        return await callback.answer("Eskirgan, qaytadan yozing", show_alert=True)

    async with heavy_slot(callback.from_user.id) as refusal:
        if refusal:
            return await callback.answer(refusal, show_alert=True)
        await callback.answer("⏳ Yuklanmoqda...")
        try:
            await send_track_to_user(chat_id, entry["results"][idx])
        except Exception:
            await bot.send_message(chat_id, "⚠️ Bu variantni yuklab bo'lmadi. Boshqasini tanlang.")


# ==================== MAIN ====================
async def main():
    global BOT_USERNAME, BOT_ID
    init_db()
    me = await bot.get_me()
    BOT_USERNAME, BOT_ID = me.username, me.id

    await bot.set_my_commands([
        BotCommand(command="start", description="🚀 Boshlash"),
        BotCommand(command="my", description="❤️ Pleylist"),
        BotCommand(command="top", description="🔥 Top"),
    ])
    await bot.delete_webhook(drop_pending_updates=DROP_PENDING)
    try:
        await dp.start_polling(bot)
    finally:
        HEAVY_POOL.shutdown(wait=False, cancel_futures=True)


if __name__ == "__main__":
    asyncio.run(main())
