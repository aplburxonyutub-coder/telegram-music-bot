"""
Telegram musiqa boti (aiogram 3.x) — tuzatilgan to'liq versiya.

Talablar (Python 3.10+):
    pip install -U aiogram yt-dlp python-dotenv shazamio google-genai
    Serverda ffmpeg o'rnatilgan bo'lishi kerak (mp3 konvertatsiya, effektlar va Shazam uchun).

.env o'zgaruvchilari:
    BOT_TOKEN       majburiy
    ADMIN_ID        admin Telegram ID raqami
    GEMINI_API_KEY  ixtiyoriy (faqat LRCLIB'da matn topilmasa zaxira sifatida ishlatiladi)
    DB_PATH         standart: /data/music_database.db
    COOKIES_FILE    ixtiyoriy: yt-dlp uchun cookies.txt yo'li (Instagram ko'pincha login talab qiladi)
    HEAVY_WORKERS   bir vaqtda nechta qidiruv/yuklash bajarilsin (standart: 3)
    DROP_PENDING    1 bo'lsa, bot o'chiq turganda yig'ilgan eski xabarlar o'tkazib yuboriladi (standart: 1)

Muhim: yt-dlp ni muntazam yangilab turing (pip install -U yt-dlp).
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

MAX_AUDIO_DURATION_SEC = 900             # 15 daqiqadan uzun audio yuklanmaydi
MIN_AUDIO_DURATION_SEC = 40              # juda qisqa treklar (30 soniyalik preview/jingl) tashlab yuboriladi; 0 = o'chirish
MAX_DOWNLOAD_BYTES = 45 * 1024 * 1024    # manba fayl uchun chegara
TELEGRAM_UPLOAD_LIMIT = 49 * 1024 * 1024
TELEGRAM_DOWNLOAD_LIMIT = 20 * 1024 * 1024
PLAYLIST_PAGE_SIZE = 10
BROADCAST_DELAY_SEC = 0.05
HEAVY_COOLDOWN_SEC = 2.0                 # bitta foydalanuvchining ketma-ket og'ir so'rovlari orasidagi tanaffus
MAX_AUTO_TRIES = 3                       # birinchi natija xato bersa, keyingi nechta variantni sinab ko'rish
MAX_LYRICS_MESSAGES = 4
FFMPEG_TIMEOUT_SEC = 180
SUB_CACHE_TTL_SEC = 300

SOCIAL_HOSTS = ("instagram.com", "tiktok.com")
MUSIC_HOSTS = ("youtube.com", "youtu.be", "soundcloud.com")
AUDIO_EXTS = {".mp3", ".m4a"}            # Telegram audio sifatida faqat shularni ko'rsatadi

FFMPEG_PATH = shutil.which("ffmpeg")

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(name)s: %(message)s")
log = logging.getLogger("musicbot")

if not BOT_TOKEN:
    raise SystemExit("BOT_TOKEN topilmadi: .env fayliga BOT_TOKEN=... qatorini qo'shing.")

# Katta audio fayllar sekin tarmoqda ham yuborilishi uchun so'rov timeout'i oshirilgan (standart 60 s)
bot = Bot(token=BOT_TOKEN, session=AiohttpSession(timeout=300))
dp = Dispatcher()
gemini_client = genai.Client(api_key=GEMINI_API_KEY) if (genai and GEMINI_API_KEY) else None

# Og'ir ishlar (yt-dlp) uchun alohida pool: oddiy DB so'rovlari ular bilan bir navbatda turib qolmasligi uchun
HEAVY_POOL = ThreadPoolExecutor(max_workers=HEAVY_WORKERS, thread_name_prefix="heavy")
FFMPEG_SEM = asyncio.Semaphore(2)

BOT_USERNAME = ""
BOT_ID = 0


# ==================== KICHIK YORDAMCHI SINFLAR ====================
class TTLCache:
    """Oddiy TTL + hajm chegarali kesh: xotira cheksiz o'sib ketmaydi."""

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
    """Bir xil kalit (masalan, source_id) uchun bir vaqtda faqat bitta yuklashni ta'minlaydi."""

    def __init__(self):
        self._locks: dict[str, list] = {}  # kalit -> [lock, kutayotganlar soni]

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


# Vaqtinchalik qidiruv natijalari: {search_id: {"user_id": ..., "results": [...]}} (1 soat, eng ko'pi bilan 5000 ta)
search_cache = TTLCache(ttl=3600, max_items=5000)
# Majburiy obunani muvaffaqiyatli o'tgan foydalanuvchilar: har safar get_chat_member chaqirmaslik uchun
sub_ok_cache = TTLCache(ttl=SUB_CACHE_TTL_SEC, max_items=100_000)
_last_heavy = TTLCache(ttl=120, max_items=100_000)
_busy_users: set[int] = set()
keyed_locks = KeyedLocks()


# ==================== MATN YORDAMCHILARI ====================
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
    """Qidiruv uchun matnni normallashtiradi: kichik harf, kirill -> lotin, apostrof variantlari olib tashlanadi."""
    s = (s or "").lower()
    s = "".join(_UZ_CYR_TO_LAT.get(ch, ch) for ch in s)
    s = _APOS_RE.sub("", s)
    s = re.sub(r"[\W_]+", " ", s)
    return s.strip()


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
    """Uzun matnni qatorlar chegarasida bo'laklarga ajratadi (Telegram 4096 belgi chegarasi uchun)."""
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
    """Har bir chaqiruv uchun alohida ulanish: muvaffaqiyatda commit, xatoda rollback, har doim close."""
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
            mode = conn.execute("PRAGMA journal_mode=WAL").fetchone()[0]
            log.info("SQLite journal_mode=%s", mode)
        except sqlite3.DatabaseError as e:
            log.warning("WAL rejimini yoqib bo'lmadi: %s", e)

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

        # Eski bazalar uchun migratsiya
        ensure_column(conn, "users", "gender_prompted", "INTEGER DEFAULT 0")
        ensure_column(conn, "users", "blocked", "INTEGER DEFAULT 0")
        ensure_column(conn, "tracks", "search_text", "TEXT DEFAULT NULL")

        conn.execute("CREATE INDEX IF NOT EXISTS idx_fav_track ON favorites(track_id)")
        conn.execute("CREATE INDEX IF NOT EXISTS idx_users_active ON users(last_active_ts)")

        # Qidiruv matni (kirill/lotin va apostrof variantlariga chidamli) yo'q treklar uchun to'ldiriladi
        rows = conn.execute("SELECT id, performer, title FROM tracks WHERE search_text IS NULL").fetchall()
        if rows:
            conn.executemany(
                "UPDATE tracks SET search_text = ? WHERE id = ?",
                [(normalize_text(f"{r['performer'] or ''} {r['title'] or ''}"), r["id"]) for r in rows],
            )

        # Bir martalik tuzatish: eski xato tufayli oshib ketgan likelarni qayta hisoblash
        version = conn.execute("PRAGMA user_version").fetchone()[0]
        if version < 1:
            conn.execute(
                "UPDATE tracks SET likes = (SELECT COUNT(*) FROM favorites f WHERE f.track_id = tracks.id)"
            )
            conn.execute("PRAGMA user_version = 1")


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
    """UPSERT: ikki foydalanuvchi bir vaqtda bir xil trekni so'rasa ham UNIQUE xatosi chiqmaydi."""
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
            # Layk ham kamayadi — aks holda ❤️/💔 ni takrorlab reytingni soxtalashtirish mumkin bo'lardi
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


def search_cached_tracks(query: str, limit: int = 10) -> list[sqlite3.Row]:
    """Keshdagi treklar ichidan qidiradi. Kirill/lotin va apostrof variantlari (o', oʻ, o‘) bir xil hisoblanadi."""
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


def make_db_backup_sync() -> str:
    """Ishlayotgan bazaning izchil nusxasini (SQLite backup API) vaqtinchalik faylga yozadi."""
    fd, tmp_path = tempfile.mkstemp(prefix="music_db_", suffix=".db")
    os.close(fd)
    src = sqlite3.connect(DB_PATH)
    dst = sqlite3.connect(tmp_path)
    try:
        src.backup(dst)
    finally:
        dst.close()
        src.close()
    return tmp_path


# ==================== XATO TURLARI ====================
class AudioError(Exception):
    """Foydalanuvchiga ko'rsatsa bo'ladigan audio xatosi."""


class AudioTooLong(AudioError):
    pass


class AudioTooBig(AudioError):
    pass


class FFmpegMissing(AudioError):
    pass


# ==================== QIDIRUV VA YUKLASH (YT-DLP + SOUNDCLOUD) ====================
_JUNK_RE = re.compile(r"\s*[\(\[](?:official|audio|video|music|lyrics|hd|4k|karaoke).*?[\)\]]", re.IGNORECASE)


def parse_artist_title(raw_title: str, uploader: str = "") -> tuple[str, str]:
    clean = _JUNK_RE.sub("", raw_title or "").strip()
    for sep in (" — ", " – ", " - "):
        if sep in clean:
            left, right = clean.split(sep, 1)
            return left.strip(), right.strip()
    return (uploader or "Noma'lum ijrochi").strip(), clean or (raw_title or "")


def build_ydl_opts(**extra) -> dict:
    opts = {
        "quiet": True,
        "no_warnings": True,
        "socket_timeout": 20,
        "retries": 3,
        # Generic extractor o'chirilgan: faqat YouTube/SoundCloud/TikTok/Instagram kabi maxsus extractorlar ishlaydi
        # (begona saytlarga so'rov yuborilishining oldini oladi). Eski yt-dlp versiyasida bu parametr e'tiborsiz qoladi.
        "allowed_extractors": ["default", "-generic"],
    }
    if COOKIES_FILE and os.path.isfile(COOKIES_FILE):
        opts["cookiefile"] = COOKIES_FILE
    opts.update(extra)
    return opts


def _extract_results(entries: list, prefix: str, query: str) -> list[dict]:
    results: list[dict] = []
    seen: set = set()
    for e in entries:
        if not e:
            continue
        eid = e.get("id")
        if not eid or eid in seen:
            continue
        dur = int(e.get("duration") or 0)
        if dur and (dur > MAX_AUDIO_DURATION_SEC or dur < MIN_AUDIO_DURATION_SEC):
            continue
        if prefix == "yt":
            url = f"https://www.youtube.com/watch?v={eid}"
        else:
            url = e.get("url") or e.get("webpage_url")
        if not url:
            continue
        artist, title = parse_artist_title(e.get("title") or query, e.get("uploader") or e.get("channel") or "")
        seen.add(eid)
        results.append(
            {
                "source_id": f"{prefix}_{eid}",
                "title": title,
                "performer": artist,
                "duration": dur,
                "url": url,
            }
        )
    return results


def search_music_sync(query: str, max_results: int = 10) -> list[dict]:
    opts = build_ydl_opts(extract_flat=True, skip_download=True)
    results: list[dict] = []
    try:
        with yt_dlp.YoutubeDL(opts) as ydl:
            info = ydl.extract_info(f"scsearch{max_results}:{query}", download=False)
        results = _extract_results((info or {}).get("entries") or [], "sc", query)
    except Exception as ex:
        log.warning("SoundCloud qidiruv xatosi: %s", ex)

    if not results:
        try:
            with yt_dlp.YoutubeDL(opts) as ydl:
                info = ydl.extract_info(f"ytsearch5:{query}", download=False)
            results = _extract_results((info or {}).get("entries") or [], "yt", query)
        except Exception as ex:
            log.warning("YouTube fallback qidiruv xatosi: %s", ex)

    return results


def download_audio_sync(url: str, outdir: str) -> tuple[str, dict, str]:
    """Audioni `outdir` ichiga yuklaydi. Qaytaradi: (fayl yo'li, info, kengaytma: 'mp3' yoki 'm4a')."""
    opts = build_ydl_opts(
        # ffmpeg bor bo'lsa mp3 ga o'giriladi; yo'q bo'lsa Telegram o'zi qabul qiladigan formatlar tanlanadi
        format="bestaudio/best" if FFMPEG_PATH else "bestaudio[ext=m4a]/bestaudio[ext=mp3]/best[ext=m4a]/best[ext=mp3]",
        outtmpl=os.path.join(outdir, "track.%(ext)s"),
        noplaylist=True,
        playlistend=1,
        max_filesize=MAX_DOWNLOAD_BYTES,
        match_filter=yt_dlp.utils.match_filter_func(f"duration <=? {MAX_AUDIO_DURATION_SEC}"),
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
            raise AudioTooLong(f"Audio {MAX_AUDIO_DURATION_SEC // 60} daqiqadan uzun — yuklanmaydi.")
        if os.listdir(outdir):
            if not FFMPEG_PATH:
                raise FFmpegMissing("Serverda ffmpeg o'rnatilmagan, shu sababli bu formatni yuborib bo'lmaydi.")
            raise AudioError("Audioni kerakli formatga o'girib bo'lmadi.")
        raise AudioError("Audioni yuklab bo'lmadi (fayl juda katta yoki mavjud emas).")

    ext = os.path.splitext(path)[1].lstrip(".").lower()
    return path, info, ext


async def run_heavy(func, *args):
    """Og'ir (yt-dlp) ishlarni alohida pool'da bajaradi — oddiy DB so'rovlariga xalaqit bermaydi."""
    return await asyncio.get_running_loop().run_in_executor(HEAVY_POOL, func, *args)


@asynccontextmanager
async def downloaded_audio(url: str):
    """Audioni vaqtinchalik papkaga yuklaydi; blokdan chiqqach papka avtomatik o'chiriladi."""
    outdir = tempfile.mkdtemp(prefix="musicbot_")
    try:
        path, info, ext = await run_heavy(download_audio_sync, url, outdir)
        yield path, info, ext
    finally:
        await asyncio.to_thread(shutil.rmtree, outdir, True)


# ==================== QO'SHIQ MATNI (LYRICS) ====================
def fetch_lyrics_sync(performer: str, title: str) -> str | None:
    """LRCLIB'dan matn oladi. Faqat nomi (va ijrochisi) mos kelgan natija qabul qilinadi."""
    query = urllib.parse.quote(f"{performer} {title}")
    url = f"https://lrclib.net/api/search?q={query}"
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "TelegramMusicBot/1.0"})
        with urllib.request.urlopen(req, timeout=8) as resp:
            data = json.loads(resp.read().decode("utf-8"))
    except Exception as e:
        log.warning("LRCLIB xatosi: %s", e)
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
        artist_in_query = bool(artist) and normalize_text(artist) in combined
        if artist_score < 0.3 and not artist_in_query:
            continue
        score = name_score + max(artist_score, 1.0 if artist_in_query else 0.0)
        if score > best_score:
            best, best_score = plain, score
    return best


async def ai_lyrics(performer: str, title: str) -> str | None:
    """Zaxira: LRCLIB'da topilmasa Gemini'dan so'raydi. Natija noto'g'ri bo'lishi mumkin — foydalanuvchiga ogohlantirish ko'rsatiladi."""
    if not gemini_client:
        return None
    try:
        res = await asyncio.wait_for(
            gemini_client.aio.models.generate_content(
                model=GEMINI_MODEL,
                contents=(
                    f"'{performer} - {title}' qo'shig'ining to'liq matnini (lyrics) yozib ber. "
                    "Agar aniq matnni bilmasang, faqat 'TOPILMADI' deb yoz."
                ),
            ),
            timeout=30,
        )
    except Exception as e:
        log.warning("Gemini xatosi: %s", e)
        return None
    text = (res.text or "").strip()
    if not text or "TOPILMADI" in text.upper():
        return None
    return text


# ==================== OVOZ EFFEKTLARI (FFMPEG) ====================
EFFECT_FILTERS = {
    # aresample=44100 boshida: manba 48 kHz bo'lsa ham sekinlashtirish aynan 0.85 bo'ladi
    "slowed": "aresample=44100,asetrate=44100*0.85,aresample=44100,aecho=0.8:0.88:60:0.4",
    "bass": "bass=g=12:f=110:w=0.6",
    # mono manbada ham chap-o'ng harakat bo'lishi uchun avval stereo'ga o'tkaziladi
    "8d": "aformat=channel_layouts=stereo,apulsator=hz=0.125",
}
EFFECT_NAMES = {"slowed": "🌙 Slowed + Reverb", "bass": "🔥 Bass Boosted", "8d": "🎧 8D Audio"}
EFFECT_SPEED = {"slowed": 0.85}  # davomiylik o'zgarishini hisoblash uchun


async def apply_audio_effect(in_path: str, out_path: str, effect: str) -> bool:
    af_filter = EFFECT_FILTERS.get(effect)
    if not af_filter or not FFMPEG_PATH:
        return False
    proc = await asyncio.create_subprocess_exec(
        FFMPEG_PATH, "-y", "-hide_banner", "-loglevel", "error",
        "-i", in_path, "-vn", "-af", af_filter, "-b:a", "192k", out_path,
        stdout=asyncio.subprocess.DEVNULL,
        stderr=asyncio.subprocess.PIPE,
    )
    try:
        _, stderr = await asyncio.wait_for(proc.communicate(), timeout=FFMPEG_TIMEOUT_SEC)
    except asyncio.TimeoutError:
        proc.kill()
        await proc.wait()
        log.error("ffmpeg timeout (%s)", effect)
        return False
    if proc.returncode != 0:
        log.error("ffmpeg xatosi (%s): %s", effect, stderr.decode(errors="ignore")[-500:])
        return False
    return os.path.exists(out_path) and os.path.getsize(out_path) > 0


# ==================== SHAZAM ====================
async def recognize_with_shazam(media_bytes: bytes) -> str | None:
    if Shazam is None:
        return None
    try:
        shazam = Shazam()
        out = await asyncio.wait_for(shazam.recognize(media_bytes), timeout=60)
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
SUB_PROMPT = "Botdan to'liq foydalanish uchun quyidagi kanallarga obuna bo'ling:"
AI_LYRICS_NOTE = "\n\n⚠️ <i>Bu matn sun'iy intellekt tomonidan yaratilgan va noto'g'ri bo'lishi mumkin.</i>"
WELCOME_TEXT = (
    "👋 <b>Salom! Qo'shiq izlash uchun menga quyidagilardan birini yuboring:</b>\n\n"
    "🎵 Qo'shiq yoki ijrochi nomi (masalan: <i>Hulkar - Bozor</i>)\n"
    "🎤 Ovozli xabar yoki video (Shazam orqali topish)\n"
    "🔗 Instagram Reels, TikTok, YouTube yoki SoundCloud havolasi\n\n"
    "📂 <b>Shaxsiy pleylistingiz:</b> /my\n"
    "🔥 <b>Top musiqalar:</b> /top"
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
    """Foydalanuvchiga bir vaqtda faqat bitta og'ir so'rov (qidiruv/yuklash/effekt) ruxsat beriladi.
    Slot olinsa None, aks holda foydalanuvchiga ko'rsatiladigan xabar (str) yield qilinadi."""
    if user_id in _busy_users:
        yield "⏳ Oldingi so'rovingiz hali bajarilmoqda. Iltimos, kuting."
        return
    last = _last_heavy.get(user_id)
    if last is not None:
        wait = HEAVY_COOLDOWN_SEC - (time.monotonic() - last)
        if wait > 0:
            yield f"⏳ Iltimos, {math.ceil(wait)} soniya kuting."
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


def get_track_keyboard(track_id: int, search_id: str | None = None) -> InlineKeyboardMarkup:
    rows = [
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
    if search_id:
        rows.append([InlineKeyboardButton(text="📋 Boshqa variantlar", callback_data=f"variants:{search_id}")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def get_gender_keyboard() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup(
        inline_keyboard=[
            [InlineKeyboardButton(text="👱‍♂️ Yigit", callback_data="gender:male")],
            [InlineKeyboardButton(text="👩 Qiz", callback_data="gender:female")],
            [InlineKeyboardButton(text="❌", callback_data="delete_msg")],
        ]
    )


def get_sub_keyboard(not_joined: list[sqlite3.Row]) -> InlineKeyboardMarkup:
    buttons = []
    for ch in not_joined:
        buttons.append([InlineKeyboardButton(text=f"➕ {ch['title']}", url=ch["invite_link"])])
    buttons.append([InlineKeyboardButton(text="✅ Tasdiqlash", callback_data="check_subs")])
    return InlineKeyboardMarkup(inline_keyboard=buttons)


def build_numbered_keyboard(
    item_callbacks: list[str],
    page: int = 0,
    total_items: int = 0,
    page_prefix: str | None = None,
) -> InlineKeyboardMarkup:
    """Raqamli tugmalar. Har bir tugma o'z callback_data'sini (masalan `play:<track_id>`) oladi —
    shuning uchun ro'yxat o'zgarsa ham aynan o'sha trek ochiladi. Sahifalash tugmalari `{page_prefix}:{sahifa}`."""
    rows = []
    current_row = []
    for i, cb in enumerate(item_callbacks, start=1):
        current_row.append(InlineKeyboardButton(text=str(i), callback_data=cb))
        if len(current_row) == 4:
            rows.append(current_row)
            current_row = []
    if current_row:
        rows.append(current_row)

    if page_prefix:
        nav_row = []
        if page > 0:
            nav_row.append(InlineKeyboardButton(text="⬅️", callback_data=f"{page_prefix}:{page - 1}"))
        if (page + 1) * PLAYLIST_PAGE_SIZE < total_items:
            nav_row.append(InlineKeyboardButton(text="➡️", callback_data=f"{page_prefix}:{page + 1}"))
        if nav_row:
            rows.append(nav_row)

    rows.append([InlineKeyboardButton(text="❌", callback_data="delete_msg")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


async def maybe_ask_gender(chat_id: int, user: sqlite3.Row) -> None:
    """Jins so'rovi har bir foydalanuvchiga faqat bir marta beriladi."""
    if user["gender"] or user["gender_prompted"]:
        return
    await asyncio.to_thread(mark_gender_prompted, user["user_id"])
    await bot.send_message(chat_id, "💬 Siz kimsiz?", reply_markup=get_gender_keyboard())


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
            if member.status in ("left", "kicked") or (
                member.status == "restricted" and getattr(member, "is_member", True) is False
            ):
                not_joined.append(ch)
        except Exception as e:
            # Odatda bot kanalda admin emas yoki kanal ID noto'g'ri. Foydalanuvchi bloklanmaydi, lekin xato logda ko'rinadi.
            log.warning("Obuna tekshiruvi xatosi (%s): %s — bot kanalda admin bo'lishi kerak", ch["channel_id"], e)
    if not not_joined:
        sub_ok_cache.set(user_id, True)
    return not_joined


class SubscriptionMiddleware(BaseMiddleware):
    """Majburiy obunani BARCHA kirish nuqtalarida (xabar, tugma, inline) tekshiradi."""

    async def __call__(self, handler, event, data):
        user = getattr(event, "from_user", None)
        if user is None or user.is_bot:
            return await handler(event, data)

        if isinstance(event, Message):
            if (event.text or "").startswith("/start"):
                return await handler(event, data)  # /start o'zi obunani tekshiradi
        elif isinstance(event, CallbackQuery):
            if event.data in ("check_subs", "delete_msg"):
                return await handler(event, data)

        not_joined = await check_user_subscriptions(user.id)
        if not not_joined:
            return await handler(event, data)

        keyboard = get_sub_keyboard(not_joined)
        try:
            if isinstance(event, Message):
                await event.answer(SUB_PROMPT, reply_markup=keyboard)
            elif isinstance(event, CallbackQuery):
                await event.answer()
                if event.message:
                    await bot.send_message(event.message.chat.id, SUB_PROMPT, reply_markup=keyboard)
            elif isinstance(event, InlineQuery):
                await event.answer(
                    [],
                    cache_time=5,
                    is_personal=True,
                    button=InlineQueryResultsButton(text="📢 Kanallarga obuna bo'lish", start_parameter="sub"),
                )
        except Exception:
            log.exception("Obuna xabarini yuborishda xato")
        return None


_subscription_mw = SubscriptionMiddleware()
dp.message.outer_middleware(_subscription_mw)
dp.callback_query.outer_middleware(_subscription_mw)
dp.inline_query.outer_middleware(_subscription_mw)


# ==================== TREKNI YUBORISH ====================
def resolve_meta(item: dict, info: dict) -> tuple[str, str, int]:
    performer = item.get("performer")
    title = item.get("title")
    if not performer or not title:
        p, t = parse_artist_title(info.get("title") or "", info.get("uploader") or info.get("channel") or "")
        performer = performer or p
        title = title or t
    duration = int(item.get("duration") or info.get("duration") or 0)
    return (performer or "Musiqa")[:100], (title or "Trek")[:100], duration


def _read_bytes(path: str) -> bytes:
    with open(path, "rb") as f:
        return f.read()


async def send_cached_track(chat_id: int, source_id: str, search_id: str | None) -> bool:
    """Trek keshda (file_id) bo'lsa darhol yuboradi. file_id yaroqsiz bo'lsa False qaytaradi — qayta yuklanadi."""
    cached = await asyncio.to_thread(get_track_by_source, source_id)
    if not (cached and cached["file_id"]):
        return False
    try:
        await bot.send_audio(
            chat_id=chat_id,
            audio=cached["file_id"],
            caption=get_audio_caption(),
            parse_mode="HTML",
            reply_markup=get_track_keyboard(cached["id"], search_id),
        )
    except TelegramBadRequest as e:
        log.warning("Keshdagi file_id ishlamadi (%s): %s", source_id, e)
        return False
    await asyncio.to_thread(bump_downloads, cached["id"])
    return True


async def deliver_audio(chat_id: int, item: dict, path: str, info: dict, ext: str, search_id: str | None = None) -> None:
    """Yuklangan faylni (diskdan oqim bilan, RAMga o'qimasdan) yuboradi va bazaga saqlaydi."""
    performer, title, dur = resolve_meta(item, info)
    if os.path.getsize(path) > TELEGRAM_UPLOAD_LIMIT:
        raise AudioTooBig("Fayl hajmi Telegram chegarasidan (50 MB) katta.")

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
    # Audio allaqachon yuborilgan: quyidagi bosqichdagi xato foydalanuvchiga "xatolik" bo'lib ko'rinmasligi kerak
    try:
        track_id = await asyncio.to_thread(
            save_or_update_track, item["source_id"], title, performer, dur, sent.audio.file_id, item["url"]
        )
        await sent.edit_reply_markup(reply_markup=get_track_keyboard(track_id, search_id))
    except Exception:
        log.exception("Trekni saqlash/tugma qo'yishda xato: %s", item["source_id"])


async def send_track_to_user(chat_id: int, item: dict, search_id: str | None = None) -> None:
    source_id = item["source_id"]
    if await send_cached_track(chat_id, source_id, search_id):
        return

    # Bir xil trekni bir vaqtda ikki marta yuklamaslik: ikkinchi foydalanuvchi birinchisini kutib, keshdan oladi
    async with keyed_locks.acquire(source_id):
        if await send_cached_track(chat_id, source_id, search_id):
            return
        wait_msg = await bot.send_message(chat_id, "⏳ Yuklanmoqda...")
        try:
            async with downloaded_audio(item["url"]) as (path, info, ext):
                await deliver_audio(chat_id, item, path, info, ext, search_id)
        finally:
            await safe_delete(chat_id, wait_msg.message_id)


async def process_music_query(message: Message, query: str) -> None:
    """Qidiradi va birinchi natijani yuboradi (xato bo'lsa keyingi variantga o'tadi).
    Chaqiruvchi `heavy_slot` ni egallagan bo'lishi kerak."""
    user_id = message.from_user.id
    chat_id = message.chat.id
    user = await asyncio.to_thread(register_or_touch_user, user_id, True)
    await chat_action(chat_id, "typing")

    try:
        results = await run_heavy(search_music_sync, query, 10)
    except Exception:
        log.exception("Qidiruvda xato: %s", query)
        results = []
    if not results:
        await message.answer("😔 Hech narsa topilmadi. Qo'shiq yoki xonanda nomini boshqacharoq yozib ko'ring.")
        return

    search_id = secrets.token_hex(4)
    search_cache.set(search_id, {"user_id": user_id, "results": results})
    variants_id = search_id if len(results) > 1 else None

    sent = False
    for item in results[:MAX_AUTO_TRIES]:
        try:
            await send_track_to_user(chat_id, item, variants_id)
            sent = True
            break
        except AudioError as e:
            log.info("Variant o'tkazib yuborildi (%s): %s", item["source_id"], e)
        except Exception:
            log.exception("Trek yuborishda xato: %s", item["source_id"])
    if not sent:
        await message.answer("⚠️ Ushbu trekni yuklashda xatolik bo'ldi. Boshqa nom bilan qidirib ko'ring.")
        return

    await maybe_ask_gender(chat_id, user)


async def process_social_link(message: Message, item: dict) -> None:
    """Instagram/TikTok: videodagi musiqani Shazam bilan aniqlab, to'liq trekni yuboradi.
    Aniqlanmasa — videodagi audioning o'zini yuboradi."""
    chat_id = message.chat.id
    if await send_cached_track(chat_id, item["source_id"], None):
        return

    wait_msg = await message.answer("🎧 Havoladagi musiqa aniqlanmoqda...")
    found = None
    try:
        async with downloaded_audio(item["url"]) as (path, info, ext):
            if Shazam is not None:
                audio_bytes = await asyncio.to_thread(_read_bytes, path)
                found = await recognize_with_shazam(audio_bytes)
            if not found:
                await deliver_audio(chat_id, item, path, info, ext)
                await message.answer("ℹ️ Musiqani aniqlab bo'lmadi, videodagi audio yuborildi.")
    finally:
        await safe_delete(chat_id, wait_msg.message_id)

    if found:
        await message.answer(f"🎶 Topildi: <b>{html.escape(found)}</b>", parse_mode="HTML")
        await process_music_query(message, found)


async def process_link(message: Message, url: str) -> None:
    """Havola bilan ishlash. Chaqiruvchi `heavy_slot` ni egallagan bo'lishi kerak."""
    chat_id = message.chat.id
    host = (urllib.parse.urlparse(url).hostname or "").lower()
    is_social = host_in(host, SOCIAL_HOSTS)
    is_music = host_in(host, MUSIC_HOSTS)
    if not (is_social or is_music):
        await message.answer("⚠️ Faqat Instagram, TikTok, YouTube va SoundCloud havolalari qo'llab-quvvatlanadi.")
        return

    # Qidiruv hisobi: musiqa havolasi bevosita hisoblanadi; ijtimoiy tarmoq havolasi — Shazam topgach process_music_query ichida
    user = await asyncio.to_thread(register_or_touch_user, message.from_user.id, is_music)
    source_id = "url_" + hashlib.sha1(url.encode("utf-8")).hexdigest()[:16]
    item = {"source_id": source_id, "title": None, "performer": None, "duration": 0, "url": url}

    try:
        if is_music:
            await send_track_to_user(chat_id, item)
            await maybe_ask_gender(chat_id, user)
        else:
            await process_social_link(message, item)
    except AudioError as e:
        await message.answer(f"⚠️ {e}")
    except Exception:
        log.exception("Havolani qayta ishlashda xato: %s", url)
        await message.answer(
            "⚠️ Havoladan audio olib bo'lmadi. Havola ochiq (public) ekanini tekshiring "
            "(Instagram ko'pincha login talab qiladi)."
        )


# ==================== /start & UMUMIY CALLBACKLAR ====================
@dp.message(CommandStart())
async def cmd_start(message: Message):
    user = await asyncio.to_thread(register_or_touch_user, message.from_user.id)
    await message.answer(WELCOME_TEXT, parse_mode="HTML")
    not_joined = await check_user_subscriptions(message.from_user.id)
    if not_joined:
        await message.answer(SUB_PROMPT, reply_markup=get_sub_keyboard(not_joined))
        return
    await maybe_ask_gender(message.chat.id, user)


@dp.callback_query(F.data.startswith("gender:"))
async def handle_gender(callback: CallbackQuery):
    gender = callback.data.split(":", 1)[1]
    if gender not in ("male", "female"):
        return await callback.answer()
    await asyncio.to_thread(set_user_gender, callback.from_user.id, gender)
    await callback.answer("✅ Qabul qilindi!")
    if callback.message:
        await safe_delete(callback.message.chat.id, callback.message.message_id)


@dp.callback_query(F.data == "check_subs")
async def cb_check_subs(callback: CallbackQuery):
    sub_ok_cache.pop(callback.from_user.id)  # yangi natija olish uchun keshni chetlab o'tamiz
    not_joined = await check_user_subscriptions(callback.from_user.id)
    if not_joined:
        return await callback.answer("❌ Hali barcha kanallarga a'zo bo'lmadingiz!", show_alert=True)
    await callback.answer("✅ Rahmat! Endi botdan foydalanishingiz mumkin.")
    if callback.message:
        await safe_delete(callback.message.chat.id, callback.message.message_id)


@dp.callback_query(F.data == "delete_msg")
async def cb_delete_msg(callback: CallbackQuery):
    await callback.answer()
    if callback.message:
        await safe_delete(callback.message.chat.id, callback.message.message_id)


# ==================== PLEYLIST (/my) VA TOP (/top) ====================
async def render_playlist_page(chat_id: int, user_id: int, page: int = 0, edit_message_id: int | None = None) -> None:
    favs = await asyncio.to_thread(get_user_favorites, user_id)
    if not favs:
        txt = "📭 Sizning pleylistingiz hozircha bo'sh.\nQo'shiqlarni saqlash uchun ularning ostidagi ❤️ tugmasini bosing!"
        if edit_message_id:
            try:
                await bot.edit_message_text(txt, chat_id=chat_id, message_id=edit_message_id)
            except TelegramBadRequest:
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
    kb = build_numbered_keyboard(
        [f"play:{tr['id']}" for tr in chunk],
        page=page,
        total_items=len(favs),
        page_prefix="my_page",
    )
    text = "\n".join(lines)
    if edit_message_id:
        try:
            await bot.edit_message_text(
                text, chat_id=chat_id, message_id=edit_message_id, parse_mode="HTML", reply_markup=kb
            )
        except TelegramBadRequest as e:
            log.debug("Pleylistni tahrirlab bo'lmadi: %s", e)  # masalan, "message is not modified"
    else:
        await bot.send_message(chat_id, text, parse_mode="HTML", reply_markup=kb)


@dp.message(Command("my"))
async def cmd_my(message: Message):
    await render_playlist_page(message.chat.id, message.from_user.id, page=0)


@dp.callback_query(F.data.startswith("my_page:"))
async def cb_playlist_page(callback: CallbackQuery):
    if callback.message is None:
        return await callback.answer()
    try:
        page = int(callback.data.split(":")[1])
    except ValueError:
        return await callback.answer()
    await callback.answer()
    await render_playlist_page(
        callback.message.chat.id,
        callback.from_user.id,
        page=page,
        edit_message_id=callback.message.message_id,
    )


@dp.callback_query(F.data.startswith("play:"))
async def cb_play_track(callback: CallbackQuery):
    """/my va /top dagi raqamli tugmalar: callback ichida indeks emas, aynan track_id turadi."""
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
    except TelegramBadRequest:
        await bot.send_message(chat_id, "⚠️ Bu trekni yuborib bo'lmadi. Uni qaytadan qidirib ko'ring.")


@dp.message(Command("top"))
async def cmd_top(message: Message):
    top = await asyncio.to_thread(get_top_tracks, 10)
    if not top:
        return await message.answer("🔥 Top musiqalar ro'yxati tez orada shakllanadi!")
    lines = ["🔥 <b>Eng ko'p tinglangan TOP musiqalar:</b>\n"]
    for idx, tr in enumerate(top, start=1):
        lines.append(f"{idx}. {html.escape(tr['performer'] or '')} — {html.escape(tr['title'] or '')} (❤️ {tr['likes']})")
    kb = build_numbered_keyboard([f"play:{tr['id']}" for tr in top])
    await message.answer("\n".join(lines), parse_mode="HTML", reply_markup=kb)


# ==================== ❤️ / 💔 / 🎤 / EFFEKTLAR ====================
@dp.callback_query(F.data.startswith("fav_add:"))
async def cb_fav_add(callback: CallbackQuery):
    track_id = int(callback.data.split(":")[1])
    added = await asyncio.to_thread(add_favorite, callback.from_user.id, track_id)
    if added:
        await callback.answer("❤️ Pleylistingizga qo'shildi! (/my)")
    else:
        await callback.answer("✅ Bu qo'shiq allaqachon pleylistingizda bor (/my)")


@dp.callback_query(F.data.startswith("fav_del:"))
async def cb_fav_del(callback: CallbackQuery):
    track_id = int(callback.data.split(":")[1])
    removed = await asyncio.to_thread(remove_favorite, callback.from_user.id, track_id)
    if removed:
        await callback.answer("💔 Pleylistdan o'chirildi")
    else:
        await callback.answer("Bu qo'shiq pleylistingizda yo'q")


@dp.callback_query(F.data.startswith("lyrics:"))
async def cb_lyrics(callback: CallbackQuery):
    track_id = int(callback.data.split(":")[1])
    tr = await asyncio.to_thread(get_track_by_id, track_id)
    chat_id = cb_chat_id(callback)
    if not tr or chat_id is None:
        return await callback.answer("Trek topilmadi", show_alert=True)

    await callback.answer("🎤 Qo'shiq matni qidirilmoqda...")
    performer, title = tr["performer"] or "", tr["title"] or ""

    lyrics = tr["lyrics"]
    ai_generated = False
    if not lyrics:
        lyrics = await asyncio.to_thread(fetch_lyrics_sync, performer, title)
        if lyrics:
            await asyncio.to_thread(save_lyrics, track_id, lyrics)
    if not lyrics:
        lyrics = await ai_lyrics(performer, title)  # saqlanmaydi: AI matni ishonchsiz bo'lishi mumkin
        ai_generated = bool(lyrics)

    if not lyrics:
        await bot.send_message(
            chat_id,
            f"😔 <b>{html.escape(performer)} — {html.escape(title)}</b> qo'shig'ining matni topilmadi.",
            parse_mode="HTML",
        )
        return

    parts = split_text(lyrics)
    truncated = len(parts) > MAX_LYRICS_MESSAGES
    parts = parts[:MAX_LYRICS_MESSAGES]
    header = f"🎤 <b>{html.escape(performer)} — {html.escape(title)}</b>\n\n"
    for i, part in enumerate(parts):
        text = (header if i == 0 else "") + html.escape(part)
        is_last = i == len(parts) - 1
        if is_last:
            if truncated:
                text += "\n…"
            if ai_generated:
                text += AI_LYRICS_NOTE
        await bot.send_message(chat_id, text, parse_mode="HTML", reply_markup=CLOSE_KB if is_last else None)


@dp.callback_query(F.data.startswith("fx:"))
async def cb_audio_effect(callback: CallbackQuery):
    try:
        _, effect, track_id_str = callback.data.split(":")
        track_id = int(track_id_str)
    except ValueError:
        return await callback.answer("Noto'g'ri so'rov", show_alert=True)
    if effect not in EFFECT_FILTERS:
        return await callback.answer("Noma'lum effekt", show_alert=True)
    if not FFMPEG_PATH:
        return await callback.answer("⚠️ Serverda FFmpeg o'rnatilmagan — effektlar ishlamaydi.", show_alert=True)

    tr = await asyncio.to_thread(get_track_by_id, track_id)
    chat_id = cb_chat_id(callback)
    if not tr or not tr["file_id"] or chat_id is None:
        return await callback.answer("Trek topilmadi", show_alert=True)

    async with heavy_slot(callback.from_user.id) as refusal:
        if refusal:
            return await callback.answer(refusal, show_alert=True)

        name = EFFECT_NAMES[effect]
        await callback.answer(f"{name} tayyorlanmoqda...")
        wait_msg = await bot.send_message(chat_id, f"🎛 {name} ishlov berilmoqda...")
        tmpdir = tempfile.mkdtemp(prefix="musicbot_fx_")
        try:
            in_path = os.path.join(tmpdir, "in.mp3")
            out_path = os.path.join(tmpdir, "out.mp3")
            tg_file = await bot.get_file(tr["file_id"])
            await bot.download_file(tg_file.file_path, destination=in_path, timeout=120)
            async with FFMPEG_SEM:
                ok = await apply_audio_effect(in_path, out_path, effect)
            if not ok:
                await wait_msg.edit_text("⚠️ Audioni qayta ishlashda xatolik yuz berdi.")
                return

            dur = int((tr["duration"] or 0) / EFFECT_SPEED.get(effect, 1.0))
            new_title = f"{tr['title']} ({effect.upper()})"
            await bot.send_audio(
                chat_id=chat_id,
                audio=FSInputFile(out_path, filename=safe_filename(tr["performer"], new_title)),
                title=new_title,
                performer=tr["performer"],
                duration=dur if dur > 0 else None,
                caption=get_audio_caption(),
                parse_mode="HTML",
                reply_markup=CLOSE_KB,
            )
            await safe_delete(chat_id, wait_msg.message_id)
        except Exception:
            log.exception("Effekt xatosi (%s)", effect)
            try:
                await wait_msg.edit_text("⚠️ Audioni qayta ishlashda xatolik yuz berdi.")
            except Exception:
                pass
        finally:
            await asyncio.to_thread(shutil.rmtree, tmpdir, True)


# ==================== SHAZAM (OVOZ / VIDEO) ====================
@dp.message(F.voice | F.video | F.video_note | F.audio)
async def handle_media_shazam(message: Message):
    media = message.voice or message.video or message.video_note or message.audio
    if media.file_size and media.file_size > TELEGRAM_DOWNLOAD_LIMIT:
        return await message.answer("⚠️ Fayl hajmi 20 MB dan kichik bo'lishi kerak.")
    if Shazam is None:
        return await message.answer("⚠️ Shazam moduli serverda o'rnatilmagan (pip install shazamio).")

    async with heavy_slot(message.from_user.id) as refusal:
        if refusal:
            return await message.answer(refusal)

        wait_msg = await message.answer("🎧 Musiqa aniqlanmoqda (Shazam)...")
        try:
            tg_file = await bot.get_file(media.file_id)
            buf = io.BytesIO()
            await bot.download_file(tg_file.file_path, buf, timeout=120)
            found_query = await recognize_with_shazam(buf.getvalue())
        except Exception:
            log.exception("Media Shazam xatosi")
            await safe_delete(message.chat.id, wait_msg.message_id)
            return await message.answer("⚠️ Musiqani aniqlashda xatolik yuz berdi.")
        await safe_delete(message.chat.id, wait_msg.message_id)

        if not found_query:
            return await message.answer("😔 Kechirasiz, bu ovozdan musiqani aniqlab bo'lmadi. Boshqa parcha yuborib ko'ring.")

        await message.answer(f"🎶 Topildi: <b>{html.escape(found_query)}</b>", parse_mode="HTML")
        await process_music_query(message, found_query)


# ==================== MATN / HAVOLA ORQALI QIDIRISH ====================
@dp.message(F.text & ~F.text.startswith("/"))
async def handle_text_search(message: Message):
    text = message.text.strip()
    url = extract_url(text)
    if not url and len(text) < 2:
        return await message.answer("🎵 Qo'shiq yoki xonanda nomini yozing.")

    async with heavy_slot(message.from_user.id) as refusal:
        if refusal:
            return await message.answer(refusal)
        if url:
            await process_link(message, url)
        else:
            await process_music_query(message, text)


@dp.callback_query(F.data.startswith("variants:"))
async def cb_show_variants(callback: CallbackQuery):
    search_id = callback.data.split(":", 1)[1]
    entry = search_cache.get(search_id)
    chat_id = cb_chat_id(callback)
    if not entry or chat_id is None:
        return await callback.answer("Qaytadan qidiruv bering", show_alert=True)

    await callback.answer()
    results = entry["results"][:10]
    lines = ["🔎 <b>Topilgan variantlar:</b>\n"]
    for idx, item in enumerate(results, start=1):
        lines.append(f"{idx}. {html.escape(item['performer'])} — {html.escape(item['title'])}")
    kb = build_numbered_keyboard([f"sr:{search_id}:{i}" for i in range(len(results))])
    await bot.send_message(chat_id, "\n".join(lines), parse_mode="HTML", reply_markup=kb)


@dp.callback_query(F.data.startswith("sr:"))
async def cb_search_play(callback: CallbackQuery):
    try:
        _, search_id, idx_str = callback.data.split(":")
        idx = int(idx_str)
    except ValueError:
        return await callback.answer("Noto'g'ri so'rov", show_alert=True)
    entry = search_cache.get(search_id)
    chat_id = cb_chat_id(callback)
    if not entry or chat_id is None or not (0 <= idx < len(entry["results"])):
        return await callback.answer("Qaytadan qidiruv bering", show_alert=True)

    async with heavy_slot(callback.from_user.id) as refusal:
        if refusal:
            return await callback.answer(refusal, show_alert=True)
        await callback.answer()
        try:
            await send_track_to_user(chat_id, entry["results"][idx])
        except AudioError as e:
            await bot.send_message(chat_id, f"⚠️ {e}")
        except Exception:
            log.exception("Variantni yuklashda xato")
            await bot.send_message(chat_id, "⚠️ Yuklashda xatolik yuz berdi.")


# ==================== INLINE REJIM (@bot_nomi qo'shiq) ====================
@dp.inline_query()
async def handle_inline_query(inline_query: InlineQuery):
    q = inline_query.query.strip()
    if len(q) < 2:
        rows = await asyncio.to_thread(get_top_tracks, 10)
    else:
        rows = await asyncio.to_thread(search_cached_tracks, q, 15)

    results = []
    for tr in rows:
        if tr["file_id"]:
            results.append(
                InlineQueryResultCachedAudio(
                    id=str(tr["id"]),
                    audio_file_id=tr["file_id"],
                    caption=get_audio_caption(),
                    parse_mode="HTML",
                )
            )
    # Natijalar foydalanuvchiga bog'liq emas, shuning uchun is_personal=False va uzoqroq kesh
    await inline_query.answer(results, cache_time=30, is_personal=False)


# ==================== ADMIN PANEL VA STATISTIKA ====================
@dp.message(Command("stat", "stats"))
async def cmd_stat(message: Message):
    if message.from_user.id != ADMIN_ID:
        return
    s = await asyncio.to_thread(get_stats)
    text = (
        f"📊 <b>Musiqa Bot Statistikasi</b>\n\n"
        f"👥 Jami foydalanuvchilar: <b>{s['total']}</b>\n"
        f"🟢 Oylik faol (MAU): <b>{s['active_30d']}</b>\n"
        f"⚡ Bugun faol: <b>{s['active_24h']}</b>\n"
        f"🚫 Botni bloklaganlar: <b>{s['blocked']}</b>\n\n"
        f"👱‍♂️ Yigitlar: <b>{s['boys']}</b> | 👩 Qizlar: <b>{s['girls']}</b>\n\n"
        f"🎵 Keshdagi qo'shiqlar: <b>{s['tracks']}</b>\n"
        f"❤️ Pleylistga saqlanganlar: <b>{s['favs']}</b>"
    )
    await message.answer(text, parse_mode="HTML")


@dp.message(Command("addchannel"))
async def cmd_add_channel(message: Message, command: CommandObject):
    if message.from_user.id != ADMIN_ID:
        return
    if not command.args or "|" not in command.args:
        return await message.answer(
            "📌 Foydalanish:\n<code>/addchannel @kanal_username | Kanal Nomi | https://t.me/kanal_username</code>",
            parse_mode="HTML",
        )
    parts = [p.strip() for p in command.args.split("|")]
    if len(parts) < 3:
        return await message.answer("⚠️ 3 ta qismni | belgisi bilan ajratib yozing.")
    ch_id, title, link = parts[0], parts[1], parts[2]

    # Bot kanalda admin bo'lmasa obuna tekshiruvi ishlamaydi — buni darhol ogohlantiramiz
    warn = ""
    try:
        me_member = await bot.get_chat_member(ch_id, BOT_ID)
        if me_member.status not in ("administrator", "creator"):
            warn = "\n⚠️ Bot bu kanalda admin emas — obuna tekshiruvi ishlamaydi. Botni kanalga admin qiling."
    except Exception as e:
        warn = f"\n⚠️ Kanalga ulanib bo'lmadi ({e}). Kanal ID/username va botning admin huquqini tekshiring."

    await asyncio.to_thread(add_channel, ch_id, title, link)
    sub_ok_cache.clear()
    await message.answer(f"✅ Kanal qo'shildi: {title} ({ch_id}){warn}")


@dp.message(Command("delchannel"))
async def cmd_del_channel(message: Message, command: CommandObject):
    if message.from_user.id != ADMIN_ID:
        return
    if not command.args:
        return await message.answer("📌 Foydalanish: <code>/delchannel @kanal_username</code>", parse_mode="HTML")
    await asyncio.to_thread(del_channel, command.args.strip())
    sub_ok_cache.clear()
    await message.answer("🗑 Kanal o'chirildi.")


@dp.message(Command("channels"))
async def cmd_list_channels(message: Message):
    if message.from_user.id != ADMIN_ID:
        return
    chs = await asyncio.to_thread(get_channels)
    if not chs:
        return await message.answer("Majburiy obuna kanallari yo'q.")
    txt = "\n".join(f"• {html.escape(c['title'] or '')} — <code>{html.escape(c['channel_id'])}</code>" for c in chs)
    await message.answer(f"📢 <b>Ulangan kanallar:</b>\n\n{txt}", parse_mode="HTML")


@dp.message(Command("broadcast"))
async def cmd_broadcast(message: Message, command: CommandObject):
    if message.from_user.id != ADMIN_ID:
        return
    is_reply = message.reply_to_message is not None
    b_text = command.args if (command.args and not is_reply) else None
    if not is_reply and not b_text:
        return await message.answer("📢 Xabarga reply qilib /broadcast yozing yoki /broadcast <matn> kiriting.")

    user_ids = await asyncio.to_thread(get_broadcast_user_ids)
    status = await message.answer(f"📤 Yuborilmoqda: 0/{len(user_ids)}")
    sent, failed = 0, 0
    blocked_now: list[int] = []

    async def send_one(uid: int) -> None:
        if is_reply:
            await bot.copy_message(
                chat_id=uid, from_chat_id=message.chat.id, message_id=message.reply_to_message.message_id
            )
        else:
            await bot.send_message(uid, b_text)

    for i, uid in enumerate(user_ids, 1):
        try:
            try:
                await send_one(uid)
            except TelegramRetryAfter as e:
                # Telegram tezlik chegarasi: aytilgan vaqt kutiladi va bir marta qayta uriniladi
                await asyncio.sleep(e.retry_after + 1)
                await send_one(uid)
            sent += 1
        except TelegramForbiddenError:
            blocked_now.append(uid)  # foydalanuvchi botni bloklagan
            failed += 1
        except Exception:
            failed += 1
        if i % 30 == 0 or i == len(user_ids):
            try:
                await status.edit_text(f"📤 Yuborilmoqda: {i}/{len(user_ids)} (✅ {sent} | ❌ {failed})")
            except Exception:
                pass
        await asyncio.sleep(BROADCAST_DELAY_SEC)

    await asyncio.to_thread(mark_blocked, blocked_now)  # keyingi broadcastlarda ularga yuborilmaydi
    await status.edit_text(f"✅ Yakunlandi! Yuborildi: {sent}, Xato: {failed} (bloklaganlar: {len(blocked_now)})")


@dp.message(Command("getdb"))
async def cmd_getdb(message: Message):
    if message.from_user.id != ADMIN_ID:
        return
    if not os.path.exists(DB_PATH):
        return await message.answer("Baza fayli topilmadi.")
    # WAL rejimida faylni oddiy nusxalash yetarli emas — SQLite backup API ishlatiladi
    tmp_path = await asyncio.to_thread(make_db_backup_sync)
    try:
        if os.path.getsize(tmp_path) > TELEGRAM_UPLOAD_LIMIT:
            await message.answer("⚠️ Baza fayli 50 MB dan katta — Telegram orqali yuborib bo'lmaydi. Uni serverdan oling.")
        else:
            await message.answer_document(FSInputFile(tmp_path, filename="music_database.db"))
    finally:
        try:
            os.remove(tmp_path)
        except OSError:
            pass


# ==================== ISHGA TUSHIRISH ====================
async def main():
    global BOT_USERNAME, BOT_ID
    init_db()
    # Oddiy to_thread chaqiruvlari (DB, lyrics) uchun yetarli kattalikdagi pool; og'ir ishlar HEAVY_POOL'da
    asyncio.get_running_loop().set_default_executor(ThreadPoolExecutor(max_workers=16, thread_name_prefix="default"))

    me = await bot.get_me()
    BOT_USERNAME, BOT_ID = me.username, me.id

    yt_version = getattr(getattr(yt_dlp, "version", None), "__version__", "?")
    log.info("Bot: @%s | yt-dlp: %s | ffmpeg: %s", BOT_USERNAME, yt_version, FFMPEG_PATH or "TOPILMADI")
    if not FFMPEG_PATH:
        log.warning("ffmpeg topilmadi: mp3 konvertatsiya, effektlar va Shazam to'liq ishlamaydi. ffmpeg o'rnating.")

    await bot.set_my_commands(
        [
            BotCommand(command="start", description="🚀 Botni ishga tushirish"),
            BotCommand(command="my", description="❤️ Pleylistingiz"),
            BotCommand(command="top", description="🔥 Top musiqalar"),
        ]
    )
    # Bot o'chiq turganda yig'ilgan eski so'rovlar qayta yoqilganda birdan yuklashga tushmasligi uchun
    await bot.delete_webhook(drop_pending_updates=DROP_PENDING)
    try:
        await dp.start_polling(bot)
    finally:
        HEAVY_POOL.shutdown(wait=False, cancel_futures=True)


if __name__ == "__main__":
    asyncio.run(main())
