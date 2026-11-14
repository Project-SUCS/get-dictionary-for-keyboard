import argparse
import curses
import gzip
import hashlib
import html
import io
import json
import logging
import os
import re
import sys
import tarfile
import tempfile
import unicodedata
import urllib.error
import urllib.request
from collections import namedtuple
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

# Logging is decoupled from business logic (rule 11): stripping this module
# must never break the application. Path is overridable via environment so the
# build machine controls where debug output lands, not the caller's CWD alone.
LOG_FILE = os.environ.get("DICT_BUILDER_LOG_FILE", "dict_builder_debug.log")
logging.basicConfig(
    filename=LOG_FILE,
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s"
)
logger = logging.getLogger("DynamicLangBuilder")

INDEX_URL = "https://kaikki.org/dictionary/index.html"

# Kaikki.org's per-language "postprocessed" .jsonl files (the ones this
# builder used to fetch one-by-one) are DEPRECATED and are served
# UNCOMPRESSED (see https://github.com/tatuylonen/wiktextract/issues/1178).
# Instead we fetch the single combined "raw Wiktextract data" dump ONCE,
# which covers every language and IS gzip-compressed (~2.7 GB compressed vs
# 23+ GB uncompressed), and filter it locally by the `lang` field for
# whichever languages the user selected.
RAW_DUMP_URL = "https://kaikki.org/dictionary/raw-wiktextract-data.jsonl.gz"

# Where finished archives and the index.json manifest live. Overridable via
# environment because this is meant to be run on a server that publishes
# these files somewhere specific (e.g. a web root), not necessarily the
# directory the script happens to be launched from.
# Default output location: "out-dictionaries" next to the script itself,
# NOT the directory the script happens to be launched from -- running via
# a cron job, a launcher, or `python /some/other/path/main.py` shouldn't
# scatter output into whatever the caller's CWD was. Still overridable, in
# order of precedence: -d/--output-dir CLI flag > DICT_BUILDER_OUTPUT_DIR
# env var > this default. Can also be changed at runtime from the language
# picker with the [D] key.
SCRIPT_DIR = Path(__file__).resolve().parent
DEFAULT_OUTPUT_DIR = SCRIPT_DIR / "out-dictionaries"
OUTPUT_DIR = Path(os.environ.get("DICT_BUILDER_OUTPUT_DIR", str(DEFAULT_OUTPUT_DIR))).resolve()
INDEX_JSON_FILENAME = "index.json"

# Optional user-supplied config listing extra/custom dictionary sources
# (plain word-list URLs) beyond what kaikki.org provides. Missing file is
# not an error -- it just means no custom sources are added.
SOURCES_CONFIG_FILE = Path(os.environ.get("DICT_BUILDER_SOURCES_FILE", "sources.json"))

# --- Licensing / attribution ------------------------------------------------
# Wiktionary-derived data is shared under CC BY-SA, so every output carries
# attribution. The license is NOT taken from these constants at build time:
# resolve_wiktionary_license() asks the source wiki's own API what license
# it is currently published under, so a future license change on Wiktionary
# is picked up without editing this script. The values below are only the
# fallback for when that request fails (offline build) and for --example,
# which deliberately never touches the network.
WIKTIONARY_LICENSE = "CC BY-SA 4.0"
WIKTIONARY_LICENSE_URL = "https://creativecommons.org/licenses/by-sa/4.0/"
KAIKKI_URL = "https://kaikki.org"
WIKTIONARY_URL = "https://en.wiktionary.org"
WIKTIONARY_API_URL = (
    WIKTIONARY_URL
    + "/w/api.php?action=query&meta=siteinfo&siprop=rightsinfo&format=json&formatversion=2"
)
WIKTEXTRACT_CITATION = (
    "Tatu Ylonen: Wiktextract: Wiktionary as Machine-Readable Structured "
    "Data, Proceedings of the 13th Conference on Language Resources and "
    "Evaluation (LREC), pp. 1317-1325, Marseille, 20-25 June 2022."
)
WIKTIONARY_ATTRIBUTION = (
    "Word list data extracted from English Wiktionary via kaikki.org "
    "(wiktextract by Tatu Ylonen)"
)
UNKNOWN_LICENSE = "unknown"

# Result of resolve_wiktionary_license(); None until a build resolves it.
_resolved_source_license: Optional[Tuple[str, str]] = None

MIN_WORD_LENGTH = 1
MAX_WORD_LENGTH = 45
# Characters allowed BETWEEN letter runs inside one word: ASCII/typographic
# apostrophes and hyphens ("don't", "l'homme", "e-mail", "по-русски"). They
# are never allowed at the start/end or doubled. Spaces stay excluded: a
# keyboard dictionary stores single tokens, not phrases.
WORD_JOINERS = "'\u2019\u02bc-\u2010"

# Fast path: letter runs (any script) optionally joined by WORD_JOINERS.
# \w-based, so it cannot see combining marks (see _is_word_with_marks).
UNIVERSAL_WORD_REGEX = re.compile(
    r"^[^\W\d_]+(?:['\u2019\u02bc\-\u2010][^\W\d_]+)*$", re.UNICODE
)

# Network read size. Kept as a named constant so download loops and any future
# tuning stay in sync instead of duplicating a magic number.
DOWNLOAD_CHUNK_SIZE = 65536

# How often (in processed lines) to refresh the curses progress screen while
# streaming a dump. Dumps can have tens of millions of lines; a redraw on
# every line would waste far more CPU than the parsing itself.
PROGRESS_REFRESH_EVERY_LINES = 50000

# Per-bucket buffer size before an individual (language, letter) bucket
# flushes to disk. Kept small deliberately: with hundreds of languages
# selected at once (the TUI's default is "everything checked"), the number
# of simultaneously-active buckets can run into the thousands, and even a
# modest per-bucket cap multiplies into serious memory. A full 467-language
# run with the old cap of 500 was enough to get the whole process killed by
# the OOM killer on an ordinary machine.
WORD_BUFFER_FLUSH_SIZE = 80

# Hard safety net independent of the per-bucket cap above: if the SUM of
# words sitting in memory across every bucket combined crosses this, flush
# everything immediately. The per-bucket cap alone only bounds memory if the
# number of buckets stays reasonable; this bounds total memory regardless of
# how many languages/buckets happen to be active at once.
GLOBAL_BUFFER_WORD_CAP = 40000

# The index page lists a meta-entry for the combined dataset itself. It is
# not a real `lang` value in the data (it is a browsing category on the
# website), so selecting it would silently produce zero words. We drop it
# from the pickable list rather than let it look like a normal language.
NON_LANGUAGE_ENTRIES = {"all languages combined"}

# Unicode code-point ranges used for a cheap first-character script check.
# This is a SECOND line of defense on top of the `lang` field match: kaikki
# occasionally tags loanwords/romanized entries under a non-Latin language
# (e.g. an English brand name documented as its own entry under "Japanese"),
# which is technically correct per Wiktionary's own editorial conventions
# but is exactly the kind of thing a keyboard dictionary doesn't want mixed
# into a Cyrillic or Japanese word list. Order matters only in that Latin
# ranges are checked last, since they're the widest.
_SCRIPT_RANGES: List[Tuple[str, int, int]] = [
    ("cyrillic", 0x0400, 0x04FF),
    ("cyrillic", 0x0500, 0x052F),
    ("greek", 0x0370, 0x03FF),
    ("hebrew", 0x0590, 0x05FF),
    ("arabic", 0x0600, 0x06FF),
    ("arabic", 0x0750, 0x077F),
    ("devanagari", 0x0900, 0x097F),
    ("thai", 0x0E00, 0x0E7F),
    ("hangul", 0xAC00, 0xD7A3),
    ("hangul", 0x1100, 0x11FF),
    ("hiragana_katakana", 0x3040, 0x30FF),
    ("cjk", 0x3400, 0x4DBF),
    ("cjk", 0x4E00, 0x9FFF),
    ("latin", 0x0041, 0x005A),
    ("latin", 0x0061, 0x007A),
    ("latin", 0x00C0, 0x024F),
]

# lang_code -> the script(s) considered normal for that language. Only
# covers major, unambiguous cases deliberately: for any lang_code NOT
# listed here, script filtering is skipped entirely rather than guessed at,
# so we never reject legitimate data for a language we haven't
# characterized. This directly targets the reported symptom (Latin-script
# words leaking into Cyrillic/Japanese output) without pretending to solve
# script validation for all ~470 languages kaikki covers.
LANG_CODE_EXPECTED_SCRIPTS: Dict[str, Set[str]] = {
    "ru": {"cyrillic"}, "uk": {"cyrillic"}, "be": {"cyrillic"}, "bg": {"cyrillic"},
    "mk": {"cyrillic"}, "sr": {"cyrillic", "latin"}, "kk": {"cyrillic"}, "ky": {"cyrillic"},
    "mn": {"cyrillic"}, "tg": {"cyrillic"},
    "ja": {"hiragana_katakana", "cjk"}, "zh": {"cjk"}, "ko": {"hangul"},
    "el": {"greek"}, "he": {"hebrew"}, "yi": {"hebrew"},
    "ar": {"arabic"}, "fa": {"arabic"}, "ur": {"arabic"}, "ps": {"arabic"},
    "hi": {"devanagari"}, "mr": {"devanagari"}, "ne": {"devanagari"},
    "th": {"thai"},
    "en": {"latin"}, "fr": {"latin"}, "de": {"latin"}, "es": {"latin"},
    "it": {"latin"}, "pt": {"latin"}, "nl": {"latin"}, "pl": {"latin"},
    "cs": {"latin"}, "sk": {"latin"}, "sv": {"latin"}, "da": {"latin"},
    "no": {"latin"}, "nb": {"latin"}, "nn": {"latin"}, "fi": {"latin"},
    "hu": {"latin"}, "ro": {"latin"}, "tr": {"latin"}, "vi": {"latin"},
    "id": {"latin"}, "ms": {"latin"}, "hr": {"latin"}, "sl": {"latin"},
    "lt": {"latin"}, "lv": {"latin"}, "et": {"latin"},
}

# Best-effort dialect/variant -> parent-language grouping for index.json's
# `group` field. Purely presentation metadata for a client UI to cluster
# related entries -- every variant still gets its own separate archive.
# Historical-stage qualifiers ("Old ", "Middle ", ...) are stripped
# generically; these overrides cover well-known cases where Wiktionary's
# naming doesn't share a literal substring with the family name.
_HISTORICAL_QUALIFIERS = ("Old", "Middle", "Ancient", "Classical", "Proto-",
                          "Archaic", "Early", "Late", "Medieval", "Vulgar")
_GROUP_OVERRIDES = {
    "mandarin": "Chinese", "cantonese": "Chinese", "min nan": "Chinese",
    "min dong": "Chinese", "hakka": "Chinese", "wu": "Chinese",
    "gan": "Chinese", "jin": "Chinese", "hokkien": "Chinese",
    "egyptian arabic": "Arabic", "moroccan arabic": "Arabic",
    "levantine arabic": "Arabic", "gulf arabic": "Arabic",
    "tunisian arabic": "Arabic", "iraqi arabic": "Arabic",
    "hejazi arabic": "Arabic", "najdi arabic": "Arabic", "sudanese arabic": "Arabic",
}

# A language to build, from whichever source. `source` is "kaikki" (goes
# through the combined dump) or "custom" (a user-supplied word-list URL).
# `folder` is only meaningful for kaikki entries (the href path segment on
# the index page); custom entries use a synthetic "custom:<code>" folder
# purely as a unique key for the TUI's selection dict.
LangEntry = namedtuple(
    "LangEntry",
    ["name", "folder", "senses", "source", "url", "license", "license_url"],
    defaults=(None, None),  # license fields only exist for custom sources
)


# Languages the keyboard app can use, i.e. those it has a layout for.
# Key: the language name exactly as Kaikki.org lists it. Value: the app's language
# codes for it. The first code names the archive; any further code gets its own
# index entry pointing at the same archive (Kaikki has one "Serbo-Croatian" for
# what the app offers as Serbian and Croatian).
# NOT checked against the live Kaikki list (no network when this was written):
# "Serbo-Croatian" and "Norwegian Bokm\u00e5l" are the likely names, and any name here
# that Kaikki does not list is reported before the menu opens.
SUPPORTED_LANGUAGES: Dict[str, Tuple[str, ...]] = {
    "Arabic": ("ar",), "Belarusian": ("be",), "Bulgarian": ("bg",), "Catalan": ("ca",),
    "Czech": ("cs",), "Danish": ("da",), "German": ("de",), "Greek": ("el",),
    "English": ("en",), "Spanish": ("es",), "Estonian": ("et",), "Finnish": ("fi",),
    "French": ("fr",), "Hebrew": ("he",), "Hindi": ("hi",), "Hungarian": ("hu",),
    "Indonesian": ("id",), "Italian": ("it",), "Japanese": ("ja",), "Korean": ("ko",),
    "Latin": ("la",), "Lithuanian": ("lt",), "Malay": ("ms",), "Dutch": ("nl",),
    "Norwegian Bokm\u00e5l": ("no",), "Polish": ("pl",), "Portuguese": ("pt",),
    "Romanian": ("ro",), "Russian": ("ru",), "Slovak": ("sk",),
    "Serbo-Croatian": ("sr", "hr"), "Swedish": ("sv",), "Turkish": ("tr",),
    "Ukrainian": ("uk",),
}

# Display names for the extra (non-first) codes above.
ALIAS_LANGUAGE_NAMES: Dict[str, str] = {"hr": "Croatian"}

# True unless --all-languages is given.
SUPPORTED_ONLY = True


def supported_codes() -> Set[str]:
    return {code for codes in SUPPORTED_LANGUAGES.values() for code in codes}


def filter_supported(languages: List[LangEntry]) -> Tuple[List[LangEntry], List[str]]:
    """Keep only languages the app supports.

    Kaikki entries are matched by name, custom sources by their language code.
    Returns (kept, supported names Kaikki did not list), so a renamed language is
    noticed instead of silently disappearing from the menu.
    """
    codes = supported_codes()
    kept: List[LangEntry] = []
    for lang in languages:
        if lang.source == "custom":
            if lang.folder.split(":", 1)[-1] in codes:
                kept.append(lang)
        elif lang.name in SUPPORTED_LANGUAGES:
            kept.append(lang)
    listed = {l.name for l in languages if l.source == "kaikki"}
    missing = sorted(name for name in SUPPORTED_LANGUAGES if name not in listed)
    return kept, missing


def with_alias_entries(built: Dict[str, dict]) -> Dict[str, dict]:
    """Add an index entry for every extra app code of a built language."""
    result = dict(built)
    for lang_key, entry in built.items():
        for extra_code in SUPPORTED_LANGUAGES.get(entry["lang_name"], ())[1:]:
            alias_key = f"{lang_key}:{extra_code}"
            result[alias_key] = {
                **entry,
                "lang_key": alias_key,
                "lang_code": extra_code,
                "lang_name": ALIAS_LANGUAGE_NAMES.get(extra_code, extra_code),
            }
    return result


def show_notice(stdscr, lines: List[str]) -> None:
    stdscr.clear()
    for i, line in enumerate(lines):
        stdscr.addstr(2 + i, 2, line)
    stdscr.addstr(4 + len(lines), 2, "Press any key to continue...")
    stdscr.refresh()
    stdscr.getch()


def fetch_dynamic_languages() -> List[LangEntry]:
    """Download and parse the list of available languages from Kaikki.org.

    How: fetches the human-readable index page and scrapes per-language links
    of the form '<a href="Folder/page">Name (N senses)</a>'. Why HTML
    scraping instead of an API: Kaikki publishes no structured index
    endpoint; the sense counts still let us rank languages by coverage. A
    hardcoded fallback guarantees the TUI always has a usable list even if
    the site is down.
    """
    languages: List[LangEntry] = []
    fallback_languages = [
        LangEntry("English", "English", 1787236, "kaikki", None),
        LangEntry("German", "German", 633412, "kaikki", None),
        LangEntry("French", "French", 459894, "kaikki", None),
        LangEntry("Spanish", "Spanish", 875726, "kaikki", None),
    ]
    # Real markup (confirmed from a live fetch) is:
    #   <li><a href="English/index.html">English (1787236 senses)</a></li>
    # i.e. the sense count lives INSIDE the anchor text. Two patterns are
    # tried: strict double-quoted first, then a quote-agnostic,
    # comma-tolerant fallback as cheap insurance against markup drift.
    patterns = [
        re.compile(
            r'href="([^/"]+)/[^"]+">\s*([^(<]+?)\s*\((\d+)\s*senses\)\s*</a>',
            re.IGNORECASE
        ),
        re.compile(
            r'''href=['"]([^/'"]+)/[^'"]+['"][^>]*>\s*([^(<]+?)\s*\(([\d,]+)\s*senses\)\s*</a>''',
            re.IGNORECASE
        ),
    ]

    try:
        req = urllib.request.Request(INDEX_URL, headers={"User-Agent": "Mozilla/5.0"})
        with urllib.request.urlopen(req, timeout=30) as response:
            html_content = response.read().decode("utf-8", errors="ignore")

        matches: List[Tuple[str, str, str]] = []
        for pattern_idx, pattern in enumerate(patterns):
            matches = pattern.findall(html_content)
            if matches:
                logger.info("Language index parsed with pattern #%d, %d raw matches",
                           pattern_idx, len(matches))
                break

        seen = set()
        for folder, lang_name, senses in matches:
            # Language names can contain HTML entities (e.g. "K&#x27;iche&#x27;"
            # for "K'iche'"). Unescaping matters beyond display: the same
            # decoded name is later compared against the `lang` field in the
            # raw data, which has the literal apostrophe, not the entity.
            lang_name = html.unescape(lang_name).strip()
            if lang_name.lower() in NON_LANGUAGE_ENTRIES:
                continue
            if lang_name not in seen:
                seen.add(lang_name)
                languages.append(LangEntry(
                    lang_name, folder, int(senses.replace(",", "")), "kaikki", None
                ))

        languages.sort(key=lambda e: e.senses, reverse=True)

        if not languages:
            # Both patterns matched nothing even though the page loaded fine.
            # The page is small (tens of KB), so dump it whole to a sibling
            # file instead of a truncated log snippet for inspection.
            debug_html_path = Path(LOG_FILE).with_name("index_debug.html")
            try:
                debug_html_path.write_text(html_content, encoding="utf-8")
            except OSError:
                debug_html_path = None
            logger.warning(
                "Fetched %s (%d bytes) but found 0 language entries with either "
                "pattern. Falling back to the static list. Full response saved to: %s",
                INDEX_URL, len(html_content), debug_html_path
            )
    except Exception as exc:
        logger.warning("Could not load dynamic language index (%s: %s), using fallback",
                       type(exc).__name__, exc)

    if not languages:
        languages = fallback_languages

    return languages


def load_custom_sources() -> List[LangEntry]:
    """Load user-defined dictionary sources from sources.json, if present.

    Format:
      {"custom_languages": [
          {"lang_name": "Klingon", "lang_code": "tlh",
           "url": "https://example.com/klingon-words.txt"}
      ]}

    Each URL must point to a plain text file, one word per line. This is the
    escape hatch for languages/sources kaikki doesn't cover, without having
    to touch the code. A missing or malformed config file is never fatal --
    it just means no custom sources get added, which is logged, not raised.
    """
    if not SOURCES_CONFIG_FILE.exists():
        return []

    try:
        raw = json.loads(SOURCES_CONFIG_FILE.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as exc:
        logger.warning("Could not read %s (%s: %s); ignoring custom sources",
                       SOURCES_CONFIG_FILE, type(exc).__name__, exc)
        return []

    entries: List[LangEntry] = []
    for item in raw.get("custom_languages", []):
        name = item.get("lang_name")
        code = item.get("lang_code")
        url = item.get("url")
        if not (name and code and url):
            logger.warning("Skipping malformed entry in %s: %r", SOURCES_CONFIG_FILE, item)
            continue
        entries.append(LangEntry(
            name, f"custom:{code.lower()}", 0, "custom", url,
            item.get("license") or None, item.get("license_url") or None,
        ))

    return entries


def is_valid_token(word: str) -> bool:
    """Validate token length and character set."""
    if not (MIN_WORD_LENGTH <= len(word) <= MAX_WORD_LENGTH):
        return False
    if UNIVERSAL_WORD_REGEX.match(word):
        return True
    if word.isascii():
        return False
    return _is_word_with_marks(word)


def _is_word_with_marks(word: str) -> bool:
    """Slow path for non-ASCII words the fast regex rejected. Python's \\w
    does not count combining marks (Unicode categories M*) as word
    characters, so words in Devanagari, Thai, Arabic with vowel marks, etc.
    ("हिन्दी") failed the fast path even though they are ordinary words.
    Here a word is accepted if it starts with a letter, contains only
    letters/marks and single inner joiners, and ends on a letter or mark.
    Only reached for words the regex already rejected, so the per-character
    category lookups don't slow down the common case."""
    if unicodedata.category(word[0])[0] != "L":
        return False
    prev_joiner = False
    for ch in word:
        if ch in WORD_JOINERS:
            if prev_joiner:
                return False
            prev_joiner = True
        elif unicodedata.category(ch)[0] in ("L", "M"):
            prev_joiner = False
        else:
            return False
    return not prev_joiner


def detect_script(word: str) -> Optional[str]:
    """Return the Unicode script of the first recognized character in the
    word, or None if it's in a script we don't have a range for. Checking
    only the first character (rather than every character) is a deliberate
    cheap-and-good-enough tradeoff -- this runs on every candidate word."""
    for ch in word:
        cp = ord(ch)
        for script, lo, hi in _SCRIPT_RANGES:
            if lo <= cp <= hi:
                return script
    return None


def script_is_acceptable(word: str, expected_scripts: Optional[Set[str]]) -> bool:
    """True if the word's script matches what's expected for its language,
    OR if we don't have an expectation for that language (unknown lang_code
    or unrecognized script) -- in which case we deliberately don't filter,
    to avoid rejecting legitimate data for languages we haven't mapped."""
    if not expected_scripts:
        return True
    script = detect_script(word)
    return script is None or script in expected_scripts


def derive_group(lang_name: str, all_names_lower: Set[str]) -> str:
    """Best-effort grouping of a dialect/historical-stage/variant under its
    parent language name, for index.json's `group` field. This is display
    metadata only -- it does not change how words are downloaded or
    archived; each variant remains its own separate archive. Coverage is
    necessarily partial: anything the heuristic can't relate to a parent
    just becomes its own single-member group (its own name).
    """
    lower = lang_name.lower()
    if lower in _GROUP_OVERRIDES:
        return _GROUP_OVERRIDES[lower]

    words = lang_name.split()
    if len(words) > 1:
        if words[0] in _HISTORICAL_QUALIFIERS:
            remainder = " ".join(words[1:])
            if remainder.lower() in all_names_lower:
                return remainder
        if words[0].lower() in all_names_lower and words[0].lower() != lower:
            return words[0]

    return lang_name


def compute_sha256(path: Path) -> str:
    """Stream a file through SHA-256 in fixed-size chunks so checksumming a
    multi-hundred-MB archive doesn't require loading it into memory."""
    digest = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_manifest(output_dir: Path) -> Dict[str, dict]:
    """Read the existing index.json (if any) into a dict keyed by lang_key,
    so callers can look up "do we already have this language built"."""
    manifest_path = output_dir / INDEX_JSON_FILENAME
    if not manifest_path.exists():
        return {}
    try:
        data = json.loads(manifest_path.read_text(encoding="utf-8"))
        return {entry["lang_key"]: entry for entry in data.get("languages", []) if "lang_key" in entry}
    except (json.JSONDecodeError, OSError, KeyError, TypeError) as exc:
        logger.warning("Could not read existing %s (%s: %s); treating as empty",
                       manifest_path, type(exc).__name__, exc)
        return {}


def save_manifest(output_dir: Path, entries: Dict[str, dict]) -> None:
    """Write index.json: the server-side manifest a keyboard client reads to
    discover which languages are available, their archive filenames, sizes,
    and checksums to verify after download."""
    manifest_path = output_dir / INDEX_JSON_FILENAME
    payload = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        **manifest_attribution(),
        "languages": sorted(entries.values(), key=lambda e: e["lang_name"]),
    }
    manifest_path.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")


def is_cache_valid(entry: dict, output_dir: Path) -> bool:
    """Authoritative "already built and not corrupted" check. Existence
    alone isn't enough -- a truncated download or a hand-edited archive
    should be treated as needing a rebuild, not silently trusted, so this
    always re-hashes the file rather than trusting a cached flag."""
    archive_path = output_dir / entry.get("archive", "")
    if not entry.get("archive") or not archive_path.exists():
        return False
    try:
        return compute_sha256(archive_path) == entry.get("sha256")
    except OSError:
        return False


def _license_label_from_url(url: str) -> Optional[str]:
    """Turn a Creative Commons license URL into a short label, e.g.
    ".../licenses/by-sa/4.0/" -> "CC BY-SA 4.0". The wiki API's own `text`
    field has no version number ("Creative Commons Attribution-ShareAlike
    License"), and the version is exactly what matters, so it is read from
    the URL. Returns None for non-CC URLs."""
    match = re.search(r"creativecommons\.org/licenses/([a-z\-]+)/([\d.]+)", url)
    if not match:
        return None
    return f"CC {match.group(1).upper()} {match.group(2)}"


def resolve_wiktionary_license() -> Tuple[str, str]:
    """Ask English Wiktionary which license its content is published under
    (MediaWiki API, siprop=rightsinfo) and cache the answer for this run.

    Why not hardcode it: the version is easy to get wrong (older material
    and third-party repos still say 3.0, the site now says 4.0) and it can
    change again. Any failure -- offline, timeout, unexpected response --
    falls back to the built-in constants and is logged, never fatal.
    """
    global _resolved_source_license
    label, url = WIKTIONARY_LICENSE, WIKTIONARY_LICENSE_URL
    try:
        # Wikimedia asks API clients for a descriptive User-Agent rather
        # than a browser string, so this call identifies itself.
        req = urllib.request.Request(
            WIKTIONARY_API_URL,
            headers={"User-Agent": "DictionaryBuilder/1.0 (keyboard word-list builder)"},
        )
        with urllib.request.urlopen(req, timeout=15) as response:
            info = json.loads(response.read().decode("utf-8"))["query"]["rightsinfo"]
        api_url = str(info.get("url") or "").strip()
        if api_url.startswith("//"):  # the API may return a protocol-relative URL
            api_url = "https:" + api_url
        if api_url.startswith(("http://", "https://")):
            url = api_url
            label = _license_label_from_url(api_url) or str(info.get("text") or label)
            logger.info("Wiktionary license from API: %s (%s)", label, url)
        else:
            logger.warning("Wiktionary API returned no usable license URL; using fallback %s", label)
    except Exception as exc:
        logger.warning("Could not fetch Wiktionary license (%s: %s); using fallback %s",
                       type(exc).__name__, exc, label)
    _resolved_source_license = (label, url)
    return _resolved_source_license


def current_wiktionary_license() -> Tuple[str, str]:
    """(label, url) resolved for this run, or the built-in fallback if no
    build has resolved it (e.g. --example). Never touches the network."""
    return _resolved_source_license or (WIKTIONARY_LICENSE, WIKTIONARY_LICENSE_URL)


def manifest_attribution() -> dict:
    """Top-level attribution fields for index.json."""
    label, url = current_wiktionary_license()
    return {
        "license": label,
        "license_url": url,
        "source": KAIKKI_URL,
        "attribution": WIKTIONARY_ATTRIBUTION,
        "citation": WIKTEXTRACT_CITATION,
    }


def license_fields(lang: Optional[LangEntry]) -> dict:
    """Per-language license/attribution fields for an index.json entry.
    Written on every entry (not only custom ones) because a catalog can mix
    Wiktionary-derived and user-supplied languages, so the single top-level
    license would be wrong for some entries."""
    if lang is not None and lang.source == "custom":
        fields = {
            "license": lang.license or UNKNOWN_LICENSE,
            "attribution": f"Data from {lang.url}",
        }
        if lang.license_url:  # only when the user actually gave one
            fields["license_url"] = lang.license_url
        return fields
    label, url = current_wiktionary_license()
    return {"license": label, "license_url": url, "attribution": WIKTIONARY_ATTRIBUTION}


def license_changed(entry: dict, lang: LangEntry) -> bool:
    """True if an otherwise-valid cached archive carries stale license text
    in its ATTRIBUTION.txt and must be rebuilt. Custom sources are small
    and cheap, so a missing license also triggers a rebuild for them.
    Wiktionary-derived archives built before license tracking existed are
    NOT rebuilt (that would mean re-downloading gigabytes); they just get
    the fields backfilled in the manifest."""
    expected = license_fields(lang)
    if "license" not in entry:
        return lang.source == "custom"
    if lang.source == "custom":
        return (entry["license"] != expected["license"]
                or entry.get("license_url") != expected.get("license_url"))
    return entry["license"] != expected["license"]


def build_attribution_text(lang_name: str, built_at: str,
                           lang: Optional[LangEntry], example: bool = False) -> str:
    """Contents of ATTRIBUTION.txt, placed inside every archive so the
    attribution travels with the data even when the archive is copied away
    from index.json."""
    if lang is not None and lang.source == "custom":
        lic = lang.license
        if not lic or lic.lower() == UNKNOWN_LICENSE:
            lic = "Unknown - user-supplied source"
        elif lang.license_url and lang.license_url != lic:
            lic = f"{lic} ({lang.license_url})"
        text = (f"{lang_name} word list\n\n"
                f"Source: {lang.url}\n"
                f"Built: {built_at}\n"
                f"License: {lic}\n")
    else:
        label, url = current_wiktionary_license()
        text = (f"{lang_name} word list\n\n"
                f"Source: English Wiktionary ({WIKTIONARY_URL}), extracted\n"
                "via kaikki.org (wiktextract by Tatu Ylonen).\n"
                f"Built: {built_at}\n"
                f"License: {label} ({url})\n\n"
                "This word list is a derivative work of Wiktionary content and is\n"
                "distributed under the same license. The full list of authors of\n"
                "each Wiktionary entry is available in the edit history of the\n"
                "corresponding page.\n\n"
                "Citation: Tatu Ylonen: Wiktextract: Wiktionary as Machine-Readable\n"
                "Structured Data, Proceedings of LREC 2022, pp. 1317-1325.\n")
    if example:
        text += "\nNOTE: this is an EXAMPLE archive with made-up sample words, not real data.\n"
    return text


def save_custom_license(lang: LangEntry, license_text: str) -> LangEntry:
    """Persist a license for a custom source into sources.json and return
    the updated entry. If the text is a URL it is also stored as
    license_url; otherwise any stale license_url is dropped. Written via a
    temp file + rename so a crash can never leave a half-written config.
    Raises ValueError if the source is no longer in the file."""
    raw = json.loads(SOURCES_CONFIG_FILE.read_text(encoding="utf-8"))
    is_url = license_text.lower().startswith(("http://", "https://"))
    for item in raw.get("custom_languages", []):
        if item.get("lang_name") == lang.name and item.get("url") == lang.url:
            item["license"] = license_text
            if is_url:
                item["license_url"] = license_text
            else:
                item.pop("license_url", None)
            break
    else:
        raise ValueError(f"{lang.name} not found in {SOURCES_CONFIG_FILE}")

    tmp_path = SOURCES_CONFIG_FILE.with_name(SOURCES_CONFIG_FILE.name + ".tmp")
    tmp_path.write_text(json.dumps(raw, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    os.replace(tmp_path, SOURCES_CONFIG_FILE)
    return lang._replace(license=license_text, license_url=license_text if is_url else None)


def prompt_license(stdscr, lang: LangEntry) -> str:
    """Text-entry screen asking for a custom source's license. Returns the
    stripped input; empty string means "leave unknown"."""
    curses.echo()
    curses.curs_set(1)
    try:
        stdscr.clear()
        height, width = stdscr.getmaxyx()
        stdscr.addstr(2, 2, f"Custom source: {lang.name} ({lang.url})"[:width - 4])
        stdscr.addstr(4, 2, "What license does this word list use?")
        stdscr.addstr(5, 2, '(e.g. "CC0", "MIT", "public domain", or a URL to the license)')
        stdscr.addstr(6, 2, "Leave empty to mark it as UNKNOWN.")
        stdscr.addstr(8, 2, "License: ")
        stdscr.refresh()
        raw = stdscr.getstr(8, 11, max(1, min(200, width - 13)))
        return raw.decode("utf-8", errors="ignore").strip()
    except curses.error:
        return ""
    finally:
        curses.noecho()
        curses.curs_set(0)


def confirm_unknown_license(stdscr, name: str) -> bool:
    """Warn that a custom source has no license and ask to continue anyway.
    True only on an explicit Y; N or Esc cancels."""
    stdscr.clear()
    height, width = stdscr.getmaxyx()
    lines = [
        f'No license specified for "{name}".',
        "",
        'The word list will be marked as "license: unknown" in',
        "index.json. You are responsible for verifying that you have",
        "the right to redistribute this data. Continue?",
        "",
        "[Y] Yes, continue    [N] Cancel",
    ]
    for i, text in enumerate(lines):
        stdscr.addstr(2 + i, 2, text[:max(1, width - 4)])
    stdscr.refresh()
    while True:
        key = stdscr.getch()
        if key in (ord('y'), ord('Y')):
            return True
        if key in (ord('n'), ord('N'), 27):
            return False


def edit_custom_license(stdscr, lang: LangEntry) -> LangEntry:
    """Ask for a license, confirm if left empty, save it. Returns the
    (possibly unchanged) entry; any failure is shown and logged, not raised."""
    text = prompt_license(stdscr, lang)
    if not text:
        if not confirm_unknown_license(stdscr, lang.name):
            return lang
        text = UNKNOWN_LICENSE
    try:
        updated = save_custom_license(lang, text)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        logger.warning("Could not save license for %s: %s: %s", lang.name, type(exc).__name__, exc)
        stdscr.clear()
        stdscr.addstr(2, 2, "Could not save the license to sources.json (see debug log).")
        stdscr.addstr(4, 2, "Press any key...")
        stdscr.refresh()
        stdscr.getch()
        return lang
    logger.info("License set for custom source %s: %s", lang.name, text)
    return updated


def run_license_menu(stdscr, languages: List[LangEntry]) -> None:
    """[L] screen: list the custom sources and set each one's license.
    Replaces entries in `languages` in place so the main picker and the
    build see the new values immediately."""
    custom_idx = [i for i, lang in enumerate(languages) if lang.source == "custom"]
    if not custom_idx:
        stdscr.clear()
        stdscr.addstr(2, 2, f"No custom sources found in {SOURCES_CONFIG_FILE}.")
        stdscr.addstr(4, 2, "Press any key to go back...")
        stdscr.refresh()
        stdscr.getch()
        return

    current = 0
    while True:
        stdscr.clear()
        height, width = stdscr.getmaxyx()
        stdscr.addstr(0, 2, " CUSTOM SOURCE LICENSES ", curses.A_REVERSE)
        stdscr.addstr(1, 2, "[Up/Down] Navigate | [Enter] Set license | [Q] Back"[:max(1, width - 3)])
        for row, idx in enumerate(custom_idx):
            y_pos = 3 + row
            if y_pos >= height - 1:
                break
            lang = languages[idx]
            line = f" {lang.name} ({lang.url})  license: {lang.license or 'not set'}"
            attr = curses.A_STANDOUT if row == current else curses.A_NORMAL
            stdscr.addstr(y_pos, 2, line[:max(1, width - 4)], attr)
        stdscr.refresh()

        key = stdscr.getch()
        if key in (curses.KEY_UP, ord('k')):
            current = (current - 1) % len(custom_idx)
        elif key in (curses.KEY_DOWN, ord('j')):
            current = (current + 1) % len(custom_idx)
        elif key in (10, 13):
            idx = custom_idx[current]
            languages[idx] = edit_custom_license(stdscr, languages[idx])
        elif key in (ord('q'), ord('Q'), 27):
            return


def resolve_unlicensed_custom(stdscr, chosen: List[LangEntry]) -> Tuple[List[LangEntry], int]:
    """Before building, make sure every chosen custom source either has a
    license or an explicit "unknown" acknowledgement. Answering N skips that
    source for this run (nothing else is blocked). Acknowledgements are
    saved to sources.json so the question is not asked again. Returns
    (sources to build, number skipped)."""
    kept: List[LangEntry] = []
    skipped = 0
    for lang in chosen:
        if lang.source != "custom" or lang.license is not None:
            kept.append(lang)
            continue
        if not confirm_unknown_license(stdscr, lang.name):
            logger.warning("Skipping custom source %s: no license and not confirmed", lang.name)
            skipped += 1
            continue
        try:
            lang = save_custom_license(lang, UNKNOWN_LICENSE)
        except (OSError, ValueError, json.JSONDecodeError) as exc:
            logger.warning("Could not persist 'unknown' license for %s: %s", lang.name, exc)
            lang = lang._replace(license=UNKNOWN_LICENSE)
        kept.append(lang)
    return kept, skipped


def prompt_for_output_dir(stdscr) -> Optional[Path]:
    """Small curses text-entry screen for typing a custom output directory
    at runtime. Returns None on empty input (cancel), otherwise the
    expanded, unresolved Path (caller is responsible for .resolve()/mkdir).
    """
    curses.echo()
    curses.curs_set(1)
    try:
        stdscr.clear()
        height, width = stdscr.getmaxyx()
        stdscr.addstr(2, 2, "New output directory (index.json + archives go here):")
        stdscr.addstr(3, 2, f"Current: {OUTPUT_DIR}")
        stdscr.addstr(5, 2, "Leave empty and press Enter to cancel.")
        stdscr.addstr(7, 2, "> ")
        stdscr.refresh()
        raw_bytes = stdscr.getstr(7, 4, min(200, width - 6))
        raw = raw_bytes.decode("utf-8", errors="ignore").strip()
    except curses.error:
        raw = ""
    finally:
        curses.noecho()
        curses.curs_set(0)

    return Path(raw).expanduser() if raw else None


def run_interactive_menu(
    stdscr, languages: List[LangEntry]
) -> Tuple[List[LangEntry], bool]:
    """Interactive TUI with scrolling and multi-select of target languages.

    Returns (selected LangEntry list, force_rebuild flag). The cache
    manifest (for the "[cached]" display hint) is loaded from OUTPUT_DIR
    internally and reloaded whenever [D] changes it mid-session -- the
    actual skip decision re-checks each archive's checksum at build time
    rather than trusting this display snapshot.
    """
    global OUTPUT_DIR

    curses.curs_set(0)
    curses.use_default_colors()

    def refresh_cached_keys() -> Set[str]:
        manifest = load_manifest(OUTPUT_DIR)
        return {
            key for key, entry in manifest.items()
            if (OUTPUT_DIR / entry.get("archive", "")).exists()
        }

    selected = {lang.folder: True for lang in languages}
    current_idx = 0
    scroll_offset = 0
    force_rebuild = False
    cached_keys = refresh_cached_keys()

    while True:
        stdscr.clear()
        height, width = stdscr.getmaxyx()

        title = " DYNAMIC LANGUAGE SELECTION FOR DICTIONARY BUILD "
        stdscr.addstr(0, max(0, (width - len(title)) // 2), title, curses.A_REVERSE)

        help_text = "[Spc] Toggle [A]ll [C]lear [F]orce [D]ir [L]icenses [Enter] Build [Q]uit"
        stdscr.addstr(1, max(0, (width - len(help_text)) // 2), help_text[:width - 1], curses.A_BOLD)
        rebuild_label = f" Force full rebuild (ignore cache): {'ON' if force_rebuild else 'OFF'} "
        stdscr.addstr(2, max(0, (width - len(rebuild_label)) // 2), rebuild_label,
                     curses.A_REVERSE if force_rebuild else curses.A_DIM)
        output_label = f" Output: {OUTPUT_DIR} "
        stdscr.addstr(3, max(0, (width - len(output_label)) // 2), output_label[:width - 1], curses.A_DIM)
        stdscr.addstr(4, 0, "-" * (width - 1))

        max_list_height = height - 7
        for i in range(max_list_height):
            idx = scroll_offset + i
            if idx >= len(languages):
                break

            lang = languages[idx]
            checkbox = "[x]" if selected[lang.folder] else "[ ]"
            if lang.source == "custom":
                status = f"(custom source, license: {lang.license or 'not set'})"
            else:
                status = f"(senses: {lang.senses:,})"
            cached_tag = " [cached]" if lang.name.lower() in cached_keys else ""
            line = f" {checkbox} {lang.name} {status}{cached_tag}"

            y_pos = 5 + i
            if idx == current_idx:
                stdscr.addstr(y_pos, 2, line[:width - 4], curses.A_STANDOUT)
            else:
                stdscr.addstr(y_pos, 2, line[:width - 4])

        stdscr.refresh()
        key = stdscr.getch()

        if key in (curses.KEY_UP, ord('k')):
            current_idx = (current_idx - 1) % len(languages)
            if current_idx < scroll_offset:
                scroll_offset = current_idx
        elif key in (curses.KEY_DOWN, ord('j')):
            current_idx = (current_idx + 1) % len(languages)
            if current_idx >= scroll_offset + max_list_height:
                scroll_offset = current_idx - max_list_height + 1
        elif key == ord(' '):
            folder = languages[current_idx].folder
            selected[folder] = not selected[folder]
        elif key in (ord('a'), ord('A')):
            for lang in languages:
                selected[lang.folder] = True
        elif key in (ord('c'), ord('C')):
            for lang in languages:
                selected[lang.folder] = False
        elif key in (ord('f'), ord('F')):
            force_rebuild = not force_rebuild
        elif key in (ord('l'), ord('L')):
            run_license_menu(stdscr, languages)
        elif key in (ord('d'), ord('D')):
            new_dir = prompt_for_output_dir(stdscr)
            if new_dir is not None:
                OUTPUT_DIR = new_dir.resolve()
                OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
                cached_keys = refresh_cached_keys()
        elif key in (10, 13):
            chosen = [lang for lang in languages if selected[lang.folder]]
            if chosen:
                return chosen, force_rebuild
        elif key in (ord('q'), ord('Q'), 27):
            sys.exit(0)


def progress_callback(stdscr, stage: str, current_val: int, total_val: int, details: str):
    """Render a detailed progress screen with percentage and current status."""
    stdscr.clear()
    height, width = stdscr.getmaxyx()

    stdscr.addstr(1, 2, "=== DICTIONARY BUILD AND VALIDATION ===", curses.A_BOLD)
    stdscr.addstr(3, 2, f"Current stage: {stage}")
    stdscr.addstr(4, 2, f"Details: {details[:width - 15]}")

    if total_val > 0:
        percent = min(100.0, (current_val / total_val) * 100)
        bar_width = min(50, width - 20)
        filled = int(bar_width * percent / 100)
        bar = "#" * filled + "-" * (bar_width - filled)
        stdscr.addstr(6, 2, f"Progress: [{bar}] {percent:.1f}%")
        stdscr.addstr(7, 2, f"Processed bytes/lines: {current_val:,} of {total_val:,}")
    else:
        stdscr.addstr(6, 2, f"Status: {current_val:,} items processed (streaming mode)")

    stdscr.addstr(height - 2, 2, "Please wait. Disk-bound processing in progress...", curses.A_DIM)
    stdscr.refresh()


class _CountingReader:
    """Wraps a raw HTTP response so gzip can decompress directly from the
    socket while we still know how many *compressed* bytes have come in, so
    the multi-gigabyte dump is never written to disk before parsing."""

    def __init__(self, response):
        self._response = response
        self.downloaded = 0

    def read(self, size: int = -1) -> bytes:
        chunk = self._response.read(size if size and size > 0 else DOWNLOAD_CHUNK_SIZE)
        self.downloaded += len(chunk)
        return chunk

    def readable(self) -> bool:
        return True


class WordBufferManager:
    """Buffers words per (lang_key, first_letter) bucket, flushing a bucket
    to disk once it hits WORD_BUFFER_FLUSH_SIZE, and flushing EVERYTHING as
    a safety net if the total across all buckets crosses
    GLOBAL_BUFFER_WORD_CAP. The per-bucket cap alone doesn't bound total
    memory when hundreds of languages are selected simultaneously (many
    buckets, each individually small, still add up to gigabytes) -- that
    combination is what previously got the whole process killed by the OS's
    OOM killer on a large multi-language run. At most one file is open at
    any instant either way.
    """

    def __init__(self):
        self.buffers: Dict[Tuple[str, str], List[str]] = {}
        self.lang_dirs: Dict[str, Path] = {}
        self.total_buffered = 0

    def register_lang_dir(self, lang_key: str, lang_dir: Path) -> None:
        self.lang_dirs[lang_key] = lang_dir

    def add(self, lang_key: str, word: str) -> None:
        first_letter = word[0].lower()
        key = (lang_key, first_letter)
        buf = self.buffers.setdefault(key, [])
        buf.append(word)
        self.total_buffered += 1

        if len(buf) >= WORD_BUFFER_FLUSH_SIZE:
            self._flush_bucket(key, buf)
        elif self.total_buffered >= GLOBAL_BUFFER_WORD_CAP:
            self.flush_all()

    def _flush_bucket(self, key: Tuple[str, str], buf: List[str]) -> None:
        if not buf:
            return
        lang_key, first_letter = key
        _flush_word_buffer(self.lang_dirs[lang_key], first_letter, buf)
        self.total_buffered -= len(buf)
        buf.clear()

    def flush_all(self) -> None:
        for key, buf in self.buffers.items():
            self._flush_bucket(key, buf)

    def close(self) -> None:
        """Final drain -- most buckets won't have hit the per-bucket cap
        exactly on the last word of the stream."""
        self.flush_all()


def _flush_word_buffer(lang_dir: Path, first_letter: str, words: List[str]) -> None:
    """Append a batch of buffered words to their letter file and close it
    immediately -- no handle is held open between flushes."""
    if not words:
        return
    with open(lang_dir / f"{first_letter}.tmp", "a", encoding="utf-8") as f:
        f.write("\n".join(words) + "\n")


def process_dumps_with_progress(
    stdscr, target_langs: List[LangEntry], temp_dir: Path
) -> Dict[str, str]:
    """Stream the single combined raw Wiktextract dump once and partition
    every selected kaikki-sourced language's words in the same pass.

    Returns lang_key (lowercase canonical name) -> lang_code, taken straight
    from the data's own `lang_code` field.
    """
    partition_base = temp_dir / "partition"
    partition_base.mkdir(parents=True, exist_ok=True)

    wanted_names: Dict[str, str] = {lang.name.lower(): lang.name for lang in target_langs}
    needles: Dict[str, str] = {f'"lang": "{name}"': key for key, name in wanted_names.items()}

    lang_part_dirs: Dict[str, Path] = {}
    lang_codes: Dict[str, str] = {}
    lang_expected_scripts: Dict[str, Optional[Set[str]]] = {}
    buf_mgr = WordBufferManager()
    line_count = 0

    req = urllib.request.Request(RAW_DUMP_URL, headers={"User-Agent": "Mozilla/5.0"})
    try:
        with urllib.request.urlopen(req, timeout=60) as response:
            total_compressed = int(response.headers.get("Content-Length") or 0)
            counting = _CountingReader(response)

            with gzip.GzipFile(fileobj=counting) as gz_stream:
                text_stream = io.TextIOWrapper(gz_stream, encoding="utf-8", errors="ignore")
                for raw_line in text_stream:
                    line_count += 1
                    if line_count % PROGRESS_REFRESH_EVERY_LINES == 0:
                        progress_callback(
                            stdscr, "Downloading & parsing combined dump",
                            counting.downloaded, total_compressed,
                            f"{line_count:,} lines scanned, "
                            f"{len(lang_part_dirs)} of {len(wanted_names)} languages found, "
                            f"{buf_mgr.total_buffered:,} words buffered"
                        )

                    if not any(needle in raw_line for needle in needles):
                        continue

                    line = raw_line.strip()
                    if not line:
                        continue
                    try:
                        data = json.loads(line)
                    except json.JSONDecodeError:
                        continue

                    rec_lang = data.get("lang")
                    if not rec_lang:
                        continue
                    lang_key = rec_lang.lower()
                    if lang_key not in wanted_names:
                        continue

                    if lang_key not in lang_part_dirs:
                        lang_dir = partition_base / lang_key
                        lang_dir.mkdir(exist_ok=True)
                        lang_part_dirs[lang_key] = lang_dir
                        buf_mgr.register_lang_dir(lang_key, lang_dir)
                        lang_codes[lang_key] = str(data.get("lang_code") or lang_key[:2]).lower()
                        lang_expected_scripts[lang_key] = LANG_CODE_EXPECTED_SCRIPTS.get(
                            lang_codes[lang_key]
                        )

                    expected_scripts = lang_expected_scripts[lang_key]

                    word = data.get("word")
                    if word and is_valid_token(word) and script_is_acceptable(word, expected_scripts):
                        buf_mgr.add(lang_key, word)

                    for form_entry in data.get("forms", []):
                        if isinstance(form_entry, dict):
                            form_val = form_entry.get("form")
                            if (form_val and is_valid_token(form_val)
                                    and script_is_acceptable(form_val, expected_scripts)):
                                buf_mgr.add(lang_key, form_val)
    finally:
        buf_mgr.close()

    return lang_codes


def process_custom_source(
    stdscr, lang: LangEntry, temp_dir: Path, idx: int, total: int
) -> Tuple[str, str]:
    """Download a plain word-list URL (one word per line) for a custom
    source and partition it the same way kaikki-derived words are, so it
    flows into the same sort/pack pipeline afterwards.

    Returns (lang_key, lang_code).
    """
    lang_key = lang.name.lower()
    lang_code = lang.folder.split(":", 1)[1] if ":" in lang.folder else lang_key[:2]
    lang_dir = temp_dir / "partition" / lang_key
    lang_dir.mkdir(parents=True, exist_ok=True)

    buf_mgr = WordBufferManager()
    buf_mgr.register_lang_dir(lang_key, lang_dir)
    req = urllib.request.Request(lang.url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=60) as response:
        total_size = int(response.headers.get("Content-Length") or 0)
        downloaded = 0
        # http.client.HTTPResponse is directly iterable, yielding raw lines
        # as bytes -- no need for our gzip/TextIOWrapper machinery here
        # since these are plain uncompressed word lists.
        for i, raw_bytes in enumerate(response):
            downloaded += len(raw_bytes)
            if i % PROGRESS_REFRESH_EVERY_LINES == 0:
                progress_callback(
                    stdscr, f"Custom source ({idx}/{total}): {lang.name}",
                    downloaded, total_size, f"{i:,} lines read"
                )
            word = raw_bytes.decode("utf-8", errors="ignore").strip()
            if word and is_valid_token(word):
                buf_mgr.add(lang_key, word)

    buf_mgr.close()

    return lang_key, lang_code


def assemble_and_pack(
    stdscr, temp_dir: Path, lang_codes: Dict[str, str],
    lang_entries: Dict[str, LangEntry], built_at: str,
) -> Dict[str, Tuple[Path, int]]:
    """Case-insensitive, diacritic-aware sort; one archive per language.

    Returns lang_key -> (archive_path, word_count), so the caller can build
    manifest entries (checksum is computed by the caller once the file is
    finalized on disk).
    """
    partition_base = temp_dir / "partition"
    assembly_base = temp_dir / "assembled"
    total_langs = len(lang_codes)
    idx = 0
    results: Dict[str, Tuple[Path, int]] = {}

    for lang_key, lang_code in lang_codes.items():
        idx += 1
        progress_callback(stdscr, "Sorting and assembling", idx, total_langs,
                          f"Processing language: {lang_key}")

        lang_part_dir = partition_base / lang_key
        if not lang_part_dir.exists():
            continue

        final_lang_dir = assembly_base / lang_key
        by_letter_dir = final_lang_dir / "by_letter"
        by_letter_dir.mkdir(parents=True, exist_ok=True)

        word_count = 0

        for letter_file in lang_part_dir.glob("*.tmp"):
            with open(letter_file, "r", encoding="utf-8") as f_in:
                unique_words = {line.strip() for line in f_in if line.strip()}

            if not unique_words:
                continue

            sorted_words = sorted(unique_words, key=_sort_key)

            target_file = by_letter_dir / f"{letter_file.stem}.txt"
            with open(target_file, "w", encoding="utf-8") as f_out:
                f_out.write("\n".join(sorted_words) + "\n")

            word_count += len(sorted_words)

        if not word_count:
            continue

        # No more all_sorted.txt: the by-letter files already are the full,
        # correctly-sorted word list split up, and a keyboard app loads
        # per-letter anyway -- keeping one more full copy of every word
        # around (potentially millions of strings for a large language)
        # only cost memory and archive size without being used.

        # ATTRIBUTION.txt travels inside the archive so the license notice
        # survives even if the archive is copied away from index.json.
        # built_at is passed in (one timestamp per build) so this file and
        # the manifest entry always agree on the build time.
        lang_entry = lang_entries.get(lang_key)
        (final_lang_dir / "ATTRIBUTION.txt").write_text(
            build_attribution_text(lang_entry.name if lang_entry else lang_key,
                                   built_at, lang_entry),
            encoding="utf-8",
        )

        progress_callback(stdscr, "Packing archive", idx, total_langs,
                          f"Creating {lang_code.upper()}-kaikki.tar.gz")
        archive_path = OUTPUT_DIR / f"{lang_code.upper()}-kaikki.tar.gz"
        with tarfile.open(archive_path, "w:gz") as tar:
            tar.add(final_lang_dir, arcname=lang_key)
        results[lang_key] = (archive_path, word_count)

    return results


def _sort_key(word: str):
    """Diacritic- and case-insensitive primary sort key, with case restored
    as a tiebreaker for determinism. NFKD-normalizes and strips combining
    marks so accented variants interleave with their base letters the way a
    reader expects (e.g. e / e-with-diaeresis)."""
    stripped = "".join(
        ch for ch in unicodedata.normalize("NFKD", word)
        if not unicodedata.combining(ch)
    )
    return (stripped.lower(), word.lower(), word)


EXAMPLE_LANGUAGES: List[Tuple[str, str, List[str]]] = [
    ("Polish", "pl", ["cześć", "pies", "książka", "dom", "słońce", "woda", "chleb"]),
    ("English", "en", ["hello", "dog", "book", "house", "sun", "water", "bread"]),
]


def generate_example_output(example_dir: Path) -> None:
    """--example: writes a sample index.json plus a couple of tiny sample
    archives with the EXACT same directory layout a real build produces
    (<lang_key>/by_letter/<letter>.txt inside each archive), but with only
    a handful of made-up words. No network access, no real dump download --
    this exists purely so someone (e.g. writing the Android client) can see
    the real output shape without waiting through a multi-GB build.

    Written to its own subdirectory rather than OUTPUT_DIR itself, so this
    can never overwrite a real, already-built catalog.
    """
    example_dir.mkdir(parents=True, exist_ok=True)
    manifest_entries: Dict[str, dict] = {}
    all_names_lower = {name.lower() for name, _, _ in EXAMPLE_LANGUAGES}
    built_at = datetime.now(timezone.utc).isoformat()

    with tempfile.TemporaryDirectory() as temp_dir_str:
        temp_dir = Path(temp_dir_str)

        for lang_name, lang_code, words in EXAMPLE_LANGUAGES:
            lang_key = lang_name.lower()
            lang_dir = temp_dir / lang_key
            by_letter_dir = lang_dir / "by_letter"
            by_letter_dir.mkdir(parents=True)

            by_letter: Dict[str, List[str]] = {}
            for w in words:
                by_letter.setdefault(w[0].lower(), []).append(w)
            for letter, letter_words in by_letter.items():
                (by_letter_dir / f"{letter}.txt").write_text(
                    "\n".join(sorted(letter_words, key=_sort_key)) + "\n", encoding="utf-8"
                )

            (lang_dir / "ATTRIBUTION.txt").write_text(
                build_attribution_text(lang_name, built_at, None, example=True),
                encoding="utf-8",
            )

            archive_path = example_dir / f"{lang_code.upper()}-kaikki.tar.gz"
            with tarfile.open(archive_path, "w:gz") as tar:
                tar.add(lang_dir, arcname=lang_key)

            manifest_entries[lang_key] = {
                "lang_key": lang_key,
                "lang_name": lang_name,
                "lang_code": lang_code,
                "group": derive_group(lang_name, all_names_lower),
                "archive": archive_path.name,
                "word_count": len(words),
                "weight": archive_path.stat().st_size,
                "sha256": compute_sha256(archive_path),
                "built_at": built_at,
                **license_fields(None),
                "example": True,
            }

    payload = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "example": True,
        "note": ("Sample output showing the real index.json/archive structure "
                "with a handful of made-up words. NOT a real dictionary "
                "catalog -- run without --example to build one."),
        **manifest_attribution(),
        "languages": sorted(manifest_entries.values(), key=lambda e: e["lang_name"]),
    }
    (example_dir / INDEX_JSON_FILENAME).write_text(
        json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8"
    )

    print(f"Example output written to: {example_dir}")
    print(f"  {INDEX_JSON_FILENAME}  (top-level \"example\": true, and on every entry)")
    for entry in manifest_entries.values():
        print(f"  {entry['archive']}  ({entry['word_count']} sample words, "
              f"{entry['weight']} bytes)")


def main(stdscr) -> None:
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # Step 1: fetch available languages (kaikki + any user-defined sources)
    progress_callback(stdscr, "Initialization", 0, 100,
                      "Fetching dynamic language list from Kaikki.org...")
    languages = fetch_dynamic_languages() + load_custom_sources()
    if SUPPORTED_ONLY:
        languages, missing_supported = filter_supported(languages)
        if missing_supported:
            logger.warning("Supported languages not listed by Kaikki: %s", ", ".join(missing_supported))
            show_notice(stdscr, ["Supported by the app but not found on Kaikki.org:"]
                        + [f"  {name}" for name in missing_supported]
                        + ["Check the names in SUPPORTED_LANGUAGES."])
    all_names_lower = {lang.name.lower() for lang in languages}

    # Step 2: interactive selection menu. OUTPUT_DIR may be changed here via
    # [D] -- the manifest/cache lookup for display is handled inside the
    # menu itself so it always reflects whichever directory is current.
    chosen_langs, force_rebuild = run_interactive_menu(stdscr, languages)
    if not chosen_langs:
        return

    # OUTPUT_DIR is final now; (re)ensure it exists and load whichever
    # manifest actually lives there (may differ from the one at startup if
    # the path was changed inside the menu).
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
    manifest = load_manifest(OUTPUT_DIR)

    # Licensing: ask the source wiki which license it uses (falls back to the
    # built-in value offline), and make sure every chosen custom source has a
    # license or an explicit "unknown" acknowledgement before anything builds.
    resolve_wiktionary_license()
    chosen_langs, skipped_unlicensed = resolve_unlicensed_custom(stdscr, chosen_langs)
    if not chosen_langs:
        stdscr.clear()
        stdscr.addstr(2, 2, "Nothing to build: all selected custom sources were skipped.")
        stdscr.addstr(4, 2, "Press any key to exit...")
        stdscr.refresh()
        stdscr.getch()
        return

    try:
        to_build: List[LangEntry] = []
        reused_count = 0
        for lang in chosen_langs:
            lang_key = lang.name.lower()
            entry = manifest.get(lang_key)
            if (not force_rebuild and entry and is_cache_valid(entry, OUTPUT_DIR)
                    and not license_changed(entry, lang)):
                # Backfill fields added in later versions of this script
                # (group, weight) onto older manifest entries that predate
                # them, so the schema stays consistent without forcing a
                # full rebuild just to pick up new metadata.
                changed = False
                if "group" not in entry:
                    entry["group"] = derive_group(entry["lang_name"], all_names_lower)
                    changed = True
                if "weight" not in entry:
                    entry["weight"] = (OUTPUT_DIR / entry["archive"]).stat().st_size
                    changed = True
                for field_name, field_value in license_fields(lang).items():
                    if field_name not in entry:
                        entry[field_name] = field_value
                        changed = True
                if changed:
                    manifest[lang_key] = entry
                reused_count += 1
                continue
            to_build.append(lang)

        built_this_run: Dict[str, dict] = {}

        if to_build:
            with tempfile.TemporaryDirectory() as temp_dir_str:
                temp_dir = Path(temp_dir_str)

                kaikki_langs = [l for l in to_build if l.source == "kaikki"]
                custom_langs = [l for l in to_build if l.source == "custom"]

                lang_codes: Dict[str, str] = {}

                # Step 3a: one streaming pass over the combined dump covers
                # every kaikki-sourced language selected this run.
                if kaikki_langs:
                    lang_codes.update(
                        process_dumps_with_progress(stdscr, kaikki_langs, temp_dir)
                    )
                    if SUPPORTED_ONLY:
                        # The archive and index use the app's code, not the dump's
                        # (the dump says "nb", the app says "no").
                        for l in kaikki_langs:
                            app_codes = SUPPORTED_LANGUAGES.get(l.name)
                            if app_codes and l.name.lower() in lang_codes:
                                lang_codes[l.name.lower()] = app_codes[0]

                # Step 3b: custom word-list sources are fetched individually
                # -- they aren't part of the combined dump.
                for i, lang in enumerate(custom_langs, start=1):
                    lk, lc = process_custom_source(stdscr, lang, temp_dir, i, len(custom_langs))
                    lang_codes[lk] = lc

                if not lang_codes:
                    raise RuntimeError("No data found for the selected languages.")

                # Step 4: assembly, sorting and per-language archiving
                built_at = datetime.now(timezone.utc).isoformat()
                pack_results = assemble_and_pack(
                    stdscr, temp_dir, lang_codes,
                    {l.name.lower(): l for l in to_build}, built_at,
                )

            # Step 5: checksum + manifest entries for what was just built.
            # Done after the TemporaryDirectory closes, since only the final
            # archives (written to OUTPUT_DIR, not temp_dir) need to survive.
            for lang_key, (archive_path, word_count) in pack_results.items():
                lang_entry = next((l for l in to_build if l.name.lower() == lang_key), None)
                lang_name = lang_entry.name if lang_entry else lang_key
                built_this_run[lang_key] = {
                    "lang_key": lang_key,
                    "lang_name": lang_name,
                    "lang_code": lang_codes[lang_key],
                    "group": derive_group(lang_name, all_names_lower),
                    "archive": archive_path.name,
                    "word_count": word_count,
                    "weight": archive_path.stat().st_size,
                    "sha256": compute_sha256(archive_path),
                    "built_at": built_at,
                    **license_fields(lang_entry),
                }
                logger.info("License for %s: %s", lang_name, built_this_run[lang_key]["license"])

        # Merge: keep every previously known language untouched except the
        # ones processed this run (newly built, or already valid and thus
        # unchanged). Languages built in earlier runs but not selected this
        # time stay in the catalog -- this manifest is a persistent
        # server-side index, not a snapshot of "this run only".
        if SUPPORTED_ONLY:
            built_this_run = with_alias_entries(built_this_run)
        full_manifest = {**manifest, **built_this_run}
        save_manifest(OUTPUT_DIR, full_manifest)

        stdscr.clear()
        stdscr.addstr(2, 2, "Build completed successfully!", curses.A_BOLD)
        line = 4
        stdscr.addstr(line, 2, f"Newly built: {len(built_this_run)}  |  "
                                f"Reused from cache: {reused_count}  |  "
                                f"Total in catalog: {len(full_manifest)}"
                                + (f"  |  Skipped (no license confirmation): {skipped_unlicensed}"
                                   if skipped_unlicensed else ""))
        line += 2
        for lang_key, entry in list(built_this_run.items())[:max(1, (curses.LINES if hasattr(curses, 'LINES') else 20) - line - 3)]:
            stdscr.addstr(line, 2, f"  {entry['archive']}  ({entry['word_count']:,} words)")
            line += 1
        stdscr.addstr(line + 1, 2, f"Manifest: {OUTPUT_DIR / INDEX_JSON_FILENAME}")
        stdscr.addstr(line + 3, 2, "Press any key to exit...")
        stdscr.refresh()
        stdscr.getch()
    except Exception:
        # Rule 11 (release target): end users must see a sanitized message.
        # Full details are already captured in the debug log file.
        logger.exception("Build failed")
        stdscr.clear()
        stdscr.addstr(2, 2, "Build failed. See debug log for details.", curses.A_BOLD)
        stdscr.addstr(4, 2, "Press any key to exit...")
        stdscr.refresh()
        stdscr.getch()
        sys.exit(1)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Kaikki.org-based dictionary builder for a keyboard app."
    )
    parser.add_argument(
        "-d", "--output-dir", type=str, default=None,
        help="Directory for index.json and archives. Defaults to "
             "out-dictionaries next to this script (or $DICT_BUILDER_OUTPUT_DIR "
             "if set). Can also be changed at runtime from the language "
             "picker with the [D] key."
    )
    parser.add_argument(
        "--example", action="store_true",
        help="Write a sample index.json plus a couple of tiny sample archives "
             "showing the real output structure -- no network access, no real "
             "build. Written to OUTPUT_DIR/example/, never touches a real catalog."
    )
    parser.add_argument(
        "--all-languages", action="store_true",
        help="List every Kaikki language and custom source, not only the ones the "
             "keyboard app supports.",
    )
    args = parser.parse_args()
    if args.all_languages:
        SUPPORTED_ONLY = False

    if args.output_dir:
        OUTPUT_DIR = Path(args.output_dir).expanduser().resolve()

    if args.example:
        generate_example_output(OUTPUT_DIR / "example")
    else:
        curses.wrapper(main)
