#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# LALALAAA — музыкальный плеер


import base64
import ctypes
import hashlib
import html as html_mod
import json
import math
import os
import random
import re
import sys
import tempfile
import time
import zlib
from collections import OrderedDict
from copy import deepcopy
from dataclasses import dataclass, field, asdict
from string import Template
from typing import List, Optional

from PySide6.QtCore import (Qt, QUrl, Signal, QTimer, QSize, QRect, QRectF,
                            QPointF, QEvent, QThread, QPoint, QLoggingCategory,
                            QPropertyAnimation, QEasingCurve, Property, QObject)
from PySide6.QtGui import (QColor, QBrush, QFont, QFontMetrics, QIcon,
                           QKeySequence, QLinearGradient, QPainter, QPen,
                           QPixmap, QShortcut, QImage, QPainterPath,
                           QRadialGradient, QCursor)
from PySide6.QtWidgets import (
    QApplication, QCheckBox, QDialog, QDialogButtonBox, QFileDialog, QFrame,
    QHBoxLayout, QHeaderView, QLabel, QLineEdit, QListWidget,
    QListWidgetItem, QMainWindow, QMenu, QMessageBox, QPlainTextEdit,
    QPushButton, QScrollArea, QSlider, QSplitter, QStyle, QStyleOptionSlider,
    QStyleOptionViewItem, QStyledItemDelegate, QTableWidget, QTableWidgetItem,
    QVBoxLayout, QWidget, QWidgetAction, QAbstractItemView, QSizePolicy,
    QAbstractButton, QAbstractSpinBox, QComboBox, QScrollBar, QSplitterHandle,
)

QLoggingCategory.setFilterRules("qt.gui.imageio=false\nqt.gui.imageio.*=false")

IS_WINDOWS = sys.platform.startswith("win")

WM_NCHITTEST = 0x0084
WM_GETMINMAXINFO = 0x0024
WM_SYSCOMMAND = 0x0112
WM_HOTKEY = 0x0312
WM_APPCOMMAND = 0x0319
WM_NCLBUTTONDOWN = 0x00A1
WM_NCLBUTTONDBLCLK = 0x00A3
WM_NCRBUTTONDOWN = 0x00A4
SC_MINIMIZE = 0xF020
SC_MAXIMIZE = 0xF030
SC_RESTORE = 0xF120
HTCLIENT, HTCAPTION = 1, 2
HTLEFT, HTRIGHT, HTTOP, HTBOTTOM = 10, 11, 12, 15
HTTOPLEFT, HTTOPRIGHT, HTBOTTOMLEFT, HTBOTTOMRIGHT = 13, 14, 16, 17

APPCMD_MEDIA_NEXT = 11
APPCMD_MEDIA_PREV = 12
APPCMD_MEDIA_STOP = 13
APPCMD_MEDIA_PLAY_PAUSE = 14

MOD_NOREPEAT = 0x4000
VK_MEDIA_NEXT_TRACK = 0xB0
VK_MEDIA_PREV_TRACK = 0xB1
VK_MEDIA_STOP = 0xB2
VK_MEDIA_PLAY_PAUSE = 0xB3
MEDIA_HOTKEYS = {
    0xA001: VK_MEDIA_PLAY_PAUSE,
    0xA002: VK_MEDIA_PREV_TRACK,
    0xA003: VK_MEDIA_NEXT_TRACK,
    0xA004: VK_MEDIA_STOP,
}

if IS_WINDOWS:
    from ctypes import wintypes

    class _POINT(ctypes.Structure):
        _fields_ = [("x", ctypes.c_long), ("y", ctypes.c_long)]

    class _MINMAXINFO(ctypes.Structure):
        _fields_ = [("ptReserved", _POINT), ("ptMaxSize", _POINT),
                    ("ptMaxPosition", _POINT), ("ptMinTrackSize", _POINT),
                    ("ptMaxTrackSize", _POINT)]

# --------------------------------------------------------------------------
# Безопасный импорт QtMultimedia
# --------------------------------------------------------------------------
HAS_MULTIMEDIA = False
MM_ERROR = ""
QAudioOutput = None
QMediaPlayer = None
COVER_ART_KEY = None

try:
    from PySide6.QtMultimedia import QAudioOutput, QMediaPlayer
    HAS_MULTIMEDIA = True
except Exception as e:
    MM_ERROR = f"{type(e).__name__}: {e}"
    print("[LALALAAA] QtMultimedia импорт ошибка:", MM_ERROR)

if HAS_MULTIMEDIA:
    try:
        from PySide6.QtMultimedia import QMediaMetadata
        try:
            COVER_ART_KEY = QMediaMetadata.Key.CoverArtImage
        except AttributeError:
            COVER_ART_KEY = getattr(QMediaMetadata, "CoverArtImage", None)
    except Exception:
        COVER_ART_KEY = None

try:
    from mutagen import File as MutagenFile
    HAS_MUTAGEN = True
except ImportError:
    HAS_MUTAGEN = False


# ==========================================================================
# Пути и конфиг
# ==========================================================================
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(BASE_DIR, "lalalaaa-setting.json")
COVERS_DIR = os.path.join(BASE_DIR, "lalalaaa-covers")
BACKDROP_PLACEHOLDER = os.path.join(BASE_DIR, "album-back-fon.png")
ICON_DIR_D = os.path.join(BASE_DIR, "lalalaaa-icon", "d-panel-lalalaaa")
ICON_DIR_U = os.path.join(BASE_DIR, "lalalaaa-icon", "u-panel-lalalaaa")
ICON_DIR_C = os.path.join(BASE_DIR, "lalalaaa-icon", "central-lalalaaa")

AUDIO_EXTS = {".mp3", ".flac", ".ogg", ".oga", ".wav", ".m4a",
              ".aac", ".wma", ".opus", ".ape", ".wv", ".mpc"}
IMG_EXTS = {".jpg", ".jpeg", ".png", ".webp", ".bmp", ".gif"}
FOLDER_COVERS = {"cover.jpg", "cover.png", "folder.jpg", "folder.png",
                 "front.jpg", "album.jpg", "album.png"}
COVER_NAME_KEYS = ("cover", "folder", "front", "album", "art", "scan", "облож")

BANNER_MIN_H = 220
BANNER_MAX_H = 760
BANNER_DEF_H = 300

DUR_GAP = "\u2002"
GREEN = "#20c950"
GREEN_HI = "#2ee365"
DOT_OFF = "#5b5b5b"
DANGER = "#e0483e"
DANGER_HI = "#f05a4f"
ZOOM_AMP = 0.08
ZOOM_PERIOD_MS = 12000.0

CAP_W, CAP_H, CAP_ICON = 34, 26, 16
SS = 4

SRC_ROW = 0
FREQ_ROW = 1
SEP_ROW = 2
USER_START = 3

FREQ_DESC = "Здесь будет появляться то, что ты часто слушаешь целиком и часто"

CONFIG_DEFAULTS = {
    "settings": {
        "volume": 50,
        "muted": False,
        "random": False,
        "rotate1": False,
        "dark_theme": False,
        "bg_zoom": False,
        "bg_pin": False,
        "follow_switch": True,
        "hide_banner": False,
        "no_cover_image": False,
        "classic_view": False,
        "banner_h": BANNER_DEF_H,
        "splitter": [260, 680],
        "window": [1150, 650],
        "maximized": False,
    },
    "source_path": "",
    "play_stats": {},
    "no_cover": [],
    "music_folders": [],
    "library": [],
    "playlists": [],
    "cfg_ver": 0,
}


class Config:
    def __init__(self, path: str):
        self.path = path
        self.data = deepcopy(CONFIG_DEFAULTS)
        if os.path.exists(path):
            try:
                with open(path, encoding="utf-8") as f:
                    loaded = json.load(f)
                self._merge(self.data, loaded)
            except Exception:
                pass
        if not self.data.get("source_path"):
            mf = self.data.get("music_folders") or []
            if mf:
                self.data["source_path"] = mf[0]
        if int(self.data.get("cfg_ver", 0)) < 2:
            self.data.setdefault("settings", {})["follow_switch"] = True
            self.data["cfg_ver"] = 2

    @staticmethod
    def _merge(base: dict, extra: dict):
        for k, v in extra.items():
            if isinstance(v, dict) and isinstance(base.get(k), dict):
                Config._merge(base[k], v)
            else:
                base[k] = v

    def save(self):
        try:
            with open(self.path, "w", encoding="utf-8") as f:
                json.dump(self.data, f, ensure_ascii=False, indent=2)
        except Exception as e:
            print("Не удалось сохранить конфиг:", e)

    @property
    def settings(self) -> dict:
        return self.data["settings"]


# ==========================================================================
# Темы
# ==========================================================================
THEME = {}


def set_theme(dark: bool):
    if dark:
        THEME.update({
            "dark": True,
            "window": "#080808", "panel": "#262626", "left": "#080808",
            "hover": "#303030", "pressed": "#3d3d3d", "checked_bg": "#3d3d3d",
            "text_main": "#ffffff", "text_sec": "#9a9a9a",
            "border": "#3d3d3d", "hline": "#262626",
            "selected": "#262626", "sel_text": "#ffffff", "sel_text_sec": "#b5b5b5",
            "accent": "#5b8dd6", "player": GREEN, "player_hi": GREEN_HI,
            "danger": DANGER, "danger_hi": DANGER_HI,
            "cover_ph": "#4a4a4a",
            "scroll_handle": "#3d3d3d", "scroll_hover": "#4a4a4a",
            "groove": "#262626",
            "header_fg": "#9a9a9a", "header_border": "#262626",
            "list_sel": "#262626",
            "menu_bg": "#262626", "menu_sel": "#3d3d3d",
            "input_bg": "#262626", "input_fg": "#ffffff",
            "search_bg": "#1a1a1a", "search_focus": "#101010",
            "pop_bg": "#141414", "pop_row": "#1f1f1f", "pop_border": "#4a4a4a",
            "btn_bg": "#262626", "btn_hover": "#303030",
            "time_fg": "#9a9a9a", "empty": "#7a7a7a",
            "disabled": "#8a8a8a",
            "icon_fg": "#ffffff", "note_fg": "#a8a8a8",
            "fade_r": 8, "fade_g": 8, "fade_b": 8,
            "chk_border": "#3d3d3d", "chk_mark": "#ffffff",
        })
    else:
        THEME.update({
            "dark": False,
            "window": "#f6f7f9", "panel": "#eef0f4", "left": "#f6f7f9",
            "hover": "#e2e5ea", "pressed": "#d3d7dd", "checked_bg": "#dce6f5",
            "text_main": "#1f2328", "text_sec": "#5f6368",
            "border": "#d0d3d8", "hline": "#d7dade",
            "selected": "#3f4348", "sel_text": "#ffffff", "sel_text_sec": "#c9cdd2",
            "accent": "#5b8dd6", "player": GREEN, "player_hi": GREEN_HI,
            "danger": DANGER, "danger_hi": DANGER_HI,
            "cover_ph": "#e3e6ea",
            "scroll_handle": "#c3c8cf", "scroll_hover": "#a9aeb6",
            "groove": "#d0d3d8",
            "header_fg": "#5f6368", "header_border": "#d0d3d8",
            "list_sel": "#cfd8e3",
            "menu_bg": "#ffffff", "menu_sel": "#e2e5ea",
            "input_bg": "#ffffff", "input_fg": "#1f2328",
            "search_bg": "#ffffff", "search_focus": "#ffffff",
            "pop_bg": "#ffffff", "pop_row": "#f1f3f7", "pop_border": "#c2c7cf",
            "btn_bg": "#e4e7ea", "btn_hover": "#d3d7dd",
            "time_fg": "#444444", "empty": "#8a8f98",
            "disabled": "#9a9a9a",
            "icon_fg": "#3a3f45", "note_fg": "#9aa0a6",
            "fade_r": 246, "fade_g": 247, "fade_b": 249,
            "chk_border": "#8a8f98", "chk_mark": "#1f2328",
        })


set_theme(False)

_CHK_CACHE = {}


def _make_check_icons(border_col: str, check_col: str):
    d = tempfile.mkdtemp(prefix="lalalaaa_chk_")

    def draw(checked):
        pm = QPixmap(32, 32)
        pm.fill(Qt.transparent)
        p = QPainter(pm)
        p.setRenderHint(QPainter.Antialiasing)
        pen = QPen(QColor(border_col))
        pen.setWidth(2)
        p.setPen(pen)
        p.drawRoundedRect(3, 3, 26, 26, 6, 6)
        if checked:
            pen2 = QPen(QColor(check_col))
            pen2.setWidth(4)
            p.setPen(pen2)
            p.drawLine(9, 17, 14, 22)
            p.drawLine(14, 22, 23, 10)
        p.end()
        return pm

    chk = os.path.join(d, "checked.png").replace("\\", "/")
    unchk = os.path.join(d, "unchecked.png").replace("\\", "/")
    draw(True).save(chk)
    draw(False).save(unchk)
    return chk, unchk


def check_icons(dark: bool):
    if dark not in _CHK_CACHE:
        if dark:
            _CHK_CACHE[dark] = _make_check_icons("#3d3d3d", "#ffffff")
        else:
            _CHK_CACHE[dark] = _make_check_icons("#8a8f98", "#1f2328")
    return _CHK_CACHE[dark]


_SS_TEMPLATE = Template("""
QWidget#centralWidget { background: $window; }
QWidget#topBar, QWidget#playerBar { background: $panel; }
QWidget#leftPanel { background: $left; }
QWidget#nowPanel { background: $left; }

QPushButton[flat="true"] {
    border: none; background: transparent; color: $text_main;
    border-radius: 6px; padding: 5px; font-size: 14px;
}
QPushButton[flat="true"]:hover    { background: $hover; }
QPushButton[flat="true"]:pressed  { background: transparent; }
QPushButton[flat="true"]:checked  { background: $checked_bg; }
QPushButton::menu-indicator { image: none; width: 0; }

QPushButton[caption="true"] {
    border: none; background: transparent; border-radius: 5px; padding: 0px;
    margin: 0px;
}
QPushButton[caption="true"]:hover   { background: $hover; }
QPushButton[caption="true"]:pressed { background: $pressed; }
QPushButton[caption="true"]:checked { background: $checked_bg; }
QPushButton[caption="true"]:disabled { background: transparent; }
QPushButton#capClose:hover   { background: $danger; }
QPushButton#capClose:pressed { background: $danger; }

QSplitter::handle:horizontal       { background: $border; width: 2px; }
QSplitter::handle:horizontal:hover { background: $player; }

QListWidget { border: none; background: transparent; color: $text_main;
              font-size: 14px; outline: none; }
QListWidget::item { padding: 6px; border-radius: 6px; }

QScrollArea { background: transparent; border: none; }

QTableWidget {
    background: transparent; border: none; color: $text_main;
    font-size: 14px; gridline-color: transparent;
}
QTableWidget::item { padding: 2px; }
QTableWidget::item:selected { background: $selected; color: $sel_text; }
QHeaderView::section {
    background: transparent; border: none;
    border-bottom: 1px solid $header_border; padding: 6px;
    font-size: 11px; font-weight: 600; color: $header_fg;
}
QTableCornerButton::section { background: transparent; border: none; }

QSlider::groove:horizontal { height: 4px; background: $groove; border-radius: 2px; }
QSlider::sub-page:horizontal { background: $player; border-radius: 2px; }
QSlider::handle:horizontal {
    width: 12px; height: 12px; margin: -4px 0;
    border-radius: 6px; background: $player;
}

QScrollBar:vertical { background: transparent; width: 8px; margin: 0; }
QScrollBar::handle:vertical { background: $scroll_handle; border-radius: 4px; min-height: 24px; }
QScrollBar::handle:vertical:hover { background: $scroll_hover; }
QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height: 0; width: 0; }
QScrollBar::add-page:vertical, QScrollBar::sub-page:vertical { background: transparent; }
QScrollBar:horizontal { background: transparent; height: 8px; margin: 0; }
QScrollBar::handle:horizontal { background: $scroll_handle; border-radius: 4px; min-width: 24px; }
QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal { width: 0; height: 0; }

QLineEdit#searchBox {
    border: none; border-radius: 6px;
    background: rgba(255,255,255,0.10);
    color: #ffffff; padding: 5px 10px; font-size: 13px;
    selection-background-color: $player;
}
QLineEdit#searchBox:focus { background: rgba(8,8,8,0.46); }

QLineEdit#topSearch {
    border: 1px solid $border; border-radius: 7px;
    background: $search_bg; color: $text_main;
    padding: 3px 10px 3px 10px; font-size: 13px;
    selection-background-color: $player;
}
QLineEdit#topSearch:focus { border: 1px solid $player; background: $search_focus; }

QListWidget#searchPopList { background: transparent; border: none; outline: none; }
QListWidget#searchPopList::item { border: none; padding: 0px; background: transparent; }
QLabel#popHead { color: $text_sec; background: transparent; }

QLabel#timeLabel { font-family: monospace; color: $time_fg; }
QLabel#coverPreview {
    background: $cover_ph; border: 1px solid $border; border-radius: 8px;
    color: $text_sec;
}

QMenu { background: $menu_bg; color: $text_main; border: 1px solid $border; padding: 4px; }
QMenu::item { padding: 6px 24px 6px 12px; border-radius: 4px; }
QMenu::item:selected { background: $menu_sel; }
QMenu::indicator { width: 16px; height: 16px; margin-left: 6px; }
QMenu::indicator:checked { image: url(@CHK@); }
QMenu::indicator:unchecked { image: url(@UNCHK@); }

QCheckBox { spacing: 8px; background: transparent; color: $text_main; }
QCheckBox::indicator { width: 16px; height: 16px; }
QCheckBox::indicator:checked { image: url(@CHK@); }
QCheckBox::indicator:unchecked { image: url(@UNCHK@); }
QCheckBox:disabled { color: $disabled; }

QDialog { background: $window; color: $text_main; }
QDialog#settingsDlg { border: 1px solid $border; }
QWidget#dlgHeader { background: $panel; }
QLabel { color: $text_main; }
QLineEdit, QPlainTextEdit {
    background: $input_bg; color: $input_fg;
    border: 1px solid $border; border-radius: 6px; padding: 6px 8px;
    selection-background-color: $player;
}
QLineEdit:focus, QPlainTextEdit:focus { border: 1px solid $player; }
QPushButton {
    background: $btn_bg; color: $text_main; border: 1px solid $border;
    border-radius: 6px; padding: 7px 16px;
}
QPushButton:hover { background: $btn_hover; }
QPushButton:pressed { background: $pressed; }
QPushButton:disabled { color: $disabled; }

QPushButton#primaryBtn {
    background: $player; color: #06210f; border: none;
    font-weight: 700; padding: 8px 20px; border-radius: 6px;
}
QPushButton#primaryBtn:hover { background: $player_hi; }
QPushButton#primaryBtn:pressed { background: $player; }
QPushButton#dangerBtn {
    background: $danger; color: #ffffff; border: none;
    font-weight: 700; padding: 8px 20px; border-radius: 6px;
}
QPushButton#dangerBtn:hover { background: $danger_hi; }
QPushButton#dangerBtn:pressed { background: $danger; }
""")


def build_stylesheet() -> str:
    ss = _SS_TEMPLATE.substitute(THEME)
    chk, unchk = check_icons(bool(THEME.get("dark", False)))
    return ss.replace("@CHK@", chk).replace("@UNCHK@", unchk)


def title_css() -> str:
    return f"color: {THEME['text_main']}; font-size: 14px; background: transparent;"


def title_play_css() -> str:
    return (f"color: {THEME['player']}; font-size: 14px; font-weight: 600;"
            " background: transparent;")


def artist_css() -> str:
    return f"color: {THEME['text_sec']}; font-size: 11px; background: transparent;"


def cover_css() -> str:
    return f"background: {THEME['cover_ph']}; border-radius: 4px;"


def soft_wrap(text: str, chunk: int = 18) -> str:
    out = []
    for word in (text or "").split(" "):
        if len(word) > chunk:
            parts = [word[i:i + chunk] for i in range(0, len(word), chunk)]
            out.append("\u200b".join(parts))
        else:
            out.append(word)
    return " ".join(out)


def _year_of(s: str) -> str:
    m = re.search(r"(19|20)\d{2}", s or "")
    return m.group(0) if m else ""


def is_interactive_widget(w) -> bool:
    while w is not None:
        if isinstance(w, (QAbstractButton, QSlider, QLineEdit, QPlainTextEdit,
                          QAbstractItemView, QScrollBar, QComboBox,
                          QAbstractSpinBox, QSplitterHandle, QCheckBox)):
            return True
        w = w.parentWidget()
    return False


# ==========================================================================
# Модель данных
# ==========================================================================
@dataclass
class Track:
    title: str = ""
    path: str = ""
    artist: str = ""
    album: str = ""
    year: str = ""
    cover: str = ""
    duration_ms: int = 0
    date_added: float = 0.0


@dataclass
class Playlist:
    name: str = ""
    description: str = ""
    cover: str = ""
    tracks: List[Track] = field(default_factory=list)


class Library:
    def __init__(self) -> None:
        self.tracks: List[Track] = []
        self.playlists: List[Playlist] = []

    def to_dict(self) -> dict:
        return {
            "library": [asdict(t) for t in self.tracks],
            "playlists": [
                {"name": p.name, "description": p.description,
                 "cover": p.cover, "tracks": [t.path for t in p.tracks]}
                for p in self.playlists],
        }

    def load_from_dict(self, data: dict):
        defaults = asdict(Track())
        self.tracks = [Track(**{k: d.get(k, v) for k, v in defaults.items()})
                       for d in data.get("library", []) if isinstance(d, dict)]
        by_path = {t.path: t for t in self.tracks}
        self.playlists = []
        for pd in data.get("playlists", []):
            if not isinstance(pd, dict):
                continue
            pl = Playlist(pd.get("name", ""), pd.get("description", ""),
                          pd.get("cover", ""))
            pl.tracks = [by_path[p] for p in pd.get("tracks", []) if p in by_path]
            self.playlists.append(pl)


def format_time(ms: int) -> str:
    s = max(0, int(ms)) // 1000
    return f"{s // 60}:{s % 60:02d}"


def plural(n: int, one: str, few: str, many: str) -> str:
    n10, n100 = n % 10, n % 100
    if n10 == 1 and n100 != 11:
        return one
    if 2 <= n10 <= 4 and not (12 <= n100 <= 14):
        return few
    return many


def total_duration_text(tracks: List[Track]) -> str:
    total = sum(t.duration_ms for t in tracks) // 1000
    h, m = total // 3600, (total % 3600) // 60
    if h:
        return f"{h} ч {m} мин"
    return f"{m} мин"


# ==========================================================================
# Теги
# ==========================================================================
def _tag_value(v) -> str:
    if v is None:
        return ""
    if isinstance(v, (list, tuple)):
        if not v:
            return ""
        v = v[0]
        if v is None:
            return ""
    if isinstance(v, (bytes, bytearray)):
        try:
            return v.decode("utf-8", "ignore").strip()
        except Exception:
            return ""
    try:
        s = str(v).strip()
    except Exception:
        return ""
    if not s or s.lower() == "none":
        return ""
    return s


def _read_tags(path: str) -> dict:
    out = {}
    if not HAS_MUTAGEN:
        return out
    try:
        m = MutagenFile(path, easy=True)
        if m is not None:
            if getattr(m, "info", None) and getattr(m.info, "length", 0):
                out["duration_ms"] = int(m.info.length * 1000)
            tags = m.tags or {}
            for key, names in (("title", ("title",)),
                               ("artist", ("artist",)),
                               ("album", ("album",)),
                               ("year", ("date", "year"))):
                for n in names:
                    s = _tag_value(tags.get(n))
                    if s:
                        out[key] = s
                        break
        missing = (not out.get("title")) or (not out.get("artist")) \
            or (not out.get("album")) or (not out.get("duration_ms")) \
            or (not out.get("year"))
        if missing:
            m2 = MutagenFile(path)
            if m2 is not None:
                if not out.get("duration_ms") and getattr(m2, "info", None) \
                        and getattr(m2.info, "length", 0):
                    out["duration_ms"] = int(m2.info.length * 1000)
                t2 = m2.tags or {}
                raw_map = (
                    ("title", ("TIT2", "\xa9nam", "TITLE", "WM/Title")),
                    ("artist", ("TPE1", "\xa9ART", "ARTIST", "WM/Artist")),
                    ("album", ("TALB", "\xa9alb", "ALBUM", "WM/AlbumTitle")),
                    ("year", ("TDRC", "TYER", "\xa9day", "DATE", "YEAR",
                              "WM/Year")),
                )
                for key, names in raw_map:
                    if out.get(key):
                        continue
                    for n in names:
                        if n in t2:
                            s = _tag_value(t2[n])
                            if s:
                                out[key] = s
                                break
        if out.get("year"):
            out["year"] = _year_of(out["year"])
    except Exception:
        pass
    return out


# ==========================================================================
# Валидация картинки
# ==========================================================================
def _jpeg_ok(b: bytes) -> bool:
    n = len(b)
    if n < 128 or b[:2] != b'\xff\xd8':
        return False
    i = 2
    seen_sof = False
    while i + 2 <= n:
        if b[i] != 0xFF:
            return False
        j = i + 1
        while j < n and b[j] == 0xFF:
            j += 1
        if j >= n:
            return False
        m = b[j]
        i = j + 1
        if m == 0xD9:
            return seen_sof
        if m == 0x01 or 0xD0 <= m <= 0xD7:
            continue
        if i + 2 > n:
            return False
        ln = int.from_bytes(b[i:i + 2], "big")
        if ln < 2 or i + ln > n:
            return False
        if m in (0xC0, 0xC1, 0xC2):
            seen_sof = True
        elif m in (0xC3, 0xC5, 0xC6, 0xC7, 0xC9, 0xCA, 0xCB, 0xCD, 0xCE, 0xCF):
            return False
        elif m == 0xDA:
            if not seen_sof:
                return False
            return b.find(b'\xff\xd9', i + ln) > 0
        i += ln
    return False


def _looks_like_image(b: bytes) -> bool:
    if not b or len(b) < 64:
        return False
    if b[:8] == b'\x89PNG\r\n\x1a\n':
        return b[12:16] == b'IHDR' and b.find(b'IEND') > 0
    if b[:2] == b'\xff\xd8':
        return _jpeg_ok(b)
    if b[:4] == b'RIFF' and b[8:12] == b'WEBP':
        return True
    if b[:2] == b'BM':
        return len(b) > 128
    if b[:6] in (b'GIF87a', b'GIF89a'):
        return True
    if b[4:8] == b'ftyp' and any(x in b[8:20] for x in
                                 (b'avif', b'avis', b'heic', b'heix', b'mif1')):
        return True
    if b[:2] == b'\xff\x0a' or b[:12] == b'\x00\x00\x00\x0cJXL \r\n\x87\n':
        return True
    if b[:4] in (b'II*\x00', b'MM\x00*'):
        return True
    return False


# ==========================================================================
# Обложки: кэши + mutagen + нативные парсеры
# ==========================================================================
_PM_CACHE: "OrderedDict[tuple, QPixmap]" = OrderedDict()
_PM_CACHE_MAX = 400
_RAW_CACHE: "OrderedDict[str, QPixmap]" = OrderedDict()
_RAW_CACHE_MAX = 6
_DOM_CACHE: "OrderedDict[str, tuple]" = OrderedDict()
_DOM_CACHE_MAX = 64
_BAD_PIX = set()
_BAD_DATA = set()


def _read_bytes(path: str, limit: int = 0) -> bytes:
    try:
        with open(path, "rb") as f:
            return f.read(limit) if limit and limit > 0 else f.read()
    except Exception:
        return b""


def load_pixmap(path: str, size: int):
    if not path:
        return None
    key = (path, size)
    pm = _PM_CACHE.get(key)
    if pm is not None:
        _PM_CACHE.move_to_end(key)
        return pm
    if path in _BAD_PIX:
        return None
    try:
        if not os.path.exists(path):
            _BAD_PIX.add(path)
            return None
        data = _read_bytes(path)
        if not _looks_like_image(data):
            _BAD_PIX.add(path)
            return None
        pm = QPixmap()
        if not pm.loadFromData(data) or pm.isNull():
            _BAD_PIX.add(path)
            return None
        pm = pm.scaled(size, size, Qt.KeepAspectRatio, Qt.SmoothTransformation)
        if pm.isNull():
            _BAD_PIX.add(path)
            return None
    except Exception:
        _BAD_PIX.add(path)
        return None
    _PM_CACHE[key] = pm
    _PM_CACHE.move_to_end(key)
    while len(_PM_CACHE) > _PM_CACHE_MAX:
        _PM_CACHE.popitem(last=False)
    return pm


def load_pixmap_raw(path: str):
    if not path:
        return None
    pm = _RAW_CACHE.get(path)
    if pm is not None:
        _RAW_CACHE.move_to_end(path)
        return pm
    if path in _BAD_PIX:
        return None
    try:
        if not os.path.exists(path):
            _BAD_PIX.add(path)
            return None
        data = _read_bytes(path)
        if not _looks_like_image(data):
            _BAD_PIX.add(path)
            return None
        pm = QPixmap()
        if not pm.loadFromData(data) or pm.isNull():
            _BAD_PIX.add(path)
            return None
    except Exception:
        _BAD_PIX.add(path)
        return None
    _RAW_CACHE[path] = pm
    _RAW_CACHE.move_to_end(path)
    while len(_RAW_CACHE) > _RAW_CACHE_MAX:
        _RAW_CACHE.popitem(last=False)
    return pm


def dominant_rgb(path: str):
    if not path:
        return None
    hit = _DOM_CACHE.get(path)
    if hit is not None:
        _DOM_CACHE.move_to_end(path)
        return hit
    pm = load_pixmap_raw(path)
    if pm is None or pm.isNull():
        return None
    try:
        img = pm.toImage().scaled(28, 28, Qt.IgnoreAspectRatio,
                                  Qt.SmoothTransformation)
        img = img.convertToFormat(QImage.Format_RGBA8888)
        bins = {}
        for y in range(img.height()):
            for x in range(img.width()):
                c = img.pixelColor(x, y)
                if c.alpha() < 128:
                    continue
                key = (c.red() // 24, c.green() // 24, c.blue() // 24)
                e = bins.get(key)
                if e is None:
                    e = [0, 0, 0, 0]
                    bins[key] = e
                e[0] += 1
                e[1] += c.red()
                e[2] += c.green()
                e[3] += c.blue()
        if not bins:
            return None
        best = max(bins.values(), key=lambda e: e[0])
        n = max(1, best[0])
        rgb = (best[1] // n, best[2] // n, best[3] // n)
    except Exception:
        return None
    _DOM_CACHE[path] = rgb
    _DOM_CACHE.move_to_end(path)
    while len(_DOM_CACHE) > _DOM_CACHE_MAX:
        _DOM_CACHE.popitem(last=False)
    return rgb


def muted_backdrop(rgb):
    if rgb is None:
        return None
    col = QColor(rgb[0], rgb[1], rgb[2])
    h, s, v, _a = col.getHsvF()
    if h < 0:
        h = 0.0
    s = max(0.10, min(0.46, s * 0.62))
    v = 0.20 + 0.15 * v
    return QColor.fromHsvF(h, s, max(0.0, min(1.0, v)))


def _syncsafe(b):
    return ((b[0] & 0x7F) << 21) | ((b[1] & 0x7F) << 14) | \
           ((b[2] & 0x7F) << 7) | (b[3] & 0x7F)


def _img_ext_magic(b):
    if b[:3] == b'\xff\xd8\xff':
        return '.jpg'
    if b[:8] == b'\x89PNG\r\n\x1a\n':
        return '.png'
    if b[:4] == b'RIFF' and b[8:12] == b'WEBP':
        return '.webp'
    if b[:2] == b'BM':
        return '.bmp'
    if b[:4] == b'GIF8':
        return '.gif'
    return '.img'


def _save_cover_bytes(data, path):
    if not data:
        return ""
    data = bytes(data)
    if len(data) < 128 or len(data) > 25 * 1024 * 1024:
        return ""
    if not _looks_like_image(data):
        return ""
    h = hashlib.md5(data).hexdigest()
    if h in _BAD_DATA:
        return ""
    try:
        img = QImage.fromData(data)
        if img.isNull():
            try:
                import io
                from PIL import Image
                im = Image.open(io.BytesIO(data))
                im.load()
                if im.mode not in ("RGB", "RGBA"):
                    im = im.convert("RGB")
                buf = io.BytesIO()
                im.save(buf, "PNG")
                data = buf.getvalue()
                img = QImage.fromData(data)
            except Exception:
                img = QImage()
        if img.isNull() or img.width() < 16 or img.height() < 16:
            _BAD_DATA.add(h)
            return ""
        os.makedirs(COVERS_DIR, exist_ok=True)
        cp = os.path.join(COVERS_DIR,
                          hashlib.md5(path.encode()).hexdigest()[:12]
                          + _img_ext_magic(data[:12]))
        if not os.path.exists(cp):
            with open(cp, "wb") as f:
                f.write(data)
        return cp
    except Exception:
        _BAD_DATA.add(h)
        return ""


def _mutagen_cover(path: str) -> str:
    if not HAS_MUTAGEN:
        return ""
    try:
        m = MutagenFile(path)
        data = None
        tags = getattr(m, "tags", None)
        if tags is not None and hasattr(tags, "getall"):
            apics = tags.getall("APIC:")
            if apics:
                data = apics[0].data
        if data is None and tags is not None and "covr" in tags:
            data = bytes(tags["covr"][0])
        if data is None and getattr(m, "pictures", None):
            data = m.pictures[0].data
        if data:
            return _save_cover_bytes(data, path)
    except Exception:
        pass
    return ""


def _apic_payload(frame: bytes):
    if len(frame) < 4:
        return None
    enc = frame[0]
    j = frame.find(b'\x00', 1)
    if j < 0:
        return None
    mime = frame[1:j].decode("latin-1", "ignore").strip().lower()
    if mime in ("-->", "--->", "text/plain"):
        return None
    k = j + 2
    if enc in (0, 3):
        e = frame.find(b'\x00', k)
        if e < 0:
            return None
        k = e + 1
    else:
        e = frame.find(b'\x00\x00', k)
        if e < 0:
            return None
        k = e + 2
    data = frame[k:]
    return data if _looks_like_image(data) else None


def _id3_cover(body, ver, flags):
    i = 0
    ext_flag = 0x40 if ver == 4 else 0x20
    if (flags & ext_flag) and len(body) >= 4:
        esz = _syncsafe(body[0:4]) if ver == 4 else int.from_bytes(body[0:4], "big")
        i = 4 + esz
    if ver == 2:
        while i + 6 <= len(body):
            fid = body[i:i + 3]
            fsz = int.from_bytes(body[i + 3:i + 6], "big")
            if fsz <= 0:
                break
            frame = body[i + 6:i + 6 + fsz]
            if fid == b'PIC' and len(frame) > 6:
                enc = frame[0]
                term = b'\x00' if enc in (0, 3) else b'\x00\x00'
                e = frame.find(term, 5)
                if e >= 0:
                    data = frame[e + len(term):]
                    if _looks_like_image(data):
                        return data
            i += 6 + fsz
        return None
    while i + 10 <= len(body):
        fid = body[i:i + 4]
        if fid == b'\x00\x00\x00\x00':
            break
        fsz = _syncsafe(body[i + 4:i + 8]) if ver == 4 else \
            int.from_bytes(body[i + 4:i + 8], "big")
        if fsz <= 0:
            break
        fflags = int.from_bytes(body[i + 8:i + 10], "big")
        frame = body[i + 10:i + 10 + fsz]
        ok = True
        if ver == 3:
            if fflags & 0x0040:
                ok = False
            elif fflags & 0x0080:
                try:
                    frame = zlib.decompress(frame[4:])
                except Exception:
                    ok = False
            if ok and (fflags & 0x0020):
                frame = frame[1:]
        else:
            if fflags & 0x0004:
                ok = False
            else:
                if fflags & 0x0040:
                    frame = frame[1:]
                if fflags & 0x0008:
                    try:
                        frame = zlib.decompress(frame[4:])
                    except Exception:
                        ok = False
                if ok and (fflags & 0x0002):
                    frame = frame.replace(b'\xff\x00', b'\xff')
                if ok and (fflags & 0x0001):
                    frame = frame[4:]
        if ok and fid == b'APIC':
            data = _apic_payload(frame)
            if data:
                return data
        i += 10 + fsz
    return None


def _flac_picture(block):
    o = 4
    if len(block) < o + 4:
        return None
    ml = int.from_bytes(block[o:o + 4], "big"); o += 4 + ml
    if len(block) < o + 4:
        return None
    dl = int.from_bytes(block[o:o + 4], "big"); o += 4 + dl
    o += 16
    if len(block) < o + 4:
        return None
    ll = int.from_bytes(block[o:o + 4], "big"); o += 4
    return block[o:o + ll]


def _flac_cover(data):
    i = 4
    n = len(data)
    while i + 4 <= n:
        hdr = data[i]
        last = hdr & 0x80
        btype = hdr & 0x7F
        ml = int.from_bytes(data[i + 1:i + 4], "big")
        if ml <= 0:
            break
        if btype == 6:
            return _flac_picture(data[i + 4:i + 4 + ml])
        i += 4 + ml
        if last:
            break
    return None


def _ogg_cover(data):
    key = b'METADATA_BLOCK_PICTURE='
    p = data.find(key)
    if p < 0:
        return None
    p += len(key)
    ok = set(b'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=')
    j = p
    while j < len(data) and data[j] in ok:
        j += 1
    try:
        block = base64.b64decode(data[p:j])
    except Exception:
        return None
    return _flac_picture(block)


def _mp4_find(buf, name, start, end):
    i = start
    while i + 8 <= end:
        sz = int.from_bytes(buf[i:i + 4], "big")
        typ = buf[i + 4:i + 8]
        hdr = 8
        if sz == 1:
            if i + 16 > end:
                return None
            sz = int.from_bytes(buf[i + 8:i + 16], "big")
            hdr = 16
        elif sz == 0:
            sz = end - i
        if sz < hdr:
            return None
        if typ == name:
            return i, sz, hdr
        i += sz
    return None


def _mp4_cover(data):
    m = _mp4_find(data, b'moov', 0, len(data))
    if not m:
        return None
    o, s, h = m
    u = _mp4_find(data, b'udta', o + h, o + s)
    if not u:
        return None
    o, s, h = u
    me = _mp4_find(data, b'meta', o + h, o + s)
    if not me:
        return None
    o, s, h = me
    il = _mp4_find(data, b'ilst', o + h + 4, o + s)
    if not il:
        return None
    o, s, h = il
    c = _mp4_find(data, b'covr', o + h, o + s)
    if not c:
        return None
    o, s, h = c
    d = _mp4_find(data, b'data', o + h, o + s)
    if not d:
        return None
    o, s, h = d
    return data[o + h + 8:o + s]


_ASF_HEADER = bytes.fromhex("3026b2758e66cf11a6d900aa0062ce6c")
_ASF_EXT_DESC = bytes.fromhex("40a4d0d207e3d21197f000a0c95ea850")


def _wm_picture(val: bytes):
    if len(val) < 5:
        return None
    dl = int.from_bytes(val[1:5], "little")
    o = 5
    for _ in range(2):
        e = val.find(b'\x00\x00', o)
        while e >= 0 and (e - o) % 2:
            e = val.find(b'\x00\x00', e + 1)
        if e < 0:
            return None
        o = e + 2
    data = val[o:o + dl] if dl else val[o:]
    return data or None


def _asf_ext_desc(body: bytes):
    if len(body) < 2:
        return None
    cnt = int.from_bytes(body[0:2], "little")
    o = 2
    for _ in range(cnt):
        if o + 2 > len(body):
            return None
        nl = int.from_bytes(body[o:o + 2], "little"); o += 2
        name = body[o:o + nl].decode("utf-16-le", "ignore").rstrip("\x00")
        o += nl
        if o + 4 > len(body):
            return None
        vt = int.from_bytes(body[o:o + 2], "little"); o += 2
        vl = int.from_bytes(body[o:o + 2], "little"); o += 2
        val = body[o:o + vl]; o += vl
        if name.strip().lower() == "wm/picture" and vt == 0:
            pic = _wm_picture(val)
            if pic:
                return pic
    return None


def _asf_cover(data: bytes):
    if data[:16] != _ASF_HEADER or len(data) < 30:
        return None
    hs = int.from_bytes(data[16:24], "little")
    cnt = int.from_bytes(data[24:28], "little")
    end = min(len(data), hs if hs else len(data))
    i = 30
    for _ in range(max(0, cnt)):
        if i + 24 > end:
            break
        guid = data[i:i + 16]
        sz = int.from_bytes(data[i + 16:i + 24], "little")
        if sz < 24:
            break
        if guid == _ASF_EXT_DESC:
            got = _asf_ext_desc(data[i + 24:i + sz])
            if got:
                return got
        i += sz
    return None


def _ape_cover(data: bytes):
    positions = []
    tail = data.rfind(b'APETAGEX', max(0, len(data) - 131072))
    if tail >= 0:
        positions.append(tail)
    head = data.find(b'APETAGEX', 0, 131072)
    if head >= 0:
        positions.append(head)
    for pos in positions:
        hdr = data[pos:pos + 32]
        if len(hdr) < 32:
            continue
        size = int.from_bytes(hdr[12:16], "little")
        count = int.from_bytes(hdr[16:20], "little")
        flags = int.from_bytes(hdr[20:24], "little")
        is_header = bool(flags & 0x80000000)
        start = pos + 32 if is_header else pos - (size - 32)
        if start < 0 or count <= 0 or count > 4096:
            continue
        o = start
        for _ in range(count):
            if o + 8 > len(data):
                break
            vs = int.from_bytes(data[o:o + 4], "little"); o += 4
            o += 4
            e = data.find(b'\x00', o)
            if e < 0 or e - o > 256:
                break
            key = data[o:e].decode("ascii", "ignore").lower(); o = e + 1
            if vs <= 0 or o + vs > len(data):
                break
            val = data[o:o + vs]; o += vs
            if "cover art" in key:
                z = val.find(b'\x00')
                img = val[z + 1:] if z >= 0 else val
                if _looks_like_image(img):
                    return img
    return None


def _native_cover_bytes(data):
    if not data:
        return None
    try:
        if data[:3] == b'ID3' and len(data) >= 10:
            sz = _syncsafe(data[6:10])
            flags = data[5]
            body = data[10:10 + sz]
            if data[3] == 3 and (flags & 0x80):
                body = body.replace(b'\xff\x00', b'\xff')
            return _id3_cover(body, data[3], flags)
        if data[:4] == b'fLaC':
            return _flac_cover(data)
        if data[:4] == b'OggS':
            return _ogg_cover(data)
        if len(data) > 8 and data[4:8] == b'ftyp':
            return _mp4_cover(data)
        if data[:16] == _ASF_HEADER:
            return _asf_cover(data)
        return _ape_cover(data)
    except Exception:
        return None


def _embedded_cover(path: str) -> str:
    cp = _mutagen_cover(path)
    if cp:
        return cp
    try:
        total = os.path.getsize(path)
    except OSError:
        return ""
    if total <= 0:
        return ""
    head = _read_bytes(path, 64 * 1024)
    if not head:
        return ""
    try:
        if head[:3] == b'ID3' and len(head) >= 10:
            tsz = _syncsafe(head[6:10])
            data = _read_bytes(path, 10 + tsz + 64)
        elif head[:4] in (b'fLaC', b'OggS'):
            data = _read_bytes(path, min(total, 4 * 1024 * 1024))
        elif len(head) > 8 and head[4:8] == b'ftyp':
            if total > 150 * 1024 * 1024:
                return ""
            data = _read_bytes(path)
        elif head[:16] == _ASF_HEADER:
            hs = int.from_bytes(head[16:24], "little") if len(head) >= 24 else 0
            data = _read_bytes(path, min(total, max(65536, min(hs, 8 * 1024 * 1024))))
        else:
            tail = _read_bytes(path, 0)[-131072:] if total > 131072 else b""
            data = head + tail
    except Exception:
        return ""
    b = _native_cover_bytes(data)
    if not b:
        return ""
    return _save_cover_bytes(b, path)


def _folder_cover(directory: str) -> str:
    try:
        names = [n for n in os.listdir(directory)
                 if os.path.splitext(n)[1].lower() in IMG_EXTS]
    except Exception:
        return ""
    if not names:
        return ""
    for n in names:
        if n.lower() in FOLDER_COVERS:
            return os.path.join(directory, n)
    for n in names:
        if any(k in n.lower() for k in COVER_NAME_KEYS):
            return os.path.join(directory, n)
    if len(names) == 1:
        return os.path.join(directory, names[0])
    return ""


def _cover_usable(path: str) -> bool:
    return bool(path) and os.path.exists(path)


def scan_folder(root_path: str, existing: set) -> List[Track]:
    found = []
    for root, _dirs, files in os.walk(root_path):
        fcover = _folder_cover(root)
        for name in files:
            ext = os.path.splitext(name)[1].lower()
            if ext not in AUDIO_EXTS:
                continue
            path = os.path.join(root, name)
            if path in existing:
                continue
            tags = _read_tags(path)
            cover = fcover
            if not cover and HAS_MUTAGEN:
                cover = _mutagen_cover(path)
            found.append(Track(
                title=tags.get("title") or os.path.splitext(name)[0],
                path=path,
                artist=tags.get("artist", ""),
                album=tags.get("album", ""),
                year=tags.get("year", ""),
                cover=cover,
                duration_ms=tags.get("duration_ms", 0),
                date_added=time.time(),
            ))
    return found


class TagRefreshThread(QThread):
    finished_results = Signal(list)

    def __init__(self, jobs: List[tuple], parent=None):
        super().__init__(parent)
        self._jobs = jobs

    def run(self):
        res = []
        for path, need_tags, need_cover in self._jobs:
            try:
                tags = _read_tags(path) if need_tags else {}
            except Exception:
                tags = {}
            cover = ""
            if need_cover:
                try:
                    cover = (_folder_cover(os.path.dirname(path))
                             or _embedded_cover(path))
                except Exception:
                    cover = ""
            res.append((path, tags, cover))
        self.finished_results.emit(res)


# ==========================================================================
# Иконки
# ==========================================================================
def custom_icon(name: str, panel: str = "d") -> Optional[QIcon]:
    base = {"d": ICON_DIR_D, "u": ICON_DIR_U, "c": ICON_DIR_C}.get(panel, ICON_DIR_D)
    path = os.path.join(base, name + ".svg")
    if os.path.exists(path):
        try:
            ic = QIcon(path)
            if not ic.isNull():
                return ic
        except Exception:
            pass
    return None


def tint_icon(icon: QIcon, color: str, size: int) -> QIcon:
    try:
        pm = icon.pixmap(size, size)
        if pm.isNull():
            return icon
        img = pm.toImage()
        p = QPainter(img)
        p.setCompositionMode(QPainter.CompositionMode_SourceIn)
        p.fillRect(img.rect(), QColor(color))
        p.end()
        return QIcon(QPixmap.fromImage(img))
    except Exception:
        return icon


def crisp_icon(icon: QIcon, color: Optional[str], size: int) -> QIcon:
    try:
        pm = icon.pixmap(size * SS, size * SS)
        if pm.isNull():
            return icon
        if color:
            img = pm.toImage()
            p = QPainter(img)
            p.setCompositionMode(QPainter.CompositionMode_SourceIn)
            p.fillRect(img.rect(), QColor(color))
            p.end()
            pm = QPixmap.fromImage(img)
        pm = pm.scaled(size, size, Qt.KeepAspectRatio, Qt.SmoothTransformation)
        return QIcon(pm)
    except Exception:
        return icon


def _arrow(p, x, y, dx, dy, s):
    L = 0.16 * s
    ang = math.atan2(dy, dx)
    for da in (math.radians(150), -math.radians(150)):
        p.drawLine(QPointF(x, y),
                   QPointF(x + L * math.cos(ang + da), y + L * math.sin(ang + da)))


def d_shuffle(p, s, col):
    p.drawLine(QPointF(.15 * s, .72 * s), QPointF(.80 * s, .30 * s))
    _arrow(p, .84 * s, .28 * s, 1, -.64, s)
    p.drawLine(QPointF(.15 * s, .28 * s), QPointF(.42 * s, .46 * s))
    p.drawLine(QPointF(.58 * s, .54 * s), QPointF(.80 * s, .70 * s))
    _arrow(p, .84 * s, .72 * s, 1, .64, s)


def d_repeat_one(p, s, col):
    p.drawLine(QPointF(.24 * s, .40 * s), QPointF(.70 * s, .40 * s))
    _arrow(p, .76 * s, .40 * s, 1, 0, s)
    p.drawLine(QPointF(.76 * s, .40 * s), QPointF(.76 * s, .60 * s))
    p.drawLine(QPointF(.76 * s, .60 * s), QPointF(.30 * s, .60 * s))
    _arrow(p, .24 * s, .60 * s, -1, 0, s)
    p.drawLine(QPointF(.24 * s, .60 * s), QPointF(.24 * s, .40 * s))
    p.setPen(Qt.NoPen); p.setBrush(col)
    p.drawEllipse(QPointF(.5 * s, .5 * s), .07 * s, .07 * s)


def d_note(p, s, col):
    p.setPen(col)
    f = p.font()
    f.setPixelSize(int(.62 * s))
    p.setFont(f)
    p.drawText(QRectF(0, 0, s, s), Qt.AlignCenter, "♪")


def d_mini(p, s, col):
    p.setBrush(Qt.NoBrush)
    p.setPen(QPen(col, s * 0.075, Qt.SolidLine, Qt.FlatCap, Qt.MiterJoin))
    p.drawRect(QRectF(.18 * s, .24 * s, .64 * s, .52 * s))
    p.setPen(Qt.NoPen)
    p.setBrush(col)
    p.drawRect(QRectF(.18 * s, .60 * s, .64 * s, .16 * s))


def make_icon(draw_fn, color: str, size: int = 24) -> QIcon:
    pm = QPixmap(size, size)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing, True)
    col = QColor(color)
    p.setPen(QPen(col, size * 0.09, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
    p.setBrush(Qt.NoBrush)
    draw_fn(p, size, col)
    p.end()
    return QIcon(pm)


def drawn_icon(draw_fn, color: str, size: int) -> QIcon:
    big = size * SS
    pm = QPixmap(big, big)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing, True)
    col = QColor(color)
    p.setPen(QPen(col, big * 0.07, Qt.SolidLine, Qt.RoundCap, Qt.RoundJoin))
    p.setBrush(Qt.NoBrush)
    draw_fn(p, big, col)
    p.end()
    return QIcon(pm.scaled(size, size, Qt.KeepAspectRatio,
                           Qt.SmoothTransformation))


def caption_icon(kind: str, color: str, size: int = CAP_ICON) -> QIcon:
    S = size * SS
    u = S / 16.0
    pm = QPixmap(S, S)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    c = QColor(color)
    p.setPen(Qt.NoPen)
    p.setBrush(c)

    if kind == "min":
        p.drawRect(QRectF(3 * u, 8 * u, 10 * u, 1 * u))

    elif kind == "max":
        p.setBrush(Qt.NoBrush)
        pen = QPen(c)
        pen.setWidthF(1 * u)
        pen.setJoinStyle(Qt.MiterJoin)
        p.setPen(pen)
        p.drawRect(QRectF(3.5 * u, 3.5 * u, 9 * u, 9 * u))

    elif kind == "restore":
        p.setBrush(Qt.NoBrush)
        pen = QPen(c)
        pen.setWidthF(1 * u)
        pen.setJoinStyle(Qt.MiterJoin)
        p.setPen(pen)
        p.drawRect(QRectF(5.5 * u, 3.5 * u, 7 * u, 7 * u))
        p.setCompositionMode(QPainter.CompositionMode_Clear)
        p.setPen(Qt.NoPen)
        p.setBrush(QColor(0, 0, 0, 255))
        p.drawRect(QRectF(3 * u, 6 * u, 8 * u, 8 * u))
        p.setCompositionMode(QPainter.CompositionMode_SourceOver)
        p.setBrush(Qt.NoBrush)
        p.setPen(pen)
        p.drawRect(QRectF(3.5 * u, 6.5 * u, 7 * u, 7 * u))

    elif kind == "close":
        p.setBrush(Qt.NoBrush)
        pen = QPen(c)
        pen.setWidthF(1.1 * u)
        pen.setCapStyle(Qt.RoundCap)
        p.setPen(pen)
        p.setRenderHint(QPainter.Antialiasing, True)
        p.drawLine(QPointF(3.6 * u, 3.6 * u), QPointF(12.4 * u, 12.4 * u))
        p.drawLine(QPointF(12.4 * u, 3.6 * u), QPointF(3.6 * u, 12.4 * u))

    p.end()
    return QIcon(pm.scaled(size, size, Qt.IgnoreAspectRatio,
                           Qt.SmoothTransformation))


IC = {}


def build_icons():
    IC.update({
        "note": make_icon(d_note, THEME["note_fg"], 40),
        "random": make_icon(d_shuffle, THEME["icon_fg"], 22),
        "rotate1": make_icon(d_repeat_one, THEME["icon_fg"], 22),
        "mini": drawn_icon(d_mini, THEME["icon_fg"], CAP_ICON),
        "library": make_icon(d_note, THEME["icon_fg"], 20),
        "cap_min": caption_icon("min", THEME["icon_fg"], CAP_ICON),
        "cap_max": caption_icon("max", THEME["icon_fg"], CAP_ICON),
        "cap_restore": caption_icon("restore", THEME["icon_fg"], CAP_ICON),
        "cap_close": caption_icon("close", THEME["icon_fg"], CAP_ICON),
        "app": make_icon(d_note, GREEN, 64),
    })


def apply_icon(obj, icon) -> None:
    if icon is None:
        return
    try:
        if isinstance(icon, (QIcon, QPixmap)):
            obj.setIcon(icon)
    except Exception:
        pass


def icon_pixmap(name: str, size: int):
    ic = IC.get(name)
    if isinstance(ic, QIcon):
        try:
            return ic.pixmap(size, size)
        except Exception:
            return None
    return None


def make_flat_button(text: str = "", icon: Optional[QIcon] = None,
                     parent=None) -> QPushButton:
    btn = QPushButton(text, parent)
    btn.setProperty("flat", True)
    btn.setFocusPolicy(Qt.NoFocus)
    apply_icon(btn, icon)
    btn.setCursor(Qt.PointingHandCursor)
    return btn


def make_caption_button(obj_name: str, icon: Optional[QIcon],
                        parent=None) -> QPushButton:
    btn = QPushButton(parent)
    btn.setObjectName(obj_name)
    btn.setProperty("caption", True)
    btn.setFocusPolicy(Qt.NoFocus)
    btn.setFixedSize(CAP_W, CAP_H)
    btn.setIconSize(QSize(CAP_ICON, CAP_ICON))
    apply_icon(btn, icon)
    btn.setCursor(Qt.PointingHandCursor)
    return btn


class FlashButton(QPushButton):
    FLASH_MS = 220

    def __init__(self, text: str = "", parent=None):
        super().__init__(text, parent)
        self._icon = None
        self._flash_icon = None
        self._flash_timer = QTimer(self)
        self._flash_timer.setSingleShot(True)
        self._flash_timer.setInterval(self.FLASH_MS)
        self._flash_timer.timeout.connect(self._restore_icon)
        self.pressed.connect(self.flash)

    def set_icon(self, icon: Optional[QIcon]):
        self._icon = icon
        if not self._flash_timer.isActive():
            apply_icon(self, icon)
        self._flash_icon = tint_icon(icon, GREEN, 44) if icon is not None else None

    def flash(self):
        if self._flash_icon is not None:
            apply_icon(self, self._flash_icon)
            self._flash_timer.start()

    def _restore_icon(self):
        apply_icon(self, self._icon)


def make_flash_button(icon: Optional[QIcon] = None,
                      parent=None) -> FlashButton:
    btn = FlashButton("", parent)
    btn.setProperty("flat", True)
    btn.setFocusPolicy(Qt.NoFocus)
    btn.setCursor(Qt.PointingHandCursor)
    btn.set_icon(icon)
    return btn


def make_hline() -> QFrame:
    line = QFrame()
    line.setFixedHeight(1)
    line.setStyleSheet(f"background: {THEME['hline']}; border: none;")
    return line


class ClickSlider(QSlider):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._drag = False

    def _value_from_x(self, x: float) -> int:
        if self.maximum() <= self.minimum():
            return self.value()
        opt = QStyleOptionSlider()
        self.initStyleOption(opt)
        groove = self.style().subControlRect(
            QStyle.CC_Slider, opt, QStyle.SC_SliderGroove, self)
        handle = self.style().subControlRect(
            QStyle.CC_Slider, opt, QStyle.SC_SliderHandle, self)
        span = groove.width() - handle.width()
        if span <= 0:
            return self.value()
        pos = x - groove.x() - handle.width() / 2.0
        ratio = min(max(0.0, pos / span), 1.0)
        return int(self.minimum() + ratio * (self.maximum() - self.minimum()))

    def mousePressEvent(self, ev):
        if ev.button() == Qt.LeftButton and self.maximum() > self.minimum():
            self.setValue(self._value_from_x(ev.position().x()))
            self.setSliderDown(True)
            self._drag = True
            ev.accept()
            return
        super().mousePressEvent(ev)

    def mouseMoveEvent(self, ev):
        if self._drag:
            self.setValue(self._value_from_x(ev.position().x()))
            ev.accept()
            return
        super().mouseMoveEvent(ev)

    def mouseReleaseEvent(self, ev):
        if self._drag:
            self._drag = False
            self.setSliderDown(False)
            ev.accept()
            return
        super().mouseReleaseEvent(ev)


# ==========================================================================
# Подавление тултипов Qt
# ==========================================================================
class NoTipFilter(QObject):
    """Полностью подавляет любые всплывающие подсказки Qt."""

    def eventFilter(self, obj, ev):
        if ev.type() == QEvent.ToolTip:
            return True
        return False


class ClickAwayFilter(QObject):
    """Клик по пустому месту программы снимает фокус и закрывает поиски."""

    def __init__(self, win):
        super().__init__(win)
        self.win = win

    def eventFilter(self, obj, ev):
        if ev.type() in (QEvent.MouseButtonPress,
                         QEvent.NonClientAreaMouseButtonPress):
            try:
                gp = ev.globalPosition().toPoint()
            except Exception:
                return False
            try:
                self.win.dismiss_searches_outside(gp)
            except Exception:
                pass
        return False


# ==========================================================================
# Шапка диалогов и подтверждение
# ==========================================================================
class DialogHeader(QWidget):
    def __init__(self, title: str, parent=None):
        super().__init__(parent)
        self.setObjectName("dlgHeader")
        self.setFixedHeight(36)
        self._drag = None
        lay = QHBoxLayout(self)
        lay.setContentsMargins(6, 0, 6, 0)
        lay.setSpacing(0)
        left_pad = QWidget()
        left_pad.setFixedWidth(CAP_W)
        lay.addWidget(left_pad)
        lay.addStretch()
        self.title_lbl = QLabel(title)
        self.title_lbl.setStyleSheet(
            f"font-weight: 600; font-size: 13px; color: {THEME['text_main']};"
            " background: transparent;")
        lay.addWidget(self.title_lbl)
        lay.addStretch()
        self.close_btn = make_caption_button(
            "capClose", caption_icon("close", THEME["icon_fg"], CAP_ICON),
            self)
        self.close_btn.clicked.connect(self.window().close)
        lay.addWidget(self.close_btn)

    def set_title(self, text: str):
        self.title_lbl.setText(text)

    def apply_styles(self):
        self.title_lbl.setStyleSheet(
            f"font-weight: 600; font-size: 13px; color: {THEME['text_main']};"
            " background: transparent;")
        apply_icon(self.close_btn,
                   caption_icon("close", THEME["icon_fg"], CAP_ICON))

    def mousePressEvent(self, ev):
        if ev.button() == Qt.LeftButton:
            self._drag = ev.globalPosition().toPoint() - self.window().pos()
            ev.accept()
            return
        super().mousePressEvent(ev)

    def mouseMoveEvent(self, ev):
        if self._drag is not None:
            self.window().move(ev.globalPosition().toPoint() - self._drag)
            ev.accept()
            return
        super().mouseMoveEvent(ev)

    def mouseReleaseEvent(self, ev):
        self._drag = None
        super().mouseReleaseEvent(ev)


class ConfirmDialog(QDialog):
    def __init__(self, parent, title: str, text: str,
                 ok_text: str = "Да", cancel_text: str = "Нет"):
        super().__init__(parent)
        self.setObjectName("settingsDlg")
        self.setWindowTitle(title)
        self.setWindowFlags(Qt.Dialog | Qt.FramelessWindowHint)
        self.setMinimumWidth(400)

        root = QVBoxLayout(self)
        root.setContentsMargins(1, 1, 1, 1)
        root.setSpacing(0)
        self.header = DialogHeader(title, self)
        root.addWidget(self.header)

        body = QWidget()
        lay = QVBoxLayout(body)
        lay.setContentsMargins(18, 18, 18, 16)
        lay.setSpacing(16)
        lbl = QLabel(text)
        lbl.setWordWrap(True)
        lbl.setStyleSheet(
            f"font-size: 14px; color: {THEME['text_main']}; background: transparent;")
        lay.addWidget(lbl)

        row = QHBoxLayout()
        row.setSpacing(8)
        row.addStretch()
        no_btn = QPushButton(cancel_text)
        no_btn.setCursor(Qt.PointingHandCursor)
        no_btn.clicked.connect(self.reject)
        row.addWidget(no_btn)
        yes_btn = QPushButton(ok_text)
        yes_btn.setCursor(Qt.PointingHandCursor)
        yes_btn.clicked.connect(self.accept)
        row.addWidget(yes_btn)
        lay.addLayout(row)
        root.addWidget(body, 1)

        no_btn.setFocus()
        QShortcut(QKeySequence(Qt.Key_Escape), self, self.reject)
        QShortcut(QKeySequence(Qt.Key_Return), self, self.accept)


# ==========================================================================
# Диалог плейлиста — в стиле окна «Настройки», без пояснительной строки
# ==========================================================================
class PlaylistDialog(QDialog):
    def __init__(self, parent=None, initial: Optional[Playlist] = None):
        super().__init__(parent)
        self.setObjectName("settingsDlg")
        self.setWindowFlags(Qt.Dialog | Qt.FramelessWindowHint)
        self.setWindowTitle("Изменить плейлист" if initial else "Новый плейлист")
        self.setMinimumWidth(430)
        self.cover_path = initial.cover if initial else ""

        root = QVBoxLayout(self)
        root.setContentsMargins(1, 1, 1, 1)
        root.setSpacing(0)
        self.header = DialogHeader(
            "Изменить плейлист" if initial else "Новый плейлист", self)
        root.addWidget(self.header)

        body = QWidget()
        lay = QVBoxLayout(body)
        lay.setContentsMargins(16, 14, 16, 16)
        lay.setSpacing(10)

        cap1 = QLabel("Название")
        cap1.setStyleSheet(
            f"font-weight: 600; color: {THEME['text_main']}; background: transparent;")
        lay.addWidget(cap1)
        self.name_edit = QLineEdit()
        self.name_edit.setPlaceholderText("Например: «Вечерний микс»")
        if initial:
            self.name_edit.setText(initial.name)
        lay.addWidget(self.name_edit)

        cap2 = QLabel("Описание")
        cap2.setStyleSheet(
            f"font-weight: 600; color: {THEME['text_main']}; background: transparent;")
        lay.addWidget(cap2)
        self.desc_edit = QPlainTextEdit()
        self.desc_edit.setFixedHeight(76)
        self.desc_edit.setPlaceholderText("Необязательно")
        if initial:
            self.desc_edit.setPlainText(initial.description)
        lay.addWidget(self.desc_edit)

        cap3 = QLabel("Обложка")
        cap3.setStyleSheet(
            f"font-weight: 600; color: {THEME['text_main']}; background: transparent;")
        lay.addWidget(cap3)
        row = QHBoxLayout()
        row.setSpacing(8)
        self.cover_preview = QLabel("—")
        self.cover_preview.setObjectName("coverPreview")
        self.cover_preview.setFixedSize(64, 64)
        self.cover_preview.setAlignment(Qt.AlignCenter)
        if initial and initial.cover:
            pm = load_pixmap(initial.cover, 60)
            if pm is not None:
                self.cover_preview.setPixmap(pm)
        cover_btn = QPushButton("Выбрать файл…")
        cover_btn.setCursor(Qt.PointingHandCursor)
        cover_btn.clicked.connect(self.choose_cover)
        clear_btn = QPushButton("Сбросить")
        clear_btn.setCursor(Qt.PointingHandCursor)
        clear_btn.clicked.connect(self.clear_cover)
        row.addWidget(self.cover_preview)
        row.addWidget(cover_btn)
        row.addWidget(clear_btn)
        row.addStretch()
        lay.addLayout(row)

        lay.addSpacing(4)
        brow = QHBoxLayout()
        brow.addStretch()
        self.ok_btn = QPushButton("Сохранить" if initial else "Создать")
        self.ok_btn.setObjectName("primaryBtn")
        self.ok_btn.setCursor(Qt.PointingHandCursor)
        self.ok_btn.clicked.connect(self.accept)
        brow.addWidget(self.ok_btn)
        lay.addLayout(brow)
        root.addWidget(body, 1)

        QShortcut(QKeySequence(Qt.Key_Escape), self, self.reject)
        self.name_edit.setFocus()

    def choose_cover(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "Обложка плейлиста", "",
            "Изображения (*.png *.jpg *.jpeg *.bmp *.webp)")
        if path:
            self.cover_path = path
            pm = load_pixmap(path, 60)
            if pm is not None:
                self.cover_preview.setPixmap(pm)

    def clear_cover(self):
        self.cover_path = ""
        self.cover_preview.clear()
        self.cover_preview.setText("—")

    def accept(self):
        if not self.name_edit.text().strip():
            self.name_edit.setFocus()
            self.name_edit.setStyleSheet(
                f"border: 1px solid {DANGER}; background: {THEME['input_bg']};"
                f" color: {THEME['input_fg']}; border-radius: 6px; padding: 6px 8px;")
            QTimer.singleShot(900, lambda: self.name_edit.setStyleSheet(""))
            return
        super().accept()


# ==========================================================================
# Окно настроек
# ==========================================================================
class SettingsDialog(QDialog):
    def __init__(self, main_win, parent=None):
        super().__init__(parent or main_win)
        self.main_win = main_win
        self.setObjectName("settingsDlg")
        self.setWindowTitle("Настройки")
        self.setWindowFlags(Qt.Dialog | Qt.FramelessWindowHint)
        self.setMinimumWidth(400)

        root = QVBoxLayout(self)
        root.setContentsMargins(1, 1, 1, 1)
        root.setSpacing(0)
        self.header = DialogHeader("Настройки", self)
        root.addWidget(self.header)

        body = QWidget()
        lay = QVBoxLayout(body)
        lay.setContentsMargins(16, 14, 16, 16)
        lay.setSpacing(10)

        self.chk_dark = QCheckBox("Тёмная тема")
        self.chk_dark.toggled.connect(main_win.apply_theme)
        lay.addWidget(self.chk_dark)

        self.chk_zoom = QCheckBox("Зум фоновой обложки")
        self.chk_zoom.toggled.connect(main_win.apply_bg_zoom)
        lay.addWidget(self.chk_zoom)

        self.chk_pin = QCheckBox("Закрепить фоновую обложку")
        self.chk_pin.toggled.connect(main_win.apply_bg_pin)
        lay.addWidget(self.chk_pin)

        self.chk_hide_banner = QCheckBox("Скрыть фоновый альбом плейлиста")
        self.chk_hide_banner.toggled.connect(main_win.apply_hide_banner)
        lay.addWidget(self.chk_hide_banner)

        self.chk_no_cover_img = QCheckBox("Отключить изображение обложки")
        self.chk_no_cover_img.toggled.connect(main_win.apply_no_cover_image)
        lay.addWidget(self.chk_no_cover_img)

        self.chk_follow = QCheckBox("Следовать за переключением")
        self.chk_follow.toggled.connect(main_win.apply_follow_switch)
        lay.addWidget(self.chk_follow)

        self.chk_classic = QCheckBox("Классический вид")
        self.chk_classic.toggled.connect(main_win.apply_classic)
        lay.addWidget(self.chk_classic)

        lay.addStretch()
        row = QHBoxLayout()
        row.addStretch()
        close_btn = QPushButton("Закрыть")
        close_btn.setCursor(Qt.PointingHandCursor)
        close_btn.clicked.connect(self.close)
        row.addWidget(close_btn)
        lay.addLayout(row)
        root.addWidget(body, 1)

        QShortcut(QKeySequence(Qt.Key_Escape), self, self.close)
        self.refresh()

    def refresh(self):
        s = self.main_win.config.settings
        for chk, key in ((self.chk_dark, "dark_theme"),
                         (self.chk_zoom, "bg_zoom"),
                         (self.chk_pin, "bg_pin"),
                         (self.chk_hide_banner, "hide_banner"),
                         (self.chk_no_cover_img, "no_cover_image"),
                         (self.chk_follow, "follow_switch"),
                         (self.chk_classic, "classic_view")):
            val = bool(s.get(key, False))
            if chk.isChecked() != val:
                chk.blockSignals(True)
                chk.setChecked(val)
                chk.blockSignals(False)
        if not self.chk_pin.isEnabled():
            self.chk_pin.setEnabled(True)


# ==========================================================================
# Делегат списка плейлистов
# ==========================================================================
class PlaylistDelegate(QStyledItemDelegate):
    def sizeHint(self, opt, idx):
        if idx.data(Qt.UserRole) == "sep":
            return QSize(0, 18)
        return super().sizeHint(opt, idx)

    def paint(self, p, opt, idx):
        if idx.data(Qt.UserRole) == "sep":
            p.save()
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(THEME["hline"]))
            y = opt.rect.center().y()
            p.drawRect(QRectF(opt.rect.x() + 8, y, opt.rect.width() - 16, 1))
            p.restore()
            return
        p.save()
        if opt.state & QStyle.State_Selected:
            text = idx.data(Qt.DisplayRole) or ""
            fm = opt.fontMetrics
            tw = fm.horizontalAdvance(text)
            has_icon = idx.data(Qt.DecorationRole) is not None
            ix = opt.rect.x() + 6
            if has_icon:
                ix += opt.decorationSize.width() + 4
            r = QRectF(ix, opt.rect.y() + 3, tw + 10, opt.rect.height() - 6)
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(THEME["list_sel"]))
            p.drawRoundedRect(r, 6, 6)
        o = QStyleOptionViewItem(opt)
        o.state &= ~QStyle.State_Selected
        o.backgroundBrush = QBrush(Qt.transparent)
        super().paint(p, o, idx)
        p.restore()


# ==========================================================================
# Делегат строки трека
# ==========================================================================
class TrackRowDelegate(QStyledItemDelegate):
    COVER = 40
    PAD_L = 6
    GAP = 10

    def __init__(self, parent=None):
        super().__init__(parent)
        self.play_row = -1

    def sizeHint(self, opt, idx):
        if idx.column() == 1:
            return QSize(160, 56)
        return super().sizeHint(opt, idx)

    def paint(self, p, opt, idx):
        if idx.column() != 1:
            super().paint(p, opt, idx)
            return
        p.save()
        r = opt.rect
        selected = bool(opt.state & QStyle.State_Selected)
        playing = (idx.row() == self.play_row)
        if selected:
            p.fillRect(r, QColor(THEME["selected"]))

        title = idx.data(Qt.DisplayRole) or ""
        artist = idx.data(Qt.UserRole + 1) or "—"
        cover = idx.data(Qt.UserRole + 2) or ""

        cx = r.x() + self.PAD_L
        cy = r.y() + (r.height() - self.COVER) // 2
        pm = load_pixmap(cover, self.COVER)
        if pm is None:
            pm = icon_pixmap("note", self.COVER)
        if pm is not None and not pm.isNull():
            p.drawPixmap(cx, cy, pm)
        else:
            p.fillRect(QRect(cx, cy, self.COVER, self.COVER),
                       QColor(THEME["cover_ph"]))

        tx = cx + self.COVER + self.GAP
        tw = max(10, r.right() - tx - 4)
        if selected:
            c_title = QColor(THEME["sel_text"])
            c_artist = QColor(THEME["sel_text_sec"])
        else:
            c_title = QColor(THEME["player"] if playing else THEME["text_main"])
            c_artist = QColor(THEME["text_sec"])

        ft = QFont(opt.font)
        ft.setPixelSize(14)
        ft.setWeight(QFont.DemiBold if (playing or selected) else QFont.Normal)
        fa = QFont(opt.font)
        fa.setPixelSize(11)
        fmt = QFontMetrics(ft)
        fma = QFontMetrics(fa)
        th = fmt.height()
        ah = fma.height()
        y0 = r.y() + max(0, (r.height() - (th + ah)) // 2)

        p.setRenderHint(QPainter.TextAntialiasing)
        p.setFont(ft)
        p.setPen(c_title)
        p.drawText(QRect(tx, y0, tw, th), Qt.AlignLeft | Qt.AlignVCenter,
                   fmt.elidedText(title, Qt.ElideRight, tw))
        p.setFont(fa)
        p.setPen(c_artist)
        p.drawText(QRect(tx, y0 + th, tw, ah), Qt.AlignLeft | Qt.AlignVCenter,
                   fma.elidedText(artist, Qt.ElideRight, tw))
        p.restore()


# ==========================================================================
# Левая панель
# ==========================================================================
class PlaylistPanel(QWidget):
    add_requested = Signal()
    selection_changed = Signal(int)
    menu_requested = Signal(int, object)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("leftPanel")
        lay = QVBoxLayout(self)
        lay.setContentsMargins(8, 8, 8, 8)
        lay.setSpacing(4)

        header = QHBoxLayout()
        self.icon_lbl = QLabel()
        self.icon_lbl.setFixedSize(18, 18)
        header.addWidget(self.icon_lbl)
        self.title_lbl = QLabel("Плейлисты")
        self.title_lbl.setStyleSheet(
            f"font-weight: 600; font-size: 14px; color: {THEME['text_main']};")
        header.addWidget(self.title_lbl)
        header.addStretch()
        add_btn = make_flat_button("+")
        add_btn.clicked.connect(self.add_requested)
        header.addWidget(add_btn)
        lay.addLayout(header)

        self.list = QListWidget()
        self.list.setIconSize(QSize(28, 28))
        self.list.setItemDelegate(PlaylistDelegate(self.list))
        self.list.setContextMenuPolicy(Qt.CustomContextMenu)
        self.list.customContextMenuRequested.connect(self._on_menu)
        self.list.currentRowChanged.connect(self.selection_changed)
        lay.addWidget(self.list)

        self.apply_styles()

    def _on_menu(self, pos):
        row = self.list.indexAt(pos).row()
        if row < 0:
            return
        it = self.list.item(row)
        if it is not None and it.data(Qt.UserRole) == "sep":
            return
        self.menu_requested.emit(row, self.list.viewport().mapToGlobal(pos))

    def apply_styles(self):
        self.title_lbl.setStyleSheet(
            f"font-weight: 600; font-size: 14px; color: {THEME['text_main']};")
        base = custom_icon("library_music", "c") or IC.get("library")
        if base is not None:
            ic = tint_icon(base, THEME["text_main"], 36)
            pm = ic.pixmap(18, 18)
            if not pm.isNull():
                self.icon_lbl.setPixmap(pm)
        col = QColor(THEME["text_main"])
        for i in range(self.list.count()):
            it = self.list.item(i)
            if it is not None:
                it.setForeground(col)
        self.list.viewport().update()

    def _update_min_width(self):
        fm = self.list.fontMetrics()
        need = 0
        for i in range(self.list.count()):
            it = self.list.item(i)
            if it is None or it.data(Qt.UserRole) == "sep":
                continue
            tw = fm.horizontalAdvance(it.text())
            iw = 32 if (not it.icon().isNull()) else 0
            need = max(need, tw + iw)
        need += 34
        self.setMinimumWidth(max(170, need))

    def reload(self, playlists: List[Playlist], select_row: Optional[int] = None,
               select_last: bool = False):
        prev = self.list.currentRow()
        self.list.blockSignals(True)
        self.list.clear()
        col = QColor(THEME["text_main"])

        it_src = QListWidgetItem("Источник")
        it_src.setForeground(col)
        self.list.addItem(it_src)

        it_freq = QListWidgetItem("Часто прослушиваемые")
        it_freq.setForeground(col)
        self.list.addItem(it_freq)

        if playlists:
            sep = QListWidgetItem("")
            sep.setFlags(Qt.NoItemFlags)
            sep.setData(Qt.UserRole, "sep")
            self.list.addItem(sep)
            for pl in playlists:
                item = QListWidgetItem(pl.name)
                item.setForeground(col)
                pm = load_pixmap(pl.cover, 28)
                if pm is not None:
                    apply_icon(item, QIcon(pm))
                self.list.addItem(item)

        self._update_min_width()

        if select_last:
            row = self.list.count() - 1
        elif select_row is not None:
            row = select_row
        else:
            row = prev if 0 <= prev < self.list.count() else 0
        it = self.list.item(row)
        if it is not None and it.data(Qt.UserRole) == "sep":
            row = SRC_ROW
        self.list.setCurrentRow(row)
        self.list.blockSignals(False)
        self.selection_changed.emit(self.list.currentRow())


# ==========================================================================
# Мягкое рассеянное затемнение за полем поиска в баннере
# ==========================================================================
class SearchScrim(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self._alpha = 0.0
        self.setAttribute(Qt.WA_TransparentForMouseEvents, True)
        self._anim = QPropertyAnimation(self, b"scrimAlpha")
        self._anim.setDuration(280)
        self._anim.setEasingCurve(QEasingCurve.OutCubic)

    def _get(self):
        return self._alpha

    def _set(self, value):
        self._alpha = max(0.0, min(1.0, float(value)))
        self.update()

    scrimAlpha = Property(float, _get, _set)

    def fade_to(self, target: float):
        self._anim.stop()
        self._anim.setStartValue(self._alpha)
        self._anim.setEndValue(max(0.0, min(1.0, float(target))))
        self._anim.start()

    def paintEvent(self, event):
        if self._alpha <= 0.01:
            return
        p = QPainter(self)
        try:
            p.setRenderHint(QPainter.Antialiasing)
            w, h = self.width(), self.height()
            g = QRadialGradient(w * 0.36, h * 0.5, max(w, h) * 0.66)
            a = self._alpha
            g.setColorAt(0.00, QColor(0, 0, 0, int(150 * a)))
            g.setColorAt(0.28, QColor(0, 0, 0, int(126 * a)))
            g.setColorAt(0.50, QColor(0, 0, 0, int(88 * a)))
            g.setColorAt(0.70, QColor(0, 0, 0, int(48 * a)))
            g.setColorAt(0.86, QColor(0, 0, 0, int(18 * a)))
            g.setColorAt(1.00, QColor(0, 0, 0, 0))
            p.setPen(Qt.NoPen)
            p.setBrush(QBrush(g))
            p.drawRect(self.rect())
        finally:
            p.end()


# ==========================================================================
# Баннер
# ==========================================================================
class HeaderBanner(QWidget):
    FADE_PX = 48
    TITLE_MAX_PX = 78
    TITLE_MIN_PX = 26

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setFixedHeight(BANNER_DEF_H)
        self._pm = None
        self._path = ""
        self._muted_mode = False
        self._zoom_enabled = False
        self._phase = 0.0
        self._scale = 1.0
        self._title_text = ""

        self.scrim = SearchScrim(self)

        self._timer = QTimer(self)
        self._timer.setInterval(30)
        self._timer.timeout.connect(self._tick)
        self._timer.start()

        lay = QVBoxLayout(self)
        lay.setContentsMargins(18, 16, 18, self.FADE_PX + 6)
        lay.setSpacing(6)

        self.title_lbl = QLabel("")
        self.title_lbl.setWordWrap(True)
        self.desc_lbl = QLabel("")
        self.desc_lbl.setWordWrap(True)
        self.desc_lbl.setStyleSheet(
            "font-size: 13px; color: #b9bdc4; background: transparent;")

        row = QHBoxLayout()
        row.setSpacing(12)
        self.search = QLineEdit()
        self.search.setObjectName("searchBox")
        self.search.setPlaceholderText("Поиск трека…")
        self.search.setFixedWidth(260)
        self.search.setFixedHeight(32)
        self.search.setFocusPolicy(Qt.ClickFocus)
        self.search.installEventFilter(self)
        self.count_lbl = QLabel("")
        self.count_lbl.setStyleSheet(
            "font-size: 12px; color: #dfe2e6; background: transparent;")
        row.addWidget(self.search)
        row.addWidget(self.count_lbl)
        row.addStretch()

        lay.addWidget(self.title_lbl)
        lay.addStretch()
        lay.addWidget(self.desc_lbl)
        lay.addLayout(row)

        self.set_title("")
        self.set_desc("")
        self._place_scrim()

    def eventFilter(self, obj, ev):
        if obj is self.search:
            if ev.type() == QEvent.FocusIn:
                self.scrim.fade_to(1.0)
            elif ev.type() == QEvent.FocusOut:
                self.scrim.fade_to(0.0)
            elif ev.type() == QEvent.KeyPress and ev.key() == Qt.Key_Escape:
                self.reset_search()
                return True
        return super().eventFilter(obj, ev)

    def reset_search(self):
        self.search.clear()
        self.search.clearFocus()
        self.scrim.fade_to(0.0)

    def _place_scrim(self):
        s = self.search.geometry()
        c = self.count_lbl.geometry()
        x = max(0, s.x() - 70)
        y = max(0, s.y() - 52)
        right_edge = max(s.right(), c.right()) + 150
        w = min(self.width() - x, max(240, right_edge - x))
        h = min(self.height() - y, s.height() + 104)
        self.scrim.setGeometry(x, y, max(120, w), max(80, h))
        self.scrim.lower()
        for wdg in (self.title_lbl, self.desc_lbl, self.search, self.count_lbl):
            wdg.raise_()

    def resizeEvent(self, e):
        super().resizeEvent(e)
        self._relayout_title()
        self._place_scrim()

    def showEvent(self, e):
        super().showEvent(e)
        self._place_scrim()

    def set_title(self, text: str):
        self._title_text = soft_wrap(text or "")
        self._relayout_title()

    def set_desc(self, text: str):
        self.desc_lbl.setText(soft_wrap(text or "", 60))

    def _relayout_title(self):
        if not self._title_text:
            self.title_lbl.setText("")
            return
        avail_w = max(50, self.width() - 36)
        lay_m = 16 + self.FADE_PX + 6
        row_h = 32
        spacing = 6 * 3
        try:
            desc_h = self.desc_lbl.heightForWidth(avail_w)
        except Exception:
            desc_h = -1
        if desc_h is None or desc_h < 0:
            desc_h = self.desc_lbl.sizeHint().height()
        avail_h = max(40, self.height() - lay_m - int(desc_h) - row_h - spacing)
        size = self.TITLE_MAX_PX
        while size > self.TITLE_MIN_PX:
            f = QFont(self.title_lbl.font())
            f.setPixelSize(size)
            f.setWeight(QFont.Bold)
            fm = QFontMetrics(f)
            r = fm.boundingRect(QRect(0, 0, avail_w, 100000),
                                Qt.TextWordWrap | Qt.AlignLeft,
                                self._title_text)
            if r.height() <= avail_h:
                break
            size -= 4
        self.title_lbl.setStyleSheet(
            f"font-size: {size}px; font-weight: 800; color: #ffffff;"
            " background: transparent;")
        self.title_lbl.setText(self._title_text)

    def set_zoom_enabled(self, on: bool):
        self._zoom_enabled = bool(on)
        if not on:
            self._phase = 0.0

    def set_muted_mode(self, on: bool):
        self._muted_mode = bool(on)
        self.update()

    def _tick(self):
        has_img = self._pm is not None and not self._pm.isNull()
        if (self._zoom_enabled and has_img and self.isVisible()
                and not self._muted_mode):
            self._phase = (self._phase + 30.0 / ZOOM_PERIOD_MS) % 1.0
            target = 1.0 + ZOOM_AMP * (0.5 - 0.5 * math.cos(2 * math.pi * self._phase))
        else:
            target = 1.0
        if abs(target - self._scale) > 0.0004:
            self._scale += (target - self._scale) * 0.12
            self.update()
        elif self._scale != target:
            self._scale = target

    def set_background(self, path: Optional[str]):
        self._path = path or ""
        self._pm = load_pixmap_raw(path)
        self.update()

    def _paint_muted(self, p, w, h):
        base = muted_backdrop(dominant_rgb(self._path))
        if base is None:
            base = QColor(38, 42, 48)
        hh, ss, vv, _ = base.getHsvF()
        top = QColor.fromHsvF(hh, max(0.0, ss * 0.92), min(1.0, vv + 0.10))
        bot = QColor.fromHsvF(hh, min(1.0, ss * 1.05), max(0.0, vv - 0.07))
        g = QLinearGradient(0, 0, w, h)
        g.setColorAt(0.0, top)
        g.setColorAt(1.0, bot)
        p.fillRect(self.rect(), g)
        glow = QRadialGradient(w * 0.28, h * 0.22, max(w, h) * 0.75)
        gl = QColor.fromHsvF(hh, max(0.0, ss * 0.75), min(1.0, vv + 0.16))
        gl.setAlpha(120)
        glow.setColorAt(0.0, gl)
        glow.setColorAt(1.0, QColor(0, 0, 0, 0))
        p.fillRect(self.rect(), QBrush(glow))

    def paintEvent(self, event):
        p = QPainter(self)
        try:
            pm = self._pm
            w = self.width()
            h = self.height()
            if self._muted_mode:
                self._paint_muted(p, w, h)
            elif pm is not None and not pm.isNull() and w > 0 and h > 0:
                p.setRenderHint(QPainter.SmoothPixmapTransform)
                iw = pm.width()
                ih = pm.height()
                aspect = w / h
                if iw / ih > aspect:
                    ch = float(ih)
                    cw = ch * aspect
                else:
                    cw = float(iw)
                    ch = cw / aspect
                s = max(1.0, self._scale)
                cw /= s
                ch /= s
                sx = (iw - cw) / 2.0
                sy = (ih - ch) / 2.0
                p.drawPixmap(QRect(0, 0, w, h), pm,
                             QRect(int(sx), int(sy),
                                   max(1, int(cw)), max(1, int(ch))))
                ov = QLinearGradient(0, 0, 0, h)
                ov.setColorAt(0.0, QColor(0, 0, 0, 100))
                ov.setColorAt(0.75, QColor(0, 0, 0, 90))
                ov.setColorAt(1.0, QColor(0, 0, 0, 30))
                p.fillRect(self.rect(), ov)
            else:
                g = QLinearGradient(0, 0, 0, h)
                g.setColorAt(0.0, QColor("#454a52"))
                g.setColorAt(1.0, QColor("#2a2e34"))
                p.fillRect(self.rect(), g)
                ov = QLinearGradient(0, 0, 0, h)
                ov.setColorAt(0.0, QColor(0, 0, 0, 100))
                ov.setColorAt(0.75, QColor(0, 0, 0, 90))
                ov.setColorAt(1.0, QColor(0, 0, 0, 30))
                p.fillRect(self.rect(), ov)
            fade = QLinearGradient(0, h - self.FADE_PX, 0, h)
            fade.setColorAt(0.0, QColor(THEME["fade_r"], THEME["fade_g"],
                                        THEME["fade_b"], 0))
            fade.setColorAt(1.0, QColor(THEME["fade_r"], THEME["fade_g"],
                                        THEME["fade_b"], 255))
            p.fillRect(0, h - self.FADE_PX, w, self.FADE_PX, fade)
        finally:
            p.end()


class BannerResizeHandle(QWidget):
    resized = Signal(int)

    def __init__(self, banner: HeaderBanner, parent=None):
        super().__init__(parent)
        self._banner = banner
        self.setFixedHeight(6)
        self.setCursor(Qt.SizeVerCursor)
        self.setStyleSheet("background: transparent;")
        self._dragging = False
        self._start_y = 0.0
        self._start_h = 0

    def mousePressEvent(self, ev):
        if ev.button() == Qt.LeftButton:
            self._dragging = True
            self._start_y = ev.globalPosition().y()
            self._start_h = self._banner.height()
            self.grabMouse()
            ev.accept()
            return
        super().mousePressEvent(ev)

    def mouseMoveEvent(self, ev):
        if self._dragging:
            dy = ev.globalPosition().y() - self._start_y
            h = int(self._start_h + dy)
            h = max(BANNER_MIN_H, min(BANNER_MAX_H, h))
            self._banner.setFixedHeight(h)
            ev.accept()
            return
        super().mouseMoveEvent(ev)

    def mouseReleaseEvent(self, ev):
        if self._dragging:
            self._dragging = False
            self.releaseMouse()
            self.resized.emit(self._banner.height())
            ev.accept()
            return
        super().mouseReleaseEvent(ev)


# ==========================================================================
# Правая область «Классический вид»
# ==========================================================================
class CoverTile(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self._path = ""
        self.setMinimumSize(96, 96)
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)

    def set_cover(self, path: str):
        self._path = path or ""
        self.update()

    def paintEvent(self, ev):
        p = QPainter(self)
        try:
            p.setRenderHint(QPainter.Antialiasing)
            p.setRenderHint(QPainter.SmoothPixmapTransform)
            r = QRectF(self.rect())
            path = QPainterPath()
            path.addRoundedRect(r, 10, 10)
            p.setClipPath(path)
            pm = load_pixmap_raw(self._path)
            if pm is not None and not pm.isNull():
                iw, ih = pm.width(), pm.height()
                aspect = r.width() / max(1.0, r.height())
                if iw / max(1, ih) > aspect:
                    ch = float(ih); cw = ch * aspect
                else:
                    cw = float(iw); ch = cw / aspect
                sx = (iw - cw) / 2.0
                sy = (ih - ch) / 2.0
                p.drawPixmap(r.toRect(), pm,
                             QRect(int(sx), int(sy),
                                   max(1, int(cw)), max(1, int(ch))))
            else:
                p.fillRect(r, QColor(THEME["cover_ph"]))
                note = icon_pixmap("note", 48)
                if note is not None:
                    p.drawPixmap(int(r.center().x() - 24),
                                 int(r.center().y() - 24), note)
        finally:
            p.end()


class NowPlayingPanel(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("nowPanel")
        self.setMinimumWidth(220)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(14, 14, 14, 14)
        lay.setSpacing(6)

        self.cover = CoverTile(self)
        lay.addWidget(self.cover)
        lay.addSpacing(4)

        self.title_lbl = QLabel("—")
        self.title_lbl.setWordWrap(True)
        lay.addWidget(self.title_lbl)

        self.artist_lbl = QLabel("—")
        self.artist_lbl.setWordWrap(True)
        lay.addWidget(self.artist_lbl)

        self.album_lbl = QLabel("—")
        self.album_lbl.setWordWrap(True)
        lay.addWidget(self.album_lbl)

        self.year_lbl = QLabel("—")
        lay.addWidget(self.year_lbl)
        lay.addStretch()

        self._track = None
        self.apply_styles()
        self._sync_cover_size()

    def _sync_cover_size(self):
        side = max(96, min(460, self.width() - 28))
        self.cover.setFixedHeight(side)

    def resizeEvent(self, ev):
        super().resizeEvent(ev)
        self._sync_cover_size()

    def apply_styles(self):
        self.title_lbl.setStyleSheet(
            f"font-size: 15px; font-weight: 700; color: {THEME['text_main']};"
            " background: transparent;")
        self.artist_lbl.setStyleSheet(
            f"font-size: 13px; font-weight: 600; color: {THEME['player']};"
            " background: transparent;")
        self.album_lbl.setStyleSheet(
            f"font-size: 13px; color: {THEME['text_sec']}; background: transparent;")
        self.year_lbl.setStyleSheet(
            f"font-size: 12px; color: {THEME['text_sec']}; background: transparent;")
        self.cover.update()

    def set_track(self, tr: Optional[Track]):
        self._track = tr
        if tr is None:
            self.title_lbl.setText("—")
            self.artist_lbl.setText("—")
            self.album_lbl.setText("—")
            self.year_lbl.setText("—")
            self.cover.set_cover("")
            return
        self.title_lbl.setText(tr.title or "—")
        self.artist_lbl.setText(tr.artist or "—")
        self.album_lbl.setText(tr.album or "—")
        self.year_lbl.setText(tr.year or "—")
        self.cover.set_cover(tr.cover if _cover_usable(tr.cover) else "")


# ==========================================================================
# Центр
# ==========================================================================
class TracksPanel(QWidget):
    track_activated = Signal(int)
    tracks_shown = Signal(list)
    banner_resized = Signal(int)
    track_menu_requested = Signal(int, object)

    WHEEL_STEP = 30
    SMOOTH_MS = 12
    SMOOTH_K = 0.35
    MAX_TABLE_H = 16_000_000

    def __init__(self, parent=None):
        super().__init__(parent)
        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(0)

        self._pin_lay = QVBoxLayout()
        self._pin_lay.setContentsMargins(0, 0, 0, 0)
        self._pin_lay.setSpacing(0)
        lay.addLayout(self._pin_lay)

        self.scroll = QScrollArea()
        self.scroll.setWidgetResizable(True)
        self.scroll.setFrameShape(QFrame.NoFrame)
        self.scroll.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.scroll.viewport().installEventFilter(self)
        self.scroll.verticalScrollBar().sliderPressed.connect(self._cancel_smooth)

        container = QWidget()
        container.setStyleSheet("background: transparent;")
        self._content_lay = QVBoxLayout(container)
        self._content_lay.setContentsMargins(0, 0, 0, 0)
        self._content_lay.setSpacing(6)

        self.banner = HeaderBanner()
        self._search_timer = QTimer(self)
        self._search_timer.setSingleShot(True)
        self._search_timer.setInterval(120)
        self._search_timer.timeout.connect(self._apply_filter)
        self.banner.search.textChanged.connect(lambda *_: self._search_timer.start())
        self._content_lay.addWidget(self.banner)

        self.resize_handle = BannerResizeHandle(self.banner)
        self.resize_handle.resized.connect(self.banner_resized)
        self._content_lay.addWidget(self.resize_handle)

        self.empty_label = QLabel("Здесь пока нет треков")
        self.empty_label.setAlignment(Qt.AlignCenter)
        self.empty_label.setStyleSheet(f"color: {THEME['empty']};")
        self._content_lay.addWidget(self.empty_label)

        self.table = QTableWidget(0, 4)
        self.table.setHorizontalHeaderLabels(["#", "НАЗВАНИЕ", "АЛЬБОМ", "ВРЕМЯ"])
        hdr = self.table.horizontalHeader()
        hdr.setSectionResizeMode(0, QHeaderView.ResizeToContents)
        hdr.setSectionResizeMode(1, QHeaderView.Stretch)
        hdr.setSectionResizeMode(2, QHeaderView.Interactive)
        hdr.setSectionResizeMode(3, QHeaderView.ResizeToContents)
        self.table.setColumnWidth(2, 200)
        self.table.verticalHeader().setVisible(False)
        self.table.verticalHeader().setDefaultSectionSize(56)
        self.table.setShowGrid(False)
        self.table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.table.setSelectionMode(QAbstractItemView.SingleSelection)
        self.table.setFocusPolicy(Qt.NoFocus)
        self.table.setVerticalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.table.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.table.setContextMenuPolicy(Qt.CustomContextMenu)
        self.table.customContextMenuRequested.connect(self._on_table_menu)
        self.table.doubleClicked.connect(
            lambda: self.track_activated.emit(self.table.currentRow()))
        self.row_delegate = TrackRowDelegate(self.table)
        self.table.setItemDelegateForColumn(1, self.row_delegate)
        self.table.itemSelectionChanged.connect(self._refresh_rows)
        self._content_lay.addWidget(self.table)
        self._content_lay.addStretch()

        self.scroll.setWidget(container)
        lay.addWidget(self.scroll)

        self._all: List[Track] = []
        self.current: List[Track] = []
        self._rows: List[dict] = []
        self._play_row: Optional[int] = None
        self._playing_track: Optional[Track] = None
        self._base_cover: str = ""
        self._scroll_target: Optional[int] = None
        self._pinned = False
        self._banner_hidden = False

        self._smooth = QTimer(self)
        self._smooth.setInterval(self.SMOOTH_MS)
        self._smooth.timeout.connect(self._smooth_step)

    def _on_table_menu(self, pos):
        row = self.table.indexAt(pos).row()
        if row < 0 or row >= len(self.current):
            return
        self.track_menu_requested.emit(row, self.table.viewport().mapToGlobal(pos))

    def set_banner_hidden(self, on: bool):
        self._banner_hidden = bool(on)
        self.banner.setVisible(not on)
        self.resize_handle.setVisible(not on)

    def set_pinned(self, on: bool):
        on = bool(on)
        if on == self._pinned:
            return
        self._pinned = on
        for lay in (self._pin_lay, self._content_lay):
            if lay.indexOf(self.banner) >= 0:
                lay.removeWidget(self.banner)
            if lay.indexOf(self.resize_handle) >= 0:
                lay.removeWidget(self.resize_handle)
        if on:
            self._pin_lay.addWidget(self.banner)
            self._pin_lay.addWidget(self.resize_handle)
        else:
            self._content_lay.insertWidget(0, self.resize_handle)
            self._content_lay.insertWidget(0, self.banner)
        self.scroll.verticalScrollBar().setValue(0)

    def set_banner_height(self, h: int):
        self.banner.setFixedHeight(
            max(BANNER_MIN_H, min(BANNER_MAX_H, int(h))))

    def apply_styles(self):
        self.empty_label.setStyleSheet(f"color: {THEME['empty']};")
        self.table.viewport().update()

    def row_of_track(self, track: Optional[Track]) -> int:
        if track is None:
            return -1
        for i, t in enumerate(self.current):
            if t is track or (track.path and t.path == track.path):
                return i
        return -1

    def ensure_row_visible(self, row: int):
        try:
            if not (0 <= row < len(self._rows)):
                return
            item = self.table.item(row, 0)
            if item is None:
                return
            rr = self.table.visualItemRect(item)
            vp = self.table.viewport()
            top_in_content = self.table.mapTo(self.scroll.widget(), vp.pos()).y() \
                + rr.top()
            bot_in_content = top_in_content + rr.height()
            sb = self.scroll.verticalScrollBar()
            view_h = self.scroll.viewport().height()
            view_top = sb.value()
            view_bot = view_top + view_h
            if top_in_content < view_top:
                sb.setValue(int(max(0, top_in_content)))
            elif bot_in_content > view_bot:
                sb.setValue(int(bot_in_content - view_h))
        except Exception:
            pass

    def _cancel_smooth(self):
        self._scroll_target = None
        self._smooth.stop()

    def _smooth_step(self):
        sb = self.scroll.verticalScrollBar()
        if self._scroll_target is None:
            self._smooth.stop()
            return
        target = min(self._scroll_target, sb.maximum())
        cur = sb.value()
        diff = target - cur
        if diff == 0:
            self._scroll_target = None
            self._smooth.stop()
            return
        move = int(diff * self.SMOOTH_K)
        if move == 0:
            move = 1 if diff > 0 else -1
        sb.setValue(cur + move)

    def eventFilter(self, obj, event):
        if obj is self.scroll.viewport() and event.type() == QEvent.Wheel:
            pd = event.pixelDelta().y()
            ad = event.angleDelta().y()
            if pd or ad:
                sb = self.scroll.verticalScrollBar()
                if sb.maximum() <= 0:
                    return True
                base = (self._scroll_target if self._scroll_target is not None
                        else sb.value())
                step = pd if pd else ad * self.WHEEL_STEP / 120.0
                target = int(base - step)
                target = max(0, min(sb.maximum(), target))
                self._scroll_target = target
                if not self._smooth.isActive():
                    self._smooth.start()
                return True
        return super().eventFilter(obj, event)

    def show_tracks(self, tracks: List[Track], title: str, desc: str,
                    cover: str):
        self._cancel_smooth()
        self._all = list(tracks)
        self._base_cover = cover or ""
        self.banner.set_title(title)
        self.banner.set_desc(desc)
        n = len(tracks)
        self.banner.count_lbl.setText(
            f"{n} {plural(n, 'трек', 'трека', 'треков')}, "
            f"{total_duration_text(tracks)}")
        self.banner.search.blockSignals(True)
        self.banner.search.clear()
        self.banner.search.blockSignals(False)
        self.scroll.verticalScrollBar().setValue(0)
        self._apply_filter()

    def set_backdrop(self, path: Optional[str]):
        self.banner.set_background(path)

    def _apply_filter(self, _text: str = ""):
        q = self.banner.search.text().strip().lower()
        if q:
            filtered = [t for t in self._all
                        if q in t.title.lower() or q in (t.artist or "").lower()]
        else:
            filtered = list(self._all)
        self._render(filtered)
        self.tracks_shown.emit(filtered)

    def _render(self, tracks: List[Track]):
        self.current = tracks
        self._rows = []
        self._play_row = None
        self.row_delegate.play_row = -1
        self.table.setUpdatesEnabled(False)
        try:
            self.table.clearContents()
            self.table.setRowCount(len(tracks))
            for r, t in enumerate(tracks):
                num = QTableWidgetItem(str(r + 1))
                num.setTextAlignment(Qt.AlignCenter | Qt.AlignVCenter)
                self.table.setItem(r, 0, num)

                name = QTableWidgetItem(t.title)
                name.setData(Qt.UserRole + 1, t.artist or "—")
                name.setData(Qt.UserRole + 2, t.cover or "")
                self.table.setItem(r, 1, name)

                alb = QTableWidgetItem(t.album or "")
                self.table.setItem(r, 2, alb)

                dur = QTableWidgetItem(format_time(t.duration_ms) + DUR_GAP)
                dur.setTextAlignment(Qt.AlignRight | Qt.AlignVCenter)
                self.table.setItem(r, 3, dur)

                self._rows.append({"num": num, "name": name, "dur": dur})

            has = bool(tracks)
            self.table.setVisible(has)
            self.empty_label.setVisible(not has)

            row_h = self.table.verticalHeader().defaultSectionSize()
            hh = self.table.horizontalHeader().height() or 30
            need = hh + len(tracks) * row_h + 4
            self.table.setFixedHeight(min(need, self.MAX_TABLE_H))
        finally:
            self.table.setUpdatesEnabled(True)
        if self._playing_track is not None:
            self.mark_playing(self._playing_track)
        self.table.viewport().update()

    def _refresh_rows(self):
        self.table.viewport().update()

    def update_row_cover(self, track: Track):
        for i, t in enumerate(self.current):
            if t is track or (track.path and t.path == track.path):
                if i < len(self._rows):
                    self._rows[i]["name"].setData(Qt.UserRole + 2, track.cover or "")
                    self.table.viewport().update()
                break

    def mark_playing(self, track: Optional[Track]):
        self._playing_track = track
        self._play_row = None
        if track is not None:
            for i, t in enumerate(self.current):
                if t is track or (track.path and t.path == track.path):
                    self._play_row = i
                    break
        self.row_delegate.play_row = self._play_row if self._play_row is not None else -1
        if self._play_row is not None:
            self.table.selectRow(self._play_row)
        else:
            self.table.clearSelection()
        self.table.viewport().update()

    def update_duration(self, track: Track):
        for i, t in enumerate(self.current):
            if t is track and i < len(self._rows):
                self._rows[i]["dur"].setText(format_time(track.duration_ms) + DUR_GAP)
                break


# ==========================================================================
# Глобальный поиск
# ==========================================================================
class SearchRowDelegate(QStyledItemDelegate):
    ROW = 46

    def sizeHint(self, opt, idx):
        return QSize(240, self.ROW)

    def paint(self, p, opt, idx):
        p.save()
        r = opt.rect
        if idx.data(Qt.UserRole + 9) == "hint":
            f = QFont(opt.font)
            f.setPixelSize(12)
            p.setFont(f)
            p.setPen(QColor(THEME["text_sec"]))
            p.drawText(r, Qt.AlignCenter, idx.data(Qt.DisplayRole) or "")
            p.restore()
            return

        sel = bool(opt.state & QStyle.State_Selected)
        hov = bool(opt.state & QStyle.State_MouseOver)
        if sel or hov:
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(THEME["menu_sel"] if sel else THEME["pop_row"]))
            p.drawRoundedRect(QRectF(r).adjusted(3, 2, -3, -2), 6, 6)
        if sel:
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(THEME["player"]))
            p.drawRoundedRect(QRectF(r.x() + 3, r.y() + 8, 3, r.height() - 16), 2, 2)

        cover = idx.data(Qt.UserRole + 2) or ""
        cx = r.x() + 12
        cy = r.y() + (r.height() - 32) // 2
        pm = load_pixmap(cover, 32)
        if pm is None:
            pm = icon_pixmap("note", 32)
        if pm is not None and not pm.isNull():
            p.drawPixmap(cx, cy, pm)
        else:
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(THEME["cover_ph"]))
            p.drawRoundedRect(QRectF(cx, cy, 32, 32), 4, 4)

        dur = idx.data(Qt.UserRole + 3) or ""
        fd = QFont(opt.font)
        fd.setPixelSize(11)
        fmd = QFontMetrics(fd)
        dw = fmd.horizontalAdvance(dur) + 4 if dur else 0

        tx = cx + 32 + 10
        tw = max(24, r.right() - tx - dw - 14)
        title = idx.data(Qt.DisplayRole) or ""
        artist = idx.data(Qt.UserRole + 1) or "—"

        ft = QFont(opt.font)
        ft.setPixelSize(13)
        ft.setWeight(QFont.DemiBold if sel else QFont.Normal)
        fa = QFont(opt.font)
        fa.setPixelSize(11)
        fmt = QFontMetrics(ft)
        fma = QFontMetrics(fa)
        th, ah = fmt.height(), fma.height()
        y0 = r.y() + max(0, (r.height() - (th + ah)) // 2)

        p.setRenderHint(QPainter.TextAntialiasing)
        p.setFont(ft)
        p.setPen(QColor(THEME["text_main"]))
        p.drawText(QRect(tx, y0, tw, th), Qt.AlignLeft | Qt.AlignVCenter,
                   fmt.elidedText(title, Qt.ElideRight, tw))
        p.setFont(fa)
        p.setPen(QColor(THEME["text_sec"]))
        p.drawText(QRect(tx, y0 + th, tw, ah), Qt.AlignLeft | Qt.AlignVCenter,
                   fma.elidedText(artist, Qt.ElideRight, tw))
        if dur:
            p.setFont(fd)
            p.setPen(QColor(THEME["text_sec"]))
            p.drawText(QRect(r.right() - dw - 14, r.y(), dw, r.height()),
                       Qt.AlignRight | Qt.AlignVCenter, dur)
        p.restore()


class SearchPopup(QWidget):
    play_requested = Signal(object)
    PAD = 8
    HEAD = 24
    MAX_ROWS = 7

    def __init__(self, field_widget):
        flags = (Qt.Tool | Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint
                 | Qt.NoDropShadowWindowHint | Qt.WindowDoesNotAcceptFocus)
        super().__init__(field_widget, flags)
        self.field_widget = field_widget
        self.setObjectName("searchPop")
        self.setAttribute(Qt.WA_TranslucentBackground, True)
        self.setAttribute(Qt.WA_ShowWithoutActivating, True)
        self.setFocusPolicy(Qt.NoFocus)
        self._rows = 1
        self._geo = None

        self.head = QLabel("", self)
        self.head.setObjectName("popHead")
        self.head.setFocusPolicy(Qt.NoFocus)
        self.head.setAttribute(Qt.WA_TransparentForMouseEvents, True)
        f = self.head.font()
        f.setPixelSize(11)
        self.head.setFont(f)

        self.list = QListWidget(self)
        self.list.setObjectName("searchPopList")
        self.list.setFocusPolicy(Qt.NoFocus)
        self.list.setSelectionMode(QAbstractItemView.SingleSelection)
        self.list.setUniformItemSizes(True)
        self.list.setMouseTracking(True)
        self.list.viewport().setMouseTracking(True)
        self.list.viewport().setFocusPolicy(Qt.NoFocus)
        self.list.setItemDelegate(SearchRowDelegate(self.list))
        self.list.setVerticalScrollMode(QAbstractItemView.ScrollPerPixel)
        self.list.setHorizontalScrollBarPolicy(Qt.ScrollBarAlwaysOff)
        self.list.setFrameShape(QFrame.NoFrame)
        self.list.doubleClicked.connect(lambda *_: self.activate_current())
        self.list.pressed.connect(self._on_pressed)

    def _on_pressed(self, idx):
        if not idx.isValid():
            return
        it = self.list.item(idx.row())
        if it is None or it.data(Qt.UserRole + 9) == "hint":
            return
        self.list.setCurrentRow(idx.row())

    def paintEvent(self, ev):
        p = QPainter(self)
        try:
            p.setRenderHint(QPainter.Antialiasing, True)
            body = QRectF(self.rect()).adjusted(self.PAD, self.PAD,
                                                -self.PAD, -self.PAD)
            for i, a in ((5, 16), (4, 22), (3, 28), (2, 34), (1, 40)):
                p.setPen(Qt.NoPen)
                p.setBrush(QColor(0, 0, 0, a))
                p.drawRoundedRect(body.adjusted(-i, -i, i, i), 12 + i, 12 + i)
            p.setBrush(QColor(THEME["pop_bg"]))
            p.setPen(QPen(QColor(THEME["pop_border"]), 1))
            p.drawRoundedRect(body, 11, 11)
            p.setPen(QPen(QColor(THEME["hline"]), 1))
            p.drawLine(QPointF(body.left() + 10, body.top() + self.HEAD),
                       QPointF(body.right() - 10, body.top() + self.HEAD))
        finally:
            p.end()

    def showEvent(self, ev):
        super().showEvent(ev)
        app = QApplication.instance()
        if app is not None:
            app.installEventFilter(self)

    def hideEvent(self, ev):
        app = QApplication.instance()
        if app is not None:
            app.removeEventFilter(self)
        super().hideEvent(ev)

    def eventFilter(self, obj, ev):
        if ev.type() == QEvent.MouseButtonPress and self.isVisible():
            try:
                gp = ev.globalPosition().toPoint()
            except Exception:
                return False
            if self.frameGeometry().contains(gp):
                return False
            fg = QRect(self.field_widget.mapToGlobal(QPoint(0, 0)),
                       self.field_widget.size())
            if not fg.contains(gp):
                self.hide()
        return False

    def set_results(self, tracks: List[Track]):
        self._rows = max(1, len(tracks))
        self.setUpdatesEnabled(False)
        try:
            self.list.setUpdatesEnabled(False)
            try:
                self.list.clear()
                if not tracks:
                    it = QListWidgetItem("Ничего не найдено")
                    it.setData(Qt.UserRole + 9, "hint")
                    it.setFlags(Qt.NoItemFlags)
                    self.list.addItem(it)
                    self.head.setText("Совпадений нет")
                else:
                    for t in tracks:
                        it = QListWidgetItem(t.title or "—")
                        it.setData(Qt.UserRole + 1, t.artist or "—")
                        it.setData(Qt.UserRole + 2, t.cover or "")
                        it.setData(Qt.UserRole + 3,
                                   format_time(t.duration_ms) if t.duration_ms else "")
                        it.setData(Qt.UserRole + 10, t)
                        self.list.addItem(it)
                    self.list.setCurrentRow(0)
                    self.head.setText(
                        f"Найдено: {len(tracks)}")
            finally:
                self.list.setUpdatesEnabled(True)
            self._apply_geometry()
        finally:
            self.setUpdatesEnabled(True)
        if not self.isVisible():
            self.show()
            self.raise_()
        self.update()
        self.list.viewport().update()

    def _apply_geometry(self):
        f = self.field_widget
        rows = max(1, min(self._rows, self.MAX_ROWS))
        body_w = max(340, f.width() + 40)
        body_h = self.HEAD + rows * SearchRowDelegate.ROW + 8
        w = int(body_w + self.PAD * 2)
        h = int(body_h + self.PAD * 2)
        below = f.mapToGlobal(QPoint(0, f.height()))
        above = f.mapToGlobal(QPoint(0, 0))
        scr = QApplication.screenAt(below) or QApplication.primaryScreen()
        ag = scr.availableGeometry() if scr else QRect(0, 0, 1920, 1080)
        space_below = ag.bottom() - below.y()
        space_above = above.y() - ag.top()
        if h <= space_below:
            y = below.y() + 2 - self.PAD
        elif h <= space_above:
            y = above.y() - h + self.PAD - 2
        elif space_below >= space_above:
            y = max(ag.top(), ag.bottom() - h)
        else:
            y = ag.top()
        x = below.x() - self.PAD - 20
        x = max(ag.left(), min(x, ag.right() - w))
        geo = (int(x), int(y), w, h)
        if geo != self._geo:
            self._geo = geo
            self.setGeometry(*geo)
        self.head.setGeometry(self.PAD + 12, self.PAD + 5,
                              body_w - 24, self.HEAD - 10)
        self.list.setGeometry(self.PAD + 6, self.PAD + self.HEAD,
                              body_w - 12, rows * SearchRowDelegate.ROW + 2)

    def move_selection(self, delta: int):
        n = self.list.count()
        if n <= 0:
            return
        row = self.list.currentRow()
        if row < 0:
            row = 0 if delta > 0 else n - 1
        else:
            row = max(0, min(n - 1, row + delta))
        it = self.list.item(row)
        if it is not None and it.data(Qt.UserRole + 9) == "hint":
            return
        self.list.setCurrentRow(row)
        self.list.scrollToItem(it, QAbstractItemView.EnsureVisible)

    def activate_current(self):
        it = self.list.currentItem()
        if it is None or it.data(Qt.UserRole + 9) == "hint":
            return
        tr = it.data(Qt.UserRole + 10)
        if tr is not None:
            self.hide()
            self.play_requested.emit(tr)


class TrackSearchField(QLineEdit):
    play_requested = Signal(object)

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("topSearch")
        self.setPlaceholderText("Поиск трека…")
        self.setClearButtonEnabled(False)
        self.setFocusPolicy(Qt.ClickFocus)
        self.tracks: List[Track] = []
        self.popup = SearchPopup(self)
        self.popup.play_requested.connect(self._on_play)
        self._timer = QTimer(self)
        self._timer.setSingleShot(True)
        self._timer.setInterval(90)
        self._timer.timeout.connect(self._rebuild)
        self.textChanged.connect(lambda *_: self._timer.start())

    def set_tracks(self, tracks: List[Track]):
        self.tracks = list(tracks)
        if self.popup.isVisible():
            self._rebuild()

    def _rebuild(self):
        q = self.text().strip().lower()
        if not q:
            self.popup.hide()
            return
        out = []
        for t in self.tracks:
            if (q in (t.title or "").lower()
                    or q in (t.artist or "").lower()
                    or q in (t.album or "").lower()):
                out.append(t)
                if len(out) >= 60:
                    break
        self.popup.set_results(out)

    def _on_play(self, tr):
        self.popup.hide()
        self.play_requested.emit(tr)

    def hide_popup(self):
        self.popup.hide()

    def reset(self):
        self._timer.stop()
        self.blockSignals(True)
        self.clear()
        self.blockSignals(False)
        self.popup.hide()
        self.clearFocus()

    def focusInEvent(self, ev):
        super().focusInEvent(ev)
        if self.text().strip():
            self._rebuild()

    def keyPressEvent(self, ev):
        k = ev.key()
        if k in (Qt.Key_Down, Qt.Key_Up):
            if not self.popup.isVisible():
                self._rebuild()
            if self.popup.isVisible():
                self.popup.move_selection(1 if k == Qt.Key_Down else -1)
            ev.accept()
            return
        if k in (Qt.Key_PageDown, Qt.Key_PageUp):
            if self.popup.isVisible():
                self.popup.move_selection(6 if k == Qt.Key_PageDown else -6)
            ev.accept()
            return
        if k in (Qt.Key_Return, Qt.Key_Enter):
            if self.popup.isVisible():
                self.popup.activate_current()
                ev.accept()
                return
        if k == Qt.Key_Escape:
            self.reset()
            ev.accept()
            return
        super().keyPressEvent(ev)


class TopBarPanel(QWidget):
    SEARCH_MAX_W = 360

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("topBar")
        self.setFixedHeight(38)
        self.center_widget = None
        self.left_anchor = None
        self.right_anchor = None

    def set_center(self, w, left_anchor, right_anchor):
        self.center_widget = w
        self.left_anchor = left_anchor
        self.right_anchor = right_anchor
        self._place()
        QTimer.singleShot(0, self._place)

    def _place(self):
        cw = self.center_widget
        if cw is None:
            return
        la = self.left_anchor.geometry().right() if self.left_anchor else 8
        ra = (self.right_anchor.geometry().left() if self.right_anchor
              else self.width() - 8)
        avail = ra - la - 24
        if avail < 210:
            cw.hide_popup()
            cw.hide()
            return
        w = int(min(self.SEARCH_MAX_W, avail - 70))
        if w < 170:
            cw.hide_popup()
            cw.hide()
            return
        h = 26
        x = (self.width() - w) // 2
        x = max(la + 15, min(x, ra - 15 - w))
        y = (self.height() - h) // 2
        geo = QRect(int(x), int(y), w, h)
        if cw.geometry() != geo:
            cw.hide_popup()
            cw.setGeometry(geo)
        cw.show()

    def resizeEvent(self, e):
        super().resizeEvent(e)
        self._place()
        QTimer.singleShot(0, self._place)


# ==========================================================================
# Нижняя панель (без подсказок)
# ==========================================================================
class MarqueeLabel(QLabel):
    SPEED_PX = 0.55
    TICK_MS = 30
    PAUSE_TICKS = 45
    GAP_PX = 48

    def __init__(self, text: str = "", parent=None):
        super().__init__(parent)
        self._full = text or ""
        self._offset = 0.0
        self._pause = self.PAUSE_TICKS
        self._need_scroll = False
        self._text_w = 0
        self._color = QColor("#1f2328")
        self.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Maximum)
        self.setMinimumWidth(40)
        self._timer = QTimer(self)
        self._timer.setInterval(self.TICK_MS)
        self._timer.timeout.connect(self._tick)

    def set_text_color(self, color: str):
        self._color = QColor(color)
        self.update()

    def setText(self, text: str):
        self._full = text or ""
        self._offset = 0.0
        self._pause = self.PAUSE_TICKS
        self._recalc()
        self.update()

    def text(self) -> str:
        return self._full

    def resizeEvent(self, e):
        super().resizeEvent(e)
        self._recalc()

    def showEvent(self, e):
        super().showEvent(e)
        self._recalc()

    def _recalc(self):
        if self.width() <= 0:
            return
        fm = self.fontMetrics()
        self._text_w = fm.horizontalAdvance(self._full) if self._full else 0
        need = self._text_w > self.width() + 2 and bool(self._full)
        if need != self._need_scroll:
            self._need_scroll = need
            self._offset = 0.0
            self._pause = self.PAUSE_TICKS
        if need:
            if not self._timer.isActive():
                self._timer.start()
        else:
            self._timer.stop()
            self._offset = 0.0

    def _tick(self):
        if not self._need_scroll:
            self._timer.stop()
            return
        if self._pause > 0:
            self._pause -= 1
            return
        cycle = self._text_w + self.GAP_PX
        self._offset += self.SPEED_PX
        if self._offset >= cycle:
            self._offset = 0.0
            self._pause = self.PAUSE_TICKS
        self.update()

    def paintEvent(self, event):
        p = QPainter(self)
        try:
            p.setRenderHint(QPainter.TextAntialiasing)
            p.setClipRect(self.rect())
            p.setFont(self.font())
            p.setPen(self._color)
            fm = self.fontMetrics()
            y = (self.height() + fm.ascent() - fm.descent()) // 2
            if not self._need_scroll:
                p.drawText(0, y, self._full)
                return
            x = -int(self._offset)
            p.drawText(x, y, self._full)
            p.drawText(x + self._text_w + self.GAP_PX, y, self._full)
        finally:
            p.end()


class PlayerBar(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setObjectName("playerBar")
        self.setFixedHeight(78)
        h = QHBoxLayout(self)
        h.setContentsMargins(12, 6, 12, 6)
        h.setSpacing(12)

        self._left_w = QWidget()
        self._left_w.setFixedWidth(190)
        self._left_w.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Preferred)
        self._left_w.setAttribute(Qt.WA_StyledBackground, True)
        ll = QHBoxLayout(self._left_w)
        ll.setContentsMargins(0, 0, 0, 0)
        ll.setSpacing(8)

        self.cover_lbl = QLabel()
        self.cover_lbl.setFixedSize(46, 46)
        info_w = QWidget()
        info_w.setFixedWidth(190 - 46 - 8)
        info_w.setSizePolicy(QSizePolicy.Fixed, QSizePolicy.Preferred)
        info = QVBoxLayout(info_w)
        info.setContentsMargins(0, 0, 0, 0)
        info.setSpacing(0)
        info.setAlignment(Qt.AlignVCenter)

        self.title_lbl = MarqueeLabel("—")
        self.title_lbl.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Maximum)
        self.title_lbl.setMaximumWidth(190 - 46 - 8)
        self.artist_lbl = QLabel("")
        self.artist_lbl.setSizePolicy(QSizePolicy.Ignored, QSizePolicy.Maximum)
        self.artist_lbl.setMaximumWidth(190 - 46 - 8)
        self.artist_lbl.setTextInteractionFlags(Qt.NoTextInteraction)
        info.addWidget(self.title_lbl)
        info.addWidget(self.artist_lbl)
        ll.addWidget(self.cover_lbl)
        ll.addWidget(info_w, 1)
        h.addWidget(self._left_w, 0)

        cv = QVBoxLayout()
        cv.setContentsMargins(0, 4, 0, 0)
        cv.setSpacing(6)
        transport = QHBoxLayout()
        transport.setSpacing(10)
        transport.addStretch()

        self.btn_random = make_flat_button()
        self.btn_random.setCheckable(True)
        self.btn_random.setIconSize(QSize(20, 20))
        self.btn_prev = make_flash_button()
        self.btn_prev.setIconSize(QSize(22, 22))
        self.btn_play = make_flash_button()
        self.btn_play.setIconSize(QSize(22, 22))
        self.btn_next = make_flash_button()
        self.btn_next.setIconSize(QSize(22, 22))
        self.btn_rotate1 = make_flat_button()
        self.btn_rotate1.setCheckable(True)
        self.btn_rotate1.setIconSize(QSize(20, 20))
        for b in (self.btn_random, self.btn_prev, self.btn_play,
                  self.btn_next, self.btn_rotate1):
            transport.addWidget(b)
        transport.addStretch()

        prog = QHBoxLayout()
        prog.setSpacing(8)
        self.time_cur = QLabel("0:00")
        self.time_cur.setObjectName("timeLabel")
        self.time_cur.setAlignment(Qt.AlignRight | Qt.AlignVCenter)
        self.time_cur.setMinimumWidth(38)
        self.progress = ClickSlider(Qt.Horizontal)
        self.progress.setRange(0, 0)
        self.progress.setFocusPolicy(Qt.NoFocus)
        self.time_tot = QLabel("0:00")
        self.time_tot.setObjectName("timeLabel")
        self.time_tot.setMinimumWidth(38)
        prog.addWidget(self.time_cur)
        prog.addWidget(self.progress, 1)
        prog.addWidget(self.time_tot)

        cv.addLayout(transport)
        cv.addLayout(prog)
        h.addLayout(cv, 1)

        right = QWidget()
        right.setFixedWidth(190)
        rl = QHBoxLayout(right)
        rl.setContentsMargins(0, 0, 0, 0)
        rl.setSpacing(6)
        rl.addStretch()
        self.btn_mute = make_flat_button()
        self.btn_mute.setIconSize(QSize(20, 20))
        self.volume = ClickSlider(Qt.Horizontal)
        self.volume.setRange(0, 100)
        self.volume.setFixedWidth(100)
        self.volume.setFocusPolicy(Qt.NoFocus)
        self.volume.valueChanged.connect(lambda v: self.update_volume_icon())
        rl.addWidget(self.btn_mute)
        rl.addWidget(self.volume)
        h.addWidget(right)

        self._ic_play = None
        self._ic_pause = None
        self._base_mute = None
        self._base_small = None
        self._base_full = None
        self._muted_state = False
        self._playing_state = False
        self.apply_styles()
        self.refresh_icons()

    def apply_styles(self):
        self.title_lbl.setStyleSheet(
            "font-size: 13px; font-weight: 600; background: transparent;")
        if hasattr(self.title_lbl, "set_text_color"):
            self.title_lbl.set_text_color(THEME["text_main"])
        f = self.title_lbl.font()
        f.setPixelSize(13)
        f.setWeight(QFont.DemiBold)
        self.title_lbl.setFont(f)
        self.artist_lbl.setStyleSheet(artist_css())
        self.cover_lbl.setStyleSheet(cover_css())

    def refresh_icons(self):
        dark = bool(THEME.get("dark", False))

        def tinted(base, size, force=None):
            if base is None:
                return None
            col = force if force else ("#ffffff" if dark else None)
            if col:
                return tint_icon(base, col, size * 2)
            return base

        base_play = custom_icon("button-play") or IC.get("play")
        base_pause = custom_icon("button-pause") or IC.get("pause")
        base_back = custom_icon("button-back") or IC.get("prev")
        base_next = custom_icon("button-next") or IC.get("next")
        base_random = custom_icon("button-random") or IC.get("random")
        base_rotate = custom_icon("button-rotate1") or IC.get("rotate1")
        self._base_mute = custom_icon("music-mute") or IC.get("muted")
        self._base_small = custom_icon("music-volume-small") or IC.get("volume")
        self._base_full = custom_icon("music-volume-full") or IC.get("volume")

        self._ic_play = tinted(base_play, 22)
        self._ic_pause = tinted(base_pause, 22)
        self.btn_prev.set_icon(tinted(base_back, 22))
        self.btn_next.set_icon(tinted(base_next, 22))
        apply_icon(self.btn_random,
                   tinted(base_random, 20,
                          GREEN if self.btn_random.isChecked() else None))
        apply_icon(self.btn_rotate1,
                   tinted(base_rotate, 20,
                          GREEN if self.btn_rotate1.isChecked() else None))
        self.set_play_icon(self._playing_state)
        self.update_volume_icon()

    def set_play_icon(self, playing: bool):
        self._playing_state = bool(playing)
        self.btn_play.set_icon(self._ic_pause if playing else self._ic_play)

    def set_mute_icon(self, muted: bool):
        self._muted_state = bool(muted)
        self.update_volume_icon()

    def update_volume_icon(self):
        dark = bool(THEME.get("dark", False))
        val = self.volume.value()
        if self._muted_state or val == 0:
            base = self._base_mute
        elif val <= 50:
            base = self._base_small
        else:
            base = self._base_full
        ic = tint_icon(base, "#ffffff", 40) if dark else base
        apply_icon(self.btn_mute, ic)

    def set_track_info(self, track: Optional[Track]):
        if track is None:
            self.title_lbl.setText("—")
            self.artist_lbl.setText("")
            self.cover_lbl.clear()
            return
        self.title_lbl.setText(track.title)
        sub = track.album or track.artist or "—"
        fm = self.artist_lbl.fontMetrics()
        max_w = max(40, self.artist_lbl.maximumWidth())
        self.artist_lbl.setText(fm.elidedText(sub, Qt.ElideRight, max_w))
        pm = load_pixmap(track.cover, 46)
        if pm is not None and not pm.isNull():
            self.cover_lbl.setPixmap(pm)
        else:
            self.cover_lbl.clear()


# ==========================================================================
# Главное окно
# ==========================================================================
class MainWindow(QMainWindow):
    COMPACT_MIN_W = 580
    COMPACT_PREF_W = 640
    SNAP_PX = 28
    EDGE = 6

    def __init__(self):
        super().__init__()
        self.setWindowTitle("LALALAAA")
        if IS_WINDOWS:
            self.setWindowFlags(Qt.Window | Qt.FramelessWindowHint
                                | Qt.WindowSystemMenuHint
                                | Qt.WindowMinimizeButtonHint
                                | Qt.WindowMaximizeButtonHint
                                | Qt.WindowCloseButtonHint)
        self._start_maximized = False
        self._hlines: List[QFrame] = []
        self._settings_dlg = None
        self._compact = False
        self._pre_compact_h = 0
        self._pre_compact_w = 0
        self._pre_compact_max = False
        self._snap_lock = False
        self._cover_threads = set()
        self._cover_jobs = set()
        self._hotkey_ids = []
        self._hotkeys_registered = False
        self._drag_offset = None

        self.config = Config(CONFIG_PATH)
        self.library = Library()
        self.library.load_from_dict(self.config.data)
        self.stats: dict = dict(self.config.data.get("play_stats") or {})
        self.no_cover: set = set(self.config.data.get("no_cover") or [])
        self._sanitize_library()
        self.queue: List[Track] = []
        self.current_index = -1
        self.focus_row = 0
        self.focus_cover = ""
        self._stopped = True
        self._tag_thread = None
        self._pending_seek: Optional[int] = None

        central = QWidget()
        central.setObjectName("centralWidget")
        root = QVBoxLayout(central)
        root.setContentsMargins(0, 0, 0, 0)
        root.setSpacing(0)

        top = TopBarPanel(self)
        self.top_bar = top
        tl = QHBoxLayout(top)
        tl.setContentsMargins(8, 2, 6, 2)
        tl.setSpacing(2)
        self.btn_file = make_flat_button("Файл")
        file_menu = QMenu(self)
        file_menu.addAction("Выбрать папку источника…").triggered.connect(
            self.choose_new_source)
        self.btn_file.setMenu(file_menu)
        self.btn_settings = make_flat_button("Настройки")
        self.btn_settings.clicked.connect(self.open_settings)
        tl.addWidget(self.btn_file)
        tl.addWidget(self.btn_settings)
        tl.addStretch()

        self.btn_compact = make_caption_button("capCompact", IC.get("mini"), self)
        self.btn_compact.setCheckable(True)
        self.btn_compact.toggled.connect(self.set_compact)
        self.cap_min = make_caption_button("capMin", IC.get("cap_min"), self)
        self.cap_min.clicked.connect(self.showMinimized)
        self.cap_max = make_caption_button("capMax", IC.get("cap_max"), self)
        self.cap_max.clicked.connect(self._toggle_max)
        self.cap_close = make_caption_button("capClose", IC.get("cap_close"), self)
        self.cap_close.clicked.connect(self.close)
        for b in (self.btn_compact, self.cap_min, self.cap_max, self.cap_close):
            tl.addWidget(b)

        self.top_search = TrackSearchField(top)
        self.top_search.play_requested.connect(self.play_from_search)
        top.set_center(self.top_search, self.btn_settings, self.btn_compact)

        root.addWidget(top)
        self._hlines.append(make_hline())
        root.addWidget(self._hlines[-1])

        self.splitter = QSplitter(Qt.Horizontal)
        self.playlist_panel = PlaylistPanel()
        self.tracks_panel = TracksPanel()
        self.now_panel = NowPlayingPanel()
        self.splitter.addWidget(self.playlist_panel)
        self.splitter.addWidget(self.tracks_panel)
        self.splitter.addWidget(self.now_panel)
        self.splitter.setChildrenCollapsible(False)
        self.splitter.setHandleWidth(2)
        self.playlist_panel.setMinimumWidth(170)
        self.tracks_panel.setMinimumWidth(320)
        self.now_panel.setVisible(False)
        root.addWidget(self.splitter, 1)
        self._hlines.append(make_hline())
        root.addWidget(self._hlines[-1])

        self.player_bar = PlayerBar()
        root.addWidget(self.player_bar)

        self.setCentralWidget(central)

        self.audio = None
        self.player = None
        if HAS_MULTIMEDIA:
            try:
                self.audio = QAudioOutput(self)
                self.player = QMediaPlayer(self)
                self.player.setAudioOutput(self.audio)
                self.player.positionChanged.connect(self._on_position)
                self.player.durationChanged.connect(self._on_duration)
                self.player.playbackStateChanged.connect(self._update_play_icon)
                self.player.mediaStatusChanged.connect(self._on_media_status)
                self.player.metaDataChanged.connect(self._on_meta_data)
                self.player.errorOccurred.connect(self._on_player_error)
            except Exception as e:
                print("[LALALAAA] Ошибка создания плеера:", e)
                self.audio = None
                self.player = None

        self._connect_signals()
        self._apply_settings()
        self.playlist_panel.reload(self.library.playlists)
        self.top_search.set_tracks(self.library.tracks)

        self._click_filter = ClickAwayFilter(self)
        app = QApplication.instance()
        if app is not None:
            app.installEventFilter(self._click_filter)

        QTimer.singleShot(0, self._prepare_settings)
        QTimer.singleShot(0, self._drop_initial_focus)
        QTimer.singleShot(30, self._start_tag_refresh)

    def _drop_initial_focus(self):
        self.top_search.clearFocus()
        self.tracks_panel.banner.search.clearFocus()
        self.centralWidget().setFocus()

    # ------------------------------------------------------------- поиски
    def dismiss_all_searches(self):
        try:
            self.top_search.reset()
        except Exception:
            pass
        try:
            self.tracks_panel.banner.reset_search()
        except Exception:
            pass

    def dismiss_searches_outside(self, gp: QPoint):
        ts = self.top_search
        if ts.isVisible():
            r = QRect(ts.mapToGlobal(QPoint(0, 0)), ts.size())
            if r.contains(gp):
                return
            if ts.popup.isVisible() and ts.popup.frameGeometry().contains(gp):
                return
        bs = self.tracks_panel.banner.search
        if bs.isVisible():
            r = QRect(bs.mapToGlobal(QPoint(0, 0)), bs.size())
            if r.contains(gp):
                return
        self.dismiss_all_searches()

    # ------------------------------------------------------------- медиа-клавиши
    def _register_media_hotkeys(self):
        if not IS_WINDOWS or self._hotkeys_registered:
            return
        try:
            hwnd = int(self.winId())
            u = ctypes.windll.user32
            for hid, vk in MEDIA_HOTKEYS.items():
                done = False
                for mods in (MOD_NOREPEAT, 0):
                    try:
                        if u.RegisterHotKey(hwnd, hid, mods, vk):
                            self._hotkey_ids.append(hid)
                            done = True
                            break
                    except Exception:
                        pass
                if not done:
                    print("[LALALAAA] Медиа-клавиша занята другой программой:",
                          hex(vk))
            self._hotkeys_registered = bool(self._hotkey_ids)
            if self._hotkeys_registered:
                print("[LALALAAA] Медиа-клавиши зарегистрированы глобально.")
        except Exception as e:
            print("[LALALAAA] Медиа-клавиши:", e)

    def _unregister_media_hotkeys(self):
        if IS_WINDOWS and self._hotkey_ids:
            try:
                hwnd = int(self.winId())
                u = ctypes.windll.user32
                for hid in self._hotkey_ids:
                    try:
                        u.UnregisterHotKey(hwnd, hid)
                    except Exception:
                        pass
            except Exception:
                pass
            self._hotkey_ids = []
            self._hotkeys_registered = False

    def _media_play_pause(self):
        self.toggle_play()

    def _media_play(self):
        if self.player is None:
            return
        if self.player.playbackState() != QMediaPlayer.PlayingState:
            self.toggle_play()

    def _media_pause(self):
        if self.player is None:
            return
        if self.player.playbackState() == QMediaPlayer.PlayingState:
            self.player.pause()

    def _handle_media_command(self, cmd: str):
        if cmd == "toggle":
            self._media_play_pause()
        elif cmd == "play":
            self._media_play()
        elif cmd == "pause":
            self._media_pause()
        elif cmd == "stop":
            self.stop()
        elif cmd == "next":
            self.switch_track(+1)
        elif cmd == "prev":
            self.switch_track(-1)
        else:
            return False
        return True

    # ------------------------------------------------------------- хром окна
    def _toggle_max(self):
        if self._compact:
            return
        if self.isMaximized():
            self.showNormal()
        else:
            self.showMaximized()

    def changeEvent(self, ev):
        super().changeEvent(ev)
        if ev.type() == QEvent.WindowStateChange:
            self._refresh_cap_max()
            if self._compact and self.isMaximized():
                QTimer.singleShot(0, self._undo_max_in_compact)
            if self.isMinimized():
                self.top_search.hide_popup()

    def _undo_max_in_compact(self):
        if self._compact and self.isMaximized():
            self.showNormal()

    def _refresh_cap_max(self):
        if self.isMaximized():
            apply_icon(self.cap_max,
                       caption_icon("restore", THEME["icon_fg"], CAP_ICON))
        else:
            apply_icon(self.cap_max,
                       caption_icon("max", THEME["icon_fg"], CAP_ICON))

    def _refresh_caption_icons(self):
        apply_icon(self.cap_min, caption_icon("min", THEME["icon_fg"], CAP_ICON))
        apply_icon(self.cap_close,
                   caption_icon("close", THEME["icon_fg"], CAP_ICON))
        self._refresh_cap_max()

    def nativeEvent(self, eventType, message):
        if IS_WINDOWS and eventType == b"windows_generic_MSG":
            try:
                msg = wintypes.MSG.from_address(int(message))
            except Exception:
                return super().nativeEvent(eventType, message)

            # клик по «свободной» части окна (HTCAPTION) не даёт Qt-события
            # мыши — снимаем фокус поисков здесь, иначе в компакте он залипает
            if msg.message in (WM_NCLBUTTONDOWN, WM_NCLBUTTONDBLCLK,
                               WM_NCRBUTTONDOWN):
                QTimer.singleShot(0, self.dismiss_all_searches)

            if msg.message == WM_HOTKEY:
                hid = int(msg.wParam)
                vk = MEDIA_HOTKEYS.get(hid)
                if vk == VK_MEDIA_PLAY_PAUSE:
                    self._media_play_pause()
                    return True, 0
                if vk == VK_MEDIA_PREV_TRACK:
                    self.switch_track(-1)
                    return True, 0
                if vk == VK_MEDIA_NEXT_TRACK:
                    self.switch_track(+1)
                    return True, 0
                if vk == VK_MEDIA_STOP:
                    self.stop()
                    return True, 0

            if msg.message == WM_APPCOMMAND:
                cmd = (int(msg.lParam) >> 16) & 0x0FFF
                mapping = {
                    APPCMD_MEDIA_PLAY_PAUSE: "toggle",
                    APPCMD_MEDIA_NEXT: "next",
                    APPCMD_MEDIA_PREV: "prev",
                    APPCMD_MEDIA_STOP: "stop",
                }
                act = mapping.get(cmd)
                if act and self._handle_media_command(act):
                    return True, 0

            if msg.message == WM_SYSCOMMAND:
                cmd = int(msg.wParam) & 0xFFF0
                if cmd == SC_MINIMIZE:
                    self.showMinimized()
                    return True, 0
                if cmd == SC_RESTORE:
                    if self.isMinimized():
                        self.showNormal()
                    elif self.isMaximized() and not self._compact:
                        self.showNormal()
                    return True, 0
                if cmd == SC_MAXIMIZE:
                    if self._compact:
                        return True, 0
                    self.showMaximized()
                    return True, 0

            if msg.message == WM_NCHITTEST:
                gx = ctypes.c_short(msg.lParam & 0xFFFF).value
                gy = ctypes.c_short((msg.lParam >> 16) & 0xFFFF).value
                pos = self.mapFromGlobal(QPoint(gx, gy))
                r = self.rect()
                b = self.EDGE
                if not self.isMaximized():
                    left = pos.x() <= b
                    right = pos.x() >= r.width() - b
                    top = pos.y() <= b
                    bottom = pos.y() >= r.height() - b
                    if top and left:
                        return True, HTTOPLEFT
                    if top and right:
                        return True, HTTOPRIGHT
                    if bottom and left:
                        return True, HTBOTTOMLEFT
                    if bottom and right:
                        return True, HTBOTTOMRIGHT
                    if left:
                        return True, HTLEFT
                    if right:
                        return True, HTRIGHT
                    if top:
                        return True, HTTOP
                    if bottom:
                        return True, HTBOTTOM
                w = self.childAt(pos)
                if self._compact:
                    if not is_interactive_widget(w):
                        return True, HTCAPTION
                else:
                    tb = self.top_bar
                    if tb.isVisible() and tb.geometry().contains(pos):
                        if w is None or w is tb or isinstance(w, QLabel):
                            return True, HTCAPTION
                return True, HTCLIENT

            if msg.message == WM_GETMINMAXINFO:
                try:
                    info = _MINMAXINFO.from_address(msg.lParam)
                    scr = self.screen() or QApplication.primaryScreen()
                    if scr is not None:
                        ag = scr.availableGeometry()
                        fg = scr.geometry()
                        info.ptMaxPosition.x = ag.x() - fg.x()
                        info.ptMaxPosition.y = ag.y() - fg.y()
                        info.ptMaxSize.x = ag.width()
                        info.ptMaxSize.y = ag.height()
                        info.ptMaxTrackSize.x = ag.width()
                        info.ptMaxTrackSize.y = ag.height()
                    info.ptMinTrackSize.x = 480
                    info.ptMinTrackSize.y = 200
                except Exception:
                    pass
                return True, 0
        return super().nativeEvent(eventType, message)

    def mousePressEvent(self, ev):
        if (self._compact and not IS_WINDOWS
                and ev.button() == Qt.LeftButton):
            w = self.childAt(ev.position().toPoint())
            if not is_interactive_widget(w):
                self.dismiss_all_searches()
                self._drag_offset = (ev.globalPosition().toPoint()
                                     - self.frameGeometry().topLeft())
                ev.accept()
                return
        super().mousePressEvent(ev)

    def mouseMoveEvent(self, ev):
        if self._drag_offset is not None:
            self.move(ev.globalPosition().toPoint() - self._drag_offset)
            ev.accept()
            return
        super().mouseMoveEvent(ev)

    def mouseReleaseEvent(self, ev):
        if self._drag_offset is not None:
            self._drag_offset = None
            ev.accept()
            return
        super().mouseReleaseEvent(ev)

    # ------------------------------------------------------------- настройки
    def _prepare_settings(self):
        if self._settings_dlg is None:
            self._settings_dlg = SettingsDialog(self)
            self._settings_dlg.ensurePolished()

    def open_settings(self):
        self.dismiss_all_searches()
        self._prepare_settings()
        self._settings_dlg.refresh()
        self._settings_dlg.show()
        self._settings_dlg.raise_()
        self._settings_dlg.activateWindow()

    # ------------------------------------------------------------- компакт
    def set_compact(self, on: bool):
        self._compact = bool(on)
        self.dismiss_all_searches()
        self.splitter.setVisible(not on)
        if len(self._hlines) > 1:
            self._hlines[1].setVisible(not on)
        if on:
            self._pre_compact_h = self.height()
            self._pre_compact_w = self.width()
            self._pre_compact_max = self.isMaximized()
            if self._pre_compact_max:
                self.showNormal()
            hh = (self.top_bar.height() + self._hlines[0].height()
                  + self.player_bar.height())
            self.setMinimumHeight(hh)
            self.setMaximumHeight(hh)
            self.setMinimumWidth(self.COMPACT_MIN_W)
            self.setMaximumWidth(16777215)
            cur_w = self.width()
            target_w = self.COMPACT_PREF_W if cur_w > self.COMPACT_PREF_W else cur_w
            target_w = max(self.COMPACT_MIN_W, target_w)
            self.resize(target_w, hh)
            self._snap_to_edges(force=False)
        else:
            self.setMinimumHeight(0)
            self.setMaximumHeight(16777215)
            self.setMinimumWidth(0)
            self.setMaximumWidth(16777215)
            w = getattr(self, "_pre_compact_w", None) or 1150
            self.resize(int(w), self._pre_compact_h or 650)
            if self._pre_compact_max:
                self.showMaximized()
        self.cap_max.setEnabled(not self._compact)
        self._update_compact_icon()
        self._refresh_cap_max()
        self.top_bar._place()

    def _screen_avail(self):
        try:
            screen = self.screen() or QApplication.primaryScreen()
            if screen is not None:
                return screen.availableGeometry()
        except Exception:
            pass
        return QRect(0, 0, 1920, 1080)

    def _snap_to_edges(self, force: bool = False):
        if not self._compact:
            return
        avail = self._screen_avail()
        geo = self.frameGeometry()
        x, y = geo.x(), geo.y()
        w, h = geo.width(), geo.height()
        th = self.SNAP_PX
        changed = False
        if force or abs(x - avail.left()) <= th:
            x = avail.left(); changed = True
        elif force or abs(x + w - avail.right()) <= th:
            x = avail.right() - w; changed = True
        if force or abs(y - avail.top()) <= th:
            y = avail.top(); changed = True
        elif force or abs(y + h - avail.bottom()) <= th:
            y = avail.bottom() - h; changed = True
        if changed and (x != geo.x() or y != geo.y()):
            self.move(x, y)

    def moveEvent(self, event):
        super().moveEvent(event)
        self.top_search.hide_popup()
        if self._compact and not getattr(self, "_snap_lock", False):
            if not hasattr(self, "_snap_timer"):
                self._snap_timer = QTimer(self)
                self._snap_timer.setSingleShot(True)
                self._snap_timer.setInterval(120)
                self._snap_timer.timeout.connect(self._on_snap_timeout)
            self._snap_timer.start()

    def resizeEvent(self, event):
        super().resizeEvent(event)
        if hasattr(self, "top_search"):
            self.top_search.hide_popup()

    def _on_snap_timeout(self):
        if not self._compact:
            return
        self._snap_lock = True
        try:
            self._snap_to_edges(force=False)
        finally:
            self._snap_lock = False

    def _update_compact_icon(self):
        base = custom_icon("mini_and_full", panel="u")
        col = GREEN if self.btn_compact.isChecked() else THEME["icon_fg"]
        if base is not None:
            ic = crisp_icon(base, col, CAP_ICON)
        else:
            ic = drawn_icon(d_mini, col, CAP_ICON)
        apply_icon(self.btn_compact, ic)

    # ------------------------------------------------------------- темы
    def apply_theme(self, dark: bool):
        set_theme(bool(dark))
        build_icons()
        app = QApplication.instance()
        if app is not None:
            app.setStyleSheet(build_stylesheet())
            app.setWindowIcon(IC.get("app") or QIcon())
        for ln in self._hlines:
            ln.setStyleSheet(f"background: {THEME['hline']}; border: none;")
        self.playlist_panel.apply_styles()
        self.player_bar.apply_styles()
        self.player_bar.refresh_icons()
        self.tracks_panel.apply_styles()
        self.tracks_panel.banner.update()
        self.now_panel.apply_styles()
        self._refresh_caption_icons()
        self._update_compact_icon()
        if self.top_search.popup.isVisible():
            self.top_search.popup.update()
        if self._settings_dlg is not None:
            self._settings_dlg.header.apply_styles()
        self.config.settings["dark_theme"] = bool(dark)
        self.config.save()

    def apply_bg_zoom(self, on: bool):
        self.config.settings["bg_zoom"] = bool(on)
        self.tracks_panel.banner.set_zoom_enabled(bool(on))
        self.config.save()

    def apply_bg_pin(self, on: bool):
        self.config.settings["bg_pin"] = bool(on)
        self.tracks_panel.set_pinned(bool(on))
        self.config.save()

    def apply_hide_banner(self, on: bool):
        self.config.settings["hide_banner"] = bool(on)
        self.tracks_panel.set_banner_hidden(bool(on))
        self.config.save()

    def apply_no_cover_image(self, on: bool):
        self.config.settings["no_cover_image"] = bool(on)
        self.tracks_panel.banner.set_muted_mode(bool(on))
        self.config.save()

    def apply_follow_switch(self, on: bool):
        self.config.settings["follow_switch"] = bool(on)
        self.config.save()

    def apply_classic(self, on: bool):
        on = bool(on)
        self.config.settings["classic_view"] = on
        self.now_panel.setVisible(on)
        if on:
            sizes = self.splitter.sizes()
            total = sum(sizes) or self.width() or 1150
            left = sizes[0] if sizes and sizes[0] > 0 else 260
            right = 320
            center = max(360, total - left - right)
            self.splitter.setSizes([left, center, right])
            self.now_panel.set_track(self._current_track())
        self.config.save()

    # ------------------------------------------------------------- json/библиотека
    def _sanitize_library(self):
        changed = False
        seen = set()
        uniq = []
        for t in self.library.tracks:
            if t.path in seen:
                changed = True
                continue
            seen.add(t.path)
            uniq.append(t)
        self.library.tracks = uniq
        for t in self.library.tracks:
            for f in ("title", "artist", "album"):
                val = getattr(t, f, "") or ""
                if val.strip().lower() == "none":
                    setattr(t, f, "")
                    changed = True
            if not t.title and t.path:
                t.title = os.path.splitext(os.path.basename(t.path))[0]
                changed = True
        if changed:
            self.config.data.update(self.library.to_dict())
            self.config.save()

    def _prune_missing(self):
        keep = [t for t in self.library.tracks if os.path.exists(t.path)]
        if len(keep) != len(self.library.tracks):
            self.library.tracks = keep
            paths = {t.path for t in keep}
            for pl in self.library.playlists:
                pl.tracks = [t for t in pl.tracks if t.path in paths]
            self.stats = {k: v for k, v in self.stats.items() if k in paths}
            self.config.data["play_stats"] = self.stats
            self.no_cover = {p for p in self.no_cover if p in paths}
            self.config.data["no_cover"] = sorted(self.no_cover)
            return True
        return False

    def _start_tag_refresh(self):
        jobs = []
        self._cover_jobs = set()
        for t in self.library.tracks:
            if not t.path or not os.path.exists(t.path):
                continue
            need_tags = (not t.album) or (not t.artist) or (not t.duration_ms) \
                or (not t.year)
            need_cover = ((not t.cover) or (not _cover_usable(t.cover))) \
                and t.path not in self.no_cover
            if need_cover:
                self._cover_jobs.add(t.path)
            if need_tags or need_cover:
                jobs.append((t.path, need_tags, need_cover))
        if not jobs:
            return
        self._tag_thread = TagRefreshThread(jobs, self)
        self._tag_thread.setPriority(QThread.LowPriority)
        self._tag_thread.finished_results.connect(self._apply_tag_results)
        self._tag_thread.start()

    def _apply_tag_results(self, results):
        by_path = {t.path: t for t in self.library.tracks}
        changed = False
        cur = self._current_track()
        for path, tags, cover in results:
            t = by_path.get(path)
            if t is None:
                continue
            if tags.get("album") and not t.album:
                t.album = tags["album"]; changed = True
            if tags.get("artist") and not t.artist:
                t.artist = tags["artist"]; changed = True
            if tags.get("title") and not t.title:
                t.title = tags["title"]; changed = True
            if tags.get("year") and not t.year:
                t.year = tags["year"]; changed = True
            if tags.get("duration_ms") and not t.duration_ms:
                t.duration_ms = tags["duration_ms"]; changed = True
            if cover and (not t.cover or not _cover_usable(t.cover)):
                t.cover = cover; changed = True
                self.no_cover.discard(path)
            elif path in self._cover_jobs and not cover:
                if path not in self.no_cover:
                    self.no_cover.add(path)
                    changed = True
        self._tag_thread = None
        self._cover_jobs = set()
        self.config.data["no_cover"] = sorted(self.no_cover)
        if changed:
            self.sync_config()
            self.config.save()
            self.on_focus_changed(self.focus_row)
            if cur is not None:
                self.player_bar.set_track_info(cur)
                self.now_panel.set_track(cur)
            self._update_backdrop()
        else:
            self.config.save()
        self.top_search.set_tracks(self.library.tracks)

    # ------------------------------------------------------------- обложка «на лету»
    def _request_cover_now(self, tr: Track):
        if _cover_usable(tr.cover) or not tr.path or not os.path.exists(tr.path):
            return
        if tr.path in self.no_cover:
            return
        th = TagRefreshThread([(tr.path, False, True)], self)
        th.setPriority(QThread.LowPriority)
        th.finished_results.connect(
            lambda res, t=tr, th=th: self._on_single_cover(t, res, th))
        self._cover_threads.add(th)
        th.start()

    def _on_single_cover(self, tr: Track, res, th):
        self._cover_threads.discard(th)
        for path, tags, cover in res:
            if cover and (not tr.cover or not _cover_usable(tr.cover)):
                tr.cover = cover
                self.no_cover.discard(path)
                self.config.data["no_cover"] = sorted(self.no_cover)
                self.sync_config()
                self.config.save()
                self.player_bar.set_track_info(tr)
                self.now_panel.set_track(tr)
                self._update_backdrop()
                self.tracks_panel.update_row_cover(tr)
            elif not cover:
                self.no_cover.add(path)
                self.config.data["no_cover"] = sorted(self.no_cover)
                self.config.save()

    # ------------------------------------------------------------- источник
    def refresh_source(self):
        path = self.config.data.get("source_path", "")
        if not path or not os.path.isdir(path):
            self.show_message("Источник не задан или папка недоступна")
            return
        self.no_cover.clear()
        self.config.data["no_cover"] = []
        _BAD_PIX.clear()
        existing = {t.path for t in self.library.tracks}
        found = scan_folder(path, existing)
        if found:
            self.library.tracks.extend(found)
        removed = self._prune_missing()
        self.sync_config()
        self.config.save()
        self.on_focus_changed(self.focus_row)
        self._start_tag_refresh()
        self.top_search.set_tracks(self.library.tracks)
        self.show_message(f"Источник обновлён: добавлено {len(found)}"
                          + (", удалённые с диска убраны" if removed else ""))

    def choose_new_source(self):
        path = QFileDialog.getExistingDirectory(self, "Выбрать папку источника")
        if not path:
            return
        self.config.data["source_path"] = path
        self.no_cover.clear()
        self.config.data["no_cover"] = []
        _BAD_PIX.clear()
        found = scan_folder(path, set())
        self.library.tracks = found
        paths = {t.path for t in found}
        for pl in self.library.playlists:
            pl.tracks = [t for t in pl.tracks if t.path in paths]
        self.stats = {k: v for k, v in self.stats.items() if k in paths}
        self.config.data["play_stats"] = self.stats
        self.sync_config()
        self.config.save()
        self.show_message(f"Новый источник: {len(found)} треков")
        self.on_focus_changed(self.focus_row)
        self._start_tag_refresh()
        self.top_search.set_tracks(self.library.tracks)

    # ------------------------------------------------------------- плейлисты
    def add_playlist(self, track_to_add: Optional[Track] = None):
        dlg = PlaylistDialog(self)
        if dlg.exec() == QDialog.Accepted:
            pl = Playlist(dlg.name_edit.text().strip(),
                          dlg.desc_edit.toPlainText().strip(),
                          dlg.cover_path)
            if track_to_add is not None:
                pl.tracks.append(track_to_add)
            self.library.playlists.append(pl)
            self.sync_config()
            self.config.save()
            self.playlist_panel.reload(self.library.playlists, select_last=True)
            return pl
        return None

    def edit_playlist(self, idx: int):
        if not (0 <= idx < len(self.library.playlists)):
            return
        pl = self.library.playlists[idx]
        dlg = PlaylistDialog(self, initial=pl)
        if dlg.exec() == QDialog.Accepted:
            pl.name = dlg.name_edit.text().strip()
            pl.description = dlg.desc_edit.toPlainText().strip()
            pl.cover = dlg.cover_path
            self.sync_config()
            self.config.save()
            self.playlist_panel.reload(self.library.playlists,
                                       select_row=USER_START + idx)

    def delete_playlist(self, idx: int):
        if not (0 <= idx < len(self.library.playlists)):
            return
        dlg = ConfirmDialog(self, "Удаление плейлиста",
                            "Вы действительно хотите удалить?",
                            "Да", "Нет")
        if dlg.exec() != QDialog.Accepted:
            return
        self.library.playlists.pop(idx)
        self.sync_config()
        self.config.save()
        old = self.focus_row
        if old == USER_START + idx:
            new_row = SRC_ROW
        elif old > USER_START + idx:
            new_row = old - 1
        else:
            new_row = old
        self.playlist_panel.reload(self.library.playlists, select_row=new_row)

    def _on_playlist_menu(self, row: int, gpos):
        menu = QMenu(self)
        if row == SRC_ROW:
            menu.addAction("Обновить").triggered.connect(self.refresh_source)
            menu.addAction("Выбрать новый путь").triggered.connect(self.choose_new_source)
        elif row == FREQ_ROW:
            menu.addAction("Очистить статистику").triggered.connect(self._clear_stats)
        elif row >= USER_START:
            idx = row - USER_START
            menu.addAction("Изменить плейлист…").triggered.connect(
                lambda checked=False, i=idx: self.edit_playlist(i))
            menu.addAction("Удалить плейлист").triggered.connect(
                lambda checked=False, i=idx: self.delete_playlist(i))
        else:
            return
        menu.exec(gpos)

    def _clear_stats(self):
        self.stats = {}
        self.config.data["play_stats"] = self.stats
        self.config.save()
        if self.focus_row == FREQ_ROW:
            self.on_focus_changed(FREQ_ROW)

    def _freq_tracks(self) -> List[Track]:
        out = [t for t in self.library.tracks
               if self.stats.get(t.path, 0) >= 10]
        out.sort(key=lambda t: self.stats.get(t.path, 0), reverse=True)
        return out

    # ------------------------------------------------------------- ПКМ по треку
    def _on_track_menu(self, row: int, gpos):
        if not (0 <= row < len(self.tracks_panel.current)):
            return
        track = self.tracks_panel.current[row]
        menu = QMenu(self)
        sub = menu.addMenu("Добавить в плейлист")
        act_new = sub.addAction("Создать плейлист +")
        act_new.triggered.connect(
            lambda checked=False, tr=track: self.add_playlist(tr))
        sub.addSeparator()
        if not self.library.playlists:
            act = sub.addAction("(нет плейлистов)")
            act.setEnabled(False)
        for pl in self.library.playlists:
            in_pl = any(t.path == track.path for t in pl.tracks)
            wa = QWidgetAction(sub)
            w = QWidget()
            hl = QHBoxLayout(w)
            hl.setContentsMargins(4, 3, 10, 3)
            hl.setSpacing(0)
            lbl = QLabel(
                f'<span style="color:{THEME["text_main"]};">'
                f'{html_mod.escape(pl.name)}</span>'
                f'<span style="color:{GREEN if in_pl else DOT_OFF};">'
                f'&nbsp;&nbsp;•</span>')
            lbl.setTextFormat(Qt.RichText)
            hl.addWidget(lbl)
            w.setAttribute(Qt.WA_TransparentForMouseEvents)
            lbl.setAttribute(Qt.WA_TransparentForMouseEvents)
            wa.setDefaultWidget(w)
            sub.addAction(wa)
            wa.triggered.connect(
                lambda checked=False, p=pl, tr=track: self._toggle_in_playlist(p, tr))
        menu.exec(gpos)

    def _toggle_in_playlist(self, pl: Playlist, track: Track):
        idx = next((i for i, t in enumerate(pl.tracks) if t.path == track.path), None)
        if idx is not None:
            pl.tracks.pop(idx)
        else:
            pl.tracks.append(track)
        self.sync_config()
        self.config.save()
        if self.focus_row >= USER_START and \
                self.library.playlists[self.focus_row - USER_START] is pl:
            sb = self.tracks_panel.scroll.verticalScrollBar().value()
            self.tracks_panel._apply_filter()
            self.tracks_panel.scroll.verticalScrollBar().setValue(sb)
            self.tracks_panel.mark_playing(self._current_track())

    # ------------------------------------------------------------- сигналы
    def _connect_signals(self):
        pb = self.player_bar
        self.playlist_panel.add_requested.connect(lambda: self.add_playlist())
        self.playlist_panel.selection_changed.connect(self.on_focus_changed)
        self.playlist_panel.menu_requested.connect(self._on_playlist_menu)
        self.tracks_panel.track_activated.connect(self.play_track_at)
        self.tracks_panel.tracks_shown.connect(self._on_queue_changed)
        self.tracks_panel.banner_resized.connect(self._on_banner_resized)
        self.tracks_panel.track_menu_requested.connect(self._on_track_menu)

        pb.btn_play.clicked.connect(self.toggle_play)
        pb.btn_prev.clicked.connect(lambda: self.switch_track(-1))
        pb.btn_next.clicked.connect(lambda: self.switch_track(+1))
        pb.btn_random.toggled.connect(self._on_random)
        pb.btn_rotate1.toggled.connect(self._on_rotate1)
        pb.progress.sliderReleased.connect(self._on_scrub_end)
        pb.volume.valueChanged.connect(self._on_volume)
        pb.volume.sliderReleased.connect(self.config.save)
        pb.btn_mute.clicked.connect(self.toggle_mute)

        QShortcut(QKeySequence(Qt.Key_Space), self, self.toggle_play)
        QShortcut(QKeySequence(Qt.Key_Left), self, lambda: self.seek_by(-5000))
        QShortcut(QKeySequence(Qt.Key_Right), self, lambda: self.seek_by(+5000))
        QShortcut(QKeySequence("Ctrl+F"), self, self._focus_top_search)

        QShortcut(QKeySequence(Qt.Key_MediaTogglePlayPause), self,
                  self._media_play_pause)
        QShortcut(QKeySequence(Qt.Key_MediaPlay), self, self._media_play)
        QShortcut(QKeySequence(Qt.Key_MediaPause), self, self._media_pause)
        QShortcut(QKeySequence(Qt.Key_MediaStop), self, self.stop)
        QShortcut(QKeySequence(Qt.Key_MediaNext), self, lambda: self.switch_track(+1))
        QShortcut(QKeySequence(Qt.Key_MediaPrevious), self,
                  lambda: self.switch_track(-1))

    def _focus_top_search(self):
        if self.top_search.isVisible():
            self.top_search.setFocus()
            self.top_search.selectAll()

    def _on_random(self, on: bool):
        self.config.settings["random"] = bool(on)
        self.player_bar.refresh_icons()
        self.config.save()

    def _on_rotate1(self, on: bool):
        self.config.settings["rotate1"] = bool(on)
        self.player_bar.refresh_icons()
        self.config.save()

    # ------------------------------------------------------------- старт
    def _apply_settings(self):
        s = self.config.settings
        pb = self.player_bar
        pb.volume.setValue(int(s.get("volume", 50)))
        if self.audio is not None:
            self.audio.setVolume(pb.volume.value() / 100.0)
            if bool(s.get("muted", False)):
                self.audio.setMuted(True)
                pb.set_mute_icon(True)
        pb.btn_random.setChecked(bool(s.get("random", s.get("shuffle", False))))
        pb.btn_rotate1.setChecked(bool(s.get("rotate1", False)))
        self.tracks_panel.set_banner_height(int(s.get("banner_h", BANNER_DEF_H)))
        self.tracks_panel.banner.set_zoom_enabled(bool(s.get("bg_zoom", False)))
        self.tracks_panel.banner.set_muted_mode(bool(s.get("no_cover_image", False)))
        self.tracks_panel.set_pinned(bool(s.get("bg_pin", False)))
        self.tracks_panel.set_banner_hidden(bool(s.get("hide_banner", False)))
        classic = bool(s.get("classic_view", False))
        self.now_panel.setVisible(classic)
        sizes = list(s.get("splitter", [260, 680]))
        if classic:
            if len(sizes) < 3:
                sizes = [sizes[0] if sizes else 260,
                         sizes[1] if len(sizes) > 1 else 680, 320]
            self.splitter.setSizes(sizes)
        else:
            self.splitter.setSizes(sizes[:2] if len(sizes) >= 2 else [260, 680])
        w, hgt = s.get("window", [1150, 650])
        self.resize(int(w), int(hgt))
        self._start_maximized = bool(s.get("maximized", False))
        self._update_compact_icon()
        self._refresh_caption_icons()
        if bool(s.get("dark_theme", False)):
            self.apply_theme(True)

    def _on_banner_resized(self, h: int):
        self.config.settings["banner_h"] = h
        self.config.save()

    def sync_config(self):
        self.config.data.update(self.library.to_dict())
        self.config.data["play_stats"] = self.stats
        self.config.data["no_cover"] = sorted(self.no_cover)

    def save_config(self):
        s = self.config.settings
        s["volume"] = self.player_bar.volume.value()
        s["muted"] = self.audio.isMuted() if self.audio else False
        s["banner_h"] = self.tracks_panel.banner.height()
        s["splitter"] = self.splitter.sizes()
        maxi = self.isMaximized() or (self._compact and self._pre_compact_max)
        if maxi:
            s["maximized"] = True
            g = self.normalGeometry()
            if g.width() > 0 and g.height() > 0:
                s["window"] = [g.width(), g.height()]
        else:
            s["maximized"] = False
            h = self._pre_compact_h if self._compact else self.height()
            w = self._pre_compact_w if self._compact else self.width()
            s["window"] = [w, h]
        self.sync_config()
        self.config.save()

    def closeEvent(self, event):
        self.top_search.hide_popup()
        self._unregister_media_hotkeys()
        self.save_config()
        event.accept()

    # ------------------------------------------------------------- фокус/очередь
    def on_focus_changed(self, row: int):
        if row == SEP_ROW:
            self.playlist_panel.list.setCurrentRow(self.focus_row)
            return
        self.focus_row = row
        if row == SRC_ROW:
            tracks, title = self.library.tracks, "Источник"
            desc = "Все музыкальные файлы папки-источника и её подпапок"
            self.focus_cover = ""
        elif row == FREQ_ROW:
            tracks, title = self._freq_tracks(), "Часто прослушиваемые"
            desc = FREQ_DESC
            self.focus_cover = ""
        else:
            pl = self.library.playlists[row - USER_START]
            tracks, title, desc = pl.tracks, pl.name, pl.description
            self.focus_cover = pl.cover or ""
        self.tracks_panel.show_tracks(tracks, title, desc, self.focus_cover)
        self.tracks_panel.mark_playing(self._current_track())
        self._update_backdrop()

    def _on_queue_changed(self, tracks: list):
        cur = self._current_track()
        self.queue = list(tracks)
        self.current_index = -1
        if cur is not None:
            for i, t in enumerate(self.queue):
                if t is cur or (cur.path and t.path == cur.path):
                    self.current_index = i
                    break

    def _ensure_queue(self):
        if not self.queue and self.library.tracks:
            self.queue = list(self.library.tracks)
            self.current_index = -1

    # ------------------------------------------------------------- баллы
    def _maybe_award(self):
        tr = self._current_track()
        if tr is None or self.player is None:
            return
        dur = self.player.duration() or tr.duration_ms
        if dur > 0 and self.player.position() >= 0.95 * dur:
            self._award_point(tr)

    def _award_point(self, tr: Track):
        if self.focus_row == FREQ_ROW:
            return
        cur = self.stats.get(tr.path, 0)
        self.stats[tr.path] = cur + 1
        self.config.data["play_stats"] = self.stats
        self.config.save()
        if cur + 1 == 10 and self.focus_row == FREQ_ROW:
            self.on_focus_changed(FREQ_ROW)

    # ------------------------------------------------------------- воспроизведение
    def _current_track(self) -> Optional[Track]:
        if 0 <= self.current_index < len(self.queue):
            return self.queue[self.current_index]
        return None

    def _begin_playback(self, track: Track):
        self._stopped = False
        self._pending_seek = None
        self.player_bar.set_track_info(track)
        self.now_panel.set_track(track)
        if not _cover_usable(track.cover):
            self._request_cover_now(track)
        self._update_backdrop()
        if self.player is None:
            self.show_message("Звук недоступен: модуль QtMultimedia не загружен.")
            return
        if not track.path or not os.path.exists(track.path):
            self.show_message(f"У трека «{track.title}» нет файла: {track.path!r}")
            return
        try:
            if hasattr(self.player, "setSource"):
                self.player.setSource(QUrl.fromLocalFile(track.path))
            else:
                self.player.setMedia(QUrl.fromLocalFile(track.path))
            self.player.play()
        except Exception as e:
            self.show_message(f"Ошибка запуска плеера: {e}")

    def play_track_at(self, row: int):
        if not (0 <= row < len(self.queue)):
            return
        self._maybe_award()
        track = self.queue[row]
        self.current_index = row
        self._begin_playback(track)
        self.tracks_panel.mark_playing(track)
        if bool(self.config.settings.get("follow_switch", True)):
            self.tracks_panel.ensure_row_visible(row)

    def play_from_search(self, tr: Optional[Track]):
        if tr is None:
            return
        self._maybe_award()
        self.queue = list(self.library.tracks)
        idx = next((i for i, t in enumerate(self.queue)
                    if t.path and t.path == tr.path), -1)
        if idx < 0:
            self.queue = [tr]
            idx = 0
        self.current_index = idx
        self._begin_playback(tr)
        self.tracks_panel.mark_playing(tr)
        if bool(self.config.settings.get("follow_switch", True)):
            vis = self.tracks_panel.row_of_track(tr)
            if vis >= 0:
                self.tracks_panel.ensure_row_visible(vis)
        self.top_search.reset()

    def play_random(self):
        self._ensure_queue()
        if not self.queue:
            return
        if len(self.queue) == 1:
            self.play_track_at(0)
            return
        idx = random.randrange(len(self.queue))
        if idx == self.current_index:
            idx = (idx + 1) % len(self.queue)
        self.play_track_at(idx)

    def toggle_play(self):
        if self.player is None:
            self.show_message("Звук недоступен: модуль QtMultimedia не загружен.")
            return
        if self.player.playbackState() == QMediaPlayer.PlayingState:
            self.player.pause()
            return
        self._ensure_queue()
        if self.player.mediaStatus() == QMediaPlayer.NoMedia:
            if not self.queue:
                self.show_message("Источник пуст — нечего воспроизводить")
                return
            self.play_track_at(0 if self.current_index < 0 else self.current_index)
        else:
            self.player.play()

    def switch_track(self, delta: int):
        self._ensure_queue()
        if not self.queue:
            return
        pb = self.player_bar
        if delta > 0 and pb.btn_random.isChecked():
            self.play_random()
            return
        if self.current_index < 0:
            idx = 0 if delta > 0 else len(self.queue) - 1
        else:
            idx = self.current_index + delta
            if idx < 0 or idx >= len(self.queue):
                self.stop()
                return
        self.play_track_at(idx)

    def stop(self):
        self._maybe_award()
        if self.player is not None:
            self.player.stop()
        self._stopped = True
        self._pending_seek = None
        self.player_bar.progress.setValue(0)
        self.player_bar.time_cur.setText("0:00")
        self.tracks_panel.mark_playing(None)
        self.now_panel.set_track(None)
        self._update_backdrop()

    def seek_by(self, ms: int):
        if self.player is None or self.player.mediaStatus() == QMediaPlayer.NoMedia:
            return
        self.player.setPosition(
            min(max(0, self.player.position() + ms), self.player.duration()))

    def _update_backdrop(self):
        base = self.focus_cover
        if not base and os.path.exists(BACKDROP_PLACEHOLDER):
            base = BACKDROP_PLACEHOLDER
        tr = self._current_track()
        cover = base
        if tr is not None and not self._stopped and _cover_usable(tr.cover):
            cover = tr.cover
        self.tracks_panel.set_backdrop(cover or None)

    # ------------------------------------------------------------- события плеера
    def _on_player_error(self, error, error_string):
        if self.player is not None and error != QMediaPlayer.NoError:
            print("[LALALAAA] errorOccurred:", error, error_string)
            self.show_message(f"Ошибка плеера: {error_string}")

    def _on_position(self, ms: int):
        bar = self.player_bar
        if not bar.progress.isSliderDown():
            bar.progress.setValue(ms)
        bar.time_cur.setText(format_time(ms))

    def _on_duration(self, ms: int):
        self.player_bar.progress.setMaximum(ms)
        self.player_bar.time_tot.setText(format_time(ms))
        tr = self._current_track()
        if tr is not None and not tr.duration_ms and ms > 0:
            tr.duration_ms = ms
            self.tracks_panel.update_duration(tr)

    def _on_meta_data(self):
        if self.player is None or COVER_ART_KEY is None:
            return
        tr = self._current_track()
        if tr is None or _cover_usable(tr.cover) or tr.path in self.no_cover:
            return
        try:
            md = self.player.metaData()
            img = md.value(COVER_ART_KEY)
        except Exception:
            return
        if not isinstance(img, QImage) or img.isNull():
            return
        try:
            os.makedirs(COVERS_DIR, exist_ok=True)
            cp = os.path.join(COVERS_DIR,
                              hashlib.md5(tr.path.encode()).hexdigest()[:12] + ".png")
            if not os.path.exists(cp):
                img.save(cp)
            tr.cover = cp
            self.sync_config()
            self.config.save()
            self.player_bar.set_track_info(tr)
            self.now_panel.set_track(tr)
            self._update_backdrop()
            self.tracks_panel.update_row_cover(tr)
        except Exception:
            pass

    def _on_scrub_end(self):
        if self.player is None:
            return
        val = self.player_bar.progress.value()
        if self.player.mediaStatus() == QMediaPlayer.NoMedia:
            tr = self._current_track()
            if tr is not None and tr.path and os.path.exists(tr.path):
                self._stopped = False
                self._pending_seek = val
                self.player.setSource(QUrl.fromLocalFile(tr.path))
                self.player.play()
        else:
            self.player.setPosition(val)

    def _on_media_status(self, status):
        if status in (QMediaPlayer.LoadedMedia, QMediaPlayer.BufferedMedia):
            if self._pending_seek is not None:
                self.player.setPosition(self._pending_seek)
                self._pending_seek = None
        elif status == QMediaPlayer.InvalidMedia:
            self.show_message("Не удалось прочитать файл трека")
        elif status == QMediaPlayer.EndOfMedia:
            self._maybe_award()
            pb = self.player_bar
            if pb.btn_rotate1.isChecked():
                self.player.setPosition(0)
                self.player.play()
            elif pb.btn_random.isChecked():
                self.play_random()
            else:
                self.switch_track(+1)

    def _on_volume(self, value: int):
        if self.audio is not None:
            self.audio.setVolume(value / 100.0)
        self.config.settings["volume"] = value

    def toggle_mute(self):
        if self.audio is None:
            return
        muted = not self.audio.isMuted()
        self.audio.setMuted(muted)
        self.player_bar.set_mute_icon(muted)
        self.config.settings["muted"] = muted
        self.config.save()

    def _update_play_icon(self, _state=None):
        playing = (self.player is not None
                   and self.player.playbackState() == QMediaPlayer.PlayingState)
        self.player_bar.set_play_icon(playing)

    def show_message(self, text: str):
        print("[LALALAAA]", text)


# ==========================================================================
def main():
    app = QApplication(sys.argv)
    app.setApplicationName("LALALAAA")
    QLoggingCategory.setFilterRules("qt.gui.imageio=false\nqt.gui.imageio.*=false")
    app.setStyleSheet(build_stylesheet())
    app.installEventFilter(NoTipFilter(app))
    build_icons()
    app.setWindowIcon(IC.get("app") or QIcon())
    st = app.style()
    IC["play"] = st.standardIcon(QStyle.StandardPixmap.SP_MediaPlay)
    IC["pause"] = st.standardIcon(QStyle.StandardPixmap.SP_MediaPause)
    IC["prev"] = st.standardIcon(QStyle.StandardPixmap.SP_MediaSkipBackward)
    IC["next"] = st.standardIcon(QStyle.StandardPixmap.SP_MediaSkipForward)
    IC["volume"] = st.standardIcon(QStyle.StandardPixmap.SP_MediaVolume)
    IC["muted"] = st.standardIcon(QStyle.StandardPixmap.SP_MediaVolumeMuted)

    win = MainWindow()
    win.show()
    if win._start_maximized:
        win.showMaximized()
    win._drop_initial_focus()
    win._register_media_hotkeys()
    if not HAS_MULTIMEDIA:
        QMessageBox.critical(win, "LALALAAA: нет звукового модуля",
                             "PySide6.QtMultimedia не загрузился — звука не будет.\n"
                             "Лечение: pip install --force-reinstall PySide6")
    sys.exit(app.exec())


if __name__ == "__main__":
    main()