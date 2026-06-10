import csv
import json
import os
import queue
import re
import shutil
import subprocess
import threading
import time
import tkinter as tk
from datetime import datetime
from pathlib import Path
from tkinter import filedialog, messagebox, simpledialog, ttk

try:
    from tkinterdnd2 import DNDFILES, TkinterDnD
    HAS_DND = True
except Exception:
    HAS_DND = False
    TkinterDnD = None
    DNDFILES = None

BASE_DIR = Path(r"E:\\3")
APP_DIR = BASE_DIR / "app"
INPUT_DIR = BASE_DIR / "input"
OUTPUT_DIR = BASE_DIR / "output"
REPORTS_DIR = BASE_DIR / "reports"
WAVEFORM_DIR = BASE_DIR / "waveforms"
TEMP_DIR = BASE_DIR / "temp"
LOGS_DIR = BASE_DIR / "logs"
TOOLS_DIR = BASE_DIR / "tools"
EXIFTOOL_DIR = TOOLS_DIR / "exiftool"
EXIFTOOL_EXE = EXIFTOOL_DIR / "exiftool.exe"
FFMPEG_EXE = BASE_DIR / "ffmpeg" / "bin" / "ffmpeg.exe"
FFPROBE_EXE = BASE_DIR / "ffmpeg" / "bin" / "ffprobe.exe"
FFPLAY_EXE = BASE_DIR / "ffmpeg" / "bin" / "ffplay.exe"
SETTINGS_FILE = BASE_DIR / "config_main.json"
PRESETS_FILE = BASE_DIR / "presets_custom.json"
HISTORY_FILE = BASE_DIR / "job_history.json"

APP_MAIN_VERSION = "main_2026-06-07_mp3fix"

SUPPORTED_AUDIO_EXTS = {".wav", ".wave", ".mp3", ".ogg", ".m4a", ".flac"}
SUPPORTED_IMAGE_EXTS = {".jpg", ".jpeg", ".png", ".tiff", ".webp", ".bmp"}
SUPPORTED_VIDEO_EXTS = {".mp4", ".mov", ".mkv", ".avi", ".m4v"}
SUPPORTED_MEDIA_EXTS = SUPPORTED_AUDIO_EXTS | SUPPORTED_IMAGE_EXTS | SUPPORTED_VIDEO_EXTS

BUILTIN_PRESETS = {
    "podcast": {"label": "Podcast", "lufs": "-16", "tp": "-1.5", "lra": "7", "samplerate": "48000", "bitrate": "192k", "description": "Mais equilibrado para fala longa e podcasts."},
    "musica": {"label": "Música", "lufs": "-14", "tp": "-1.0", "lra": "11", "samplerate": "48000", "bitrate": "320k", "description": "Mais aberto para música e instrumentais."},
    "voz": {"label": "Voz", "lufs": "-16", "tp": "-2.0", "lra": "6", "samplerate": "44100", "bitrate": "192k", "description": "Mais controlado para locução, reels e falas curtas."},
}

DEFAULT_SETTINGS = {
    "inputdir": str(INPUT_DIR), "outputdir": str(OUTPUT_DIR), "targetlufs": "-14", "truepeak": "-1.5", "lra": "11", "samplerate": "48000",
    "outputformat": "mp3", "bitrate": "320k", "suffix": "master", "preset": "musica", "mode": "singlefile", "keeporiginalformat": False,
    "preservemetadata": True, "recursivescan": True, "twopassmode": True, "skipexistingoutput": True, "confirmoverwritewhennotskipping": True,
    "statusfilter": "Todos", "searchtext": "", "metadataoutputmode": "copy", "metadatasuffix": "clean", "metadatapolicy": "all", "showdetailedlogs": True,
}

def ensure_dirs():
    for p in [BASE_DIR, APP_DIR, INPUT_DIR, OUTPUT_DIR, REPORTS_DIR, WAVEFORM_DIR, TEMP_DIR, LOGS_DIR, TOOLS_DIR, EXIFTOOL_DIR]:
        p.mkdir(parents=True, exist_ok=True)

def load_json_file(path: Path, fallback):
    if path.exists():
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(fallback, dict) and isinstance(data, dict):
                merged = fallback.copy(); merged.update(data); return merged
            return data
        except Exception:
            pass
    return fallback.copy() if isinstance(fallback, dict) else list(fallback)

def save_json_file(path: Path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2)

def sanitize_name(name: str):
    return re.sub(r"[^a-zA-Z0-9._-]+", "_", name.strip())

def parse_dnd_files(data: str):
    files, current, in_brace = [], "", False
    for ch in data:
        if ch == "{": in_brace = True; current = ""
        elif ch == "}": in_brace = False; files.append(current) if current else None; current = ""
        elif ch == " " and not in_brace: files.append(current) if current else None; current = ""
        else: current += ch
    if current: files.append(current)
    return [f.strip() for f in files if f.strip()]

class AppMain:
    def __init__(self, root):
        self.root = root
        self.root.title("MasterMP3 Main")
        self.root.geometry("1740x1120")
        self.root.minsize(1380, 920)
        ensure_dirs()
        self.settings = load_json_file(SETTINGS_FILE, DEFAULT_SETTINGS)
        self.custom_presets = load_json_file(PRESETS_FILE, {})
        self.job_history = load_json_file(HISTORY_FILE, [])
        self.processing = False
        self.cancel_requested = False
        self.paused = False
        self.current_process = None
        self.preview_process = None
        self.log_queue = queue.Queue()
        self.overwrite_all_decision = None
        self.manual_audio_files = []
        self.manual_metadata_files = []
        self.file_rows = {}
        self.path_to_iid = {}
        self.row_state = {}
        self.current_audio_cache = []
        self.current_metadata_cache = []
        self.metadata_iid_to_path = {}
        self.analysis_results = []
        self.last_results = []
        self.last_technical_lines = []
        self.waveform_image = None
        self.sort_state = {}
        self.mode_var = tk.StringVar(value=self.settings.get("mode", "singlefile"))
        self.input_var = tk.StringVar(value=self.settings.get("inputdir", str(INPUT_DIR)))
        self.output_var = tk.StringVar(value=self.settings.get("outputdir", str(OUTPUT_DIR)))
        self.lufs_var = tk.StringVar(value=self.settings.get("targetlufs", "-14"))
        self.tp_var = tk.StringVar(value=self.settings.get("truepeak", "-1.5"))
        self.lra_var = tk.StringVar(value=self.settings.get("lra", "11"))
        self.rate_var = tk.StringVar(value=self.settings.get("samplerate", "48000"))
        self.format_var = tk.StringVar(value=self.settings.get("outputformat", "mp3"))
        self.bitrate_var = tk.StringVar(value=self.settings.get("bitrate", "320k"))
        self.suffix_var = tk.StringVar(value=self.settings.get("suffix", "master"))
        self.preset_var = tk.StringVar(value=self.settings.get("preset", "musica"))
        self.keep_original_var = tk.BooleanVar(value=bool(self.settings.get("keeporiginalformat", False)))
        self.preserve_metadata_var = tk.BooleanVar(value=bool(self.settings.get("preservemetadata", True)))
        self.recursive_scan_var = tk.BooleanVar(value=bool(self.settings.get("recursivescan", True)))
        self.two_pass_var = tk.BooleanVar(value=bool(self.settings.get("twopassmode", True)))
        self.skip_existing_var = tk.BooleanVar(value=bool(self.settings.get("skipexistingoutput", True)))
        self.confirm_overwrite_var = tk.BooleanVar(value=bool(self.settings.get("confirmoverwritewhennotskipping", True)))
        self.status_filter_var = tk.StringVar(value=self.settings.get("statusfilter", "Todos"))
        self.search_var = tk.StringVar(value=self.settings.get("searchtext", ""))
        self.metadata_output_mode_var = tk.StringVar(value=self.settings.get("metadataoutputmode", "copy"))
        self.metadata_suffix_var = tk.StringVar(value=self.settings.get("metadatasuffix", "clean"))
        self.metadata_policy_var = tk.StringVar(value=self.settings.get("metadatapolicy", "all"))
        self.show_detailed_logs_var = tk.BooleanVar(value=bool(self.settings.get("showdetailedlogs", True)))
        self.manual_gain_var = tk.DoubleVar(value=float(self.settings.get("manual_gain_db", 0.0)))
        self.preview_gain_var = tk.DoubleVar(value=float(self.settings.get("preview_gain_db", 0.0)))
        self.preview_status_var = tk.StringVar(value="Preview parado.")
        self.master_live_var = tk.StringVar(value="Sem processamento em andamento.")
        self.preview_position_var = tk.DoubleVar(value=0.0)
        self.preview_seek_seconds = 0
        self.preview_paused = False
        self.preview_current_target = None
        self.preview_update_job = None
        self.transport_buttons = {}
        self.meta_title_var = tk.StringVar(value="")
        self.meta_artist_var = tk.StringVar(value="")
        self.meta_album_var = tk.StringVar(value="")
        self.meta_genre_var = tk.StringVar(value="")
        self.meta_comment_var = tk.StringVar(value="")
        self.status_var = tk.StringVar(value="Pronto.")
        self.detail_var = tk.StringVar(value="Aguardando arquivos.")
        self.exiftool_status_var = tk.StringVar(value=self.exiftool_status_text())
        self.ffmpeg_status_var = tk.StringVar(value=self.ffmpeg_status_text())
        self.build_ui()
        self.attach_filters()
        self.refresh_preset_combo()
        self.apply_preset(self.preset_var.get(), log_change=False)
        self.update_output_format_ui()
        self.update_mode_ui()
        self.refresh_audio_file_list()
        self.refresh_metadata_file_list()
        self.refresh_history_box()
        self.root.after(120, self.flush_log_queue)
        self.update_manual_reference()
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    def configure_professional_styles(self):
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass
        bg = "#171a23"
        panel = "#202534"
        panel_2 = "#262c3d"
        edge = "#313a52"
        text = "#eef2f7"
        muted = "#9ba7bc"
        accent = "#1bb39b"
        accent_hover = "#24c7ad"
        warn = "#e59a3a"
        danger = "#d14b63"
        violet = "#8b68d9"
        lime = "#93c949"
        stop_bg = "#37222a"
        self.root.configure(bg=bg)
        style.configure("TNotebook", background=bg, borderwidth=0)
        style.configure("TNotebook.Tab", background=panel, foreground=text, padding=(14, 10), borderwidth=0, font=("Segoe UI Semibold", 10))
        style.map("TNotebook.Tab", background=[("selected", panel_2)], foreground=[("selected", accent_hover)])
        style.configure("TFrame", background=bg)
        style.configure("Card.TFrame", background=panel, relief="flat")
        style.configure("PlayerBar.TFrame", background=panel_2, relief="flat")
        style.configure("TLabelframe", background=bg, foreground=text, bordercolor=edge, relief="solid")
        style.configure("TLabelframe.Label", background=bg, foreground=text, font=("Segoe UI Semibold", 10))
        style.configure("TLabel", background=bg, foreground=text, font=("Segoe UI", 10))
        style.configure("Muted.TLabel", background=panel_2, foreground=muted)
        style.configure("PlayerTitle.TLabel", background=panel_2, foreground=text, font=("Segoe UI Semibold", 11))
        style.configure("Status.TLabel", background=panel_2, foreground=accent_hover, font=("Segoe UI", 10))
        style.configure("TCheckbutton", background=bg, foreground=text)
        style.map("TCheckbutton", background=[("active", bg)], foreground=[("active", accent_hover)])
        style.configure("TRadiobutton", background=bg, foreground=text)
        style.map("TRadiobutton", background=[("active", bg)], foreground=[("active", accent_hover)])
        style.configure("TEntry", fieldbackground=panel, foreground=text, insertcolor=text, bordercolor="#5d6b8a", padding=(8, 6))
        style.configure("TCombobox", fieldbackground=panel, foreground=text, bordercolor=edge, arrowsize=16, padding=(8, 6), font=("Segoe UI", 10))
        style.map("TCombobox",
                  fieldbackground=[("readonly", panel), ("disabled", bg)],
                  foreground=[("readonly", text), ("disabled", muted)],
                  selectbackground=[("readonly", edge)],
                  selectforeground=[("readonly", text)])
        style.configure("Compact.TButton", padding=(10, 6))
        style.configure("Wide.TCombobox", fieldbackground=panel, foreground=text, bordercolor=edge, arrowsize=16, padding=(10, 7), font=("Segoe UI Semibold", 10))
        style.configure("TSpinbox", fieldbackground=panel, foreground=text, bordercolor=edge, arrowsize=14)
        style.configure("Treeview", background="#1c2130", fieldbackground="#1c2130", foreground=text, bordercolor=edge, rowheight=26)
        style.map("Treeview", background=[("selected", "#284a58")], foreground=[("selected", text)])
        style.configure("Treeview.Heading", background=panel_2, foreground=text, relief="flat")
        style.map("Treeview.Heading", background=[("active", edge)])
        style.configure("Horizontal.TProgressbar", troughcolor="#151923", background=accent, bordercolor=edge, lightcolor=accent, darkcolor=accent)
        style.configure("Primary.TButton", background=accent, foreground=text, borderwidth=0, focusthickness=0, padding=(12, 8))
        style.map("Primary.TButton", background=[("active", accent_hover), ("disabled", "#315a53")], foreground=[("disabled", "#c9d1dc")])
        style.configure("Danger.TButton", background=danger, foreground=text, borderwidth=0, focusthickness=0, padding=(12, 8))
        style.map("Danger.TButton", background=[("active", "#e35e76"), ("disabled", "#5c303a")])
        style.configure("Secondary.TButton", background=panel_2, foreground=text, borderwidth=0, focusthickness=0, padding=(12, 8))
        style.map("Secondary.TButton", background=[("active", edge), ("disabled", "#2a3040")])
        style.configure("TransportPlay.TButton", background=panel_2, foreground=accent_hover, borderwidth=1, focusthickness=0, padding=(10, 10), relief="flat")
        style.map("TransportPlay.TButton", background=[("active", accent), ("pressed", accent)], foreground=[("active", text), ("pressed", text)])
        style.configure("TransportPause.TButton", background=panel_2, foreground=warn, borderwidth=1, focusthickness=0, padding=(10, 10), relief="flat")
        style.map("TransportPause.TButton", background=[("active", warn), ("pressed", warn)], foreground=[("active", text), ("pressed", text)])
        style.configure("TransportPrev.TButton", background=panel_2, foreground=danger, borderwidth=1, focusthickness=0, padding=(10, 10), relief="flat")
        style.map("TransportPrev.TButton", background=[("active", danger), ("pressed", danger)], foreground=[("active", text), ("pressed", text)])
        style.configure("TransportStop.TButton", background=stop_bg, foreground=lime, borderwidth=1, focusthickness=0, padding=(10, 10), relief="flat")
        style.map("TransportStop.TButton", background=[("active", lime), ("pressed", lime)], foreground=[("active", bg), ("pressed", bg)])
        style.configure("TransportNext.TButton", background=panel_2, foreground=violet, borderwidth=1, focusthickness=0, padding=(10, 10), relief="flat")
        style.map("TransportNext.TButton", background=[("active", violet), ("pressed", violet)], foreground=[("active", text), ("pressed", text)])
        style.configure("TransportMaster.TButton", background=panel_2, foreground="#78b8ff", borderwidth=1, focusthickness=0, padding=(10, 10), relief="flat")
        style.map("TransportMaster.TButton", background=[("active", "#4d84cf"), ("pressed", "#4d84cf")], foreground=[("active", text), ("pressed", text)])

    def build_ui(self):
        self.configure_professional_styles()
        self.notebook = ttk.Notebook(self.root); self.notebook.pack(fill="both", expand=True, padx=10, pady=10)
        self.tab_master = ttk.Frame(self.notebook); self.tab_metadata = ttk.Frame(self.notebook); self.tab_inspection = ttk.Frame(self.notebook)
        self.tab_queue = ttk.Frame(self.notebook); self.tab_settings = ttk.Frame(self.notebook); self.tab_help = ttk.Frame(self.notebook)
        self.notebook.add(self.tab_master, text="Masterização"); self.notebook.add(self.tab_metadata, text="Remover metadados")
        self.notebook.add(self.tab_inspection, text="Inspeção"); self.notebook.add(self.tab_queue, text="Fila")
        self.notebook.add(self.tab_settings, text="Configurações"); self.notebook.add(self.tab_help, text="Ajuda")
        self.build_master_tab(); self.build_metadata_tab(); self.build_inspection_tab(); self.build_queue_tab(); self.build_settings_tab(); self.build_help_tab(); self.build_global_footer()

    def build_master_tab(self):
        pad = {"padx": 8, "pady": 5}
        top = ttk.Frame(self.tab_master); top.pack(fill="x", padx=10, pady=8)
        mode_box = ttk.LabelFrame(top, text="Modo"); mode_box.pack(fill="x")
        ttk.Radiobutton(mode_box, text="Arquivo único", value="singlefile", variable=self.mode_var, command=self.update_mode_ui).grid(row=0, column=0, sticky="w", **pad)
        ttk.Radiobutton(mode_box, text="Pasta inteira", value="folder", variable=self.mode_var, command=self.update_mode_ui).grid(row=0, column=1, sticky="w", **pad)
        ttk.Checkbutton(mode_box, text="Procurar em subpastas", variable=self.recursive_scan_var, command=self.refresh_audio_file_list).grid(row=0, column=2, sticky="w", **pad)
        ttk.Checkbutton(mode_box, text="2-pass loudnorm", variable=self.two_pass_var).grid(row=0, column=3, sticky="w", **pad)
        ttk.Checkbutton(mode_box, text="Pular output existente", variable=self.skip_existing_var).grid(row=0, column=4, sticky="w", **pad)
        ttk.Checkbutton(mode_box, text="Confirmar overwrite", variable=self.confirm_overwrite_var).grid(row=0, column=5, sticky="w", **pad)
        preset_box = ttk.LabelFrame(self.tab_master, text="Preset"); preset_box.pack(fill="x", padx=10, pady=6)
        ttk.Label(preset_box, text="Perfil").grid(row=0, column=0, sticky="w", **pad)
        self.preset_combo = ttk.Combobox(preset_box, textvariable=self.preset_var, state="readonly", width=18, style="Wide.TCombobox"); self.preset_combo.grid(row=0, column=1, sticky="w", **pad)
        self.preset_combo.bind("<<ComboboxSelected>>", lambda e: self.apply_preset(self.preset_var.get()))
        ttk.Button(preset_box, text="Salvar", command=self.save_current_as_preset).grid(row=0, column=2, **pad)
        ttk.Button(preset_box, text="Excluir", command=self.delete_selected_custom_preset).grid(row=0, column=3, **pad)
        ttk.Button(preset_box, text="Exportar", command=self.export_presets).grid(row=0, column=4, **pad)
        ttk.Button(preset_box, text="Importar", command=self.import_presets).grid(row=0, column=5, **pad)
        self.preset_desc = ttk.Label(preset_box, text=""); self.preset_desc.grid(row=0, column=6, sticky="w", **pad)
        path_box = ttk.LabelFrame(self.tab_master, text="Origem e saída"); path_box.pack(fill="x", padx=10, pady=6)
        self.single_file_frame = ttk.Frame(path_box); self.single_file_frame.grid(row=0, column=0, columnspan=5, sticky="ew")
        ttk.Button(self.single_file_frame, text="Adicionar", command=self.add_audio_files).pack(side="left", padx=8, pady=8)
        ttk.Button(self.single_file_frame, text="Remover", command=self.remove_selected_audio_files).pack(side="left", padx=8, pady=8)
        ttk.Button(self.single_file_frame, text="Limpar", command=self.clear_audio_files).pack(side="left", padx=8, pady=8)
        self.dnd_hint = ttk.Label(self.single_file_frame, text="Arraste e solte arquivos de áudio aqui."); self.dnd_hint.pack(side="left", padx=8, pady=8)
        self.folder_frame = ttk.Frame(path_box)
        ttk.Label(self.folder_frame, text="Pasta de entrada").grid(row=0, column=0, sticky="w", **pad)
        ttk.Entry(self.folder_frame, textvariable=self.input_var, width=72).grid(row=0, column=1, sticky="ew", **pad)
        ttk.Button(self.folder_frame, text="Abrir", command=self.choose_input).grid(row=0, column=2, **pad)
        self.folder_frame.columnconfigure(1, weight=1)
        ttk.Label(path_box, text="Pasta de saída").grid(row=1, column=0, sticky="w", **pad)
        ttk.Entry(path_box, textvariable=self.output_var, width=72).grid(row=1, column=1, sticky="ew", **pad)
        ttk.Button(path_box, text="Abrir", command=self.choose_output).grid(row=1, column=2, **pad)
        ttk.Button(path_box, text="Saída", command=self.open_output_folder).grid(row=1, column=3, **pad)
        ttk.Button(path_box, text="Reports", command=self.open_reports_folder).grid(row=1, column=4, **pad)
        path_box.columnconfigure(1, weight=1)
        filter_box = ttk.LabelFrame(self.tab_master, text="Busca e filtros"); filter_box.pack(fill="x", padx=10, pady=6)
        ttk.Label(filter_box, text="Buscar").grid(row=0, column=0, sticky="w", **pad)
        ttk.Entry(filter_box, textvariable=self.search_var, width=40).grid(row=0, column=1, sticky="w", **pad)
        ttk.Label(filter_box, text="Status").grid(row=0, column=2, sticky="w", **pad)
        self.status_filter_combo = ttk.Combobox(filter_box, textvariable=self.status_filter_var, values=["Todos", "Pronto", "Analisando", "Processando", "OK", "Erro", "Pulado", "Pendentes", "Concluídos"], state="readonly", width=16)
        self.status_filter_combo.grid(row=0, column=3, sticky="w", **pad)
        ttk.Button(filter_box, text="Limpar", command=self.clear_filters).grid(row=0, column=4, **pad)
        self.filter_info_label = ttk.Label(filter_box, text="Mostrando todos."); self.filter_info_label.grid(row=0, column=5, sticky="w", **pad)
        opts = ttk.LabelFrame(self.tab_master, text="Masterização"); opts.pack(fill="x", padx=10, pady=6)
        manual_box = ttk.LabelFrame(self.tab_master, text="Ajuste manual / referência")
        manual_box.pack(fill="x", padx=10, pady=6)
        ttk.Label(manual_box, text="Ganho extra (dB):").grid(row=0, column=0, sticky="w", **pad)
        self.manual_gain_scale = ttk.Scale(manual_box, from_=-12.0, to=12.0, variable=self.manual_gain_var, orient="horizontal", length=240, command=self.on_manual_gain_change)
        self.manual_gain_scale.grid(row=0, column=1, sticky="ew", **pad)
        self.manual_gain_label = ttk.Label(manual_box, text="0.0 dB")
        self.manual_gain_label.grid(row=0, column=2, sticky="w", **pad)
        self.manual_vu_canvas = tk.Canvas(manual_box, width=260, height=22, bg="#111111", highlightthickness=1, highlightbackground="#333333")
        self.manual_vu_canvas.grid(row=0, column=3, sticky="ew", **pad)
        self.manual_vu_bar = self.manual_vu_canvas.create_rectangle(0, 0, 0, 22, fill="#22c55e", width=0)
        self.manual_vu_text = self.manual_vu_canvas.create_text(130, 11, text="Master gain ref.", fill="white")
        ttk.Label(manual_box, text="Preview gain (dB):").grid(row=1, column=0, sticky="w", **pad)
        self.preview_gain_scale = ttk.Scale(manual_box, from_=-12.0, to=12.0, variable=self.preview_gain_var, orient="horizontal", length=240, command=self.on_preview_gain_change)
        self.preview_gain_scale.grid(row=1, column=1, sticky="ew", **pad)
        self.preview_gain_label = ttk.Label(manual_box, text="0.0 dB")
        self.preview_gain_label.grid(row=1, column=2, sticky="w", **pad)
        self.preview_vu_canvas = tk.Canvas(manual_box, width=260, height=22, bg="#111111", highlightthickness=1, highlightbackground="#333333")
        self.preview_vu_canvas.grid(row=1, column=3, sticky="ew", **pad)
        self.preview_vu_bar = self.preview_vu_canvas.create_rectangle(0, 0, 0, 22, fill="#22c55e", width=0)
        self.preview_vu_text = self.preview_vu_canvas.create_text(130, 11, text="Preview gain ref.", fill="white")
        manual_box.columnconfigure(1, weight=1)

        fields = [("Target LUFS", self.lufs_var), ("True Peak", self.tp_var), ("LRA", self.lra_var), ("Sample Rate", self.rate_var), ("Bitrate", self.bitrate_var), ("Sufixo", self.suffix_var)]
        for idx, (label, var) in enumerate(fields):
            ttk.Label(opts, text=label).grid(row=0, column=idx * 2, sticky="w", **pad); ttk.Entry(opts, textvariable=var, width=10).grid(row=0, column=idx * 2 + 1, sticky="w", **pad)
        ttk.Label(opts, text="Formato").grid(row=1, column=0, sticky="w", **pad)
        self.output_combo = ttk.Combobox(opts, textvariable=self.format_var, values=["mp3", "wav", "ogg"], state="readonly", width=10, style="Wide.TCombobox"); self.output_combo.grid(row=1, column=1, sticky="w", **pad)
        ttk.Checkbutton(opts, text="Manter formato original", variable=self.keep_original_var, command=lambda: (self.update_output_format_ui(), self.refresh_audio_file_list())).grid(row=1, column=2, sticky="w", **pad)
        ttk.Checkbutton(opts, text="Preservar metadados", variable=self.preserve_metadata_var).grid(row=1, column=3, sticky="w", **pad)
        actions = ttk.Frame(self.tab_master); actions.pack(fill="x", padx=10, pady=8)
        ttk.Button(actions, text="Atualizar", command=self.refresh_audio_file_list).pack(side="left", padx=5)
        ttk.Button(actions, text="Salvar", command=self.save_current_settings).pack(side="left", padx=5)
        ttk.Button(actions, text="Analisar", command=self.start_analysis_only).pack(side="left", padx=5)
        ttk.Button(actions, text="Reanalisar", command=self.analyze_selected_files).pack(side="left", padx=5)
        ttk.Button(actions, text="Processar", command=self.process_selected_files).pack(side="left", padx=5)
        ttk.Button(actions, text="Só erros", command=self.process_error_files).pack(side="left", padx=5)
        player_box = ttk.Frame(actions)
        player_box.pack(side="left", padx=5)
        self.make_transport_button(player_box, "▶", "Play", lambda: self.preview_selected("input")).pack(side="left", padx=2)
        self.make_transport_button(player_box, "⏸", "Pause", self.pause_preview).pack(side="left", padx=2)
        self.make_transport_button(player_box, "⏮", "Voltar", lambda: self.goto_prev_track()).pack(side="left", padx=2)
        self.make_transport_button(player_box, "⏹", "Stop", self.stop_preview).pack(side="left", padx=2)
        self.make_transport_button(player_box, "⏭", "Avançar", lambda: self.goto_next_track()).pack(side="left", padx=2)
        self.make_transport_button(player_box, "Ⓜ", "Master", lambda: self.preview_selected("output")).pack(side="left", padx=8)
        ttk.Button(actions, text="Exportar", command=self.export_selected_report).pack(side="left", padx=5)
        self.pause_btn = ttk.Button(actions, text="Pausar", command=self.toggle_pause, state="disabled"); self.pause_btn.pack(side="right", padx=5)
        self.start_btn = ttk.Button(actions, text="Iniciar", command=self.start_processing); self.start_btn.pack(side="right", padx=5)
        self.cancel_btn = ttk.Button(actions, text="Cancelar", command=self.request_cancel, state="disabled"); self.cancel_btn.pack(side="right", padx=5)
        middle = ttk.Panedwindow(self.tab_master, orient="horizontal"); middle.pack(fill="both", expand=True, padx=10, pady=8)
        left = ttk.Labelframe(middle, text="Arquivos"); center = ttk.Labelframe(middle, text="Waveform / Análise"); right = ttk.Labelframe(middle, text="Log / Histórico")
        middle.add(left, weight=4); middle.add(center, weight=3); middle.add(right, weight=2)
        columns = ("arquivo", "duracao", "ext", "title", "artist", "status", "analise", "saida")
        self.tree = ttk.Treeview(left, columns=columns, show="headings", height=18, selectmode="extended")
        for col, width in [("arquivo", 240), ("duracao", 80), ("ext", 60), ("title", 150), ("artist", 130), ("status", 110), ("analise", 180), ("saida", 220)]:
            self.tree.heading(col, text=col.title(), command=lambda c=col: self.sort_by_column(c)); self.tree.column(col, width=width, anchor="w")
        self.tree.pack(fill="both", expand=True, padx=8, pady=8); self.tree.bind("<<TreeviewSelect>>", lambda e: self.generate_waveform_for_selected())
        center_top = ttk.Frame(center); center_top.pack(fill="both", expand=True, padx=8, pady=8)
        self.waveform_label = ttk.Label(center_top, text="Waveform ainda não gerado.", anchor="center"); self.waveform_label.pack(fill="x", pady=(0, 8))
        self.analysis_box = tk.Text(center_top, height=16, wrap="word"); self.analysis_box.pack(fill="both", expand=True); self.analysis_box.insert("end", "Selecione um arquivo para gerar waveform e mostrar análises.")
        right_pane = ttk.Panedwindow(right, orient="vertical"); right_pane.pack(fill="both", expand=True, padx=8, pady=8)
        log_frame = ttk.Frame(right_pane); hist_frame = ttk.Frame(right_pane); right_pane.add(log_frame, weight=3); right_pane.add(hist_frame, weight=2)
        ttk.Label(log_frame, textvariable=self.preview_status_var).pack(anchor="w", padx=2, pady=(2, 4))
        self.preview_progress = ttk.Progressbar(log_frame, mode="determinate", maximum=100, variable=self.preview_position_var)
        self.preview_progress.pack(fill="x", padx=2, pady=(0, 6))
        ttk.Label(log_frame, textvariable=self.master_live_var).pack(anchor="w", padx=2, pady=(0, 4))
        self.master_live_progress = ttk.Progressbar(log_frame, mode="determinate")
        self.master_live_progress.pack(fill="x", padx=2, pady=(0, 6))
        self.log_text = tk.Text(log_frame, height=12, wrap="word"); self.log_text.pack(fill="both", expand=True)
        self.history_text = tk.Text(hist_frame, height=8, wrap="word"); self.history_text.pack(fill="both", expand=True)
        if HAS_DND:
            self.tree.drop_target_register(DNDFILES); self.tree.dnd_bind("<<Drop>>", self.on_audio_drop)
        else:
            self.dnd_hint.config(text="Drag and drop disponível após instalar tkinterdnd2.")

    def build_metadata_tab(self):
        pad = {"padx": 8, "pady": 5}
        intro = ttk.LabelFrame(self.tab_metadata, text="Módulo de metadados"); intro.pack(fill="x", padx=10, pady=8)
        ttk.Label(intro, text="Aba pronta para inspeção, edição, visualização e gravação de metadados.").grid(row=0, column=0, sticky="w", **pad)
        ttk.Label(intro, textvariable=self.exiftool_status_var).grid(row=0, column=1, sticky="w", **pad)
        config = ttk.LabelFrame(self.tab_metadata, text="Política de saída"); config.pack(fill="x", padx=10, pady=6)
        ttk.Label(config, text="Saída").grid(row=0, column=0, sticky="w", **pad)
        ttk.Combobox(config, textvariable=self.metadata_output_mode_var, values=["copy", "overwrite"], state="readonly", width=12).grid(row=0, column=1, sticky="w", **pad)
        ttk.Label(config, text="Sufixo").grid(row=0, column=2, sticky="w", **pad)
        ttk.Entry(config, textvariable=self.metadata_suffix_var, width=12).grid(row=0, column=3, sticky="w", **pad)
        ttk.Label(config, text="Regra").grid(row=0, column=4, sticky="w", **pad)
        ttk.Combobox(config, textvariable=self.metadata_policy_var, values=["all", "gpsonly", "textonly"], state="readonly", width=14).grid(row=0, column=5, sticky="w", **pad)
        ttk.Button(config, text="Salvar", command=self.save_current_settings).grid(row=0, column=6, **pad)
        actions = ttk.Frame(self.tab_metadata); actions.pack(fill="x", padx=10, pady=6)
        ttk.Button(actions, text="Adicionar mídia", command=self.add_metadata_files).pack(side="left", padx=5)
        ttk.Button(actions, text="Remover", command=self.remove_selected_metadata_files).pack(side="left", padx=5)
        ttk.Button(actions, text="Limpar", command=self.clear_metadata_files).pack(side="left", padx=5)
        ttk.Button(actions, text="Atualizar", command=self.refresh_metadata_file_list).pack(side="left", padx=5)
        ttk.Button(actions, text="Inspecionar", command=self.inspect_selected_metadata_real).pack(side="left", padx=5)
        ttk.Button(actions, text="Editar", command=self.load_metadata_to_form).pack(side="left", padx=5)
        ttk.Button(actions, text="Salvar", command=self.save_metadata_changes).pack(side="left", padx=5)
        ttk.Button(actions, text="Visualizar", command=self.open_metadata_file).pack(side="left", padx=5)
        ttk.Button(actions, text="Pasta", command=self.reveal_metadata_file).pack(side="left", padx=5)
        ttk.Button(actions, text="Simular", command=self.simulate_metadata_clean).pack(side="left", padx=5)
        body = ttk.Panedwindow(self.tab_metadata, orient="horizontal"); body.pack(fill="both", expand=True, padx=10, pady=8)
        left = ttk.Labelframe(body, text="Arquivos de mídia"); right = ttk.Labelframe(body, text="Editar / resumo"); body.add(left, weight=4); body.add(right, weight=3)
        cols = ("arquivo", "tipo", "ext", "status", "acao")
        self.metadata_tree = ttk.Treeview(left, columns=cols, show="headings", height=18, selectmode="extended")
        for col, width in [("arquivo", 260), ("tipo", 110), ("ext", 70), ("status", 140), ("acao", 240)]: self.metadata_tree.heading(col, text=col.title()); self.metadata_tree.column(col, width=width, anchor="w")
        self.metadata_tree.pack(fill="both", expand=True, padx=8, pady=8); self.metadata_tree.bind("<<TreeviewSelect>>", lambda e: self.update_inspection_from_metadata_selection())
        form = ttk.Frame(right); form.pack(fill="x", padx=8, pady=8)
        ttk.Label(form, text="Título").grid(row=0, column=0, sticky="w", **pad); ttk.Entry(form, textvariable=self.meta_title_var, width=50).grid(row=0, column=1, sticky="ew", **pad)
        ttk.Label(form, text="Artista / Autor").grid(row=1, column=0, sticky="w", **pad); ttk.Entry(form, textvariable=self.meta_artist_var, width=50).grid(row=1, column=1, sticky="ew", **pad)
        ttk.Label(form, text="Álbum").grid(row=2, column=0, sticky="w", **pad); ttk.Entry(form, textvariable=self.meta_album_var, width=50).grid(row=2, column=1, sticky="ew", **pad)
        ttk.Label(form, text="Gênero").grid(row=3, column=0, sticky="w", **pad); ttk.Entry(form, textvariable=self.meta_genre_var, width=50).grid(row=3, column=1, sticky="ew", **pad)
        ttk.Label(form, text="Comentário").grid(row=4, column=0, sticky="w", **pad); ttk.Entry(form, textvariable=self.meta_comment_var, width=50).grid(row=4, column=1, sticky="ew", **pad)
        form.columnconfigure(1, weight=1)
        self.metadata_info = tk.Text(right, wrap="word"); self.metadata_info.pack(fill="both", expand=True, padx=8, pady=8)
        self.metadata_info.insert("end", "Selecione uma mídia, inspecione, carregue para edição e salve as alterações aqui.")
        if HAS_DND:
            self.metadata_tree.drop_target_register(DNDFILES); self.metadata_tree.dnd_bind("<<Drop>>", self.on_metadata_drop)

    def build_inspection_tab(self):
        pad = {"padx": 8, "pady": 5}
        top = ttk.LabelFrame(self.tab_inspection, text="Inspeção de mídia"); top.pack(fill="x", padx=10, pady=8)
        ttk.Label(top, text="A aba de inspeção centraliza leitura de informações técnicas e metadados.").grid(row=0, column=0, sticky="w", **pad)
        ttk.Label(top, textvariable=self.ffmpeg_status_var).grid(row=0, column=1, sticky="w", **pad)
        ttk.Label(top, textvariable=self.exiftool_status_var).grid(row=0, column=2, sticky="w", **pad)
        actions = ttk.Frame(self.tab_inspection); actions.pack(fill="x", padx=10, pady=6)
        ttk.Button(actions, text="Inspecionar áudio selecionado", command=self.inspect_current_audio).pack(side="left", padx=5)
        ttk.Button(actions, text="Inspecionar mídia selecionada", command=self.inspect_selected_metadata_real).pack(side="left", padx=5)
        ttk.Button(actions, text="Atualizar status das ferramentas", command=self.refresh_tool_status_labels).pack(side="left", padx=5)
        self.inspection_text = tk.Text(self.tab_inspection, wrap="word"); self.inspection_text.pack(fill="both", expand=True, padx=10, pady=10)
        self.inspection_text.insert("end", "Esta área mostrará leituras consolidadas com FFprobe e ExifTool.")

    def build_queue_tab(self):
        top = ttk.LabelFrame(self.tab_queue, text="Fila unificada"); top.pack(fill="x", padx=10, pady=8)
        ttk.Label(top, text="Fila compartilhada entre masterização e metadados.").pack(anchor="w", padx=10, pady=8)
        actions = ttk.Frame(self.tab_queue); actions.pack(fill="x", padx=10, pady=6)
        ttk.Button(actions, text="Atualizar fila", command=self.refresh_queue_view).pack(side="left", padx=5)
        ttk.Button(actions, text="Pausar/Retomar", command=self.toggle_pause).pack(side="left", padx=5)
        ttk.Button(actions, text="Cancelar job", command=self.request_cancel).pack(side="left", padx=5)
        cols = ("tipo", "arquivo", "status", "detalhe")
        self.queue_tree = ttk.Treeview(self.tab_queue, columns=cols, show="headings", height=18)
        for col, width in [("tipo", 120), ("arquivo", 380), ("status", 140), ("detalhe", 500)]: self.queue_tree.heading(col, text=col.title()); self.queue_tree.column(col, width=width, anchor="w")
        self.queue_tree.pack(fill="both", expand=True, padx=10, pady=10)

    def build_settings_tab(self):
        pad = {"padx": 8, "pady": 5}
        paths = ttk.LabelFrame(self.tab_settings, text="Caminhos"); paths.pack(fill="x", padx=10, pady=8)
        rows = [("Base", str(BASE_DIR)), ("Input", self.input_var.get()), ("Output", self.output_var.get()), ("FFmpeg", str(FFMPEG_EXE)), ("FFprobe", str(FFPROBE_EXE)), ("FFplay", str(FFPLAY_EXE)), ("ExifTool", str(EXIFTOOL_EXE))]
        for i, (label, value) in enumerate(rows): ttk.Label(paths, text=label).grid(row=i, column=0, sticky="w", **pad); ttk.Label(paths, text=value).grid(row=i, column=1, sticky="w", **pad)
        prefs = ttk.LabelFrame(self.tab_settings, text="Preferências gerais"); prefs.pack(fill="x", padx=10, pady=8)
        ttk.Checkbutton(prefs, text="Logs detalhados", variable=self.show_detailed_logs_var).grid(row=0, column=0, sticky="w", **pad)
        ttk.Checkbutton(prefs, text="Preservar metadados no módulo de masterização", variable=self.preserve_metadata_var).grid(row=0, column=1, sticky="w", **pad)
        ttk.Checkbutton(prefs, text="Pular output existente", variable=self.skip_existing_var).grid(row=0, column=2, sticky="w", **pad)
        ttk.Button(prefs, text="Salvar configuração principal", command=self.save_current_settings).grid(row=0, column=3, **pad)

    def build_help_tab(self):
        actions = ttk.Frame(self.tab_help); actions.pack(fill="x", padx=10, pady=8)
        ttk.Button(actions, text="Abrir pasta base", command=lambda: os.startfile(str(BASE_DIR))).pack(side="left", padx=5)
        ttk.Button(actions, text="Reports", command=self.open_reports_folder).pack(side="left", padx=5)
        ttk.Button(actions, text="Abrir logs", command=lambda: os.startfile(str(LOGS_DIR))).pack(side="left", padx=5)
        ttk.Button(actions, text="Atualizar status das ferramentas", command=self.refresh_tool_status_labels).pack(side="left", padx=5)
        self.help_text = tk.Text(self.tab_help, wrap="word"); self.help_text.pack(fill="both", expand=True, padx=10, pady=10)
        self.help_text.insert("end", "MasterMP3 Main: base principal com masterização, inspeção e metadados funcionais.")

    def build_global_footer(self):
        footer = ttk.LabelFrame(self.root, text="Status global"); footer.pack(fill="x", padx=10, pady=(0, 10))
        self.overall_progress = ttk.Progressbar(footer, mode="determinate"); self.overall_progress.pack(fill="x", padx=10, pady=(10, 5))
        self.file_progress = ttk.Progressbar(footer, mode="determinate"); self.file_progress.pack(fill="x", padx=10, pady=(0, 5))
        ttk.Label(footer, textvariable=self.status_var).pack(anchor="w", padx=10, pady=(0, 2)); ttk.Label(footer, textvariable=self.detail_var).pack(anchor="w", padx=10, pady=(0, 10))

    def attach_filters(self):
        try: self.search_var.trace_add("write", lambda *args: self.apply_audio_filters())
        except Exception: self.search_var.trace("w", lambda *args: self.apply_audio_filters())
        self.status_filter_combo.bind("<<ComboboxSelected>>", lambda e: self.apply_audio_filters())

    def all_presets(self):
        presets = {}; presets.update(BUILTIN_PRESETS); presets.update(self.custom_presets); return presets

    def refresh_preset_combo(self):
        values = list(self.all_presets().keys()); self.preset_combo["values"] = values
        if self.preset_var.get() not in values and values: self.preset_var.set(values[0])

    def apply_preset(self, preset_key, log_change=True):
        preset = self.all_presets().get(preset_key)
        if not preset: return
        self.lufs_var.set(preset["lufs"]); self.tp_var.set(preset["tp"]); self.lra_var.set(preset["lra"]); self.rate_var.set(preset["samplerate"]); self.bitrate_var.set(preset["bitrate"])
        self.preset_desc.config(text=preset.get("description", ""))
        if log_change: self.queue_log(f"Preset aplicado: {preset.get('label', preset_key)}")

    def save_current_as_preset(self):
        name = simpledialog.askstring("Salvar preset", "Nome do preset customizado:")
        if not name: return
        key = sanitize_name(name.lower().replace(" ", "_"))
        self.custom_presets[key] = {"label": name, "lufs": self.lufs_var.get(), "tp": self.tp_var.get(), "lra": self.lra_var.get(), "samplerate": self.rate_var.get(), "bitrate": self.bitrate_var.get(), "description": f"Preset customizado: {name}"}
        save_json_file(PRESETS_FILE, self.custom_presets); self.refresh_preset_combo(); self.preset_var.set(key); self.queue_log(f"Preset custom salvo: {name}")

    def delete_selected_custom_preset(self):
        key = self.preset_var.get()
        if key in BUILTIN_PRESETS: messagebox.showwarning("Preset padrão", "Presets padrão não podem ser excluídos."); return
        if key in self.custom_presets:
            label = self.custom_presets[key].get("label", key); del self.custom_presets[key]; save_json_file(PRESETS_FILE, self.custom_presets); self.refresh_preset_combo(); self.preset_var.set("musica"); self.apply_preset("musica"); self.queue_log(f"Preset custom removido: {label}")

    def export_presets(self):
        filepath = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON", ".json")], title="Exportar presets")
        if filepath: save_json_file(Path(filepath), self.custom_presets); self.queue_log(f"Presets exportados para: {filepath}")

    def import_presets(self):
        filepath = filedialog.askopenfilename(filetypes=[("JSON", ".json")], title="Importar presets")
        if not filepath: return
        incoming = load_json_file(Path(filepath), {})
        if not isinstance(incoming, dict): messagebox.showerror("Erro", "Arquivo de presets inválido."); return
        self.custom_presets.update(incoming); save_json_file(PRESETS_FILE, self.custom_presets); self.refresh_preset_combo(); self.queue_log(f"Presets importados de: {filepath}")

    def update_output_format_ui(self): self.output_combo.config(state="disabled" if self.keep_original_var.get() else "readonly")

    def update_mode_ui(self):
        if self.mode_var.get() == "singlefile": self.folder_frame.grid_forget(); self.single_file_frame.grid(row=0, column=0, columnspan=5, sticky="ew")
        else: self.single_file_frame.grid_forget(); self.folder_frame.grid(row=0, column=0, columnspan=5, sticky="ew")
        self.refresh_audio_file_list()

    def choose_input(self):
        folder = filedialog.askdirectory(initialdir=self.input_var.get() or str(BASE_DIR))
        if folder: self.input_var.set(folder); self.refresh_audio_file_list()

    def choose_output(self):
        folder = filedialog.askdirectory(initialdir=self.output_var.get() or str(BASE_DIR))
        if folder: self.output_var.set(folder)

    def open_output_folder(self):
        p = Path(self.output_var.get()); p.mkdir(parents=True, exist_ok=True); os.startfile(str(p))

    def open_reports_folder(self):
        REPORTS_DIR.mkdir(parents=True, exist_ok=True); os.startfile(str(REPORTS_DIR))

    def exiftool_status_text(self): return f"ExifTool {'OK' if EXIFTOOL_EXE.exists() else 'não encontrado em tools/exiftool'}"
    def ffmpeg_status_text(self): return f"FFmpeg {'OK' if FFMPEG_EXE.exists() and FFPROBE_EXE.exists() else 'faltando ffmpeg/ffprobe'}"
    def refresh_tool_status_labels(self): self.exiftool_status_var.set(self.exiftool_status_text()); self.ffmpeg_status_var.set(self.ffmpeg_status_text()); self.queue_log("Status das ferramentas atualizado.")

    def save_current_settings(self):
        data = {"inputdir": self.input_var.get(), "outputdir": self.output_var.get(), "targetlufs": self.lufs_var.get(), "truepeak": self.tp_var.get(), "lra": self.lra_var.get(), "samplerate": self.rate_var.get(), "outputformat": self.format_var.get(), "bitrate": self.bitrate_var.get(), "suffix": self.suffix_var.get(), "preset": self.preset_var.get(), "mode": self.mode_var.get(), "keeporiginalformat": self.keep_original_var.get(), "preservemetadata": self.preserve_metadata_var.get(), "recursivescan": self.recursive_scan_var.get(), "twopassmode": self.two_pass_var.get(), "skipexistingoutput": self.skip_existing_var.get(), "confirmoverwritewhennotskipping": self.confirm_overwrite_var.get(), "statusfilter": self.status_filter_var.get(), "searchtext": self.search_var.get(), "metadataoutputmode": self.metadata_output_mode_var.get(), "metadatasuffix": self.metadata_suffix_var.get(), "metadatapolicy": self.metadata_policy_var.get(), "showdetailedlogs": self.show_detailed_logs_var.get()}
        save_json_file(SETTINGS_FILE, data); self.queue_log("Configuração principal salva em config_main.json"); self.status_var.set("Configuração salva.")

    def on_close(self): self.stop_preview(); self.root.destroy()
    def queue_log(self, msg): self.log_queue.put(msg)

    def flush_log_queue(self):
        while not self.log_queue.empty():
            msg = self.log_queue.get_nowait(); timestamp = datetime.now().strftime("%H:%M:%S")
            if self.show_detailed_logs_var.get(): self.log_text.insert("end", f"[{timestamp}] {msg}\n"); self.log_text.see("end")
        self.root.after(120, self.flush_log_queue)

    def refresh_history_box(self):
        self.history_text.delete("1.0", "end"); items = self.job_history[-8:]
        if not items: self.history_text.insert("end", "Sem histórico ainda."); return
        for item in reversed(items): self.history_text.insert("end", f"{item.get('timestamp')} | {item.get('mode')} | ok={item.get('ok')}/{item.get('total')} | analysis={item.get('analysisonly')}\n")

    def add_audio_files(self):
        files = filedialog.askopenfilenames(title="Selecionar arquivos de áudio", filetypes=[("Áudio", ".wav .wave .mp3 .ogg .m4a .flac")], initialdir=str(INPUT_DIR)); current = {str(x) for x in self.manual_audio_files}
        for item in files:
            p = Path(item)
            if p.suffix.lower() in SUPPORTED_AUDIO_EXTS and str(p) not in current: self.manual_audio_files.append(p)
        self.queue_log(f"Fila de áudio atualizada: {len(self.manual_audio_files)} item(ns)."); self.refresh_audio_file_list()

    def add_metadata_files(self):
        files = filedialog.askopenfilenames(title="Selecionar mídias", filetypes=[("Mídia", ".jpg .jpeg .png .tiff .webp .bmp .mp3 .wav .wave .ogg .m4a .flac .mp4 .mov .mkv .avi .m4v")], initialdir=str(INPUT_DIR)); current = {str(x) for x in self.manual_metadata_files}
        for item in files:
            p = Path(item)
            if p.suffix.lower() in SUPPORTED_MEDIA_EXTS and str(p) not in current: self.manual_metadata_files.append(p)
        self.queue_log(f"Fila de metadados atualizada: {len(self.manual_metadata_files)} item(ns)."); self.refresh_metadata_file_list(); self.refresh_queue_view()

    def on_audio_drop(self, event):
        current = {str(x) for x in self.manual_audio_files}
        for item in parse_dnd_files(event.data):
            p = Path(item)
            if p.is_file() and p.suffix.lower() in SUPPORTED_AUDIO_EXTS and str(p) not in current: self.manual_audio_files.append(p)
        self.refresh_audio_file_list()

    def on_metadata_drop(self, event):
        current = {str(x) for x in self.manual_metadata_files}
        for item in parse_dnd_files(event.data):
            p = Path(item)
            if p.is_file() and p.suffix.lower() in SUPPORTED_MEDIA_EXTS and str(p) not in current: self.manual_metadata_files.append(p)
        self.refresh_metadata_file_list(); self.refresh_queue_view()

    def clear_audio_files(self): self.manual_audio_files = []; self.refresh_audio_file_list()
    def clear_metadata_files(self): self.manual_metadata_files = []; self.refresh_metadata_file_list(); self.refresh_queue_view()

    def remove_selected_metadata_files(self):
        selected_paths = {str(p) for p in self.selected_metadata_paths()}
        if not selected_paths:
            messagebox.showwarning("Sem seleção", "Selecione um ou mais arquivos na aba de metadados.")
            return
        self.manual_metadata_files = [p for p in self.manual_metadata_files if str(p) not in selected_paths]
        self.refresh_metadata_file_list()
        self.refresh_queue_view()


    def remove_selected_audio_files(self):
        selected = self.tree.selection(); selected_paths = {self.file_rows.get(iid) for iid in selected if self.file_rows.get(iid)}
        self.manual_audio_files = [p for p in self.manual_audio_files if str(p) not in selected_paths]; self.refresh_audio_file_list()

    def media_type_for_path(self, path: Path):
        ext = path.suffix.lower()
        if ext in SUPPORTED_AUDIO_EXTS: return "áudio"
        if ext in SUPPORTED_IMAGE_EXTS: return "imagem"
        if ext in SUPPORTED_VIDEO_EXTS: return "vídeo"
        return "desconhecido"

    def get_audio_input_files(self):
        if self.mode_var.get() == "singlefile": return [p for p in self.manual_audio_files if p.exists() and p.suffix.lower() in SUPPORTED_AUDIO_EXTS]
        folder = Path(self.input_var.get())
        if not folder.exists(): return []
        if self.recursive_scan_var.get(): return [p for p in folder.rglob("*") if p.is_file() and p.suffix.lower() in SUPPORTED_AUDIO_EXTS]
        return [p for p in folder.iterdir() if p.is_file() and p.suffix.lower() in SUPPORTED_AUDIO_EXTS]

    def get_media_info(self, src: Path):
        if not FFPROBE_EXE.exists(): return {"duration": None, "title": "", "artist": "", "album": ""}
        cmd = [str(FFPROBE_EXE), "-v", "error", "-show_format", "-of", "json", str(src)]; result = subprocess.run(cmd, capture_output=True, text=True)
        duration = None; tags = {}
        if result.returncode == 0:
            try:
                data = json.loads(result.stdout); fmt = data.get("format", {}); duration = float(fmt.get("duration")) if fmt.get("duration") else None; tags = fmt.get("tags", {}) or {}
            except Exception: pass
        return {"duration": duration, "title": tags.get("title", ""), "artist": tags.get("artist", ""), "album": tags.get("album", "")}

    def seconds_to_hms(self, seconds):
        if seconds is None: return "--:--"
        s = int(round(seconds)); h, rem = divmod(s, 3600); m, sec = divmod(rem, 60)
        return f"{h:02d}:{m:02d}:{sec:02d}" if h > 0 else f"{m:02d}:{sec:02d}"

    def state_for_path(self, src_path: Path):
        key = str(src_path)
        if key not in self.row_state: self.row_state[key] = {"status": "Pronto", "analise": "-", "saida": "-"}
        return self.row_state[key]

    def normalize_status(self, status_text):
        s = str(status_text or "").strip().lower()
        if s == "ok": return "OK"
        if s in ["erro", "error"]: return "Erro"
        if s in ["pulado", "skip", "skipped"]: return "Pulado"
        if s == "processando": return "Processando"
        if s == "analisando": return "Analisando"
        return "Pronto"

    def status_matches_filter(self, status_text):
        current_filter = self.status_filter_var.get().strip().lower(); normalized = self.normalize_status(status_text).lower()
        if current_filter in ["", "todos"]: return True
        if current_filter == "pendentes": return normalized in ["pronto", "analisando", "processando"]
        if current_filter == "concluídos": return normalized in ["ok", "pulado"]
        return normalized == current_filter

    def build_search_blob(self, src: Path, info, state):
        values = [src.name, str(src), src.suffix.lower(), info.get("title", ""), info.get("artist", ""), info.get("album", ""), state.get("status", ""), state.get("analise", ""), state.get("saida", "")]
        return " ".join(str(v).lower() for v in values if v)

    def clear_filters(self): self.search_var.set(""); self.status_filter_var.set("Todos"); self.apply_audio_filters()

    def refresh_audio_file_list(self):
        files = self.get_audio_input_files(); self.current_audio_cache = []
        for src in files: self.current_audio_cache.append({"src": src, "info": self.get_media_info(src)})
        self.apply_audio_filters(); self.refresh_queue_view()

    def apply_audio_filters(self):
        selected_paths = {self.file_rows.get(iid) for iid in self.tree.selection() if self.file_rows.get(iid)}
        for item in self.tree.get_children(): self.tree.delete(item)
        self.file_rows = {}; self.path_to_iid = {}; query = self.search_var.get().strip().lower(); visible = 0; total = len(self.current_audio_cache)
        for entry in self.current_audio_cache:
            src = entry["src"]; info = entry["info"]; state = self.state_for_path(src)
            if not self.status_matches_filter(state.get("status", "")): continue
            blob = self.build_search_blob(src, info, state)
            if query and query not in blob: continue
            rowid = self.tree.insert("", "end", values=(src.name, self.seconds_to_hms(info.get("duration")), src.suffix.lower(), info.get("title", ""), info.get("artist", ""), state["status"], state["analise"], state["saida"]))
            self.file_rows[rowid] = str(src); self.path_to_iid[str(src)] = rowid; visible += 1
            if str(src) in selected_paths: self.tree.selection_add(rowid)
        self.filter_info_label.config(text=f"Mostrando {visible} de {total}.")
        self.status_var.set(f"{visible} visível(is) de {total} total.") if total else self.status_var.set("Nenhum áudio carregado.")

    def refresh_metadata_file_list(self):
        for item in self.metadata_tree.get_children(): self.metadata_tree.delete(item)
        self.current_metadata_cache = []; self.metadata_iid_to_path = {}
        for src in [p for p in self.manual_metadata_files if p.exists() and p.suffix.lower() in SUPPORTED_MEDIA_EXTS]:
            media_type = self.media_type_for_path(src); action = self.describe_metadata_policy(media_type); self.current_metadata_cache.append({"src": src, "tipo": media_type, "acao": action})
            iid = self.metadata_tree.insert("", "end", values=(src.name, media_type, src.suffix.lower(), "Pronto para inspeção", action)); self.metadata_iid_to_path[iid] = str(src)

    def describe_metadata_policy(self, media_type):
        return f"política={self.metadata_policy_var.get()} | modo={self.metadata_output_mode_var.get()} | sufixo={self.metadata_suffix_var.get()} | tipo={media_type}"

    def selected_audio_iid(self):
        selected = self.tree.selection(); return selected[0] if selected else None

    def selected_audio_path(self):
        iid = self.selected_audio_iid()
        if not iid: return None
        raw = self.file_rows.get(iid); return Path(raw) if raw else None

    def selected_audio_paths(self):
        paths = []
        for iid in self.tree.selection():
            raw = self.file_rows.get(iid)
            if raw: paths.append(Path(raw))
        return paths

    def selected_metadata_paths(self):
        paths = []
        for iid in self.metadata_tree.selection():
            raw = self.metadata_iid_to_path.get(iid)
            if raw: paths.append(Path(raw))
        return paths

    def selected_metadata_path(self):
        paths = self.selected_metadata_paths(); return paths[0] if paths else None

    def open_metadata_file(self):
        src = self.selected_metadata_path()
        if not src: messagebox.showwarning("Sem seleção", "Selecione um arquivo na aba de metadados."); return
        if not src.exists(): messagebox.showerror("Arquivo não encontrado", f"O arquivo não existe mais:\n{src}"); return
        try: os.startfile(str(src)); self.queue_log(f"Arquivo aberto: {src}")
        except Exception as e: messagebox.showerror("Falha ao abrir", f"Não foi possível abrir o arquivo.\n\n{e}")

    def reveal_metadata_file(self):
        src = self.selected_metadata_path()
        if not src: messagebox.showwarning("Sem seleção", "Selecione um arquivo na aba de metadados."); return
        if not src.exists(): messagebox.showerror("Arquivo não encontrado", f"O arquivo não existe mais:\n{src}"); return
        try: subprocess.Popen(f'explorer /select,"{src}"'); self.queue_log(f"Pasta aberta para: {src}")
        except Exception as e: messagebox.showerror("Falha ao abrir pasta", f"Não foi possível abrir a pasta do arquivo.\n\n{e}")

    def run_exiftool_read(self, src: Path):
        if not EXIFTOOL_EXE.exists(): return {"error": f"ExifTool não encontrado em {EXIFTOOL_EXE}"}
        try:
            result = subprocess.run([str(EXIFTOOL_EXE), "-j", "-G", "-a", "-u", str(src)], capture_output=True, text=True, encoding="utf-8", errors="replace")
            if result.returncode != 0: return {"error": (result.stderr or result.stdout or "Falha desconhecida").strip()}
            data = json.loads(result.stdout)
            if isinstance(data, list) and data: return data[0]
            return {}
        except Exception as e: return {"error": str(e)}

    def inspect_selected_metadata_real(self):
        selected = self.selected_metadata_paths(); self.inspection_text.delete("1.0", "end"); self.metadata_info.delete("1.0", "end")
        if not selected: self.inspection_text.insert("end", "Selecione um ou mais arquivos na aba de metadados."); return
        for src in selected:
            self.inspection_text.insert("end", f"\n=== {src.name} ===\nCaminho: {src}\nTipo: {self.media_type_for_path(src)}\n")
            info = self.run_exiftool_read(src)
            if "error" in info: self.inspection_text.insert("end", f"Erro ExifTool: {info['error']}\n"); continue
            preferred_keys = ["Title", "Artist", "Author", "Album", "Genre", "Comment", "CreateDate", "ModifyDate", "FileType", "MIMEType", "ImageWidth", "ImageHeight", "Duration", "AudioChannels"]
            for key in preferred_keys:
                if key in info: self.inspection_text.insert("end", f"{key}: {info[key]}\n")
            self.inspection_text.insert("end", "\n-- Todas as tags lidas --\n")
            for key in sorted(info.keys()):
                if key == "SourceFile": continue
                self.inspection_text.insert("end", f"{key}: {info[key]}\n")
        self.metadata_info.insert("end", "Inspeção real concluída com leitura via ExifTool.\n"); self.queue_log("Inspeção real de metadados executada.")

    def load_metadata_to_form(self):
        src = self.selected_metadata_path()
        if not src: messagebox.showwarning("Sem seleção", "Selecione um arquivo na aba de metadados."); return
        info = self.run_exiftool_read(src)
        if "error" in info: messagebox.showerror("Erro de leitura", info["error"]); return
        self.meta_title_var.set(str(info.get("Title", ""))); self.meta_artist_var.set(str(info.get("Artist", info.get("Author", "")))); self.meta_album_var.set(str(info.get("Album", ""))); self.meta_genre_var.set(str(info.get("Genre", ""))); self.meta_comment_var.set(str(info.get("Comment", "")))
        self.metadata_info.delete("1.0", "end"); self.metadata_info.insert("end", f"Campos carregados para edição:\n{src.name}\n"); self.queue_log(f"Metadados carregados para edição: {src.name}")

    def path_has_special_chars(self, path_obj):
        text = str(path_obj)
        return any(ord(ch) > 127 for ch in text)

    def make_safe_ascii_name(self, value):
        import unicodedata
        normalized = unicodedata.normalize("NFKD", str(value))
        ascii_only = normalized.encode("ascii", "ignore").decode("ascii")
        ascii_only = ascii_only.lower()
        ascii_only = re.sub(r"&", " and ", ascii_only)
        ascii_only = re.sub(r"[^a-z0-9]+", "_", ascii_only)
        ascii_only = re.sub(r"_+", "_", ascii_only).strip("_")
        return ascii_only or "arquivo"

    def build_safe_metadata_copy_path(self, src):
        safe_parent = BASE_DIR / "metadata_safe"
        safe_parent.mkdir(parents=True, exist_ok=True)
        base_name = self.make_safe_ascii_name(src.stem)
        safe_name = base_name + src.suffix.lower()
        candidate = safe_parent / safe_name
        idx = 1
        while candidate.exists() and candidate.resolve() != src.resolve():
            candidate = safe_parent / f"{base_name}_{idx:03d}{src.suffix.lower()}"
            idx += 1
        return candidate

    def save_metadata_changes(self):
        src = self.selected_metadata_path()
        if not src:
            messagebox.showwarning("Sem seleção", "Selecione um arquivo na aba de metadados.")
            return
        mode = self.metadata_output_mode_var.get().strip().lower()
        suffix = self.metadata_suffix_var.get().strip() or "clean"
        ext = src.suffix.lower()
        target = src if mode != "copy" else src.with_name(f"{src.stem}_{suffix}{src.suffix}")

        warned_special = False
        if self.path_has_special_chars(src):
            warned_special = True
            self.metadata_info.delete("1.0", "end")
            self.metadata_info.insert("end", f"Aviso: caminho com acentos/caracteres especiais detectado.\n\nOrigem:\n{src}\n\nIsso pode impedir a gravação de metadados em MP3/MP4.\n")
            if not messagebox.askyesno(
                "Caminho com caracteres especiais",
                f"Foi detectado acento ou caractere especial no caminho do arquivo.\n\n{src}\n\nDeseja criar uma cópia segura em metadata_safe com nome padronizado antes de salvar os metadados?"
            ):
                return
            safe_copy = self.build_safe_metadata_copy_path(src)
            try:
                shutil.copy2(src, safe_copy)
            except Exception as e:
                messagebox.showerror("Falha ao criar cópia segura", f"Não foi possível criar a cópia com nome limpo.\n\n{e}")
                return
            target = safe_copy
            mode = "copy"

        if mode == "copy" and target == src:
            target = src.with_name(f"{src.stem}_{suffix}{src.suffix}")

        if mode == "copy" and target != src and not warned_special:
            try:
                shutil.copy2(src, target)
            except Exception as e:
                messagebox.showerror("Falha ao copiar", f"Não foi possível criar a cópia.\n\n{e}")
                return

        try:
            if ext == ".mp3":
                if not FFMPEG_EXE.exists():
                    messagebox.showerror("FFmpeg ausente", f"FFmpeg não encontrado em:\n{FFMPEG_EXE}")
                    return
                work_src = target
                tmp_target = target.with_name(f"{target.stem}__meta_tmp{target.suffix}")
                if tmp_target.exists():
                    try:
                        tmp_target.unlink()
                    except Exception:
                        pass
                cmd = [
                    str(FFMPEG_EXE), "-y", "-i", str(work_src),
                    "-map", "0:a?",
                    "-c:a", "libmp3lame",
                    "-q:a", "2",
                    "-id3v2_version", "3",
                    "-write_id3v1", "1",
                    "-metadata", f"title={self.meta_title_var.get()}",
                    "-metadata", f"artist={self.meta_artist_var.get()}",
                    "-metadata", f"album={self.meta_album_var.get()}",
                    "-metadata", f"genre={self.meta_genre_var.get()}",
                    "-metadata", f"comment={self.meta_comment_var.get()}",
                    str(tmp_target)
                ]
                result = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace")
                if result.returncode != 0:
                    raise RuntimeError((result.stderr or result.stdout or "Falha ao salvar MP3 com FFmpeg").strip())
                if work_src.exists():
                    try:
                        work_src.unlink()
                    except Exception:
                        pass
                tmp_target.replace(work_src)
                target = work_src
            elif ext in {".mp4", ".mov", ".m4v", ".mkv", ".avi"}:
                if not FFMPEG_EXE.exists():
                    messagebox.showerror("FFmpeg ausente", f"FFmpeg não encontrado em:\n{FFMPEG_EXE}")
                    return
                if not EXIFTOOL_EXE.exists():
                    messagebox.showerror("ExifTool ausente", f"ExifTool não encontrado em:\n{EXIFTOOL_EXE}")
                    return
                remux_target = target.with_name(f"{target.stem}__flat{target.suffix}")
                if remux_target.exists():
                    try:
                        remux_target.unlink()
                    except Exception:
                        pass
                remux_cmd = [
                    str(FFMPEG_EXE), "-y", "-i", str(target),
                    "-map", "0",
                    "-c", "copy",
                    "-movflags", "faststart",
                    str(remux_target)
                ]
                remux_result = subprocess.run(remux_cmd, capture_output=True, text=True, encoding="utf-8", errors="replace")
                if remux_result.returncode != 0:
                    raise RuntimeError((remux_result.stderr or remux_result.stdout or "Falha ao remuxar vídeo fragmentado").strip())
                if target.exists():
                    try:
                        target.unlink()
                    except Exception:
                        pass
                remux_target.replace(target)
                cmd = [
                    str(EXIFTOOL_EXE),
                    "-charset", "filename=utf8",
                    "-overwrite_original",
                    "-api", "QuickTimeUTC=1",
                    f"-QuickTime:Title={self.meta_title_var.get()}",
                    f"-QuickTime:Artist={self.meta_artist_var.get()}",
                    f"-QuickTime:Album={self.meta_album_var.get()}",
                    f"-QuickTime:Genre={self.meta_genre_var.get()}",
                    f"-QuickTime:Comment={self.meta_comment_var.get()}",
                    str(target)
                ]
                result = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace")
                if result.returncode != 0:
                    raise RuntimeError((result.stderr or result.stdout or "Falha ao salvar vídeo com ExifTool").strip())
            else:
                if not EXIFTOOL_EXE.exists():
                    messagebox.showerror("ExifTool ausente", f"ExifTool não encontrado em:\n{EXIFTOOL_EXE}")
                    return
                cmd = [
                    str(EXIFTOOL_EXE),
                    "-charset", "filename=utf8",
                    "-overwrite_original",
                    f"-Title={self.meta_title_var.get()}",
                    f"-Artist={self.meta_artist_var.get()}",
                    f"-Album={self.meta_album_var.get()}",
                    f"-Genre={self.meta_genre_var.get()}",
                    f"-Comment={self.meta_comment_var.get()}",
                    str(target)
                ]
                result = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace")
                if result.returncode != 0:
                    raise RuntimeError((result.stderr or result.stdout or "Falha ao salvar").strip())

            self.metadata_info.delete("1.0", "end")
            self.metadata_info.insert("end", f"Alterações salvas com sucesso em:\n{target}\n")
            if warned_special:
                self.metadata_info.insert("end", "\nObs.: foi criada uma cópia segura em metadata_safe com nome padronizado.\n")
            self.queue_log(f"Metadados salvos: {target}")
            self.refresh_metadata_file_list()
            messagebox.showinfo("Sucesso", f"Metadados atualizados com sucesso.\n\nArquivo:\n{target}")
        except Exception as e:
            messagebox.showerror("Erro ao salvar", str(e))

    def simulate_metadata_clean(self):
        total = len(self.metadata_tree.selection()) or len(self.current_metadata_cache)
        self.metadata_info.delete("1.0", "end"); self.metadata_info.insert("end", f"Simulação\n\nAlvos: {total}\nModo de saída: {self.metadata_output_mode_var.get()}\nSufixo: {self.metadata_suffix_var.get()}\nPolítica: {self.metadata_policy_var.get()}\n\nUse 'Salvar alterações' para gravar metadados editados.\n"); self.queue_log("Simulação de limpeza de metadados executada.")

    def update_inspection_from_metadata_selection(self): self.inspect_selected_metadata_real()

    def inspect_current_audio(self):
        src = self.selected_audio_path(); self.inspection_text.delete("1.0", "end")
        if not src: self.inspection_text.insert("end", "Selecione um arquivo na aba Masterização."); return
        info = self.get_media_info(src); state = self.state_for_path(src)
        self.inspection_text.insert("end", f"Arquivo: {src}\nDuração: {self.seconds_to_hms(info.get('duration'))}\nTítulo: {info.get('title', '')}\nArtista: {info.get('artist', '')}\nÁlbum: {info.get('album', '')}\nStatus: {state.get('status')}\nAnálise: {state.get('analise')}\nSaída: {state.get('saida')}\n")

    def refresh_queue_view(self):
        for item in self.queue_tree.get_children(): self.queue_tree.delete(item)
        for entry in self.current_audio_cache:
            src = entry["src"]; state = self.state_for_path(src); self.queue_tree.insert("", "end", values=("masterização", str(src), state.get("status"), state.get("analise")))
        for entry in self.current_metadata_cache:
            src = entry["src"]; self.queue_tree.insert("", "end", values=("metadados", str(src), "Pronto", entry.get("acao")))

    def update_row_status(self, src_path, status=None, analise=None, saida=None):
        state = self.state_for_path(src_path)
        if status is not None: state["status"] = status
        if analise is not None: state["analise"] = analise
        if saida is not None: state["saida"] = saida
        self.root.after(0, self.apply_audio_filters); self.root.after(0, self.refresh_queue_view)

    def request_cancel(self):
        self.cancel_requested = True; self.detail_var.set("Cancelamento solicitado...")
        if self.current_process and self.current_process.poll() is None:
            try: self.current_process.terminate()
            except Exception: pass

    def toggle_pause(self):
        self.paused = not self.paused; self.pause_btn.config(text="Retomar" if self.paused else "Pausar"); self.detail_var.set("Pausado." if self.paused else "Retomando..."); self.queue_log("Fila pausada." if self.paused else "Fila retomada.")

    def wait_if_paused(self):
        while self.paused and not self.cancel_requested: time.sleep(0.2)

    def show_waveform_image(self, png_path: Path):
        try:
            if png_path.exists(): self.waveform_image = tk.PhotoImage(file=str(png_path)); self.waveform_label.config(image=self.waveform_image, text="")
            else: self.waveform_label.config(text="Waveform não disponível.", image=""); self.waveform_image = None
        except Exception:
            self.waveform_label.config(text=f"Waveform gerado em: {png_path}", image=""); self.waveform_image = None

    def generate_waveform_for_selected(self):
        src = self.selected_audio_path()
        if not src or not FFMPEG_EXE.exists(): return
        png_path = WAVEFORM_DIR / f"{sanitize_name(src.stem)}.png"; cmd = [str(FFMPEG_EXE), "-y", "-i", str(src), "-filter_complex", "aformat=channel_layouts=mono,showwavespic=s=700x220:colors=DodgerBlue", "-frames:v", "1", str(png_path)]
        result = subprocess.run(cmd, capture_output=True, text=True); self.analysis_box.delete("1.0", "end")
        if result.returncode == 0 and png_path.exists(): self.analysis_box.insert("end", f"Waveform gerado em: {png_path}\n\n"); self.show_waveform_image(png_path)
        else: self.analysis_box.insert("end", "Não foi possível gerar waveform.\n\n"); self.waveform_label.config(text="Não foi possível gerar waveform.", image=""); self.waveform_image = None
        info = self.get_media_info(src); state = self.state_for_path(src)
        self.analysis_box.insert("end", f"Arquivo em foco: {src.name}\nDuração: {self.seconds_to_hms(info.get('duration'))}\nTítulo: {info.get('title', '')}\nArtista: {info.get('artist', '')}\nÁlbum: {info.get('album', '')}\nStatus: {state.get('status', '-')}\nAnálise: {state.get('analise', '-')}\nSaída: {state.get('saida', '-')}\n")

    def make_transport_button(self, parent, icon_text, label_text, command):
        frame = ttk.Frame(parent)
        btn = tk.Button(frame, text=icon_text, command=command, width=4, height=1, relief="raised", bd=1, font=("Segoe UI Symbol", 12))
        btn.pack(fill="x")
        ttk.Label(frame, text=label_text).pack()
        return frame

    def update_manual_reference(self):
        gain = float(self.manual_gain_var.get())
        preview_gain = float(self.preview_gain_var.get())
        if hasattr(self, "manual_gain_label"):
            self.manual_gain_label.config(text=f"{gain:+.1f} dB")
        if hasattr(self, "preview_gain_label"):
            self.preview_gain_label.config(text=f"{preview_gain:+.1f} dB")
        self.update_gain_meter("manual", gain)
        self.update_gain_meter("preview", preview_gain)

    def update_gain_meter(self, meter_type, value_db):
        normalized = max(0.0, min(1.0, (float(value_db) + 12.0) / 24.0))
        width = int(260 * normalized)
        color = "#22c55e" if value_db <= 3 else "#eab308" if value_db <= 6 else "#ef4444"
        if meter_type == "manual" and hasattr(self, "manual_vu_canvas"):
            self.manual_vu_canvas.coords(self.manual_vu_bar, 0, 0, width, 22)
            self.manual_vu_canvas.itemconfig(self.manual_vu_bar, fill=color)
            self.manual_vu_canvas.itemconfig(self.manual_vu_text, text=f"Master ref {value_db:+.1f} dB")
        elif meter_type == "preview" and hasattr(self, "preview_vu_canvas"):
            self.preview_vu_canvas.coords(self.preview_vu_bar, 0, 0, width, 22)
            self.preview_vu_canvas.itemconfig(self.preview_vu_bar, fill=color)
            self.preview_vu_canvas.itemconfig(self.preview_vu_text, text=f"Preview ref {value_db:+.1f} dB")

    def on_manual_gain_change(self, value=None):
        self.update_manual_reference()
        self.master_live_var.set(f"Ganho extra ajustado: {float(self.manual_gain_var.get()):+.1f} dB")

    def on_preview_gain_change(self, value=None):
        self.update_manual_reference()
        if self.preview_process and self.preview_process.poll() is None:
            current_mode = getattr(self, "preview_mode", None)
            self.restart_preview_with_current_gain(current_mode)
        else:
            self.preview_status_var.set(f"Preview gain ajustado para {float(self.preview_gain_var.get()):+.1f} dB")

    def restart_preview_with_current_gain(self, which=None):
        which = which or getattr(self, "preview_mode", None)
        if not which:
            return
        self.preview_selected(which, restart=True, seek_seconds=self.preview_seek_seconds)

    def build_preview_command(self, target, seek_seconds=0):
        preview_gain = float(self.preview_gain_var.get())
        cmd = [str(FFPLAY_EXE), "-nodisp", "-autoexit"]
        if seek_seconds > 0:
            cmd += ["-ss", str(max(0, int(seek_seconds)))]
        if abs(preview_gain) > 0.01:
            volume = max(0.01, min(8.0, 10 ** (preview_gain / 20.0)))
            cmd += ["-af", f"volume={volume:.4f}"]
        cmd.append(str(target))
        return cmd

    def pause_preview(self):
        if self.preview_process and self.preview_process.poll() is None:
            try:
                self.preview_process.terminate()
            except Exception:
                pass
            self.preview_process = None
        self.preview_paused = True
        self.preview_status_var.set(f"Preview pausado em {int(self.preview_seek_seconds)}s")

    def seek_preview(self, seconds_delta):
        self.preview_seek_seconds = max(0, int(self.preview_seek_seconds + seconds_delta))
        if self.preview_current_target and self.preview_mode:
            self.preview_selected(self.preview_mode, restart=True, seek_seconds=self.preview_seek_seconds)
        else:
            self.preview_status_var.set(f"Posição preparada: {self.preview_seek_seconds}s")

    def preview_selected(self, which, restart=False, seek_seconds=None):
        src = self.selected_audio_path()
        if not src:
            messagebox.showwarning("Sem seleção", "Selecione um arquivo na tabela.")
            return
        if not FFPLAY_EXE.exists():
            messagebox.showwarning("Sem ffplay", f"ffplay.exe não encontrado em\n{FFPLAY_EXE}")
            return
        target = src if which == "input" else self.build_output_path(src, Path(self.output_var.get()))
        if not target.exists():
            messagebox.showwarning("Sem arquivo", "Arquivo ainda não existe para preview.")
            return
        self.stop_preview(reset_position=False)
        if seek_seconds is None:
            seek_seconds = self.preview_seek_seconds if restart else 0
        self.preview_seek_seconds = max(0, int(seek_seconds))
        self.preview_current_target = target
        self.set_current_row_highlight(target)
        self.preview_mode = which
        self.preview_paused = False
        cmd = self.build_preview_command(target, seek_seconds=self.preview_seek_seconds)
        self.preview_process = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        label = 'original' if which == 'input' else 'master'
        self.preview_status_var.set(f"Tocando {label}: {target.name} | gain {float(self.preview_gain_var.get()):+.1f} dB | posição {self.preview_seek_seconds}s")
        self.queue_log(f"Preview {label}: {target.name} | gain {float(self.preview_gain_var.get()):+.1f} dB | posição {self.preview_seek_seconds}s")
        self.start_preview_progress_updater(target)

    def start_preview_progress_updater(self, target):
        try:
            info = self.get_media_info(target)
            duration = float(info.get("duration") or 0)
        except Exception:
            duration = 0
        if self.preview_update_job:
            try:
                self.root.after_cancel(self.preview_update_job)
            except Exception:
                pass
        def tick():
            if not self.preview_process or self.preview_process.poll() is not None:
                self.preview_update_job = None
                return
            self.preview_seek_seconds += 1
            pct = 0 if duration <= 0 else max(0, min(100, (self.preview_seek_seconds / duration) * 100))
            self.preview_position_var.set(pct)
            if hasattr(self, "preview_progress"):
                self.preview_progress.configure(value=pct)
            self.preview_update_job = self.root.after(1000, tick)
        self.preview_update_job = self.root.after(1000, tick)

    def stop_preview(self, reset_position=True):
        if self.preview_update_job:
            try:
                self.root.after_cancel(self.preview_update_job)
            except Exception:
                pass
            self.preview_update_job = None
        if self.preview_process and self.preview_process.poll() is None:
            try:
                self.preview_process.terminate()
            except Exception:
                pass
        self.preview_process = None
        self.preview_mode = None
        self.preview_current_target = None
        if hasattr(self, 'preview_progress'):
            self.preview_progress.configure(value=0 if reset_position else self.preview_position_var.get())
        if reset_position:
            self.preview_seek_seconds = 0
            self.preview_position_var.set(0)
        self.preview_status_var.set("Preview parado." if reset_position else f"Preview reiniciando em {int(self.preview_seek_seconds)}s...")

    def set_current_row_highlight(self, path):
        try:
            for item in self.tree.get_children():
                self.tree.item(item, tags=())
            if not path:
                return
            for item in self.tree.get_children():
                values = self.tree.item(item, "values")
                if values and str(values[0]) == str(path.name):
                    self.tree.item(item, tags=("playing",))
                    self.tree.see(item)
                    break
            if not hasattr(self, "tree_style_done"):
                style = ttk.Style()
                style.configure("Treeview", rowheight=24)
                style.configure("Treeview.Playing", background="#2b4f7a", foreground="white")
                style.map("Treeview", background=[("selected", "#355c84")])
                self.tree.tag_configure("playing", background="#355c84", foreground="white")
                self.tree_style_done = True
        except Exception:
            pass

    def get_audio_paths_in_tree_order(self):
        paths = []
        for iid in self.tree.get_children():
            raw = self.file_rows.get(iid)
            if raw:
                paths.append(Path(raw))
        return paths

    def select_audio_path_in_tree(self, path):
        if not path:
            return False
        for iid in self.tree.get_children():
            raw = self.file_rows.get(iid)
            if raw and Path(raw).resolve() == path.resolve():
                self.tree.selection_set(iid)
                self.tree.focus(iid)
                self.tree.see(iid)
                return True
        return False

    def goto_prev_track(self):
        paths = self.get_audio_paths_in_tree_order()
        if not paths:
            self.preview_status_var.set("Sem faixa anterior.")
            return
        current = getattr(self, "preview_current_target", None)
        if current and current.exists():
            try:
                idx = [p.resolve() for p in paths].index(current.resolve())
            except Exception:
                idx = 0
        else:
            selected = self.selected_audio_path()
            if selected:
                try:
                    idx = [p.resolve() for p in paths].index(selected.resolve())
                except Exception:
                    idx = 0
            else:
                idx = 0
        prev_path = paths[(idx - 1) % len(paths)]
        self.select_audio_path_in_tree(prev_path)
        self.preview_seek_seconds = 0
        self.preview_selected("input", restart=False, seek_seconds=0)
        self.preview_status_var.set(f"Tocando faixa anterior: {prev_path.name}")

    def goto_next_track(self):
        paths = self.get_audio_paths_in_tree_order()
        if not paths:
            self.preview_status_var.set("Sem próxima faixa.")
            return
        current = getattr(self, "preview_current_target", None)
        if current and current.exists():
            try:
                idx = [p.resolve() for p in paths].index(current.resolve())
            except Exception:
                idx = -1
        else:
            selected = self.selected_audio_path()
            if selected:
                try:
                    idx = [p.resolve() for p in paths].index(selected.resolve())
                except Exception:
                    idx = -1
            else:
                idx = -1
        next_path = paths[(idx + 1) % len(paths)]
        self.select_audio_path_in_tree(next_path)
        self.preview_seek_seconds = 0
        self.preview_selected("input", restart=False, seek_seconds=0)
        self.preview_status_var.set(f"Tocando próxima faixa: {next_path.name}")

    def build_output_path(self, src: Path, output_dir: Path):
        if self.keep_original_var.get(): ext = src.suffix.lower() if src.suffix.lower() in SUPPORTED_AUDIO_EXTS else ".mp3"
        else:
            fmt = self.format_var.get().lower().strip(); ext = ".mp3" if fmt == "mp3" else ".wav" if fmt == "wav" else ".ogg"
        suffix = sanitize_name(self.suffix_var.get() or "master"); return output_dir / f"{src.stem}_{suffix}{ext}"

    def safe_loudnorm_value(self, value, fallback):
        try:
            if value is None: return str(fallback)
            f = float(str(value).strip())
            if f != f: return str(fallback)
            return str(f)
        except Exception: return str(fallback)

    def analyze_loudnorm(self, src: Path):
        target_lufs = self.lufs_var.get().strip() or "-14"; true_peak = self.tp_var.get().strip() or "-1.5"; lra = self.lra_var.get().strip() or "11"
        cmd = [str(FFMPEG_EXE), "-hide_banner", "-i", str(src), "-af", f"loudnorm=I={target_lufs}:TP={true_peak}:LRA={lra}:print_format=json", "-f", "null", "-"]
        result = subprocess.run(cmd, capture_output=True, text=True); text = result.stderr or result.stdout or ""; match = re.search(r"\{\s*\"input_i\".*?\}", text, re.S); parsed = {"input": str(src)}
        if match:
            try: parsed.update(json.loads(match.group(0)))
            except Exception: parsed["raw"] = match.group(0)
        else: parsed["raw"] = text[-1500:]
        parsed["input_i"] = self.safe_loudnorm_value(parsed.get("input_i"), -20.0); parsed["input_tp"] = self.safe_loudnorm_value(parsed.get("input_tp"), -6.0); parsed["input_lra"] = self.safe_loudnorm_value(parsed.get("input_lra"), 1.0); parsed["input_thresh"] = self.safe_loudnorm_value(parsed.get("input_thresh"), -30.0); parsed["target_offset"] = self.safe_loudnorm_value(parsed.get("target_offset"), 0.0)
        return parsed

    def format_analysis_summary(self, result): return f"I {result.get('input_i', '?')} | TP {result.get('input_tp', '?')}"
    def set_overall_progress(self, value): self.root.after(0, lambda: self.overall_progress.configure(value=value))
    def set_file_progress(self, value): self.root.after(0, lambda: self.file_progress.configure(value=max(0, min(100, value))))
    def set_detail(self, text): self.root.after(0, lambda: self.detail_var.set(text))

    def start_analysis_only(self):
        if self.processing: return
        if not FFMPEG_EXE.exists(): messagebox.showerror("FFmpeg ausente", "Verifique ffmpeg.exe em ffmpeg."); return
        files = self.get_audio_input_files()
        if not files: messagebox.showwarning("Sem arquivos", "Nenhum arquivo válido encontrado para analisar."); return
        self.processing = True; self.cancel_requested = False; self.paused = False; self.analysis_results = []; self.start_btn.config(state="disabled"); self.cancel_btn.config(state="normal"); self.pause_btn.config(state="normal", text="Pausar"); self.overall_progress["value"] = 0; self.overall_progress["maximum"] = len(files); self.file_progress["value"] = 0; self.file_progress["maximum"] = 100
        threading.Thread(target=self.run_analysis_only, args=(files,), daemon=True).start()

    def run_analysis_only(self, files):
        ok = 0; total = len(files)
        for idx, src in enumerate(files, start=1):
            self.wait_if_paused()
            if self.cancel_requested: break
            try:
                self.update_row_status(src, status="Analisando", analise="Em andamento"); result = self.analyze_loudnorm(src); self.analysis_results.append(result); self.update_row_status(src, status="Pronto", analise=self.format_analysis_summary(result)); self.queue_log(f"Análise OK: {src.name}"); ok += 1
            except Exception as e:
                self.analysis_results.append({"input": str(src), "error": str(e)}); self.update_row_status(src, status="Erro", analise="Falhou"); self.queue_log(f"Falha na análise: {src.name} - {e}")
            self.set_overall_progress(idx)
        report = self.generate_analysis_report(); self.add_job_history(ok, total, True); self.processing = False; self.start_btn.config(state="normal"); self.cancel_btn.config(state="disabled"); self.pause_btn.config(state="disabled", text="Pausar"); self.status_var.set(f"Dry run concluído: {ok}/{total}"); self.detail_var.set(f"Relatório de análise: {report.name}"); self.refresh_queue_view()

    def analyze_selected_files(self):
        if self.processing: return
        selected = self.selected_audio_paths()
        if not selected: messagebox.showwarning("Sem seleção", "Selecione um ou mais arquivos na tabela."); return
        self.processing = True; self.cancel_requested = False; self.paused = False; self.analysis_results = []; self.start_btn.config(state="disabled"); self.cancel_btn.config(state="normal"); self.pause_btn.config(state="normal", text="Pausar"); self.overall_progress["value"] = 0; self.overall_progress["maximum"] = len(selected)
        threading.Thread(target=self.analyze_selected_worker, args=(selected,), daemon=True).start()

    def analyze_selected_worker(self, selected):
        ok = 0; total = len(selected)
        for idx, src in enumerate(selected, start=1):
            self.wait_if_paused()
            if self.cancel_requested: break
            try:
                self.update_row_status(src, status="Analisando", analise="Em andamento"); result = self.analyze_loudnorm(src); self.analysis_results.append(result); self.update_row_status(src, status="Pronto", analise=self.format_analysis_summary(result)); ok += 1
            except Exception as e:
                self.update_row_status(src, status="Erro", analise="Falhou"); self.analysis_results.append({"input": str(src), "error": str(e)})
            self.set_overall_progress(idx)
        self.generate_analysis_report(); self.add_job_history(ok, total, True); self.processing = False; self.start_btn.config(state="normal"); self.cancel_btn.config(state="disabled"); self.pause_btn.config(state="disabled", text="Pausar"); self.status_var.set(f"Reanálise concluída: {ok}/{total}"); self.refresh_queue_view()

    def start_processing(self):
        files = self.get_audio_input_files()
        if not files: messagebox.showwarning("Sem arquivos", "Nenhum arquivo válido encontrado para processar."); return
        self.start_job_queue(files, selected_mode=False, queue_label="lote")

    def process_selected_files(self):
        selected = self.selected_audio_paths()
        if not selected: messagebox.showwarning("Sem seleção", "Selecione um ou mais arquivos na tabela."); return
        self.start_job_queue(selected, selected_mode=True, queue_label="selecionados")

    def process_error_files(self):
        files = []
        for path_str, state in self.row_state.items():
            if state.get("status", "").strip().lower() == "erro":
                p = Path(path_str)
                if p.exists(): files.append(p)
        if not files: messagebox.showinfo("Sem erros", "Não há arquivos com status Erro para reprocessar."); return
        self.start_job_queue(files, selected_mode=True, queue_label="somente erros")

    def should_process_output(self, dst: Path):
        if not dst.exists(): return True, "NOVO"
        if self.skip_existing_var.get(): return False, "PULAR_EXISTENTE"
        if not self.confirm_overwrite_var.get(): return True, "SOBRESCREVER_SEM_CONFIRMAR"
        if self.overwrite_all_decision is True: return True, "SOBRESCREVER_TODOS"
        if self.overwrite_all_decision is False: return False, "PULAR_TODOS"
        return None, "PERGUNTAR"

    def ask_overwrite_decision(self, dst: Path):
        answer = messagebox.askyesnocancel("Arquivo existente", f"O arquivo já existe:\n{dst}\n\nSim = sobrescrever este e os próximos\nNão = pular este e os próximos\nCancelar = abortar processamento")
        if answer is True: self.overwrite_all_decision = True; return True
        if answer is False: self.overwrite_all_decision = False; return False
        self.cancel_requested = True; return None

    def start_job_queue(self, files, selected_mode=False, queue_label="lote"):
        if self.processing: messagebox.showwarning("Em processamento", "Aguarde o processamento atual terminar."); return
        if not FFMPEG_EXE.exists() or not FFPROBE_EXE.exists(): messagebox.showerror("FFmpeg/FFprobe ausente", "Verifique ffmpeg.exe e ffprobe.exe em ffmpeg."); return
        output_dir = Path(self.output_var.get()); output_dir.mkdir(parents=True, exist_ok=True); self.save_current_settings(); self.processing = True; self.cancel_requested = False; self.paused = False; self.last_results = []; self.last_technical_lines = []; self.overwrite_all_decision = None; self.start_btn.config(state="disabled"); self.cancel_btn.config(state="normal"); self.pause_btn.config(state="normal", text="Pausar"); self.overall_progress["value"] = 0; self.overall_progress["maximum"] = len(files); self.file_progress["value"] = 0; self.file_progress["maximum"] = 100; self.status_var.set(f"Processando {queue_label}..."); self.detail_var.set(f"Jobs na fila: {len(files)}")
        threading.Thread(target=self.process_files, args=(files, output_dir, selected_mode, queue_label), daemon=True).start()

    def run_ffmpeg(self, src: Path, dst: Path):
        target_lufs = self.lufs_var.get().strip() or "-14"; true_peak = self.tp_var.get().strip() or "-1.5"; lra = self.lra_var.get().strip() or "11"; sample_rate = self.rate_var.get().strip() or "48000"; bitrate = self.bitrate_var.get().strip() or "320k"; out_ext = dst.suffix.lower(); duration_seconds = self.get_media_info(src).get("duration")
        extra_gain = float(self.manual_gain_var.get())
        if abs(extra_gain) > 0.01:
            gain_db = f",volume={extra_gain:.2f}dB"
        else:
            gain_db = ""
        if self.two_pass_var.get():
            analysis = self.analyze_loudnorm(src); self.update_row_status(src, analise=self.format_analysis_summary(analysis))
            af = f"loudnorm=I={target_lufs}:TP={true_peak}:LRA={lra}:measured_I={self.safe_loudnorm_value(analysis.get('input_i'), -20.0)}:measured_TP={self.safe_loudnorm_value(analysis.get('input_tp'), -6.0)}:measured_LRA={self.safe_loudnorm_value(analysis.get('input_lra'), 1.0)}:measured_thresh={self.safe_loudnorm_value(analysis.get('input_thresh'), -30.0)}:offset={self.safe_loudnorm_value(analysis.get('target_offset'), 0.0)}:linear=true" + gain_db
        else: af = f"loudnorm=I={target_lufs}:TP={true_peak}:LRA={lra}" + gain_db
        cmd = [str(FFMPEG_EXE), "-y", "-hide_banner", "-progress", "pipe:1", "-nostats", "-i", str(src)]
        if self.preserve_metadata_var.get(): cmd += ["-map_metadata", "0"]
        cmd += ["-af", af, "-ar", sample_rate]
        if out_ext == ".mp3": cmd += ["-codec:a", "libmp3lame", "-b:a", bitrate, "-id3v2_version", "3", "-write_id3v1", "1"]
        elif out_ext == ".ogg": cmd += ["-codec:a", "libvorbis", "-q:a", "6"]
        else: cmd += ["-codec:a", "pcm_s16le"]
        cmd.append(str(dst)); self.current_process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, universal_newlines=True); progress_lines = []
        while True:
            self.wait_if_paused()
            if self.cancel_requested: raise RuntimeError("Processamento cancelado pelo usuário")
            line = self.current_process.stdout.readline()
            if not line:
                if self.current_process.poll() is not None: break
                time.sleep(0.05); continue
            line = line.strip(); progress_lines.append(line)
            if line.startswith("out_time_ms="):
                try:
                    out_time_ms = int(line.split("=", 1)[1].strip())
                    if duration_seconds and duration_seconds > 0:
                        pct = int(out_time_ms / (duration_seconds * 1000000.0) * 100); self.set_file_progress(pct); self.set_detail(f"Processando... {pct}%")
                except Exception: pass
            elif line.startswith("progress=") and line.endswith("end"): self.set_file_progress(100); self.set_detail("Finalizando arquivo..."); self.root.after(0, lambda n=src.name: self.master_live_var.set(f"Finalizando: {n}"))
        stderr_output = self.current_process.stderr.read().strip(); return_code = self.current_process.wait(); self.current_process = None; technical = "\n".join(progress_lines[-30:])
        if stderr_output: technical += "\n" + stderr_output[-2000:]
        if return_code != 0: raise RuntimeError(technical or "Falha desconhecida no FFmpeg")
        self.root.after(0, lambda: self.master_live_progress.configure(value=0))
        self.root.after(0, lambda: self.master_live_var.set("Sem processamento em andamento."))
        return technical

    def generate_reports(self, prefix="master_report"):
        REPORTS_DIR.mkdir(parents=True, exist_ok=True); stamp = datetime.now().strftime("%Y%m%d_%H%M%S"); csv_path = REPORTS_DIR / f"{prefix}_{stamp}.csv"; txt_path = REPORTS_DIR / f"{prefix}_{stamp}.txt"
        with open(csv_path, "w", newline="", encoding="utf-8-sig") as f:
            writer = csv.DictWriter(f, fieldnames=["input", "output", "status", "error"]); writer.writeheader()
            for row in self.last_results: writer.writerow(row)
        with open(txt_path, "w", encoding="utf-8") as f:
            f.write("MASTERMP3 MAIN - LOG TECNICO\n" + "=" * 60 + "\n")
            for block in self.last_technical_lines: f.write(block + "\n\n")
        return csv_path, txt_path

    def export_selected_report(self):
        selected = self.selected_audio_paths()
        if not selected: messagebox.showwarning("Sem seleção", "Selecione um ou mais arquivos."); return
        REPORTS_DIR.mkdir(parents=True, exist_ok=True); stamp = datetime.now().strftime("%Y%m%d_%H%M%S"); csv_path = REPORTS_DIR / f"selected_rows_{stamp}.csv"
        with open(csv_path, "w", newline="", encoding="utf-8-sig") as f:
            writer = csv.writer(f); writer.writerow(["input", "status", "analise", "saida"])
            for src in selected:
                state = self.state_for_path(src); writer.writerow([str(src), state["status"], state["analise"], state["saida"]])
        messagebox.showinfo("Relatório exportado", f"Arquivo gerado:\n{csv_path}")

    def extract_numbers(self, text): return [float(n) for n in re.findall(r"-?\d+(?:\.\d+)?", str(text))]

    def process_files(self, files, output_dir, selected_mode=False, queue_label="lote"):
        ok = 0; total = len(files)
        for idx, src in enumerate(files, start=1):
            self.wait_if_paused()
            if self.cancel_requested: break
            dst = self.build_output_path(src, output_dir); status = "OK"; error = ""; technical = ""
            try:
                decision, reason = self.should_process_output(dst)
                if decision is None and reason == "PERGUNTAR":
                    self.set_detail(f"Confirmando overwrite: {dst.name}"); user_choice = self.ask_overwrite_decision(dst)
                    if user_choice is None: raise RuntimeError("Processamento cancelado pelo usuário")
                    decision = user_choice; reason = "SOBRESCREVER_ESCOLHIDO" if user_choice else "PULAR_ESCOLHIDO"
                if decision is False:
                    status = "PULADO"; technical = f"Output já existe. Ação={reason}"; self.update_row_status(src, status="Pulado", saida=dst.name); self.queue_log(f"PULADO: {dst.name}")
                else:
                    self.update_row_status(src, status="Processando", saida=dst.name); self.queue_log(f"{queue_label.title()} {idx}/{total}: {src}"); self.set_detail(f"Arquivo atual: {src.name}"); technical = self.run_ffmpeg(src, dst); self.update_row_status(src, status="OK", saida=dst.name); self.queue_log(f"OK: {dst.name}"); ok += 1
            except Exception as e:
                status = "ERRO"; error = str(e); technical = str(e); self.update_row_status(src, status="Erro", saida="Cancelado" if self.cancel_requested else "Falhou"); self.queue_log(f"ERRO em {src.name}: {e}")
            self.last_results.append({"input": str(src), "output": str(dst), "status": status, "error": error}); self.last_technical_lines.append(f"{status}\nINPUT={src}\nOUTPUT={dst}\n{technical}"); self.set_overall_progress(idx)
        report_csv, report_txt = self.generate_reports("selected_report" if selected_mode else "master_report"); self.add_job_history(ok, total, False); self.finish_processing(ok, total, report_csv, report_txt, queue_label)

    def finish_processing(self, ok, total, report_csv, report_txt, queue_label="lote"):
        self.processing = False; self.overwrite_all_decision = None; self.start_btn.config(state="normal"); self.cancel_btn.config(state="disabled"); self.pause_btn.config(state="disabled", text="Pausar"); self.file_progress["value"] = 0
        if self.cancel_requested: self.status_var.set(f"Cancelado. Sucesso antes do cancelamento: {ok}/{total}"); self.detail_var.set("Processamento interrompido pelo usuário.")
        else: self.status_var.set(f"Concluído: {ok}/{total} em {queue_label}."); self.detail_var.set(f"Relatórios: {report_csv.name} | {report_txt.name}")
        self.refresh_queue_view()

    def add_job_history(self, ok, total, analysis_only):
        self.job_history.append({"timestamp": datetime.now().strftime("%Y-%m-%d %H:%M:%S"), "mode": self.mode_var.get(), "ok": ok, "total": total, "analysisonly": analysis_only, "preset": self.preset_var.get()})
        self.job_history = self.job_history[-50:]; save_json_file(HISTORY_FILE, self.job_history); self.refresh_history_box()

    def generate_analysis_report(self):
        REPORTS_DIR.mkdir(parents=True, exist_ok=True); stamp = datetime.now().strftime("%Y%m%d_%H%M%S"); path = REPORTS_DIR / f"analysis_report_{stamp}.csv"; fieldnames = sorted({k for row in self.analysis_results for k in row.keys()}) if self.analysis_results else ["input"]
        with open(path, "w", newline="", encoding="utf-8-sig") as f:
            writer = csv.DictWriter(f, fieldnames=fieldnames); writer.writeheader()
            for row in self.analysis_results: writer.writerow(row)
        return path

    def sort_by_column(self, column):
        items = []
        for iid in self.tree.get_children():
            vals = self.tree.item(iid, "values"); mapping = {"arquivo": vals[0], "duracao": vals[1], "ext": vals[2], "title": vals[3], "artist": vals[4], "status": vals[5], "analise": vals[6], "saida": vals[7]}; items.append((mapping[column], iid))
        reverse = not self.sort_state.get(column, False); self.sort_state[column] = reverse
        def duration_key(v):
            text = str(v[0]); parts = text.split(":")
            try:
                if len(parts) == 2: return int(parts[0]) * 60 + int(parts[1])
                if len(parts) == 3: return int(parts[0]) * 3600 + int(parts[1]) * 60 + int(parts[2])
            except Exception: return 0
            return 0
        def analysis_key(v):
            nums = self.extract_numbers(v[0]); return tuple(nums) if nums else (float("inf"),)
        def smart_key(v): return str(v[0]).strip().lower()
        if column == "duracao": items.sort(key=duration_key, reverse=reverse)
        elif column == "analise": items.sort(key=analysis_key, reverse=reverse)
        else: items.sort(key=smart_key, reverse=reverse)
        for index, (_, iid) in enumerate(items): self.tree.move(iid, "", index)

if __name__ == "__main__":
    root = TkinterDnD.Tk() if HAS_DND else tk.Tk()
    try: ttk.Style().theme_use("vista")
    except Exception: pass
    app = AppMain(root)
    root.mainloop()
