import csv
import json
import math
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

APP_MAIN_VERSION = "main_2026-06-10_imagem_complete_module"

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
        self.root.geometry("1700x990")
        self.root.minsize(1400, 900)
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
        self.header_live_hint_var = tk.StringVar(value="Base aprovada pronta para polish ultra pró.")
        self.master_live_var = tk.StringVar(value="Sem processamento em andamento.")
        self.preview_position_var = tk.DoubleVar(value=0.0)
        self.preview_seek_seconds = 0
        self.preview_paused = False
        self.preview_current_target = None
        self.preview_update_job = None
        self.transport_buttons = {}
        self.wave_anim_job = None
        self.wave_anim_phase = 0.0
        self.wave_anim_seed = 0.0
        self.wave_bars = []
        self.wave_peaks = []
        self.waveform_bg_image = None
        self.meta_title_var = tk.StringVar(value="")
        self.meta_artist_var = tk.StringVar(value="")
        self.meta_album_var = tk.StringVar(value="")
        self.meta_genre_var = tk.StringVar(value="")
        self.meta_comment_var = tk.StringVar(value="")
        self.imagen_input_var = tk.StringVar(value=str(INPUT_DIR))
        self.imagen_output_var = tk.StringVar(value=str(OUTPUT_DIR))
        self.imagen_selected_files = []
        self.imagen_preview_ready_var = tk.StringVar(value="Nenhum preview gerado.")
        self.imagen_last_saved_var = tk.StringVar(value="Nada salvo ainda.")
        self.imagen_preview_pil = None
        self.imagen_preview_tk = None
        self.imagen_preview_mode = "Prévia"
        self.imagen_last_operation = None
        self.imagen_last_outputs = []
        self.imagen_convert_preview_pil = None
        self.imagen_convert_from_var = tk.StringVar(value="png")
        self.imagen_convert_to_var = tk.StringVar(value="jpg")
        self.imagen_quality_var = tk.StringVar(value="Alta")
        self.imagen_bg_var = tk.StringVar(value="Transparente")
        self.imagen_resize_preset_var = tk.StringVar(value="Instagram 1080x1080")
        self.imagen_width_var = tk.StringVar(value="1080")
        self.imagen_height_var = tk.StringVar(value="1080")
        self.imagen_keep_ratio_resize_var = tk.BooleanVar(value=True)
        self.imagen_icon_preset_var = tk.StringVar(value="256x256")
        self.imagen_icon_width_var = tk.StringVar(value="256")
        self.imagen_icon_height_var = tk.StringVar(value="256")
        self.imagen_keep_ratio_icon_var = tk.BooleanVar(value=True)
        self.imagen_icon_preview_pil = None
        self.imagen_preview_title_var = tk.StringVar(value="Preview Imagem")
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
        self.root.after(180, self.animate_preview_wave)
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)

    def configure_professional_styles(self):
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass
        bg = "#d6d3cd"
        panel = "#d1cec8"
        panel2 = "#c8c4bc"
        edge = "#a39d94"
        text = "#302d29"
        muted = "#5b5650"
        accent = "#31d58b"
        accenthover = "#25bb79"
        warn = "#d8a84a"
        danger = "#b86c59"
        violet = "#8577ae"
        lime = "#1f1f1f"
        stopbg = "#c1bbb2"
        self.root.configure(bg=bg)
        style.configure("TNotebook", background=bg, borderwidth=0)
        style.configure("TNotebook.Tab", background=panel, foreground=text, padding=(10, 5), borderwidth=1)
        style.map("TNotebook.Tab", background=[("selected", "#c4bfb6")], foreground=[("selected", text)])
        style.configure("TFrame", background=bg)
        style.configure("Card.TFrame", background=panel, relief="flat")
        style.configure("SoftCard.TFrame", background=panel2, relief="flat")
        style.configure("PlayerBar.TFrame", background=panel2, relief="flat")
        style.configure("TLabelframe", background=bg, foreground=text, bordercolor=edge, relief="solid")
        style.configure("TLabelframe.Label", background=bg, foreground=text)
        style.configure("TLabel", background=bg, foreground=text)
        style.configure("Muted.TLabel", background=panel2, foreground=muted)
        style.configure("Hero.TLabel", background=bg, foreground=text, font=("Segoe UI Semibold", 9))
        style.configure("SectionHint.TLabel", background=bg, foreground=muted, font=("Segoe UI", 8))
        style.configure("PlayerTitle.TLabel", background=panel2, foreground=text, font=("Segoe UI Semibold", 9))
        style.configure("Status.TLabel", background=panel2, foreground=muted, font=("Segoe UI", 8))
        style.configure("TCheckbutton", background=bg, foreground=text)
        style.map("TCheckbutton", background=[("active", bg)], foreground=[("active", text)])
        style.configure("TRadiobutton", background=bg, foreground=text)
        style.map("TRadiobutton", background=[("active", bg)], foreground=[("active", text)])
        style.configure("TEntry", fieldbackground="#f7f6f2", foreground=text, insertcolor=text, bordercolor=edge)
        style.configure("TCombobox", fieldbackground="#f7f6f2", foreground=text, bordercolor=edge, arrowsize=14)
        style.configure("TSpinbox", fieldbackground="#f7f6f2", foreground=text, bordercolor=edge, arrowsize=14)
        style.configure("Treeview", background="#f7f6f2", fieldbackground="#f7f6f2", foreground=text, bordercolor=edge, rowheight=26)
        style.map("Treeview", background=[("selected", "#d8e5de")], foreground=[("selected", text)])
        style.configure("Treeview.Heading", background=panel2, foreground=text, relief="flat", font=("Segoe UI Semibold", 9))
        style.map("Treeview.Heading", background=[("active", "#d5d0c8")])
        style.configure("Horizontal.TProgressbar", troughcolor="#beb8af", background=accent, bordercolor=edge, lightcolor=accent, darkcolor=accent)
        style.configure("Primary.TButton", background=panel, foreground=text, borderwidth=1, focusthickness=0, padding=(10, 5))
        style.map("Primary.TButton", background=[("active", "#e6e2db"), ("disabled", panel)], foreground=[("disabled", "#8c877f")])
        style.configure("Danger.TButton", background=panel, foreground=text, borderwidth=1, focusthickness=0, padding=(10, 5))
        style.map("Danger.TButton", background=[("active", "#e6e2db"), ("disabled", panel)])
        style.configure("Secondary.TButton", background=panel, foreground=text, borderwidth=1, focusthickness=0, padding=(10, 5))
        style.map("Secondary.TButton", background=[("active", "#e6e2db"), ("disabled", panel)])
        style.configure("TransportPlay.TButton", background=panel, foreground=text, borderwidth=1, focusthickness=0, padding=(10, 6), relief="flat")
        style.map("TransportPlay.TButton", background=[("active", "#ece9e2"), ("pressed", "#ece9e2")], foreground=[("active", text), ("pressed", text)])
        style.configure("TransportPause.TButton", background=panel, foreground=text, borderwidth=1, focusthickness=0, padding=(8, 4), relief="flat")
        style.map("TransportPause.TButton", background=[("active", "#ece9e2"), ("pressed", "#ece9e2")], foreground=[("active", text), ("pressed", text)])
        style.configure("TransportPrev.TButton", background=panel, foreground=text, borderwidth=1, focusthickness=0, padding=(8, 4), relief="flat")
        style.map("TransportPrev.TButton", background=[("active", "#ece9e2"), ("pressed", "#ece9e2")], foreground=[("active", text), ("pressed", text)])
        style.configure("TransportStop.TButton", background=panel, foreground=text, borderwidth=1, focusthickness=0, padding=(8, 4), relief="flat")
        style.map("TransportStop.TButton", background=[("active", "#ece9e2"), ("pressed", "#ece9e2")], foreground=[("active", text), ("pressed", text)])
        style.configure("TransportNext.TButton", background=panel, foreground=text, borderwidth=1, focusthickness=0, padding=(8, 4), relief="flat")
        style.map("TransportNext.TButton", background=[("active", "#ece9e2"), ("pressed", "#ece9e2")], foreground=[("active", text), ("pressed", text)])
        style.configure("TransportMaster.TButton", background=panel, foreground=text, borderwidth=1, focusthickness=0, padding=(8, 4), relief="flat")
        style.map("TransportMaster.TButton", background=[("active", "#ece9e2"), ("pressed", "#ece9e2")], foreground=[("active", text), ("pressed", text)])
    def build_ui(self):
        self.configure_professional_styles()
        self.notebook = ttk.Notebook(self.root); self.notebook.pack(fill="both", expand=True, padx=10, pady=10)
        self.tab_master = ttk.Frame(self.notebook); self.tab_metadata = ttk.Frame(self.notebook); self.tab_inspection = ttk.Frame(self.notebook)
        self.tab_queue = ttk.Frame(self.notebook); self.tab_settings = ttk.Frame(self.notebook); self.tab_imagen = ttk.Frame(self.notebook); self.tab_help = ttk.Frame(self.notebook)
        self.notebook.add(self.tab_master, text="Masterização"); self.notebook.add(self.tab_metadata, text="Remover metadados")
        self.notebook.add(self.tab_inspection, text="Inspeção"); self.notebook.add(self.tab_queue, text="Fila")
        self.notebook.add(self.tab_settings, text="Configurações"); self.notebook.add(self.tab_imagen, text="Imagem"); self.notebook.add(self.tab_help, text="Ajuda")
        self.build_master_tab(); self.build_metadata_tab(); self.build_inspection_tab(); self.build_queue_tab(); self.build_settings_tab(); self.build_imagen_tab(); self.build_help_tab(); self.build_global_footer()

    def build_master_tab(self):
        pad = {"padx": 8, "pady": 5}
        top = ttk.Frame(self.tab_master); top.pack(fill="x", padx=10, pady=(8, 6))
        ttk.Label(self.tab_master, textvariable=self.header_live_hint_var, style="SectionHint.TLabel").pack(anchor="w", padx=14, pady=(2, 2))
        mode_box = ttk.LabelFrame(top, text="Modo"); mode_box.pack(fill="x")
        ttk.Radiobutton(mode_box, text="Arquivo único", value="singlefile", variable=self.mode_var, command=self.update_mode_ui).grid(row=0, column=0, sticky="w", **pad)
        ttk.Radiobutton(mode_box, text="Pasta inteira", value="folder", variable=self.mode_var, command=self.update_mode_ui).grid(row=0, column=1, sticky="w", **pad)
        ttk.Checkbutton(mode_box, text="Procurar em subpastas", variable=self.recursive_scan_var, command=self.refresh_audio_file_list).grid(row=0, column=2, sticky="w", **pad)
        ttk.Checkbutton(mode_box, text="2-pass loudnorm", variable=self.two_pass_var).grid(row=0, column=3, sticky="w", **pad)
        ttk.Checkbutton(mode_box, text="Pular output existente", variable=self.skip_existing_var).grid(row=0, column=4, sticky="w", **pad)
        ttk.Checkbutton(mode_box, text="Confirmar overwrite", variable=self.confirm_overwrite_var).grid(row=0, column=5, sticky="w", **pad)
        preset_box = ttk.LabelFrame(self.tab_master, text="Presets"); preset_box.pack(fill="x", padx=10, pady=6)
        ttk.Label(preset_box, text="Perfil").grid(row=0, column=0, sticky="w", **pad)
        self.preset_combo = ttk.Combobox(preset_box, textvariable=self.preset_var, state="readonly", width=22); self.preset_combo.grid(row=0, column=1, sticky="w", **pad)
        self.preset_combo.bind("<<ComboboxSelected>>", lambda e: self.apply_preset(self.preset_var.get()))
        ttk.Button(preset_box, text="Salvar", command=self.save_current_as_preset).grid(row=0, column=2, **pad)
        ttk.Button(preset_box, text="Excluir", command=self.delete_selected_custom_preset).grid(row=0, column=3, **pad)
        ttk.Button(preset_box, text="Exportar", command=self.export_presets).grid(row=0, column=4, **pad)
        ttk.Button(preset_box, text="Importar", command=self.import_presets).grid(row=0, column=5, **pad)
        self.preset_desc = ttk.Label(preset_box, text="", style="SectionHint.TLabel"); self.preset_desc.grid(row=0, column=6, sticky="w", **pad)
        preset_box.columnconfigure(6, weight=1)
        path_box = ttk.LabelFrame(self.tab_master, text="Origem e saída"); path_box.pack(fill="x", padx=10, pady=6)
        self.single_file_frame = ttk.Frame(path_box); self.single_file_frame.grid(row=0, column=0, columnspan=5, sticky="ew")
        ttk.Button(self.single_file_frame, text="Adicionar", command=self.add_audio_files).pack(side="left", padx=8, pady=8)
        ttk.Button(self.single_file_frame, text="Remover", command=self.remove_selected_audio_files).pack(side="left", padx=8, pady=8)
        ttk.Button(self.single_file_frame, text="Limpar", command=self.clear_audio_files).pack(side="left", padx=8, pady=8)
        self.dnd_hint = ttk.Label(self.single_file_frame, text="Drag and drop disponível após instalar tkinterdnd2.", style="SectionHint.TLabel"); self.dnd_hint.pack(side="left", padx=10, pady=8)
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
        self.filter_info_label = ttk.Label(filter_box, text="Mostrando todos.", style="SectionHint.TLabel"); self.filter_info_label.grid(row=0, column=5, sticky="w", **pad)
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
        ttk.Label(opts, text="Formato de saída").grid(row=1, column=0, sticky="w", **pad)
        self.output_combo = ttk.Combobox(opts, textvariable=self.format_var, values=["mp3", "wav", "ogg"], state="readonly", width=8); self.output_combo.grid(row=1, column=1, sticky="w", **pad)
        ttk.Checkbutton(opts, text="Manter formato original", variable=self.keep_original_var, command=lambda: (self.update_output_format_ui(), self.refresh_audio_file_list())).grid(row=1, column=2, sticky="w", **pad)
        ttk.Checkbutton(opts, text="Preservar metadados", variable=self.preserve_metadata_var).grid(row=1, column=3, sticky="w", **pad)
        actions = ttk.Frame(self.tab_master); actions.pack(fill="x", padx=10, pady=8)
        ttk.Button(actions, text="Atualizar lista", command=self.refresh_audio_file_list).pack(side="left", padx=5)
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
        for col, width in [("arquivo", 280), ("duracao", 78), ("ext", 56), ("title", 170), ("artist", 150), ("status", 100), ("analise", 180), ("saida", 240)]:
            self.tree.heading(col, text=col.title(), command=lambda c=col: self.sort_by_column(c)); self.tree.column(col, width=width, anchor="w")
        self.tree.pack(fill="both", expand=True, padx=8, pady=8); self.tree.bind("<<TreeviewSelect>>", lambda e: self.generate_waveform_for_selected())
        center_top = ttk.Frame(center); center_top.pack(fill="both", expand=True, padx=2, pady=8)
        self.waveform_label = ttk.Label(center_top, text="Waveform / análise", anchor="center"); self.waveform_label.pack(fill="x", pady=(0, 6))
        self.wave_canvas = tk.Canvas(center_top, height=176, bg="#07111b", highlightthickness=1, highlightbackground="#958f86", bd=0, relief="flat")
        self.wave_canvas.pack(fill="x", expand=True, pady=(0, 8))
        self.build_preview_wave_canvas()
        self.analysis_box = tk.Text(center_top, height=12, wrap="word", bg="#f6f4ef", fg="#302d29", insertbackground="#302d29", relief="flat", bd=1, highlightthickness=1, highlightbackground="#b7b0a5"); self.analysis_box.pack(fill="both", expand=True); self.analysis_box.insert("end", "Selecione um arquivo para gerar waveform e mostrar análises.\nDurante o Play, o quadro acima movimenta como um VU dinâmico.\nLayout preparado para expansão futura de ferramentas visuais.")
        right_pane = ttk.Panedwindow(right, orient="vertical"); right_pane.pack(fill="both", expand=True, padx=8, pady=8)
        log_frame = ttk.Frame(right_pane); hist_frame = ttk.Frame(right_pane); right_pane.add(log_frame, weight=3); right_pane.add(hist_frame, weight=2)
        ttk.Label(log_frame, textvariable=self.preview_status_var).pack(anchor="w", padx=2, pady=(2, 4))
        self.preview_progress = ttk.Progressbar(log_frame, mode="determinate", maximum=100, variable=self.preview_position_var)
        self.preview_progress.pack(fill="x", padx=2, pady=(0, 6))
        ttk.Label(log_frame, textvariable=self.master_live_var).pack(anchor="w", padx=2, pady=(0, 4))
        self.master_live_progress = ttk.Progressbar(log_frame, mode="determinate")
        self.master_live_progress.pack(fill="x", padx=2, pady=(0, 6))
        self.log_text = tk.Text(log_frame, height=12, wrap="word", bg="#f6f4ef", fg="#302d29", insertbackground="#302d29", relief="flat", bd=1, highlightthickness=1, highlightbackground="#b7b0a5"); self.log_text.pack(fill="both", expand=True)
        self.history_text = tk.Text(hist_frame, height=8, wrap="word", bg="#f6f4ef", fg="#302d29", insertbackground="#302d29", relief="flat", bd=1, highlightthickness=1, highlightbackground="#b7b0a5"); self.history_text.pack(fill="both", expand=True)
        if HAS_DND:
            self.tree.drop_target_register(DNDFILES); self.tree.dnd_bind("<<Drop>>", self.on_audio_drop)
        else:
            self.dnd_hint.config(text="Drag and drop disponível após instalar tkinterdnd2.")

    def build_preview_wave_canvas(self):
        if not hasattr(self, "wave_canvas"):
            return
        c = self.wave_canvas
        c.delete("all")
        c.update_idletasks()
        width = max(c.winfo_width(), c.winfo_reqwidth(), 520)
        height = max(c.winfo_height(), 176)
        mid = height // 2
        c.create_rectangle(0, 0, width, height, fill="#06101a", outline="")
        c.create_line(0, mid, width, mid, fill="#183149", width=1)
        c.create_text(width - 10, 12, text="Preview dinâmico", fill="#d7d0c4", anchor="e", font=("Segoe UI", 8))
        bars = 34
        side_pad = 2
        gap = 2
        usable = max(120, width - side_pad * 2 - 2)
        bar_w = max(3, int((usable - (bars - 1) * gap) / bars))
        total_w = bars * bar_w + (bars - 1) * gap
        start_x = side_pad
        self.wave_bars = []
        self.wave_peaks = []
        for i in range(bars):
            x0 = start_x + i * (bar_w + gap)
            x1 = x0 + bar_w
            bar = c.create_rectangle(x0, mid - 8, x1, mid + 8, fill="#36d399", outline="")
            peak = c.create_rectangle(x0, mid - 11, x1, mid - 8, fill="#f0c04d", outline="")
            self.wave_bars.append(bar)
            self.wave_peaks.append(peak)

    def set_wave_idle_state(self):
        if not hasattr(self, "wave_canvas"):
            return
        if not self.wave_bars:
            self.build_preview_wave_canvas()
        c = self.wave_canvas
        height = max(c.winfo_height(), 176)
        mid = height // 2
        for i, bar in enumerate(self.wave_bars):
            x0, _, x1, _ = c.coords(bar)
            base = 7 + (i % 3)
            c.coords(bar, x0, mid - base, x1, mid + base)
            c.coords(self.wave_peaks[i], x0, mid - base - 3, x1, mid - base - 1)

    def animate_preview_wave(self):
        try:
            if not hasattr(self, "wave_canvas"):
                self.wave_anim_job = self.root.after(90, self.animate_preview_wave)
                return
            if not self.wave_bars:
                self.build_preview_wave_canvas()
            c = self.wave_canvas
            height = max(c.winfo_height(), 176)
            mid = height // 2
            playing = bool(self.preview_process and self.preview_process.poll() is None and not self.preview_paused)
            if playing:
                self.wave_anim_phase += 0.24
                self.wave_anim_seed += 0.11
            else:
                self.wave_anim_phase += 0.05
            for i, bar in enumerate(self.wave_bars):
                x0, _, x1, _ = c.coords(bar)
                if playing:
                    s1 = abs(math.sin(self.wave_anim_phase + i * 0.31))
                    s2 = abs(math.sin(self.wave_anim_phase * 0.67 + i * 0.17 + self.wave_anim_seed))
                    s3 = abs(math.cos(self.wave_anim_phase * 1.23 + i * 0.09))
                    shape = 0.72 + 0.28 * abs(math.sin((i / max(len(self.wave_bars), 1)) * math.pi))
                    amp = int((16 + s1 * 30 + s2 * 16 + s3 * 9) * shape)
                    peak = min(amp + 4 + int(5 * abs(math.sin(self.wave_anim_phase + i * 0.13))), 76)
                else:
                    amp = 7 + (i % 3)
                    peak = amp + 2
                c.coords(bar, x0, mid - amp, x1, mid + amp)
                c.coords(self.wave_peaks[i], x0, mid - peak - 3, x1, mid - peak)
            self.wave_anim_job = self.root.after(60 if playing else 120, self.animate_preview_wave)
        except Exception:
            self.wave_anim_job = self.root.after(180, self.animate_preview_wave)

    def build_metadata_tab(self):
        pad = {"padx": 8, "pady": 5}
        intro = ttk.LabelFrame(self.tab_metadata, text="Metadados"); intro.pack(fill="x", padx=10, pady=8)
        ttk.Label(intro, text="Aba pronta para inspeção, edição, visualização e gravação de metadados.").grid(row=0, column=0, sticky="w", **pad)
        ttk.Label(intro, textvariable=self.exiftool_status_var).grid(row=0, column=1, sticky="w", **pad)
        config = ttk.LabelFrame(self.tab_metadata, text="Saída"); config.pack(fill="x", padx=10, pady=6)
        ttk.Label(config, text="Modo de saída").grid(row=0, column=0, sticky="w", **pad)
        ttk.Combobox(config, textvariable=self.metadata_output_mode_var, values=["copy", "overwrite"], state="readonly", width=12).grid(row=0, column=1, sticky="w", **pad)
        ttk.Label(config, text="Sufixo").grid(row=0, column=2, sticky="w", **pad)
        ttk.Entry(config, textvariable=self.metadata_suffix_var, width=12).grid(row=0, column=3, sticky="w", **pad)
        ttk.Label(config, text="Política").grid(row=0, column=4, sticky="w", **pad)
        ttk.Combobox(config, textvariable=self.metadata_policy_var, values=["all", "gpsonly", "textonly"], state="readonly", width=14).grid(row=0, column=5, sticky="w", **pad)
        ttk.Button(config, text="Salvar", command=self.save_current_settings).grid(row=0, column=6, **pad)
        actions = ttk.Frame(self.tab_metadata); actions.pack(fill="x", padx=10, pady=6)
        ttk.Button(actions, text="Adicionar", command=self.add_metadata_files).pack(side="left", padx=5)
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
        for col, width in [("arquivo", 290), ("tipo", 95), ("ext", 60), ("status", 120), ("acao", 240)]: self.metadata_tree.heading(col, text=col.title()); self.metadata_tree.column(col, width=width, anchor="w")
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
        top = ttk.LabelFrame(self.tab_inspection, text="Inspeção"); top.pack(fill="x", padx=10, pady=8)
        ttk.Label(top, text="A aba de inspeção centraliza leitura de informações técnicas e metadados.").grid(row=0, column=0, sticky="w", **pad)
        ttk.Label(top, textvariable=self.ffmpeg_status_var).grid(row=0, column=1, sticky="w", **pad)
        ttk.Label(top, textvariable=self.exiftool_status_var).grid(row=0, column=2, sticky="w", **pad)
        actions = ttk.Frame(self.tab_inspection); actions.pack(fill="x", padx=10, pady=6)
        ttk.Button(actions, text="Áudio", command=self.inspect_current_audio).pack(side="left", padx=5)
        ttk.Button(actions, text="Mídia", command=self.inspect_selected_metadata_real).pack(side="left", padx=5)
        ttk.Button(actions, text="Status", command=self.refresh_tool_status_labels).pack(side="left", padx=5)
        self.inspection_text = tk.Text(self.tab_inspection, wrap="word"); self.inspection_text.pack(fill="both", expand=True, padx=10, pady=10)
        self.inspection_text.insert("end", "Esta área mostrará leituras consolidadas com FFprobe e ExifTool.")

    def build_queue_tab(self):
        top = ttk.LabelFrame(self.tab_queue, text="Fila"); top.pack(fill="x", padx=10, pady=8)
        ttk.Label(top, text="Fila compartilhada entre masterização e metadados.").pack(anchor="w", padx=10, pady=8)
        actions = ttk.Frame(self.tab_queue); actions.pack(fill="x", padx=10, pady=6)
        ttk.Button(actions, text="Atualizar", command=self.refresh_queue_view).pack(side="left", padx=5)
        ttk.Button(actions, text="Pausar", command=self.toggle_pause).pack(side="left", padx=5)
        ttk.Button(actions, text="Cancelar", command=self.request_cancel).pack(side="left", padx=5)
        cols = ("tipo", "arquivo", "status", "detalhe")
        self.queue_tree = ttk.Treeview(self.tab_queue, columns=cols, show="headings", height=18)
        for col, width in [("tipo", 100), ("arquivo", 420), ("status", 120), ("detalhe", 520)]: self.queue_tree.heading(col, text=col.title()); self.queue_tree.column(col, width=width, anchor="w")
        self.queue_tree.pack(fill="both", expand=True, padx=10, pady=10)

    def build_settings_tab(self):
        pad = {"padx": 8, "pady": 5}
        paths = ttk.LabelFrame(self.tab_settings, text="Caminhos"); paths.pack(fill="x", padx=10, pady=8)
        rows = [("Base", str(BASE_DIR)), ("Input", self.input_var.get()), ("Output", self.output_var.get()), ("FFmpeg", str(FFMPEG_EXE)), ("FFprobe", str(FFPROBE_EXE)), ("FFplay", str(FFPLAY_EXE)), ("ExifTool", str(EXIFTOOL_EXE))]
        for i, (label, value) in enumerate(rows): ttk.Label(paths, text=label).grid(row=i, column=0, sticky="w", **pad); ttk.Label(paths, text=value).grid(row=i, column=1, sticky="w", **pad)
        prefs = ttk.LabelFrame(self.tab_settings, text="Preferências"); prefs.pack(fill="x", padx=10, pady=8)
        ttk.Checkbutton(prefs, text="Logs detalhados", variable=self.show_detailed_logs_var).grid(row=0, column=0, sticky="w", **pad)
        ttk.Checkbutton(prefs, text="Preservar metadados no módulo de masterização", variable=self.preserve_metadata_var).grid(row=0, column=1, sticky="w", **pad)
        ttk.Checkbutton(prefs, text="Pular output existente", variable=self.skip_existing_var).grid(row=0, column=2, sticky="w", **pad)
        ttk.Button(prefs, text="Salvar", command=self.save_current_settings).grid(row=0, column=3, **pad)

    def build_imagen_tab(self):
        pad = {"padx": 8, "pady": 5}
        ttk.Label(self.tab_imagen, text="REDIMENSIONADOR | CONVERSOR | GERADOR DE ICONE", style="Hero.TLabel").pack(anchor="w", padx=14, pady=(8, 2))
        ttk.Label(self.tab_imagen, text="Fluxo sugerido: escolher arquivos, visualizar, converter e salvar se o resultado estiver de acordo.", style="SectionHint.TLabel").pack(anchor="w", padx=14, pady=(0, 6))
        body = ttk.Panedwindow(self.tab_imagen, orient="horizontal")
        body.pack(fill="both", expand=True, padx=10, pady=(4, 10))
        left = ttk.Frame(body)
        right = ttk.LabelFrame(body, text="Preview")
        body.add(left, weight=5)
        body.add(right, weight=3)

        source_box = ttk.LabelFrame(left, text="Origem e saída")
        source_box.pack(fill="x", pady=6)
        ttk.Label(source_box, text="Entrada").grid(row=0, column=0, sticky="w", **pad)
        ttk.Entry(source_box, textvariable=self.imagen_input_var, width=78).grid(row=0, column=1, sticky="ew", **pad)
        ttk.Button(source_box, text="Pasta", command=self.choose_imagen_input).grid(row=0, column=2, **pad)
        ttk.Button(source_box, text="Arquivo", command=self.choose_imagen_single_file).grid(row=0, column=3, **pad)
        ttk.Button(source_box, text="Vários", command=self.choose_imagen_multiple_files).grid(row=0, column=4, **pad)
        ttk.Label(source_box, text="Saída").grid(row=1, column=0, sticky="w", **pad)
        ttk.Entry(source_box, textvariable=self.imagen_output_var, width=78).grid(row=1, column=1, sticky="ew", **pad)
        ttk.Button(source_box, text="Pasta", command=self.choose_imagen_output).grid(row=1, column=2, **pad)
        ttk.Button(source_box, text="Abrir saída", command=self.open_imagen_output_folder).grid(row=1, column=3, **pad)
        ttk.Label(source_box, textvariable=self.imagen_preview_ready_var, style="SectionHint.TLabel").grid(row=2, column=0, columnspan=3, sticky="w", **pad)
        ttk.Label(source_box, textvariable=self.imagen_last_saved_var, style="SectionHint.TLabel").grid(row=2, column=3, columnspan=2, sticky="w", **pad)
        source_box.columnconfigure(1, weight=1)

        grid = ttk.Frame(left)
        grid.pack(fill="both", expand=True)
        conv_box = ttk.LabelFrame(grid, text="Conversão")
        resize_box = ttk.LabelFrame(grid, text="Redimensionar")
        icon_box = ttk.LabelFrame(grid, text="Gerador de .icone")
        conv_box.grid(row=0, column=0, sticky="nsew", padx=(0, 6), pady=6)
        resize_box.grid(row=0, column=1, sticky="nsew", padx=6, pady=6)
        icon_box.grid(row=0, column=2, sticky="nsew", padx=(6, 0), pady=6)
        grid.columnconfigure(0, weight=1)
        grid.columnconfigure(1, weight=1)
        grid.columnconfigure(2, weight=1)
        grid.rowconfigure(0, weight=1)

        ttk.Label(conv_box, text="Converter, visualizar e salvar.", style="SectionHint.TLabel").grid(row=0, column=0, columnspan=2, sticky="w", **pad)
        ttk.Label(conv_box, text="De").grid(row=1, column=0, sticky="w", **pad)
        ttk.Combobox(conv_box, textvariable=self.imagen_convert_from_var, values=["png", "jpg", "jpeg", "webp", "bmp", "tiff", "ico"], state="readonly", width=18).grid(row=1, column=1, sticky="ew", **pad)
        ttk.Label(conv_box, text="Para").grid(row=2, column=0, sticky="w", **pad)
        ttk.Combobox(conv_box, textvariable=self.imagen_convert_to_var, values=["png", "jpg", "jpeg", "webp", "bmp", "tiff", "ico"], state="readonly", width=18).grid(row=2, column=1, sticky="ew", **pad)
        ttk.Label(conv_box, text="Qualidade").grid(row=3, column=0, sticky="w", **pad)
        ttk.Combobox(conv_box, textvariable=self.imagen_quality_var, values=["Baixa", "Média", "Alta", "Máxima"], state="readonly", width=18).grid(row=3, column=1, sticky="ew", **pad)
        ttk.Label(conv_box, text="Fundo").grid(row=4, column=0, sticky="w", **pad)
        ttk.Combobox(conv_box, textvariable=self.imagen_bg_var, values=["Transparente", "Branco", "Preto", "Automático"], state="readonly", width=18).grid(row=4, column=1, sticky="ew", **pad)
        ttk.Button(conv_box, text="Visualizar", command=self.imagen_prepare_conversion_preview).grid(row=5, column=0, sticky="ew", **pad)
        ttk.Button(conv_box, text="Salvar", command=self.imagen_save_conversion_result).grid(row=5, column=1, sticky="ew", **pad)
        ttk.Button(conv_box, text="Converter", command=self.imagen_prepare_conversion_preview).grid(row=6, column=0, columnspan=2, sticky="ew", **pad)
        conv_box.columnconfigure(1, weight=1)

        ttk.Label(resize_box, text="Presets + tamanho manual + proporção.", style="SectionHint.TLabel").grid(row=0, column=0, columnspan=2, sticky="w", **pad)
        ttk.Label(resize_box, text="Preset").grid(row=1, column=0, sticky="w", **pad)
        self.imagen_resize_preset_combo = ttk.Combobox(resize_box, textvariable=self.imagen_resize_preset_var, values=["Instagram 1080x1080", "Feed 1350x1080", "Story 1080x1920", "YouTube Thumb 1280x720", "HD 1920x1080", "4K 3840x2160", "Avatar 512x512", "Livre"], state="readonly", width=22)
        self.imagen_resize_preset_combo.grid(row=1, column=1, sticky="ew", **pad)
        self.imagen_resize_preset_combo.bind("<<ComboboxSelected>>", self.on_imagen_resize_preset)
        ttk.Label(resize_box, text="Largura").grid(row=2, column=0, sticky="w", **pad)
        ttk.Entry(resize_box, textvariable=self.imagen_width_var, width=16).grid(row=2, column=1, sticky="ew", **pad)
        ttk.Label(resize_box, text="Altura").grid(row=3, column=0, sticky="w", **pad)
        ttk.Entry(resize_box, textvariable=self.imagen_height_var, width=16).grid(row=3, column=1, sticky="ew", **pad)
        ttk.Checkbutton(resize_box, text="Manter proporção", variable=self.imagen_keep_ratio_resize_var).grid(row=4, column=0, columnspan=2, sticky="w", **pad)
        ttk.Button(resize_box, text="Visualizar", command=self.imagen_prepare_resize_preview).grid(row=5, column=0, sticky="ew", **pad)
        ttk.Button(resize_box, text="Salvar", command=self.imagen_save_resize_result).grid(row=5, column=1, sticky="ew", **pad)
        ttk.Button(resize_box, text="Redimensionar", command=self.imagen_prepare_resize_preview).grid(row=6, column=0, columnspan=2, sticky="ew", **pad)
        resize_box.columnconfigure(1, weight=1)

        ttk.Label(icon_box, text="Tamanhos padrão, manual e preview.", style="SectionHint.TLabel").grid(row=0, column=0, columnspan=2, sticky="w", **pad)
        ttk.Label(icon_box, text="Preset").grid(row=1, column=0, sticky="w", **pad)
        ttk.Combobox(icon_box, textvariable=self.imagen_icon_preset_var, values=["16x16", "24x24", "32x32", "48x48", "64x64", "128x128", "256x256", "512x512", "Livre"], state="readonly", width=18).grid(row=1, column=1, sticky="ew", **pad)
        ttk.Label(icon_box, text="Largura").grid(row=2, column=0, sticky="w", **pad)
        ttk.Entry(icon_box, textvariable=self.imagen_icon_width_var, width=16).grid(row=2, column=1, sticky="ew", **pad)
        ttk.Label(icon_box, text="Altura").grid(row=3, column=0, sticky="w", **pad)
        ttk.Entry(icon_box, textvariable=self.imagen_icon_height_var, width=16).grid(row=3, column=1, sticky="ew", **pad)
        ttk.Checkbutton(icon_box, text="Manter proporção", variable=self.imagen_keep_ratio_icon_var).grid(row=4, column=0, columnspan=2, sticky="w", **pad)
        ttk.Button(icon_box, text="Visualizar", command=self.imagen_prepare_icon_preview).grid(row=5, column=0, sticky="ew", **pad)
        ttk.Button(icon_box, text="Salvar", command=self.imagen_save_icon_result).grid(row=5, column=1, sticky="ew", **pad)
        ttk.Button(icon_box, text="Gerar .icone", command=self.imagen_prepare_icon_preview).grid(row=6, column=0, columnspan=2, sticky="ew", **pad)
        icon_box.columnconfigure(1, weight=1)

        ttk.Label(right, textvariable=self.imagen_preview_title_var, style="Hero.TLabel").pack(anchor="w", padx=10, pady=(10, 6))
        ttk.Label(right, text="Preview do resultado antes de salvar.", style="SectionHint.TLabel").pack(anchor="w", padx=10, pady=(0, 6))
        self.imagen_preview_canvas = tk.Canvas(right, bg="#0a1420", highlightthickness=1, highlightbackground="#958f86", bd=0, relief="flat")
        self.imagen_preview_canvas.pack(fill="both", expand=True, padx=10, pady=(0, 10))
        self.draw_imagen_preview()

    def choose_imagen_input(self):
        folder = filedialog.askdirectory(initialdir=self.imagen_input_var.get() or str(BASE_DIR))
        if folder:
            self.imagen_input_var.set(folder)
            self.imagen_selected_files = []
            self.imagen_preview_ready_var.set(f"Origem definida: {folder}")
            self.imagen_preview_pil = None
            self.imagen_preview_tk = None
            self.draw_imagen_preview()

    def choose_imagen_output(self):
        folder = filedialog.askdirectory(initialdir=self.imagen_output_var.get() or str(BASE_DIR))
        if folder:
            self.imagen_output_var.set(folder)
            self.imagen_last_saved_var.set(f"Destino: {folder}")
            self.draw_imagen_preview()

    def choose_imagen_single_file(self):
        fp = filedialog.askopenfilename(title="Escolher imagem", initialdir=self.imagen_input_var.get() or str(INPUT_DIR), filetypes=[("Imagens", "*.png *.jpg *.jpeg *.webp *.bmp *.tiff *.ico")])
        if fp:
            self.imagen_selected_files = [fp]
            self.imagen_input_var.set(str(Path(fp).parent))
            self.imagen_preview_ready_var.set(f"1 arquivo selecionado: {Path(fp).name}")
            self.imagen_preview_pil = None
            self.imagen_preview_tk = None
            self.draw_imagen_preview()

    def choose_imagen_multiple_files(self):
        fps = filedialog.askopenfilenames(title="Escolher várias imagens", initialdir=self.imagen_input_var.get() or str(INPUT_DIR), filetypes=[("Imagens", "*.png *.jpg *.jpeg *.webp *.bmp *.tiff *.ico")])
        if fps:
            self.imagen_selected_files = list(fps)
            self.imagen_input_var.set(str(Path(fps[0]).parent))
            self.imagen_preview_ready_var.set(f"{len(fps)} arquivos selecionados")
            self.imagen_preview_pil = None
            self.imagen_preview_tk = None
            self.draw_imagen_preview()

    def open_imagen_output_folder(self):
        p = Path(self.imagen_output_var.get())
        p.mkdir(parents=True, exist_ok=True)
        try:
            os.startfile(str(p))
        except Exception:
            messagebox.showinfo("Saída", str(p))

    def on_imagen_resize_preset(self, event=None):
        presets = {
            "Instagram 1080x1080": (1080, 1080),
            "Feed 1350x1080": (1350, 1080),
            "Story 1080x1920": (1080, 1920),
            "YouTube Thumb 1280x720": (1280, 720),
            "HD 1920x1080": (1920, 1080),
            "4K 3840x2160": (3840, 2160),
            "Avatar 512x512": (512, 512),
        }
        sel = self.imagen_resize_preset_var.get()
        if sel in presets:
            w, h = presets[sel]
            self.imagen_width_var.set(str(w))
            self.imagen_height_var.set(str(h))

    def _imagen_square_icon(self, img, size):
        from PIL import Image, ImageOps
        img = ImageOps.exif_transpose(img)
        if img.mode not in ('RGBA', 'RGB'):
            img = img.convert('RGBA')
        bg = Image.new('RGBA', (size, size), (0, 0, 0, 0))
        copy = img.copy()
        copy.thumbnail((size, size), Image.Resampling.LANCZOS)
        ox = (size - copy.size[0]) // 2
        oy = (size - copy.size[1]) // 2
        bg.paste(copy, (ox, oy), copy if copy.mode == 'RGBA' else None)
        return bg

    def _imagen_icon_sizes(self):
        preset = self.imagen_icon_preset_var.get()
        presets = {
            '16x16': [16], '24x24': [24], '32x32': [32], '48x48': [48], '64x64': [64], '128x128': [128], '256x256': [256], '512x512': [512]
        }
        if preset in presets:
            return presets[preset]
        try:
            a = int(self.imagen_icon_width_var.get())
            b = int(self.imagen_icon_height_var.get())
            s = max(16, min(a, b)) if self.imagen_keep_ratio_icon_var.get() else max(16, a, b)
            return sorted({16, 24, 32, 48, 64, 128, 256, s})
        except Exception:
            return [16, 32, 48, 64, 128, 256]

    def imagen_prepare_icon_preview(self):
        try:
            src, img = self._imagen_open_source_image()
            size = max(16, int(self.imagen_icon_width_var.get() or '256'))
            preview_img = self._imagen_square_icon(img, size)
            self.imagen_preview_pil = preview_img
            self.imagen_icon_preview_pil = preview_img
            self.imagen_last_operation = 'Ícone'
            self.imagen_preview_mode = 'Ícone'
            self.imagen_preview_title_var.set('Preview Imagem | Ícone')
            self.imagen_preview_ready_var.set(f'Preview pronto: {src.name} | ícone quadrado {size}x{size}')
            self.queue_log(f'Imagem: preview real de ícone gerado para {src.name}.')
            self.draw_imagen_preview('Ícone')
        except Exception as e:
            messagebox.showerror('Ícone', str(e))

    def imagen_save_icon_result(self):
        if self.imagen_last_operation != 'Ícone':
            messagebox.showinfo('Ícone', 'Gere um preview de ícone antes de salvar.')
            return
        files = self._imagen_get_source_files()
        if not files:
            messagebox.showinfo('Ícone', 'Nenhuma imagem selecionada.')
            return
        try:
            from PIL import Image
            out_dir = Path(self.imagen_output_var.get())
            out_dir.mkdir(parents=True, exist_ok=True)
            sizes = self._imagen_icon_sizes()
            outputs = []
            for src in files:
                with Image.open(src) as img:
                    base = self._imagen_square_icon(img, max(sizes))
                    out_path = out_dir / f'{src.stem}.ico'
                    base.save(out_path, format='ICO', sizes=[(s, s) for s in sizes])
                    outputs.append(out_path)
            self.imagen_last_outputs = outputs
            self.imagen_last_saved_var.set(f'{len(outputs)} ícone(s) salvo(s) em {out_dir}')
            self.queue_log(f'Imagem: ícone real salvo em {out_dir}.')
            self.draw_imagen_preview('Ícone')
        except Exception as e:
            messagebox.showerror('Ícone', str(e))

    def _imagen_normalize_for_format(self, img, target_ext):
        ext = target_ext.lower().lstrip('.')
        if ext in {'jpg', 'jpeg'} and img.mode in ('RGBA', 'LA', 'P'):
            bg = Image.new('RGB', img.size, (255, 255, 255))
            alpha = img.getchannel('A') if 'A' in img.getbands() else None
            bg.paste(img.convert('RGBA'), mask=alpha)
            return bg
        if ext in {'bmp', 'jpg', 'jpeg'} and img.mode not in ('RGB', 'L'):
            return img.convert('RGB')
        if ext == 'ico' and img.mode not in ('RGBA', 'RGB'):
            return img.convert('RGBA')
        return img

    def imagen_prepare_conversion_preview(self):
        try:
            from PIL import Image, ImageOps
            src, img = self._imagen_open_source_image()
            img = ImageOps.exif_transpose(img)
            target_ext = self.imagen_convert_to_var.get().lower()
            preview_img = self._imagen_normalize_for_format(img.copy(), target_ext)
            self.imagen_preview_pil = preview_img
            self.imagen_convert_preview_pil = preview_img
            self.imagen_last_operation = 'Conversão'
            self.imagen_preview_mode = 'Conversão'
            self.imagen_preview_title_var.set('Preview Imagem | Conversão')
            self.imagen_preview_ready_var.set(f'Preview pronto: {src.name} | {img.mode} → {preview_img.mode} | .{target_ext}')
            self.queue_log(f'Imagem: preview real de conversão gerado para {src.name}.')
            self.draw_imagen_preview('Conversão')
        except Exception as e:
            messagebox.showerror('Conversão', str(e))

    def imagen_save_conversion_result(self):
        if self.imagen_last_operation != 'Conversão':
            messagebox.showinfo('Conversão', 'Gere um preview de conversão antes de salvar.')
            return
        files = self._imagen_get_source_files()
        if not files:
            messagebox.showinfo('Conversão', 'Nenhuma imagem selecionada.')
            return
        try:
            from PIL import Image, ImageOps
            out_dir = Path(self.imagen_output_var.get())
            out_dir.mkdir(parents=True, exist_ok=True)
            target_ext = self.imagen_convert_to_var.get().lower().lstrip('.')
            quality_map = {'Baixa': 70, 'Média': 82, 'Alta': 92, 'Máxima': 98}
            quality = quality_map.get(self.imagen_quality_var.get(), 92)
            outputs = []
            for src in files:
                with Image.open(src) as img:
                    img = ImageOps.exif_transpose(img)
                    out_img = self._imagen_normalize_for_format(img.copy(), target_ext)
                    out_path = out_dir / f'{src.stem}.{target_ext}'
                    save_kwargs = {}
                    if target_ext in {'jpg', 'jpeg', 'webp'}:
                        save_kwargs['quality'] = quality
                    if target_ext == 'ico':
                        base_w = int(self.imagen_icon_width_var.get() or '256')
                        base_h = int(self.imagen_icon_height_var.get() or '256')
                        size = min(base_w, base_h)
                        save_kwargs['sizes'] = [(size, size)]
                        if out_img.mode != 'RGBA':
                            out_img = out_img.convert('RGBA')
                    out_img.save(out_path, **save_kwargs)
                    outputs.append(out_path)
            self.imagen_last_outputs = outputs
            self.imagen_last_saved_var.set(f'{len(outputs)} arquivo(s) convertido(s) em {out_dir}')
            self.queue_log(f'Imagem: conversão real salva em {out_dir}.')
            self.draw_imagen_preview('Conversão')
        except Exception as e:
            messagebox.showerror('Conversão', str(e))

    def imagen_prepare_preview(self, mode):
        self.imagen_preview_title_var.set(f"Preview Imagem | {mode}")
        selected = len(self.imagen_selected_files)
        base = f"{selected} arquivo(s)" if selected else (Path(self.imagen_input_var.get()).name or self.imagen_input_var.get())
        self.imagen_preview_mode = mode
        self.imagen_preview_ready_var.set(f"Preview pronto para {mode.lower()} | origem: {base}")
        self.draw_imagen_preview(mode)
        self.queue_log(f"Imagem: preview gerado para {mode}.")

    def imagen_save_result(self, mode):
        out = Path(self.imagen_output_var.get())
        out.mkdir(parents=True, exist_ok=True)
        self.imagen_last_saved_var.set(f"Pronto para salvar em: {out}")
        self.queue_log(f"Imagem: fluxo de salvar preparado para {mode}.")
        self.draw_imagen_preview(mode)

    def _imagen_get_source_files(self):
        if self.imagen_selected_files:
            return [Path(x) for x in self.imagen_selected_files]
        folder = Path(self.imagen_input_var.get())
        if folder.exists() and folder.is_dir():
            exts = {'.png', '.jpg', '.jpeg', '.webp', '.bmp', '.tiff', '.ico'}
            return [p for p in folder.iterdir() if p.is_file() and p.suffix.lower() in exts]
        return []

    def _imagen_open_source_image(self):
        files = self._imagen_get_source_files()
        if not files:
            raise FileNotFoundError('Nenhuma imagem encontrada para preview.')
        src = files[0]
        try:
            from PIL import Image
        except Exception as e:
            raise RuntimeError('Pillow não está disponível. Instale com: pip install Pillow') from e
        img = Image.open(src)
        return src, img

    def imagen_prepare_resize_preview(self):
        try:
            target_w = int(self.imagen_width_var.get())
            target_h = int(self.imagen_height_var.get())
            if target_w <= 0 or target_h <= 0:
                raise ValueError
        except Exception:
            messagebox.showerror('Redimensionar', 'Informe largura e altura válidas.')
            return
        try:
            from PIL import Image, ImageOps, ImageTk
            src, img = self._imagen_open_source_image()
            img = ImageOps.exif_transpose(img)
            original_mode = img.mode
            if self.imagen_keep_ratio_resize_var.get():
                preview_img = img.copy()
                preview_img.thumbnail((target_w, target_h), Image.Resampling.LANCZOS)
            else:
                preview_img = img.resize((target_w, target_h), Image.Resampling.LANCZOS)
            self.imagen_preview_pil = preview_img
            self.imagen_last_operation = 'Redimensionar'
            self.imagen_preview_mode = 'Redimensionar'
            self.imagen_preview_title_var.set('Preview Imagem | Redimensionar')
            self.imagen_preview_ready_var.set(f'Preview pronto: {src.name} | {img.size[0]}x{img.size[1]} → {preview_img.size[0]}x{preview_img.size[1]}')
            self.queue_log(f'Imagem: preview real de redimensionamento gerado para {src.name}.')
            self.draw_imagen_preview('Redimensionar')
        except Exception as e:
            messagebox.showerror('Redimensionar', str(e))

    def imagen_save_resize_result(self):
        if self.imagen_last_operation != 'Redimensionar':
            messagebox.showinfo('Redimensionar', 'Gere um preview de redimensionamento antes de salvar.')
            return
        files = self._imagen_get_source_files()
        if not files:
            messagebox.showinfo('Redimensionar', 'Nenhuma imagem selecionada.')
            return
        try:
            from PIL import Image, ImageOps
            target_w = int(self.imagen_width_var.get())
            target_h = int(self.imagen_height_var.get())
            keep = self.imagen_keep_ratio_resize_var.get()
            out_dir = Path(self.imagen_output_var.get())
            out_dir.mkdir(parents=True, exist_ok=True)
            outputs = []
            for src in files:
                with Image.open(src) as img:
                    img = ImageOps.exif_transpose(img)
                    if keep:
                        out_img = img.copy()
                        out_img.thumbnail((target_w, target_h), Image.Resampling.LANCZOS)
                    else:
                        out_img = img.resize((target_w, target_h), Image.Resampling.LANCZOS)
                    ext = src.suffix.lower() if src.suffix.lower() in {'.png', '.jpg', '.jpeg', '.webp', '.bmp', '.tiff'} else '.png'
                    out_path = out_dir / f'{src.stem}_{out_img.size[0]}x{out_img.size[1]}{ext}'
                    save_img = out_img
                    if ext in {'.jpg', '.jpeg'} and save_img.mode in ('RGBA', 'LA', 'P'):
                        save_img = save_img.convert('RGB')
                    save_img.save(out_path)
                    outputs.append(out_path)
            self.imagen_last_outputs = outputs
            self.imagen_last_saved_var.set(f'{len(outputs)} arquivo(s) salvo(s) em {out_dir}')
            self.queue_log(f'Imagem: redimensionamento real salvo em {out_dir}.')
            self.draw_imagen_preview('Redimensionar')
        except Exception as e:
            messagebox.showerror('Redimensionar', str(e))

    def draw_imagen_preview(self, mode="Prévia"):
        if not hasattr(self, "imagen_preview_canvas"):
            return
        c = self.imagen_preview_canvas
        c.delete("all")
        c.update_idletasks()
        w = max(c.winfo_width(), 360)
        h = max(c.winfo_height(), 520)
        c.create_rectangle(0, 0, w, h, fill="#09131d", outline="")
        c.create_text(20, 22, anchor="w", text=mode, fill="#d7d0c4", font=("Segoe UI Semibold", 10))
        frame_x0, frame_y0, frame_x1, frame_y1 = 24, 56, w - 24, h - 34
        c.create_rectangle(frame_x0, frame_y0, frame_x1, frame_y1, outline="#6e8aa3", width=1)
        inner_pad = 24
        x0, y0, x1, y1 = frame_x0 + inner_pad, frame_y0 + inner_pad, frame_x1 - inner_pad, frame_y1 - 162
        c.create_rectangle(x0, y0, x1, y1, fill="#102338", outline="#2d506d")
        if self.imagen_preview_pil is not None:
            try:
                from PIL import ImageTk
                img = self.imagen_preview_pil.copy()
                max_w = max(80, x1 - x0 - 10)
                max_h = max(80, y1 - y0 - 10)
                img.thumbnail((max_w, max_h))
                self.imagen_preview_tk = ImageTk.PhotoImage(img)
                px = (x0 + x1) // 2
                py = (y0 + y1) // 2
                c.create_image(px, py, image=self.imagen_preview_tk)
                c.create_rectangle(x0, y0, x1, y1, outline="#355b79")
            except Exception:
                c.create_line(x0, y0, x1, y1, fill="#284a67")
                c.create_line(x1, y0, x0, y1, fill="#284a67")
        else:
            c.create_line(x0, y0, x1, y1, fill="#284a67")
            c.create_line(x1, y0, x0, y1, fill="#284a67")
            c.create_text((x0+x1)//2, y0+20, text="Pré-visualização", fill="#d7d0c4", font=("Segoe UI", 10))
        selected = self.imagen_selected_files
        source_label = Path(selected[0]).name if len(selected) == 1 else (f"{len(selected)} arquivos" if selected else (Path(self.imagen_input_var.get()).name or self.imagen_input_var.get()))
        card_y = y1 + 18
        lines = [
            f"Origem: {source_label}",
            f"Conversão: {self.imagen_convert_from_var.get()} → {self.imagen_convert_to_var.get()} | {self.imagen_quality_var.get()}",
            f"Resize: {self.imagen_width_var.get()} x {self.imagen_height_var.get()} | proporção {'sim' if self.imagen_keep_ratio_resize_var.get() else 'não'}",
            f"Ícone: {self.imagen_icon_width_var.get()} x {self.imagen_icon_height_var.get()} | proporção {'sim' if self.imagen_keep_ratio_icon_var.get() else 'não'}",
            f"Destino: {Path(self.imagen_output_var.get()).name or self.imagen_output_var.get()}",
            f"Status: {self.imagen_preview_ready_var.get()}"
        ]
        for idx, line in enumerate(lines):
            y = card_y + idx * 28
            c.create_rectangle(x0, y, x1, y + 22, fill="#13283f", outline="#274b68")
            c.create_text(x0 + 10, y + 11, anchor="w", text=line, fill="#d7d0c4", font=("Segoe UI", 8))

    def build_help_tab(self):
        actions = ttk.Frame(self.tab_help); actions.pack(fill="x", padx=10, pady=8)
        ttk.Button(actions, text="Base", command=lambda: os.startfile(str(BASE_DIR))).pack(side="left", padx=5)
        ttk.Button(actions, text="Reports", command=self.open_reports_folder).pack(side="left", padx=5)
        ttk.Button(actions, text="Logs", command=lambda: os.startfile(str(LOGS_DIR))).pack(side="left", padx=5)
        ttk.Button(actions, text="Status", command=self.refresh_tool_status_labels).pack(side="left", padx=5)
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

    def on_close(self):
        self.stop_preview()
        if self.wave_anim_job:
            try:
                self.root.after_cancel(self.wave_anim_job)
            except Exception:
                pass
        self.root.destroy()
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
            if png_path.exists():
                self.waveform_image = tk.PhotoImage(file=str(png_path))
                if hasattr(self, "wave_canvas"):
                    self.wave_canvas.delete("bgwave")
                    self.wave_canvas.delete("bgwave_tint")
                    canvas_w = max(self.wave_canvas.winfo_width(), self.wave_canvas.winfo_reqwidth(), 520)
                    src_img = self.waveform_image
                    img_w = max(1, src_img.width())
                    if img_w > canvas_w:
                        shrink = max(1, round(img_w / canvas_w))
                        if shrink > 1:
                            src_img = src_img.subsample(shrink, 1)
                            img_w = src_img.width()
                    self.waveform_bg_image = src_img
                    self.wave_canvas.create_image(0, 0, image=self.waveform_bg_image, anchor="nw", tags=("bgwave",))
                    self.wave_canvas.tag_lower("bgwave")
                    self.wave_canvas.create_rectangle(0, 0, max(self.wave_canvas.winfo_width(), 320), max(self.wave_canvas.winfo_height(), 176), fill="#06101a", outline="", stipple="gray50", tags=("bgwave_tint",))
                    self.wave_canvas.tag_raise("bgwave_tint", "bgwave")
                    for item in getattr(self, "wave_bars", []):
                        self.wave_canvas.tag_raise(item)
                    for item in getattr(self, "wave_peaks", []):
                        self.wave_canvas.tag_raise(item)
                self.waveform_label.config(text="Waveform / análise", image="")
            else:
                self.waveform_label.config(text="Waveform não disponível.", image="")
                self.waveform_image = None
        except Exception:
            self.waveform_label.config(text=f"Waveform gerado em: {png_path}", image="")
            self.waveform_image = None

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
        wrap = tk.Frame(parent, bg="#c8c4bc", bd=0)
        btn = tk.Button(
            wrap,
            text=f"{icon_text} {label_text}",
            command=command,
            relief="solid",
            bd=1,
            bg="#d1cec8",
            fg="#302d29",
            activebackground="#ece9e2",
            activeforeground="#302d29",
            font=("Segoe UI", 8),
            padx=8,
            pady=3,
            cursor="hand2",
        )
        btn.pack(fill="x")
        return wrap

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
