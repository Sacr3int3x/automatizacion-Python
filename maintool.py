import customtkinter as ctk
from tkinter import filedialog, messagebox
import threading
import os
import sys
import subprocess
from PIL import Image, ImageTk
import hashlib
from collections import defaultdict
from pathlib import Path
from reportlab.pdfgen import canvas
from reportlab.lib.pagesizes import A4, landscape
from reportlab.platypus import (
    BaseDocTemplate, PageTemplate, Frame,
    Paragraph, Spacer, Image as ReportLabImage, PageBreak, Table,
    KeepTogether, TableStyle
)
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.enums import TA_LEFT
from reportlab.lib import colors
import pandas as pd
from PyPDF2 import PdfMerger
import re
from datetime import datetime
from PIL.ExifTags import TAGS as ExifTags
import time
import zipfile
import shutil
from concurrent.futures import ThreadPoolExecutor, as_completed
import json

# === Constantes y configuración ===
HASH_CACHE_FILE = "hash_cache.json"
APP_CONFIG_FILE = "fttxg_config.json"
HTML_REPORT_NAME = "reporte_duplicados.html"
IMAGE_EXTENSIONS = (".jpg", ".jpeg", ".png", ".gif", ".bmp")
EXCEL_FILENAME = "estaciones.xlsx"
SUBCARPETAS = [
    "Acceso a la estacion",
    "Limpieza general (in site)",
    "Limpieza general (Out site)",
    "Equipos RAN y transmision",
    "Estado de la torre, mastil o monopolo",
    "Estado de Rectificadores y Controladora",
    "Mediciones Electricas (tablero principal)",
    "Estado de la iluminaria",
    "Estado de sistema puesta a tierra",
    "Banco de baterias",
    "Estado de motogenerador #1",
    "Estado de motogenerador #2",
    "Mantenimiento y lavado de Aires",
    "Aire 1 (Corriente general)",
    "Aire 1 (Corrientes del compresor)",
    "Aire 1 (Presiones)",
    "Aire 1 (Tensión General)",
    "Aire 2 (Corriente general)",
    "Aire 2 (Corrientes del compresor)",
    "Aire 2 (Presiones)",
    "Aire 2 (Tensión General)",
    "Aire 3 (Corriente general)",
    "Aire 3 (Corrientes del compresor)",
    "Aire 3 (Presiones)",
    "Aire 3 (Tensión General)",
    "Observaciones",
]
DEFAULT_APPEARANCE = "Dark"

# Apariencia por defecto
ctk.set_appearance_mode(DEFAULT_APPEARANCE)
ctk.set_default_color_theme("blue")

class MaintenanceApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        
        self.title("Gestor de mantenimiento preventivo")
        self.geometry("1000x850")
        self.minsize(900, 750)
        
        self.preferences = self.load_preferences()
        self.appearance_mode = self.preferences.get("appearance_mode", DEFAULT_APPEARANCE)
        ctk.set_appearance_mode(self.appearance_mode)

        self.ruta_base = self.preferences.get("last_base_folder", "")
        self.estaciones_dict = {}      # {eid: datos}
        self.station_vars = {}         # {eid: CTkBooleanVar} para selección múltiple
        self.station_widgets = {}      # {eid: CTkCheckBox} para filtrado
        self.create_station_vars = {}
        self.create_station_widgets = {}
        self.estaciones_cache = None
        self.hash_cache = self.load_hash_cache()
        self.hash_dirty = False
        self.last_generated_pdf = None  # Para vista previa
        self.duplicates_to_review = []  # Para revisión manual de duplicados
        self.cancel_event = threading.Event()
        self.pause_event = threading.Event()
        self.is_paused = False
        self.current_task = None

        self.setup_ui()

        if self.ruta_base:
            self.apply_saved_base_folder()

    # ------------------------------------------------------------------ #
    # Persistencia y utilidades                                          #
    # ------------------------------------------------------------------ #

    def load_preferences(self):
        """Carga preferencias persistentes."""
        config_path = Path(APP_CONFIG_FILE)
        if config_path.exists():
            try:
                with config_path.open("r", encoding="utf-8") as fh:
                    return json.load(fh)
            except (json.JSONDecodeError, OSError):
                return {}
        return {}

    def save_preferences(self):
        """Guarda preferencias persistentes."""
        config_path = Path(APP_CONFIG_FILE)
        try:
            with config_path.open("w", encoding="utf-8") as fh:
                json.dump(self.preferences, fh, indent=2)
        except OSError:
            pass  # Evitar que un error silencie la UI

    def load_hash_cache(self):
        """Carga el caché de hashes desde un archivo JSON."""
        cache_path = Path(HASH_CACHE_FILE)
        if cache_path.exists():
            try:
                with cache_path.open('r', encoding="utf-8") as f:
                    return json.load(f)
            except Exception:
                return {}
        return {}
        
    def save_hash_cache(self):
        """Guarda el caché de hashes en un archivo JSON."""
        if not self.hash_dirty:
            return
        cache_path = Path(HASH_CACHE_FILE)
        try:
            with cache_path.open('w', encoding="utf-8") as f:
                json.dump(self.hash_cache, f)
            self.hash_dirty = False
        except OSError:
            pass

    def call_on_ui(self, func, *args, **kwargs):
        """Ejecuta una función en el hilo principal de Tk."""
        if threading.current_thread() is threading.main_thread():
            func(*args, **kwargs)
        else:
            self.after(0, lambda: func(*args, **kwargs))

    def show_info(self, title, message):
        self.call_on_ui(messagebox.showinfo, title, message)

    def show_error(self, title, message):
        self.call_on_ui(messagebox.showerror, title, message)

    def show_warning(self, title, message):
        self.call_on_ui(messagebox.showwarning, title, message)

    def append_text(self, widget, message):
        widget.insert("end", message + "\n")
        widget.see("end")

    def log_message(self, widget, message):
        self.call_on_ui(self.append_text, widget, message)

    def set_label(self, label, **kwargs):
        self.call_on_ui(label.configure, **kwargs)

    def set_progress(self, progress_bar, value):
        self.call_on_ui(progress_bar.set, value)

    def set_idle_status(self):
        self.set_label(self.status_label, text="Listo.", text_color="gray")

    def tick_ui(self):
        self.call_on_ui(self.update_idletasks)

    def update_time_remaining(self, start_time, progreso):
        if not hasattr(self, "time_remaining_label"):
            return
        if progreso <= 0:
            texto = "Tiempo restante estimado: --:--"
        else:
            elapsed = time.time() - start_time
            remaining = elapsed * (1 / progreso - 1)
            mins, secs = divmod(int(max(0, remaining)), 60)
            texto = f"Tiempo restante estimado: {mins:02d}:{secs:02d}"
        self.set_label(self.time_remaining_label, text=texto)

    def toggle_buttons(self, enabled):
        state = "normal" if enabled else "disabled"
        for widget in getattr(self, "action_buttons", []):
            self.call_on_ui(widget.configure, state=state)
        cancel_state = "normal" if not enabled else "disabled"
        if getattr(self, "cancel_button", None) is not None:
            self.call_on_ui(self.cancel_button.configure, state=cancel_state)
        # Ajustar controles de selección personalizada según el alcance activo
        selection_state = "normal" if enabled and self.create_scope_var.get() == "selected" else "disabled"
        if getattr(self, "create_select_all_btn", None) is not None:
            self.call_on_ui(self.create_select_all_btn.configure, state=selection_state)
        if getattr(self, "create_clear_btn", None) is not None:
            self.call_on_ui(self.create_clear_btn.configure, state=selection_state)
        if getattr(self, "create_search_entry", None) is not None:
            self.call_on_ui(self.create_search_entry.configure, state=selection_state)
        if getattr(self, "pause_duplicates_btn", None) is not None:
            pause_state = "disabled"
            if not enabled and self.current_task == "búsqueda de duplicados":
                pause_state = "normal"
            self.call_on_ui(self.pause_duplicates_btn.configure, state=pause_state)
            if pause_state == "disabled":
                self.call_on_ui(self.pause_duplicates_btn.configure, text="Pausar análisis")
        if getattr(self, "open_duplicates_viewer_btn", None) is not None:
            viewer_state = "normal" if enabled and self.duplicates_to_review else "disabled"
            self.call_on_ui(self.open_duplicates_viewer_btn.configure, state=viewer_state)

    def run_background_task(self, target, description, *args):
        if self.current_task is not None:
            self.show_warning("Operación en curso", f"Ya se está ejecutando: {self.current_task}")
            return False
        self.current_task = description
        self.cancel_event.clear()
        thread = threading.Thread(target=target, args=args, daemon=True)
        thread.start()
        return True

    def request_cancel(self):
        if self.current_task:
            self.cancel_event.set()
            self.set_label(self.status_label, text=f"Cancelando {self.current_task}...", text_color="orange")

    def finish_task(self):
        self.current_task = None
        self.cancel_event.clear()
        self.pause_event.clear()
        self.is_paused = False
        self.toggle_buttons(True)

    def apply_saved_base_folder(self):
        if not self.ruta_base:
            return
        if not Path(self.ruta_base).exists():
            self.ruta_base = ""
            self.preferences.pop("last_base_folder", None)
            self.save_preferences()
            return
        if hasattr(self, "folder_entry"):
            self.call_on_ui(self.folder_entry.delete, 0, "end")
            self.call_on_ui(self.folder_entry.insert, 0, self.ruta_base)
        self.set_label(
            self.folder_status,
            text="✅ Carpeta base cargada desde la última sesión",
            text_color="green",
        )
        self.enable_workflow_buttons()

    def enable_workflow_buttons(self):
        for widget in getattr(self, "action_buttons", []):
            self.call_on_ui(widget.configure, state="normal")
        if getattr(self, "cancel_button", None):
            self.call_on_ui(self.cancel_button.configure, state="disabled")
        if getattr(self, "open_duplicates_viewer_btn", None):
            self.call_on_ui(self.open_duplicates_viewer_btn.configure, state="disabled")
        if getattr(self, "pause_duplicates_btn", None):
            self.call_on_ui(self.pause_duplicates_btn.configure, state="disabled")

    def load_estaciones_dataframe(self, required_columns=None):
        """Carga el Excel de estaciones validando columnas esenciales."""
        if not self.ruta_base:
            self.show_error("Carpeta no seleccionada", "Seleccione la carpeta base antes de continuar.")
            return None

        excel_path = Path(self.ruta_base) / EXCEL_FILENAME
        if not excel_path.exists():
            self.show_error("Archivo faltante", f"No se encuentra {EXCEL_FILENAME} en la carpeta base.")
            return None

        try:
            df = pd.read_excel(excel_path)
        except FileNotFoundError:
            self.show_error("Archivo no encontrado", f"No se puede abrir {excel_path}.")
            return None
        except PermissionError:
            self.show_error("Archivo en uso", f"No se pudo leer {excel_path}. Cierre el archivo si está abierto e intente nuevamente.")
            return None
        except Exception as exc:
            self.show_error("Error al leer Excel", f"Ocurrió un problema al leer el Excel: {exc}")
            return None

        df.columns = df.columns.str.strip()
        required_columns = required_columns or []
        missing = [col for col in required_columns if col not in df.columns]
        if missing:
            self.show_error("Columnas faltantes", f"El archivo debe contener las columnas: {', '.join(required_columns)}.")
            return None
        if "Estacion" in df.columns:
            df = df.dropna(subset=["Estacion"])
            df["Estacion"] = df["Estacion"].astype(str).str.strip()
            df = df[df["Estacion"].str.len() > 0]
            df = df[df["Estacion"].str.lower() != "nan"]
            df = df.drop_duplicates(subset=["Estacion"])

        return df
        
    def setup_ui(self):
        # Crear frame principal con pestañas
        self.tabview = ctk.CTkTabview(self)
        self.tabview.pack(fill="both", expand=True, padx=20, pady=20)
        
        # Crear pestañas
        self.tabview.add("Inicio")
        self.tabview.add("Crear Carpetas")
        self.tabview.add("Verificar Duplicados")
        self.tabview.add("Generar Informes")
        
        # Configurar pestaña de Inicio
        self.setup_inicio_tab()
        
        # Configurar pestaña de Crear Carpetas
        self.setup_crear_carpetas_tab()
        
        # Configurar pestaña de Verificar Duplicados
        self.setup_verificar_duplicados_tab()
        
        # Configurar pestaña de Generar Informes
        self.setup_generar_informes_tab()

        # Controles globales
        status_frame = ctk.CTkFrame(self)
        status_frame.pack(fill="x", padx=20, pady=(0, 20))

        self.status_label = ctk.CTkLabel(
            status_frame,
            text="Listo.",
            text_color="gray",
            anchor="w"
        )
        self.status_label.pack(side="left", fill="x", expand=True, padx=(10, 0))

        self.cancel_button = ctk.CTkButton(
            status_frame,
            text="Cancelar",
            command=self.request_cancel,
            width=120,
            state="disabled"
        )
        self.cancel_button.pack(side="right", padx=10, pady=10)

        # Lista de botones a bloquear durante operaciones largas
        self.action_buttons = [
            self.create_folders_btn,
            self.generate_reports_btn,
            self.find_duplicates_btn,
            self.browse_button,
            self.refresh_estaciones_btn,
            self.reload_stations_btn,
            self.toggle_all_btn,
            self.preview_report_btn,
            self.open_duplicates_viewer_btn,
            self.create_scope_selector,
        ]
        
    def setup_inicio_tab(self):
        tab = self.tabview.tab("Inicio")
        tab.grid_columnconfigure(0, weight=1)
        
        hero = ctk.CTkFrame(tab, corner_radius=16, fg_color=("gray15", "gray20"))
        hero.pack(fill="x", padx=24, pady=(24, 12))
        ctk.CTkLabel(
            hero,
            text="Gestor de mantenimiento digital",
            font=ctk.CTkFont(size=26, weight="bold")
        ).pack(anchor="w", padx=20, pady=(20, 4))
        ctk.CTkLabel(
            hero,
            text="Centraliza estaciones, organiza evidencia fotográfica y produce reportes profesionales en tres pasos sencillos.",
            font=ctk.CTkFont(size=15),
            wraplength=760,
            justify="left"
        ).pack(anchor="w", padx=20, pady=(0, 12))
        
        quick_actions = ctk.CTkFrame(hero, fg_color="transparent")
        quick_actions.pack(fill="x", padx=20, pady=(8, 20))
        for text, desc in [
            ("1. Configura la carpeta base", "Ubica el mes de trabajo y el archivo estaciones.xlsx."),
            ("2. Clasifica y depura fotos", "Detecta duplicados antes de generar documentación."),
            ("3. Exporta informes", "Obtén PDFs resumidos y la carpeta final comprimida.")
        ]:
            card = ctk.CTkFrame(quick_actions, corner_radius=12)
            card.pack(side="left", expand=True, fill="both", padx=(0, 12) if text != "3. Exporta informes" else 0)
            ctk.CTkLabel(card, text=text, font=ctk.CTkFont(size=15, weight="bold")).pack(anchor="w", padx=16, pady=(14, 4))
            ctk.CTkLabel(card, text=desc, font=ctk.CTkFont(size=13), wraplength=220, justify="left").pack(anchor="w", padx=16, pady=(0, 14))
        
        selector_card = ctk.CTkFrame(tab, corner_radius=14)
        selector_card.pack(fill="x", padx=24, pady=(0, 20))
        selector_card.grid_columnconfigure(1, weight=1)
        
        ctk.CTkLabel(
            selector_card,
            text="Carpeta base",
            font=ctk.CTkFont(size=16, weight="bold")
        ).grid(row=0, column=0, sticky="w", padx=20, pady=(20, 6))
        ctk.CTkLabel(
            selector_card,
            text="Selecciona la ubicación raíz donde se almacenan los meses de trabajo y el Excel de estaciones.",
            font=ctk.CTkFont(size=13),
            wraplength=520,
            justify="left",
            text_color=("gray65", "gray80")
        ).grid(row=1, column=0, columnspan=2, sticky="w", padx=20)
        
        folder_selection_frame = ctk.CTkFrame(selector_card, fg_color="transparent")
        folder_selection_frame.grid(row=2, column=0, columnspan=2, sticky="ew", padx=20, pady=16)
        folder_selection_frame.grid_columnconfigure(0, weight=1)
        
        self.folder_entry = ctk.CTkEntry(
            folder_selection_frame,
            placeholder_text="Ej.: /Volumes/Drive/Mantenimiento/2024/01 Enero",
            height=42
        )
        self.folder_entry.grid(row=0, column=0, sticky="ew", padx=(0, 12))
        
        self.browse_button = ctk.CTkButton(
            folder_selection_frame,
            text="Explorar…",
            height=42,
            width=140,
            command=self.browse_folder
        )
        self.browse_button.grid(row=0, column=1)
        
        self.folder_status = ctk.CTkLabel(
            selector_card,
            text="Estado: No se ha seleccionado carpeta",
            text_color="red",
            font=ctk.CTkFont(size=13)
        )
        self.folder_status.grid(row=3, column=0, columnspan=2, sticky="w", padx=20, pady=(0, 16))
        
        controls_bar = ctk.CTkFrame(tab, fg_color="transparent")
        controls_bar.pack(fill="x", padx=24, pady=(0, 12))
        
        appearance_switch = ctk.CTkSwitch(
            controls_bar,
            text="Modo claro",
            command=self.toggle_appearance
        )
        appearance_switch.pack(side="left")
        
        ctk.CTkButton(
            controls_bar,
            text="Guía rápida",
            command=self.show_help,
            height=36,
            corner_radius=8
        ).pack(side="right")
        
    def toggle_appearance(self):
        if self.appearance_mode == "Dark":
            ctk.set_appearance_mode("Light")
            self.appearance_mode = "Light"
        else:
            ctk.set_appearance_mode("Dark")
            self.appearance_mode = "Dark"
        self.preferences["appearance_mode"] = self.appearance_mode
        self.save_preferences()
        
    def show_help(self):
        help_text = """
        Bienvenido al gestor digital de mantenimiento preventivo.

        - Inicio: Seleccione la carpeta base.
        - Crear Carpetas: Crea estructura para estaciones.
        - Verificar Duplicados: Busca fotos repetidas.
        - Generar Informes: Crea PDFs para estaciones seleccionadas.

        Para más detalles, consulte el manual.
        """
        messagebox.showinfo("Ayuda", help_text)
        
    def setup_crear_carpetas_tab(self):
        tab = self.tabview.tab("Crear Carpetas")
        tab.grid_columnconfigure(0, weight=1)
        
        header = ctk.CTkFrame(tab, corner_radius=14)
        header.pack(fill="x", padx=24, pady=(24, 12))
        header.grid_columnconfigure(1, weight=1)
        
        ctk.CTkLabel(
            header,
            text="Estructura de carpetas",
            font=ctk.CTkFont(size=22, weight="bold")
        ).grid(row=0, column=0, sticky="w", padx=20, pady=(18, 4))
        ctk.CTkLabel(
            header,
            text="Genera las subcarpetas estándar para cada estación registrada en el Excel del mes.",
            font=ctk.CTkFont(size=13),
            wraplength=420,
            text_color=("gray70", "gray80"),
            justify="left"
        ).grid(row=1, column=0, sticky="w", padx=20, pady=(0, 18))
        
        self.ready_status_create = ctk.CTkLabel(
            header,
            text="⚠️ Primero selecciona una carpeta base en Inicio",
            text_color="orange",
            font=ctk.CTkFont(size=13)
        )
        self.ready_status_create.grid(row=0, column=1, rowspan=2, sticky="e", padx=20)
        
        layout = ctk.CTkFrame(tab, fg_color="transparent")
        layout.pack(fill="both", expand=True, padx=24, pady=(0, 12))
        layout.grid_columnconfigure(0, weight=3)
        layout.grid_columnconfigure(1, weight=2)
        layout.grid_rowconfigure(1, weight=1)
        
        control_card = ctk.CTkFrame(layout, corner_radius=14)
        control_card.grid(row=0, column=0, rowspan=2, sticky="nsew", padx=(0, 12), pady=(0, 12))
        control_card.grid_columnconfigure(0, weight=1)
        
        scope_row = ctk.CTkFrame(control_card, fg_color="transparent")
        scope_row.grid(row=0, column=0, sticky="ew", padx=20, pady=(20, 10))
        scope_row.grid_columnconfigure(0, weight=1)
        scope_row.grid_columnconfigure(1, weight=0)
        ctk.CTkLabel(
            scope_row,
            text="Alcance de creación",
            font=ctk.CTkFont(size=15, weight="bold")
        ).grid(row=0, column=0, sticky="w")
        self.refresh_estaciones_btn = ctk.CTkButton(
            scope_row,
            text="Actualizar listado",
            command=self.cargar_estaciones_para_seleccion,
            height=32,
            width=150,
            state="disabled"
        )
        self.refresh_estaciones_btn.grid(row=0, column=1, sticky="e")
        ctk.CTkLabel(
            scope_row,
            text="Decide si deseas crear la estructura para todas las estaciones o solo para una selección puntual.",
            font=ctk.CTkFont(size=12),
            wraplength=440,
            justify="left",
            text_color=("gray70", "gray80")
        ).grid(row=1, column=0, columnspan=2, sticky="w", pady=(6, 12))
        
        self.create_scope_var = ctk.StringVar(value="all")
        self.create_scope_selector = ctk.CTkSegmentedButton(
            scope_row,
            values=["Todas", "Seleccionadas"],
            command=self.on_create_scope_change
        )
        self.create_scope_selector.set("Todas")
        self.create_scope_selector.grid(row=2, column=0, columnspan=2, sticky="w", pady=(0, 12))
        
        self.create_selection_container = ctk.CTkFrame(control_card, fg_color=("gray15", "gray18"), corner_radius=12)
        self.create_selection_container.grid(row=1, column=0, sticky="nsew", padx=20, pady=(0, 16))
        self.create_selection_container.grid_columnconfigure(0, weight=1)
        self.create_selection_container.grid_rowconfigure(2, weight=1)
        
        selection_header = ctk.CTkFrame(self.create_selection_container, fg_color="transparent")
        selection_header.grid(row=0, column=0, sticky="ew", padx=18, pady=(18, 6))
        selection_header.grid_columnconfigure(1, weight=1)
        ctk.CTkLabel(
            selection_header,
            text="Selecciona estaciones",
            font=ctk.CTkFont(size=14, weight="bold")
        ).grid(row=0, column=0, sticky="w")
        self.create_summary_label = ctk.CTkLabel(
            selection_header,
            text="0 estaciones seleccionadas",
            font=ctk.CTkFont(size=12),
            text_color=("gray70", "gray80")
        )
        self.create_summary_label.grid(row=0, column=1, sticky="e")
        
        self.create_search_entry = ctk.CTkEntry(
            self.create_selection_container,
            placeholder_text="Buscar por nombre o ID...",
            height=34
        )
        self.create_search_entry.grid(row=1, column=0, sticky="ew", padx=18, pady=(0, 10))
        self.create_search_entry.bind("<KeyRelease>", self.filtrar_estaciones_crear)
        
        self.create_stations_scroll = ctk.CTkScrollableFrame(self.create_selection_container, height=240)
        self.create_stations_scroll.grid(row=2, column=0, sticky="nsew", padx=18, pady=(0, 10))
        
        selection_actions = ctk.CTkFrame(self.create_selection_container, fg_color="transparent")
        selection_actions.grid(row=3, column=0, sticky="ew", padx=18, pady=(0, 18))
        self.create_select_all_btn = ctk.CTkButton(
            selection_actions,
            text="Seleccionar todo",
            height=32,
            command=self.create_select_all
        )
        self.create_select_all_btn.pack(side="left")
        self.create_clear_btn = ctk.CTkButton(
            selection_actions,
            text="Limpiar selección",
            height=32,
            command=self.create_clear_selection
        )
        self.create_clear_btn.pack(side="right")
        
        action_row = ctk.CTkFrame(control_card, fg_color="transparent")
        action_row.grid(row=2, column=0, sticky="ew", padx=20, pady=(0, 20))
        self.create_folders_btn = ctk.CTkButton(
            action_row,
            text="Crear estructura de carpetas",
            height=46,
            font=ctk.CTkFont(size=16, weight="bold"),
            command=self.crear_carpetas,
            state="disabled"
        )
        self.create_folders_btn.pack(fill="x")
        
        log_card = ctk.CTkFrame(layout, corner_radius=14)
        log_card.grid(row=0, column=1, rowspan=2, sticky="nsew", pady=(0, 12))
        log_card.grid_rowconfigure(1, weight=1)
        log_card.grid_columnconfigure(0, weight=1)
        
        ctk.CTkLabel(
            log_card,
            text="Actividad",
            font=ctk.CTkFont(size=15, weight="bold")
        ).grid(row=0, column=0, sticky="w", padx=18, pady=(18, 6))
        
        self.output_create = ctk.CTkTextbox(
            log_card,
            font=ctk.CTkFont(family="Courier", size=12)
        )
        self.output_create.grid(row=1, column=0, sticky="nsew", padx=18, pady=(0, 12))
        
        self.progress_create = ctk.CTkProgressBar(log_card)
        self.progress_create.grid(row=2, column=0, sticky="ew", padx=18, pady=(0, 18))
        self.progress_create.set(0)
        
        self.on_create_scope_change("Todas")
        
    def setup_verificar_duplicados_tab(self):
        tab = self.tabview.tab("Verificar Duplicados")
        tab.grid_columnconfigure(0, weight=1)
        
        header = ctk.CTkFrame(tab, corner_radius=14)
        header.pack(fill="x", padx=24, pady=(24, 12))
        header.grid_columnconfigure(1, weight=1)
        
        ctk.CTkLabel(
            header,
            text="Verificación de duplicados",
            font=ctk.CTkFont(size=22, weight="bold")
        ).grid(row=0, column=0, sticky="w", padx=20, pady=(18, 4))
        ctk.CTkLabel(
            header,
            text="Escanea la carpeta base, agrupa coincidencias y decide si prefieres reportarlas o eliminarlas automáticamente.",
            font=ctk.CTkFont(size=13),
            wraplength=440,
            justify="left",
            text_color=("gray70", "gray80")
        ).grid(row=1, column=0, sticky="w", padx=20, pady=(0, 18))
        
        self.ready_status_duplicates = ctk.CTkLabel(
            header,
            text="⚠️ Primero selecciona una carpeta base en Inicio",
            text_color="orange",
            font=ctk.CTkFont(size=13)
        )
        self.ready_status_duplicates.grid(row=0, column=1, rowspan=2, sticky="e", padx=20)
        
        layout = ctk.CTkFrame(tab, fg_color="transparent")
        layout.pack(fill="both", expand=True, padx=24, pady=(0, 12))
        layout.grid_columnconfigure(0, weight=2)
        layout.grid_columnconfigure(1, weight=3)
        layout.grid_rowconfigure(1, weight=1)
        config_card = ctk.CTkFrame(layout, corner_radius=14)
        config_card.grid(row=0, column=0, sticky="nsew", padx=(0, 12), pady=(0, 12))
        config_card.grid_columnconfigure(0, weight=1)
        
        ctk.CTkLabel(
            config_card,
            text="Controles de análisis",
            font=ctk.CTkFont(size=15, weight="bold")
        ).grid(row=0, column=0, sticky="w", padx=20, pady=(20, 6))
        ctk.CTkLabel(
            config_card,
            text="Inicia o detén el análisis cuando lo necesites. El progreso se mostrará en tiempo real.",
            font=ctk.CTkFont(size=12),
            wraplength=360,
            justify="left",
            text_color=("gray70", "gray80")
        ).grid(row=1, column=0, sticky="w", padx=20, pady=(0, 12))
        
        controls = ctk.CTkFrame(config_card, fg_color="transparent")
        controls.grid(row=2, column=0, sticky="ew", padx=20, pady=(0, 20))
        controls.grid_columnconfigure(0, weight=1)
        
        self.find_duplicates_btn = ctk.CTkButton(
            controls,
            text="Buscar duplicados",
            height=46,
            font=ctk.CTkFont(size=16, weight="bold"),
            command=self.buscar_duplicados,
            state="disabled"
        )
        self.find_duplicates_btn.grid(row=0, column=0, sticky="ew")
        
        button_row = ctk.CTkFrame(controls, fg_color="transparent")
        button_row.grid(row=1, column=0, sticky="ew", pady=(10, 0))
        button_row.grid_columnconfigure((0,1), weight=1)
        
        self.pause_duplicates_btn = ctk.CTkButton(
            button_row,
            text="Pausar análisis",
            command=self.toggle_pause_duplicates,
            height=36,
            state="disabled"
        )
        self.pause_duplicates_btn.grid(row=0, column=0, sticky="ew", padx=(0, 6))
        
        self.open_duplicates_viewer_btn = ctk.CTkButton(
            button_row,
            text="Panel de duplicados",
            command=self.review_duplicates,
            height=36,
            state="disabled"
        )
        self.open_duplicates_viewer_btn.grid(row=0, column=1, sticky="ew", padx=(6, 0))

        results_card = ctk.CTkFrame(layout, corner_radius=14)
        results_card.grid(row=0, column=1, rowspan=2, sticky="nsew", pady=(0, 12))
        results_card.grid_columnconfigure(0, weight=1)
        results_card.grid_rowconfigure(1, weight=1)
        
        ctk.CTkLabel(
            results_card,
            text="Resultado del análisis",
            font=ctk.CTkFont(size=15, weight="bold")
        ).grid(row=0, column=0, sticky="w", padx=18, pady=(18, 6))
        
        self.output_duplicates = ctk.CTkTextbox(
            results_card,
            font=ctk.CTkFont(family="Courier", size=12)
        )
        self.output_duplicates.grid(row=1, column=0, sticky="nsew", padx=18, pady=(0, 12))
        
        preview_box = ctk.CTkFrame(results_card, fg_color=("gray15", "gray18"), corner_radius=12)
        preview_box.grid(row=2, column=0, sticky="nsew", padx=18, pady=(0, 12))
        ctk.CTkLabel(
            preview_box,
            text="Vista rápida de coincidencias",
            font=ctk.CTkFont(size=13, weight="bold")
        ).pack(anchor="w", padx=14, pady=(12, 4))
        self.duplicates_preview = ctk.CTkScrollableFrame(preview_box, height=120)
        self.duplicates_preview.pack(fill="both", expand=True, padx=14, pady=(0, 12))
        
        self.progress_duplicates = ctk.CTkProgressBar(results_card)
        self.progress_duplicates.grid(row=3, column=0, sticky="ew", padx=18, pady=(0, 18))
        self.progress_duplicates.set(0)
        self.duplicates_progress_label = ctk.CTkLabel(
            results_card,
            text="Progreso: 0 elementos procesados.",
            font=ctk.CTkFont(size=12),
            text_color=("gray70", "gray80")
        )
        self.duplicates_progress_label.grid(row=4, column=0, sticky="w", padx=18, pady=(0, 12))
        
        # Preferencias internas (sin controles visibles)
        self.generate_html_report_flag = True
        self.auto_delete_duplicates_flag = False
        
    def setup_generar_informes_tab(self):
        tab = self.tabview.tab("Generar Informes")
        tab.grid_columnconfigure(0, weight=1)
        
        header = ctk.CTkFrame(tab, corner_radius=14)
        header.pack(fill="x", padx=24, pady=(24, 12))
        header.grid_columnconfigure(1, weight=1)
        
        ctk.CTkLabel(
            header,
            text="Generar informes PDF",
            font=ctk.CTkFont(size=22, weight="bold")
        ).grid(row=0, column=0, sticky="w", padx=20, pady=(18, 4))
        ctk.CTkLabel(
            header,
            text="Selecciona las estaciones a documentar, ejecuta el proceso y lleva el control del estado de cada corrida.",
            font=ctk.CTkFont(size=13),
            wraplength=440,
            justify="left",
            text_color=("gray70", "gray80")
        ).grid(row=1, column=0, sticky="w", padx=20, pady=(0, 18))

        self.ready_status_reports = ctk.CTkLabel(
            header,
            text="⚠️ Primero selecciona una carpeta base en Inicio",
            text_color="orange",
            font=ctk.CTkFont(size=13)
        )
        self.ready_status_reports.grid(row=0, column=1, rowspan=2, sticky="e", padx=20, pady=(18, 0))

        self.excel_status = ctk.CTkLabel(
            header,
            text="Estado: Archivo estaciones.xlsx no verificado",
            text_color="gray",
            font=ctk.CTkFont(size=12)
        )
        self.excel_status.grid(row=2, column=0, columnspan=2, sticky="w", padx=20, pady=(0, 18))

        layout = ctk.CTkFrame(tab, fg_color="transparent")
        layout.pack(fill="both", expand=True, padx=24, pady=(0, 12))
        layout.grid_columnconfigure(0, weight=2)
        layout.grid_columnconfigure(1, weight=3)
        layout.grid_rowconfigure(0, weight=1)

        selector_card = ctk.CTkFrame(layout, corner_radius=14)
        selector_card.grid(row=0, column=0, sticky="nsew", padx=(0, 12), pady=(0, 12))
        selector_card.grid_columnconfigure(0, weight=1)
        selector_card.grid_rowconfigure(3, weight=1)

        ctk.CTkLabel(
            selector_card,
            text="Estaciones disponibles",
            font=ctk.CTkFont(size=15, weight="bold")
        ).grid(row=0, column=0, sticky="w", padx=20, pady=(20, 6))
        ctk.CTkLabel(
            selector_card,
            text="Busca por nombre o identificador y marca las estaciones que formarán parte del informe.",
            font=ctk.CTkFont(size=12),
            text_color=("gray70", "gray80"),
            wraplength=360,
            justify="left"
        ).grid(row=1, column=0, sticky="w", padx=20, pady=(0, 12))

        self.search_entry = ctk.CTkEntry(
            selector_card,
            placeholder_text="Buscar por ID, nombre o estado...",
            height=34
        )
        self.search_entry.grid(row=2, column=0, sticky="ew", padx=20, pady=(0, 12))
        self.search_entry.bind("<KeyRelease>", self.filtrar_estaciones)

        self.stations_scroll = ctk.CTkScrollableFrame(selector_card, height=240)
        self.stations_scroll.grid(row=3, column=0, sticky="nsew", padx=20, pady=(0, 12))

        selector_actions = ctk.CTkFrame(selector_card, fg_color="transparent")
        selector_actions.grid(row=4, column=0, sticky="ew", padx=20, pady=(0, 18))
        self.reload_stations_btn = ctk.CTkButton(
            selector_actions,
            text="Recargar desde Excel",
            command=self.cargar_estaciones_para_seleccion,
            state="disabled",
            height=36
        )
        self.reload_stations_btn.pack(side="left")
        self.toggle_all_btn = ctk.CTkButton(
            selector_actions,
            text="Seleccionar todas",
            command=self.toggle_all_stations,
            state="disabled",
            height=36
        )
        self.toggle_all_btn.pack(side="right")

        actions_card = ctk.CTkFrame(layout, corner_radius=14)
        actions_card.grid(row=0, column=1, sticky="nsew", pady=(0, 12))
        actions_card.grid_columnconfigure(0, weight=1)
        actions_card.grid_rowconfigure(3, weight=1)

        ctk.CTkLabel(
            actions_card,
            text="Ejecución y seguimiento",
            font=ctk.CTkFont(size=15, weight="bold")
        ).grid(row=0, column=0, sticky="w", padx=18, pady=(18, 6))

        self.generate_reports_btn = ctk.CTkButton(
            actions_card,
            text="Generar informes (seleccionadas)",
            height=46,
            font=ctk.CTkFont(size=16, weight="bold"),
            command=self.generar_informes,
            state="disabled"
        )
        self.generate_reports_btn.grid(row=1, column=0, sticky="ew", padx=18, pady=(0, 12))

        self.preview_report_btn = ctk.CTkButton(
            actions_card,
            text="Abrir último informe generado",
            command=self.preview_report,
            height=36,
            state="disabled"
        )
        self.preview_report_btn.grid(row=2, column=0, sticky="ew", padx=18, pady=(0, 12))

        self.output_reports = ctk.CTkTextbox(
            actions_card,
            font=ctk.CTkFont(family="Courier", size=12)
        )
        self.output_reports.grid(row=3, column=0, sticky="nsew", padx=18, pady=(0, 12))

        progress_block = ctk.CTkFrame(actions_card, fg_color="transparent")
        progress_block.grid(row=4, column=0, sticky="ew", padx=18, pady=(0, 12))
        self.progress_reports = ctk.CTkProgressBar(progress_block)
        self.progress_reports.pack(fill="x")
        self.progress_reports.set(0)
        self.time_remaining_label = ctk.CTkLabel(
            progress_block,
            text="Tiempo restante estimado: --:--",
            font=ctk.CTkFont(size=12)
        )
        self.time_remaining_label.pack(anchor="w", pady=(4, 0))

        history_card = ctk.CTkFrame(actions_card, fg_color=("gray15", "gray18"), corner_radius=12)
        history_card.grid(row=5, column=0, sticky="ew", padx=18, pady=(0, 18))
        ctk.CTkLabel(
            history_card,
            text="Historial reciente",
            font=ctk.CTkFont(size=13, weight="bold")
        ).pack(anchor="w", padx=14, pady=(12, 4))
        self.history_box = ctk.CTkTextbox(history_card, height=120, font=ctk.CTkFont(family="Courier", size=11))
        self.history_box.pack(fill="x", padx=14, pady=(0, 12))
        
    def toggle_all_stations(self):
        """Toggles the selection state of all station checkboxes."""
        all_selected = all(var.get() for var in self.station_vars.values())
        new_state = not all_selected
        for var in self.station_vars.values():
            var.set(new_state)
        self.toggle_all_btn.configure(text="Deseleccionar todas" if new_state else "Seleccionar todas")
    
    def on_create_scope_change(self, value):
        mode = "selected" if value == "Seleccionadas" else "all"
        self.create_scope_var.set(mode)
        if mode == "selected":
            self.create_selection_container.grid()
            self.create_select_all_btn.configure(state="normal")
            self.create_clear_btn.configure(state="normal")
            self.create_search_entry.configure(state="normal")
        else:
            self.create_selection_container.grid_remove()
            self.create_select_all_btn.configure(state="disabled")
            self.create_clear_btn.configure(state="disabled")
            self.create_search_entry.configure(state="disabled")
        self.update_create_selection_summary()
        
    def filtrar_estaciones_crear(self, event=None):
        query = (self.create_search_entry.get() if self.create_search_entry.winfo_exists() else "").lower()
        for eid, widget in self.create_station_widgets.items():
            nombre = self.estaciones_dict.get(eid, {}).get("nombre", "")
            if query in eid.lower() or query in nombre.lower():
                widget.pack(anchor="w", fill="x", padx=4, pady=2)
            else:
                widget.pack_forget()
        self.update_create_selection_summary()
        
    def create_select_all(self):
        for var in self.create_station_vars.values():
            var.set(True)
        self.update_create_selection_summary()
        
    def create_clear_selection(self):
        for var in self.create_station_vars.values():
            var.set(False)
        self.update_create_selection_summary()
        
    def update_create_selection_summary(self):
        if not hasattr(self, "create_summary_label"):
            return
        total_disponibles = len(self.create_station_vars) if self.create_station_vars else 0
        if self.create_scope_var.get() == "all":
            total_registradas = (
                len(self.estaciones_cache["Estacion"].dropna())
                if isinstance(self.estaciones_cache, pd.DataFrame) else total_disponibles
            )
            texto = f"Se crearán todas las estaciones ({total_registradas or 0})"
        else:
            seleccionadas = sum(1 for var in self.create_station_vars.values() if var.get())
            texto = f"{seleccionadas}/{total_disponibles or 0} estaciones seleccionadas"
        self.create_summary_label.configure(text=texto)
        
    def filtrar_estaciones(self, event=None):
        query = self.search_entry.get().lower()
        for eid, widget in self.station_widgets.items():
            if query in eid.lower() or query in self.estaciones_dict[eid]["nombre"].lower():
                widget.pack(anchor="w", padx=6, pady=2)
            else:
                widget.pack_forget()
        
    def preview_report(self):
        if not self.last_generated_pdf:
            self.show_warning("Aviso", "No hay informe generado para previsualizar.")
            return
        try:
            if sys.platform == "win32":
                os.startfile(self.last_generated_pdf)
            elif sys.platform == "darwin":
                subprocess.call(("open", self.last_generated_pdf))
            else:
                subprocess.call(("xdg-open", self.last_generated_pdf))
        except Exception as e:
            self.show_error("Error", f"No se pudo abrir la vista previa: {e}")
        
    def browse_folder(self):
        folder_path = filedialog.askdirectory(title="Seleccionar carpeta base")
        if not folder_path:
            return

        self.ruta_base = folder_path
        self.call_on_ui(self.folder_entry.delete, 0, "end")
        self.call_on_ui(self.folder_entry.insert, 0, folder_path)

        self.preferences["last_base_folder"] = folder_path
        self.save_preferences()

        self.set_label(self.folder_status, text="✅ Carpeta base seleccionada", text_color="green")
        self.set_label(self.status_label, text=f"Carpeta base: {folder_path}", text_color="green")
        self.set_label(self.ready_status_create, text="✅ Listo para crear carpetas", text_color="green")
        self.set_label(self.ready_status_duplicates, text="✅ Listo para buscar duplicados", text_color="green")
        self.set_label(self.ready_status_reports, text="✅ Listo para generar informes", text_color="green")

        self.enable_workflow_buttons()

        excel_path = Path(self.ruta_base) / EXCEL_FILENAME
        if excel_path.exists():
            self.set_label(self.excel_status, text="✅ Archivo estaciones.xlsx encontrado", text_color="green")
            self.cargar_estaciones_para_seleccion()
        else:
            self.set_label(self.excel_status, text=f"❌ Archivo {EXCEL_FILENAME} no encontrado", text_color="red")
        
    def validar_ruta(self):
        if not self.ruta_base:
            self.show_error("Ruta no válida", "Por favor, seleccione una carpeta base.")
            return False
        return True
        
    def calcular_hash_archivo(self, ruta_archivo, bloque=65536):
        """Calcula el hash MD5 de un archivo para comparación."""
        try:
            file_stat = os.stat(ruta_archivo)
        except OSError:
            return None
        cache_key = f"{ruta_archivo}_{file_stat.st_mtime}_{file_stat.st_size}"
        if cache_key in self.hash_cache:
            return self.hash_cache[cache_key]
        
        hasher = hashlib.md5()
        try:
            with open(ruta_archivo, 'rb') as f:
                for datos in iter(lambda: f.read(bloque), b""):
                    hasher.update(datos)
            hash_value = hasher.hexdigest()
            self.hash_cache[cache_key] = hash_value
            self.hash_dirty = True
            return hash_value
        except (IOError, OSError):
            return None
            
    def crear_carpetas(self):
        if not self.validar_ruta():
            return
        
        df = self.load_estaciones_dataframe(required_columns=["Estacion"])
        if df is None:
            return

        scope = self.create_scope_var.get()
        selected_ids = None
        target_df = df.copy()
        if scope == "selected":
            selected_ids = [eid for eid, var in self.create_station_vars.items() if var.get()]
            if not selected_ids:
                self.show_warning("Selección vacía", "Selecciona al menos una estación para crear su estructura.")
                return
            selected_ids_clean = {eid.strip() for eid in selected_ids}
            target_df["Estacion"] = target_df["Estacion"].astype(str).str.strip()
            target_df = target_df[target_df["Estacion"].isin(selected_ids_clean)]
            if target_df.empty:
                self.show_warning("Sin coincidencias", "Las estaciones seleccionadas no se encontraron en el Excel.")
                return
        else:
            selected_ids_clean = None

        existentes = self.validate_existing_structure(target_df)
        if existentes:
            listado = ", ".join(existentes[:8])
            if len(existentes) > 8:
                listado += f" y {len(existentes) - 8} más"
            if not messagebox.askyesno("Advertencia", f"Ya existen carpetas para: {listado}. ¿Desea continuar?"):
                return

        self.output_create.delete("1.0", "end")
        self.set_progress(self.progress_create, 0)
        self.toggle_buttons(False)
        self.set_label(self.status_label, text="Creando estructura de carpetas...", text_color="orange")

        if not self.run_background_task(self._crear_carpetas_thread, "creación de carpetas", target_df, selected_ids_clean):
            self.toggle_buttons(True)
            self.set_idle_status()
        
    def validate_existing_structure(self, df):
        """Devuelve lista de estaciones con carpetas ya creadas."""
        existentes = []
        base_path = Path(self.ruta_base)
        for _, row in df.iterrows():
            eid = str(row.get("Estacion", "")).strip()
            if eid and (base_path / eid).exists():
                existentes.append(eid)
        return existentes
        
    def _crear_carpetas_thread(self, df, selected_ids=None):
        try:
            self.log_message(self.output_create, "Iniciando creación de carpetas...")

            nombres_carpetas = []
            for _, row in df.iterrows():
                eid = str(row.get("Estacion", "")).strip()
                if eid:
                    nombres_carpetas.append(eid)
            
            if not nombres_carpetas:
                self.log_message(self.output_create, "No se encontraron estaciones en el archivo Excel.")
                self.show_error("Error", "No se encontraron estaciones en el archivo Excel.")
                return
                
            self.log_message(self.output_create, f"Se encontraron {len(nombres_carpetas)} estaciones en el archivo Excel.")
            base_path = Path(self.ruta_base)
            base_path.mkdir(parents=True, exist_ok=True)

            total = len(nombres_carpetas)
            objetivo_texto = "seleccionadas" if selected_ids else "registradas"
            self.log_message(self.output_create, f"Creando estructura para {total} estaciones {objetivo_texto}.")
            for i, nombre in enumerate(nombres_carpetas, start=1):
                if self.cancel_event.is_set():
                    self.log_message(self.output_create, "Creación cancelada por el usuario.")
                    self.set_label(self.status_label, text="Creación cancelada.", text_color="orange")
                    return

                ruta_carpeta = base_path / nombre
                if not ruta_carpeta.exists():
                    ruta_carpeta.mkdir(parents=True, exist_ok=True)
                    self.log_message(self.output_create, f"Carpeta creada: {nombre}")
                else:
                    self.log_message(self.output_create, f"La carpeta ya existe: {nombre}")

                # Crear subcarpetas
                for subcarpeta in SUBCARPETAS:
                    ruta_subcarpeta = ruta_carpeta / subcarpeta
                    if not ruta_subcarpeta.exists():
                        ruta_subcarpeta.mkdir(parents=True, exist_ok=True)
                        self.log_message(self.output_create, f"  Subcarpeta creada: {subcarpeta}")
                
                # Actualizar barra de progreso
                self.set_progress(self.progress_create, i / total)
            
            self.log_message(self.output_create, "Proceso de creación de carpetas completado.")
            self.show_info("Éxito", "Las carpetas se han creado correctamente.")
            self.set_label(self.status_label, text="Carpetas creadas correctamente.", text_color="green")
            
        except Exception as e:
            self.log_message(self.output_create, f"Error: {str(e)}")
            self.show_error("Error", f"Ocurrió un error: {str(e)}")
            self.set_label(self.status_label, text="Error durante la creación de carpetas.", text_color="red")
        finally:
            self.set_progress(self.progress_create, 0)
            self.finish_task()
    
    def buscar_duplicados(self):
        if not self.validar_ruta():
            return

        self.pause_event.clear()
        self.is_paused = False
        self.duplicates_to_review = []
        self.open_duplicates_viewer_btn.configure(state="disabled")
        self.toggle_buttons(False)
        self.set_progress(self.progress_duplicates, 0)
        self.output_duplicates.delete("1.0", "end")
        for widget in self.duplicates_preview.winfo_children():
            widget.destroy()
        self.set_label(self.status_label, text="Analizando duplicados...", text_color="orange")
        self.set_label(self.duplicates_progress_label, text="Progreso: 0 elementos procesados.")

        if not self.run_background_task(self._buscar_duplicados_thread, "búsqueda de duplicados"):
            self.toggle_buttons(True)
            self.set_idle_status()
            return

        self.pause_duplicates_btn.configure(state="normal", text="Pausar análisis")

    def toggle_pause_duplicates(self):
        if self.current_task != "búsqueda de duplicados":
            return
        if not self.is_paused:
            self.pause_event.set()
            self.is_paused = True
            self.pause_duplicates_btn.configure(text="Reanudar análisis")
            self.set_label(self.status_label, text="Análisis pausado.", text_color="orange")
            actual_text = self.duplicates_progress_label.cget("text") if hasattr(self.duplicates_progress_label, "cget") else ""
            if actual_text:
                self.set_label(self.duplicates_progress_label, text=f"{actual_text} · Pausado")
        else:
            self.pause_event.clear()
            self.is_paused = False
            self.pause_duplicates_btn.configure(text="Pausar análisis")
            self.set_label(self.status_label, text="Analizando duplicados...", text_color="orange")

    def _buscar_duplicados_thread(self):
        try:
            self.log_message(self.output_duplicates, "Buscando fotos duplicadas...")
            self.log_message(self.output_duplicates, "Explorando directorios...")
            duplicados = defaultdict(list)

            base_path = Path(self.ruta_base)
            image_files = []
            for root, _, files in os.walk(base_path):
                if "imagenes_temp" in Path(root).parts:
                    continue
                for filename in files:
                    if filename.lower().endswith(IMAGE_EXTENSIONS):
                        image_files.append(Path(root) / filename)

            total_archivos = len(image_files)
            if total_archivos == 0:
                self.log_message(self.output_duplicates, "No se encontraron archivos de imagen.")
                self.show_info("Información", "No se encontraron archivos de imagen en la carpeta seleccionada.")
                self.set_label(self.status_label, text="Sin archivos de imagen para revisar.", text_color="orange")
                return

            self.log_message(self.output_duplicates, f"Se encontraron {total_archivos} archivos de imagen para analizar.")

            archivos_procesados = 0
            max_workers = max(2, os.cpu_count() or 2)
            with ThreadPoolExecutor(max_workers=max_workers) as executor:
                future_map = {
                    executor.submit(self.process_file_for_duplicates, path): path
                    for path in image_files
                }
                for future in as_completed(future_map):
                    if self.cancel_event.is_set():
                        break
                    while self.pause_event.is_set() and not self.cancel_event.is_set():
                        time.sleep(0.2)
                    if self.cancel_event.is_set():
                        break
                    result = future.result()
                    if result:
                        file_hash, info = result
                        duplicados[file_hash].append(info)
                    archivos_procesados += 1
                    progreso = archivos_procesados / total_archivos
                    self.set_progress(self.progress_duplicates, progreso)
                    porcentaje = progreso * 100
                    self.set_label(
                        self.duplicates_progress_label,
                        text=f"Progreso: {archivos_procesados}/{total_archivos} archivos ({porcentaje:.1f}%)"
                    )
                    self.set_label(
                        self.status_label,
                        text=f"Analizando duplicados... {porcentaje:.1f}%",
                        text_color="orange"
                    )
                    self.tick_ui()
                    if archivos_procesados % 50 == 0 or archivos_procesados == total_archivos:
                        self.log_message(
                            self.output_duplicates,
                            f"Avance: {archivos_procesados}/{total_archivos} archivos analizados..."
                        )

            if self.cancel_event.is_set():
                self.log_message(self.output_duplicates, "Búsqueda cancelada por el usuario.")
                self.set_label(self.status_label, text="Búsqueda cancelada.", text_color="orange")
                return

            duplicados = {hash_: archivos for hash_, archivos in duplicados.items() if len(archivos) > 1}

            if not duplicados:
                self.log_message(self.output_duplicates, "No se encontraron fotos duplicadas.")
                self.show_info("Resultado", "No se encontraron fotos duplicadas.")
                self.set_label(self.status_label, text="Sin duplicados detectados.", text_color="green")
                self.call_on_ui(self.open_duplicates_viewer_btn.configure, state="disabled")
                return

            self.log_message(self.output_duplicates, f"\nSe encontraron {len(duplicados)} grupos de fotos duplicadas:")

            for i, (hash_value, archivos) in enumerate(duplicados.items(), 1):
                estaciones = sorted({item['estacion'] for item in archivos})
                self.log_message(
                    self.output_duplicates,
                    f"Grupo {i}: {len(archivos)} archivos idénticos | Estaciones: {', '.join(estaciones)} | Hash: {hash_value[:10]}..."
                )
                for archivo in archivos[:5]:
                    self.log_message(
                        self.output_duplicates,
                        f"  - {archivo['nombre_archivo']} ({archivo['subcarpeta']})"
                    )
                if len(archivos) > 5:
                    self.log_message(
                        self.output_duplicates,
                        f"  ... y {len(archivos) - 5} archivos adicionales."
                    )

            self.duplicates_to_review = list(duplicados.values())
            self.call_on_ui(self.open_duplicates_viewer_btn.configure, state="normal")

            if self.generate_html_report_flag:
                self.log_message(self.output_duplicates, "Generando reporte HTML...")
                html_root = Path(self.ruta_base) / "reportes_duplicados"
                ruta_reporte = html_root / HTML_REPORT_NAME
                ruta_final = self.generar_reporte_html(duplicados, ruta_reporte)
                self.log_message(self.output_duplicates, f"Reporte generado en: {ruta_final}")

            if self.auto_delete_duplicates_flag:
                self.delete_duplicates(duplicados)

            self.call_on_ui(self.populate_duplicates_preview, duplicados)
            self.log_message(self.output_duplicates, "\nBúsqueda de duplicados completada.")
            self.show_info("Éxito", f"Se encontraron {len(duplicados)} grupos de duplicados.")
            self.set_label(self.status_label, text="Duplicados analizados.", text_color="green")

        except Exception as e:
            self.log_message(self.output_duplicates, f"Error: {str(e)}")
            self.show_error("Error", f"Ocurrió un error: {str(e)}")
            self.set_label(self.status_label, text="Error al buscar duplicados.", text_color="red")
        finally:
            self.pause_event.clear()
            self.is_paused = False
            self.call_on_ui(self.pause_duplicates_btn.configure, state="disabled", text="Pausar análisis")
            self.save_hash_cache()
            self.set_progress(self.progress_duplicates, 0)
            self.set_label(self.duplicates_progress_label, text="Progreso: 0 elementos procesados.")
            self.finish_task()

    def process_file_for_duplicates(self, ruta_completa):
        """Procesar archivo para duplicados."""
        if self.cancel_event.is_set():
            return None
        ruta_completa = Path(ruta_completa)
        file_hash = self.calcular_hash_archivo(str(ruta_completa))
        if file_hash:
            base_path = Path(self.ruta_base)
            try:
                relative_parts = ruta_completa.relative_to(base_path).parts
            except ValueError:
                relative_parts = ruta_completa.parts
            estacion = relative_parts[0] if len(relative_parts) > 0 else "Desconocida"
            subcarpeta = relative_parts[1] if len(relative_parts) > 1 else "Desconocida"
            return file_hash, {
                'ruta': str(ruta_completa),
                'estacion': estacion,
                'subcarpeta': subcarpeta,
                'nombre_archivo': ruta_completa.name
            }
        return None
        
    def populate_duplicates_preview(self, duplicados):
        """Muestra una vista previa limitada de duplicados en el hilo principal."""
        for widget in self.duplicates_preview.winfo_children():
            widget.destroy()

        max_groups = min(3, len(duplicados))
        if max_groups == 0:
            return

        for idx, archivos in enumerate(list(duplicados.values())[:max_groups], start=1):
            group_frame = ctk.CTkFrame(self.duplicates_preview)
            group_frame.pack(fill="x", padx=4, pady=4)

            ctk.CTkLabel(group_frame, text=f"Grupo {idx}", font=ctk.CTkFont(weight="bold")).pack(anchor="w", padx=6, pady=(4, 2))

            preview_frame = ctk.CTkFrame(group_frame)
            preview_frame.pack(fill="x", padx=6, pady=(0, 6))

            for archivo in archivos[:3]:
                self.show_image_preview(preview_frame, archivo['ruta'], archivo['nombre_archivo'])

    def show_image_preview(self, parent, image_path, tooltip):
        """Mostrar vista previa de imagen en la interfaz."""
        try:
            img = Image.open(image_path)
            img.thumbnail((100, 100))
            img_ctk = ctk.CTkImage(light_image=img, size=(100, 100))
            label = ctk.CTkLabel(parent, image=img_ctk, text=tooltip[:18])
            label.image = img_ctk  # Mantener referencia
            label.pack(side="left", padx=5, pady=5)
        except Exception as e:
            self.log_message(self.output_duplicates, f"Error al mostrar vista previa: {str(e)}")
            
    def review_duplicates(self):
        """Abre ventana para revisión manual de duplicados."""
        if not self.duplicates_to_review:
            self.show_info("Información", "No hay duplicados para revisar. Primero ejecute la búsqueda.")
            return
            
        ReviewDuplicatesWindow(self, self.duplicates_to_review)
            
    def delete_duplicates(self, duplicados):
        """Eliminar duplicados automáticamente, manteniendo la primera copia."""
        for hash, archivos in duplicados.items():
            to_keep = archivos[0]['ruta']
            self.log_message(self.output_duplicates, f"Manteniendo: {to_keep}")
            for archivo in archivos[1:]:
                try:
                    os.remove(archivo['ruta'])
                    self.log_message(self.output_duplicates, f"Eliminado: {archivo['ruta']}")
                except Exception as e:
                    self.log_message(self.output_duplicates, f"Error al eliminar: {str(e)}")
    def generar_reporte_html(self, duplicados, ruta_reporte):
        """Genera un reporte HTML con los resultados y devuelve la ruta escrita."""
        ruta_reporte = Path(ruta_reporte)
        ruta_reporte.parent.mkdir(parents=True, exist_ok=True)
        destino = ruta_reporte
        if destino.exists():
            timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
            destino = ruta_reporte.with_name(f"{ruta_reporte.stem}_{timestamp}{ruta_reporte.suffix}")

        html = f"""
        <html>
        <head>
            <title>Reporte de Fotos Duplicadas</title>
            <style>
                body {{ font-family: Arial, sans-serif; margin: 20px; }}
                .grupo {{ border: 1px solid #ddd; padding: 15px; margin-bottom: 20px; border-radius: 5px; }}
                .foto {{ margin: 10px 0; padding: 10px; background-color: #f9f9f9; border-left: 4px solid #4CAF50; }}
                h1 {{ color: #333; }}
                h2 {{ color: #444; }}
                .hash {{ font-family: monospace; color: #666; }}
                .estacion {{ font-weight: bold; color: #2c3e50; }}
                .subcarpeta {{ color: #7f8c8d; }}
                img {{ max-width: 100px; height: auto; }}
            </style>
        </head>
        <body>
            <h1>Reporte de Fotos Duplicadas</h1>
            <p>Generado el: {datetime.now().strftime('%d/%m/%Y %H:%M')}</p>
            <p>Directorio analizado: {self.ruta_base}</p>
            <p>Se encontraron {len(duplicados)} grupos de fotos duplicadas.</p>
        """

        for i, (hash_value, archivos) in enumerate(duplicados.items(), 1):
            html += f"""
            <div class="grupo">
                <h2>Grupo {i} - {len(archivos)} fotos idénticas</h2>
                <p class="hash">Hash: {hash_value}</p>
            """

            for archivo in archivos:
                html += f"""
                <div class="foto">
                    <p class="estacion">Estación: {archivo['estacion']}</p>
                    <p class="subcarpeta">Subcarpeta: {archivo['subcarpeta']}</p>
                    <p>Archivo: {archivo['nombre_archivo']}</p>
                    <p>Ruta: {archivo['ruta']}</p>
                    <img src="{archivo['ruta']}" alt="{archivo['nombre_archivo']}">
                </div>
                """

            html += "</div>"

        html += "</body></html>"

        with destino.open('w', encoding='utf-8') as archivo_html:
            archivo_html.write(html)

        return destino
    
    def generar_informes(self):
        if not self.validar_ruta():
            return

        df = self.load_estaciones_dataframe(required_columns=["Estacion"])
        if df is None:
            return

        seleccionadas = [eid for eid, var in self.station_vars.items() if var.get()]
        if not seleccionadas:
            self.show_warning("Aviso", "Por favor, seleccione al menos una estación para generar informes.")
            return

        self.output_reports.delete("1.0", "end")
        self.set_progress(self.progress_reports, 0)
        self.set_label(self.time_remaining_label, text="Tiempo restante estimado: --:--")
        self.toggle_buttons(False)
        self.set_label(self.status_label, text="Generando informes...", text_color="orange")

        if not self.run_background_task(self._generar_informes_thread, "generación de informes", df, seleccionadas):
            self.toggle_buttons(True)
            self.set_idle_status()
        
    def _generar_informes_thread(self, df, seleccionadas):
        ruta_temporal = Path(self.ruta_base) / "imagenes_temp"
        try:
            self.log_message(self.output_reports, "Iniciando generación de informes...")

            estaciones = {}
            for _, row in df.iterrows():
                eid = str(row.get("Estacion", "")).strip()
                if not eid:
                    continue
                nombre = str(row.get("Nombre", "")).strip()
                estaciones[eid] = {
                    "nombre": nombre,
                    "tipo": str(row.get("Tipo", "")),
                    "coordenadas": str(row.get("Coordenadas", "")),
                    "fecha": row.get("Fecha"),
                    "hora_visita": row.get("Hora_Visita", ""),
                    "hora_salida": row.get("Hora_Salida", ""),
                    "estado": str(row.get("Estado", "")).strip().upper(),
                    "problemas": str(row.get("Problemas", "")).strip().upper() in ("1", "TRUE", "SI", "SÍ", "YES"),
                    "fotos": {}
                }
            
            self.log_message(self.output_reports, f"Se cargaron {len(estaciones)} estaciones.")

            def normalizar_seccion(nombre):
                return re.sub(r'\s*\(?(I{1,3}|IV|V{1,3})\)?$', '', nombre).strip()

            total_estaciones = len([eid for eid in seleccionadas if eid in estaciones])
            if total_estaciones == 0:
                self.log_message(self.output_reports, "No hay estaciones válidas seleccionadas para procesar.")
                self.show_warning("Aviso", "No hay estaciones válidas seleccionadas para procesar.")
                self.set_label(self.status_label, text="Sin estaciones válidas.", text_color="orange")
                return

            ruta_temporal.mkdir(parents=True, exist_ok=True)
            self.log_message(self.output_reports, "Generando informes PDF...")
            start_time = time.time()
            generados_paths = []
            procesadas_validas = 0

            for eid in seleccionadas:
                if self.cancel_event.is_set():
                    self.log_message(self.output_reports, "Generación cancelada por el usuario.")
                    self.set_label(self.status_label, text="Generación cancelada.", text_color="orange")
                    break

                if eid not in estaciones:
                    self.log_message(self.output_reports, f"⚠️ Estación {eid} no encontrada en el Excel.")
                    continue

                datos = estaciones[eid]
                carpeta = Path(self.ruta_base) / eid
                if not carpeta.is_dir():
                    self.log_message(self.output_reports, f"⚠️ No existe carpeta para la estación: {eid}")
                    continue

                datos["fotos"] = {}
                for subdir in carpeta.iterdir():
                    if not subdir.is_dir():
                        continue
                    seccion = normalizar_seccion(subdir.name)
                    if seccion not in SUBCARPETAS:
                        continue
                    fotos = [
                        str(f)
                        for f in subdir.iterdir()
                        if f.suffix.lower() in IMAGE_EXTENSIONS
                    ]
                    if fotos:
                        datos["fotos"].setdefault(seccion, []).extend(sorted(fotos))

                if not datos["fotos"]:
                    self.log_message(self.output_reports, f"⚠️ La estación {eid} no tiene fotos clasificadas.")
                    continue

                self.log_message(self.output_reports, f"Generando informe para {eid} ({datos['nombre'] or 'Sin nombre'})...")
                pdf_generado = self.crear_informe_estacion(eid, datos, self.ruta_base, str(ruta_temporal))
                if pdf_generado:
                    generados_paths.append(pdf_generado)
                    self.last_generated_pdf = pdf_generado
                    self.log_message(
                        self.history_box,
                        f"[{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}] Informe generado para estación {eid}"
                    )

                procesadas_validas += 1
                progreso = procesadas_validas / total_estaciones
                self.set_progress(self.progress_reports, progreso)
                self.update_time_remaining(start_time, progreso)

            if self.cancel_event.is_set():
                return

            if generados_paths:
                zip_name = f"reportes_{datetime.now().strftime('%Y%m%d_%H%M%S')}.zip"
                zip_path = Path(self.ruta_base) / zip_name
                with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as zf:
                    for pdf in generados_paths:
                        if pdf.endswith("-FINAL.pdf"):
                            zf.write(pdf, Path(pdf).name)
                self.log_message(self.output_reports, f"✅ ZIP creado: {zip_path} (solo PDFs finales)")
                self.log_message(self.output_reports, "Proceso de generación de informes completado.")
                self.show_info("Éxito", "Los informes se han generado correctamente.")
                self.set_label(self.status_label, text="Informes generados correctamente.", text_color="green")
            else:
                self.log_message(self.output_reports, "No se generaron informes debido a falta de datos válidos.")
                self.show_warning("Aviso", "No se generaron informes. Verifique las estaciones seleccionadas.")
                self.set_label(self.status_label, text="Sin informes generados.", text_color="orange")
            
        except Exception as e:
            self.log_message(self.output_reports, f"Error: {str(e)}")
            self.show_error("Error", f"Ocurrió un error: {str(e)}")
            self.set_label(self.status_label, text="Error al generar informes.", text_color="red")
        finally:
            if ruta_temporal.exists():
                shutil.rmtree(ruta_temporal, ignore_errors=True)
                self.log_message(self.output_reports, f"Carpeta temporal {ruta_temporal} eliminada.")
            self.set_progress(self.progress_reports, 0)
            self.set_label(self.time_remaining_label, text="Tiempo restante estimado: --:--")
            self.finish_task()
    def redimensionar_imagen(self, path, max_size=(400, 600)):
        """Redimensiona una imagen manteniendo la relación de aspecto."""
        for attempt in range(3):  # Reintentar hasta 3 veces
            try:
                img = Image.open(path)
                
                # Corregir orientación EXIF
                exif = img.getexif()
                if exif:
                    exif_dict = {ExifTags.get(k, k): v for k, v in exif.items()}
                    orientation = exif_dict.get('Orientation', 1)
                    
                    if orientation == 3:
                        img = img.rotate(180, expand=True)
                    elif orientation == 6:
                        img = img.rotate(270, expand=True)
                    elif orientation == 8:
                        img = img.rotate(90, expand=True)
                
                # Redimensionar
                img.thumbnail(max_size, Image.LANCZOS, reducing_gap=3.0)
                
                # Guardar temporalmente
                tmp_path = os.path.join(self.ruta_base, "imagenes_temp", os.path.basename(path))
                img.save(tmp_path, quality=100, dpi=(600, 600), optimize=True, subsampling=0)
                img.close()  # Liberar memoria
                
                return tmp_path
            except Exception as e:
                self.log_message(self.output_reports, f"❌ Error procesando {path} (intento {attempt + 1}): {str(e)}")
                if attempt == 2:  # Último intento
                    self.log_message(self.output_reports, f"⚠️ Se omitirá la imagen por errores persistentes: {path}")
                    return None
                time.sleep(1)  # Esperar antes de reintentar
        return None
    
    def crear_informe_estacion(self, eid, datos, ruta_base, ruta_temporal):
        """Crea un informe PDF para una estación, con portada y banner de problemas."""
        try:
            carpeta_estacion = os.path.join(ruta_base, eid)
            nombre_pdf = f"RP-{eid}.pdf"
            salida_pdf = os.path.join(carpeta_estacion, nombre_pdf)
            salida_final = os.path.join(carpeta_estacion, f"RP-{eid}-FINAL.pdf")
            
            # Rutas de imágenes de fondo
            fondo_portada_path = os.path.join(ruta_base, "fondo_portada.jpg")
            fondo_paginas_path = os.path.join(ruta_base, "fondo_paginas.jpg")
            
            # Función para fondo dinámico basado en el número de página
            def fondo_dinamico(canv, doc):
                canv.saveState()
                try:
                    if doc.page == 1 and os.path.exists(fondo_portada_path):
                        canv.drawImage(fondo_portada_path, 0, 0, width=A4[1], height=A4[0], preserveAspectRatio=True)
                    elif doc.page > 1 and os.path.exists(fondo_paginas_path):
                        canv.drawImage(fondo_paginas_path, 0, 0, width=A4[1], height=A4[0], preserveAspectRatio=True)
                except Exception as e:
                    self.log_message(self.output_reports, f"⚠️ Error al aplicar fondo en página {doc.page}: {str(e)}")
                canv.restoreState()
            
            # Crear documento PDF con una sola plantilla
            doc = BaseDocTemplate(salida_pdf, pagesize=landscape(A4))
            frame = Frame(doc.leftMargin, doc.bottomMargin, doc.width, doc.height, id="normal")
            
            # Plantilla única con fondo dinámico
            plantilla = PageTemplate(id='unica', frames=[frame], onPage=fondo_dinamico)
            doc.addPageTemplates([plantilla])
            
            styles = getSampleStyleSheet()
            s_normal = ParagraphStyle("NormalIzq", parent=styles["Normal"], alignment=TA_LEFT, fontSize=10, leading=14)
            s_titulo = ParagraphStyle("Titulo", parent=styles["Heading3"], textColor=colors.purple, alignment=TA_LEFT, spaceAfter=6)
            s_banner = ParagraphStyle("Banner", parent=styles["Heading2"], textColor=colors.white, backColor=colors.red, alignment=TA_LEFT, leading=16)
            
            story = []
            
            # --- Portada ---
            fecha = datos.get('fecha')
            fecha_str = fecha.strftime('%d/%m/%Y') if hasattr(fecha, 'strftime') else str(fecha) if fecha else '---'
            hora_visita = datos.get('hora_visita')
            hora_visita_str = hora_visita.strftime('%H:%M') if hasattr(hora_visita, 'strftime') else str(hora_visita) if hora_visita else '---'
            hora_salida = datos.get('hora_salida')
            hora_salida_str = hora_salida.strftime('%H:%M') if hasattr(hora_salida, 'strftime') else str(hora_salida) if hora_salida else '---'
            
            trabajos_realizados = """
            <b>TRABAJOS DE MANTENIMIENTO REALIZADOS:</b><br/>
            - Limpieza de áreas verdes.<br/>
            - Limpieza de casetas.<br/>
            - Limpieza general.<br/>
            - Limpieza equipos de acceso y transmisión.<br/>
            - Revisión de sistemas AC y SPaT.<br/>
            - Revisión de equipos de energía y baterías.<br/>
            - Mantenimiento de MG's.<br/>
            - Mantenimiento de A/A o ventilación forzada.
            """
            
            # Bloque de portada: datos de la estación
            portada_bloque = []
            texto_portada = (
                f"<b>{datos['nombre'].upper()}</b><br/><br/>"
                f"<b>Tipo:</b> {datos['tipo']}<br/>"
                f"<b>Coordenadas:</b> {datos['coordenadas']}<br/>"
                f"<b>Fecha:</b> {fecha_str}<br/>"
                f"<b>Hora inspección:</b> {hora_visita_str}<br/>"
                f"<b>Hora salida:</b> {hora_salida_str}<br/><br/>"
                f"{trabajos_realizados}"
            )
            
            portada_bloque.append(Spacer(1, 60))
            portada_bloque.append(Paragraph(texto_portada, s_normal))
            story.extend(portada_bloque)
            story.append(PageBreak())
            
            # --- Contenido de las páginas siguientes ---
            # Banner rojo si hay problemas
            if datos.get("estado", "") == "FALLA" or datos.get("problemas", False):
                story.append(Spacer(1, 6))
                banner_tabla = Table(
                    [[Paragraph("ESTACIÓN CON PROBLEMAS", s_banner)]],
                    colWidths=[doc.width]
                )
                banner_tabla.setStyle(TableStyle([
                    ("BACKGROUND", (0,0), (-1,-1), colors.red),
                    ("ALIGN", (0,0), (-1,-1), "CENTER"),
                    ("VALIGN", (0,0), (-1,-1), "MIDDLE"),
                    ("INNERGRID", (0,0), (-1,-1), 0, colors.red),
                    ("BOX", (0,0), (-1,-1), 0, colors.red),
                    ("TOPPADDING", (0,0), (-1,-1), 6),
                    ("BOTTOMPADDING", (0,0), (-1,-1), 6),
                ]))
                story.append(banner_tabla)
                story.append(Spacer(1, 12))
            
            # Secciones con fotos
            orden_secciones = SUBCARPETAS
            
            fotos_dict = datos["fotos"]
            
            for sec in orden_secciones:
                fotos = fotos_dict.get(sec, [])
                if not fotos:
                    continue
                
                for i in range(0, len(fotos), 3):
                    grupo = fotos[i:i + 3]
                    fila = []
                    col_w = []
                    
                    for fpath in grupo:
                        tmp = self.redimensionar_imagen(fpath)
                        if tmp:
                            img = ReportLabImage(tmp, width=200, height=300)
                            fila.append(img)
                            col_w.append(200)
                            fila.append(Spacer(1, 12))
                            col_w.append(12)
                    
                    if fila and isinstance(fila[-1], Spacer):
                        fila.pop(); col_w.pop()
                    
                    if not fila:
                        continue
                    
                    tabla = Table([fila], colWidths=col_w)
                    tabla.setStyle(TableStyle([
                        ("ALIGN", (0,0), (-1,-1), "CENTER"),
                        ("VALIGN", (0,0), (-1,-1), "MIDDLE"),
                        ("BOTTOMPADDING", (0,0), (-1,-1), 12),
                        ("TOPPADDING", (0,0), (-1,-1), 12),
                    ]))
                    
                    bloque = [
                        Paragraph(f"ESTACIÓN: {datos['nombre'].upper()}", s_titulo),
                        Paragraph(f"SECCIÓN: {sec}", s_titulo),
                        Spacer(1, 6),
                        tabla,
                        Spacer(1, 20)
                    ]
                    story.append(KeepTogether(bloque))
            
            # Construir PDF
            doc.build(story)
            self.log_message(self.output_reports, f"✅ Informe generado: {salida_pdf}")
            
            # Combinar con otros PDFs si existen
            pdfs_a_unir = [salida_pdf]
            for f in os.listdir(carpeta_estacion):
                if f.lower().endswith('.pdf') and f != nombre_pdf and "-FINAL" not in f:
                    pdfs_a_unir.append(os.path.join(carpeta_estacion, f))
            
            # Agregar imagen final si existe
            imagen_final_path = os.path.join(ruta_base, "imagen_final.jpg")
            if os.path.exists(imagen_final_path):
                imagen_final_temp_pdf = os.path.join(ruta_temporal, "imagen_final_temp.pdf")
                self.generar_pdf_imagen_final(imagen_final_path, imagen_final_temp_pdf)
                pdfs_a_unir.append(imagen_final_temp_pdf)
            
            # Unir todos los PDFs
            salida_resultado = salida_pdf
            if len(pdfs_a_unir) > 1:
                merger = PdfMerger()
                for p in pdfs_a_unir:
                    merger.append(p)
                merger.write(salida_final)
                merger.close()
                self.log_message(self.output_reports, f"✅ Informe FINAL generado: {salida_final}")
                salida_resultado = salida_final

            return salida_resultado
            
        except Exception as e:
            self.log_message(self.output_reports, f"❌ Error generando informe para {eid}: {str(e)}")
            return None
    
    def generar_pdf_imagen_final(self, path_img, path_pdf):
        """Genera un PDF con una sola imagen."""
        c = canvas.Canvas(path_pdf, pagesize=landscape(A4))
        c.drawImage(path_img, 0, 0, width=A4[1], height=A4[0])
        c.showPage()
        c.save()

    def cargar_estaciones_para_seleccion(self):
        try:
            df = self.load_estaciones_dataframe(required_columns=["Estacion"])
            if df is None:
                return

            self.estaciones_cache = df
            for container in (self.stations_scroll, self.create_stations_scroll):
                for widget in container.winfo_children():
                    widget.destroy()

            self.station_vars.clear()
            self.station_widgets.clear()
            self.create_station_vars.clear()
            self.create_station_widgets.clear()
            self.estaciones_dict.clear()

            total = 0
            for _, row in df.iterrows():
                eid = str(row.get("Estacion", "")).strip()
                if not eid:
                    continue
                nombre = str(row.get("Nombre", "")).strip()
                estado_raw = str(row.get("Estado", "")).strip().upper()
                estado = estado_raw if estado_raw and estado_raw != "NAN" else "N/A"
                self.estaciones_dict[eid] = {"nombre": nombre, "estado": estado}
                # Reportes selector
                var_report = ctk.BooleanVar(value=True)
                color = "green" if estado == "OK" else "orange" if estado == "PENDIENTE" else "red" if estado == "FALLA" else "gray70"
                chk_report = ctk.CTkCheckBox(
                    self.stations_scroll,
                    text=f"{eid} · {nombre or 'Sin nombre'}",
                    variable=var_report,
                    text_color=color
                )
                chk_report.pack(anchor="w", fill="x", padx=6, pady=2)
                self.station_vars[eid] = var_report
                self.station_widgets[eid] = chk_report

                # Creación selector (inicialmente sin selección)
                var_create = ctk.BooleanVar(value=False)
                chk_create = ctk.CTkCheckBox(
                    self.create_stations_scroll,
                    text=f"{eid} · {nombre or 'Sin nombre'}",
                    variable=var_create,
                    command=self.update_create_selection_summary
                )
                chk_create.pack(anchor="w", fill="x", padx=4, pady=2)
                self.create_station_vars[eid] = var_create
                self.create_station_widgets[eid] = chk_create

                total += 1

            if total == 0:
                ctk.CTkLabel(self.stations_scroll, text="No se encontraron estaciones en el Excel.").pack(anchor="w", padx=6, pady=6)
                ctk.CTkLabel(self.create_stations_scroll, text="No se encontraron estaciones en el Excel.").pack(anchor="w", padx=6, pady=6)
                self.set_label(self.excel_status, text="❌ No se encontraron estaciones válidas en el Excel", text_color="red")
            else:
                self.set_label(self.excel_status, text=f"✅ {total} estaciones disponibles", text_color="green")

            # Restablecer controles
            self.toggle_all_btn.configure(text="Deseleccionar todas")
            self.update_create_selection_summary()

        except Exception as e:
            self.set_label(self.excel_status, text=f"❌ Error al cargar estaciones: {str(e)}", text_color="red")
            self.show_error("Error", f"No se pudieron cargar estaciones del Excel.\n{e}")


class ReviewDuplicatesWindow(ctk.CTkToplevel):
    """Ventana para revisión manual de duplicados."""
    def __init__(self, parent, duplicates_groups):
        super().__init__(parent)
        self.title("Revisión de Duplicados")
        self.geometry("1100x720")
        self.configure(fg_color=parent._fg_color)
        
        self.parent_app = parent
        self.duplicates_groups = duplicates_groups
        self.current_group_index = 0
        self.current_selection = None
        
        self.setup_ui()
        self.show_group(0)
        
    def setup_ui(self):
        hero = ctk.CTkFrame(self, corner_radius=16)
        hero.pack(fill="x", padx=24, pady=(24, 12))
        hero.grid_columnconfigure(1, weight=1)
        ctk.CTkLabel(
            hero,
            text="Panel de duplicados",
            font=ctk.CTkFont(size=22, weight="bold")
        ).grid(row=0, column=0, sticky="w", padx=20, pady=(18, 4))
        self.group_info = ctk.CTkLabel(
            hero,
            text="",
            font=ctk.CTkFont(size=13),
            text_color=("gray70", "gray80")
        )
        self.group_info.grid(row=1, column=0, sticky="w", padx=20, pady=(0, 12))
        ctk.CTkLabel(
            hero,
            text="Marca las imágenes que deseas eliminar. Mantendremos siempre la primera versión de cada grupo.",
            font=ctk.CTkFont(size=12),
            text_color=("gray70", "gray80")
        ).grid(row=2, column=0, sticky="w", padx=20, pady=(0, 18))
        
        body = ctk.CTkFrame(self, fg_color="transparent")
        body.pack(fill="both", expand=True, padx=24, pady=(0, 16))
        body.grid_columnconfigure(0, weight=1)
        body.grid_rowconfigure(0, weight=1)
        
        self.cards_container = ctk.CTkScrollableFrame(body, corner_radius=14)
        self.cards_container.grid(row=0, column=0, sticky="nsew")
        self.cards_container.grid_columnconfigure(0, weight=1)
        
        footer = ctk.CTkFrame(self, corner_radius=14)
        footer.pack(fill="x", padx=24, pady=(0, 24))
        footer.grid_columnconfigure((0, 1, 2), weight=1)
        
        self.prev_btn = ctk.CTkButton(
            footer,
            text="← Grupo anterior",
            command=self.prev_group,
            state="disabled",
            height=36
        )
        self.prev_btn.grid(row=0, column=0, sticky="w", padx=12, pady=12)
        
        self.keep_all_btn = ctk.CTkButton(
            footer,
            text="Mantener todo el grupo",
            command=self.keep_all,
            fg_color=("gray30", "#2ecc71"),
            height=36
        )
        self.keep_all_btn.grid(row=0, column=1, sticky="ew", padx=12, pady=12)
        
        actions_right = ctk.CTkFrame(footer, fg_color="transparent")
        actions_right.grid(row=0, column=2, sticky="e")
        actions_right.grid_columnconfigure((0, 1), weight=1)
        
        self.next_btn = ctk.CTkButton(
            actions_right,
            text="Siguiente grupo →",
            command=self.next_group,
            height=36
        )
        self.next_btn.grid(row=0, column=0, sticky="ew")
        
        self.delete_btn = ctk.CTkButton(
            actions_right,
            text="Eliminar seleccionadas",
            command=self.delete_selected,
            fg_color="#e74c3c",
            state="disabled",
            height=36
        )
        self.delete_btn.grid(row=0, column=1, sticky="ew", padx=(12, 0))

    def show_group(self, index):
        if index < 0 or index >= len(self.duplicates_groups):
            return
            
        self.current_group_index = index
        group = self.duplicates_groups[index]
        
        self.group_info.configure(
            text=f"Grupo {index + 1} de {len(self.duplicates_groups)} · {len(group)} archivos idénticos"
        )
        
        for widget in self.cards_container.winfo_children():
            widget.destroy()
        
        self.image_vars = {}
        for file_info in group:
            card = ctk.CTkFrame(self.cards_container, corner_radius=12)
            card.pack(fill="x", padx=12, pady=8)
            card.grid_columnconfigure(2, weight=1)

            var = ctk.BooleanVar(value=False)
            self.image_vars[file_info['ruta']] = var
            
            toggle = ctk.CTkCheckBox(
                card,
                text="Eliminar",
                variable=var,
                command=lambda v=var, p=file_info['ruta']: self.on_selection_change(v, p)
            )
            toggle.grid(row=0, column=0, rowspan=2, sticky="n", padx=16, pady=16)
            
            try:
                img = Image.open(file_info['ruta'])
                img.thumbnail((180, 180))
                img_ctk = ctk.CTkImage(light_image=img, size=(180, 180))
                img_label = ctk.CTkLabel(card, image=img_ctk, text="")
                img_label.image = img_ctk
                img_label.grid(row=0, column=1, rowspan=2, sticky="w", padx=12, pady=12)
            except Exception as e:
                img_label = ctk.CTkLabel(card, text="Vista previa no disponible", text_color="red")
                img_label.grid(row=0, column=1, rowspan=2, sticky="w", padx=12, pady=12)
                self.parent_app.log_message(self.parent_app.output_duplicates, f"Error al cargar imagen para vista previa: {str(e)}")

            info_block = ctk.CTkFrame(card, fg_color="transparent")
            info_block.grid(row=0, column=2, sticky="nw", padx=12, pady=(16, 0))
            info_block.grid_columnconfigure(0, weight=1)
            ctk.CTkLabel(
                info_block,
                text=file_info['nombre_archivo'],
                font=ctk.CTkFont(size=14, weight="bold")
            ).grid(row=0, column=0, sticky="w")
            ctk.CTkLabel(
                info_block,
                text=f"Estación: {file_info['estacion']}  ·  Sección: {file_info['subcarpeta']}",
                font=ctk.CTkFont(size=12),
                text_color=("gray70", "gray80")
            ).grid(row=1, column=0, sticky="w", pady=(4, 0))
            ctk.CTkLabel(
                info_block,
                text=file_info['ruta'],
                font=ctk.CTkFont(size=11),
                text_color=("gray60", "gray70"),
                wraplength=640,
                justify="left"
            ).grid(row=2, column=0, sticky="w", pady=(4, 0))
            
            view_btn = ctk.CTkButton(
                card,
                text="Abrir imagen",
                command=lambda p=file_info['ruta']: self.view_full_image(p),
                height=32
            )
            view_btn.grid(row=1, column=2, sticky="se", padx=12, pady=12)
        
        self.prev_btn.configure(state="normal" if index > 0 else "disabled")
        self.next_btn.configure(state="normal" if index < len(self.duplicates_groups) - 1 else "disabled")
        
    def on_selection_change(self, var, path):
        if var.get():
            self.current_selection = path
            self.delete_btn.configure(state="normal")
        else:
            self.current_selection = None
            # Verificar si hay alguna selección
            any_selected = any(var.get() for var in self.image_vars.values())
            self.delete_btn.configure(state="normal" if any_selected else "disabled")
    
    def view_full_image(self, path):
        """Abre la imagen en el visor predeterminado del sistema."""
        try:
            if sys.platform == "win32":
                os.startfile(path)
            elif sys.platform == "darwin":
                subprocess.call(("open", path))
            else:
                subprocess.call(("xdg-open", path))
        except Exception as e:
            messagebox.showerror("Error", f"No se pudo abrir la imagen: {str(e)}")
    
    def prev_group(self):
        if self.current_group_index > 0:
            self.show_group(self.current_group_index - 1)
    
    def next_group(self):
        if self.current_group_index < len(self.duplicates_groups) - 1:
            self.show_group(self.current_group_index + 1)
    
    def keep_all(self):
        """Mantiene todas las fotos del grupo actual."""
        messagebox.showinfo("Información", "Todas las fotos se mantendrán.")
        if self.current_group_index < len(self.duplicates_groups) - 1:
            self.next_group()
        else:
            messagebox.showinfo("Completado", "Revisión de todos los grupos completada.")
            self.destroy()
    
    def delete_selected(self):
        """Elimina las fotos seleccionadas."""
        selected_files = [path for path, var in self.image_vars.items() if var.get()]
        
        if not selected_files:
            messagebox.showwarning("Advertencia", "No hay fotos seleccionadas para eliminar.")
            return
        
        confirm = messagebox.askyesno(
            "Confirmar Eliminación",
            f"¿Está seguro de que desea eliminar {len(selected_files)} foto(s)?\n\n"
            "Esta acción no se puede deshacer."
        )
        
        if confirm:
            deleted_count = 0
            for file_path in selected_files:
                try:
                    os.remove(file_path)
                    deleted_count += 1
                except Exception as e:
                    messagebox.showerror("Error", f"No se pudo eliminar {file_path}: {str(e)}")
            
            messagebox.showinfo("Éxito", f"Se eliminaron {deleted_count} foto(s).")
            
            # Recargar el grupo actual o pasar al siguiente
            if self.current_group_index < len(self.duplicates_groups) - 1:
                self.next_group()
            else:
                messagebox.showinfo("Completado", "Revisión de todos los grupos completada.")
                self.destroy()


if __name__ == "__main__":
    app = MaintenanceApp()
    app.mainloop()
