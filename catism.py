import copy
import os
import shutil
import subprocess
import tempfile
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import xml.etree.ElementTree as ET

from PIL import Image, ImageTk
from psd_tools import PSDImage
from psd_tools.api.layers import Group, PixelLayer


THEME = {
    "accent": "#F47B20",
    "accent_dark": "#D96312",
    "accent_light": "#FF9A4A",
    "background": "#F3F3F3",
    "panel": "#FFFFFF",
    "text": "#292929",
    "muted": "#777777",
    "border": "#D4D4D4",
    "selected": "#FFE2CF",
}

EXPORT_WORKERS = 4


def local_name(tag):
    if not isinstance(tag, str):
        return ""
    return tag.rsplit("}", 1)[-1]


def is_graphical_element(element):
    return local_name(element.tag) in {
        "path",
        "rect",
        "circle",
        "ellipse",
        "line",
        "polyline",
        "polygon",
        "image",
        "text",
        "use",
        "symbol",
    }


def set_display_hidden(element):
    style = element.get("style", "")
    parts = []

    if style:
        for item in style.split(";"):
            item = item.strip()
            if item and not item.startswith("display:"):
                parts.append(item)

    parts.append("display:none")
    element.set("style", ";".join(parts))


def write_xml(root, filename):
    tree = ET.ElementTree(root)

    try:
        ET.indent(tree, space="  ")
    except AttributeError:
        pass

    tree.write(
        filename,
        encoding="utf-8",
        xml_declaration=True,
    )

def find_inkscape_startup():
    candidates = []

    env_path = os.environ.get("INKSCAPE_PATH")

    if env_path:
        candidates.append(env_path)

    candidates.extend([
        r"C:\Program Files\Inkscape\bin\inkscape.exe",
        r"C:\Program Files\Inkscape\inkscape.exe",
        r"C:\Program Files (x86)\Inkscape\bin\inkscape.exe",
        r"C:\Program Files (x86)\Inkscape\inkscape.exe",
        os.path.expandvars(
            r"%LOCALAPPDATA%\Programs\Inkscape\bin\inkscape.exe"
        ),
        os.path.expandvars(
            r"%LOCALAPPDATA%\Programs\Inkscape\inkscape.exe"
        ),
    ])

    which = shutil.which("inkscape")

    if which:
        candidates.append(which)

    for candidate in candidates:
        if candidate and os.path.isfile(candidate):
            return True

    return False


class LayerNode:
    def __init__(
        self,
        name,
        node_type,
        parent=None,
        xml_element=None,
        path_index=None,
    ):
        self.name = name
        self.node_type = node_type
        self.parent = parent
        self.children = []
        self.xml_element = xml_element
        self.path_index = path_index
        self.visible = True

        if parent is not None:
            parent.children.append(self)

    @property
    def is_group(self):
        return self.node_type == "group"

    @property
    def is_path(self):
        return self.node_type == "path"


class SVGProject:
    def __init__(self):
        self.filename = None
        self.svg_root = None
        self.tree_root = None
        self.svg_path_elements = []
        self.svg_path_index = {}
        self.native_width = None
        self.native_height = None
        self.viewbox = None
        self.output_width = 1000
        self.output_height = 1000

    def load(self, filename):
        self.filename = filename
        tree = ET.parse(filename)
        self.svg_root = tree.getroot()

        self._read_dimensions()
        self._index_paths()
        self._build_layer_tree()

        if self.native_width and self.native_height:
            self.output_width = int(round(self.native_width))
            self.output_height = int(round(self.native_height))
        elif self.viewbox:
            _, _, width, height = self.viewbox

            if width > 0 and height > 0:
                self.output_width = int(round(width))
                self.output_height = int(round(height))

    def _read_dimensions(self):
        root = self.svg_root

        self.native_width = self._parse_dimension(
            root.get("width")
        )
        self.native_height = self._parse_dimension(
            root.get("height")
        )

        viewbox = root.get("viewBox")

        if viewbox:
            try:
                values = [
                    float(x)
                    for x in viewbox.replace(",", " ").split()
                ]

                if len(values) == 4:
                    self.viewbox = tuple(values)
            except ValueError:
                self.viewbox = None

    @staticmethod
    def _parse_dimension(value):
        if not value:
            return None

        value = value.strip()
        number = ""

        for char in value:
            if char.isdigit() or char in ".-+":
                number += char
            else:
                break

        try:
            return float(number)
        except ValueError:
            return None

    def _index_paths(self):
        self.svg_path_elements = []
        self.svg_path_index = {}

        for element in self.svg_root.iter():
            if local_name(element.tag) == "path":
                index = len(self.svg_path_elements)
                self.svg_path_elements.append(element)
                self.svg_path_index[id(element)] = index

    def _build_layer_tree(self):
        self.tree_root = LayerNode("SVG", "root")

        def walk(element, parent_node, inside_group=False):
            for child in list(element):
                tag = local_name(child.tag)

                if tag == "g":
                    group_name = (
                        child.get("inkscape:label")
                        or child.get("label")
                        or child.get("id")
                        or "Group"
                    )

                    group_node = LayerNode(
                        group_name,
                        "group",
                        parent=parent_node,
                        xml_element=child,
                    )

                    walk(
                        child,
                        group_node,
                        inside_group=True,
                    )

                elif tag == "path":
                    path_index = self.svg_path_index.get(id(child))

                    if inside_group:
                        path_parent = parent_node
                    else:
                        path_parent = LayerNode(
                            "Path Group",
                            "group",
                            parent=parent_node,
                        )

                    path_name = (
                        child.get("inkscape:label")
                        or child.get("label")
                        or child.get("id")
                        or f"Path {path_index + 1}"
                    )

                    LayerNode(
                        path_name,
                        "path",
                        parent=path_parent,
                        xml_element=child,
                        path_index=path_index,
                    )

                else:
                    walk(
                        child,
                        parent_node,
                        inside_group=inside_group,
                    )

        walk(self.svg_root, self.tree_root)

    def all_path_nodes(self):
        result = []

        def walk(node):
            for child in node.children:
                if child.is_path:
                    result.append(child)
                walk(child)

        walk(self.tree_root)
        return result

    def all_groups(self):
        result = []

        def walk(node):
            for child in node.children:
                if child.is_group:
                    result.append(child)
                walk(child)

        walk(self.tree_root)
        return result

    def set_visibility_recursive(self, node, visible):
        node.visible = visible

        for child in node.children:
            self.set_visibility_recursive(child, visible)

    def prepare_render_svg(self, selected_path=None):
        if self.svg_root is None:
            raise RuntimeError("No SVG is loaded.")

        root = copy.deepcopy(self.svg_root)

        copied_paths = [
            element
            for element in root.iter()
            if local_name(element.tag) == "path"
        ]

        if len(copied_paths) != len(self.svg_path_elements):
            raise RuntimeError(
                "The copied SVG has a different number "
                "of paths than the original."
            )

        copied_path_indices = {
            id(element): index
            for index, element in enumerate(copied_paths)
        }

        selected_index = None

        if selected_path is not None:
            selected_index = selected_path.path_index

        visible_indices = None

        if selected_path is None:
            visible_indices = {
                node.path_index
                for node in self.all_path_nodes()
                if node.visible and node.path_index is not None
            }

        for element in root.iter():
            tag = local_name(element.tag)

            if tag in {
                "defs",
                "clipPath",
                "mask",
                "linearGradient",
                "radialGradient",
                "filter",
                "pattern",
                "marker",
                "symbol",
            }:
                continue

            if tag == "path":
                index = copied_path_indices.get(id(element))

                if selected_path is not None:
                    if index != selected_index:
                        set_display_hidden(element)
                elif index not in visible_indices:
                    set_display_hidden(element)

            elif selected_path is not None:
                if is_graphical_element(element):
                    set_display_hidden(element)

        root.set(
            "preserveAspectRatio",
            "xMidYMid meet",
        )

        return root

    def prepare_preview_svg(self):
        if self.svg_root is None:
            raise RuntimeError("No SVG is loaded.")

        root = copy.deepcopy(self.svg_root)
        root.set(
            "preserveAspectRatio",
            "xMidYMid meet",
        )

        return root


class InkscapeRenderer:
    def __init__(self):
        self.exe = self.find_inkscape()

    @staticmethod
    def find_inkscape():
        candidates = []

        env_path = os.environ.get("INKSCAPE_PATH")

        if env_path:
            candidates.append(env_path)

        candidates.extend([
            r"C:\Program Files\Inkscape\bin\inkscape.exe",
            r"C:\Program Files\Inkscape\inkscape.exe",
            r"C:\Program Files (x86)\Inkscape\bin\inkscape.exe",
            r"C:\Program Files (x86)\Inkscape\inkscape.exe",
            os.path.expandvars(
                r"%LOCALAPPDATA%\Programs\Inkscape\bin\inkscape.exe"
            ),
            os.path.expandvars(
                r"%LOCALAPPDATA%\Programs\Inkscape\inkscape.exe"
            ),
        ])

        which = shutil.which("inkscape")

        if which:
            candidates.append(which)

        for candidate in candidates:
            if candidate and os.path.isfile(candidate):
                return candidate

        return None

    def require(self):
        if not self.exe:
            raise RuntimeError(
                "Inkscape could not be found.\n\n"
                "Install Inkscape or set INKSCAPE_PATH "
                "to your inkscape.exe."
            )

    def render_svg_root(
        self,
        root,
        output_png,
        width=None,
        height=None,
        cancel_event=None,
        working_dir=None,
        temp_svg_name="render.svg",
    ):
        self.require()

        owns_temp_dir = working_dir is None

        if owns_temp_dir:
            temp_dir = tempfile.mkdtemp(
                prefix="cubism_svg_"
            )
        else:
            temp_dir = working_dir
            os.makedirs(temp_dir, exist_ok=True)

        try:
            temp_svg = os.path.join(
                temp_dir,
                temp_svg_name,
            )

            write_xml(root, temp_svg)

            command = [
                self.exe,
                temp_svg,
                "--export-type=png",
                f"--export-filename={output_png}",
                "--export-background-opacity=0",
                "--export-overwrite",
            ]

            if width is not None:
                command.append(
                    f"--export-width={int(width)}"
                )

            if height is not None:
                command.append(
                    f"--export-height={int(height)}"
                )

            process = subprocess.Popen(
                command,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                encoding="utf-8",
                errors="replace",
            )

            while process.poll() is None:
                if (
                    cancel_event is not None
                    and cancel_event.is_set()
                ):
                    process.kill()
                    process.wait()
                    raise RuntimeError("Operation cancelled.")

                threading.Event().wait(0.05)

            stdout, stderr = process.communicate()

            if process.returncode != 0:
                error_text = stderr.strip() or stdout.strip()
                raise RuntimeError(
                    "Inkscape rendering failed.\n\n"
                    + error_text
                )

            if not os.path.isfile(output_png):
                raise RuntimeError(
                    "Inkscape completed but did not create "
                    "the PNG output."
                )

            return output_png

        finally:
            if owns_temp_dir:
                shutil.rmtree(
                    temp_dir,
                    ignore_errors=True,
                )

    def render_preview(
        self,
        root,
        output_png,
        max_size=700,
        cancel_event=None,
    ):
        aspect = self.get_aspect_ratio(root)

        if aspect >= 1:
            return self.render_svg_root(
                root,
                output_png,
                width=int(max_size),
                height=None,
                cancel_event=cancel_event,
            )

        return self.render_svg_root(
            root,
            output_png,
            width=None,
            height=int(max_size),
            cancel_event=cancel_event,
        )

    @staticmethod
    def get_aspect_ratio(root):
        viewbox = root.get("viewBox")

        if viewbox:
            try:
                values = [
                    float(x)
                    for x in viewbox.replace(",", " ").split()
                ]

                if len(values) == 4:
                    _, _, width, height = values

                    if width > 0 and height > 0:
                        return width / height

            except ValueError:
                pass

        width = SVGProject._parse_dimension(
            root.get("width")
        )
        height = SVGProject._parse_dimension(
            root.get("height")
        )

        if width and height and width > 0 and height > 0:
            return width / height

        return 1.0


def add_psd_group(parent, name):
    group = Group.new(
        name=name,
        parent=parent,
    )

    parent.append(group)
    return group


def add_pixel_layer(parent, image, name):
    layer = PixelLayer.frompil(
        image,
        parent=parent,
        name=name,
        top=0,
        left=0,
    )

    parent.append(layer)
    return layer


class CubismPrepApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Catism (V1.0)")
        self.root.geometry("620x470")
        self.root.minsize(560, 600)
        self.root.resizable(False, False)

        self.project = SVGProject()
        self.renderer = InkscapeRenderer()

        self.preview_image = None
        self.preview_photo = None

        self.svg_title_photo = None
        self.cubism_title_photo = None
        self.load_title_images()

        self.export_thread = None
        self.cancel_event = threading.Event()

        self.layer_items = {}
        self.layer_nodes_by_item = {}

        self.width_var = tk.StringVar(value="1000")
        self.height_var = tk.StringVar(value="1000")
        self.link_ratio_var = tk.BooleanVar(value=True)
        self.linked_ratio = 1.0

        self.path_progress_var = tk.StringVar(
            value=""
        )

        self.status_var = tk.StringVar(
            value="Import an SVG to begin."
        )

        self.build_style()
        self.build_ui()

    def load_title_images(self):
        base_dir = os.path.dirname(
            os.path.abspath(__file__)
        )

        svg_path = os.path.join(
            base_dir,
            "svg.png",
        )

        cubism_path = os.path.join(
            base_dir,
            "cubism.png",
        )

        try:
            if os.path.isfile(svg_path):
                image = Image.open(svg_path).convert("RGBA")
                image.thumbnail(
                    (28, 28),
                    Image.Resampling.LANCZOS,
                )
                self.svg_title_photo = ImageTk.PhotoImage(image)
        except Exception:
            self.svg_title_photo = None

        try:
            if os.path.isfile(cubism_path):
                image = Image.open(cubism_path).convert("RGBA")
                image.thumbnail(
                    (28, 28),
                    Image.Resampling.LANCZOS,
                )
                self.cubism_title_photo = ImageTk.PhotoImage(image)
        except Exception:
            self.cubism_title_photo = None

    def build_style(self):
        style = ttk.Style()

        try:
            style.theme_use("clam")
        except tk.TclError:
            pass

        style.configure(
            ".",
            font=("Segoe UI", 9),
        )

        style.configure(
            "TFrame",
            background=THEME["background"],
        )

        style.configure(
            "Panel.TFrame",
            background=THEME["panel"],
        )

        style.configure(
            "TLabel",
            background=THEME["background"],
            foreground=THEME["text"],
        )

        style.configure(
            "Panel.TLabel",
            background=THEME["panel"],
            foreground=THEME["text"],
        )

        style.configure(
            "Muted.TLabel",
            background=THEME["panel"],
            foreground=THEME["muted"],
        )

        style.configure(
            "TButton",
            padding=(9, 5),
            background=THEME["panel"],
            foreground=THEME["text"],
            bordercolor=THEME["border"],
        )

        style.map(
            "TButton",
            background=[
                ("active", THEME["accent_light"])
            ],
            foreground=[
                ("active", "#FFFFFF")
            ],
        )

        style.configure(
            "Accent.TButton",
            padding=(11, 5),
            background=THEME["accent"],
            foreground="#FFFFFF",
            bordercolor=THEME["accent"],
        )

        style.map(
            "Accent.TButton",
            background=[
                ("active", THEME["accent_dark"])
            ],
        )

        style.configure(
            "TNotebook",
            background=THEME["background"],
            borderwidth=0,
        )

        style.configure(
            "TNotebook.Tab",
            padding=(11, 6),
            background=THEME["background"],
            foreground=THEME["muted"],
        )

        style.map(
            "TNotebook.Tab",
            background=[
                ("selected", THEME["accent"])
            ],
            foreground=[
                ("selected", "#FFFFFF")
            ],
        )

        style.configure(
            "Treeview",
            background=THEME["panel"],
            fieldbackground=THEME["panel"],
            foreground=THEME["text"],
            rowheight=22,
            bordercolor=THEME["border"],
        )

        style.map(
            "Treeview",
            background=[
                ("selected", THEME["selected"])
            ],
            foreground=[
                ("selected", THEME["text"])
            ],
        )

        style.configure(
            "TEntry",
            padding=4,
        )

    def build_ui(self):
        outer = ttk.Frame(
            self.root,
            padding=8,
        )

        outer.pack(
            fill="both",
            expand=True,
        )

        header = ttk.Frame(outer)

        header.pack(
            fill="x",
            pady=(0, 6),
        )

        title_frame = tk.Frame(
            header,
            bg=THEME["background"],
        )

        title_frame.pack(side="left")

        if self.svg_title_photo is not None:
            tk.Label(
                title_frame,
                image=self.svg_title_photo,
                bg=THEME["background"],
                bd=0,
            ).pack(
                side="left",
                padx=(0, 4),
            )

        tk.Label(
            title_frame,
            text="SVG",
            font=("Segoe UI Semibold", 13),
            fg=THEME["accent"],
            bg=THEME["background"],
            bd=0,
        ).pack(side="left")

        tk.Label(
            title_frame,
            text=" → ",
            font=("Segoe UI Semibold", 13),
            fg=THEME["accent"],
            bg=THEME["background"],
            bd=0,
        ).pack(side="left")

        if self.cubism_title_photo is not None:
            tk.Label(
                title_frame,
                image=self.cubism_title_photo,
                bg=THEME["background"],
                bd=0,
            ).pack(
                side="left",
                padx=(0, 4),
            )

        tk.Label(
            title_frame,
            text="Cubism",
            font=("Segoe UI Semibold", 13),
            fg=THEME["accent"],
            bg=THEME["background"],
            bd=0,
        ).pack(side="left")

        ttk.Label(
            header,
            textvariable=self.path_progress_var,
            style="TLabel",
        ).pack(
            side="right",
            padx=(0, 7),
        )

        ttk.Button(
            header,
            text="Import SVG",
            style="Accent.TButton",
            command=self.import_svg,
        ).pack(side="right")

        self.notebook = ttk.Notebook(outer)

        self.notebook.pack(
            fill="both",
            expand=True,
        )

        self.build_import_tab()
        self.build_layers_tab()
        self.build_export_tab()

        status_frame = ttk.Frame(outer)

        status_frame.pack(
            fill="x",
            pady=(5, 0),
        )

        ttk.Label(
            status_frame,
            textvariable=self.status_var,
            foreground=THEME["muted"],
        ).pack(side="left")

    def build_import_tab(self):
        self.import_tab = ttk.Frame(
            self.notebook,
            padding=8,
        )

        self.notebook.add(
            self.import_tab,
            text="Import",
        )

        panel = ttk.Frame(
            self.import_tab,
            style="Panel.TFrame",
            padding=12,
        )

        panel.pack(
            fill="both",
            expand=True,
        )

        self.file_label = ttk.Label(
            panel,
            text="No SVG loaded",
            style="Panel.TLabel",
            font=("Segoe UI Semibold", 10),
        )

        self.file_label.pack(anchor="w")

        self.svg_info_label = ttk.Label(
            panel,
            text="",
            style="Muted.TLabel",
        )

        self.svg_info_label.pack(
            anchor="w",
            pady=(3, 12),
        )

        ttk.Label(
            panel,
            text=(
                "SVG groups become PSD groups.\n"
                "SVG paths become individual PSD layers.\n"
                "Non-path background elements are not imported "
                "as layers.\n"
                "Transparency is preserved."
            ),
            style="Panel.TLabel",
            justify="left",
        ).pack(anchor="w")

    def build_layers_tab(self):
        self.layers_tab = ttk.Frame(
            self.notebook,
            padding=7,
        )

        self.notebook.add(
            self.layers_tab,
            text="Layers",
        )

        left = ttk.Frame(self.layers_tab)

        left.pack(
            side="left",
            fill="both",
            expand=True,
        )

        right = ttk.Frame(
            self.layers_tab,
            width=140,
        )

        right.pack(
            side="right",
            fill="y",
            padx=(7, 0),
        )

        tree_frame = ttk.Frame(
            left,
            style="Panel.TFrame",
        )

        tree_frame.pack(
            fill="both",
            expand=True,
        )

        self.layer_tree = ttk.Treeview(
            tree_frame,
            show="tree",
            selectmode="browse",
        )

        self.layer_tree.pack(
            side="left",
            fill="both",
            expand=True,
        )

        scrollbar = ttk.Scrollbar(
            tree_frame,
            orient="vertical",
            command=self.layer_tree.yview,
        )

        scrollbar.pack(
            side="right",
            fill="y",
        )

        self.layer_tree.configure(
            yscrollcommand=scrollbar.set
        )

        self.layer_tree.bind(
            "<Double-1>",
            self.rename_selected_layer,
        )

        self.layer_tree.bind(
            "<space>",
            self.toggle_selected_visibility,
        )

        ttk.Button(
            right,
            text="Rename",
            command=self.rename_selected_layer,
        ).pack(
            fill="x",
            pady=(0, 4),
        )

        ttk.Button(
            right,
            text="Visibility",
            command=self.toggle_selected_visibility,
        ).pack(
            fill="x",
            pady=(0, 4),
        )

        ttk.Button(
            right,
            text="Expand All",
            command=lambda: self.expand_all(True),
        ).pack(
            fill="x",
            pady=(12, 4),
        )

        ttk.Button(
            right,
            text="Collapse All",
            command=lambda: self.expand_all(False),
        ).pack(
            fill="x",
        )

    def build_export_tab(self):
        self.export_tab = ttk.Frame(
            self.notebook,
            padding=8,
        )

        self.notebook.add(
            self.export_tab,
            text="Export",
        )

        panel = ttk.Frame(
            self.export_tab,
            style="Panel.TFrame",
            padding=10,
        )

        panel.pack(
            fill="both",
            expand=True,
        )

        resolution_frame = ttk.Frame(
            panel,
            style="Panel.TFrame",
        )

        resolution_frame.pack(fill="x")

        ttk.Label(
            resolution_frame,
            text="Output size",
            style="Panel.TLabel",
            font=("Segoe UI Semibold", 10),
        ).grid(
            row=0,
            column=0,
            columnspan=5,
            sticky="w",
            pady=(0, 6),
        )

        ttk.Label(
            resolution_frame,
            text="Width",
            style="Panel.TLabel",
        ).grid(
            row=1,
            column=0,
        )

        self.width_entry = ttk.Entry(
            resolution_frame,
            textvariable=self.width_var,
            width=9,
        )

        self.width_entry.grid(
            row=1,
            column=1,
            padx=(4, 8),
        )

        ttk.Label(
            resolution_frame,
            text="Height",
            style="Panel.TLabel",
        ).grid(
            row=1,
            column=2,
        )

        self.height_entry = ttk.Entry(
            resolution_frame,
            textvariable=self.height_var,
            width=9,
        )

        self.height_entry.grid(
            row=1,
            column=3,
            padx=(4, 8),
        )

        ttk.Checkbutton(
            resolution_frame,
            text="Link",
            variable=self.link_ratio_var,
            command=self.on_ratio_toggle,
        ).grid(
            row=1,
            column=4,
        )

        self.width_entry.bind(
            "<KeyRelease>",
            self.on_width_changed,
        )

        self.height_entry.bind(
            "<KeyRelease>",
            self.on_height_changed,
        )

        ttk.Label(
            panel,
            text="Preview",
            style="Panel.TLabel",
            font=("Segoe UI Semibold", 10),
        ).pack(
            anchor="w",
            pady=(10, 4),
        )

        preview_frame = ttk.Frame(
            panel,
            style="Panel.TFrame",
        )

        preview_frame.pack(
            fill="both",
            expand=True,
        )

        self.preview_canvas = tk.Canvas(
            preview_frame,
            background="#E7E7E7",
            highlightthickness=1,
            highlightbackground=THEME["border"],
        )

        self.preview_canvas.pack(
            fill="both",
            expand=True,
        )

        self.preview_canvas.bind(
            "<Configure>",
            lambda event: self.redraw_preview(),
        )

        bottom = ttk.Frame(
            panel,
            style="Panel.TFrame",
        )

        bottom.pack(
            fill="x",
            pady=(6, 0),
        )

        self.export_button = ttk.Button(
            bottom,
            text="Export PSD",
            style="Accent.TButton",
            command=self.export_psd,
        )

        self.export_button.pack(side="left")

        self.cancel_button = ttk.Button(
            bottom,
            text="Cancel",
            command=self.cancel_export,
            state="disabled",
        )

        self.cancel_button.pack(
            side="left",
            padx=(4, 0),
        )

    def import_svg(self):
        filename = filedialog.askopenfilename(
            title="Import SVG",
            filetypes=[
                ("SVG files", "*.svg"),
                ("All files", "*.*"),
            ],
        )

        if not filename:
            return

        try:
            self.project.load(filename)

            width = self.project.output_width
            height = self.project.output_height

            self.width_var.set(str(width))
            self.height_var.set(str(height))

            if width > 0 and height > 0:
                self.linked_ratio = width / height

            self.file_label.configure(
                text=os.path.basename(filename)
            )

            info = []

            if (
                self.project.native_width
                and self.project.native_height
            ):
                info.append(
                    "Native: "
                    f"{self.project.native_width:g} × "
                    f"{self.project.native_height:g}"
                )

            if self.project.viewbox:
                _, _, vb_width, vb_height = self.project.viewbox

                info.append(
                    "ViewBox: "
                    f"{vb_width:g} × "
                    f"{vb_height:g}"
                )

            total_paths = len(
                self.project.svg_path_elements
            )

            self.path_progress_var.set(
                f"0 / {total_paths} paths"
            )

            info.append(f"Paths: {total_paths}")

            self.svg_info_label.configure(
                text="    ".join(info)
            )

            self.populate_layer_tree()

            self.status_var.set(
                "SVG imported successfully."
            )

            self.notebook.select(self.layers_tab)
            self.refresh_preview()

        except Exception as exc:
            messagebox.showerror(
                "Import failed",
                str(exc),
            )

    def populate_layer_tree(self):
        for item in self.layer_tree.get_children():
            self.layer_tree.delete(item)

        self.layer_items.clear()
        self.layer_nodes_by_item.clear()

        root_node = self.project.tree_root

        if root_node is None:
            return

        def add_node(node, parent_item=""):
            if node is root_node:
                item = self.layer_tree.insert(
                    "",
                    "end",
                    text=node.name,
                    open=True,
                )
            else:
                prefix = "● " if node.visible else "○ "

                item = self.layer_tree.insert(
                    parent_item,
                    "end",
                    text=prefix + node.name,
                    open=node.is_group,
                )

            self.layer_items[id(node)] = item
            self.layer_nodes_by_item[item] = node

            for child in node.children:
                add_node(child, item)

        add_node(root_node)

    def selected_node(self):
        selection = self.layer_tree.selection()

        if not selection:
            return None

        return self.layer_nodes_by_item.get(
            selection[0]
        )

    def refresh_tree_node_text(self, node):
        item = self.layer_items.get(id(node))

        if not item:
            return

        prefix = "● " if node.visible else "○ "

        self.layer_tree.item(
            item,
            text=prefix + node.name,
        )

    def rename_selected_layer(self, event=None):
        node = self.selected_node()

        if node is None or node is self.project.tree_root:
            return

        item = self.layer_items.get(id(node))

        if item is None:
            return

        bbox = self.layer_tree.bbox(item, "#0")

        if not bbox:
            return

        x, y, width, height = bbox

        entry = tk.Entry(
            self.layer_tree,
            bd=0,
            highlightthickness=1,
            highlightcolor=THEME["accent"],
        )

        entry.place(
            x=x,
            y=y,
            width=width,
            height=height,
        )

        entry.insert(0, node.name)
        entry.select_range(0, "end")
        entry.focus_set()

        def finish(event=None):
            new_name = entry.get().strip()

            if new_name:
                node.name = new_name
                self.refresh_tree_node_text(node)

            entry.destroy()

        entry.bind("<Return>", finish)
        entry.bind(
            "<Escape>",
            lambda event: entry.destroy(),
        )
        entry.bind("<FocusOut>", finish)

    def toggle_selected_visibility(self, event=None):
        node = self.selected_node()

        if node is None or node is self.project.tree_root:
            return

        new_visibility = not node.visible

        self.project.set_visibility_recursive(
            node,
            new_visibility,
        )

        def refresh(current):
            self.refresh_tree_node_text(current)

            for child in current.children:
                refresh(child)

        refresh(node)
        self.refresh_preview()

    def expand_all(self, expand):
        def walk(item):
            self.layer_tree.item(
                item,
                open=expand,
            )

            for child in self.layer_tree.get_children(item):
                walk(child)

        for root_item in self.layer_tree.get_children():
            walk(root_item)

    def parse_output_size(self):
        try:
            width = int(float(self.width_var.get()))
            height = int(float(self.height_var.get()))
        except ValueError:
            raise ValueError(
                "Width and height must be valid numbers."
            )

        if width <= 0 or height <= 0:
            raise ValueError(
                "Width and height must be greater than zero."
            )

        return width, height

    def on_ratio_toggle(self):
        if not self.link_ratio_var.get():
            return

        try:
            width = float(self.width_var.get())
            height = float(self.height_var.get())

            if width <= 0 or height <= 0:
                return

            self.linked_ratio = width / height

        except ValueError:
            pass

    def on_width_changed(self, event=None):
        if not self.link_ratio_var.get():
            return

        try:
            width = float(self.width_var.get())

            if width > 0 and self.linked_ratio > 0:
                height = width / self.linked_ratio

                self.height_var.set(
                    str(max(1, int(round(height))))
                )

        except ValueError:
            pass

    def on_height_changed(self, *_):
        if not self.project:
            return

        try:
            height = int(self.height_var.get())

            if height <= 0:
                return

            ratio = self.linked_ratio

            if not ratio or ratio <= 0:
                return

            width = int(round(height * ratio))

            self.width_var.set(
                str(max(1, width))
            )

        except (ValueError, TypeError):
            pass

    def refresh_preview(self):
        if self.project.svg_root is None:
            return

        try:
            preview_root = self.project.prepare_render_svg(
                selected_path=None
            )

            temp_dir = tempfile.mkdtemp(
                prefix="cubism_preview_"
            )

            output_png = os.path.join(
                temp_dir,
                "preview.png",
            )

            self.renderer.render_preview(
                preview_root,
                output_png,
                max_size=700,
            )

            with Image.open(output_png) as image:
                self.preview_image = image.convert("RGBA")

            shutil.rmtree(
                temp_dir,
                ignore_errors=True,
            )

            self.redraw_preview()

        except Exception as exc:
            self.status_var.set(
                f"Preview error: {exc}"
            )

    def redraw_preview(self):
        if self.preview_image is None:
            return

        canvas_width = self.preview_canvas.winfo_width()
        canvas_height = self.preview_canvas.winfo_height()

        if canvas_width <= 2 or canvas_height <= 2:
            return

        image_width, image_height = self.preview_image.size

        if image_width <= 0 or image_height <= 0:
            return

        scale = min(
            canvas_width / image_width,
            canvas_height / image_height,
        )

        display_width = max(
            1,
            int(round(image_width * scale)),
        )

        display_height = max(
            1,
            int(round(image_height * scale)),
        )

        resized = self.preview_image.resize(
            (
                display_width,
                display_height,
            ),
            Image.Resampling.LANCZOS,
        )

        self.preview_photo = ImageTk.PhotoImage(resized)

        self.preview_canvas.delete("all")

        self.preview_canvas.create_image(
            canvas_width // 2,
            canvas_height // 2,
            image=self.preview_photo,
            anchor="center",
        )

    def set_path_progress(self, completed, total):
        def update():
            try:
                self.path_progress_var.set(
                    f"{completed} / {total} paths"
                )
            except tk.TclError:
                pass

        try:
            self.root.after(0, update)
        except tk.TclError:
            pass

    def build_psd_from_nodes(
        self,
        root_nodes,
        render_width,
        render_height,
        cancel_event,
        temp_dir,
    ):
        psd = PSDImage.new(
            mode="RGBA",
            size=(
                render_width,
                render_height,
            ),
            color=0,
        )

        render_jobs = []

        def collect_paths(node):
            if cancel_event.is_set():
                raise RuntimeError(
                    "Operation cancelled."
                )

            if node.is_path:
                if node.visible:
                    render_jobs.append(node)
                return

            for child in node.children:
                collect_paths(child)

        for node in root_nodes:
            collect_paths(node)

        total_paths = len(render_jobs)

        self.set_path_progress(
            0,
            total_paths,
        )

        def render_one_path(node):
            if cancel_event.is_set():
                raise RuntimeError(
                    "Operation cancelled."
                )

            render_root = self.project.prepare_render_svg(
                selected_path=node
            )

            path_index = node.path_index

            png_path = os.path.join(
                temp_dir,
                f"path_{path_index}.png",
            )

            svg_name = f"path_{path_index}.svg"

            self.renderer.render_svg_root(
                render_root,
                png_path,
                width=render_width,
                height=render_height,
                cancel_event=cancel_event,
                working_dir=temp_dir,
                temp_svg_name=svg_name,
            )

            if cancel_event.is_set():
                raise RuntimeError(
                    "Operation cancelled."
                )

            return path_index, png_path

        rendered_paths = {}

        worker_count = min(
            EXPORT_WORKERS,
            len(render_jobs),
        )

        if worker_count > 0:
            executor = ThreadPoolExecutor(
                max_workers=worker_count,
                thread_name_prefix="InkscapeRender",
            )

            futures = []

            try:
                futures = [
                    executor.submit(
                        render_one_path,
                        node,
                    )
                    for node in render_jobs
                ]

                for future in as_completed(futures):
                    if cancel_event.is_set():
                        for pending in futures:
                            pending.cancel()

                        raise RuntimeError(
                            "Operation cancelled."
                        )

                    path_index, png_path = future.result()

                    rendered_paths[path_index] = png_path

                    self.set_path_progress(
                        len(rendered_paths),
                        total_paths,
                    )

            except Exception:
                for pending in futures:
                    pending.cancel()
                raise

            finally:
                executor.shutdown(wait=True)

        def process_node(node, parent_psd):
            if cancel_event.is_set():
                raise RuntimeError(
                    "Operation cancelled."
                )

            if node.is_group:
                psd_group = add_psd_group(
                    parent_psd,
                    node.name,
                )

                for child in node.children:
                    process_node(
                        child,
                        psd_group,
                    )

            elif node.is_path:
                if not node.visible:
                    return

                png_path = rendered_paths.get(
                    node.path_index
                )

                if png_path is None:
                    raise RuntimeError(
                        f"Missing rendered PNG for "
                        f"path {node.path_index + 1}."
                    )

                with Image.open(png_path) as source:
                    image = source.convert("RGBA")

                add_pixel_layer(
                    parent_psd,
                    image,
                    node.name,
                )

        for node in root_nodes:
            process_node(node, psd)

        return psd

    def export_psd(self):
        if self.project.svg_root is None:
            messagebox.showwarning(
                "No SVG",
                "Import an SVG first.",
            )
            return

        try:
            width, height = self.parse_output_size()
        except ValueError as exc:
            messagebox.showerror(
                "Invalid output size",
                str(exc),
            )
            return

        filename = filedialog.asksaveasfilename(
            title="Export PSD",
            defaultextension=".psd",
            filetypes=[
                (
                    "Photoshop PSD",
                    "*.psd",
                )
            ],
        )

        if not filename:
            return

        self.project.output_width = width
        self.project.output_height = height

        self.cancel_event.clear()

        self.export_button.configure(
            state="disabled"
        )

        self.cancel_button.configure(
            state="normal"
        )

        self.status_var.set(
            "Exporting PSD..."
        )

        self.export_thread = threading.Thread(
            target=self.export_worker,
            args=(
                filename,
                width,
                height,
            ),
            daemon=True,
        )

        self.export_thread.start()

    def export_worker(
        self,
        filename,
        width,
        height,
    ):
        temp_dir = tempfile.mkdtemp(
            prefix="cubism_export_"
        )

        try:
            if self.cancel_event.is_set():
                raise RuntimeError(
                    "Operation cancelled."
                )

            root_children = self.project.tree_root.children

            psd = self.build_psd_from_nodes(
                root_children,
                width,
                height,
                self.cancel_event,
                temp_dir,
            )

            if self.cancel_event.is_set():
                raise RuntimeError(
                    "Operation cancelled."
                )

            psd.save(filename)

            self.root.after(
                0,
                lambda: self.export_finished(filename),
            )

        except Exception as exc:
            self.root.after(
                0,
                lambda error=exc: self.export_failed(error),
            )

        finally:
            shutil.rmtree(
                temp_dir,
                ignore_errors=True,
            )

    def export_finished(self, filename):
        self.export_button.configure(
            state="normal"
        )

        self.cancel_button.configure(
            state="disabled"
        )

        self.status_var.set(
            "PSD exported successfully."
        )

        messagebox.showinfo(
            "Export complete",
            f"PSD exported successfully:\n\n{filename}",
        )

    def export_failed(self, error):
        self.export_button.configure(
            state="normal"
        )

        self.cancel_button.configure(
            state="disabled"
        )

        if str(error) == "Operation cancelled.":
            self.status_var.set(
                "Export cancelled."
            )
            return

        self.status_var.set(
            "Export failed."
        )

        messagebox.showerror(
            "Export failed",
            str(error),
        )

    def cancel_export(self):
        if (
            self.export_thread
            and self.export_thread.is_alive()
        ):
            self.cancel_event.set()

            self.status_var.set(
                "Cancelling..."
            )


def main():
    if find_inkscape_startup() == False:
        messagebox.showinfo(
            "MESSAGE! MESSAGE! INCOMING!",
            f"Hey buddy. just letting you know you need to have installed inkscape before using this!",
        )

    root = tk.Tk()
    app = CubismPrepApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()