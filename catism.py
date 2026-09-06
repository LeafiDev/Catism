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
import json
import urllib.request
import webbrowser

from PIL import Image, ImageTk, ImageEnhance
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
    "checker_a": "#E8E8E8",
    "checker_b": "#F7F7F7",
}

EXPORT_WORKERS = 4
APP_VERSION = "1.1"
UPDATE_REPO = "LeafiDev/Catism"
GRAPHICAL_TAGS = {"path", "rect", "circle", "ellipse", "line", "polyline", "polygon", "image", "text", "use"}
NON_LAYER_TAGS = {"defs", "metadata", "title", "desc", "namedview", "linearGradient", "radialGradient", "stop", "clipPath", "mask", "filter", "pattern", "marker", "symbol"}
PRESENTATION_ATTRS = {
    "style", "fill", "fill-opacity", "stroke", "stroke-width", "stroke-opacity",
    "stroke-linecap", "stroke-linejoin", "stroke-miterlimit", "stroke-dasharray",
    "stroke-dashoffset", "opacity", "fill-rule", "clip-rule", "color", "display",
    "visibility", "transform", "vector-effect", "shape-rendering", "paint-order"
}


def local_name(tag):
    return tag.rsplit("}", 1)[-1] if isinstance(tag, str) else ""


def get_attr(element, name):
    value = element.get(name)
    if value is not None:
        return value
    for key, value in element.attrib.items():
        if local_name(key) == name:
            return value
    return None


def get_label(element):
    return get_attr(element, "label") or get_attr(element, "id")


def is_graphical(element):
    return local_name(element.tag) in GRAPHICAL_TAGS


def set_hidden(element):
    style = element.get("style", "")
    parts = []
    for item in style.split(";"):
        item = item.strip()
        if item and not item.startswith("display:"):
            parts.append(item)
    parts.append("display:none")
    element.set("style", ";".join(parts))


def set_hit_style(element, color):
    style = element.get("style", "")
    kept = []
    for item in style.split(";"):
        item = item.strip()
        if not item:
            continue
        key = item.split(":", 1)[0].strip().lower()
        if key not in {"fill", "fill-opacity", "stroke", "stroke-opacity", "opacity", "display", "visibility"}:
            kept.append(item)
    kept.extend([
        f"fill:{color}",
        "fill-opacity:1",
        f"stroke:{color}",
        "stroke-opacity:1",
        "opacity:1",
        "visibility:visible",
    ])
    element.set("style", ";".join(kept))


def write_xml(root, filename):
    tree = ET.ElementTree(root)
    try:
        ET.indent(tree, space="  ")
    except AttributeError:
        pass
    tree.write(filename, encoding="utf-8", xml_declaration=True)


def parse_viewbox(root):
    value = root.get("viewBox")
    if not value:
        return None
    try:
        values = [float(x) for x in value.replace(",", " ").split()]
        return tuple(values) if len(values) == 4 else None
    except ValueError:
        return None


class LayerNode:
    def __init__(self, name, node_type, parent=None, xml_element=None, path_index=None):
        self.name = name
        self.node_type = node_type
        self.parent = parent
        self.children = []
        self.xml_element = xml_element
        self.path_index = path_index
        self.visible = True
        self.owned_paths = []
        self.hit_color = None
        if parent is not None:
            parent.children.append(self)

    @property
    def is_group(self):
        return self.node_type in {"group", "stray_group"}

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
        self.path_owner = {}
        self.node_list = []

    def load(self, filename):
        self.filename = filename
        tree = ET.parse(filename)
        self.svg_root = tree.getroot()
        self.native_width = self._dimension(self.svg_root.get("width"))
        self.native_height = self._dimension(self.svg_root.get("height"))
        self.viewbox = parse_viewbox(self.svg_root)
        self._index_paths()
        self._build_layer_tree()
        if self.native_width and self.native_height:
            self.output_width = max(1, int(round(self.native_width)))
            self.output_height = max(1, int(round(self.native_height)))
        elif self.viewbox:
            self.output_width = max(1, int(round(self.viewbox[2])))
            self.output_height = max(1, int(round(self.viewbox[3])))

    @staticmethod
    def _dimension(value):
        if not value:
            return None
        text = value.strip()
        number = ""
        for char in text:
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

    def _group_is_wrapper(self, element, depth):
        label = get_label(element)
        children = list(element)
        graphical = [x for x in children if is_graphical(x)]
        groups = [x for x in children if local_name(x.tag) == "g"]
        nonpresentation = [local_name(k) for k in element.attrib if local_name(k) not in PRESENTATION_ATTRS]
        if label:
            return False
        if depth <= 1 and len(children) == 1 and local_name(children[0].tag) == "g":
            return True
        if nonpresentation:
            return False
        if len(graphical) == 0 and len(groups) == 1:
            return True
        if len(groups) > 0 and len(graphical) > 0 and not label and not nonpresentation:
            return True
        if len(graphical) == 1 and len(groups) == 0:
            return True
        return False

    def _build_layer_tree(self):
        self.tree_root = LayerNode("SVG", "root")
        self.path_owner = {}
        self.node_list = []
        stray_counter = [0]

        def make_stray_group(parent, element, stray_number):
            index = self.svg_path_index.get(id(element))
            if index is None:
                return
            node = LayerNode(f"Stray Path {stray_number}", "stray_group", parent, element)
            node.owned_paths.append(index)
            self.node_list.append(node)
            self.path_owner[index] = node

        def scan(element, semantic_parent, depth=0):
            for child in list(element):
                tag = local_name(child.tag)
                if tag in NON_LAYER_TAGS:
                    continue
                if tag == "g":
                    if self._group_is_wrapper(child, depth):
                        scan(child, semantic_parent, depth + 1)
                        continue
                    name = get_label(child) or f"Group {len(self.all_groups()) + 1}"
                    node = LayerNode(name, "group", semantic_parent, child)
                    self.node_list.append(node)
                    scan(child, node, depth + 1)
                elif tag == "path":
                    index = self.svg_path_index.get(id(child))
                    if index is None:
                        continue
                    if semantic_parent.is_group:
                        semantic_parent.owned_paths.append(index)
                        self.path_owner[index] = semantic_parent
                    else:
                        stray_counter[0] += 1
                        make_stray_group(self.tree_root, child, stray_counter[0])
                elif is_graphical(child):
                    continue
                else:
                    scan(child, semantic_parent, depth)

        scan(self.svg_root, self.tree_root, 0)
        self._remove_empty_groups()
        self._assign_hit_colors()

    def _remove_empty_groups(self):
        changed = True
        while changed:
            changed = False
            def walk(node):
                nonlocal changed
                for child in list(node.children):
                    walk(child)
                    if child.is_group and not child.children and not child.owned_paths:
                        node.children.remove(child)
                        changed = True
            walk(self.tree_root)

    def _assign_hit_colors(self):
        palette = []
        for i in range(1, 250):
            r = (i * 53) % 251
            g = (i * 97) % 251
            b = (i * 149) % 251
            if (r, g, b) not in {(0, 0, 0), (255, 255, 255)}:
                palette.append((r, g, b))
        for index, node in enumerate(self.layerable_nodes()):
            node.hit_color = palette[index % len(palette)]

    def layerable_nodes(self):
        result = []
        def walk(node):
            for child in node.children:
                if child.is_group:
                    result.append(child)
                    walk(child)
                elif child.is_path:
                    result.append(child)
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

    def all_path_nodes(self):
        result = []
        def walk(node):
            for child in node.children:
                if child.is_path:
                    result.append(child)
                elif child.is_group:
                    walk(child)
        walk(self.tree_root)
        return result

    def set_visibility_recursive(self, node, visible):
        node.visible = visible
        for child in node.children:
            self.set_visibility_recursive(child, visible)

    def _copy_paths(self, root):
        return [x for x in root.iter() if local_name(x.tag) == "path"]

    def prepare_svg_for_paths(self, selected_indices=None, visible_only=True):
        root = copy.deepcopy(self.svg_root)
        copied = self._copy_paths(root)
        if len(copied) != len(self.svg_path_elements):
            raise RuntimeError("The copied SVG has a different number of paths.")
        allowed = set(selected_indices) if selected_indices is not None else None
        visible = set()
        for node in self.all_groups():
            if node.visible:
                visible.update(node.owned_paths)
        for node in self.all_path_nodes():
            if node.visible and node.path_index is not None:
                visible.add(node.path_index)
        for index, element in enumerate(copied):
            if allowed is not None:
                if index not in allowed:
                    set_hidden(element)
            elif visible_only and index not in visible:
                set_hidden(element)
        root.set("preserveAspectRatio", "xMidYMid meet")
        return root

    def paths_for_node(self, node):
        if node.is_path:
            return [node.path_index]
        return list(node.owned_paths)

    def prepare_svg_for_node(self, node):
        paths = self.paths_for_node(node)
        indices = set(paths)
        return self.prepare_svg_for_paths(indices, visible_only=False)

    def prepare_hit_svg(self, selected_node=None):
        root = copy.deepcopy(self.svg_root)
        copied_paths = self._copy_paths(root)
        path_to_node = {}
        for node in self.all_groups():
            for index in self.paths_for_node(node):
                path_to_node[index] = node
        for node in self.all_path_nodes():
            path_to_node[node.path_index] = node
        allowed = None if selected_node is None else set(self.paths_for_node(selected_node))
        for index, element in enumerate(copied_paths):
            node = path_to_node.get(index)
            if node is None or not node.visible or (allowed is not None and index not in allowed):
                set_hidden(element)
            else:
                color = "#%02x%02x%02x" % node.hit_color
                set_hit_style(element, color)
        root.set("preserveAspectRatio", "xMidYMid meet")
        return root

    def prepare_full_preview(self):
        return self.prepare_svg_for_paths(None, visible_only=True)


class InkscapeRenderer:
    def __init__(self):
        self.exe = self.find_inkscape()

    @staticmethod
    def find_inkscape():
        candidates = [
            os.environ.get("INKSCAPE_PATH"),
            r"C:\Program Files\Inkscape\bin\inkscape.exe",
            r"C:\Program Files\Inkscape\inkscape.exe",
            r"C:\Program Files (x86)\Inkscape\bin\inkscape.exe",
            r"C:\Program Files (x86)\Inkscape\inkscape.exe",
            os.path.expandvars(r"%LOCALAPPDATA%\Programs\Inkscape\bin\inkscape.exe"),
            os.path.expandvars(r"%LOCALAPPDATA%\Programs\Inkscape\inkscape.exe"),
            shutil.which("inkscape"),
        ]
        for candidate in candidates:
            if candidate and os.path.isfile(candidate):
                return candidate
        return None

    def require(self):
        if not self.exe:
            raise RuntimeError("Inkscape could not be found. Install Inkscape or set INKSCAPE_PATH to inkscape.exe.")

    def render(self, root, output_png, width, height, cancel_event=None, working_dir=None, temp_svg_name="render.svg"):
        self.require()
        own = working_dir is None
        temp_dir = working_dir or tempfile.mkdtemp(prefix="catism_render_")
        try:
            os.makedirs(temp_dir, exist_ok=True)
            svg_path = os.path.join(temp_dir, temp_svg_name)
            write_xml(root, svg_path)
            command = [
                self.exe, svg_path, "--export-type=png",
                f"--export-filename={output_png}",
                f"--export-width={int(width)}",
                f"--export-height={int(height)}",
                "--export-background-opacity=0",
                "--export-overwrite",
            ]
            process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, encoding="utf-8", errors="replace")
            while process.poll() is None:
                if cancel_event is not None and cancel_event.is_set():
                    process.kill()
                    process.wait()
                    raise RuntimeError("Operation cancelled.")
                threading.Event().wait(0.05)
            stdout, stderr = process.communicate()
            if process.returncode != 0:
                raise RuntimeError("Inkscape rendering failed.\n\n" + (stderr.strip() or stdout.strip()))
            if not os.path.isfile(output_png):
                raise RuntimeError("Inkscape completed but did not create the PNG output.")
            return output_png
        finally:
            if own:
                shutil.rmtree(temp_dir, ignore_errors=True)

    def render_batch(self, requests, cancel_event=None, working_dir=None):
        self.require()
        if not requests:
            return []
        own = working_dir is None
        temp_dir = working_dir or tempfile.mkdtemp(prefix="catism_render_batch_")
        try:
            os.makedirs(temp_dir, exist_ok=True)
            outputs = []
            for index, request in enumerate(requests):
                if cancel_event is not None and cancel_event.is_set():
                    raise RuntimeError("Operation cancelled.")
                root, output_png, width, height, temp_svg_name = request
                svg_path = os.path.join(temp_dir, temp_svg_name or f"render_{index}.svg")
                write_xml(root, svg_path)
                command = [
                    self.exe,
                    svg_path,
                    "--export-type=png",
                    f"--export-filename={output_png}",
                    f"--export-width={int(width)}",
                    f"--export-height={int(height)}",
                    "--export-background-opacity=0",
                    "--export-overwrite",
                ]
                process = subprocess.Popen(
                    command,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    encoding="utf-8",
                    errors="replace",
                )
                while process.poll() is None:
                    if cancel_event is not None and cancel_event.is_set():
                        process.kill()
                        process.wait()
                        raise RuntimeError("Operation cancelled.")
                    threading.Event().wait(0.05)
                stdout, stderr = process.communicate()
                if process.returncode != 0:
                    raise RuntimeError(
                        "Inkscape rendering failed.\n\n"
                        + (stderr.strip() or stdout.strip())
                    )
                if not os.path.isfile(output_png):
                    raise RuntimeError(
                        f"Inkscape completed but did not create the PNG output:\n\n{output_png}"
                    )
                if os.path.getsize(output_png) <= 0:
                    raise RuntimeError(
                        f"Inkscape created an empty PNG:\n\n{output_png}"
                    )
                outputs.append(output_png)
            return outputs
        finally:
            if own:
                shutil.rmtree(temp_dir, ignore_errors=True)


def add_psd_group(parent, name):
    group = Group.new(name=name, parent=parent)
    parent.append(group)
    return group


def add_pixel_layer(parent, image, name, top=0, left=0):
    layer = PixelLayer.frompil(image, parent=parent, name=name, top=top, left=left)
    parent.append(layer)
    return layer


class CubismPrepApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Catism (V1.0)")
        self.root.geometry("820x600")
        self.root.minsize(760, 600)
        self.root.resizable(False, False)
        self.project = SVGProject()
        self.renderer = InkscapeRenderer()
        self.preview_image = None
        self.preview_hit = None
        self.preview_photo = None
        self.hover_node = None
        self.selected_preview_node = None
        self.preview_bounds = None
        self.render_lock = threading.Lock()
        self.cancel_event = threading.Event()
        self.export_thread = None
        self.layer_items = {}
        self.layer_nodes_by_item = {}
        self.svg_title_photo = None
        self.cubism_title_photo = None
        self.width_var = tk.StringVar(value="1000")
        self.height_var = tk.StringVar(value="1000")
        self.link_ratio_var = tk.BooleanVar(value=True)
        self.linked_ratio = 1.0
        self.status_var = tk.StringVar(value="Import an SVG to begin.")
        self.path_progress_var = tk.StringVar(value="0 / 0 paths")
        self.preview_info_var = tk.StringVar(value="Move the mouse over the artwork to identify a layer.")
        self.build_style()
        self.load_title_images()
        self.build_ui()
        self.root.after(1000, self.check_for_updates)

    def load_title_images(self):
        base = os.path.dirname(os.path.abspath(__file__))
        for name, attr in (("svg.png", "svg_title_photo"), ("cubism.png", "cubism_title_photo")):
            try:
                path = os.path.join(base, name)
                if os.path.isfile(path):
                    image = Image.open(path).convert("RGBA")
                    image.thumbnail((26, 26), Image.Resampling.LANCZOS)
                    setattr(self, attr, ImageTk.PhotoImage(image))
            except Exception:
                setattr(self, attr, None)

    def build_style(self):
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except tk.TclError:
            pass
        style.configure(".", font=("Segoe UI", 9))
        style.configure("TFrame", background=THEME["background"])
        style.configure("Panel.TFrame", background=THEME["panel"])
        style.configure("TLabel", background=THEME["background"], foreground=THEME["text"])
        style.configure("Panel.TLabel", background=THEME["panel"], foreground=THEME["text"])
        style.configure("Muted.TLabel", background=THEME["panel"], foreground=THEME["muted"])
        style.configure("TButton", padding=(9, 5), background=THEME["panel"], foreground=THEME["text"], bordercolor=THEME["border"])
        style.map("TButton", background=[("active", THEME["accent_light"])], foreground=[("active", "#FFFFFF")])
        style.configure("Accent.TButton", padding=(11, 5), background=THEME["accent"], foreground="#FFFFFF", bordercolor=THEME["accent"])
        style.map("Accent.TButton", background=[("active", THEME["accent_dark"])])
        style.configure("TNotebook", background=THEME["background"], borderwidth=0)
        style.configure("TNotebook.Tab", padding=(11, 6), background=THEME["background"], foreground=THEME["muted"])
        style.map("TNotebook.Tab", background=[("selected", THEME["accent"])], foreground=[("selected", "#FFFFFF")])
        style.configure("Treeview", background=THEME["panel"], fieldbackground=THEME["panel"], foreground=THEME["text"], rowheight=24, bordercolor=THEME["border"])
        style.map("Treeview", background=[("selected", THEME["selected"])], foreground=[("selected", THEME["text"])])
        style.configure("TEntry", padding=4)

    def check_for_updates(self):
        if not UPDATE_REPO:
            return
        threading.Thread(target=self._update_check_worker, daemon=True).start()

    def _version_key(self, version):
        import re
        parts = re.findall(r"\d+", str(version or ""))
        return tuple(int(x) for x in parts) if parts else (0,)

    def _update_check_worker(self):
        try:
            url = f"https://api.github.com/repos/{UPDATE_REPO}/releases/latest"
            request = urllib.request.Request(
                url,
                headers={
                    "User-Agent": "Catism-Updater",
                    "Accept": "application/vnd.github+json",
                },
            )
            with urllib.request.urlopen(request, timeout=5) as response:
                data = json.loads(response.read().decode("utf-8"))
            latest = str(data.get("tag_name") or data.get("name") or "").lstrip("vV")
            release_url = str(data.get("html_url") or "")
            if not latest or not release_url:
                return
            if self._version_key(latest) <= self._version_key(APP_VERSION):
                return
            self.root.after(0, lambda: self.show_update_alert(latest, release_url))
        except Exception:
            pass

    def show_update_alert(self, latest_version, release_url):
        try:
            answer = messagebox.askyesno(
                "Catism Update Available",
                f"A newer version of Catism is available.\n\n"
                f"Current version: {APP_VERSION}\n"
                f"Latest version: {latest_version}\n\n"
                "Would you like to open the update page?",
            )
            if answer:
                webbrowser.open(release_url)
        except tk.TclError:
            pass

    def build_ui(self):
        outer = ttk.Frame(self.root, padding=8)
        outer.pack(fill="both", expand=True)
        header = ttk.Frame(outer)
        header.pack(fill="x", pady=(0, 7))
        title = tk.Frame(header, bg=THEME["background"])
        title.pack(side="left")
        if self.svg_title_photo:
            tk.Label(title, image=self.svg_title_photo, bg=THEME["background"], bd=0).pack(side="left", padx=(0, 4))
        tk.Label(title, text="SVG", font=("Segoe UI Semibold", 13), fg=THEME["accent"], bg=THEME["background"]).pack(side="left")
        tk.Label(title, text=" → ", font=("Segoe UI Semibold", 13), fg=THEME["accent"], bg=THEME["background"]).pack(side="left")
        if self.cubism_title_photo:
            tk.Label(title, image=self.cubism_title_photo, bg=THEME["background"], bd=0).pack(side="left", padx=(0, 4))
        tk.Label(title, text="Cubism", font=("Segoe UI Semibold", 13), fg=THEME["accent"], bg=THEME["background"]).pack(side="left")
        ttk.Label(header, textvariable=self.path_progress_var).pack(side="right", padx=(0, 7))
        ttk.Button(header, text="Import SVG", style="Accent.TButton", command=self.import_svg).pack(side="right")
        self.notebook = ttk.Notebook(outer)
        self.notebook.pack(fill="both", expand=True)
        self.build_import_tab()
        self.build_layers_tab()
        self.build_export_tab()
        status = ttk.Frame(outer)
        status.pack(fill="x", pady=(5, 0))
        ttk.Label(status, textvariable=self.status_var, foreground=THEME["muted"]).pack(side="left")

    def build_import_tab(self):
        tab = ttk.Frame(self.notebook, padding=8)
        self.notebook.add(tab, text="Import")
        panel = ttk.Frame(tab, style="Panel.TFrame", padding=14)
        panel.pack(fill="both", expand=True)
        self.file_label = ttk.Label(panel, text="No SVG loaded", style="Panel.TLabel", font=("Segoe UI Semibold", 10))
        self.file_label.pack(anchor="w")
        self.svg_info_label = ttk.Label(panel, text="", style="Muted.TLabel")
        self.svg_info_label.pack(anchor="w", pady=(3, 12))
        ttk.Label(panel, text="Import an SVG and Catism will build a layer hierarchy while preserving transparency and the original canvas proportions.", style="Panel.TLabel", wraplength=680, justify="left").pack(anchor="w")

    def build_layers_tab(self):
        self.layers_tab = ttk.Frame(self.notebook, padding=7)
        self.notebook.add(self.layers_tab, text="Layers")
        self.layers_tab.columnconfigure(0, weight=5)
        self.layers_tab.columnconfigure(1, weight=4)
        self.layers_tab.rowconfigure(1, weight=1)

        left_header = ttk.Frame(self.layers_tab, style="Panel.TFrame", padding=(10, 7))
        left_header.grid(row=0, column=0, sticky="ew", padx=(0, 4))
        ttk.Label(left_header, text="LAYERS", style="Panel.TLabel", font=("Segoe UI Semibold", 9)).pack(side="left")

        right_header = ttk.Frame(self.layers_tab, style="Panel.TFrame", padding=(10, 7))
        right_header.grid(row=0, column=1, sticky="ew", padx=(4, 0))
        ttk.Label(right_header, text="PREVIEW", style="Panel.TLabel", font=("Segoe UI Semibold", 9)).pack(side="left")

        tree_frame = ttk.Frame(self.layers_tab, style="Panel.TFrame")
        tree_frame.grid(row=1, column=0, sticky="nsew", padx=(0, 4), pady=(4, 0))
        tree_frame.rowconfigure(0, weight=1)
        tree_frame.columnconfigure(0, weight=1)
        self.layer_tree = ttk.Treeview(tree_frame, show="tree", selectmode="browse")
        self.layer_tree.grid(row=0, column=0, sticky="nsew")
        scrollbar = ttk.Scrollbar(tree_frame, orient="vertical", command=self.layer_tree.yview)
        scrollbar.grid(row=0, column=1, sticky="ns")
        self.layer_tree.configure(yscrollcommand=scrollbar.set)
        self.layer_tree.bind("<<TreeviewSelect>>", self.on_tree_select)
        self.layer_tree.bind("<Double-1>", self.rename_selected_layer)
        self.layer_tree.bind("<space>", self.toggle_selected_visibility)

        preview_panel = ttk.Frame(self.layers_tab, style="Panel.TFrame")
        preview_panel.grid(row=1, column=1, sticky="nsew", padx=(4, 0), pady=(4, 0))
        preview_panel.rowconfigure(0, weight=1)
        preview_panel.columnconfigure(0, weight=1)
        self.preview_canvas = tk.Canvas(preview_panel, highlightthickness=1, highlightbackground=THEME["border"], bd=0)
        self.preview_canvas.grid(row=0, column=0, sticky="nsew", padx=8, pady=(8, 5))
        self.preview_canvas.bind("<Configure>", lambda e: self.redraw_preview())
        self.preview_canvas.bind("<Motion>", self.on_preview_motion)
        self.preview_canvas.bind("<Leave>", self.on_preview_leave)
        self.preview_canvas.bind("<Button-1>", self.on_preview_click)
        self.preview_info = ttk.Label(preview_panel, textvariable=self.preview_info_var, style="Muted.TLabel", anchor="center")
        self.preview_info.grid(row=1, column=0, sticky="ew", padx=8, pady=(0, 8))

        controls = ttk.Frame(self.layers_tab)
        controls.grid(row=2, column=0, columnspan=2, sticky="ew", pady=(6, 0))
        ttk.Button(controls, text="Rename", command=self.rename_selected_layer).pack(side="left")
        ttk.Button(controls, text="Visibility", command=self.toggle_selected_visibility).pack(side="left", padx=(4, 0))
        ttk.Button(controls, text="Expand All", command=lambda: self.expand_all(True)).pack(side="right")
        ttk.Button(controls, text="Collapse All", command=lambda: self.expand_all(False)).pack(side="right", padx=(0, 4))

    def build_export_tab(self):
        self.export_tab = ttk.Frame(self.notebook, padding=8)
        self.notebook.add(self.export_tab, text="Export")
        panel = ttk.Frame(self.export_tab, style="Panel.TFrame", padding=10)
        panel.pack(fill="both", expand=True)
        row = ttk.Frame(panel, style="Panel.TFrame")
        row.pack(fill="x")
        ttk.Label(row, text="Output size", style="Panel.TLabel", font=("Segoe UI Semibold", 10)).pack(side="left", padx=(0, 12))
        ttk.Label(row, text="W", style="Panel.TLabel").pack(side="left")
        self.width_entry = ttk.Entry(row, textvariable=self.width_var, width=8)
        self.width_entry.pack(side="left", padx=(4, 8))
        ttk.Label(row, text="H", style="Panel.TLabel").pack(side="left")
        self.height_entry = ttk.Entry(row, textvariable=self.height_var, width=8)
        self.height_entry.pack(side="left", padx=(4, 8))
        ttk.Checkbutton(row, text="Link", variable=self.link_ratio_var, command=self.on_ratio_toggle).pack(side="left")
        self.width_entry.bind("<KeyRelease>", self.on_width_changed)
        self.height_entry.bind("<KeyRelease>", self.on_height_changed)
        ttk.Label(panel, text="Full artwork preview", style="Panel.TLabel", font=("Segoe UI Semibold", 10)).pack(anchor="w", pady=(10, 4))
        frame = ttk.Frame(panel, style="Panel.TFrame")
        frame.pack(fill="both", expand=True)
        self.export_preview_canvas = tk.Canvas(frame, background="#E7E7E7", highlightthickness=1, highlightbackground=THEME["border"])
        self.export_preview_canvas.pack(fill="both", expand=True)
        self.export_preview_canvas.bind("<Configure>", lambda e: self.redraw_export_preview())
        bottom = ttk.Frame(panel, style="Panel.TFrame")
        bottom.pack(fill="x", pady=(6, 0))
        self.export_button = ttk.Button(bottom, text="Export PSD", style="Accent.TButton", command=self.export_psd)
        self.export_button.pack(side="left")
        self.cancel_button = ttk.Button(bottom, text="Cancel", command=self.cancel_export, state="disabled")
        self.cancel_button.pack(side="left", padx=(4, 0))

    def import_svg(self):
        filename = filedialog.askopenfilename(title="Import SVG", filetypes=[("SVG files", "*.svg"), ("All files", "*.*")])
        if not filename:
            return
        try:
            self.project.load(filename)
            w, h = self.project.output_width, self.project.output_height
            self.width_var.set(str(w))
            self.height_var.set(str(h))
            self.linked_ratio = w / h if h else 1
            self.file_label.configure(text=os.path.basename(filename))
            info = []
            if self.project.native_width and self.project.native_height:
                info.append(f"Native: {self.project.native_width:g} × {self.project.native_height:g}")
            if self.project.viewbox:
                info.append(f"ViewBox: {self.project.viewbox[2]:g} × {self.project.viewbox[3]:g}")
            info.append(f"Paths: {len(self.project.svg_path_elements)}")
            info.append(f"Layers: {len(self.project.layerable_nodes())}")
            self.svg_info_label.configure(text="    ".join(info))
            self.path_progress_var.set(f"0 / {len(self.project.svg_path_elements)} paths")
            self.populate_layer_tree()
            self.notebook.select(self.layers_tab)
            self.status_var.set("SVG imported successfully.")
            self.refresh_preview()
            self.refresh_export_preview()
        except Exception as exc:
            messagebox.showerror("Import failed", str(exc))

    def populate_layer_tree(self):
        for item in self.layer_tree.get_children():
            self.layer_tree.delete(item)
        self.layer_items.clear()
        self.layer_nodes_by_item.clear()
        root = self.project.tree_root
        if root is None:
            return
        def add(node, parent=""):
            text = node.name if node is root else ("● " if node.visible else "○ ") + node.name
            item = self.layer_tree.insert(parent, "end", text=text, open=node.is_group or node is root)
            self.layer_items[id(node)] = item
            self.layer_nodes_by_item[item] = node
            for child in node.children:
                add(child, item)
        add(root)

    def selected_node(self):
        selection = self.layer_tree.selection()
        return self.layer_nodes_by_item.get(selection[0]) if selection else None

    def on_tree_select(self, event=None):
        node = self.selected_node()
        if node is None or node is self.project.tree_root:
            self.selected_preview_node = None
            self.preview_info_var.set("Move the mouse over the artwork to identify a layer.")
            self.refresh_preview()
            return
        self.selected_preview_node = node
        self.preview_info_var.set(f"Selected: {node.name}")
        self.refresh_preview()

    def refresh_tree_text(self, node):
        item = self.layer_items.get(id(node))
        if item:
            self.layer_tree.item(item, text=("● " if node.visible else "○ ") + node.name)

    def rename_selected_layer(self, event=None):
        node = self.selected_node()
        if node is None or node is self.project.tree_root:
            return
        item = self.layer_items.get(id(node))
        if not item:
            return
        bbox = self.layer_tree.bbox(item, "#0")
        if not bbox:
            return
        x, y, w, h = bbox
        entry = tk.Entry(self.layer_tree, bd=0, highlightthickness=1, highlightcolor=THEME["accent"])
        entry.place(x=x, y=y, width=w, height=h)
        entry.insert(0, node.name)
        entry.select_range(0, "end")
        entry.focus_set()
        def finish(event=None):
            name = entry.get().strip()
            if name:
                node.name = name
                self.refresh_tree_text(node)
                if self.hover_node is node:
                    self.preview_info_var.set(name)
            entry.destroy()
        entry.bind("<Return>", finish)
        entry.bind("<Escape>", lambda e: entry.destroy())
        entry.bind("<FocusOut>", finish)

    def toggle_selected_visibility(self, event=None):
        node = self.selected_node()
        if node is None or node is self.project.tree_root:
            return
        self.project.set_visibility_recursive(node, not node.visible)
        def refresh(n):
            self.refresh_tree_text(n)
            for child in n.children:
                refresh(child)
        refresh(node)
        self.refresh_preview()
        self.refresh_export_preview()

    def expand_all(self, expand):
        def walk(item):
            self.layer_tree.item(item, open=expand)
            for child in self.layer_tree.get_children(item):
                walk(child)
        for item in self.layer_tree.get_children():
            walk(item)

    def parse_output_size(self):
        try:
            w = int(float(self.width_var.get()))
            h = int(float(self.height_var.get()))
        except ValueError:
            raise ValueError("Width and height must be valid numbers.")
        if w <= 0 or h <= 0:
            raise ValueError("Width and height must be greater than zero.")
        return w, h

    def on_ratio_toggle(self):
        if not self.link_ratio_var.get():
            return
        try:
            w, h = float(self.width_var.get()), float(self.height_var.get())
            if w > 0 and h > 0:
                self.linked_ratio = w / h
        except ValueError:
            pass

    def on_width_changed(self, event=None):
        if not self.link_ratio_var.get():
            return
        try:
            w = float(self.width_var.get())
            if w > 0 and self.linked_ratio > 0:
                self.height_var.set(str(max(1, round(w / self.linked_ratio))))
        except ValueError:
            pass

    def on_height_changed(self, event=None):
        if not self.link_ratio_var.get():
            return
        try:
            h = float(self.height_var.get())
            if h > 0 and self.linked_ratio > 0:
                self.width_var.set(str(max(1, round(h * self.linked_ratio))))
        except ValueError:
            pass

    def checkerboard(self, size):
        w, h = size
        image = Image.new("RGBA", (w, h), THEME["checker_a"])
        pixels = image.load()
        step = 12
        a = tuple(int(THEME["checker_a"][i:i+2], 16) for i in (1, 3, 5))
        b = tuple(int(THEME["checker_b"][i:i+2], 16) for i in (1, 3, 5))
        for y in range(0, h, step):
            for x in range(0, w, step):
                c = a if ((x // step) + (y // step)) % 2 == 0 else b
                for yy in range(y, min(y + step, h)):
                    for xx in range(x, min(x + step, w)):
                        pixels[xx, yy] = (*c, 255)
        return image

    def preview_render_size(self, max_w=700, max_h=700):
        w = float(self.project.output_width or 0)
        h = float(self.project.output_height or 0)
        if w <= 0 or h <= 0:
            if self.project.viewbox:
                w = abs(float(self.project.viewbox[2]))
                h = abs(float(self.project.viewbox[3]))
        if w <= 0 or h <= 0:
            return max_w, max_h
        aspect = w / h
        if aspect >= 1:
            render_w = max_w
            render_h = max(1, round(render_w / aspect))
            if render_h > max_h:
                render_h = max_h
                render_w = max(1, round(render_h * aspect))
        else:
            render_h = max_h
            render_w = max(1, round(render_h * aspect))
            if render_w > max_w:
                render_w = max_w
                render_h = max(1, round(render_w / aspect))
        return render_w, render_h

    def render_preview_root(self, root, size=None):
        if size is None:
            size = self.preview_render_size()
        temp = tempfile.mkdtemp(prefix="catism_preview_")
        try:
            path = os.path.join(temp, "preview.png")
            self.renderer.render(root, path, size[0], size[1])
            return Image.open(path).convert("RGBA")
        finally:
            shutil.rmtree(temp, ignore_errors=True)

    def refresh_preview(self):
        if self.project.svg_root is None:
            return
        temp = tempfile.mkdtemp(prefix="catism_preview_pair_")
        try:
            node = self.selected_preview_node
            root = self.project.prepare_full_preview() if node is None else self.project.prepare_svg_for_node(node)
            hit_root = self.project.prepare_hit_svg(node)
            size = self.preview_render_size()
            image_path = os.path.join(temp, "preview.png")
            hit_path = os.path.join(temp, "hit.png")
            outputs = self.renderer.render_batch(
                [
                    (root, image_path, size[0], size[1], "preview.svg"),
                    (hit_root, hit_path, size[0], size[1], "hit.svg"),
                ],
                working_dir=temp,
            )
            with Image.open(outputs[0]) as image:
                self.preview_image = image.convert("RGBA")
            with Image.open(outputs[1]) as image:
                self.preview_hit = image.convert("RGBA")
            self.redraw_preview()
        except Exception as exc:
            self.status_var.set(f"Preview error: {exc}")
        finally:
            shutil.rmtree(temp, ignore_errors=True)

    def refresh_export_preview(self):
        if self.project.svg_root is None:
            return
        try:
            image = self.render_preview_root(self.project.prepare_full_preview())
            self.export_preview_image = image
            self.redraw_export_preview()
        except Exception:
            pass

    def display_geometry(self, image, canvas):
        cw, ch = canvas.winfo_width(), canvas.winfo_height()
        iw, ih = image.size
        if cw <= 2 or ch <= 2 or iw <= 0 or ih <= 0:
            return None
        scale = min(cw / iw, ch / ih)
        dw, dh = max(1, round(iw * scale)), max(1, round(ih * scale))
        x0 = (cw - dw) // 2
        y0 = (ch - dh) // 2
        return x0, y0, dw, dh

    def composite_for_display(self, image, hit=False):
        geom = self.display_geometry(image, self.preview_canvas)
        if geom is None:
            return None
        x0, y0, dw, dh = geom
        resized = image.resize((dw, dh), Image.Resampling.LANCZOS)
        if hit:
            return resized
        base = self.checkerboard((dw, dh))
        base.alpha_composite(resized)
        if self.hover_node is not None:
            overlay = Image.new("RGBA", (dw, dh), (0, 0, 0, 0))
            source = self.preview_hit.resize((dw, dh), Image.Resampling.NEAREST)
            target = self.hover_node.hit_color
            sp = source.load()
            op = overlay.load()
            for y in range(dh):
                for x in range(dw):
                    r, g, b, a = sp[x, y]
                    if abs(r-target[0]) <= 8 and abs(g-target[1]) <= 8 and abs(b-target[2]) <= 8:
                        op[x, y] = (244, 123, 32, 90)
                    else:
                        op[x, y] = (0, 0, 0, 38)
            base.alpha_composite(overlay)
        return base

    def redraw_preview(self):
        if self.preview_image is None:
            self.preview_canvas.delete("all")
            return
        geom = self.display_geometry(self.preview_image, self.preview_canvas)
        if geom is None:
            return
        x0, y0, dw, dh = geom
        display = self.composite_for_display(self.preview_image)
        self.preview_photo = ImageTk.PhotoImage(display)
        self.preview_canvas.delete("all")
        self.preview_canvas.create_image(x0, y0, image=self.preview_photo, anchor="nw")
        self.preview_bounds = geom

    def redraw_export_preview(self):
        image = getattr(self, "export_preview_image", None)
        if image is None:
            return
        geom = self.display_geometry(image, self.export_preview_canvas)
        if geom is None:
            return
        x0, y0, dw, dh = geom
        resized = image.resize((dw, dh), Image.Resampling.LANCZOS)
        base = self.checkerboard((dw, dh))
        base.alpha_composite(resized)
        self.export_preview_photo = ImageTk.PhotoImage(base)
        self.export_preview_canvas.delete("all")
        self.export_preview_canvas.create_image(x0, y0, image=self.export_preview_photo, anchor="nw")

    def node_from_hit(self, x, y):
        if self.preview_hit is None or self.preview_bounds is None:
            return None
        x0, y0, dw, dh = self.preview_bounds
        if not (x0 <= x < x0 + dw and y0 <= y < y0 + dh):
            return None
        px = min(self.preview_hit.width - 1, max(0, int((x - x0) * self.preview_hit.width / dw)))
        py = min(self.preview_hit.height - 1, max(0, int((y - y0) * self.preview_hit.height / dh)))
        pixel = self.preview_hit.getpixel((px, py))[:3]
        best = None
        best_dist = 999999
        for node in self.project.layerable_nodes():
            r, g, b = node.hit_color
            dist = (pixel[0]-r)**2 + (pixel[1]-g)**2 + (pixel[2]-b)**2
            if dist < best_dist:
                best_dist = dist
                best = node
        return best if best_dist < 8000 else None

    def on_preview_motion(self, event):
        node = self.node_from_hit(event.x, event.y)
        if node is not self.hover_node:
            self.hover_node = node
            if node:
                self.preview_info_var.set(f"Hover: {node.name}")
                self.redraw_preview()
            else:
                selected = self.selected_preview_node.name if self.selected_preview_node else "Move the mouse over the artwork to identify a layer."
                self.preview_info_var.set(selected)
                self.redraw_preview()

    def on_preview_leave(self, event):
        self.hover_node = None
        selected = self.selected_preview_node.name if self.selected_preview_node else "Move the mouse over the artwork to identify a layer."
        self.preview_info_var.set(selected)
        self.redraw_preview()

    def on_preview_click(self, event):
        node = self.node_from_hit(event.x, event.y)
        if node is None:
            return
        item = self.layer_items.get(id(node))
        if item:
            self.layer_tree.selection_set(item)
            self.layer_tree.focus(item)
            self.layer_tree.see(item)

    def set_path_progress(self, done, total):
        try:
            self.root.after(0, lambda: self.path_progress_var.set(f"{done} / {total} paths"))
        except tk.TclError:
            pass

    def crop_alpha(self, image):
        image = image.convert("RGBA")
        bbox = image.getchannel("A").getbbox()
        if bbox is None:
            return None, None
        return image.crop(bbox), bbox

    def build_psd(self, width, height, cancel_event, temp_dir):
        psd = PSDImage.new(mode="RGBA", size=(width, height), color=0)
        jobs = []

        def collect(node):
            if not node.visible:
                return
            if node.is_group:
                if node.owned_paths:
                    jobs.append(node)
                for child in node.children:
                    if child.is_group:
                        collect(child)
                    elif child.is_path and child.parent is self.project.tree_root:
                        jobs.append(child)
            elif node.is_path:
                jobs.append(node)

        for node in self.project.tree_root.children:
            collect(node)

        total_paths = sum(len(self.project.paths_for_node(n)) for n in jobs)
        self.set_path_progress(0, total_paths)
        rendered = {}
        requests = []
        request_nodes = []

        for node in jobs:
            indices = self.project.paths_for_node(node)
            if not indices:
                continue
            root = self.project.prepare_svg_for_paths(indices, visible_only=False)
            png = os.path.join(temp_dir, f"layer_{id(node)}.png")
            requests.append((root, png, width, height, f"layer_{id(node)}.svg"))
            request_nodes.append(node)

        outputs = self.renderer.render_batch(requests, cancel_event, temp_dir)
        done = 0
        for node, path in zip(request_nodes, outputs):
            rendered[id(node)] = path
            done += len(self.project.paths_for_node(node))
            self.set_path_progress(done, total_paths)

        def add_node(node, parent):
            if cancel_event.is_set():
                raise RuntimeError("Operation cancelled.")
            if not node.visible:
                return
            if node.is_path:
                if node.parent is not self.project.tree_root:
                    return
                path = rendered.get(id(node))
                if path:
                    with Image.open(path) as src:
                        image = src.convert("RGBA")
                    cropped, bbox = self.crop_alpha(image)
                    if cropped:
                        add_pixel_layer(parent, cropped, node.name, bbox[1], bbox[0])
                return
            child_groups = [child for child in node.children if child.is_group and child.node_type == "group"]
            path = rendered.get(id(node))
            if node.node_type == "stray_group":
                group = add_psd_group(parent, node.name)
                if path:
                    with Image.open(path) as src:
                        image = src.convert("RGBA")
                    cropped, bbox = self.crop_alpha(image)
                    if cropped:
                        add_pixel_layer(group, cropped, "Artwork", bbox[1], bbox[0])
                return
            if not child_groups:
                if path:
                    with Image.open(path) as src:
                        image = src.convert("RGBA")
                    cropped, bbox = self.crop_alpha(image)
                    if cropped:
                        add_pixel_layer(parent, cropped, node.name, bbox[1], bbox[0])
                return
            group = add_psd_group(parent, node.name)
            if path:
                with Image.open(path) as src:
                    image = src.convert("RGBA")
                cropped, bbox = self.crop_alpha(image)
                if cropped:
                    add_pixel_layer(group, cropped, f"{node.name} (Flattened)", bbox[1], bbox[0])
            for child in child_groups:
                add_node(child, group)

        for child in self.project.tree_root.children:
            add_node(child, psd)
        return psd

    def export_psd(self):
        if self.project.svg_root is None:
            messagebox.showwarning("No SVG", "Import an SVG first.")
            return
        try:
            width, height = self.parse_output_size()
        except ValueError as exc:
            messagebox.showerror("Invalid output size", str(exc))
            return
        filename = filedialog.asksaveasfilename(title="Export PSD", defaultextension=".psd", filetypes=[("Photoshop PSD", "*.psd")])
        if not filename:
            return
        self.project.output_width, self.project.output_height = width, height
        self.cancel_event.clear()
        self.export_button.configure(state="disabled")
        self.cancel_button.configure(state="normal")
        self.status_var.set("Exporting PSD...")
        self.export_thread = threading.Thread(target=self.export_worker, args=(filename, width, height), daemon=True)
        self.export_thread.start()

    def export_worker(self, filename, width, height):
        temp_dir = tempfile.mkdtemp(prefix="catism_export_")
        try:
            psd = self.build_psd(width, height, self.cancel_event, temp_dir)
            if self.cancel_event.is_set():
                raise RuntimeError("Operation cancelled.")
            psd.save(filename)
            self.root.after(0, lambda: self.export_finished(filename))
        except Exception as exc:
            self.root.after(0, lambda error=exc: self.export_failed(error))
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

    def export_finished(self, filename):
        self.export_button.configure(state="normal")
        self.cancel_button.configure(state="disabled")
        self.status_var.set("PSD exported successfully.")
        messagebox.showinfo("Export complete", f"PSD exported successfully:\n\n{filename}")

    def export_failed(self, error):
        self.export_button.configure(state="normal")
        self.cancel_button.configure(state="disabled")
        if str(error) == "Operation cancelled.":
            self.status_var.set("Export cancelled.")
            return
        self.status_var.set("Export failed.")
        messagebox.showerror("Export failed", str(error))

    def cancel_export(self):
        if self.export_thread and self.export_thread.is_alive():
            self.cancel_event.set()
            self.status_var.set("Cancelling...")


def main():
    root = tk.Tk()
    CubismPrepApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
