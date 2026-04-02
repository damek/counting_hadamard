from __future__ import annotations

import html
import json
import os
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
BLUEPRINT_ROOT = ROOT / "blueprint"
SRC_DIR = BLUEPRINT_ROOT / "src"
CHAPTER_DIR = SRC_DIR / "chapters"
OUT_DIR = BLUEPRINT_ROOT / "out"
GENERATED_DIR = BLUEPRINT_ROOT / "generated"

CANONICAL_PAPER = ROOT / "documents" / "short.tex"


def html_escape(text: str) -> str:
    return html.escape(text, quote=True)


def read_lines(relpath: str) -> list[str]:
    return (ROOT / relpath).read_text().splitlines()


def excerpt_lines(relpath: str, start: int, end: int) -> str:
    lines = read_lines(relpath)
    return "\n".join(lines[start - 1 : end]).rstrip()


def rel_href(target: Path, page: Path) -> str:
    return os.path.relpath(target, page.parent)


def source_href(relpath: str, page: Path, line: int | None = None) -> str:
    repo_web_base = os.environ.get("BLUEPRINT_REPO_WEB_BASE", "").strip().rstrip("/")
    if repo_web_base:
        suffix = f"#L{line}" if line is not None else ""
        return f"{repo_web_base}/{relpath}{suffix}"
    return rel_href(ROOT / relpath, page)


def source_label(relpath: str, line: int | None = None) -> str:
    return f"{relpath}:{line}" if line is not None else relpath


def render_badges(values: list[str], cls: str = "badge") -> str:
    return "".join(f'<span class="{cls}">{html_escape(v)}</span>' for v in values)


def render_code_block(code: str, language: str) -> str:
    return f'<pre><code class="language-{language}">{html_escape(code)}</code></pre>'


def find_symbol(relpath: str, symbol: str) -> int | None:
    text = (ROOT / relpath).read_text()
    pattern = re.compile(
        rf"(?m)^(?:theorem|lemma|def|abbrev|private theorem|private lemma|private def)\s+{re.escape(symbol)}\b"
    )
    match = pattern.search(text)
    if not match:
        return None
    return text[: match.start()].count("\n") + 1


def extract_lean_statement(relpath: str, line: int) -> str:
    lines = read_lines(relpath)
    start = max(0, line - 1)
    first = lines[start].lstrip()
    is_definition = first.startswith("def ") or first.startswith("abbrev ") or first.startswith("private def ")
    out: list[str] = []
    for idx, raw in enumerate(lines[start : start + 160]):
        stripped = raw.strip()
        if idx > 0 and raw and not raw.startswith((" ", "\t")):
            if re.match(r"^(?:theorem|lemma|def|abbrev|private theorem|private lemma|private def)\b", stripped):
                break
        if is_definition:
            out.append(raw.rstrip())
            if idx > 0 and (stripped == "" or stripped.startswith("/--")):
                out.pop()
                break
        else:
            out.append(raw.rstrip())
            if ":=" in raw:
                out[-1] = raw.split(":=", 1)[0].rstrip()
                break
            if stripped == "where":
                break
            if stripped == "by" and len(out) > 1:
                break
    return "\n".join(out).rstrip()


def simplify_text_latex(text: str) -> str:
    text = text.replace("~", " ")
    text = re.sub(r"\\label\{[^}]+\}", "", text)
    text = re.sub(r"\\eqref\{([^}]+)\}", r"(\1)", text)
    text = re.sub(r"\\ref\{([^}]+)\}", r"\1", text)
    text = re.sub(r"\\cite(?:\[[^\]]*\])?\{([^}]+)\}", r"[cite: \1]", text)
    text = re.sub(r"\\emph\{([^{}]*)\}", r"\1", text)
    text = re.sub(r"\\texttt\{([^{}]*)\}", r"\1", text)
    text = re.sub(r"\\textbf\{([^{}]*)\}", r"\1", text)
    text = re.sub(r"\\textit\{([^{}]*)\}", r"\1", text)
    text = re.sub(r"\\url\{([^}]+)\}", r"\1", text)
    text = re.sub(r"\s+", " ", text).strip()
    return text


def render_tex_snippet(tex: str) -> str:
    lines = tex.splitlines()
    out: list[str] = ['<div class="tex-render">']
    paragraph: list[str] = []
    i = 0

    def flush_paragraph() -> None:
        if not paragraph:
            return
        text = simplify_text_latex(" ".join(paragraph))
        if text:
            out.append(f"<p>{html_escape(text)}</p>")
        paragraph.clear()

    while i < len(lines):
        stripped = lines[i].strip()
        if not stripped:
            flush_paragraph()
            i += 1
            continue

        if stripped.startswith(r"\begin{equation") or stripped.startswith(r"\begin{align") or stripped.startswith(r"\["):
            flush_paragraph()
            block: list[str] = [stripped]
            if stripped.startswith(r"\["):
                i += 1
                while i < len(lines):
                    block.append(lines[i].strip())
                    if lines[i].strip().endswith(r"\]"):
                        break
                    i += 1
            else:
                env_match = re.match(r"\\begin\{([^}]+)\}", stripped)
                env = env_match.group(1) if env_match else ""
                i += 1
                while i < len(lines):
                    block.append(lines[i].rstrip())
                    if lines[i].strip() == rf"\end{{{env}}}":
                        break
                    i += 1
            out.append('<div class="tex-block-math">' + html_escape("\n".join(block)) + "</div>")
            i += 1
            continue

        m = re.match(r"\\(?:subsubsection|subsection|section)\{([^}]*)\}", stripped)
        if m:
            flush_paragraph()
            title = m.group(1)
            cls = "tex-heading" if stripped.startswith(r"\section{") else "tex-subheading"
            out.append(f'<p class="{cls}">{html_escape(simplify_text_latex(title))}</p>')
            i += 1
            continue

        m = re.match(r"\\begin\{proof\}(?:\[(.*)\])?", stripped)
        if m:
            flush_paragraph()
            title = simplify_text_latex(m.group(1) or "Proof")
            out.append(f'<p class="tex-subheading">{html_escape(title)}</p>')
            i += 1
            continue

        if stripped.startswith("%"):
            flush_paragraph()
            i += 1
            continue

        if stripped.startswith(r"\begin{") or stripped.startswith(r"\end{"):
            flush_paragraph()
            i += 1
            continue

        paragraph.append(stripped)
        i += 1

    flush_paragraph()
    out.append("</div>")
    return "\n".join(out)


def parse_record_blocks(path: Path) -> list[dict[str, Any]]:
    lines = path.read_text().splitlines()
    records: list[dict[str, Any]] = []
    i = 0
    relpath = path.relative_to(ROOT).as_posix()
    while i < len(lines):
        if lines[i].strip() != "% BP_RECORD_BEGIN":
            i += 1
            continue
        start_line = i + 1
        i += 1
        payload: list[str] = []
        while i < len(lines) and lines[i].strip() != "% BP_RECORD_END":
            raw = lines[i]
            if not raw.lstrip().startswith("%"):
                raise ValueError(f"Non-comment line inside BP_RECORD block at {relpath}:{i + 1}")
            stripped = raw.lstrip()[1:]
            if stripped.startswith(" "):
                stripped = stripped[1:]
            payload.append(stripped)
            i += 1
        if i >= len(lines):
            raise ValueError(f"Unclosed BP_RECORD block in {relpath}:{start_line}")
        record = json.loads("\n".join(payload))
        record["_source_file"] = relpath
        record["_source_line"] = start_line
        records.append(record)
        i += 1
    return records


def load_blueprint_records() -> dict[str, Any]:
    data: dict[str, Any] = {
        "chapters": [],
        "modules": [],
        "paper_items": [],
        "lean_items": [],
    }
    for path in sorted(CHAPTER_DIR.glob("*.tex")):
        for record in parse_record_blocks(path):
            rtype = record["record_type"]
            if rtype == "chapter":
                data["chapters"].append(record)
            elif rtype == "module":
                data["modules"].append(record)
            elif rtype == "paper_item":
                data["paper_items"].append(record)
            elif rtype == "lean_item":
                data["lean_items"].append(record)
            else:
                raise ValueError(f"Unknown record_type {rtype} in {record['_source_file']}")

    # Lean source lines are derived data. Resolve them from the current source tree so the
    # blueprint input remains robust under ongoing API cleanup and file edits.
    for item in data["lean_items"]:
        actual_line = find_symbol(item["file"], item["symbol"])
        if actual_line is not None:
            item["line"] = actual_line

    chapters_by_id = {chapter["id"]: chapter for chapter in data["chapters"]}
    modules_by_id = {module["id"]: module for module in data["modules"]}
    lean_by_id = {item["id"]: item for item in data["lean_items"]}
    paper_by_id = {item["id"]: item for item in data["paper_items"]}

    data["chapters_by_id"] = chapters_by_id
    data["modules_by_id"] = modules_by_id
    data["lean_by_id"] = lean_by_id
    data["paper_by_id"] = paper_by_id
    return data


def nav_html(prefix: str) -> str:
    return f"""
    <nav class="topnav">
      <a href="{prefix}index.html">Overview</a>
      <a href="{prefix}chapters.html">Chapters</a>
      <a href="{prefix}paper-results.html">Paper Results</a>
      <a href="{prefix}lean-results.html">Lean Results</a>
      <a href="{prefix}modules.html">Modules</a>
      <a href="{prefix}proof-graph.html">Graph</a>
      <a href="{prefix}how-to-read.html">How To Read</a>
    </nav>
    """.strip()


def page_template(title: str, body: str, *, prefix: str = "", extra_head: str = "") -> str:
    nav = nav_html(prefix)
    return f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{html_escape(title)}</title>
  <link rel="stylesheet" href="{prefix}assets/style.css">
  <script defer src="{prefix}assets/app.js"></script>
  {extra_head}
</head>
<body>
  <main class="page">
    {nav}
    {body}
  </main>
</body>
</html>
"""


def flatten_search_text(parts: list[str]) -> str:
    return " ".join(part for part in parts if part).lower()
