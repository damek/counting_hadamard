#!/usr/bin/env python3

from __future__ import annotations

import json
import sys
from typing import Any

from _blueprint_common import BLUEPRINT_ROOT, CANONICAL_PAPER, ROOT, find_symbol, load_blueprint_records, read_lines


def fail(message: str) -> None:
    raise SystemExit(f"[blueprint-validate] {message}")


def require_keys(obj: dict[str, Any], keys: list[str], context: str) -> None:
    missing = [key for key in keys if key not in obj]
    if missing:
        fail(f"{context} is missing required keys: {missing}")


def validate_line_range(relpath: str, line_range: dict[str, int] | None, context: str) -> None:
    if line_range is None:
        return
    require_keys(line_range, ["start", "end"], context)
    start = line_range["start"]
    end = line_range["end"]
    if not isinstance(start, int) or not isinstance(end, int) or start < 1 or end < start:
        fail(f"{context} has invalid line range {line_range}")
    lines = read_lines(relpath)
    if end > len(lines):
        fail(f"{context} exceeds file length: {relpath}:{end} > {len(lines)}")


def main() -> int:
    data = load_blueprint_records()
    lean_details_path = BLUEPRINT_ROOT / "data" / "lean_details.json"

    if not CANONICAL_PAPER.exists():
        fail("documents/short.tex is missing")
    if not lean_details_path.exists():
        fail("blueprint/data/lean_details.json is missing")

    lean_details = json.loads(lean_details_path.read_text())

    chapter_ids: set[str] = set()
    module_ids: set[str] = set()
    paper_ids: set[str] = set()
    lean_ids: set[str] = set()

    for chapter in data["chapters"]:
        require_keys(
            chapter,
            ["id", "title", "summary", "chapter_file", "order"],
            f"chapter {chapter.get('id', '?')}",
        )
        if chapter["id"] in chapter_ids:
            fail(f"duplicate chapter id: {chapter['id']}")
        chapter_ids.add(chapter["id"])

    for module in data["modules"]:
        require_keys(
            module,
            ["id", "name", "file", "role", "imports", "public_entrypoints", "summary", "chapter"],
            f"module {module.get('id', '?')}",
        )
        if module["id"] in module_ids:
            fail(f"duplicate module id: {module['id']}")
        module_ids.add(module["id"])
        if module["chapter"] not in chapter_ids:
            fail(f"module {module['id']} points to unknown chapter {module['chapter']}")
        if not (ROOT / module["file"]).exists():
            fail(f"module file does not exist: {module['file']}")

    for item in data["lean_items"]:
        require_keys(
            item,
            [
                "id",
                "symbol",
                "file",
                "line",
                "module",
                "kind",
                "summary",
                "paper_item",
                "depends_on",
                "used_by",
                "chapter",
            ],
            f"lean item {item.get('id', '?')}",
        )
        if item["id"] in lean_ids:
            fail(f"duplicate lean item id: {item['id']}")
        lean_ids.add(item["id"])
        if item["chapter"] not in chapter_ids:
            fail(f"lean item {item['id']} points to unknown chapter {item['chapter']}")
        if item["module"] not in module_ids:
            fail(f"lean item {item['id']} points to unknown module {item['module']}")
        if not (ROOT / item["file"]).exists():
            fail(f"lean file does not exist: {item['file']}")
        actual_line = find_symbol(item["file"], item["symbol"])
        if actual_line is None:
            fail(f"Lean symbol not found: {item['symbol']} ({item['file']})")
        if actual_line != item["line"]:
            fail(
                f"Lean line mismatch for {item['symbol']}: metadata {item['line']}, source {actual_line}"
            )
        detail = lean_details.get(item["id"], {})
        if item["kind"] != "definition" and "proof_idea" not in detail:
            fail(f"lean item {item['id']} is missing proof_idea in blueprint/data/lean_details.json")

    for item in data["paper_items"]:
        require_keys(
            item,
            [
                "id",
                "label",
                "title",
                "kind",
                "tex_path",
                "statement_lines",
                "proof_lines",
                "lean_primary",
                "lean_support",
                "module_owner",
                "summary",
                "proof_steps",
                "chapter",
            ],
            f"paper item {item.get('id', '?')}",
        )
        if item["id"] in paper_ids:
            fail(f"duplicate paper item id: {item['id']}")
        paper_ids.add(item["id"])
        if item["chapter"] not in chapter_ids:
            fail(f"paper item {item['id']} points to unknown chapter {item['chapter']}")
        if item["module_owner"] not in module_ids:
            fail(f"paper item {item['id']} points to unknown module {item['module_owner']}")
        if item["lean_primary"] not in lean_ids:
            fail(f"paper item {item['id']} points to unknown lean_primary {item['lean_primary']}")
        for ref in item["lean_support"]:
            if ref not in lean_ids:
                fail(f"paper item {item['id']} points to unknown lean_support {ref}")
        if item["tex_path"] != "documents/short.tex":
            fail(f"paper item {item['id']} uses non-canonical tex source {item['tex_path']}")
        validate_line_range(item["tex_path"], item["statement_lines"], f"{item['id']} statement_lines")
        validate_line_range(item["tex_path"], item["proof_lines"], f"{item['id']} proof_lines")
        for step in item["proof_steps"]:
            require_keys(step, ["id", "title", "tex_lines", "lean_refs", "summary"], f"proof step {step.get('id', '?')}")
            validate_line_range(item["tex_path"], step["tex_lines"], f"{step['id']} tex_lines")
            for ref in step["lean_refs"]:
                if ref not in lean_ids:
                    fail(f"proof step {step['id']} points to unknown Lean ref {ref}")

    for item in data["lean_items"]:
        paper_ref = item["paper_item"]
        if paper_ref is not None and paper_ref not in paper_ids:
            fail(f"lean item {item['id']} points to unknown paper item {paper_ref}")
        for ref in item["depends_on"]:
            if ref not in lean_ids:
                fail(f"lean item {item['id']} has unknown depends_on ref {ref}")
        for ref in item["used_by"]:
            if ref not in lean_ids:
                fail(f"lean item {item['id']} has unknown used_by ref {ref}")

    print(
        "[blueprint-validate] ok:",
        f"{len(data['chapters'])} chapters,",
        f"{len(data['paper_items'])} paper items,",
        f"{len(data['lean_items'])} lean items,",
        f"{len(data['modules'])} modules",
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
