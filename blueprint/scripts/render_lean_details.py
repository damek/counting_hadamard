#!/usr/bin/env python3

from __future__ import annotations

import json
import shutil
import sys
from pathlib import Path

from _blueprint_common import BLUEPRINT_ROOT, extract_lean_statement, load_blueprint_records


DATA_PATH = BLUEPRINT_ROOT / "data" / "lean_details.json"
OUT_DIR = BLUEPRINT_ROOT / "src" / "generated_details"


def tex_escape(text: str) -> str:
    return (
        text.replace("\\", r"\textbackslash{}")
        .replace("{", r"\{")
        .replace("}", r"\}")
        .replace("_", r"\_")
        .replace("%", r"\%")
        .replace("&", r"\&")
        .replace("#", r"\#")
        .replace("$", r"\$")
    )


def role_text(item: dict, lean_by_id: dict[str, dict]) -> str:
    uses = [lean_by_id[ref]["symbol"] for ref in item["depends_on"]]
    feeds = [lean_by_id[ref]["symbol"] for ref in item["used_by"]]
    parts: list[str] = []
    if uses:
        uses_text = ", ".join(uses)
        parts.append(f"It depends directly on {uses_text}.")
    if feeds:
        feeds_text = ", ".join(feeds)
        parts.append(f"It is used directly by {feeds_text}.")
    if item["paper_item"] is None:
        parts.append("This is a Lean-only route item rather than a named paper statement.")
    return " ".join(parts)


def render_detail(item: dict, details: dict[str, str], lean_by_id: dict[str, dict]) -> str:
    statement = extract_lean_statement(item["file"], item["line"])
    in_words = details.get("in_words", item["summary"])
    proof_idea = details.get("proof_idea")
    if item["kind"] != "definition" and not proof_idea:
        raise SystemExit(f"[render_lean_details] missing proof_idea for {item['id']}")

    body = [r"\medskip"]
    if item["kind"] == "definition":
        body.extend(
            [
                r"\paragraph{Meaning.}",
                tex_escape(in_words),
                r"\paragraph{Formal Lean definition.}",
                r"\begin{verbatim}",
                statement,
                r"\end{verbatim}",
            ]
        )
    else:
        body.extend(
            [
                r"\paragraph{Formal Lean statement.}",
                r"\begin{verbatim}",
                statement,
                r"\end{verbatim}",
                r"\begin{proof}[Proof sketch]",
                tex_escape(proof_idea),
                r"\end{proof}",
            ]
        )

        if in_words and in_words != item["summary"]:
            body.extend(
                [
                    r"\paragraph{In words.}",
                    tex_escape(in_words),
                ]
            )

    role = details.get("role", role_text(item, lean_by_id))
    if role:
        body.extend(
            [
                r"\paragraph{Role in the route.}",
                tex_escape(role),
            ]
        )
    body.extend(
        [
            r"\paragraph{Source location.}",
            rf"\texttt{{{tex_escape(item['file'])}:{item['line']}}}",
            r"\medskip",
            "",
        ]
    )
    return "\n".join(body)


def main() -> int:
    if not DATA_PATH.exists():
        raise SystemExit(f"[render_lean_details] missing data file {DATA_PATH}")

    data = json.loads(DATA_PATH.read_text())
    records = load_blueprint_records()
    lean_by_id = records["lean_by_id"]
    shutil.rmtree(OUT_DIR, ignore_errors=True)
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    for item_id, item in lean_by_id.items():
        details = data.get(item_id, {})
        content = render_detail(item, details, lean_by_id)
        (OUT_DIR / f"{item_id}.tex").write_text(content)

    print(f"[render_lean_details] wrote {len(lean_by_id)} detail files to {OUT_DIR}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
