#!/usr/bin/env python3

from __future__ import annotations

import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
BLUEPRINT_ROOT = ROOT / "blueprint"
SRC_DIR = BLUEPRINT_ROOT / "src"
WEB_DIR = BLUEPRINT_ROOT / "web"
WEB_STYLE_DIR = WEB_DIR / "styles"
WEB_JS_DIR = WEB_DIR / "js"
SOURCE_STYLE = SRC_DIR / "extra_styles.css"
TARGET_STYLE = WEB_STYLE_DIR / "extra_styles.css"
PLASTEX_JS = WEB_JS_DIR / "plastex.js"
MODAL_FIX = """$(document).on("click", "div.modal-container", function(e) {\n        if (e.target === this) { $(this).hide(); }\n    })"""


def run(cmd: list[str], cwd: Path) -> None:
    completed = subprocess.run(cmd, cwd=cwd)
    if completed.returncode != 0:
        raise SystemExit(completed.returncode)


def sync_extra_styles() -> None:
    WEB_STYLE_DIR.mkdir(parents=True, exist_ok=True)
    shutil.copy2(SOURCE_STYLE, TARGET_STYLE)


def ensure_modal_fix() -> None:
    if not PLASTEX_JS.exists():
        raise SystemExit(f"missing expected plasTeX output: {PLASTEX_JS}")
    text = PLASTEX_JS.read_text()
    if '$(document).on("click", "div.modal-container"' in text:
        return
    marker = """    $("button.closebtn").click(
        function() {
          $(this).parent().parent().parent().hide();
        })"""
    replacement = marker + "\n    " + MODAL_FIX
    if marker not in text:
        raise SystemExit("could not find modal close button block in plastex.js")
    PLASTEX_JS.write_text(text.replace(marker, replacement))


def main() -> int:
    shutil.rmtree(WEB_DIR, ignore_errors=True)
    run([sys.executable, "blueprint/scripts/render_lean_details.py"], ROOT)
    run([sys.executable, "blueprint/scripts/validate_blueprint.py"], ROOT)
    run([str(BLUEPRINT_ROOT / ".venv" / "bin" / "plastex"), "-c", "plastex.cfg", "web.tex"], SRC_DIR)
    sync_extra_styles()
    ensure_modal_fix()
    print(f"[build_real_blueprint] wrote {WEB_DIR}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
