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


def run(cmd: list[str], cwd: Path) -> None:
    completed = subprocess.run(cmd, cwd=cwd)
    if completed.returncode != 0:
        raise SystemExit(completed.returncode)


def main() -> int:
    shutil.rmtree(WEB_DIR, ignore_errors=True)
    run([sys.executable, "blueprint/scripts/render_lean_details.py"], ROOT)
    run([sys.executable, "blueprint/scripts/validate_blueprint.py"], ROOT)
    run([str(BLUEPRINT_ROOT / ".venv" / "bin" / "plastex"), "-c", "plastex.cfg", "web.tex"], SRC_DIR)
    print(f"[build_real_blueprint] wrote {WEB_DIR}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
