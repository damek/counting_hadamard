#!/usr/bin/env python3

from __future__ import annotations

import shutil
import subprocess
import sys
import os
from pathlib import Path


DOCBUILD_ROOT = Path(__file__).resolve().parents[1]
DOC_DIR = DOCBUILD_ROOT / ".lake" / "build" / "doc"


def main() -> int:
    shutil.rmtree(DOC_DIR, ignore_errors=True)
    DOC_DIR.mkdir(parents=True, exist_ok=True)
    (DOC_DIR / "references.bib").write_text("", encoding="utf-8")
    env = os.environ.copy()
    env.setdefault("DOCGEN_SRC", "file")
    completed = subprocess.run(
        ["lake", "build", "RequestProject:docs"],
        cwd=DOCBUILD_ROOT,
        env=env,
    )
    if completed.returncode != 0:
        raise SystemExit(completed.returncode)
    print(f"[rebuild_docs] wrote {DOC_DIR}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
