#!/usr/bin/env python3

from __future__ import annotations

import shutil
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SITE_DIR = ROOT / ".site"
PUBLISH_DIR = ROOT / "publish"
BLUEPRINT_WEB_DIR = ROOT / "blueprint" / "web"
DOC_DIR = ROOT / "docbuild" / ".lake" / "build" / "doc"
SOURCE_DIR = ROOT / "RequestProject"

DOC_DIR_ALLOWLIST = {
    "RequestProject",
    "find",
    "src",
    "declarations",
}

DOC_FILE_ALLOWLIST = {
    "404.html",
    "color-scheme.js",
    "declaration-data.js",
    "expand-nav.js",
    "favicon.svg",
    "foundational_types.html",
    "how-about.js",
    "importedBy.js",
    "index.html",
    "instances.js",
    "jump-src.js",
    "mathjax-config.js",
    "nav.js",
    "navbar.html",
    "references.bib",
    "references.html",
    "search.html",
    "search.js",
    "style.css",
    "tactics.html",
}


def copytree(src: Path, dst: Path) -> None:
    shutil.copytree(src, dst, dirs_exist_ok=True)


def copy_curated_docs(src_root: Path, dst_root: Path) -> None:
    dst_root.mkdir(parents=True, exist_ok=True)
    for path in src_root.iterdir():
        if path.name in DOC_DIR_ALLOWLIST and path.is_dir():
            copytree(path, dst_root / path.name)
        elif path.name in DOC_FILE_ALLOWLIST and path.is_file():
            shutil.copy2(path, dst_root / path.name)


def main() -> int:
    shutil.rmtree(SITE_DIR, ignore_errors=True)
    SITE_DIR.mkdir(parents=True, exist_ok=True)

    shutil.copy2(PUBLISH_DIR / "index.html", SITE_DIR / "index.html")
    copytree(BLUEPRINT_WEB_DIR, SITE_DIR / "blueprint")
    copy_curated_docs(DOC_DIR, SITE_DIR / "docs")

    source_root = SITE_DIR / "source"
    source_root.mkdir(parents=True, exist_ok=True)
    shutil.copy2(ROOT / "RequestProject.lean", source_root / "RequestProject.lean")
    copytree(SOURCE_DIR, source_root / "RequestProject")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
