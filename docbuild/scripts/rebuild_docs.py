#!/usr/bin/env python3

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import os
from pathlib import Path


DOCBUILD_ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = DOCBUILD_ROOT.parent
DOC_DIR = DOCBUILD_ROOT / ".lake" / "build" / "doc"


def run(cmd: list[str], *, cwd: Path, env: dict[str, str]) -> None:
    print(f"[rebuild_docs] {' '.join(cmd)}", flush=True)
    completed = subprocess.run(cmd, cwd=cwd, env=env)
    if completed.returncode != 0:
        raise SystemExit(completed.returncode)


def project_modules() -> list[tuple[str, Path]]:
    modules: list[tuple[str, Path]] = []
    for path in sorted((REPO_ROOT / "RequestProject").rglob("*.lean")):
        module = ".".join(path.relative_to(REPO_ROOT).with_suffix("").parts)
        modules.append((module, path))
    return modules


def github_repo(env: dict[str, str]) -> str:
    repo = env.get("DOCGEN_REPOSITORY")
    if repo:
        return repo.rstrip("/")
    github_repo_name = env.get("GITHUB_REPOSITORY")
    if github_repo_name:
        server = env.get("GITHUB_SERVER_URL", "https://github.com").rstrip("/")
        return f"{server}/{github_repo_name}"
    raise SystemExit("DOCGEN_SRC=github requires DOCGEN_REPOSITORY or GITHUB_REPOSITORY")


def github_rev(env: dict[str, str]) -> str:
    rev = env.get("DOCGEN_REV") or env.get("GITHUB_SHA")
    if rev:
        return rev
    completed = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    if completed.returncode == 0:
        return completed.stdout.strip()
    raise SystemExit("DOCGEN_SRC=github requires DOCGEN_REV, GITHUB_SHA, or a readable git HEAD")


def source_uri(path: Path, env: dict[str, str]) -> str:
    mode = env.get("DOCGEN_SRC", "file").lower()
    if mode == "file":
        return path.resolve().as_uri()
    if mode == "github":
        rel = path.relative_to(REPO_ROOT).as_posix()
        return f"{github_repo(env)}/blob/{github_rev(env)}/{rel}"
    raise SystemExit(f"Unsupported DOCGEN_SRC mode: {mode}")


def reset_doc_dir() -> None:
    shutil.rmtree(DOC_DIR, ignore_errors=True)
    DOC_DIR.mkdir(parents=True, exist_ok=True)
    (DOC_DIR / "references.bib").write_text("", encoding="utf-8")


def rebuild_curated(env: dict[str, str], *, skip_build: bool) -> None:
    reset_doc_dir()
    if not skip_build:
        run(["lake", "build"], cwd=REPO_ROOT, env=env)
    for module, path in project_modules():
        run(
            [
                "lake",
                "exe",
                "doc-gen4",
                "single",
                "--build",
                ".lake/build",
                module,
                source_uri(path, env),
            ],
            cwd=DOCBUILD_ROOT,
            env=env,
        )
    run(["lake", "exe", "doc-gen4", "index", "--build", ".lake/build"], cwd=DOCBUILD_ROOT, env=env)


def rebuild_full(env: dict[str, str]) -> None:
    reset_doc_dir()
    run(["lake", "build", "RequestProject:docs"], cwd=DOCBUILD_ROOT, env=env)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Rebuild Lean docs for RequestProject.",
    )
    parser.add_argument(
        "--mode",
        choices=("curated", "full"),
        default=os.environ.get("DOCBUILD_MODE", "curated"),
        help="curated builds only RequestProject module docs; full uses the recursive library facet",
    )
    parser.add_argument(
        "--skip-build",
        action="store_true",
        default=os.environ.get("DOCBUILD_SKIP_BUILD", "").lower() in {"1", "true", "yes"},
        help="skip the preliminary root lake build (useful in CI after an earlier compile step)",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    env = os.environ.copy()
    env.setdefault("DOCGEN_SRC", "file")
    if args.mode == "curated":
        rebuild_curated(env, skip_build=args.skip_build)
    else:
        rebuild_full(env)
    print(f"[rebuild_docs] mode={args.mode} wrote {DOC_DIR}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
