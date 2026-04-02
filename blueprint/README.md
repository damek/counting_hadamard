# Blueprint

This directory is the canonical human-facing formalization map for the active
route formalizing the paper [arXiv:2603.30013](https://arxiv.org/pdf/2603.30013).

It is intentionally separate from:

- the canonical public paper reference at `https://arxiv.org/pdf/2603.30013`
- the live Lean source in `RequestProject/`
- the local synchronized TeX source in `documents/short.tex`
- the archived prototype proof-map in `archive/legacy-sites/site/`

## What this blueprint answers

1. Which paper-level results are formalized?
2. Which Lean theorem proves each such result?
3. Which Lean-only bridge results are on the active route?
4. Which module owns each declaration?
5. How do the route items depend on one another?

## Source layout

- `src/`
  Blueprint-style TeX source files. These are the canonical documentation source.
- `src/chapters/`
  Chapter-level route content.
- `scripts/`
  Local validators and static-site builders that keep the blueprint synchronized to the
  live Lean source.
- `web/`
  Generated HTML output from the real `leanblueprint` toolchain. This directory
  is rebuilt for local preview and for the Pages deployment artifact; it is not
  part of the clean source snapshot.

Legacy generated snapshots have been retired into `archive/legacy-sites/`.

## Important rule

The blueprint is allowed to reflect the formalization architecture rather than mirroring
the paper proof structure one-for-one.

That means the blueprint includes Lean-only route items such as:

- `normalizedCount_asymptotic`
- `fixed_n_count_asymptotic`

when they are needed to understand the active formal route.

## Local checks

```sh
python3 blueprint/scripts/render_lean_details.py
python3 blueprint/scripts/validate_blueprint.py
```

The first command regenerates the per-declaration detail blocks that expose:

- the actual Lean statement for each curated declaration
- an English-language explanation or proof idea
- route role and source location

## Build The Real Blueprint HTML

The real `leanblueprint` tooling is installed in the local virtual environment:

```sh
blueprint/.venv/bin/leanblueprint --help
```

Because this project sits inside a larger parent Git checkout, the
`leanblueprint web` wrapper resolves the wrong repo root. Use the local rebuild
wrapper instead:

```sh
python3 blueprint/scripts/build_real_blueprint.py
```

This produces the canonical HTML output in:

- `blueprint/web/`

## Local preview

```sh
python3 -m http.server 8002 -d blueprint/web
```

Then open `http://localhost:8002/`.

## Public site

The public Pages site publishes the blueprint under `/blueprint/` alongside the
project Lean docs under `/docs/`.

## Tooling note

The real `leanblueprint` package is installed locally in `blueprint/.venv`.
The repo keeps local validation helpers in `blueprint/scripts/` because they provide
line-level checks against the live Lean source even when the canonical HTML is built by
the real blueprint toolchain.
