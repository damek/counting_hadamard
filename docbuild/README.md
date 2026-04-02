# Lean Docs Build

This nested Lake project builds a real `doc-gen4` documentation site for the
main `RequestProject` package.

The intended published layout is:

- `.../blueprint/` for the proof blueprint
- `.../docs/` for the generated Lean declaration docs

This mirrors the split used by the PFR project.

## First-time setup

```sh
cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update doc-gen4
```

## Build docs

```sh
python3 docbuild/scripts/rebuild_docs.py
```

The rebuild helper sets `DOCGEN_SRC=file`, so the generated declaration pages
use local source-file links instead of requiring a configured GitHub remote.

The generated docs site will be at:

- `.lake/build/doc/`

## Local preview

To preview together with the blueprint, build both outputs and then copy them
into one common web root:

```sh
python3 scripts/build_publish_root.py
python3 -m http.server 8004 -d publish
```

Then open:

- `http://localhost:8004/blueprint/`
- `http://localhost:8004/docs/`
