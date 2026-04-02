# Counting Partial Hadamard Matrices

This repository contains the Lean formalization behind
[arXiv:2603.30013](https://arxiv.org/pdf/2603.30013).

The repository has two reader-facing surfaces:

- the source tree on `main`
- the generated GitHub Pages site with the landing page, blueprint, and Lean docs

## Repository Layout

- `RequestProject/`: active Lean modules
- `RequestProject.lean`: package entrypoint
- `documents/short.tex`: local synchronized TeX source used by the blueprint toolchain
- `blueprint/src/`: blueprint source
- `docbuild/`: `doc-gen4` configuration for project docs
- `publish/index.html`: landing page source for the Pages site

## Build

From the repository root:

```sh
lake build
lake env lean scripts/print_axioms_check.lean
```

The axiom audit for the key endpoint theorems should report only:

- `propext`
- `Classical.choice`
- `Quot.sound`

## Lean Docs

The default docs build is curated: it generates Lean docs only for the
`RequestProject` modules that are published on the Pages site.

```sh
python3 docbuild/scripts/rebuild_docs.py
```

For the old exhaustive recursive `doc-gen4` build, use:

```sh
python3 docbuild/scripts/rebuild_docs.py --mode full
```

## Blueprint

To rebuild the blueprint locally:

```sh
python3 -m venv blueprint/.venv
blueprint/.venv/bin/pip install --upgrade pip
blueprint/.venv/bin/pip install -r blueprint/requirements.txt
python3 blueprint/scripts/build_real_blueprint.py
```

## Local Site Preview

To preview the same site layout used for GitHub Pages:

```sh
python3 docbuild/scripts/rebuild_docs.py
python3 blueprint/scripts/build_real_blueprint.py
python3 scripts/assemble_pages_site.py
cd .site
python3 -m http.server 8005
```

Then open:

- `/` for the landing page
- `/blueprint/` for the blueprint
- `/docs/` for the Lean docs

## Where To Start Reading

If you want to inspect the formalized paper statements first, start with:

- `RequestProject/HadamardCn3.lean`
- `RequestProject/HadamardCn3ShortMain.lean`
- `RequestProject/HadamardCn3Asymptotics.lean`
- `RequestProject/HadamardCn3WeakInvariance.lean`
- `RequestProject/HadamardCn3PaperSpec.lean`

`HadamardCn3ShortMain.lean` is the count-facing endpoint file. It defines the
literal count of partial Hadamard matrices and states the two final count
theorems:

- `thm_main_intro`
- `cor_uniform`

`HadamardCn3Asymptotics.lean` contains the normalized-count and integral bridge
used to reach those endpoint theorems.

## Notes

- `MOO` refers to the Mossel-O'Donnell-Oleszkiewicz invariance principle; see
  Mossel, O'Donnell, Oleszkiewicz, *Noise stability of functions with low
  influences: Invariance and optimality*, Annals of Mathematics 171 (2010),
  295-341.
- The `main` branch is intended to stay source-only and reviewable.
- Generated HTML belongs to the GitHub Pages deployment output, not normal
  source history.
