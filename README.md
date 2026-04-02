# Counting Partial Hadamard Matrices

This repository contains the Lean formalization behind
[arXiv:2603.30013](https://arxiv.org/pdf/2603.30013).

The repository has two reader-facing surfaces:

- the source tree on `main`
- the generated GitHub Pages site with the landing page, blueprint, and Lean docs

## Repository Layout

- `RequestProject/`: active Lean modules
- `RequestProject.lean`: package entrypoint
- `index.html`: landing page source for the published site
- `documents/short.tex`: local synchronized TeX source used by the blueprint toolchain
- `blueprint/src/`: blueprint source
- `blueprint/web/`: checked-in published blueprint HTML
- `docbuild/`: `doc-gen4` configuration for project docs

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

## Additional Audits

GitHub Actions uses `leanchecker` as its kernel-replay audit:

```sh
lake env leanchecker RequestProject.HadamardCn3ShortMain
lake env leanchecker RequestProject.HadamardCn3Asymptotics
lake env leanchecker RequestProject.HadamardCn3WeakInvariance
lake env leanchecker RequestProject.HadamardCn3LocalGapResidual
lake env leanchecker RequestProject.HadamardCn3
```

The repository also includes a separate comparator audit surface under
`Comparator/`:

- `Comparator/Challenge.lean`: trusted challenge statements for the endpoint theorems
- `Comparator/Solution.lean`: wrappers that point those statements at the actual formal proofs
- `Comparator/comparator.json`: comparator configuration

These files are kept for a self-hosted Linux comparator run. The GitHub-hosted
workflow was removed because comparator depends on `landrun`, and the
GitHub-hosted runner failed before theorem comparison with a `permission denied`
error from `landrun` while building `Comparator.Challenge`.

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

The published blueprint is served from `blueprint/web/`. To rebuild that local
HTML surface:

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
- `/blueprint/web/` for the blueprint
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
