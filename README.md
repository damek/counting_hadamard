# Cn^3 Hadamard Formalization

This repository contains the active Lean formalization behind the paper
[arXiv:2603.30013](https://arxiv.org/pdf/2603.30013).

This repository is organized as a clean source tree on `main` plus a generated
GitHub Pages site built from the same source.

The source tree contains:

- [RequestProject](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/RequestProject): active Lean source
- [documents](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/documents): local synchronized TeX source used by the blueprint toolchain
- [blueprint](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/blueprint): blueprint source
- [docbuild](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/docbuild): helper configuration for regenerating Lean docs
- [publish](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/publish): landing-page source for the public site

## Build

Run from the repository root:

```sh
lake build
lake env lean scripts/print_axioms_check.lean
```

## Public Site

The GitHub Pages site is generated from this source tree and exposes:

- a landing page
- a blueprint with theorem-by-theorem navigation
- Lean docs for the project modules
- a source snapshot for the key Lean files

Generated HTML is assembled into `.site/` by:

```sh
python3 docbuild/scripts/rebuild_docs.py
python3 blueprint/scripts/build_real_blueprint.py
python3 scripts/assemble_pages_site.py
```

## Where To Start Reading

If you want to check the formalized paper statements first, begin with:

- [RequestProject/HadamardCn3.lean](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/RequestProject/HadamardCn3.lean)
- [RequestProject/HadamardCn3ShortMain.lean](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/RequestProject/HadamardCn3ShortMain.lean)
- [RequestProject/HadamardCn3Asymptotics.lean](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/RequestProject/HadamardCn3Asymptotics.lean)
- [RequestProject/HadamardCn3WeakInvariance.lean](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/RequestProject/HadamardCn3WeakInvariance.lean)
- [RequestProject/HadamardCn3PaperSpec.lean](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/RequestProject/HadamardCn3PaperSpec.lean)

The curated public entrypoint is:

- [RequestProject/HadamardCn3.lean](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/RequestProject/HadamardCn3.lean)

The paper theorem file is:

- [RequestProject/HadamardCn3ShortMain.lean](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/RequestProject/HadamardCn3ShortMain.lean)
- [RequestProject/HadamardCn3Asymptotics.lean](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/RequestProject/HadamardCn3Asymptotics.lean)

`HadamardCn3ShortMain.lean` now contains only the final count-facing quantities

- `paperCount n s = N_{n,s}`
- `paperAsymptoticCount n t = A_{n,4t}`

and then states the endpoint theorems `thm_main_intro` and `cor_uniform`
directly in terms of the ratio
`(paperCount n (4 * t) : ℝ) / paperAsymptoticCount n t`.

`HadamardCn3Asymptotics.lean` contains the intermediate normalized-count statements:

- `paperNormalizedCount n t`
- `paperTargetIntegral n t`
- `paperNormalizedIntegral n t`
- `paperMainScale n t`
- `paperMainTerm n t`
- `paperNormalizedCount_eq_integral`
- `prop_primary_box`
- `normalizedCount_asymptotic`

So the count theorems are now separated cleanly from the integral and
normalized-count infrastructure.

The weak-comparison input and the remaining project-specific normalization bridge live in:

- [RequestProject/HadamardCn3WeakInvariance.lean](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/RequestProject/HadamardCn3WeakInvariance.lean)
- [RequestProject/HadamardCn3PaperSpec.lean](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/RequestProject/HadamardCn3PaperSpec.lean)

## Packaging For Upload

This working repository still contains local tooling and archived material.
To stage a clean source-only upload tree, use:

```sh
scripts/stage_upload_repo.sh
```

That staging step keeps the active formalization and public-site sources while
excluding local caches, generated HTML, archived material, and developer-only
helpers.

## Archive

Historical material has been quarantined under [archive](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/archive):

- [archive/lean](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/archive/lean): archived Lean modules kept for reference
- [archive/scratch](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/archive/scratch): old scratch Lean files
- [archive/workfiles](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/archive/workfiles): saved `.bak` work files
- [archive/legacy-docs](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/archive/legacy-docs): historical plans, ledgers, and notes
- [archive/legacy-sites](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/archive/legacy-sites): retired documentation experiments and generated site prototypes
- [archive/legacy-tex](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/archive/legacy-tex): legacy TeX drafts and generated byproducts
- [archive/root-artifacts](/Users/damek/Documents/Code/cursor/partial_hadamard/lean%20formalizations/aristotle_n3/f56e8781-1af5-4d6d-a663-0f49ef57299a-aristotle.tar_aristotle/archive/root-artifacts): miscellaneous root artifacts no longer part of the active project

## Notes

- The canonical public paper reference is [arXiv:2603.30013](https://arxiv.org/pdf/2603.30013).
- The local `documents/` directory contains the repository's TeX sources and build artifacts.
- `MOO` refers to the Mossel-O'Donnell-Oleszkiewicz invariance principle;
  see Mossel, O'Donnell, Oleszkiewicz, "Noise stability of functions with low
  influences: Invariance and optimality", Annals of Mathematics 171 (2010),
  295-341.
- The source branch is intended to stay source-only and reviewable; generated
  HTML belongs in the Pages deployment output.
- The repository root is intentionally minimal; historical notes and experiments live under `archive/`.
- The old curated `active/` mirror has been retired into `archive/legacy-sites/active-view/`.
