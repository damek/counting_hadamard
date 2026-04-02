import RequestProject.HadamardCn3ShortMain
import RequestProject.HadamardCn3Asymptotics
import RequestProject.HadamardCn3PaperSpec
import RequestProject.HadamardCn3WeakInvariance

/-!
# Public Entry Point For The Cn^3 Formalization

This thin umbrella module re-exports the reader-facing surface of the active
formalization of the paper at `https://arxiv.org/pdf/2603.30013`.

Readers should start with:

- `paperCount n s`, the literal count `N_{n,s}` of `n × s` partial Hadamard matrices
- `paperAsymptoticCount n t = A_{n,4t}`
- `thm_main_intro`
- `cor_uniform`

from `RequestProject.HadamardCn3ShortMain`.

The intermediate normalized-count statements live in
`RequestProject.HadamardCn3Asymptotics`, where the two key inputs are:

- `prop_primary_box`
- `normalizedCount_asymptotic`

The two paper endpoint theorems are therefore literally statements about the
count `N_{n,4t}` of `n × 4t` partial Hadamard matrices:

- `thm_main_intro`, which bounds the ratio
  `(paperCount n (4 * t) : ℝ) / paperAsymptoticCount n t`
  around `1 - (Nat.choose n 3 : ℝ) / (8 * (t : ℝ))`
- `cor_uniform`, which deduces uniform closeness of the same ratio to `1`
  for `t ≥ K n^3`

For the weak comparison input, inspect:

- `quadraticForm_lindeberg_comparison_C3`
- `psi_sub_gaussianPsi_le_threeHalfInfluenceSum`

from `RequestProject.HadamardCn3WeakInvariance`.

The only extra paper-notation bridge retained here is:

- `paper_threeHalfInfluenceSum_eq_eight_kernelInfluence_sum`

from `RequestProject.HadamardCn3PaperSpec`.

The canonical trust audit for the active source tree is:

- `lake build`
- `bash scripts/verify_trust.sh`
-/
