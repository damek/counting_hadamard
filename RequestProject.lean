import RequestProject.HadamardCn3
import RequestProject.HadamardCn3Defs
import RequestProject.HadamardCn3TorusCount
import RequestProject.HadamardCn3Moments
import RequestProject.HadamardCn3DiscreteMoments
import RequestProject.HadamardCn3MOO
import RequestProject.HadamardCn3ResidualBase
import RequestProject.HadamardCn3LocalGap
import RequestProject.HadamardCn3LocalGapBridge
import RequestProject.HadamardCn3LocalGapCore
import RequestProject.HadamardCn3LocalGapFixedN
import RequestProject.HadamardCn3LocalGapResidual
import RequestProject.HadamardCn3PaperSpec
import RequestProject.HadamardCn3QuarticBounds
import RequestProject.HadamardCn3QuarticFiber
import RequestProject.HadamardCn3Asymptotics
import RequestProject.HadamardCn3ShortMain
import RequestProject.HadamardCn3WeakInvariance

/-!
# RequestProject

Umbrella import for the active formalization modules of the Cn^3 Hadamard-count
project. This root module exists primarily to give the library a clean entrypoint
for generated documentation and cross-linked blueprint references.

Readers looking for the proof route should usually start with:

- `RequestProject.HadamardCn3`
- `RequestProject.HadamardCn3ShortMain`
- `RequestProject.HadamardCn3Asymptotics`
- `RequestProject.HadamardCn3TorusCount`
- `RequestProject.HadamardCn3DiscreteMoments`
- `RequestProject.HadamardCn3MOO`
- `RequestProject.HadamardCn3WeakInvariance`
- `RequestProject.HadamardCn3LocalGapBridge`
- `RequestProject.HadamardCn3QuarticFiber`

The paper-facing count definitions and endpoint theorems live in
`RequestProject.HadamardCn3ShortMain`, where

- `paperCount n s` is the literal count `N_{n,s}` of partial Hadamard matrices,
- `paperAsymptoticCount n t` is the paper scale `A_{n,4t}`,
- `thm_main_intro` and `cor_uniform` are stated directly in terms of the
  ratio `(paperCount n (4 * t) : ℝ) / paperAsymptoticCount n t`.

The intermediate normalized-count route lives in
`RequestProject.HadamardCn3Asymptotics`, which contains
`prop_primary_box` and `normalizedCount_asymptotic`.
-/
