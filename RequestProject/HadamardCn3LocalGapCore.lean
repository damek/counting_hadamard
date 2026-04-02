import RequestProject.HadamardCn3LocalGapBridge
import RequestProject.HadamardCn3LocalGapResidual
import RequestProject.HadamardCn3LocalGapFixedN

/-!
# Local-Gap Core

Aggregator module for the local-gap proof.

This re-exports the three layers used by the main asymptotic theorem:

- `HadamardCn3LocalGapBridge`: exact-to-corrected-to-quartic-to-cubic bridge
- `HadamardCn3LocalGapResidual`: large-`n` residual estimate
- `HadamardCn3LocalGapFixedN`: fixed-`n` fallback asymptotic
-/
