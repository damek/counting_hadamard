import RequestProject.HadamardCn3QuarticFiber

/-!
# Quartic Core Bounds

This module contains the quartic-core Gaussian bounds used by the active local-gap
bridge. The content formerly lived in a scratch file; it is now part of the
`RequestProject` library proper.
-/

open MeasureTheory
open Classical

private lemma quartic_core_integral_bound_explicit
    (β D t : ℝ) (hβ : 0 ≤ β) (hD : 0 ≤ D) (ht : 0 < t)
    (hsmall : β * (D / t) ≤ 1 / 2) (n : ℕ) :
    ∫ mu in edgeCoreRegionD n D t,
        Real.exp (β * t * quarticCorr n (matrixOfEdge n mu))
          * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
      ≤ Real.exp ((β ^ (2 : Nat) / 2) * (n : ℝ) * (D / t) ^ (2 : Nat))
          * gaussianF (dim n) t := by
  have hmain := (quarticCoreTrunc_bound β D t hβ hD ht hsmall n).2
  have hmeas : MeasurableSet (edgeCoreRegionD n D t) :=
    measurableSet_edgeCoreRegionD n D t
  calc
    ∫ mu in edgeCoreRegionD n D t,
        Real.exp (β * t * quarticCorr n (matrixOfEdge n mu))
          * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
      = ∫ mu : Cn3Torus.Edge n → ℝ,
          Set.indicator (edgeCoreRegionD n D t) (quarticCoreDensity β t n) mu := by
            symm
            simpa [quarticCoreDensity] using
              (MeasureTheory.integral_indicator (μ := MeasureTheory.volume)
                (f := quarticCoreDensity β t n) hmeas)
    _ = ∫ mu : Cn3Torus.Edge n → ℝ, quarticCoreTrunc β D t n mu := by
          rfl
    _ ≤ Real.exp ((β ^ (2 : Nat) / 2) * (n : ℝ) * (D / t) ^ (2 : Nat))
          * gaussianF (dim n) t := hmain

/-- Quartic-core integral bound specialized to the natural radius `dim n / t`. -/
lemma quartic_core_integral_dim_bound
    (β t : ℝ) (hβ : 0 ≤ β) (ht : 0 < t)
    (n : ℕ) (hsmall : β * ((dim n : ℝ) / t) ≤ 1 / 2) :
    ∫ mu in edgeCoreRegion n t,
        Real.exp (β * t * quarticCorr n (matrixOfEdge n mu))
          * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
      ≤ Real.exp ((β ^ (2 : Nat) / 2) * (n : ℝ) * ((dim n : ℝ) / t) ^ (2 : Nat))
          * gaussianF (dim n) t := by
  have hset : edgeCoreRegionD n (dim n : ℝ) t = edgeCoreRegion n t := by
    ext mu
    simp [edgeCoreRegionD, edgeCoreRegion, coreRegion, sNorm_matrixOfEdge_eq]
  rw [← hset]
  exact quartic_core_integral_bound_explicit β (dim n : ℝ) t hβ (by positivity) ht hsmall n
