import RequestProject.HadamardCn3LocalGapBridge

noncomputable section

open Real MeasureTheory Filter Finset Topology
open scoped Pointwise

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-!
## Local-Gap Residual Layer

This file packages the residual contribution after the primary core region is removed.

The public theorems a reader should inspect first are:

- `primaryCoreContribution`
- `residual_estimate_quantitative`
- `cubicT_sq_core_gaussian_correction_tail_le`

The threshold bookkeeping lemmas immediately above `residual_estimate_quantitative` are
implementation detail for that theorem.
-/

def primaryCoreContribution (n t : ℕ) : ℝ :=
  Cn3Torus.texPrefactor n
    * ∫ mu in edgeCoreRegion n (t : ℝ), Complex.re (Cn3Torus.psi n mu ^ (4 * t))

private lemma residual_threshold_parameters
    {cSm CSm cBig CBig cExp CExp cTr CTr : ℝ}
    (hcSm_pos : 0 < cSm) (hCSm_pos : 0 < CSm)
    (hcBig_pos : 0 < cBig) (hCBig_pos : 0 < CBig)
    (hcExp_pos : 0 < cExp) (hCExp_pos : 0 < CExp)
    (hcTr_pos : 0 < cTr) (hCTr_pos : 0 < CTr) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      c ≤ (1 / 32 : ℝ) ∧ c ≤ cSm ∧ c ≤ cBig ∧ c ≤ cExp ∧ c ≤ cTr ∧
      CSm ≤ C ∧ CBig ≤ C ∧ CExp ≤ C ∧ CTr ≤ C ∧
      (1 : ℝ) ≤ C ∧ 1 / (Cn3Torus.delta ^ (2 : Nat)) ≤ C := by
  let c : ℝ := min (1 / 32 : ℝ) (min cSm (min cBig (min cExp cTr)))
  let Cgeom : ℝ := max 1 (1 / (Cn3Torus.delta ^ (2 : Nat)))
  let C : ℝ := max Cgeom (max CSm (max CBig (max CExp CTr)))
  refine ⟨c, C, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold c
    positivity
  · have hCgeom_pos : 0 < Cgeom := by
      unfold Cgeom
      have hdelta : 0 < Cn3Torus.delta := Cn3Torus.delta_pos
      positivity
    unfold C
    positivity [hCgeom_pos]
  · unfold c
    exact min_le_left _ _
  · unfold c
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  · unfold c
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  · unfold c
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  · unfold c
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  · unfold C
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  · unfold C
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
  · unfold C
    exact le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
      (le_max_right _ _)
  · unfold C
    exact le_trans
      (le_trans
        (le_trans
          (le_max_right _ _)
          (le_max_right _ _))
        (le_max_right _ _))
      (le_max_right _ _)
  · have hCgeom_one : (1 : ℝ) ≤ Cgeom := by
      unfold Cgeom
      exact le_max_left _ _
    unfold C
    exact le_trans hCgeom_one (le_max_left _ _)
  · unfold C Cgeom
    exact le_trans (le_max_right _ _) (le_max_left _ _)

private lemma residual_transport_scaled
    (n t : ℕ) {c cTr CTr : ℝ}
    (hn : 3 ≤ n)
    (ht_tr : (t : ℝ) ≥ CTr * (n : ℝ) ^ (3 : Nat))
    (ht_pos : 0 < (t : ℝ))
    (hc_le_tr : c ≤ cTr)
    (htransportExp :
      ∀ n : ℕ, 3 ≤ n →
      ∀ t : ℕ, (t : ℝ) ≥ CTr * ↑n ^ (3 : Nat) →
        Real.exp (-(1 / 2 : ℝ) * (t : ℝ))
          ≤ Real.exp (-(cTr * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ)) :
    |normalizedCount n (4 * t) - Cn3Torus.texPrefactor n * Cn3Torus.localIntegral n t|
      ≤ Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
  have hn2 : 2 ≤ n := by omega
  have htransport_half :
      |normalizedCount n (4 * t) - Cn3Torus.texPrefactor n * Cn3Torus.localIntegral n t|
        ≤ Real.exp (-(1 / 2 : ℝ) * (t : ℝ)) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (normalizedCount_sub_texPrefactor_mul_localIntegral_abs_le_exp_neg_half_t n t hn2)
  have hscale_nonneg : 0 ≤ gaussianScale n (t : ℝ) := le_of_lt (gaussianScale_pos n ht_pos)
  refine le_trans htransport_half ?_
  refine le_trans (htransportExp n hn t ht_tr) ?_
  refine mul_le_mul_of_nonneg_right ?_ hscale_nonneg
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (n : ℝ), hc_le_tr]

private lemma residual_annulus_scaled
    (n t : ℕ) {c C₆ r₁ : ℝ}
    (hn : 3 ≤ n) (hdim : 1 ≤ dim n) (ht_one : 1 ≤ t) (ht_pos : 0 < (t : ℝ))
    (hC₆_nonneg : 0 ≤ C₆) (hc_le_ann : c ≤ (1 / 32 : ℝ))
    (hA_raw :
      ∫ mu in ((edgeBox n Cn3Torus.delta ∩ edgeEuclidBall n r₁) \ edgeCoreRegion n (t : ℝ)),
          ‖Cn3Torus.psi n mu‖ ^ (4 * t)
        ≤ C₆ * Real.exp (-((dim n : ℝ) / 8)) * coreMass (dim n) (t : ℝ)) :
    Cn3Torus.texPrefactor n
        * ∫ mu in ((edgeBox n Cn3Torus.delta ∩ edgeEuclidBall n r₁) \ edgeCoreRegion n (t : ℝ)),
            ‖Cn3Torus.psi n mu‖ ^ (4 * t)
      ≤ C₆ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
  have hn2 : 2 ≤ n := by omega
  have hT_nonneg : 0 ≤ Cn3Torus.texPrefactor n := texPrefactor_nonneg n
  have hscale_eq :
      Cn3Torus.texPrefactor n * gaussianF (dim n) (t : ℝ) = gaussianScale n (t : ℝ) := by
    exact gaussianScale_eq_texPrefactor_mul_gaussianF n hn2 (t : ℝ) ht_pos
  have hscale_nonneg : 0 ≤ gaussianScale n (t : ℝ) := le_of_lt (gaussianScale_pos n ht_pos)
  have hcore_to_scale :
      Cn3Torus.texPrefactor n * coreMass (dim n) (t : ℝ) ≤ gaussianScale n (t : ℝ) := by
    calc
      Cn3Torus.texPrefactor n * coreMass (dim n) (t : ℝ)
          ≤ Cn3Torus.texPrefactor n * gaussianF (dim n) (t : ℝ) := by
            gcongr
            exact coreMass_le_gaussianF n (t : ℝ) ht_pos
      _ = gaussianScale n (t : ℝ) := by simpa using hscale_eq
  have hAnn_exp :
      Real.exp (-((dim n : ℝ) / 8))
        ≤ Real.exp (-((1 / 32 : ℝ) * (n : ℝ) ^ (2 : Nat))) := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      exp_neg_dim_over_eight_le_exp_neg_nsq_div_thirty_two hn2
  calc
    Cn3Torus.texPrefactor n
        * ∫ mu in ((edgeBox n Cn3Torus.delta ∩ edgeEuclidBall n r₁) \ edgeCoreRegion n (t : ℝ)),
            ‖Cn3Torus.psi n mu‖ ^ (4 * t)
      ≤ Cn3Torus.texPrefactor n
          * (C₆ * Real.exp (-((dim n : ℝ) / 8)) * coreMass (dim n) (t : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hA_raw hT_nonneg
    _ = C₆ * Real.exp (-((dim n : ℝ) / 8))
          * (Cn3Torus.texPrefactor n * coreMass (dim n) (t : ℝ)) := by ring
    _ ≤ C₆ * Real.exp (-((dim n : ℝ) / 8)) * gaussianScale n (t : ℝ) := by
          exact mul_le_mul_of_nonneg_left hcore_to_scale (mul_nonneg hC₆_nonneg (by positivity))
    _ ≤ C₆ * Real.exp (-((1 / 32 : ℝ) * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hAnn_exp hC₆_nonneg) hscale_nonneg
    _ ≤ C₆ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
          refine mul_le_mul_of_nonneg_right ?_ hscale_nonneg
          refine mul_le_mul_of_nonneg_left ?_ hC₆_nonneg
          apply Real.exp_le_exp.mpr
          nlinarith [sq_nonneg (n : ℝ), hc_le_ann]

private lemma residual_far_shell_scaled
    (n t : ℕ) {c r₁ qSm qBig aFar cSm CSm cBig CBig cExp CExp : ℝ}
    (hn : 3 ≤ n) (ht_one : 1 ≤ t) (ht_pos : 0 < (t : ℝ))
    (hc_le_sm : c ≤ cSm) (hc_le_big : c ≤ cBig) (hc_le_exp : c ≤ cExp)
    (ht_farSm : (t : ℝ) ≥ CSm * (n : ℝ) ^ (3 : Nat))
    (ht_farBig : (t : ℝ) ≥ CBig * (n : ℝ) ^ (3 : Nat))
    (ht_farExp : (t : ℝ) ≥ CExp * (n : ℝ) ^ (3 : Nat))
    (hB_le_far :
      ∫ mu in ((edgeBox n Cn3Torus.delta \ edgeEuclidBall n r₁) \ edgeCoreRegion n (t : ℝ)),
          ‖Cn3Torus.psi n mu‖ ^ (4 * t)
        ≤ ∫ mu in edgeEvenFarShell n r₁, ‖Cn3Torus.psi n mu‖ ^ (4 * t))
    (hfarShell :
      ∀ (n t : ℕ),
        2 ≤ n →
          1 ≤ t →
            Cn3Torus.texPrefactor n
              * ∫ mu in edgeEvenFarShell n r₁, ‖Cn3Torus.psi n mu‖ ^ (4 * t)
                ≤ qSm ^ (4 * t) + qBig ^ (4 * t)
                    + Real.exp (-(aFar * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ)))))
    (hfarSm :
      ∀ n : ℕ, 3 ≤ n →
      ∀ t : ℕ, (t : ℝ) ≥ CSm * ↑n ^ (3 : Nat) →
        qSm ^ (4 * t) ≤ Real.exp (-(cSm * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ))
    (hfarBig :
      ∀ n : ℕ, 3 ≤ n →
      ∀ t : ℕ, (t : ℝ) ≥ CBig * ↑n ^ (3 : Nat) →
        qBig ^ (4 * t) ≤ Real.exp (-(cBig * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ))
    (hfarExp :
      ∀ n : ℕ, 3 ≤ n →
      ∀ t : ℕ, (t : ℝ) ≥ CExp * ↑n ^ (3 : Nat) →
        Real.exp (-(aFar * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ))))
          ≤ Real.exp (-(cExp * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ)) :
    Cn3Torus.texPrefactor n
        * ∫ mu in ((edgeBox n Cn3Torus.delta \ edgeEuclidBall n r₁) \ edgeCoreRegion n (t : ℝ)),
            ‖Cn3Torus.psi n mu‖ ^ (4 * t)
      ≤ (3 : ℝ) * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
  have hn2 : 2 ≤ n := by omega
  have hscale_nonneg : 0 ≤ gaussianScale n (t : ℝ) := le_of_lt (gaussianScale_pos n ht_pos)
  have hraw :
      Cn3Torus.texPrefactor n
          * ∫ mu in ((edgeBox n Cn3Torus.delta \ edgeEuclidBall n r₁) \ edgeCoreRegion n (t : ℝ)),
              ‖Cn3Torus.psi n mu‖ ^ (4 * t)
        ≤ qSm ^ (4 * t) + qBig ^ (4 * t)
            + Real.exp (-(aFar * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ)))) := by
    calc
      Cn3Torus.texPrefactor n
          * ∫ mu in ((edgeBox n Cn3Torus.delta \ edgeEuclidBall n r₁) \ edgeCoreRegion n (t : ℝ)),
              ‖Cn3Torus.psi n mu‖ ^ (4 * t)
        ≤ Cn3Torus.texPrefactor n * ∫ mu in edgeEvenFarShell n r₁, ‖Cn3Torus.psi n mu‖ ^ (4 * t) := by
              exact mul_le_mul_of_nonneg_left hB_le_far (texPrefactor_nonneg n)
      _ ≤ qSm ^ (4 * t) + qBig ^ (4 * t)
            + Real.exp (-(aFar * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ)))) := by
              simpa using hfarShell n t hn2 ht_one
  have hsm0 : qSm ^ (4 * t) ≤ Real.exp (-(cSm * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) :=
    hfarSm n hn t ht_farSm
  have hbig0 : qBig ^ (4 * t) ≤ Real.exp (-(cBig * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) :=
    hfarBig n hn t ht_farBig
  have hexp0 :
      Real.exp (-(aFar * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ))))
        ≤ Real.exp (-(cExp * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) :=
    hfarExp n hn t ht_farExp
  have hsm : qSm ^ (4 * t) ≤ Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
    refine le_trans hsm0 ?_
    refine mul_le_mul_of_nonneg_right ?_ hscale_nonneg
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (n : ℝ), hc_le_sm]
  have hbig : qBig ^ (4 * t) ≤ Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
    refine le_trans hbig0 ?_
    refine mul_le_mul_of_nonneg_right ?_ hscale_nonneg
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (n : ℝ), hc_le_big]
  have hexp :
      Real.exp (-(aFar * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ))))
        ≤ Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
    refine le_trans hexp0 ?_
    refine mul_le_mul_of_nonneg_right ?_ hscale_nonneg
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (n : ℝ), hc_le_exp]
  calc
    Cn3Torus.texPrefactor n
        * ∫ mu in ((edgeBox n Cn3Torus.delta \ edgeEuclidBall n r₁) \ edgeCoreRegion n (t : ℝ)),
            ‖Cn3Torus.psi n mu‖ ^ (4 * t)
      ≤ qSm ^ (4 * t) + qBig ^ (4 * t)
          + Real.exp (-(aFar * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ)))) := hraw
    _ ≤ Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ)
          + Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ)
          + Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
            gcongr
    _ = (3 : ℝ) * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
          ring

private lemma residual_local_to_core_scaled
    (n t : ℕ) {c C₆ r₁ qSm qBig aFar cSm CSm cBig CBig cExp CExp : ℝ}
    (hn : 3 ≤ n) (hdim : 1 ≤ dim n) (ht_one : 1 ≤ t) (ht_pos : 0 < (t : ℝ))
    (hC₆_nonneg : 0 ≤ C₆) (hr₁_pos : 0 < r₁)
    (hbox : (dim n : ℝ) / (t : ℝ) ≤ Cn3Torus.delta ^ (2 : Nat))
    (hc_le_ann : c ≤ (1 / 32 : ℝ))
    (hc_le_sm : c ≤ cSm) (hc_le_big : c ≤ cBig) (hc_le_exp : c ≤ cExp)
    (ht_farSm : (t : ℝ) ≥ CSm * (n : ℝ) ^ (3 : Nat))
    (ht_farBig : (t : ℝ) ≥ CBig * (n : ℝ) ^ (3 : Nat))
    (ht_farExp : (t : ℝ) ≥ CExp * (n : ℝ) ^ (3 : Nat))
    (hannulus :
      ∀ (n : ℕ),
        1 ≤ dim n →
          ∀ {r delta : ℝ},
            0 < r →
              r ≤ r₁ →
                ∀ (t : ℕ),
                  1 ≤ t →
                    ∫ mu in (edgeBox n delta ∩ edgeEuclidBall n r) \ edgeCoreRegion n (t : ℝ),
                        ‖Cn3Torus.psi n mu‖ ^ (4 * t)
                      ≤ C₆ * Real.exp (-((dim n : ℝ) / 8)) * coreMass (dim n) (t : ℝ))
    (hfarShell :
      ∀ (n t : ℕ),
        2 ≤ n →
          1 ≤ t →
            Cn3Torus.texPrefactor n
              * ∫ mu in edgeEvenFarShell n r₁, ‖Cn3Torus.psi n mu‖ ^ (4 * t)
                ≤ qSm ^ (4 * t) + qBig ^ (4 * t)
                    + Real.exp (-(aFar * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ)))))
    (hfarSm :
      ∀ n : ℕ, 3 ≤ n →
      ∀ t : ℕ, (t : ℝ) ≥ CSm * ↑n ^ (3 : Nat) →
        qSm ^ (4 * t) ≤ Real.exp (-(cSm * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ))
    (hfarBig :
      ∀ n : ℕ, 3 ≤ n →
      ∀ t : ℕ, (t : ℝ) ≥ CBig * ↑n ^ (3 : Nat) →
        qBig ^ (4 * t) ≤ Real.exp (-(cBig * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ))
    (hfarExp :
      ∀ n : ℕ, 3 ≤ n →
      ∀ t : ℕ, (t : ℝ) ≥ CExp * ↑n ^ (3 : Nat) →
        Real.exp (-(aFar * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ))))
          ≤ Real.exp (-(cExp * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ)) :
    |Cn3Torus.texPrefactor n * Cn3Torus.localIntegral n t - primaryCoreContribution n t|
      ≤ (C₆ + 3) * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
  have hn2 : 2 ≤ n := by omega
  let T : ℝ := Cn3Torus.texPrefactor n
  let core : Set (Cn3Torus.Edge n → ℝ) := edgeCoreRegion n (t : ℝ)
  let Jψ : ℝ := ∫ mu in core, Complex.re (Cn3Torus.psi n mu ^ (4 * t))
  let f : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu => ‖Cn3Torus.psi n mu‖ ^ (4 * t)
  let A : Set (Cn3Torus.Edge n → ℝ) := ((edgeBox n Cn3Torus.delta ∩ edgeEuclidBall n r₁) \ core)
  let B : Set (Cn3Torus.Edge n → ℝ) := ((edgeBox n Cn3Torus.delta \ edgeEuclidBall n r₁) \ core)
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact texPrefactor_nonneg n
  have hA_raw :
      ∫ mu in A, f mu ≤ C₆ * Real.exp (-((dim n : ℝ) / 8)) * coreMass (dim n) (t : ℝ) := by
    simpa [A, core, f] using hannulus n hdim hr₁_pos le_rfl t ht_one
  have hB_meas : MeasurableSet B := by
    dsimp [B, core]
    exact ((edgeBox_isCompact n Cn3Torus.delta).measurableSet.diff
      (measurableSet_edgeEuclidBall n r₁)).diff (measurableSet_edgeCoreRegion n (t : ℝ))
  have hB_subset_far : B ⊆ edgeEvenFarShell n r₁ := by
    intro mu hmu
    have hboxmu : mu ∈ edgeBox n Cn3Torus.delta := hmu.1.1
    have hnotball : mu ∉ edgeEuclidBall n r₁ := hmu.1.2
    have hsq_not : ¬ Cn3Torus.sqNormEdge n mu ≤ r₁ ^ (2 : Nat) := by
      intro hsq
      exact hnotball ((mem_edgeEuclidBall_iff n r₁ mu).2 hsq)
    have hsq_ge : r₁ ^ (2 : Nat) ≤ Cn3Torus.sqNormEdge n mu := by
      exact le_of_not_ge hsq_not
    exact (mem_edgeEvenFarShell_iff n r₁ mu).2
      ⟨edgeBox_delta_subset_pi_div_four n hboxmu, hsq_ge⟩
  have hf_far_int :
      MeasureTheory.IntegrableOn f (edgeEvenFarShell n r₁) := by
    simpa [f, MeasureTheory.IntegrableOn] using
      (((Cn3Torus.continuous_psi n).norm.pow (4 * t)).continuousOn.integrableOn_compact
        (edgeBox_isCompact n (π / 4))).mono_set
        (edgeEvenFarShell_subset_edgeBox n r₁)
  have hB_le_far :
      ∫ mu in B, f mu ≤ ∫ mu in edgeEvenFarShell n r₁, f mu := by
    exact integralOn_mono_of_nonneg hB_subset_far hB_meas (measurableSet_edgeEvenFarShell n r₁)
      hf_far_int (Filter.Eventually.of_forall (fun _ => by positivity))
  have hAnn_scaled :=
    residual_annulus_scaled n t hn hdim ht_one ht_pos hC₆_nonneg hc_le_ann hA_raw
  have hfar_scaled :=
    residual_far_shell_scaled n t hn ht_one ht_pos hc_le_sm hc_le_big hc_le_exp
      ht_farSm ht_farBig ht_farExp hB_le_far hfarShell hfarSm hfarBig hfarExp
  have hlocal_core_raw :
      |Cn3Torus.localIntegral n t - Jψ| ≤ (∫ mu in A, f mu) + ∫ mu in B, f mu := by
    simpa [A, B, core, Jψ, f] using
      localIntegral_sub_core_abs_le_annulus_plus_far n t hbox r₁
  have hmul := mul_le_mul_of_nonneg_left hlocal_core_raw hT_nonneg
  have habs :
      |T * Cn3Torus.localIntegral n t - primaryCoreContribution n t|
        = T * |Cn3Torus.localIntegral n t - Jψ| := by
    rw [show T * Cn3Torus.localIntegral n t - primaryCoreContribution n t
              = T * (Cn3Torus.localIntegral n t - Jψ) by
            simp [primaryCoreContribution, T, Jψ]
            ring,
      abs_mul, abs_of_nonneg hT_nonneg]
  have hmul' :
      T * |Cn3Torus.localIntegral n t - Jψ|
        ≤ T * (∫ mu in A, f mu) + T * (∫ mu in B, f mu) := by
    calc
      T * |Cn3Torus.localIntegral n t - Jψ|
        ≤ T * ((∫ mu in A, f mu) + ∫ mu in B, f mu) := hmul
      _ = T * (∫ mu in A, f mu) + T * (∫ mu in B, f mu) := by ring
  have hsum :
      T * (∫ mu in A, f mu) + T * (∫ mu in B, f mu)
        ≤ (C₆ + 3) * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
    calc
      T * (∫ mu in A, f mu) + T * (∫ mu in B, f mu)
        ≤ C₆ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ)
            + (3 : ℝ) * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
              exact add_le_add hAnn_scaled hfar_scaled
      _ = (C₆ + 3) * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
            ring
  calc
    |T * Cn3Torus.localIntegral n t - primaryCoreContribution n t|
      = T * |Cn3Torus.localIntegral n t - Jψ| := habs
    _ ≤ T * (∫ mu in A, f mu) + T * (∫ mu in B, f mu) := hmul'
    _ ≤ (C₆ + 3) * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := hsum

/-- After discarding the primary core region, the remaining contribution is
exponentially small in `n²` on the Gaussian scale at the `n³` threshold. -/
theorem residual_estimate_quantitative :
    ∃ c K C : ℝ, 0 < c ∧ 0 < K ∧ 0 < C ∧
      ∀ n : ℕ, 3 ≤ n →
      ∀ t : ℕ, (t : ℝ) ≥ C * ↑n ^ 3 →
        |normalizedCount n (4 * t) - primaryCoreContribution n t|
          ≤ K * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n ↑t := by
  obtain ⟨r₁, C₆, hr₁_pos, hC₆_pos, hr₁_lt, hannulus⟩ :=
    edgePrimaryLocalAnnulus_integral_bound_coreMass_uniform
  obtain ⟨qSm, qBig, aFar, hqSm_pos, hqSm_lt, hqBig_pos, hqBig_lt, haFar_pos, hfarShell⟩ :=
    edgeEvenFarShell_contribution_bound_Jsplit r₁ hr₁_pos hr₁_lt
  obtain ⟨cSm, CSm, hcSm_pos, hCSm_pos, hfarSm⟩ :=
    qpow_le_exp_neg_nsq_mul_gaussianScale_uniform_ge_three qSm hqSm_pos hqSm_lt
  obtain ⟨cBig, CBig, hcBig_pos, hCBig_pos, hfarBig⟩ :=
    qpow_le_exp_neg_nsq_mul_gaussianScale_uniform_ge_three qBig hqBig_pos hqBig_lt
  obtain ⟨cExp, CExp, hcExp_pos, hCExp_pos, hfarExp⟩ :=
    exp_neg_mul_t_div_n_two_thirds_le_exp_neg_nsq_mul_gaussianScale_uniform_ge_three aFar haFar_pos
  obtain ⟨cTr, CTr, hcTr_pos, hCTr_pos, htransportExp⟩ :=
    exp_neg_mul_t_le_exp_neg_nsq_mul_gaussianScale_uniform_ge_three (1 / 2 : ℝ) (by norm_num)
  obtain ⟨c, C, hc_pos, hC_pos, hc_le_ann, hc_le_sm, hc_le_big, hc_le_exp, hc_le_tr,
      hCSm_le_C, hCBig_le_C, hCExp_le_C, hCTr_le_C, hC_one, hCgeom_inv⟩ :=
    residual_threshold_parameters hcSm_pos hCSm_pos hcBig_pos hCBig_pos hcExp_pos hCExp_pos hcTr_pos hCTr_pos
  let K : ℝ := C₆ + 4
  have hK_pos : 0 < K := by
    unfold K
    positivity [hC₆_pos]
  refine ⟨c, K, C, hc_pos, hK_pos, hC_pos, ?_⟩
  intro n hn t ht
  have hn2 : 2 ≤ n := by omega
  have hn_pos : 0 < n := by omega
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hdim : 1 ≤ dim n := one_le_dim_of_three_le n hn
  have ht_pos : (0 : ℝ) < (t : ℝ) := by
    have : 0 < C * (n : ℝ) ^ (3 : Nat) := by positivity [hC_pos, hnR_pos]
    linarith
  have ht_one_real : (1 : ℝ) ≤ (t : ℝ) := by
    have hn_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
    have hn_cube_ge_one : (1 : ℝ) ≤ (n : ℝ) ^ (3 : Nat) := by
      calc
        (1 : ℝ) = (1 : ℝ) ^ (3 : Nat) := by norm_num
        _ ≤ (n : ℝ) ^ (3 : Nat) := by
            gcongr
    have : (1 : ℝ) ≤ C * (n : ℝ) ^ (3 : Nat) := by nlinarith
    linarith
  have ht_one : 1 ≤ t := by exact_mod_cast ht_one_real
  have h_invC_le_delta : 1 / C ≤ Cn3Torus.delta ^ (2 : Nat) := by
    have hdelta_sq_pos : 0 < Cn3Torus.delta ^ (2 : Nat) := by
      have hdelta : 0 < Cn3Torus.delta := Cn3Torus.delta_pos
      positivity
    calc
      1 / C ≤ 1 / (1 / (Cn3Torus.delta ^ (2 : Nat))) := by
            exact one_div_le_one_div_of_le (one_div_pos.mpr hdelta_sq_pos) hCgeom_inv
      _ = Cn3Torus.delta ^ (2 : Nat) := by
            field_simp [hdelta_sq_pos.ne']
  have hbox : (dim n : ℝ) / (t : ℝ) ≤ Cn3Torus.delta ^ (2 : Nat) := by
    have hdt_small := dim_div_t_le_inv_C n t hC_pos hC_one hn_pos ht
    exact le_trans hdt_small h_invC_le_delta
  have ht_farSm : (t : ℝ) ≥ CSm * (n : ℝ) ^ (3 : Nat) := by nlinarith
  have ht_farBig : (t : ℝ) ≥ CBig * (n : ℝ) ^ (3 : Nat) := by nlinarith
  have ht_farExp : (t : ℝ) ≥ CExp * (n : ℝ) ^ (3 : Nat) := by nlinarith
  have ht_tr : (t : ℝ) ≥ CTr * (n : ℝ) ^ (3 : Nat) := by nlinarith
  have htransport_scaled :=
    residual_transport_scaled n t hn ht_tr ht_pos hc_le_tr htransportExp
  have hlocal_core_scaled :=
    residual_local_to_core_scaled n t hn hdim ht_one ht_pos hC₆_pos.le hr₁_pos hbox hc_le_ann hc_le_sm hc_le_big hc_le_exp
      ht_farSm ht_farBig ht_farExp hannulus hfarShell hfarSm hfarBig hfarExp
  calc
    |normalizedCount n (4 * t) - primaryCoreContribution n t|
      = |(normalizedCount n (4 * t) - Cn3Torus.texPrefactor n * Cn3Torus.localIntegral n t)
          + (Cn3Torus.texPrefactor n * Cn3Torus.localIntegral n t - primaryCoreContribution n t)| := by
            congr 1
            ring
    _ ≤ |normalizedCount n (4 * t) - Cn3Torus.texPrefactor n * Cn3Torus.localIntegral n t|
          + |Cn3Torus.texPrefactor n * Cn3Torus.localIntegral n t - primaryCoreContribution n t| := by
            simpa using abs_add_le
              (normalizedCount n (4 * t) - Cn3Torus.texPrefactor n * Cn3Torus.localIntegral n t)
              (Cn3Torus.texPrefactor n * Cn3Torus.localIntegral n t - primaryCoreContribution n t)
    _ ≤ Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ)
          + (C₆ + 3) * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
            exact add_le_add htransport_scaled hlocal_core_scaled
    _ = K * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n (t : ℝ) := by
          unfold K
          ring

/-- The Gaussian mass outside the dynamic core is exponentially small in the edge-space
dimension. This is the complement form of `coreMass_gap_le_exp_gaussianF`. -/
lemma edgeCoreRegion_compl_gaussian_integral_le_exp_neg_dim_mul_gaussianF :
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, ∀ t : ℝ, 1 ≤ t →
        ∫ mu in (edgeCoreRegion n t)ᶜ,
            Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
          ≤ Real.exp (-(c * (dim n : ℝ))) * gaussianF (dim n) t := by
  obtain ⟨c, hc_pos, hgap⟩ := coreMass_gap_le_exp_gaussianF
  refine ⟨c, hc_pos, ?_⟩
  intro n t ht
  let core : Set (Cn3Torus.Edge n → ℝ) := edgeCoreRegion n t
  let g : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu =>
    Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
  have hcore_meas : MeasurableSet core := by
    simpa [core] using measurableSet_edgeCoreRegion n t
  have hg_int : MeasureTheory.Integrable g := by
    simpa [g, mul_assoc] using gaussian_integrable_edge n (2 * t) (by positivity)
  have hgauss :
      ∫ mu : Cn3Torus.Edge n → ℝ, g mu = gaussianF (dim n) t := by
    simpa [g] using gaussian_integral_formula_edge n (2 * t) (by positivity)
  have hcore :
      ∫ mu in core, g mu = coreMass (dim n) t := by
    simpa [core, g] using
      (coreMass_eq_edgeCoreRegion_gaussian_integral n t).symm
  have hsum :
      (∫ mu in core, g mu) + ∫ mu in coreᶜ, g mu = ∫ mu, g mu := by
    simpa [core] using
      (MeasureTheory.integral_add_compl (μ := MeasureTheory.volume) (f := g) hcore_meas hg_int)
  have hcompl :
      ∫ mu in coreᶜ, g mu = gaussianF (dim n) t - coreMass (dim n) t := by
    rw [hgauss, hcore] at hsum
    linarith
  have hcore_le : coreMass (dim n) t ≤ gaussianF (dim n) t := by
    exact coreMass_le_gaussianF n t (by linarith)
  calc
    ∫ mu in coreᶜ, g mu = gaussianF (dim n) t - coreMass (dim n) t := hcompl
    _ = |coreMass (dim n) t - gaussianF (dim n) t| := by
          rw [abs_of_nonpos]
          · ring
          · exact sub_nonpos.mpr hcore_le
    _ ≤ Real.exp (-(c * (dim n : ℝ))) * gaussianF (dim n) t := hgap n t ht

/-- Replacing the core-restricted cubic second moment by the exact full Gaussian moment
costs only an exponentially small factor in the dimension. -/
lemma cubicT_sq_core_gaussian_correction_tail_le :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∀ n : ℕ, ∀ t : ℝ, 1 ≤ t →
        |((8 : ℝ) * t ^ (2 : Nat)
            * ∫ mu in edgeCoreRegion n t,
                (cubicT n (matrixOfEdge n mu)) ^ (2 : Nat)
                  * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu))
            - ((Nat.choose n 3 : ℝ) / (8 * t)) * gaussianF (dim n) t|
          ≤ K * ((n : ℝ) ^ (3 : Nat) / t)
              * Real.exp (-(c * (dim n : ℝ))) * gaussianF (dim n) t := by
  obtain ⟨c0, hc0_pos, htailMass⟩ := edgeCoreRegion_compl_gaussian_integral_le_exp_neg_dim_mul_gaussianF
  let C4 : ℝ := ((7 : ℝ) * (6 : ℝ) ^ (12 : Nat) * gaussianEvenMomentEnvelope 6 ^ 6)
  let K : ℝ := (8 : ℝ) * Real.sqrt C4
  have hC4_pos : 0 < C4 := by
    unfold C4
    have henv1 : 1 ≤ gaussianEvenMomentEnvelope 6 := gaussianEvenMomentEnvelope_one_le 6
    positivity
  have hK_pos : 0 < K := by
    have hsqrt_pos : 0 < Real.sqrt C4 := Real.sqrt_pos.2 hC4_pos
    unfold K
    positivity
  refine ⟨c0 / 2, K, by linarith, hK_pos, ?_⟩
  intro n t ht
  have ht_pos : 0 < t := by linarith
  let core : Set (Cn3Torus.Edge n → ℝ) := edgeCoreRegion n t
  let tail : Set (Cn3Torus.Edge n → ℝ) := coreᶜ
  let μ : MeasureTheory.Measure (Cn3Torus.Edge n → ℝ) := MeasureTheory.volume.restrict tail
  let f : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu =>
    (cubicT n (matrixOfEdge n mu)) ^ (2 : Nat)
      * Real.exp (-t * Cn3Torus.sqNormEdge n mu)
  let g : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu =>
    Real.exp (-t * Cn3Torus.sqNormEdge n mu)
  have htail_meas : MeasurableSet tail := by
    simpa [tail, core] using (measurableSet_edgeCoreRegion n t).compl
  have hf_ae : MeasureTheory.AEStronglyMeasurable f μ := by
    have hcont : Continuous f := by
      have hcub :
          Continuous (fun mu : Cn3Torus.Edge n → ℝ => cubicT n (matrixOfEdge n mu)) :=
        (continuous_cubicT n).comp (continuous_matrixOfEdge n)
      have hsq :
          Continuous (fun mu : Cn3Torus.Edge n → ℝ => Cn3Torus.sqNormEdge n mu) :=
        Cn3Torus.continuous_sqNormEdge n
      dsimp [f]
      fun_prop
    exact hcont.aestronglyMeasurable
  have hg_ae : MeasureTheory.AEStronglyMeasurable g μ := by
    have hcont : Continuous g := by
      have hsq :
          Continuous (fun mu : Cn3Torus.Edge n → ℝ => Cn3Torus.sqNormEdge n mu) :=
        Cn3Torus.continuous_sqNormEdge n
      dsimp [g]
      fun_prop
    exact hcont.aestronglyMeasurable
  have hf_nonneg : 0 ≤ᵐ[μ] f := by
    exact Filter.Eventually.of_forall (fun _ => by
      dsimp [f]
      positivity)
  have hg_nonneg : 0 ≤ᵐ[μ] g := by
    exact Filter.Eventually.of_forall (fun _ => by
      dsimp [g]
      positivity)
  have hf_sq_int : MeasureTheory.Integrable (fun x => f x ^ (2 : Nat)) μ := by
    have hfull :
        MeasureTheory.Integrable
          (fun mu : Cn3Torus.Edge n → ℝ =>
            (cubicT n (matrixOfEdge n mu)) ^ (4 : Nat)
              * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)) := by
      simpa using cubicT_fourth_full_gaussian_integrable n t ht_pos
    have hEq :
        (fun x => f x ^ (2 : Nat))
          = (fun mu : Cn3Torus.Edge n → ℝ =>
              (cubicT n (matrixOfEdge n mu)) ^ (4 : Nat)
                * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)) := by
      funext x
      dsimp [f]
      rw [pow_two]
      calc
        ((cubicT n (matrixOfEdge n x)) ^ (2 : Nat)
              * Real.exp (-t * Cn3Torus.sqNormEdge n x))
            * ((cubicT n (matrixOfEdge n x)) ^ (2 : Nat)
                * Real.exp (-t * Cn3Torus.sqNormEdge n x))
            = (cubicT n (matrixOfEdge n x)) ^ (4 : Nat)
                * (Real.exp (-t * Cn3Torus.sqNormEdge n x)
                    * Real.exp (-t * Cn3Torus.sqNormEdge n x)) := by
              ring
        _ = (cubicT n (matrixOfEdge n x)) ^ (4 : Nat)
                * Real.exp (-2 * t * Cn3Torus.sqNormEdge n x) := by
              rw [← Real.exp_add]
              congr 1
              ring
    simpa [μ, tail, hEq] using hfull.integrableOn
  have hg_sq_int : MeasureTheory.Integrable (fun x => g x ^ (2 : Nat)) μ := by
    have hfull :
        MeasureTheory.Integrable
          (fun mu : Cn3Torus.Edge n → ℝ =>
            Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)) := by
      simpa [mul_assoc] using gaussian_integrable_edge n (2 * t) (by positivity)
    have hEq :
        (fun x => g x ^ (2 : Nat))
          = (fun mu : Cn3Torus.Edge n → ℝ =>
              Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)) := by
      funext x
      dsimp [g]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    simpa [μ, tail, hEq] using hfull.integrableOn
  have hcs := cs_helper μ hf_ae hg_ae hf_nonneg hg_nonneg hf_sq_int hg_sq_int
  have hleft_eq :
      ∫ x, f x * g x ∂μ
        = ∫ mu in tail,
            (cubicT n (matrixOfEdge n mu)) ^ (2 : Nat)
              * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu) := by
    simp [μ]
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall (fun x => by
      dsimp [f, g]
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring)
  have hA :
      ∫ x, f x ^ (2 : Nat) ∂μ
        ≤ (C4 * (n : ℝ) ^ (6 : Nat) / t ^ (6 : Nat)) * gaussianF (dim n) t := by
    have hEq :
        ∫ x, f x ^ (2 : Nat) ∂μ
          = ∫ mu in tail,
              (cubicT n (matrixOfEdge n mu)) ^ (4 : Nat)
                * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu) := by
      simp [μ]
      refine MeasureTheory.integral_congr_ae ?_
      exact Filter.Eventually.of_forall (fun x => by
        dsimp [f]
        have hexp :
            Real.exp (-t * Cn3Torus.sqNormEdge n x)
                * Real.exp (-t * Cn3Torus.sqNormEdge n x)
              = Real.exp (-(2 * t * Cn3Torus.sqNormEdge n x)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [pow_two]
        calc
          ((cubicT n (matrixOfEdge n x)) ^ (2 : Nat)
                * Real.exp (-t * Cn3Torus.sqNormEdge n x))
              * ((cubicT n (matrixOfEdge n x)) ^ (2 : Nat)
                  * Real.exp (-t * Cn3Torus.sqNormEdge n x))
            = (cubicT n (matrixOfEdge n x)) ^ (4 : Nat)
                * (Real.exp (-t * Cn3Torus.sqNormEdge n x)
                    * Real.exp (-t * Cn3Torus.sqNormEdge n x)) := by
              ring
          _ = (cubicT n (matrixOfEdge n x)) ^ (4 : Nat)
                * Real.exp (-(2 * t * Cn3Torus.sqNormEdge n x)) := by
              rw [hexp])
    rw [hEq]
    have hnonneg :
        0 ≤ᵐ[MeasureTheory.volume]
          fun mu : Cn3Torus.Edge n → ℝ =>
            (cubicT n (matrixOfEdge n mu)) ^ (4 : Nat)
              * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu) := by
      exact Filter.Eventually.of_forall (fun _ => by positivity)
    have hint :
        MeasureTheory.Integrable
          (fun mu : Cn3Torus.Edge n → ℝ =>
            (cubicT n (matrixOfEdge n mu)) ^ (4 : Nat)
              * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)) := by
      simpa using cubicT_fourth_full_gaussian_integrable n t ht_pos
    calc
      ∫ mu in tail,
          (cubicT n (matrixOfEdge n mu)) ^ (4 : Nat)
            * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
        ≤ ∫ mu : Cn3Torus.Edge n → ℝ,
            (cubicT n (matrixOfEdge n mu)) ^ (4 : Nat)
              * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu) := by
              simpa [tail] using MeasureTheory.setIntegral_le_integral hint hnonneg
      _ ≤ (C4 * (n : ℝ) ^ (6 : Nat) / t ^ (6 : Nat)) * gaussianF (dim n) t := by
            simpa [C4] using cubicT_fourth_full_gaussian_bound_explicit n t ht
  have hB :
      ∫ x, g x ^ (2 : Nat) ∂μ
        ≤ Real.exp (-(c0 * (dim n : ℝ))) * gaussianF (dim n) t := by
    have hEq :
        ∫ x, g x ^ (2 : Nat) ∂μ
          = ∫ mu in tail, Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu) := by
      simp [μ]
      refine MeasureTheory.integral_congr_ae ?_
      exact Filter.Eventually.of_forall (fun x => by
        dsimp [g]
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring)
    rw [hEq]
    simpa [tail, core] using htailMass n t ht
  have hgauss_nonneg : 0 ≤ gaussianF (dim n) t := by
    exact Real.rpow_nonneg (by positivity) _
  have hA_rpow :
      (∫ x, f x ^ (2 : Nat) ∂μ) ^ (1 / (2 : ℝ))
        ≤ ((C4 * (n : ℝ) ^ (6 : Nat) / t ^ (6 : Nat)) * gaussianF (dim n) t) ^ (1 / (2 : ℝ)) := by
    exact Real.rpow_le_rpow (by positivity) hA (by norm_num)
  have hB_rpow :
      (∫ x, g x ^ (2 : Nat) ∂μ) ^ (1 / (2 : ℝ))
        ≤ (Real.exp (-(c0 * (dim n : ℝ))) * gaussianF (dim n) t) ^ (1 / (2 : ℝ)) := by
    exact Real.rpow_le_rpow (by positivity) hB (by norm_num)
  have hA_nonneg :
      0 ≤ ((C4 * (n : ℝ) ^ (6 : Nat) / t ^ (6 : Nat)) * gaussianF (dim n) t) ^ (1 / (2 : ℝ)) := by
    positivity
  have hprod :
      ∫ mu in tail,
          (cubicT n (matrixOfEdge n mu)) ^ (2 : Nat)
            * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
        ≤ (Real.sqrt C4 * ((n : ℝ) ^ (3 : Nat) / t ^ (3 : Nat))
              * Real.exp (-(c0 * (dim n : ℝ)) / 2))
            * gaussianF (dim n) t := by
    rw [← hleft_eq]
    calc
      ∫ x, f x * g x ∂μ
        ≤ (∫ x, f x ^ (2 : Nat) ∂μ) ^ (1 / (2 : ℝ))
            * (∫ x, g x ^ (2 : Nat) ∂μ) ^ (1 / (2 : ℝ)) := hcs
      _ ≤ ((C4 * (n : ℝ) ^ (6 : Nat) / t ^ (6 : Nat)) * gaussianF (dim n) t) ^ (1 / (2 : ℝ))
            * (∫ x, g x ^ (2 : Nat) ∂μ) ^ (1 / (2 : ℝ)) := by
              exact mul_le_mul_of_nonneg_right hA_rpow (by positivity)
      _ ≤ ((C4 * (n : ℝ) ^ (6 : Nat) / t ^ (6 : Nat)) * gaussianF (dim n) t) ^ (1 / (2 : ℝ))
            * (Real.exp (-(c0 * (dim n : ℝ))) * gaussianF (dim n) t) ^ (1 / (2 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hB_rpow hA_nonneg
      _ = (Real.sqrt C4 * ((n : ℝ) ^ (3 : Nat) / t ^ (3 : Nat))
              * Real.exp (-(c0 * (dim n : ℝ)) / 2))
            * gaussianF (dim n) t := by
              rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
              have hsqrtA :
                  Real.sqrt ((C4 * (n : ℝ) ^ (6 : Nat) / t ^ (6 : Nat)) * gaussianF (dim n) t)
                    = (Real.sqrt C4 * ((n : ℝ) ^ (3 : Nat) / t ^ (3 : Nat)))
                        * Real.sqrt (gaussianF (dim n) t) := by
                rw [Real.sqrt_mul (by positivity)]
                have hsq_nonneg : 0 ≤ (n : ℝ) ^ (3 : Nat) / t ^ (3 : Nat) := by positivity
                have hrewA :
                    C4 * (n : ℝ) ^ (6 : Nat) / t ^ (6 : Nat)
                      = C4 * (((n : ℝ) ^ (3 : Nat) / t ^ (3 : Nat)) ^ (2 : Nat)) := by
                  field_simp [ht_pos.ne']
                rw [hrewA, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs,
                  abs_of_nonneg hsq_nonneg]
              have hsqrtB :
                  Real.sqrt (Real.exp (-(c0 * (dim n : ℝ))) * gaussianF (dim n) t)
                    = Real.exp (-(c0 * (dim n : ℝ)) / 2)
                        * Real.sqrt (gaussianF (dim n) t) := by
                rw [Real.sqrt_mul (by positivity)]
                have hrewB :
                    Real.exp (-(c0 * (dim n : ℝ)))
                      = (Real.exp (-(c0 * (dim n : ℝ)) / 2)) ^ (2 : Nat) := by
                  rw [pow_two, ← Real.exp_add]
                  congr 1
                  ring
                rw [hrewB, Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
              rw [hsqrtA, hsqrtB]
              calc
                (Real.sqrt C4 * ((n : ℝ) ^ (3 : Nat) / t ^ (3 : Nat)) * Real.sqrt (gaussianF (dim n) t))
                    * (Real.exp (-(c0 * (dim n : ℝ)) / 2) * Real.sqrt (gaussianF (dim n) t))
                    = (Real.sqrt C4 * ((n : ℝ) ^ (3 : Nat) / t ^ (3 : Nat))
                        * Real.exp (-(c0 * (dim n : ℝ)) / 2))
                        * (Real.sqrt (gaussianF (dim n) t) * Real.sqrt (gaussianF (dim n) t)) := by
                          ring
                _ = (Real.sqrt C4 * ((n : ℝ) ^ (3 : Nat) / t ^ (3 : Nat))
                        * Real.exp (-(c0 * (dim n : ℝ)) / 2))
                        * gaussianF (dim n) t := by
                          have hsq_gauss :
                              Real.sqrt (gaussianF (dim n) t) * Real.sqrt (gaussianF (dim n) t)
                                = gaussianF (dim n) t := by
                            nlinarith [Real.sq_sqrt hgauss_nonneg]
                          rw [hsq_gauss]
  let h : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu =>
    (cubicT n (matrixOfEdge n mu)) ^ (2 : Nat)
      * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
  have hsplit :
      ((8 : ℝ) * t ^ (2 : Nat) * ∫ mu in core, h mu)
        - ((Nat.choose n 3 : ℝ) / (8 * t)) * gaussianF (dim n) t
        = -((8 : ℝ) * t ^ (2 : Nat) * ∫ mu in tail, h mu) := by
    have hfull :
        (8 : ℝ) * t ^ (2 : Nat) * ∫ mu : Cn3Torus.Edge n → ℝ, h mu
          = ((Nat.choose n 3 : ℝ) / (8 * t)) * gaussianF (dim n) t := by
      simpa [h] using cubicT_sq_full_gaussian_correction_exact n t ht_pos
    have hsum :
        (∫ mu in core, h mu) + ∫ mu in tail, h mu = ∫ mu, h mu := by
      simpa [core, tail] using
        (MeasureTheory.integral_add_compl (μ := MeasureTheory.volume) (f := h)
          (measurableSet_edgeCoreRegion n t) (by simpa [h] using cubicT_sq_gaussian_integrable_edge n t ht_pos))
    have hcore_eq :
        ∫ mu in core, h mu = (∫ mu, h mu) - ∫ mu in tail, h mu := by
      have htmp := congrArg (fun z : ℝ => z - ∫ mu in tail, h mu) hsum
      linarith
    have hcore_mul :
        (8 : ℝ) * t ^ (2 : Nat) * ∫ mu in core, h mu
          = (8 : ℝ) * t ^ (2 : Nat) * ((∫ mu, h mu) - ∫ mu in tail, h mu) := by
      exact congrArg (fun z : ℝ => (8 : ℝ) * t ^ (2 : Nat) * z) hcore_eq
    have hstep :
        ((8 : ℝ) * t ^ (2 : Nat) * ∫ mu in core, h mu)
          - ((Nat.choose n 3 : ℝ) / (8 * t)) * gaussianF (dim n) t
          =
        ((8 : ℝ) * t ^ (2 : Nat) * ((∫ mu, h mu) - ∫ mu in tail, h mu))
          - ((Nat.choose n 3 : ℝ) / (8 * t)) * gaussianF (dim n) t := by
      exact congrArg
        (fun z : ℝ => z - ((Nat.choose n 3 : ℝ) / (8 * t)) * gaussianF (dim n) t)
        hcore_mul
    have hmain :
        ((8 : ℝ) * t ^ (2 : Nat) * ∫ mu in core, h mu)
          - ((Nat.choose n 3 : ℝ) / (8 * t)) * gaussianF (dim n) t
          = -((8 : ℝ) * t ^ (2 : Nat) * ∫ mu in tail, h mu) := by
      nlinarith [hstep, hfull]
    exact hmain
  have htail_nonneg :
      0 ≤ ∫ mu in tail, h mu := by
    exact MeasureTheory.integral_nonneg (fun _ => by
      dsimp [h]
      positivity)
  calc
    |((8 : ℝ) * t ^ (2 : Nat) * ∫ mu in core, h mu)
        - ((Nat.choose n 3 : ℝ) / (8 * t)) * gaussianF (dim n) t|
      = (8 : ℝ) * t ^ (2 : Nat) * ∫ mu in tail, h mu := by
          rw [hsplit, abs_neg, abs_of_nonneg]
          positivity
    _ ≤ (8 : ℝ) * t ^ (2 : Nat)
          * ((Real.sqrt C4 * ((n : ℝ) ^ (3 : Nat) / t ^ (3 : Nat))
                * Real.exp (-(c0 * (dim n : ℝ)) / 2))
              * gaussianF (dim n) t) := by
            exact mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = ((8 : ℝ) * Real.sqrt C4)
          * ((n : ℝ) ^ (3 : Nat) / t)
          * Real.exp (-((c0 / 2) * (dim n : ℝ)))
          * gaussianF (dim n) t := by
            field_simp [ht_pos.ne']
    _ = K * ((n : ℝ) ^ (3 : Nat) / t)
          * Real.exp (-((c0 / 2) * (dim n : ℝ)))
          * gaussianF (dim n) t := by
            simp [K]


end
