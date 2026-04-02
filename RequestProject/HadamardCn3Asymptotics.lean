import RequestProject.HadamardCn3LocalGapCore

noncomputable section

open Real MeasureTheory Filter Finset Topology
open scoped Pointwise

/-!
# Intermediate Asymptotic Statements

This file contains the two intermediate asymptotic statements used to prove the
paper's final count theorems:

- `prop_primary_box`
- `normalizedCount_asymptotic`

Unlike `RequestProject.HadamardCn3ShortMain`, this file records the normalized
count and the normalized torus integral. The final count statements are kept in
`HadamardCn3ShortMain` on purpose.
-/

/-- The normalized count `N_{n,4t} / 2^(4nt)`. -/
def paperNormalizedCount (n t : ℕ) : ℝ :=
  (hadamardCount n (4 * t) : ℝ) / (2 : ℝ) ^ (4 * n * t)

/-- The raw torus integral whose normalized form computes `paperNormalizedCount n t`. -/
def paperTargetIntegral (n t : ℕ) : ℝ :=
  ∫ lam in Cn3Torus.torusBox n, Complex.re (Cn3Torus.psi n lam ^ (4 * t))

/-- The normalized torus integral representing `paperNormalizedCount n t`. -/
def paperNormalizedIntegral (n t : ℕ) : ℝ :=
  (1 / ((2 * Real.pi) ^ (Nat.choose n 2 : Nat) : ℝ)) * paperTargetIntegral n t

/-- The Gaussian main scale `A_n(t)`. -/
def paperMainScale (n t : ℕ) : ℝ :=
  2 ^ (2 * Nat.choose n 2 - n + 1 : ℤ) * (8 * π * (t : ℝ)) ^ (-(Nat.choose n 2 : ℝ) / 2)

/-- The Gaussian main term for the normalized count. -/
def paperMainTerm (n t : ℕ) : ℝ :=
  (((1 : ℝ) - ((Nat.choose n 3 : ℝ) / (8 * (t : ℝ)))) * paperMainScale n t)

/-- Fourier inversion bridge for the normalized count. -/
theorem paperNormalizedCount_eq_integral (n t : ℕ) :
    paperNormalizedCount n t = paperNormalizedIntegral n t := by
  have hmul : n * (4 * t) = 4 * n * t := by ac_rfl
  simpa [paperNormalizedCount, paperNormalizedIntegral, paperTargetIntegral, normalizedCount,
    hmul, Cn3Torus.normalizedTargetIntegral,
    Cn3Torus.targetIntegral, Cn3Torus.d] using
    (normalizedCount_eq_normalizedTargetIntegral n t)

/- Primary-box theorem `prop:primary-box`.

This states that the primary core contribution is approximated by the centered
Gaussian main term `paperMainTerm n t`, with explicit polynomial and
exponentially small error terms. -/
set_option maxHeartbeats 20000000 in
theorem prop_primary_box :
    ∃ c K C : ℝ, 0 < c ∧ 0 < K ∧ 0 < C ∧
      ∀ n : ℕ, 3 ≤ n →
      ∀ t : ℕ, (t : ℝ) ≥ C * ↑n ^ (3 : Nat) →
        |primaryCoreContribution n t - paperMainTerm n t|
          ≤ (K * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
              + K * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
              + K * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
              + K * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))))
            * paperMainScale n t := by
  obtain ⟨c₁, K₁, hc₁_pos, hK₁_pos, hstep1⟩ := exactCore_correctedCore_gap_abs_le_gaussianF_short
  obtain ⟨c₂, K₂, hc₂_pos, hK₂_pos, hstep2⟩ := correctedCore_quarticCore_gap_abs_le_gaussianF_short
  obtain ⟨c₃, K₃, hc₃_pos, hK₃_pos, hstep3⟩ := quarticCore_cubicCore_gap_abs_le_gaussianF_short
  obtain ⟨Csec, hCsec_pos, hstep4⟩ := cubic_core_second_order_gap_uniform
  obtain ⟨cCub, Kcub, hcCub_pos, hKcub_pos, hcubTail⟩ := cubicT_sq_core_gaussian_correction_tail_le
  obtain ⟨cMass, hcMass_pos, hmassGap⟩ := coreMass_gap_le_exp_gaussianF
  let K : ℝ := K₁ + K₂ + K₃ + Csec + Kcub + 1
  let c : ℝ := min (cCub / 4) (cMass / 4)
  let m : ℝ := min c₁ (min c₂ (min c₃ (1 / 16 : ℝ)))
  let C : ℝ := max 1 (1 / m)
  have hK_pos : 0 < K := by
    unfold K
    positivity
  have hm_pos : 0 < m := by
    unfold m
    positivity [hc₁_pos, hc₂_pos, hc₃_pos]
  have hC_pos : 0 < C := by
    unfold C
    positivity [hm_pos]
  have hc_pos : 0 < c := by
    unfold c
    positivity [hcCub_pos, hcMass_pos]
  refine ⟨c, K, C, hc_pos, hK_pos, hC_pos, ?_⟩
  intro n hn3 t ht
  have hn2 : 2 ≤ n := by omega
  have hdim : 1 ≤ dim n := one_le_dim_of_three_le n hn3
  have hn_pos : 0 < n := by omega
  have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
  have hC_one : (1 : ℝ) ≤ C := by
    unfold C
    exact le_max_left _ _
  have h_invC_le_m : 1 / C ≤ m := by
    calc
      1 / C ≤ 1 / (1 / m) := by
            exact one_div_le_one_div_of_le (one_div_pos.mpr hm_pos) (by unfold C; exact le_max_right _ _)
      _ = m := by
            field_simp [hm_pos.ne']
  have hm_le_c₁ : m ≤ c₁ := by
    unfold m
    exact min_le_left _ _
  have hm_le_c₂ : m ≤ c₂ := by
    unfold m
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hm_le_c₃ : m ≤ c₃ := by
    unfold m
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hm_le_sixteenth : m ≤ (1 / 16 : ℝ) := by
    unfold m
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hc_le_cCub : c ≤ cCub / 4 := by
    unfold c
    exact min_le_left _ _
  have hc_le_cMass : c ≤ cMass / 4 := by
    unfold c
    exact min_le_right _ _
  have ht_pos : (0 : ℝ) < (t : ℝ) := by
    have : 0 < C * (n : ℝ) ^ (3 : Nat) := by positivity [hC_pos, hnR_pos]
    linarith
  have ht_one_real : (1 : ℝ) ≤ (t : ℝ) := by
    have hn_cube_ge_one : (1 : ℝ) ≤ (n : ℝ) ^ (3 : Nat) := by
      calc
        (1 : ℝ) = (1 : ℝ) ^ (3 : Nat) := by norm_num
        _ ≤ (n : ℝ) ^ (3 : Nat) := by
            gcongr
    have : (1 : ℝ) ≤ C * (n : ℝ) ^ (3 : Nat) := by
      nlinarith
    linarith
  have ht_one : 1 ≤ t := by exact_mod_cast ht_one_real
  have hC_inv_le_one : 1 / C ≤ 1 := by
    simpa using (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hC_one)
  have hdt_small := dim_div_t_le_inv_C n t hC_pos hC_one hn_pos ht
  have hcube_small := n_mul_sq_dim_div_t_le_inv_C n t hC_pos hC_one hn_pos ht
  have hdt_c₁ : (dim n : ℝ) / (t : ℝ) ≤ c₁ := by
    exact le_trans hdt_small (le_trans h_invC_le_m hm_le_c₁)
  have hdt_c₂ : (dim n : ℝ) / (t : ℝ) ≤ c₂ := by
    exact le_trans hdt_small (le_trans h_invC_le_m hm_le_c₂)
  have hcube_c₂ : (n : ℝ) * (((dim n : ℝ) / (t : ℝ)) ^ (2 : Nat)) ≤ c₂ := by
    exact le_trans hcube_small (le_trans h_invC_le_m hm_le_c₂)
  have hdt_c₃ : (dim n : ℝ) / (t : ℝ) ≤ c₃ := by
    exact le_trans hdt_small (le_trans h_invC_le_m hm_le_c₃)
  have hcube_c₃ : (n : ℝ) * (((dim n : ℝ) / (t : ℝ)) ^ (2 : Nat)) ≤ c₃ := by
    exact le_trans hcube_small (le_trans h_invC_le_m hm_le_c₃)
  have hn_cube_div_t_le_one : (n : ℝ) ^ (3 : Nat) / (t : ℝ) ≤ 1 := by
    calc
      (n : ℝ) ^ (3 : Nat) / (t : ℝ) ≤ 1 / C := by
        exact n_cube_div_t_le_inv_C n t hC_pos hn_pos ht
      _ ≤ 1 := hC_inv_le_one
  let core : Set (Cn3Torus.Edge n → ℝ) := edgeCoreRegion n (t : ℝ)
  let T : ℝ := Cn3Torus.texPrefactor n
  let gf : ℝ := gaussianF (dim n) (t : ℝ)
  let Jψ : ℝ := ∫ mu in core, Complex.re (Cn3Torus.psi n mu ^ (4 * t))
  let Jcorr : ℝ := ∫ mu in core, Complex.re (correctedCoreIntegrand n t mu)
  let Jquart : ℝ := ∫ mu in core, Complex.re (quarticCoreIntegrand n t mu)
  let Jcubic : ℝ := ∫ mu in core, Complex.re (cubicCoreIntegrand n t mu)
  let JcubCorr : ℝ := (8 : ℝ) * (t : ℝ) ^ (2 : Nat)
      * ∫ mu in core,
          (cubicT n (matrixOfEdge n mu)) ^ (2 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
  let cubicChoose : ℝ := ((Nat.choose n 3 : ℝ) / (8 * (t : ℝ))) * gf
  let centerGF : ℝ :=
    ((1 : ℝ) - ((Nat.choose n 3 : ℝ) / (8 * (t : ℝ)))) * gf
  have hscale_eq : T * gf = gaussianScale n (t : ℝ) := by
    simpa [T, gf] using gaussianScale_eq_texPrefactor_mul_gaussianF n hn2 (t : ℝ) ht_pos
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact texPrefactor_nonneg n
  have hgauss_nonneg : 0 ≤ gf := by
    dsimp [gf]
    exact Real.rpow_nonneg (by positivity) _
  have hscale_nonneg : 0 ≤ gaussianScale n (t : ℝ) := by
    exact (gaussianScale_pos n ht_pos).le
  have hstep4_raw :
      |Jcubic - (coreMass (dim n) (t : ℝ) - JcubCorr)|
        ≤ (Csec * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)) * gf := by
    simpa [core, Jcubic, JcubCorr, gf, cubicCoreIntegrand_re, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
      using hstep4 n (t : ℝ) ht_one_real
  have hcub_tail_raw :
      |JcubCorr - cubicChoose|
        ≤ Kcub * ((n : ℝ) ^ (3 : Nat) / (t : ℝ))
            * Real.exp (-(cCub * (dim n : ℝ))) * gf := by
    simpa [core, JcubCorr, cubicChoose, gf, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
      using hcubTail n (t : ℝ) ht_one_real
  have hmass_raw :
      |coreMass (dim n) (t : ℝ) - gf|
        ≤ Real.exp (-(cMass * (dim n : ℝ))) * gf := by
    simpa [gf] using hmassGap n (t : ℝ) ht_one_real
  let poly2 : ℝ := (n : ℝ) ^ (2 : Nat) / (t : ℝ)
  let poly32 : ℝ := (n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ)
  let poly6 : ℝ := (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
  let expn : ℝ := Real.exp (-(c * (n : ℝ) ^ (2 : Nat)))
  have hpoly2_nonneg : 0 ≤ poly2 := by
    dsimp [poly2]
    positivity
  have hpoly32_nonneg : 0 ≤ poly32 := by
    dsimp [poly32]
    positivity
  have hpoly6_nonneg : 0 ≤ poly6 := by
    dsimp [poly6]
    positivity
  have hexpn_nonneg : 0 ≤ expn := by
    dsimp [expn]
    positivity
  have hpoly6_small :
      (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat) ≤ 1 / C := by
    have hcube_le :
        ((n : ℝ) ^ (3 : Nat) / (t : ℝ)) ^ (2 : Nat) ≤ (1 / C) ^ (2 : Nat) := by
      have hbase := n_cube_div_t_le_inv_C n t hC_pos hn_pos ht
      exact pow_le_pow_left₀ (by positivity) hbase 2
    calc
      (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
        = ((n : ℝ) ^ (3 : Nat) / (t : ℝ)) ^ (2 : Nat) := by
            field_simp [ht_pos.ne']
      _ ≤ (1 / C) ^ (2 : Nat) := hcube_le
      _ ≤ 1 / C := by
            have hnonneg : 0 ≤ 1 / C := by positivity
            nlinarith [hC_inv_le_one]
  have hstep1_poly :
      |Jψ - Jcorr| ≤ (K₁ * poly6) * gf := by
    simpa [core, Jψ, Jcorr, gf, poly6, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
      hstep1 n hn3 t ht_one hdt_c₁ (le_trans hpoly6_small (le_trans h_invC_le_m hm_le_c₁))
  have hstep2_poly :
      |Jcorr - Jquart| ≤ (K₂ * poly32) * gf := by
    simpa [core, Jcorr, Jquart, gf, poly32, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
      hstep2 n hn2 t ht_one hdt_c₂ hcube_c₂
  have hstep3_poly :
      |Jquart - Jcubic| ≤ (K₃ * poly2) * gf := by
    simpa [core, Jquart, Jcubic, gf, poly2, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
      hstep3 n t ht_one hdt_c₃ hcube_c₃
  have hstep4_poly :
      |Jcubic - (coreMass (dim n) (t : ℝ) - JcubCorr)| ≤ (Csec * poly6) * gf := by
    simpa [poly6, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hstep4_raw
  have hcub_exp :
      |JcubCorr - cubicChoose| ≤ Kcub * expn * gf := by
    calc
      |JcubCorr - cubicChoose|
        ≤ Kcub * ((n : ℝ) ^ (3 : Nat) / (t : ℝ))
            * Real.exp (-(cCub * (dim n : ℝ))) * gf := hcub_tail_raw
      _ ≤ Kcub * Real.exp (-(cCub * (dim n : ℝ))) * gf := by
            have hcoeff : (n : ℝ) ^ (3 : Nat) / (t : ℝ) ≤ 1 := hn_cube_div_t_le_one
            calc
              Kcub * ((n : ℝ) ^ (3 : Nat) / (t : ℝ))
                  * Real.exp (-(cCub * (dim n : ℝ))) * gf
                ≤ Kcub * (1 : ℝ) * Real.exp (-(cCub * (dim n : ℝ))) * gf := by
                    gcongr
              _ = Kcub * Real.exp (-(cCub * (dim n : ℝ))) * gf := by ring
      _ ≤ Kcub * Real.exp (-((cCub / 4) * (n : ℝ) ^ (2 : Nat))) * gf := by
            have hdimexp := exp_neg_c_mul_dim_le_exp_neg_c_div_four_mul_nsq hn2 hcCub_pos.le
            gcongr
      _ ≤ Kcub * expn * gf := by
            dsimp [expn]
            have hexp :
                Real.exp (-((cCub / 4) * (n : ℝ) ^ (2 : Nat)))
                  ≤ Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) := by
              have hsq_nonneg : 0 ≤ (n : ℝ) ^ (2 : Nat) := by positivity
              have hmul :
                  c * (n : ℝ) ^ (2 : Nat) ≤ (cCub / 4) * (n : ℝ) ^ (2 : Nat) := by
                exact mul_le_mul_of_nonneg_right hc_le_cCub hsq_nonneg
              apply Real.exp_le_exp.mpr
              linarith
            gcongr
  have hmass_exp :
      |coreMass (dim n) (t : ℝ) - gf| ≤ expn * gf := by
    calc
      |coreMass (dim n) (t : ℝ) - gf|
        ≤ Real.exp (-(cMass * (dim n : ℝ))) * gf := hmass_raw
      _ ≤ Real.exp (-((cMass / 4) * (n : ℝ) ^ (2 : Nat))) * gf := by
            have hdimexp := exp_neg_c_mul_dim_le_exp_neg_c_div_four_mul_nsq hn2 hcMass_pos.le
            gcongr
      _ ≤ expn * gf := by
            dsimp [expn]
            have hexp :
                Real.exp (-((cMass / 4) * (n : ℝ) ^ (2 : Nat)))
                  ≤ Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) := by
              have hsq_nonneg : 0 ≤ (n : ℝ) ^ (2 : Nat) := by positivity
              have hmul :
                  c * (n : ℝ) ^ (2 : Nat) ≤ (cMass / 4) * (n : ℝ) ^ (2 : Nat) := by
                exact mul_le_mul_of_nonneg_right hc_le_cMass hsq_nonneg
              apply Real.exp_le_exp.mpr
              linarith
            gcongr
  have htele :
      |Jψ - centerGF|
        ≤ |Jψ - Jcorr| + |Jcorr - Jquart| + |Jquart - Jcubic|
            + |Jcubic - (coreMass (dim n) (t : ℝ) - JcubCorr)|
            + |JcubCorr - cubicChoose| + |coreMass (dim n) (t : ℝ) - gf| := by
    have hcenter_eq : centerGF = gf - cubicChoose := by
      unfold centerGF cubicChoose
      ring
    have hcub_eq :
        |(coreMass (dim n) (t : ℝ) - JcubCorr) - (coreMass (dim n) (t : ℝ) - cubicChoose)|
          = |JcubCorr - cubicChoose| := by
      calc
        |(coreMass (dim n) (t : ℝ) - JcubCorr) - (coreMass (dim n) (t : ℝ) - cubicChoose)|
          = |cubicChoose - JcubCorr| := by ring_nf
        _ = |JcubCorr - cubicChoose| := by rw [abs_sub_comm]
    have hmass_eq :
        |(coreMass (dim n) (t : ℝ) - cubicChoose) - (gf - cubicChoose)|
          = |coreMass (dim n) (t : ℝ) - gf| := by
      ring_nf
    have htele' := abs_sub_le_sum_abs_sub_six Jψ Jcorr Jquart Jcubic
      (coreMass (dim n) (t : ℝ) - JcubCorr)
      (coreMass (dim n) (t : ℝ) - cubicChoose)
      (gf - cubicChoose)
    calc
      |Jψ - centerGF| = |Jψ - (gf - cubicChoose)| := by rw [hcenter_eq]
      _ ≤ |Jψ - Jcorr| + |Jcorr - Jquart| + |Jquart - Jcubic|
            + |Jcubic - (coreMass (dim n) (t : ℝ) - JcubCorr)|
            + |(coreMass (dim n) (t : ℝ) - JcubCorr) - (coreMass (dim n) (t : ℝ) - cubicChoose)|
            + |(coreMass (dim n) (t : ℝ) - cubicChoose) - (gf - cubicChoose)| := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htele'
      _ = |Jψ - Jcorr| + |Jcorr - Jquart| + |Jquart - Jcubic|
            + |Jcubic - (coreMass (dim n) (t : ℝ) - JcubCorr)|
            + |JcubCorr - cubicChoose| + |coreMass (dim n) (t : ℝ) - gf| := by
              rw [hcub_eq, hmass_eq]
  have hsum :
      |Jψ - centerGF|
        ≤ (K₁ * poly6) * gf + (K₂ * poly32) * gf + (K₃ * poly2) * gf
            + (Csec * poly6) * gf + (Kcub * expn) * gf + expn * gf := by
    nlinarith [htele, hstep1_poly, hstep2_poly, hstep3_poly, hstep4_poly, hcub_exp, hmass_exp]
  have hK₁_le : K₁ ≤ K := by
    unfold K
    nlinarith [hK₂_pos, hK₃_pos, hCsec_pos, hKcub_pos]
  have hK₂_le : K₂ ≤ K := by
    unfold K
    nlinarith [hK₁_pos, hK₃_pos, hCsec_pos, hKcub_pos]
  have hK₃_le : K₃ ≤ K := by
    unfold K
    nlinarith [hK₁_pos, hK₂_pos, hCsec_pos, hKcub_pos]
  have hCsec_le : Csec ≤ K := by
    unfold K
    nlinarith [hK₁_pos, hK₂_pos, hK₃_pos, hKcub_pos]
  have hKcub_le : Kcub ≤ K := by
    unfold K
    nlinarith [hK₁_pos, hK₂_pos, hK₃_pos, hCsec_pos]
  have hone_le_K : (1 : ℝ) ≤ K := by
    unfold K
    nlinarith [hK₁_pos, hK₂_pos, hK₃_pos, hCsec_pos, hKcub_pos]
  have hraw :
      |Jψ - centerGF|
        ≤ (K * poly2 + K * poly32 + K * poly6 + K * expn) * gf := by
    have hcoeff :
        K₁ * poly6 + K₂ * poly32 + K₃ * poly2 + Csec * poly6 + Kcub * expn + expn
          ≤ K * poly2 + K * poly32 + K * poly6 + K * expn := by
      have h1 : K₁ * poly6 ≤ K * poly6 := by
        exact mul_le_mul_of_nonneg_right hK₁_le hpoly6_nonneg
      have h2 : K₂ * poly32 ≤ K * poly32 := by
        exact mul_le_mul_of_nonneg_right hK₂_le hpoly32_nonneg
      have h3 : K₃ * poly2 ≤ K * poly2 := by
        exact mul_le_mul_of_nonneg_right hK₃_le hpoly2_nonneg
      have h4 : Csec * poly6 ≤ K * poly6 := by
        exact mul_le_mul_of_nonneg_right hCsec_le hpoly6_nonneg
      have h5 : Kcub * expn ≤ K * expn := by
        exact mul_le_mul_of_nonneg_right hKcub_le hexpn_nonneg
      have h6 : expn ≤ K * expn := by
        simpa [one_mul] using (mul_le_mul_of_nonneg_right hone_le_K hexpn_nonneg)
      nlinarith [h1, h2, h3, h4, h5, h6]
    calc
      |Jψ - centerGF|
        ≤ (K₁ * poly6) * gf + (K₂ * poly32) * gf + (K₃ * poly2) * gf
            + (Csec * poly6) * gf + (Kcub * expn) * gf + expn * gf := hsum
      _ = (K₁ * poly6 + K₂ * poly32 + K₃ * poly2 + Csec * poly6 + Kcub * expn + expn) * gf := by
            ring
      _ ≤ (K * poly2 + K * poly32 + K * poly6 + K * expn) * gf := by
            exact mul_le_mul_of_nonneg_right hcoeff hgauss_nonneg
  have hmain_eq :
      primaryCoreContribution n t
        - (((1 : ℝ) - ((Nat.choose n 3 : ℝ) / (8 * (t : ℝ))))
            * gaussianScale n ↑t)
        = T * (Jψ - centerGF) := by
    unfold primaryCoreContribution
    dsimp [T, Jψ, centerGF, gf]
    rw [← hscale_eq]
    ring
  calc
    |primaryCoreContribution n t - paperMainTerm n t|
      = |primaryCoreContribution n t
          - (((1 : ℝ) - ((Nat.choose n 3 : ℝ) / (8 * (t : ℝ))))
              * gaussianScale n ↑t)| := by
          simp [paperMainTerm, paperMainScale, gaussianScale, dim]
    _ 
      = T * |Jψ - centerGF| := by
          rw [hmain_eq, abs_mul, abs_of_nonneg hT_nonneg]
    _ ≤ T * ((K * poly2 + K * poly32 + K * poly6 + K * expn) * gf) := by
          exact mul_le_mul_of_nonneg_left hraw hT_nonneg
    _ = (K * poly2 + K * poly32 + K * poly6 + K * expn) * gaussianScale n ↑t := by
          rw [← hscale_eq]
          ring
    _ = (K * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
            + K * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
            + K * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
            + K * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))))
          * gaussianScale n ↑t := by
          dsimp [poly2, poly32, poly6, expn]
          ring
    _ = (K * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
            + K * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
            + K * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
            + K * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))))
          * paperMainScale n t := by
          simp [paperMainScale, gaussianScale, dim]

/-- Paper-facing normalized-count theorem on the Gaussian scale.

This upgrades `prop_primary_box` by adding the residual estimate, so the same
explicit center controls the full normalized count `N_{n,4t} / 2^{4nt}`. -/
theorem normalizedCount_asymptotic :
    ∃ c K C : ℝ, 0 < c ∧ 0 < K ∧ 0 < C ∧
      ∀ n : ℕ, 3 ≤ n →
      ∀ t : ℕ, (t : ℝ) ≥ C * ↑n ^ (3 : Nat) →
        |paperNormalizedCount n t - paperMainTerm n t|
          ≤ (K * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
              + K * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
              + K * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
              + K * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))))
            * paperMainScale n t := by
  obtain ⟨c₁, K₁, C₁, hc₁_pos, hK₁_pos, hC₁_pos, hcore⟩ :=
    prop_primary_box
  obtain ⟨c₂, K₂, C₂, hc₂_pos, hK₂_pos, hC₂_pos, hres⟩ :=
    residual_estimate_quantitative
  let c : ℝ := min c₁ c₂
  let K : ℝ := K₁ + K₂
  let C : ℝ := max C₁ C₂
  refine ⟨c, K, C, by positivity, by positivity, by positivity, ?_⟩
  intro n hn3 t ht
  have ht_core : (t : ℝ) ≥ C₁ * ↑n ^ (3 : Nat) := by
    have hC₁_le : C₁ ≤ C := by
      unfold C
      exact le_max_left _ _
    nlinarith
  have ht_res : (t : ℝ) ≥ C₂ * ↑n ^ (3 : Nat) := by
    have hC₂_le : C₂ ≤ C := by
      unfold C
      exact le_max_right _ _
    nlinarith
  have hcore0 := hcore n hn3 t ht_core
  have hres0 := hres n hn3 t ht_res
  let center : ℝ := (1 : ℝ) - ((Nat.choose n 3 : ℝ) / (8 * (t : ℝ)))
  have hpaper_scale_eq : paperMainScale n t = gaussianScale n ↑t := by
    simp [paperMainScale, gaussianScale, dim]
  have hpaper_norm_eq : paperNormalizedCount n t = normalizedCount n (4 * t) := by
    have hmul : n * (4 * t) = 4 * n * t := by ac_rfl
    simp [paperNormalizedCount, normalizedCount, hmul]
  have ht_pos : (0 : ℝ) < (t : ℝ) := by
    have hC_pos : 0 < C := by
      unfold C
      positivity
    have : 0 < C * (n : ℝ) ^ (3 : Nat) := by positivity
    linarith
  have hscale_nonneg : 0 ≤ gaussianScale n ↑t := (gaussianScale_pos n ht_pos).le
  have hp2_nonneg : 0 ≤ (n : ℝ) ^ (2 : Nat) / (t : ℝ) := by positivity
  have hp32_nonneg : 0 ≤ (n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ) := by positivity
  have hp6_nonneg : 0 ≤ (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat) := by positivity
  have hexp_nonneg : 0 ≤ Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) := by positivity
  have hexp₁ :
      Real.exp (-(c₁ * (n : ℝ) ^ (2 : Nat)))
        ≤ Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [show 0 ≤ (n : ℝ) ^ (2 : Nat) by positivity, min_le_left c₁ c₂]
  have hexp₂ :
      Real.exp (-(c₂ * (n : ℝ) ^ (2 : Nat)))
        ≤ Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) := by
    apply Real.exp_le_exp.mpr
    nlinarith [show 0 ≤ (n : ℝ) ^ (2 : Nat) by positivity, min_le_right c₁ c₂]
  have hcore1 :
      |primaryCoreContribution n t - center * gaussianScale n ↑t|
        ≤ (K₁ * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
            + K₁ * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
            + K₁ * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
            + K₁ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))))
          * gaussianScale n ↑t := by
    calc
      |primaryCoreContribution n t - center * gaussianScale n ↑t|
        ≤ (K₁ * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
            + K₁ * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
            + K₁ * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
            + K₁ * Real.exp (-(c₁ * (n : ℝ) ^ (2 : Nat))))
          * gaussianScale n ↑t := by
            simpa [center, paperMainTerm, hpaper_scale_eq] using hcore0
      _ ≤ (K₁ * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
            + K₁ * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
            + K₁ * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
            + K₁ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))))
          * gaussianScale n ↑t := by
            have hcoeff :
                K₁ * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
                  + K₁ * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
                  + K₁ * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
                  + K₁ * Real.exp (-(c₁ * (n : ℝ) ^ (2 : Nat)))
              ≤ K₁ * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
                  + K₁ * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
                  + K₁ * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
                  + K₁ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) := by
              have hexp_term :
                  K₁ * Real.exp (-(c₁ * (n : ℝ) ^ (2 : Nat)))
                    ≤ K₁ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) := by
                exact mul_le_mul_of_nonneg_left hexp₁ hK₁_pos.le
              nlinarith
            exact mul_le_mul_of_nonneg_right hcoeff hscale_nonneg
  have hres1 :
      |normalizedCount n (4 * t) - primaryCoreContribution n t|
        ≤ K₂ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n ↑t := by
    calc
      |normalizedCount n (4 * t) - primaryCoreContribution n t|
        ≤ K₂ * Real.exp (-(c₂ * (n : ℝ) ^ (2 : Nat))) * gaussianScale n ↑t := hres0
      _ ≤ K₂ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n ↑t := by
            have hcoeff :
                K₂ * Real.exp (-(c₂ * (n : ℝ) ^ (2 : Nat)))
                  ≤ K₂ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) := by
              exact mul_le_mul_of_nonneg_left hexp₂ hK₂_pos.le
            exact mul_le_mul_of_nonneg_right hcoeff hscale_nonneg
  calc
    |paperNormalizedCount n t - paperMainTerm n t|
      = |normalizedCount n (4 * t) - center * gaussianScale n ↑t| := by
          simp [hpaper_norm_eq, center, paperMainTerm, hpaper_scale_eq]
    _ 
      = |(normalizedCount n (4 * t) - primaryCoreContribution n t)
          + (primaryCoreContribution n t - center * gaussianScale n ↑t)| := by
            congr 1
            ring
    _ ≤ |normalizedCount n (4 * t) - primaryCoreContribution n t|
          + |primaryCoreContribution n t - center * gaussianScale n ↑t| := by
            simpa using abs_add_le
              (normalizedCount n (4 * t) - primaryCoreContribution n t)
              (primaryCoreContribution n t - center * gaussianScale n ↑t)
    _ ≤ K₂ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n ↑t
          + ((K₁ * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
              + K₁ * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
              + K₁ * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
              + K₁ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))))
            * gaussianScale n ↑t) := by
            exact add_le_add hres1 hcore1
    _ ≤ ((K₁ + K₂) * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
          + (K₁ + K₂) * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
          + (K₁ + K₂) * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
          + (K₁ + K₂) * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))))
        * gaussianScale n ↑t := by
          have hcoeff :
              K₂ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat)))
                + (K₁ * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
                    + K₁ * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
                    + K₁ * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
                    + K₁ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))))
            ≤ (K₁ + K₂) * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
                + (K₁ + K₂) * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
                + (K₁ + K₂) * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
                + (K₁ + K₂) * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) := by
            have hpad_nonneg :
                0 ≤ K₂ * ((n : ℝ) ^ (2 : Nat) / (t : ℝ))
                    + K₂ * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
                    + K₂ * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat) := by
              positivity
            calc
              K₂ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat)))
                  + (K₁ * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
                      + K₁ * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
                      + K₁ * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
                      + K₁ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))))
                ≤ (K₂ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat)))
                    + (K₁ * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
                        + K₁ * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
                        + K₁ * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
                        + K₁ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat)))))
                    + (K₂ * ((n : ℝ) ^ (2 : Nat) / (t : ℝ))
                        + K₂ * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
                        + K₂ * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)) := by
                    linarith
              _ = (K₁ + K₂) * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
                    + (K₁ + K₂) * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
                    + (K₁ + K₂) * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
                    + (K₁ + K₂) * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) := by
                    ring
          have hfactor :
              K₂ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) * gaussianScale n ↑t
                + ((K₁ * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
                    + K₁ * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
                    + K₁ * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
                    + K₁ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))))
                  * gaussianScale n ↑t)
                =
              (K₂ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat)))
                  + (K₁ * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
                      + K₁ * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
                      + K₁ * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
                      + K₁ * Real.exp (-(c * (n : ℝ) ^ (2 : Nat)))))
                * gaussianScale n ↑t := by
            ring
          rw [hfactor]
          exact mul_le_mul_of_nonneg_right hcoeff hscale_nonneg
    _ = (K * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
          + K * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
          + K * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
          + K * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))))
        * paperMainScale n t := by
          simp [K, hpaper_scale_eq]

end
