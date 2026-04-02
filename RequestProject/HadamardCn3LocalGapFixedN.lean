import RequestProject.HadamardCn3LocalGapResidual

noncomputable section

open Real MeasureTheory Filter Finset Topology
open scoped Pointwise

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-!
## Local-Gap Fixed-`n` Layer

This file contains the fixed-`n` fallback argument used by `cor_uniform`.

The public theorem a reader should inspect first is:

- `fixed_n_count_asymptotic`

The staged bridge lemmas and the primary-box telescope are implementation detail for
that endpoint.
-/

def fixedCountDelta (t : ℕ) : ℝ :=
  ((max t 1 : ℕ) : ℝ) ^ (-(2 / 5 : ℝ))

private lemma fixedCountDelta_pos (t : ℕ) : 0 < fixedCountDelta t := by
  unfold fixedCountDelta
  positivity

private lemma fixedCountDelta_le_one (t : ℕ) : fixedCountDelta t ≤ 1 := by
  unfold fixedCountDelta
  have hbase : (1 : ℝ) ≤ ((max t 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.le_max_right t 1)
  exact Real.rpow_le_one_of_one_le_of_nonpos hbase (by norm_num)

private lemma fixedCountDelta_of_one_le {t : ℕ} (ht : 1 ≤ t) :
    fixedCountDelta t = (t : ℝ) ^ (-(2 / 5 : ℝ)) := by
  unfold fixedCountDelta
  rw [max_eq_left ht]

private lemma fixedCountDelta_pow_of_one_le {t : ℕ} (ht : 1 ≤ t) (k : ℕ) :
    fixedCountDelta t ^ k = (t : ℝ) ^ (-(((2 * k : ℕ) : ℝ) / 5)) := by
  have ht_pos : 0 < (t : ℝ) := by exact_mod_cast ht
  have ht_nonneg : 0 ≤ (t : ℝ) := ht_pos.le
  calc
    fixedCountDelta t ^ k = ((t : ℝ) ^ (-(2 / 5 : ℝ))) ^ k := by
      rw [fixedCountDelta_of_one_le ht]
    _ = (t : ℝ) ^ ((-(2 / 5 : ℝ)) * (k : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht_nonneg]
    _ = (t : ℝ) ^ (-(((2 * k : ℕ) : ℝ) / 5)) := by
      congr 1
      norm_num [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

private lemma t_mul_fixedCountDelta_pow_of_one_le {t : ℕ} (ht : 1 ≤ t) (k : ℕ) :
    (t : ℝ) * fixedCountDelta t ^ k = (t : ℝ) ^ (1 - (((2 * k : ℕ) : ℝ) / 5)) := by
  have ht_pos : 0 < (t : ℝ) := by exact_mod_cast ht
  calc
    (t : ℝ) * fixedCountDelta t ^ k
        = (t : ℝ) ^ (1 : ℝ) * (t : ℝ) ^ (-(((2 * k : ℕ) : ℝ) / 5)) := by
            rw [Real.rpow_one, fixedCountDelta_pow_of_one_le ht k]
    _ = (t : ℝ) ^ ((1 : ℝ) + (-(((2 * k : ℕ) : ℝ) / 5))) := by
          rw [← Real.rpow_add ht_pos]
    _ = (t : ℝ) ^ (1 - (((2 * k : ℕ) : ℝ) / 5)) := by ring

private lemma fixedCountDelta_sq_mul_t_of_one_le {t : ℕ} (ht : 1 ≤ t) :
    fixedCountDelta t ^ (2 : Nat) * (t : ℝ) = (t : ℝ) ^ (1 / 5 : ℝ) := by
  calc
    fixedCountDelta t ^ (2 : Nat) * (t : ℝ)
        = (t : ℝ) * fixedCountDelta t ^ (2 : Nat) := by ring
    _ = (t : ℝ) ^ (1 - (((2 * 2 : ℕ) : ℝ) / 5)) := by
          simpa using t_mul_fixedCountDelta_pow_of_one_le ht 2
    _ = (t : ℝ) ^ (1 / 5 : ℝ) := by norm_num

private lemma rpow_neg_nat_eq_inv_pow {x : ℝ} (hx : 0 < x) (m : ℕ) :
    x ^ (-(m : ℝ)) = 1 / x ^ m := by
  rw [Real.rpow_neg (le_of_lt hx), Real.rpow_natCast]
  simp

private lemma const_mul_nat_rpow_neg_eventually_le
    (K α ε : ℝ) (hK : 0 ≤ K) (hα : 0 < α) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in Filter.atTop, K * ((t : ℝ) ^ (-α)) ≤ ε := by
  have hlim0 :
      Tendsto (fun t : ℕ => (t : ℝ) ^ (-α)) Filter.atTop (𝓝 (0 : ℝ)) := by
    exact (tendsto_rpow_neg_atTop hα).comp tendsto_natCast_atTop_atTop
  have hlim :
      Tendsto (fun t : ℕ => K * ((t : ℝ) ^ (-α))) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa using hlim0.const_mul K
  have hnear : ∀ᶠ t : ℕ in Filter.atTop, K * ((t : ℝ) ^ (-α)) < ε := by
    exact hlim (Iio_mem_nhds hε)
  exact hnear.mono fun _ ht => le_of_lt ht

private lemma fixedCountDelta_eventually_le (r : ℝ) (hr : 0 < r) :
    ∀ᶠ t : ℕ in Filter.atTop, fixedCountDelta t ≤ r := by
  filter_upwards
    [Filter.eventually_ge_atTop 1,
      const_mul_nat_rpow_neg_eventually_le 1 (2 / 5 : ℝ) r (by positivity) (by positivity) hr]
      with t ht1 ht
  rw [fixedCountDelta_of_one_le ht1]
  simpa using ht

private lemma const_mul_fixedCountDelta_pow_eventually_le
    (K ε : ℝ) (k : ℕ) (hK : 0 ≤ K) (hk : 0 < k) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in Filter.atTop, K * fixedCountDelta t ^ k ≤ ε := by
  have hα : 0 < (((2 * k : ℕ) : ℝ) / 5) := by
    have hk' : 0 < ((2 * k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_pos (by decide) hk)
    positivity
  filter_upwards
    [Filter.eventually_ge_atTop 1,
      const_mul_nat_rpow_neg_eventually_le K (((2 * k : ℕ) : ℝ) / 5) ε hK hα hε]
    with t ht1 ht
  calc
    K * fixedCountDelta t ^ k = K * (t : ℝ) ^ (-(((2 * k : ℕ) : ℝ) / 5)) := by
      rw [fixedCountDelta_pow_of_one_le ht1 k]
    _ ≤ ε := by
      simpa using ht

private lemma const_mul_t_mul_fixedCountDelta_pow_eventually_le
    (K ε : ℝ) (k : ℕ) (hk : 5 < 2 * k) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in Filter.atTop, K * ((t : ℝ) * fixedCountDelta t ^ k) ≤ ε := by
  let α : ℝ := (((2 * k : ℕ) : ℝ) / 5) - 1
  have hα : 0 < α := by
    have hk' : (5 : ℝ) < ((2 * k : ℕ) : ℝ) := by
      exact_mod_cast hk
    dsimp [α]
    nlinarith
  filter_upwards
    [Filter.eventually_ge_atTop 1,
      const_mul_nat_rpow_neg_eventually_le K α ε hK hα hε]
    with t ht1 ht
  calc
    K * ((t : ℝ) * fixedCountDelta t ^ k)
        = K * (t : ℝ) ^ (1 - (((2 * k : ℕ) : ℝ) / 5)) := by
            rw [t_mul_fixedCountDelta_pow_of_one_le ht1 k]
    _ = K * (t : ℝ) ^ (-α) := by
          congr 1
          dsimp [α]
          ring
    _ ≤ ε := by
          simpa [α] using ht

private lemma scale_gap_le_of_gap_le_gaussianF
    {T A B coeff gaussianFVal gaussianScaleVal : ℝ}
    (hT_nonneg : 0 ≤ T)
    (hscale_eq : T * gaussianFVal = gaussianScaleVal)
    (hgap : |A - B| ≤ coeff * gaussianFVal) :
    |T * A - T * B| ≤ coeff * gaussianScaleVal := by
  calc
    |T * A - T * B| = T * |A - B| := by
          rw [show T * A - T * B = T * (A - B) by ring, abs_mul, abs_of_nonneg hT_nonneg]
    _ ≤ T * (coeff * gaussianFVal) := by
          exact mul_le_mul_of_nonneg_left hgap hT_nonneg
    _ = coeff * gaussianScaleVal := by
          rw [← hscale_eq]
          ring

private lemma scaled_gap_le_of_gap_le_gaussianF_and_coeff
    {T A B coeff gaussianFVal gaussianScaleVal ε : ℝ}
    (hT_nonneg : 0 ≤ T)
    (hscale_nonneg : 0 ≤ gaussianScaleVal)
    (hscale_eq : T * gaussianFVal = gaussianScaleVal)
    (hgap : |A - B| ≤ coeff * gaussianFVal)
    (hcoeff : coeff ≤ ε) :
    |T * A - T * B| ≤ ε * gaussianScaleVal := by
  have hscaled : |T * A - T * B| ≤ coeff * gaussianScaleVal :=
    scale_gap_le_of_gap_le_gaussianF hT_nonneg hscale_eq hgap
  exact le_trans hscaled (mul_le_mul_of_nonneg_right hcoeff hscale_nonneg)

private lemma gaussianScale_lower_bound
    (n : ℕ) (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) :
    (8 * Real.pi * t) ^ (-((dim n : ℝ) / 2)) ≤ gaussianScale n t := by
  unfold gaussianScale dim
  have hsub : n ≤ 2 * Nat.choose n 2 := by
    rcases eq_or_lt_of_le hn with h2 | h3
    · simpa [h2]
    · exact Cn3Torus.n_le_two_mul_d n (Nat.succ_le_of_lt h3)
  have hExp : ((2 * Nat.choose n 2 - n + 1 : Nat) : ℤ) = (2 * ↑(Nat.choose n 2) - ↑n + 1 : ℤ) := by
    rw [Nat.cast_add, Nat.cast_sub hsub, Nat.cast_one]
    norm_num
  have hcoeff_ge_one_nat : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * Nat.choose n 2 - n + 1 : Nat) := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hcoeff_ge_one : (1 : ℝ) ≤ (2 ^ (2 * Nat.choose n 2 - n + 1 : ℤ) : ℝ) := by
    rw [← hExp, zpow_natCast]
    simpa using hcoeff_ge_one_nat
  have hbase_nonneg_arg : 0 ≤ 8 * Real.pi * t := by positivity [Real.pi_pos, ht]
  have hbase_nonneg : 0 ≤ (8 * Real.pi * t) ^ (-((Nat.choose n 2 : ℝ) / 2)) := by
    exact Real.rpow_nonneg hbase_nonneg_arg _
  have hmul :
      (8 * Real.pi * t) ^ (-((Nat.choose n 2 : ℝ) / 2))
        ≤ (2 ^ (2 * Nat.choose n 2 - n + 1 : ℤ) : ℝ)
            * (8 * Real.pi * t) ^ (-((Nat.choose n 2 : ℝ) / 2)) := by
    nlinarith
  have hrew : -((Nat.choose n 2 : ℝ) / 2) = -(↑(Nat.choose n 2)) / 2 := by ring
  simpa [hrew, Cn3Torus.d, mul_assoc, mul_left_comm, mul_comm] using hmul

lemma const_mul_nat_rpow_mul_exp_neg_mul_nat_rpow_eventually_le
    (K s a p ε : ℝ) (hK : 0 ≤ K) (ha : 0 < a) (hp : 0 < p) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in Filter.atTop, K * (t : ℝ) ^ s * Real.exp (-a * (t : ℝ) ^ p) ≤ ε := by
  have hlim_core :
      Tendsto
        (fun x : ℝ => x ^ (s / p) * Real.exp (-a * x))
        Filter.atTop (𝓝 (0 : ℝ)) := by
    exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / p) a ha
  have hpow_atTop : Tendsto (fun x : ℝ => x ^ p) Filter.atTop Filter.atTop := by
    exact tendsto_rpow_atTop hp
  have hlim_real_aux :
      Tendsto
        (fun x : ℝ => (x ^ p) ^ (s / p) * Real.exp (-a * (x ^ p)))
        Filter.atTop (𝓝 (0 : ℝ)) := by
    exact hlim_core.comp hpow_atTop
  have hlim_real :
      Tendsto
        (fun x : ℝ => K * (x ^ s * Real.exp (-a * x ^ p)))
        Filter.atTop (𝓝 (0 : ℝ)) := by
    have hcongr :
        (fun x : ℝ => K * ((x ^ p) ^ (s / p) * Real.exp (-a * (x ^ p))))
          =ᶠ[Filter.atTop]
            (fun x : ℝ => K * (x ^ s * Real.exp (-a * x ^ p))) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      have hx_nonneg : 0 ≤ x := hx.le
      have hpow :
          (x ^ p) ^ (s / p) = x ^ s := by
        rw [← Real.rpow_mul hx_nonneg]
        field_simp [hp.ne']
      simp [hpow]
    simpa [zero_mul] using (hlim_real_aux.const_mul K).congr' hcongr
  have hlim_nat :
      Tendsto
        (fun t : ℕ => K * ((t : ℝ) ^ s * Real.exp (-a * (t : ℝ) ^ p)))
        Filter.atTop (𝓝 (0 : ℝ)) := by
    exact hlim_real.comp tendsto_natCast_atTop_atTop
  have hnear :
      ∀ᶠ t : ℕ in Filter.atTop,
        K * ((t : ℝ) ^ s * Real.exp (-a * (t : ℝ) ^ p)) < ε := by
    exact hlim_nat (Iio_mem_nhds hε)
  exact hnear.mono (fun _ ht => by simpa [mul_assoc] using (le_of_lt ht))

private lemma exp_neg_mul_nat_rpow_le_eps_gaussianScale_fixed
    (n : ℕ) (hn : 2 ≤ n) (a p ε : ℝ)
    (ha : 0 < a) (hp : 0 < p) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in Filter.atTop, Real.exp (-a * (t : ℝ) ^ p) ≤ ε * gaussianScale n (t : ℝ) := by
  let s : ℝ := (dim n : ℝ) / 2
  let K : ℝ := ((8 * Real.pi) : ℝ) ^ s
  have hK_nonneg : 0 ≤ K := by
    unfold K s
    positivity [Real.pi_pos]
  have hmain :=
    const_mul_nat_rpow_mul_exp_neg_mul_nat_rpow_eventually_le K s a p ε
      hK_nonneg ha hp hε
  filter_upwards [Filter.eventually_ge_atTop 1, hmain] with t ht1 ht
  have ht_pos : (0 : ℝ) < (t : ℝ) := by
    exact_mod_cast ht1
  have hbase_pos : 0 < (8 * Real.pi : ℝ) := by positivity [Real.pi_pos]
  have hpow_pos : 0 < ((8 * Real.pi : ℝ) ^ s * (t : ℝ) ^ s) := by
    positivity [Real.pi_pos, ht_pos]
  have hrewrite :
      ((8 * Real.pi : ℝ) ^ s * (t : ℝ) ^ s)
        = (((8 * Real.pi : ℝ) * (t : ℝ)) ^ s) := by
    rw [Real.mul_rpow (show 0 ≤ (8 * Real.pi : ℝ) by positivity [Real.pi_pos]) ht_pos.le]
  have hstep :
      Real.exp (-a * (t : ℝ) ^ p)
        ≤ ε * (((8 * Real.pi : ℝ) * (t : ℝ)) ^ (-s)) := by
    have hdiv :
        Real.exp (-a * (t : ℝ) ^ p)
          ≤ ε / (((8 * Real.pi : ℝ) ^ s) * (t : ℝ) ^ s) := by
      exact (le_div_iff₀ hpow_pos).2 (by simpa [K, s, mul_assoc, mul_left_comm, mul_comm] using ht)
    calc
      Real.exp (-a * (t : ℝ) ^ p)
        ≤ ε / (((8 * Real.pi : ℝ) ^ s) * (t : ℝ) ^ s) := hdiv
      _ = ε * ((((8 * Real.pi : ℝ) ^ s) * (t : ℝ) ^ s)⁻¹) := by rw [div_eq_mul_inv]
      _ = ε * (((8 * Real.pi : ℝ) * (t : ℝ)) ^ (-s)) := by
            rw [hrewrite, Real.rpow_neg (le_of_lt (mul_pos hbase_pos ht_pos))]
  exact le_trans hstep (mul_le_mul_of_nonneg_left (gaussianScale_lower_bound n hn ht_pos) hε.le)

private lemma gaussianF_three_quarters_eq (d : ℕ) {t : ℝ} (ht : 0 < t) :
    gaussianF d ((3 / 4 : ℝ) * t)
      = (4 / 3 : ℝ) ^ ((d : ℝ) / 2) * gaussianF d t := by
  unfold gaussianF
  have hbase :
      π / (2 * ((3 / 4 : ℝ) * t))
        = (4 / 3 : ℝ) * (π / (2 * t)) := by
    field_simp [ht.ne', Real.pi_ne_zero]
  calc
    (π / (2 * ((3 / 4 : ℝ) * t))) ^ ((d : ℝ) / 2)
        = ((4 / 3 : ℝ) * (π / (2 * t))) ^ ((d : ℝ) / 2) := by rw [hbase]
    _ = (4 / 3 : ℝ) ^ ((d : ℝ) / 2) * (π / (2 * t)) ^ ((d : ℝ) / 2) := by
            rw [Real.mul_rpow
              (show 0 ≤ (4 / 3 : ℝ) by positivity)
              (show 0 ≤ π / (2 * t) by positivity [Real.pi_pos, ht])]
    _ = (4 / 3 : ℝ) ^ ((d : ℝ) / 2) * gaussianF d t := by rfl

/-- On the shrinking annulus between `fixedCountDelta t` and a fixed small radius `r₀`,
the local-box contribution is polynomially small relative to `gaussianF`. -/
private lemma fixedCount_annulus_integral_bound
    (n : ℕ) :
    ∃ r₀ Cann : ℝ, 0 < r₀ ∧ r₀ < π / 4 ∧ 0 < Cann ∧
      ∀ t : ℕ, 2 ≤ t → fixedCountDelta t ≤ r₀ →
        let A : Set (Cn3Torus.Edge n → ℝ) :=
          ((edgeBox n Cn3Torus.delta ∩ edgeEuclidBall n r₀) \ edgeEuclidBall n (fixedCountDelta t))
        ∫ mu in A, ‖Cn3Torus.psi n mu‖ ^ (4 * t)
          ≤ (Cann / (fixedCountDelta t ^ (2 : Nat) * (t : ℝ))) * gaussianF (dim n) (t : ℝ) := by
  obtain ⟨r₀, hr₀_pos, hr₀_lt, hsmall⟩ := small_ball_gaussian_decay_uniform
  obtain ⟨Cmom, hCmom_pos, hmoment⟩ := gaussian_radial_moments_edge n 1
  let Cann : ℝ := ((4 / 3 : ℝ) * Cmom) * (4 / 3 : ℝ) ^ ((dim n : ℝ) / 2)
  refine ⟨r₀, Cann, hr₀_pos, hr₀_lt, ?_, ?_⟩
  · unfold Cann
    positivity
  · intro t ht_two hdelta
    let A : Set (Cn3Torus.Edge n → ℝ) :=
      ((edgeBox n Cn3Torus.delta ∩ edgeEuclidBall n r₀) \ edgeEuclidBall n (fixedCountDelta t))
    have ht_one : 1 ≤ t := by omega
    have ht_pos_nat : 0 < t := by omega
    have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
    have hs_pos : (0 : ℝ) < (3 / 4 : ℝ) * (t : ℝ) := by positivity
    have hs_one : (1 : ℝ) ≤ (3 / 4 : ℝ) * (t : ℝ) := by
      have : (3 / 4 : ℝ) * (2 : ℝ) ≤ (3 / 4 : ℝ) * (t : ℝ) := by
        gcongr
        exact_mod_cast ht_two
      linarith
    have hdelta_pos : 0 < fixedCountDelta t := fixedCountDelta_pos t
    have hdelta_sq_pos : 0 < fixedCountDelta t ^ (2 : Nat) := by
      exact pow_pos hdelta_pos 2
    have hdelta_sq_ne : fixedCountDelta t ^ (2 : Nat) ≠ 0 := hdelta_sq_pos.ne'
    have hA_meas : MeasurableSet A := by
      dsimp [A]
      exact ((edgeBox_isCompact n Cn3Torus.delta).measurableSet.inter
        (measurableSet_edgeEuclidBall n r₀)).diff (measurableSet_edgeEuclidBall n (fixedCountDelta t))
    let g : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu => ‖Cn3Torus.psi n mu‖ ^ (4 * t)
    let h : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu =>
      Real.exp (-(3 * (t : ℝ) * Cn3Torus.sqNormEdge n mu / 2))
    let w : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu =>
      (1 / (fixedCountDelta t ^ (2 : Nat))) * Cn3Torus.sqNormEdge n mu * h mu
    have hw_int : MeasureTheory.Integrable w := by
      have hsq_int :
          MeasureTheory.Integrable
            (fun mu : Cn3Torus.Edge n → ℝ =>
              Cn3Torus.sqNormEdge n mu
                * Real.exp (-2 * (((3 / 4 : ℝ) * (t : ℝ))) * Cn3Torus.sqNormEdge n mu)) := by
        simpa [pow_one, mul_assoc, mul_left_comm, mul_comm] using
          sqNorm_moment_gaussian_integrable_edge n 1 (by norm_num) ((3 / 4 : ℝ) * (t : ℝ)) hs_pos
      have hEq :
          w =
          (fun mu : Cn3Torus.Edge n → ℝ =>
            (1 / (fixedCountDelta t ^ (2 : Nat)))
              * (Cn3Torus.sqNormEdge n mu
                  * Real.exp (-2 * (((3 / 4 : ℝ) * (t : ℝ))) * Cn3Torus.sqNormEdge n mu))) := by
        funext mu
        dsimp [w, h]
        have hexp :
            Real.exp (-(3 * (t : ℝ) * Cn3Torus.sqNormEdge n mu / 2))
              = Real.exp (-2 * (((3 / 4 : ℝ) * (t : ℝ))) * Cn3Torus.sqNormEdge n mu) := by
          congr 1
          ring
        rw [hexp]
        ring
      rw [hEq]
      exact hsq_int.const_mul (1 / (fixedCountDelta t ^ (2 : Nat)))
    have hA_subset_ball : A ⊆ edgeEuclidBall n r₀ := by
      intro mu hmu
      exact hmu.1.2
    have hA_sq_upper :
        ∀ mu, mu ∈ A → Cn3Torus.sqNormEdge n mu ≤ r₀ ^ (2 : Nat) := by
      intro mu hmu
      exact (mem_edgeEuclidBall_iff n r₀ mu).1 (hA_subset_ball hmu)
    have hA_sq_lower :
        ∀ mu, mu ∈ A → fixedCountDelta t ^ (2 : Nat) ≤ Cn3Torus.sqNormEdge n mu := by
      intro mu hmu
      have hnot : mu ∉ edgeEuclidBall n (fixedCountDelta t) := hmu.2
      exact le_of_not_ge (by
        intro hsq
        exact hnot ((mem_edgeEuclidBall_iff n (fixedCountDelta t) mu).2 hsq))
    have hpoint :
        ∀ mu, mu ∈ A → g mu ≤ w mu := by
      intro mu hmu
      have hsmall_mu := hsmall n mu (hA_sq_upper mu hmu) t ht_one
      have hmul :
          h mu ≤ (1 / (fixedCountDelta t ^ (2 : Nat))) * Cn3Torus.sqNormEdge n mu * h mu := by
        calc
          h mu = (1 / (fixedCountDelta t ^ (2 : Nat))) * ((fixedCountDelta t ^ (2 : Nat)) * h mu) := by
                  field_simp [hdelta_sq_ne]
          _ ≤ (1 / (fixedCountDelta t ^ (2 : Nat))) * (Cn3Torus.sqNormEdge n mu * h mu) := by
                  gcongr
                  exact hA_sq_lower mu hmu
          _ = (1 / (fixedCountDelta t ^ (2 : Nat))) * Cn3Torus.sqNormEdge n mu * h mu := by
                  ring
      exact le_trans hsmall_mu hmul
    have hA_subset_box : A ⊆ edgeBox n Cn3Torus.delta := by
      intro mu hmu
      exact hmu.1.1
    have hg_nonneg : ∀ mu, 0 ≤ g mu := by
      intro mu
      dsimp [g]
      positivity
    have hw_nonneg : ∀ mu, 0 ≤ w mu := by
      intro mu
      dsimp [w, h]
      have h0 : 0 ≤ 1 / (fixedCountDelta t ^ (2 : Nat)) := by positivity
      have h1 : 0 ≤ Cn3Torus.sqNormEdge n mu := Cn3Torus.sqNormEdge_nonneg n mu
      have h2 : 0 ≤ Real.exp (-(3 * (t : ℝ) * Cn3Torus.sqNormEdge n mu / 2)) := by positivity
      exact mul_nonneg (mul_nonneg h0 h1) h2
    have hA_le_weighted :
        ∫ mu in A, g mu ≤ ∫ mu in A, w mu := by
      have hg_int_on : MeasureTheory.IntegrableOn g A := by
        simpa [MeasureTheory.IntegrableOn] using
          ((((Cn3Torus.continuous_psi n).norm.pow (4 * t)).continuousOn.integrableOn_compact
              (edgeBox_isCompact n Cn3Torus.delta)).mono_set hA_subset_box)
      have hmono : ∀ᵐ mu ∂MeasureTheory.volume.restrict A, g mu ≤ w mu := by
        rw [MeasureTheory.ae_restrict_iff' hA_meas]
        exact Filter.Eventually.of_forall (fun mu hmu => hpoint mu hmu)
      exact MeasureTheory.integral_mono_ae hg_int_on hw_int.integrableOn hmono
    have hweighted_le :
        ∫ mu in A, w mu ≤ ∫ mu, w mu := by
      simpa using
        (integralOn_mono_of_nonneg (μ := MeasureTheory.volume) (s := A) (t := Set.univ) (f := w)
          (by intro _ _; simp) hA_meas MeasurableSet.univ hw_int.integrableOn
          (Filter.Eventually.of_forall hw_nonneg))
    have hmoment' :
        ∫ mu : Cn3Torus.Edge n → ℝ,
            Cn3Torus.sqNormEdge n mu
              * Real.exp (-2 * (((3 / 4 : ℝ) * (t : ℝ))) * Cn3Torus.sqNormEdge n mu)
          ≤ (Cmom / (((3 / 4 : ℝ) * (t : ℝ)))) * gaussianF (dim n) (((3 / 4 : ℝ) * (t : ℝ))) := by
      simpa [pow_one] using hmoment (((3 / 4 : ℝ) * (t : ℝ))) hs_one
    have hw_full :
        ∫ mu, w mu
          = (1 / (fixedCountDelta t ^ (2 : Nat)))
              * ∫ mu : Cn3Torus.Edge n → ℝ,
                  Cn3Torus.sqNormEdge n mu
                    * Real.exp (-2 * (((3 / 4 : ℝ) * (t : ℝ))) * Cn3Torus.sqNormEdge n mu) := by
      have hEq :
          w =
            fun mu : Cn3Torus.Edge n → ℝ =>
              (1 / (fixedCountDelta t ^ (2 : Nat)))
                * (Cn3Torus.sqNormEdge n mu
                    * Real.exp (-2 * (((3 / 4 : ℝ) * (t : ℝ))) * Cn3Torus.sqNormEdge n mu)) := by
        funext mu
        dsimp [w, h]
        have hexp :
            Real.exp (-(3 * (t : ℝ) * Cn3Torus.sqNormEdge n mu / 2))
              = Real.exp (-2 * (((3 / 4 : ℝ) * (t : ℝ))) * Cn3Torus.sqNormEdge n mu) := by
          congr 1
          ring
        rw [hexp]
        ring
      rw [hEq, MeasureTheory.integral_const_mul]
    calc
      ∫ mu in A, ‖Cn3Torus.psi n mu‖ ^ (4 * t) = ∫ mu in A, g mu := by rfl
      _ ≤ ∫ mu in A, w mu := hA_le_weighted
      _ ≤ ∫ mu, w mu := hweighted_le
      _ = (1 / (fixedCountDelta t ^ (2 : Nat)))
            * ∫ mu : Cn3Torus.Edge n → ℝ,
                Cn3Torus.sqNormEdge n mu
                  * Real.exp (-2 * (((3 / 4 : ℝ) * (t : ℝ))) * Cn3Torus.sqNormEdge n mu) := hw_full
      _ ≤ (1 / (fixedCountDelta t ^ (2 : Nat)))
            * ((Cmom / (((3 / 4 : ℝ) * (t : ℝ))))
                * gaussianF (dim n) (((3 / 4 : ℝ) * (t : ℝ)))) := by
            exact mul_le_mul_of_nonneg_left hmoment' (by positivity)
      _ = (((4 / 3 : ℝ) * Cmom) / (fixedCountDelta t ^ (2 : Nat) * (t : ℝ)))
            * gaussianF (dim n) (((3 / 4 : ℝ) * (t : ℝ))) := by
            field_simp [hdelta_sq_ne, ht_pos.ne']
      _ = (Cann / (fixedCountDelta t ^ (2 : Nat) * (t : ℝ)))
            * gaussianF (dim n) (t : ℝ) := by
            rw [gaussianF_three_quarters_eq (dim n) ht_pos]
            unfold Cann
            field_simp [hdelta_sq_ne, ht_pos.ne']

/-- The Gaussian mass outside the shrinking fixed-`n` ball is `O(t^{-1/5})` relative
to the full Gaussian core mass. -/
private lemma fixedCount_gaussian_tail_bound
    (n : ℕ) (hn : 2 ≤ n) :
    ∃ Ctail : ℝ, 0 < Ctail ∧
      ∀ t : ℕ, 2 ≤ t →
        Cn3Torus.texPrefactor n *
            |(∫ mu in edgeEuclidBall n (fixedCountDelta t),
                Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))
              - gaussianF (dim n) (t : ℝ)|
          ≤ (Ctail * (t : ℝ) ^ (-(1 / 5 : ℝ))) * gaussianScale n (t : ℝ) := by
  obtain ⟨Cmom, hCmom_pos, hmoment⟩ := gaussian_radial_moments_edge n 1
  refine ⟨Cmom, hCmom_pos, ?_⟩
  intro t ht2
  have ht1 : 1 ≤ t := by omega
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  have hdelta_sq_pos : 0 < fixedCountDelta t ^ (2 : Nat) := by
    exact pow_pos (fixedCountDelta_pos t) 2
  have hdelta_sq_ne : fixedCountDelta t ^ (2 : Nat) ≠ 0 := hdelta_sq_pos.ne'
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  let tail : Set (Cn3Torus.Edge n → ℝ) := innerᶜ
  let g : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu =>
    Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
  let w : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu =>
    (1 / (fixedCountDelta t ^ (2 : Nat)))
      * Cn3Torus.sqNormEdge n mu * g mu
  have hinner_meas : MeasurableSet inner := measurableSet_edgeEuclidBall n (fixedCountDelta t)
  have htail_meas : MeasurableSet tail := hinner_meas.compl
  have hg_nonneg : ∀ mu, 0 ≤ g mu := by
    intro mu
    dsimp [g]
    positivity
  have hw_nonneg : ∀ mu, 0 ≤ w mu := by
    intro mu
    dsimp [w, g]
    have h0 : 0 ≤ 1 / (fixedCountDelta t ^ (2 : Nat)) := by positivity
    have h1 : 0 ≤ Cn3Torus.sqNormEdge n mu := Cn3Torus.sqNormEdge_nonneg n mu
    have h2 : 0 ≤ Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by positivity
    exact mul_nonneg (mul_nonneg h0 h1) h2
  have hw_int : MeasureTheory.Integrable w := by
    have hsq_int :
        MeasureTheory.Integrable
          (fun mu : Cn3Torus.Edge n → ℝ =>
            Cn3Torus.sqNormEdge n mu
              * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
      simpa [pow_one] using
        sqNorm_moment_gaussian_integrable_edge n 1 (by norm_num) (t : ℝ) ht_pos
    have hEq :
        w =
          (fun mu : Cn3Torus.Edge n → ℝ =>
            (1 / (fixedCountDelta t ^ (2 : Nat)))
              * (Cn3Torus.sqNormEdge n mu
                  * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))) := by
      funext mu
      dsimp [w, g]
      ring
    rw [hEq]
    exact hsq_int.const_mul (1 / (fixedCountDelta t ^ (2 : Nat)))
  have htail_point :
      ∀ mu, mu ∈ tail → g mu ≤ w mu := by
    intro mu hmu
    have hsq_lower :
        fixedCountDelta t ^ (2 : Nat) ≤ Cn3Torus.sqNormEdge n mu := by
      have hnot : mu ∉ inner := hmu
      exact le_of_not_ge (by
        intro hsq
        exact hnot ((mem_edgeEuclidBall_iff n (fixedCountDelta t) mu).2 hsq))
    have hdelta_sq_pos : 0 < fixedCountDelta t ^ (2 : Nat) := by
      exact pow_pos (fixedCountDelta_pos t) 2
    have hdelta_sq_ne : fixedCountDelta t ^ (2 : Nat) ≠ 0 := hdelta_sq_pos.ne'
    have hfrac_one : (1 / (fixedCountDelta t ^ (2 : Nat))) * (fixedCountDelta t ^ (2 : Nat)) = 1 := by
      rw [one_div]
      exact inv_mul_cancel₀ hdelta_sq_ne
    calc
      g mu = ((1 / (fixedCountDelta t ^ (2 : Nat))) * (fixedCountDelta t ^ (2 : Nat))) * g mu := by
                rw [hfrac_one, one_mul]
      _ = (1 / (fixedCountDelta t ^ (2 : Nat))) * ((fixedCountDelta t ^ (2 : Nat)) * g mu) := by
                ring
      _ ≤ (1 / (fixedCountDelta t ^ (2 : Nat))) * (Cn3Torus.sqNormEdge n mu * g mu) := by
                gcongr
      _ = w mu := by
                dsimp [w]
                ring
  have hg_int_on : MeasureTheory.IntegrableOn g tail := by
    simpa [g] using (gaussian_integrable_edge n (2 * (t : ℝ)) (by positivity)).integrableOn
  have hg_int : MeasureTheory.Integrable g := by
    simpa [g] using gaussian_integrable_edge n (2 * (t : ℝ)) (by positivity)
  have htail_le :
      ∫ mu in tail, g mu ≤ ∫ mu in tail, w mu := by
    have hmono : ∀ᵐ mu ∂MeasureTheory.volume.restrict tail, g mu ≤ w mu := by
      rw [MeasureTheory.ae_restrict_iff' htail_meas]
      exact Filter.Eventually.of_forall (fun mu hmu => htail_point mu hmu)
    exact MeasureTheory.integral_mono_ae hg_int_on hw_int.integrableOn hmono
  have htail_le_univ :
      ∫ mu in tail, w mu ≤ ∫ mu, w mu := by
    simpa using
      (integralOn_mono_of_nonneg (μ := MeasureTheory.volume) (s := tail) (t := Set.univ) (f := w)
        (by intro _ _; simp) htail_meas MeasurableSet.univ hw_int.integrableOn
        (Filter.Eventually.of_forall hw_nonneg))
  have hmoment' :
      ∫ mu : Cn3Torus.Edge n → ℝ,
          Cn3Torus.sqNormEdge n mu
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
        ≤ (Cmom / (t : ℝ)) * gaussianF (dim n) (t : ℝ) := by
    simpa [pow_one] using hmoment (t : ℝ) (by exact_mod_cast ht1)
  have hw_full :
      ∫ mu, w mu
        = (1 / (fixedCountDelta t ^ (2 : Nat)))
            * ∫ mu : Cn3Torus.Edge n → ℝ,
                Cn3Torus.sqNormEdge n mu
                  * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
    have hEq :
        w =
          (fun mu : Cn3Torus.Edge n → ℝ =>
            (1 / (fixedCountDelta t ^ (2 : Nat)))
              * (Cn3Torus.sqNormEdge n mu
                  * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))) := by
      funext mu
      dsimp [w, g]
      ring
    rw [hEq, MeasureTheory.integral_const_mul]
  have htail_bound :
      ∫ mu in tail, g mu
        ≤ (Cmom / (fixedCountDelta t ^ (2 : Nat) * (t : ℝ)))
            * gaussianF (dim n) (t : ℝ) := by
    calc
      ∫ mu in tail, g mu ≤ ∫ mu in tail, w mu := htail_le
      _ ≤ ∫ mu, w mu := htail_le_univ
      _ = (1 / (fixedCountDelta t ^ (2 : Nat)))
            * ∫ mu : Cn3Torus.Edge n → ℝ,
                Cn3Torus.sqNormEdge n mu
                  * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := hw_full
      _ ≤ (1 / (fixedCountDelta t ^ (2 : Nat)))
            * ((Cmom / (t : ℝ)) * gaussianF (dim n) (t : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hmoment' (by positivity)
      _ = (Cmom / (fixedCountDelta t ^ (2 : Nat) * (t : ℝ)))
            * gaussianF (dim n) (t : ℝ) := by
            calc
              (1 / (fixedCountDelta t ^ (2 : Nat)))
                    * ((Cmom / (t : ℝ)) * gaussianF (dim n) (t : ℝ))
                  = (((1 / (fixedCountDelta t ^ (2 : Nat))) * (Cmom / (t : ℝ)))
                      * gaussianF (dim n) (t : ℝ)) := by ring
              _ = (Cmom / (fixedCountDelta t ^ (2 : Nat) * (t : ℝ)))
                      * gaussianF (dim n) (t : ℝ) := by
                    field_simp [hdelta_sq_ne, ht_pos.ne']
  have hinner_gauss :
      ∫ mu in inner, g mu = gaussianF (dim n) (t : ℝ) - ∫ mu in tail, g mu := by
    have hfull : ∫ mu : Cn3Torus.Edge n → ℝ, g mu = gaussianF (dim n) (t : ℝ) := by
      simpa [g] using gaussian_integral_formula_edge n (2 * (t : ℝ)) (by positivity)
    have hdecomp0 : (∫ mu in inner, g mu) + ∫ mu in innerᶜ, g mu = ∫ mu, g mu := by
      exact MeasureTheory.integral_add_compl (μ := MeasureTheory.volume) (f := g) hinner_meas hg_int
    have hdecomp' : (∫ mu in inner, g mu) + ∫ mu in tail, g mu = ∫ mu, g mu := by
      simpa [tail] using hdecomp0
    have hdecomp'' : (∫ mu in inner, g mu) + ∫ mu in tail, g mu = gaussianF (dim n) (t : ℝ) := by
      rw [hfull] at hdecomp'
      exact hdecomp'
    rw [eq_sub_iff_add_eq]
    exact hdecomp''
  have htail_nonneg : 0 ≤ ∫ mu in tail, g mu := by
    exact MeasureTheory.integral_nonneg (fun _ => hg_nonneg _)
  have habs :
      |(∫ mu in inner, g mu) - gaussianF (dim n) (t : ℝ)| = ∫ mu in tail, g mu := by
    rw [hinner_gauss]
    ring_nf
    rw [abs_neg, abs_of_nonneg htail_nonneg]
  have hscale_eq :
      Cn3Torus.texPrefactor n * gaussianF (dim n) (t : ℝ) = gaussianScale n (t : ℝ) := by
    simpa using gaussianScale_eq_texPrefactor_mul_gaussianF n hn (t : ℝ) ht_pos
  have htex_nonneg : 0 ≤ Cn3Torus.texPrefactor n := by
    exact texPrefactor_nonneg n
  calc
    Cn3Torus.texPrefactor n *
        |(∫ mu in edgeEuclidBall n (fixedCountDelta t),
            Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))
          - gaussianF (dim n) (t : ℝ)|
      = Cn3Torus.texPrefactor n * ∫ mu in tail, g mu := by
          simpa [inner, g] using congrArg (fun x : ℝ => Cn3Torus.texPrefactor n * x) habs
    _ ≤ Cn3Torus.texPrefactor n
          * ((Cmom / (fixedCountDelta t ^ (2 : Nat) * (t : ℝ)))
              * gaussianF (dim n) (t : ℝ)) := by
            exact mul_le_mul_of_nonneg_left htail_bound htex_nonneg
    _ = (Cmom / (fixedCountDelta t ^ (2 : Nat) * (t : ℝ))) * gaussianScale n (t : ℝ) := by
          rw [← hscale_eq]
          ring
      _ = (Cmom * (t : ℝ) ^ (-(1 / 5 : ℝ))) * gaussianScale n (t : ℝ) := by
          have hcoeff :
              Cmom / (fixedCountDelta t ^ (2 : Nat) * (t : ℝ)) = Cmom * (t : ℝ) ^ (-(1 / 5 : ℝ)) := by
            calc
              Cmom / (fixedCountDelta t ^ (2 : Nat) * (t : ℝ))
                  = Cmom * (fixedCountDelta t ^ (2 : Nat) * (t : ℝ))⁻¹ := by
                      rw [div_eq_mul_inv]
              _ = Cmom * (t : ℝ) ^ (-(1 / 5 : ℝ)) := by
                      have hbase :
                          (fixedCountDelta t ^ (2 : Nat) * (t : ℝ))⁻¹ = (t : ℝ) ^ (-(1 / 5 : ℝ)) := by
                        rw [fixedCountDelta_sq_mul_t_of_one_le ht1]
                        simpa using (Real.rpow_neg (show 0 ≤ (t : ℝ) by positivity) (1 / 5 : ℝ)).symm
                      exact congrArg (fun x : ℝ => Cmom * x) hbase
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            congrArg (fun x : ℝ => x * gaussianScale n (t : ℝ)) hcoeff

private lemma sqNormEdge_le_edgeCount_mul_sq_of_mem_edgeBox
    (n : ℕ) {delta : ℝ} (hdelta : 0 ≤ delta)
    {mu : Cn3Torus.Edge n → ℝ} (hmu : mu ∈ edgeBox n delta) :
    Cn3Torus.sqNormEdge n mu ≤ Cn3Torus.edgeCount n * delta ^ (2 : Nat) := by
  rw [edgeBox_eq_pi] at hmu
  unfold Cn3Torus.sqNormEdge
  calc
    ∑ e : Cn3Torus.Edge n, mu e ^ (2 : Nat)
      ≤ ∑ e : Cn3Torus.Edge n, delta ^ (2 : Nat) := by
          exact Finset.sum_le_sum (fun e he => by
            have hcoord := hmu e (by simp)
            have habs : |mu e| ≤ delta := by
              simpa [Set.mem_Icc, abs_le] using hcoord
            have habs_sq : |mu e| ^ (2 : Nat) ≤ delta ^ (2 : Nat) := by
              exact pow_le_pow_left₀ (abs_nonneg _) habs 2
            simpa [sq_abs] using habs_sq)
    _ = Cn3Torus.edgeCount n * delta ^ (2 : Nat) := by
          simp [Cn3Torus.edgeCount]

private lemma fixedCount_box_annulus_integral_bound
    (n : ℕ) :
    ∃ Cann : ℝ, 0 < Cann ∧
      ∀ᶠ t : ℕ in Filter.atTop,
        ∫ mu in (edgeBox n (fixedCountDelta t) \ edgeEuclidBall n (fixedCountDelta t)),
            ‖Cn3Torus.psi n mu‖ ^ (4 * t)
          ≤ (Cann * (t : ℝ) ^ (-(1 / 5 : ℝ))) * gaussianF (dim n) (t : ℝ) := by
  obtain ⟨r₀, Cann, hr₀_pos, hr₀_lt, hCann_pos, hannulus⟩ := fixedCount_annulus_integral_bound n
  have hdelta_r₀ := fixedCountDelta_eventually_le r₀ hr₀_pos
  have hdelta_box := fixedCountDelta_eventually_le Cn3Torus.delta Cn3Torus.delta_pos
  have hbox_small :
      ∀ᶠ t : ℕ in Filter.atTop,
        Cn3Torus.edgeCount n * fixedCountDelta t ^ (2 : Nat) ≤ r₀ ^ (2 : Nat) := by
    have hedgeCount_nonneg : 0 ≤ Cn3Torus.edgeCount n := by
      simp [Cn3Torus.edgeCount]
    filter_upwards
      [Filter.eventually_ge_atTop 1,
        const_mul_nat_rpow_neg_eventually_le (Cn3Torus.edgeCount n) (4 / 5 : ℝ) (r₀ ^ (2 : Nat))
          hedgeCount_nonneg (by positivity) (by positivity)] with t ht1 ht
    rw [fixedCountDelta_pow_of_one_le ht1 2]
    simpa [Cn3Torus.edgeCount, mul_comm, mul_left_comm, mul_assoc] using ht
  refine ⟨Cann, hCann_pos, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 2, hdelta_r₀, hdelta_box, hbox_small] with
      t ht2 hdelta_r₀_t hdelta_box_t hbox_small_t
  let A : Set (Cn3Torus.Edge n → ℝ) :=
    (edgeBox n Cn3Torus.delta ∩ edgeEuclidBall n r₀) \ edgeEuclidBall n (fixedCountDelta t)
  have hsubset : edgeBox n (fixedCountDelta t) \ edgeEuclidBall n (fixedCountDelta t) ⊆ A := by
    intro mu hmu
    refine ⟨?_, hmu.2⟩
    refine ⟨?_, ?_⟩
    · have hdelta_le_delta : fixedCountDelta t ≤ Cn3Torus.delta := by
        exact hdelta_box_t
      rw [edgeBox_eq_pi] at hmu ⊢
      intro e he
      have hcoord := hmu.1 e he
      exact ⟨le_trans (by linarith) hcoord.1, le_trans hcoord.2 hdelta_le_delta⟩
    · exact (mem_edgeEuclidBall_iff n r₀ mu).2 <|
        le_trans (sqNormEdge_le_edgeCount_mul_sq_of_mem_edgeBox n (fixedCountDelta_pos t).le hmu.1) hbox_small_t
  calc
    ∫ mu in (edgeBox n (fixedCountDelta t) \ edgeEuclidBall n (fixedCountDelta t)),
        ‖Cn3Torus.psi n mu‖ ^ (4 * t)
      ≤ ∫ mu in A, ‖Cn3Torus.psi n mu‖ ^ (4 * t) := by
          have hA_meas : MeasurableSet A := by
            dsimp [A]
            exact ((edgeBox_isCompact n Cn3Torus.delta).measurableSet.inter
              (measurableSet_edgeEuclidBall n r₀)).diff (measurableSet_edgeEuclidBall n (fixedCountDelta t))
          have hsmall_meas : MeasurableSet (edgeBox n (fixedCountDelta t) \ edgeEuclidBall n (fixedCountDelta t)) := by
            exact (edgeBox_isCompact n (fixedCountDelta t)).measurableSet.diff
              (measurableSet_edgeEuclidBall n (fixedCountDelta t))
          have hsmall_int :
              MeasureTheory.IntegrableOn
                (fun mu => ‖Cn3Torus.psi n mu‖ ^ (4 * t))
                (edgeBox n (fixedCountDelta t) \ edgeEuclidBall n (fixedCountDelta t)) := by
            simpa [MeasureTheory.IntegrableOn] using
              ((((Cn3Torus.continuous_psi n).norm.pow (4 * t)).continuousOn.integrableOn_compact
                  (edgeBox_isCompact n (fixedCountDelta t))).mono_set (by
                    intro mu hmu
                    exact hmu.1))
          have hA_int :
              MeasureTheory.IntegrableOn
                (fun mu => ‖Cn3Torus.psi n mu‖ ^ (4 * t)) A := by
            simpa [MeasureTheory.IntegrableOn] using
              ((((Cn3Torus.continuous_psi n).norm.pow (4 * t)).continuousOn.integrableOn_compact
                  (edgeBox_isCompact n Cn3Torus.delta)).mono_set (by
                    intro mu hmu
                    exact hmu.1.1))
          exact integralOn_mono_of_nonneg hsubset hsmall_meas hA_meas hA_int
            (Filter.Eventually.of_forall (fun _ => by positivity))
    _ ≤ (Cann / (fixedCountDelta t ^ (2 : Nat) * (t : ℝ))) * gaussianF (dim n) (t : ℝ) := by
          simpa [A] using hannulus t ht2 hdelta_r₀_t
    _ = (Cann * (t : ℝ) ^ (-(1 / 5 : ℝ))) * gaussianF (dim n) (t : ℝ) := by
          have ht1 : 1 ≤ t := by omega
          have hcoeff :
              Cann / (fixedCountDelta t ^ (2 : Nat) * (t : ℝ)) = Cann * (t : ℝ) ^ (-(1 / 5 : ℝ)) := by
            calc
              Cann / (fixedCountDelta t ^ (2 : Nat) * (t : ℝ))
                  = Cann * (fixedCountDelta t ^ (2 : Nat) * (t : ℝ))⁻¹ := by
                      rw [div_eq_mul_inv]
              _ = Cann * (t : ℝ) ^ (-(1 / 5 : ℝ)) := by
                      have hbase :
                          (fixedCountDelta t ^ (2 : Nat) * (t : ℝ))⁻¹ = (t : ℝ) ^ (-(1 / 5 : ℝ)) := by
                        rw [fixedCountDelta_sq_mul_t_of_one_le ht1]
                        simpa using (Real.rpow_neg (show 0 ≤ (t : ℝ) by positivity) (1 / 5 : ℝ)).symm
                      exact congrArg (fun x : ℝ => Cann * x) hbase
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            congrArg (fun x : ℝ => x * gaussianF (dim n) (t : ℝ)) hcoeff

private lemma fixedCountDelta_cos_pow_le_exp
    {t : ℕ} (ht : 1 ≤ t) :
    (Real.cos (fixedCountDelta t)) ^ (4 * t)
      ≤ Real.exp (-((8 / Real.pi ^ (2 : Nat)) : ℝ) * (t : ℝ) ^ (1 / 5 : ℝ)) := by
  let δ : ℝ := fixedCountDelta t
  let c : ℝ := (2 / Real.pi ^ (2 : Nat) : ℝ)
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hδ_pos : 0 < δ := fixedCountDelta_pos t
  have hδ_le_one : δ ≤ 1 := fixedCountDelta_le_one t
  have hδ_abs_pi : |δ| ≤ Real.pi := by
    have hpi : (1 : ℝ) ≤ Real.pi := by
      linarith [Real.pi_gt_three]
    rw [abs_of_nonneg hδ_pos.le]
    exact le_trans hδ_le_one hpi
  have hcos_nonneg : 0 ≤ Real.cos δ := by
    have hpi2 : (1 : ℝ) ≤ Real.pi / 2 := by
      linarith [Real.pi_gt_three]
    have hneg : -(Real.pi / 2) ≤ δ := by
      linarith [Real.pi_pos, hδ_pos]
    exact Real.cos_nonneg_of_mem_Icc ⟨hneg, le_trans hδ_le_one hpi2⟩
  have hc_nonneg : 0 ≤ c := by
    unfold c
    positivity [Real.pi_pos]
  have hcδ_le_one : c * δ ^ (2 : Nat) ≤ 1 := by
    have hc_le_one : c ≤ 1 := by
      unfold c
      have hpi_sq_pos : 0 < Real.pi ^ (2 : Nat) := by positivity [Real.pi_pos]
      have hpi_sq : (2 : ℝ) ≤ Real.pi ^ (2 : Nat) := by
        nlinarith [Real.pi_gt_three]
      exact (div_le_iff₀ hpi_sq_pos).2 (by simpa [one_mul] using hpi_sq)
    have hδsq_le_one : δ ^ (2 : Nat) ≤ 1 := by
      calc
        δ ^ (2 : Nat) ≤ (1 : ℝ) ^ (2 : Nat) := by
          exact pow_le_pow_left₀ hδ_pos.le hδ_le_one 2
        _ = 1 := by norm_num
    nlinarith
  have hbase_nonneg : 0 ≤ 1 - c * δ ^ (2 : Nat) := by
    linarith
  have hcos_le : Real.cos δ ≤ 1 - c * δ ^ (2 : Nat) := by
    have hraw := Real.cos_le_one_sub_mul_cos_sq (x := δ) hδ_abs_pi
    simpa [δ, c] using hraw
  have hpow_le :
      (Real.cos δ) ^ (4 * t) ≤ (1 - c * δ ^ (2 : Nat)) ^ (4 * t) := by
    exact pow_le_pow_left₀ hcos_nonneg hcos_le (4 * t)
  have hparam_le : ((4 * t : ℕ) : ℝ) * (c * δ ^ (2 : Nat)) ≤ (4 * t : ℕ) := by
    have h4t_nonneg : 0 ≤ ((4 * t : ℕ) : ℝ) := by positivity
    calc
      ((4 * t : ℕ) : ℝ) * (c * δ ^ (2 : Nat)) ≤ ((4 * t : ℕ) : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left hcδ_le_one h4t_nonneg
      _ = (4 * t : ℕ) := by ring
  have hpow_exp :
      (1 - c * δ ^ (2 : Nat)) ^ (4 * t)
        ≤ Real.exp (-(((4 * t : ℕ) : ℝ) * (c * δ ^ (2 : Nat)))) := by
    have hmain :=
      Real.one_sub_div_pow_le_exp_neg
        (n := 4 * t) (t := ((4 * t : ℕ) : ℝ) * (c * δ ^ (2 : Nat))) hparam_le
    have hden :
        (1 - (((4 * t : ℕ) : ℝ) * (c * δ ^ (2 : Nat))) / (4 * t : ℕ)) ^ (4 * t)
          = (1 - c * δ ^ (2 : Nat)) ^ (4 * t) := by
      have h4t_ne : ((4 * t : ℕ) : ℝ) ≠ 0 := by positivity
      congr 1
      field_simp [h4t_ne]
    rw [hden] at hmain
    exact hmain
  have hdelta_sq_mul :
      δ ^ (2 : Nat) * (t : ℝ) = (t : ℝ) ^ (1 / 5 : ℝ) := by
    simpa [δ] using fixedCountDelta_sq_mul_t_of_one_le ht
  calc
    (Real.cos (fixedCountDelta t)) ^ (4 * t) = (Real.cos δ) ^ (4 * t) := by rfl
    _ ≤ (1 - c * δ ^ (2 : Nat)) ^ (4 * t) := hpow_le
    _ ≤ Real.exp (-(((4 * t : ℕ) : ℝ) * (c * δ ^ (2 : Nat)))) := hpow_exp
    _ = Real.exp (-((8 / Real.pi ^ (2 : Nat)) : ℝ) * (t : ℝ) ^ (1 / 5 : ℝ)) := by
          have hcoeff :
              (((4 * t : ℕ) : ℝ) * (c * δ ^ (2 : Nat)))
                = ((8 / Real.pi ^ (2 : Nat)) : ℝ) * (t : ℝ) ^ (1 / 5 : ℝ) := by
            calc
              (((4 * t : ℕ) : ℝ) * (c * δ ^ (2 : Nat)))
                  = 4 * c * (δ ^ (2 : Nat) * (t : ℝ)) := by
                      norm_num
                      ring
              _ = 4 * c * (t : ℝ) ^ (1 / 5 : ℝ) := by rw [hdelta_sq_mul]
              _ = ((8 / Real.pi ^ (2 : Nat)) : ℝ) * (t : ℝ) ^ (1 / 5 : ℝ) := by
                      unfold c
                      ring
          congr 1
          rw [hcoeff]
          ring

private lemma fixedCount_residualContribution_bound
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℕ in Filter.atTop,
        |(1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ)) *
            ∫ lam in Cn3Torus.edgeResidualTorusRegion n (fixedCountDelta t),
              Complex.re (Cn3Torus.psi n lam ^ (4 * t))|
          ≤ ε * gaussianScale n (t : ℝ) := by
  intro ε hε
  have hdelta_lt : ∀ᶠ t : ℕ in Filter.atTop, fixedCountDelta t ≤ (3 / 4 : ℝ) := by
    exact fixedCountDelta_eventually_le (3 / 4 : ℝ) (by positivity)
  have hres_small :=
    exp_neg_mul_nat_rpow_le_eps_gaussianScale_fixed n hn ((8 / Real.pi ^ (2 : Nat)) : ℝ)
      (1 / 5 : ℝ) ε
      (by positivity [Real.pi_pos]) (by positivity) hε
  filter_upwards [Filter.eventually_ge_atTop 1, hdelta_lt, hres_small] with t ht1 hdelta_lt_t hres_small_t
  have hdelta_pos : 0 < fixedCountDelta t := fixedCountDelta_pos t
  have hdelta_lt_pi : fixedCountDelta t < Real.pi / 4 := by
    linarith [hdelta_lt_t, Real.pi_gt_three]
  calc
    |(1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ)) *
        ∫ lam in Cn3Torus.edgeResidualTorusRegion n (fixedCountDelta t),
          Complex.re (Cn3Torus.psi n lam ^ (4 * t))|
      ≤ (Real.cos (fixedCountDelta t)) ^ (4 * t) := by
          exact normalized_edgeResidualTorusRegion_abs_le_cos_pow n t hn hdelta_pos hdelta_lt_pi
    _ ≤ Real.exp (-((8 / Real.pi ^ (2 : Nat)) : ℝ) * (t : ℝ) ^ (1 / 5 : ℝ)) :=
          fixedCountDelta_cos_pow_le_exp ht1
    _ ≤ ε * gaussianScale n (t : ℝ) := hres_small_t

set_option maxHeartbeats 4000000 in
private lemma fixed_n_box_shell_scaled
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℕ in Filter.atTop,
        |Cn3Torus.texPrefactor n
            * (∫ mu in edgeBox n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
          - Cn3Torus.texPrefactor n
            * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n mu ^ (4 * t)))|
          ≤ ε * gaussianScale n (t : ℝ) := by
  intro ε hε
  obtain ⟨Cann, hCann_pos, hbox_annulus⟩ := fixedCount_box_annulus_integral_bound n
  have hbox_annulus_small :=
    const_mul_nat_rpow_neg_eventually_le Cann (1 / 5 : ℝ) ε
      (by positivity) (by positivity) hε
  filter_upwards [Filter.eventually_ge_atTop 2, hbox_annulus, hbox_annulus_small] with t ht2
      hbox_annulus_t hbox_annulus_small_t
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  let box : Set (Cn3Torus.Edge n → ℝ) := edgeBox n (fixedCountDelta t)
  let shell : Set (Cn3Torus.Edge n → ℝ) := box \ inner
  let T : ℝ := Cn3Torus.texPrefactor n
  let Jbox : ℝ := ∫ mu in box, Complex.re (Cn3Torus.psi n mu ^ (4 * t))
  let Jψ : ℝ := ∫ mu in inner, Complex.re (Cn3Torus.psi n mu ^ (4 * t))
  have hscale_pos : 0 < gaussianScale n (t : ℝ) := gaussianScale_pos n ht_pos
  have hscale_eq :
      T * gaussianF (dim n) (t : ℝ) = gaussianScale n (t : ℝ) := by
    simpa [T] using gaussianScale_eq_texPrefactor_mul_gaussianF n hn (t : ℝ) ht_pos
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact texPrefactor_nonneg n
  have hinner_subset_box : inner ⊆ box := by
    exact edgeEuclidBall_subset_edgeBox n (fixedCountDelta_pos t).le le_rfl
  have hshell_meas : MeasurableSet shell := by
    dsimp [shell, box, inner]
    exact (edgeBox_isCompact n (fixedCountDelta t)).measurableSet.diff
      (measurableSet_edgeEuclidBall n (fixedCountDelta t))
  have hpsi_box_int :
      MeasureTheory.IntegrableOn (fun mu => Cn3Torus.psi n mu ^ (4 * t)) box := by
    simpa [box, MeasureTheory.IntegrableOn] using
      (((Cn3Torus.continuous_psi n).pow (4 * t)).continuousOn.integrableOn_compact
        (edgeBox_isCompact n (fixedCountDelta t)))
  have hpsi_shell_int :
      MeasureTheory.IntegrableOn (fun mu => Cn3Torus.psi n mu ^ (4 * t)) shell := by
    exact hpsi_box_int.mono_set (by intro x hx; exact hx.1)
  have hpsi_inner_int :
      MeasureTheory.IntegrableOn (fun mu => Cn3Torus.psi n mu ^ (4 * t)) inner := by
    exact hpsi_box_int.mono_set hinner_subset_box
  have hre_inner_int :
      MeasureTheory.IntegrableOn (fun mu => Complex.re (Cn3Torus.psi n mu ^ (4 * t))) inner := by
    exact hpsi_inner_int.re
  have hre_shell_int :
      MeasureTheory.IntegrableOn (fun mu => Complex.re (Cn3Torus.psi n mu ^ (4 * t))) shell := by
    exact hpsi_shell_int.re
  have hbox_split :
      ∫ mu in box, Complex.re (Cn3Torus.psi n mu ^ (4 * t))
        = (∫ mu in inner, Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
            + ∫ mu in shell, Complex.re (Cn3Torus.psi n mu ^ (4 * t)) := by
    have hbox_eq : inner ∪ shell = box := by
      simpa [shell] using Set.union_diff_cancel hinner_subset_box
    have hinner_shell_disj : Disjoint inner shell := by
      rw [Set.disjoint_left]
      intro x hx hxs
      exact hxs.2 hx
    rw [← hbox_eq]
    exact MeasureTheory.integral_union_ae hinner_shell_disj.aedisjoint
      hshell_meas.nullMeasurableSet
      hre_inner_int hre_shell_int
  have hbox_repr :
      Jbox - Jψ = ∫ mu in shell, Complex.re (Cn3Torus.psi n mu ^ (4 * t)) := by
    dsimp [Jbox, Jψ]
    linarith [hbox_split]
  have habs_shell :
      |∫ mu in shell, Complex.re (Cn3Torus.psi n mu ^ (4 * t))|
        ≤ ∫ mu in shell, ‖Cn3Torus.psi n mu‖ ^ (4 * t) := by
    simpa [norm_pow] using
      (abs_integral_re_le_integral_norm (n := n) (s := shell)
        (f := fun mu => Cn3Torus.psi n mu ^ (4 * t)) hpsi_shell_int)
  have hbox_raw :
      |Jbox - Jψ| ≤ ∫ mu in shell, ‖Cn3Torus.psi n mu‖ ^ (4 * t) := by
    rw [hbox_repr]
    exact habs_shell
  have hbox_annulus_raw :
      ∫ mu in shell, ‖Cn3Torus.psi n mu‖ ^ (4 * t)
        ≤ (Cann * (t : ℝ) ^ (-(1 / 5 : ℝ))) * gaussianF (dim n) (t : ℝ) := by
    simpa [shell, box, inner] using hbox_annulus_t
  calc
    |Cn3Torus.texPrefactor n
          * (∫ mu in edgeBox n (fixedCountDelta t),
              Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
        - Cn3Torus.texPrefactor n
          * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Complex.re (Cn3Torus.psi n mu ^ (4 * t)))|
      = |T * Jbox - T * Jψ| := by
          simp [T, Jbox, Jψ, box, inner]
    _ ≤ ε * gaussianScale n (t : ℝ) := by
        refine le_trans ?_ (mul_le_mul_of_nonneg_right hbox_annulus_small_t (le_of_lt hscale_pos))
        exact scale_gap_le_of_gap_le_gaussianF hT_nonneg hscale_eq (le_trans hbox_raw hbox_annulus_raw)

private lemma fixed_n_exact_to_corrected_pointwise
    (n t : ℕ) {c₂ C₂ Cquart : ℝ}
    (ht1 : 1 ≤ t)
    (hsq_c₂_t : fixedCountDelta t ^ (2 : Nat) ≤ c₂)
    (hquart_small_t : 4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) ≤ 1)
    (hstep1_small_t : 4 * C₂ * ((t : ℝ) * fixedCountDelta t ^ (6 : Nat)) ≤ 1)
    (hstep1_pt : ∀ n : ℕ, ∀ t : ℕ, ∀ mu : Cn3Torus.Edge n → ℝ,
      Cn3Torus.sqNormEdge n mu ≤ c₂ →
      4 * (t : ℝ) * C₂ * Cn3Torus.sqNormEdge n mu ^ 3 ≤ 1 →
      ‖Cn3Torus.psi n mu ^ (4 * t) - correctedCoreIntegrand n t mu‖
        ≤ (8 * (t : ℝ) * C₂ * Cn3Torus.sqNormEdge n mu ^ 3)
            * Real.exp
                (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu
                  + 4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)))
    (hquart_pt : ∀ n : ℕ, ∀ lam : Fin n → Fin n → ℝ,
      |quarticCorr n lam| ≤ Cquart * sNorm n lam ^ (2 : Nat))
    (hC₂_nonneg : 0 ≤ C₂)
    (hCquart_nonneg : 0 ≤ Cquart)
    {mu : Cn3Torus.Edge n → ℝ}
    (hmu : mu ∈ edgeEuclidBall n (fixedCountDelta t)) :
    ‖Cn3Torus.psi n mu ^ (4 * t) - correctedCoreIntegrand n t mu‖
      ≤ (8 * Real.exp 1 * C₂ * (t : ℝ) ^ (-(7 / 5 : ℝ)))
          * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  set s : ℝ := Cn3Torus.sqNormEdge n mu
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Cn3Torus.sqNormEdge_nonneg n mu
  have hs_inner : s ≤ fixedCountDelta t ^ (2 : Nat) := by
    simpa [s] using (mem_edgeEuclidBall_iff n (fixedCountDelta t) mu).1 hmu
  have hs_small : s ≤ c₂ := le_trans hs_inner hsq_c₂_t
  have hquart_abs :
      |quarticCorr n (matrixOfEdge n mu)| ≤ Cquart * s ^ (2 : Nat) := by
    simpa [s, sNorm_matrixOfEdge_eq] using hquart_pt n (matrixOfEdge n mu)
  have hquart_exp :
      Real.exp (-2 * (t : ℝ) * s + 4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu))
        ≤ Real.exp 1 * Real.exp (-2 * (t : ℝ) * s) := by
    have hquart_term :
        4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu) ≤ 1 := by
      calc
        4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)
            ≤ 4 * (t : ℝ) * |quarticCorr n (matrixOfEdge n mu)| := by
                gcongr
                exact le_abs_self _
        _ ≤ 4 * (t : ℝ) * (Cquart * s ^ (2 : Nat)) := by
                gcongr
        _ ≤ 4 * (t : ℝ) * (Cquart * fixedCountDelta t ^ (4 : Nat)) := by
                have hs_sq :
                    s ^ (2 : Nat) ≤ fixedCountDelta t ^ (4 : Nat) := by
                  calc
                    s ^ (2 : Nat) ≤ (fixedCountDelta t ^ (2 : Nat)) ^ (2 : Nat) := by
                      exact pow_le_pow_left₀ hs_nonneg hs_inner 2
                    _ = fixedCountDelta t ^ (4 : Nat) := by ring
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hs_sq (by positivity))
                  (by positivity)
        _ = 4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) := by ring
        _ ≤ 1 := hquart_small_t
    calc
      Real.exp (-2 * (t : ℝ) * s + 4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu))
          ≤ Real.exp (-2 * (t : ℝ) * s + 1) := by
                gcongr
      _ = Real.exp 1 * Real.exp (-2 * (t : ℝ) * s) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have hsmall :
      4 * (t : ℝ) * C₂ * s ^ (3 : Nat) ≤ 1 := by
    have hs_cube :
        s ^ (3 : Nat) ≤ fixedCountDelta t ^ (6 : Nat) := by
      calc
        s ^ (3 : Nat) ≤ (fixedCountDelta t ^ (2 : Nat)) ^ (3 : Nat) := by
          exact pow_le_pow_left₀ hs_nonneg hs_inner 3
        _ = fixedCountDelta t ^ (6 : Nat) := by ring
    calc
      4 * (t : ℝ) * C₂ * s ^ (3 : Nat)
          = (4 * (t : ℝ) * C₂) * s ^ (3 : Nat) := by ring
      _ ≤ (4 * (t : ℝ) * C₂) * fixedCountDelta t ^ (6 : Nat) := by
          exact mul_le_mul_of_nonneg_left hs_cube (by positivity)
      _ = 4 * (t : ℝ) * C₂ * fixedCountDelta t ^ (6 : Nat) := by ring
      _ = 4 * C₂ * ((t : ℝ) * fixedCountDelta t ^ (6 : Nat)) := by ring
      _ ≤ 1 := hstep1_small_t
  have hmain := hstep1_pt n t mu hs_small hsmall
  calc
    ‖Cn3Torus.psi n mu ^ (4 * t) - correctedCoreIntegrand n t mu‖
        ≤ (8 * (t : ℝ) * C₂ * s ^ (3 : Nat))
              * Real.exp
                  (-2 * (t : ℝ) * s
                    + 4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)) := by
              simpa [s] using hmain
    _ ≤ (8 * (t : ℝ) * C₂ * fixedCountDelta t ^ (6 : Nat))
          * (Real.exp 1 * Real.exp (-2 * (t : ℝ) * s)) := by
            have hs_cube :
                s ^ (3 : Nat) ≤ fixedCountDelta t ^ (6 : Nat) := by
              calc
                s ^ (3 : Nat) ≤ (fixedCountDelta t ^ (2 : Nat)) ^ (3 : Nat) := by
                  exact pow_le_pow_left₀ hs_nonneg hs_inner 3
                _ = fixedCountDelta t ^ (6 : Nat) := by ring
            have hcoeff_le :
                8 * (t : ℝ) * C₂ * s ^ (3 : Nat)
                  ≤ 8 * (t : ℝ) * C₂ * fixedCountDelta t ^ (6 : Nat) := by
              calc
                8 * (t : ℝ) * C₂ * s ^ (3 : Nat)
                    = (8 * (t : ℝ) * C₂) * s ^ (3 : Nat) := by ring
                _ ≤ (8 * (t : ℝ) * C₂) * fixedCountDelta t ^ (6 : Nat) := by
                    exact mul_le_mul_of_nonneg_left hs_cube (by positivity)
                _ = 8 * (t : ℝ) * C₂ * fixedCountDelta t ^ (6 : Nat) := by ring
            exact mul_le_mul hcoeff_le hquart_exp (by positivity) (by positivity)
    _ = (8 * Real.exp 1 * C₂ * (t : ℝ) ^ (-(7 / 5 : ℝ)))
          * Real.exp (-2 * (t : ℝ) * s) := by
          have hpow6 :
              (t : ℝ) * fixedCountDelta t ^ (6 : Nat) = (t : ℝ) ^ (-(7 / 5 : ℝ)) := by
            calc
              (t : ℝ) * fixedCountDelta t ^ (6 : Nat)
                  = (t : ℝ) ^ (1 - (((2 * 6 : ℕ) : ℝ) / 5)) := by
                      simpa using t_mul_fixedCountDelta_pow_of_one_le ht1 6
              _ = (t : ℝ) ^ (-(7 / 5 : ℝ)) := by norm_num
          calc
            (8 * (t : ℝ) * C₂ * fixedCountDelta t ^ (6 : Nat))
                * (Real.exp 1 * Real.exp (-2 * (t : ℝ) * s))
                = 8 * C₂ * ((t : ℝ) * fixedCountDelta t ^ (6 : Nat))
                    * (Real.exp 1 * Real.exp (-2 * (t : ℝ) * s)) := by ring
            _ = 8 * C₂ * (t : ℝ) ^ (-(7 / 5 : ℝ))
                    * (Real.exp 1 * Real.exp (-2 * (t : ℝ) * s)) := by rw [hpow6]
            _ = (8 * Real.exp 1 * C₂ * (t : ℝ) ^ (-(7 / 5 : ℝ)))
                    * Real.exp (-2 * (t : ℝ) * s) := by ring
    _ = (8 * Real.exp 1 * C₂ * (t : ℝ) ^ (-(7 / 5 : ℝ)))
          * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
            simp [s]

private lemma fixed_n_exact_to_corrected_integral_raw
    (n t : ℕ) {c₂ C₂ Cquart : ℝ}
    (ht1 : 1 ≤ t)
    (hsq_c₂_t : fixedCountDelta t ^ (2 : Nat) ≤ c₂)
    (hquart_small_t : 4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) ≤ 1)
    (hstep1_small_t : 4 * C₂ * ((t : ℝ) * fixedCountDelta t ^ (6 : Nat)) ≤ 1)
    (hstep1_pt : ∀ n : ℕ, ∀ t : ℕ, ∀ mu : Cn3Torus.Edge n → ℝ,
      Cn3Torus.sqNormEdge n mu ≤ c₂ →
      4 * (t : ℝ) * C₂ * Cn3Torus.sqNormEdge n mu ^ 3 ≤ 1 →
      ‖Cn3Torus.psi n mu ^ (4 * t) - correctedCoreIntegrand n t mu‖
        ≤ (8 * (t : ℝ) * C₂ * Cn3Torus.sqNormEdge n mu ^ 3)
            * Real.exp
                (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu
                  + 4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)))
    (hquart_pt : ∀ n : ℕ, ∀ lam : Fin n → Fin n → ℝ,
      |quarticCorr n lam| ≤ Cquart * sNorm n lam ^ (2 : Nat))
    (hC₂_nonneg : 0 ≤ C₂)
    (hCquart_nonneg : 0 ≤ Cquart) :
    |((∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
        - (∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (correctedCoreIntegrand n t mu)))|
      ≤ (8 * Real.exp 1 * C₂ * (t : ℝ) ^ (-(7 / 5 : ℝ)))
          * ∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
  have ht_pos_nat : 0 < t := by omega
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  have hinner_meas : MeasurableSet inner := measurableSet_edgeEuclidBall n (fixedCountDelta t)
  have hinner_subset_box : inner ⊆ edgeBox n (fixedCountDelta t) := by
    exact edgeEuclidBall_subset_edgeBox n (fixedCountDelta_pos t).le le_rfl
  have hpsi_inner_int :
      MeasureTheory.IntegrableOn (fun mu => Cn3Torus.psi n mu ^ (4 * t)) inner := by
    simpa [MeasureTheory.IntegrableOn] using
      ((((Cn3Torus.continuous_psi n).pow (4 * t)).continuousOn.integrableOn_compact
          (edgeBox_isCompact n (fixedCountDelta t))).mono_set hinner_subset_box)
  have hcorr_inner_int :
      MeasureTheory.IntegrableOn (fun mu => correctedCoreIntegrand n t mu) inner := by
    simpa [MeasureTheory.IntegrableOn] using
      (((continuous_correctedCoreIntegrand n t).continuousOn.integrableOn_compact
          (edgeBox_isCompact n (fixedCountDelta t))).mono_set hinner_subset_box)
  have hg0_int :
      MeasureTheory.IntegrableOn
        (fun mu => Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) inner := by
    simpa [MeasureTheory.IntegrableOn] using
      (((Real.continuous_exp.comp
          ((continuous_const.mul (Cn3Torus.continuous_sqNormEdge n)).neg)).continuousOn.integrableOn_compact
          (edgeBox_isCompact n (fixedCountDelta t))).mono_set hinner_subset_box)
  have habs := abs_integral_re_sub_le_integral_norm
    (n := n) (s := inner) (f := fun mu => Cn3Torus.psi n mu ^ (4 * t))
    (g := fun mu => correctedCoreIntegrand n t mu) hpsi_inner_int hcorr_inner_int
  have hleft_int :
      MeasureTheory.IntegrableOn
        (fun mu => ‖Cn3Torus.psi n mu ^ (4 * t) - correctedCoreIntegrand n t mu‖) inner := by
    exact (hpsi_inner_int.sub hcorr_inner_int).norm
  have hright_int :
      MeasureTheory.IntegrableOn
        (fun mu =>
          (8 * Real.exp 1 * C₂ * (t : ℝ) ^ (-(7 / 5 : ℝ)))
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) inner := by
    exact (hg0_int.const_mul _)
  calc
    |(∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
        - (∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (correctedCoreIntegrand n t mu))|
        = |(∫ mu in inner, Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
            - (∫ mu in inner, Complex.re (correctedCoreIntegrand n t mu))| := by
            simp [inner]
    _ ≤ ∫ mu in inner, ‖Cn3Torus.psi n mu ^ (4 * t) - correctedCoreIntegrand n t mu‖ := by
            simpa [inner] using habs
    _ ≤ ∫ mu in inner,
          (8 * Real.exp 1 * C₂ * (t : ℝ) ^ (-(7 / 5 : ℝ)))
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
            have hmono :
                ∀ᵐ mu ∂MeasureTheory.volume.restrict inner,
                  ‖Cn3Torus.psi n mu ^ (4 * t) - correctedCoreIntegrand n t mu‖
                    ≤ (8 * Real.exp 1 * C₂ * (t : ℝ) ^ (-(7 / 5 : ℝ)))
                        * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
              rw [MeasureTheory.ae_restrict_iff' hinner_meas]
              exact Filter.Eventually.of_forall (fun mu hmu =>
                fixed_n_exact_to_corrected_pointwise (n := n) (t := t) (c₂ := c₂)
                  (C₂ := C₂) (Cquart := Cquart) ht1 hsq_c₂_t hquart_small_t hstep1_small_t
                  hstep1_pt hquart_pt hC₂_nonneg hCquart_nonneg hmu)
            exact MeasureTheory.integral_mono_ae hleft_int hright_int hmono
    _ = (8 * Real.exp 1 * C₂ * (t : ℝ) ^ (-(7 / 5 : ℝ)))
          * ∫ mu in inner, Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
            rw [MeasureTheory.integral_const_mul]
    _ = (8 * Real.exp 1 * C₂ * (t : ℝ) ^ (-(7 / 5 : ℝ)))
          * ∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
            simp [inner]

private lemma fixed_n_exact_to_corrected_raw_gaussianF
    (n t : ℕ) (ht1 : 1 ≤ t) {c₂ C₂ Cquart Cgauss0 : ℝ}
    (hsq_c₂_t : fixedCountDelta t ^ (2 : Nat) ≤ c₂)
    (hquart_small_t : 4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) ≤ 1)
    (hstep1_small_t : 4 * C₂ * ((t : ℝ) * fixedCountDelta t ^ (6 : Nat)) ≤ 1)
    (hstep1_pt : ∀ n : ℕ, ∀ t : ℕ, ∀ mu : Cn3Torus.Edge n → ℝ,
      Cn3Torus.sqNormEdge n mu ≤ c₂ →
      4 * (t : ℝ) * C₂ * Cn3Torus.sqNormEdge n mu ^ 3 ≤ 1 →
      ‖Cn3Torus.psi n mu ^ (4 * t) - correctedCoreIntegrand n t mu‖
        ≤ (8 * (t : ℝ) * C₂ * Cn3Torus.sqNormEdge n mu ^ 3)
            * Real.exp
                (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu
                  + 4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)))
    (hquart_pt : ∀ n : ℕ, ∀ lam : Fin n → Fin n → ℝ,
      |quarticCorr n lam| ≤ Cquart * sNorm n lam ^ (2 : Nat))
    (hC₂_nonneg : 0 ≤ C₂)
    (hCquart_nonneg : 0 ≤ Cquart)
    (hgauss0 : ∀ t : ℝ, 1 ≤ t →
      ∫ mu : Cn3Torus.Edge n → ℝ,
        Cn3Torus.sqNormEdge n mu ^ (0 : Nat)
          * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
          ≤ (Cgauss0 / t ^ (0 : Nat)) * gaussianF (dim n) t) :
    |((∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
        - (∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (correctedCoreIntegrand n t mu)))|
      ≤ (8 * Real.exp 1 * C₂ * Cgauss0 * (t : ℝ) ^ (-(7 / 5 : ℝ)))
          * gaussianF (dim n) (t : ℝ) := by
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  have hg0_int : MeasureTheory.Integrable
      (fun mu : Cn3Torus.Edge n → ℝ =>
        Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
    simpa [mul_assoc] using gaussian_integrable_edge n (2 * (t : ℝ)) (by positivity)
  have hg0_nonneg :
      ∀ mu : Cn3Torus.Edge n → ℝ,
        0 ≤ Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
    intro mu
    positivity
  have hinner_g0_le :
      ∫ mu in inner, Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
        ≤ ∫ mu : Cn3Torus.Edge n → ℝ, Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
    simpa [inner] using
      (integralOn_mono_of_nonneg (by intro _ _; simp)
        (measurableSet_edgeEuclidBall n (fixedCountDelta t))
        MeasurableSet.univ hg0_int.integrableOn
        (Filter.Eventually.of_forall hg0_nonneg))
  have hfull_g0 :
      ∫ mu : Cn3Torus.Edge n → ℝ, Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
        ≤ Cgauss0 * gaussianF (dim n) (t : ℝ) := by
    simpa using hgauss0 (t : ℝ) (by exact_mod_cast ht1)
  calc
    |((∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
        - (∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (correctedCoreIntegrand n t mu)))|
        ≤ (8 * Real.exp 1 * C₂ * (t : ℝ) ^ (-(7 / 5 : ℝ)))
            * ∫ mu in edgeEuclidBall n (fixedCountDelta t),
                Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
            exact fixed_n_exact_to_corrected_integral_raw (n := n) (t := t)
              (c₂ := c₂) (C₂ := C₂) (Cquart := Cquart)
              ht1 hsq_c₂_t hquart_small_t hstep1_small_t hstep1_pt hquart_pt
              hC₂_nonneg hCquart_nonneg
    _ ≤ (8 * Real.exp 1 * C₂ * (t : ℝ) ^ (-(7 / 5 : ℝ)))
          * ∫ mu : Cn3Torus.Edge n → ℝ,
              Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
          exact mul_le_mul_of_nonneg_left hinner_g0_le (by positivity)
    _ ≤ (8 * Real.exp 1 * C₂ * (t : ℝ) ^ (-(7 / 5 : ℝ)))
          * (Cgauss0 * gaussianF (dim n) (t : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hfull_g0 (by positivity)
    _ = (8 * Real.exp 1 * C₂ * Cgauss0 * (t : ℝ) ^ (-(7 / 5 : ℝ)))
          * gaussianF (dim n) (t : ℝ) := by
          ring

set_option maxHeartbeats 4000000 in
private lemma fixed_n_exact_to_corrected_scaled
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℕ in Filter.atTop,
        |Cn3Torus.texPrefactor n
            * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
          - Cn3Torus.texPrefactor n
            * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
                Complex.re (correctedCoreIntegrand n t mu))|
          ≤ ε * gaussianScale n (t : ℝ) := by
  intro ε hε
  obtain ⟨c₂, C₂, hc₂_pos, hC₂_pos, hstep1_pt⟩ := psi_pow_sub_correctedCoreIntegrand_norm_le_uniform
  obtain ⟨Cquart, hCquart_pos, hquart_pt⟩ := quarticCorr_pointwise_bound_uniform
  obtain ⟨Cgauss0, hCgauss0_pos, hgauss0⟩ := gaussian_radial_moments_edge n 0
  let K₁ : ℝ := 8 * Real.exp 1 * C₂ * Cgauss0
  have hK₁_nonneg : 0 ≤ K₁ := by
    unfold K₁
    positivity
  have hsq_c₂ :
      ∀ᶠ t : ℕ in Filter.atTop, fixedCountDelta t ^ (2 : Nat) ≤ c₂ := by
    simpa using
      const_mul_fixedCountDelta_pow_eventually_le 1 c₂ 2 (by positivity) (by norm_num) hc₂_pos
  have hquart_small :
      ∀ᶠ t : ℕ in Filter.atTop,
        4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) ≤ 1 := by
    simpa using
      const_mul_t_mul_fixedCountDelta_pow_eventually_le (4 * Cquart) 1 4 (by norm_num)
        (by positivity) (by norm_num)
  have hstep1_small :
      ∀ᶠ t : ℕ in Filter.atTop,
        4 * C₂ * ((t : ℝ) * fixedCountDelta t ^ (6 : Nat)) ≤ 1 := by
    simpa using
      const_mul_t_mul_fixedCountDelta_pow_eventually_le (4 * C₂) 1 6 (by norm_num)
        (by positivity) (by norm_num)
  have hstep1_small_coeff :=
    const_mul_nat_rpow_neg_eventually_le K₁ (7 / 5 : ℝ) ε
      hK₁_nonneg (by positivity) hε
  filter_upwards
    [Filter.eventually_ge_atTop 1, hsq_c₂, hquart_small, hstep1_small, hstep1_small_coeff]
    with t ht1 hsq_c₂_t hquart_small_t hstep1_small_t hstep1_small_coeff_t
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  let T : ℝ := Cn3Torus.texPrefactor n
  let Jψ : ℝ := ∫ mu in inner, Complex.re (Cn3Torus.psi n mu ^ (4 * t))
  let Jcorr : ℝ := ∫ mu in inner, Complex.re (correctedCoreIntegrand n t mu)
  have hscale_pos : 0 < gaussianScale n (t : ℝ) := gaussianScale_pos n ht_pos
  have hscale_eq :
      T * gaussianF (dim n) (t : ℝ) = gaussianScale n (t : ℝ) := by
    simpa [T] using gaussianScale_eq_texPrefactor_mul_gaussianF n hn (t : ℝ) ht_pos
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact texPrefactor_nonneg n
  have hbound :
      |Jψ - Jcorr| ≤ (K₁ * (t : ℝ) ^ (-(7 / 5 : ℝ))) * gaussianF (dim n) (t : ℝ) := by
    simpa [K₁] using
      fixed_n_exact_to_corrected_raw_gaussianF (n := n) (t := t) ht1
        (c₂ := c₂) (C₂ := C₂) (Cquart := Cquart) (Cgauss0 := Cgauss0)
        hsq_c₂_t hquart_small_t hstep1_small_t hstep1_pt hquart_pt
        hC₂_pos.le hCquart_pos.le hgauss0
  have hstep1_scaled :
      |T * Jψ - T * Jcorr| ≤ ε * gaussianScale n (t : ℝ) := by
    exact scaled_gap_le_of_gap_le_gaussianF_and_coeff hT_nonneg (le_of_lt hscale_pos)
      hscale_eq hbound hstep1_small_coeff_t
  calc
    |Cn3Torus.texPrefactor n
          * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
        - Cn3Torus.texPrefactor n
          * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Complex.re (correctedCoreIntegrand n t mu))|
      = |T * Jψ - T * Jcorr| := by
          simp [T, Jψ, Jcorr, inner]
    _ ≤ ε * gaussianScale n (t : ℝ) := hstep1_scaled

private lemma fixed_n_corrected_to_quartic_pointwise
    (n t : ℕ) {Cq5 Cquart : ℝ}
    (hquart_small_t : 4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) ≤ 1)
    (hquintic_pt : ∀ lam : Fin n → Fin n → ℝ,
      |quinticP5 n lam| ≤ Cq5 * sNorm n lam ^ (5 / 2 : ℝ))
    (hquart_pt : ∀ n : ℕ, ∀ lam : Fin n → Fin n → ℝ,
      |quarticCorr n lam| ≤ Cquart * sNorm n lam ^ (2 : Nat))
    (hCq5_nonneg : 0 ≤ Cq5)
    (hCquart_nonneg : 0 ≤ Cquart)
    {mu : Cn3Torus.Edge n → ℝ}
    (hmu : mu ∈ edgeEuclidBall n (fixedCountDelta t)) :
    ‖correctedCoreIntegrand n t mu - quarticCoreIntegrand n t mu‖
      ≤ (4 * Real.exp 1 * Cq5 * (t : ℝ))
          * (Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
              * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
  set s : ℝ := Cn3Torus.sqNormEdge n mu
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Cn3Torus.sqNormEdge_nonneg n mu
  have hs_inner : s ≤ fixedCountDelta t ^ (2 : Nat) := by
    simpa [s] using (mem_edgeEuclidBall_iff n (fixedCountDelta t) mu).1 hmu
  have hdelta_sq_le_one : fixedCountDelta t ^ (2 : Nat) ≤ 1 := by
    calc
      fixedCountDelta t ^ (2 : Nat) ≤ (1 : ℝ) ^ (2 : Nat) := by
            exact pow_le_pow_left₀ (by positivity [fixedCountDelta_pos t]) (fixedCountDelta_le_one t) 2
      _ = 1 := by norm_num
  have hs_le_one : s ≤ 1 := le_trans hs_inner hdelta_sq_le_one
  have hs52_le_sq : s ^ (5 / 2 : ℝ) ≤ s ^ (2 : Nat) := by
    rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num,
      Real.rpow_add_of_nonneg hs_nonneg (by positivity) (by positivity)]
    calc
      s ^ (2 : ℝ) * s ^ (1 / 2 : ℝ) ≤ s ^ (2 : ℝ) * 1 := by
            gcongr
            exact Real.rpow_le_one hs_nonneg hs_le_one (by positivity)
      _ = s ^ (2 : Nat) := by norm_num
  have hquart_abs :
      |quarticCorr n (matrixOfEdge n mu)| ≤ Cquart * s ^ (2 : Nat) := by
    simpa [s, sNorm_matrixOfEdge_eq] using hquart_pt n (matrixOfEdge n mu)
  have hquart_exp :
      Real.exp (-2 * (t : ℝ) * s + 4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu))
        ≤ Real.exp 1 * Real.exp (-2 * (t : ℝ) * s) := by
    have hquart_term :
        4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu) ≤ 1 := by
      calc
        4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)
            ≤ 4 * (t : ℝ) * |quarticCorr n (matrixOfEdge n mu)| := by
                gcongr
                exact le_abs_self _
        _ ≤ 4 * (t : ℝ) * (Cquart * s ^ (2 : Nat)) := by
                gcongr
        _ ≤ 4 * (t : ℝ) * (Cquart * fixedCountDelta t ^ (4 : Nat)) := by
                have hs_sq :
                    s ^ (2 : Nat) ≤ fixedCountDelta t ^ (4 : Nat) := by
                  calc
                    s ^ (2 : Nat) ≤ (fixedCountDelta t ^ (2 : Nat)) ^ (2 : Nat) := by
                      exact pow_le_pow_left₀ hs_nonneg hs_inner 2
                    _ = fixedCountDelta t ^ (4 : Nat) := by ring
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hs_sq (by positivity))
                  (by positivity)
        _ = 4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) := by ring
        _ ≤ 1 := hquart_small_t
    calc
      Real.exp (-2 * (t : ℝ) * s + 4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu))
          ≤ Real.exp (-2 * (t : ℝ) * s + 1) := by
                gcongr
      _ = Real.exp 1 * Real.exp (-2 * (t : ℝ) * s) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have hquintic_abs :
      |quinticP5 n (matrixOfEdge n mu)| ≤ Cq5 * s ^ (5 / 2 : ℝ) := by
    simpa [s, sNorm_matrixOfEdge_eq] using hquintic_pt (matrixOfEdge n mu)
  calc
    ‖correctedCoreIntegrand n t mu - quarticCoreIntegrand n t mu‖
        ≤ (4 * (t : ℝ) * |quinticP5 n (matrixOfEdge n mu)|)
            * Real.exp
                (-2 * (t : ℝ) * s + 4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)) := by
              simpa [s] using correctedCoreIntegrand_sub_quarticCoreIntegrand_norm_le n t mu
    _ ≤ (4 * (t : ℝ) * (Cq5 * s ^ (5 / 2 : ℝ)))
          * (Real.exp 1 * Real.exp (-2 * (t : ℝ) * s)) := by
            have hcoeff_le :
                4 * (t : ℝ) * |quinticP5 n (matrixOfEdge n mu)|
                  ≤ 4 * (t : ℝ) * (Cq5 * s ^ (5 / 2 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hquintic_abs (by positivity)
            exact mul_le_mul hcoeff_le hquart_exp (by positivity) (by positivity)
    _ ≤ (4 * (t : ℝ) * (Cq5 * s ^ (2 : Nat)))
          * (Real.exp 1 * Real.exp (-2 * (t : ℝ) * s)) := by
            have hcoeff_le :
                4 * (t : ℝ) * (Cq5 * s ^ (5 / 2 : ℝ))
                  ≤ 4 * (t : ℝ) * (Cq5 * s ^ (2 : Nat)) := by
              calc
                4 * (t : ℝ) * (Cq5 * s ^ (5 / 2 : ℝ))
                    = (4 * (t : ℝ) * Cq5) * s ^ (5 / 2 : ℝ) := by ring
                _ ≤ (4 * (t : ℝ) * Cq5) * s ^ (2 : Nat) := by
                    exact mul_le_mul_of_nonneg_left hs52_le_sq (by positivity)
                _ = 4 * (t : ℝ) * (Cq5 * s ^ (2 : Nat)) := by ring
            exact mul_le_mul_of_nonneg_right hcoeff_le (by positivity)
    _ = (4 * Real.exp 1 * Cq5 * (t : ℝ))
          * (s ^ (2 : Nat) * Real.exp (-2 * (t : ℝ) * s)) := by ring
    _ = (4 * Real.exp 1 * Cq5 * (t : ℝ))
          * (Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
              * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
            simp [s]

private lemma fixed_n_corrected_to_quartic_integral_raw
    (n t : ℕ) (ht1 : 1 ≤ t) {Cq5 Cquart : ℝ}
    (hquart_small_t : 4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) ≤ 1)
    (hquintic_pt : ∀ lam : Fin n → Fin n → ℝ,
      |quinticP5 n lam| ≤ Cq5 * sNorm n lam ^ (5 / 2 : ℝ))
    (hquart_pt : ∀ n : ℕ, ∀ lam : Fin n → Fin n → ℝ,
      |quarticCorr n lam| ≤ Cquart * sNorm n lam ^ (2 : Nat))
    (hCq5_nonneg : 0 ≤ Cq5)
    (hCquart_nonneg : 0 ≤ Cquart) :
    |((∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (correctedCoreIntegrand n t mu))
        - (∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (quarticCoreIntegrand n t mu)))|
      ≤ (4 * Real.exp 1 * Cq5 * (t : ℝ))
          * ∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  have hinner_meas : MeasurableSet inner := measurableSet_edgeEuclidBall n (fixedCountDelta t)
  have hinner_subset_box : inner ⊆ edgeBox n (fixedCountDelta t) := by
    exact edgeEuclidBall_subset_edgeBox n (fixedCountDelta_pos t).le le_rfl
  have hcorr_inner_int :
      MeasureTheory.IntegrableOn (fun mu => correctedCoreIntegrand n t mu) inner := by
    simpa [MeasureTheory.IntegrableOn] using
      (((continuous_correctedCoreIntegrand n t).continuousOn.integrableOn_compact
          (edgeBox_isCompact n (fixedCountDelta t))).mono_set hinner_subset_box)
  have hquart_inner_int :
      MeasureTheory.IntegrableOn (fun mu => quarticCoreIntegrand n t mu) inner := by
    simpa [MeasureTheory.IntegrableOn] using
      (((continuous_quarticCoreIntegrand n t).continuousOn.integrableOn_compact
          (edgeBox_isCompact n (fixedCountDelta t))).mono_set hinner_subset_box)
  have hmoment2_int :
      MeasureTheory.IntegrableOn
        (fun mu =>
          Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) inner := by
    have hfull :
        MeasureTheory.Integrable
          (fun mu : Cn3Torus.Edge n → ℝ =>
            Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
              * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
      have ht_pos_nat : 0 < t := by omega
      have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
      simpa using sqNorm_moment_gaussian_integrable_edge n 2 (by norm_num) (t : ℝ) ht_pos
    exact hfull.integrableOn
  have habs := abs_integral_re_sub_le_integral_norm
    (n := n) (s := inner) (f := fun mu => correctedCoreIntegrand n t mu)
    (g := fun mu => quarticCoreIntegrand n t mu) hcorr_inner_int hquart_inner_int
  have hleft_int :
      MeasureTheory.IntegrableOn
        (fun mu => ‖correctedCoreIntegrand n t mu - quarticCoreIntegrand n t mu‖) inner := by
    exact (hcorr_inner_int.sub hquart_inner_int).norm
  have hright_int :
      MeasureTheory.IntegrableOn
        (fun mu =>
          (4 * Real.exp 1 * Cq5 * (t : ℝ))
            * (Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))) inner := by
    exact hmoment2_int.const_mul _
  calc
    |((∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (correctedCoreIntegrand n t mu))
        - (∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (quarticCoreIntegrand n t mu)))|
        = |(∫ mu in inner, Complex.re (correctedCoreIntegrand n t mu))
            - (∫ mu in inner, Complex.re (quarticCoreIntegrand n t mu))| := by
            simp [inner]
    _ ≤ ∫ mu in inner, ‖correctedCoreIntegrand n t mu - quarticCoreIntegrand n t mu‖ := by
            simpa [inner] using habs
    _ ≤ ∫ mu in inner,
          (4 * Real.exp 1 * Cq5 * (t : ℝ))
            * (Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
            have hmono :
                ∀ᵐ mu ∂MeasureTheory.volume.restrict inner,
                  ‖correctedCoreIntegrand n t mu - quarticCoreIntegrand n t mu‖
                    ≤ (4 * Real.exp 1 * Cq5 * (t : ℝ))
                        * (Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
              rw [MeasureTheory.ae_restrict_iff' hinner_meas]
              exact Filter.Eventually.of_forall (fun mu hmu =>
                fixed_n_corrected_to_quartic_pointwise (n := n) (t := t) (Cq5 := Cq5)
                  (Cquart := Cquart) hquart_small_t hquintic_pt hquart_pt
                  hCq5_nonneg hCquart_nonneg hmu)
            exact MeasureTheory.integral_mono_ae hleft_int hright_int hmono
    _ = (4 * Real.exp 1 * Cq5 * (t : ℝ))
          * ∫ mu in inner,
              Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
            rw [MeasureTheory.integral_const_mul]
    _ = (4 * Real.exp 1 * Cq5 * (t : ℝ))
          * ∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
            simp [inner]

private lemma fixed_n_corrected_to_quartic_raw_gaussianF
    (n t : ℕ) (ht1 : 1 ≤ t) {Cq5 Cquart Cgauss2 : ℝ}
    (hquart_small_t : 4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) ≤ 1)
    (hquintic_pt : ∀ lam : Fin n → Fin n → ℝ,
      |quinticP5 n lam| ≤ Cq5 * sNorm n lam ^ (5 / 2 : ℝ))
    (hquart_pt : ∀ n : ℕ, ∀ lam : Fin n → Fin n → ℝ,
      |quarticCorr n lam| ≤ Cquart * sNorm n lam ^ (2 : Nat))
    (hCq5_nonneg : 0 ≤ Cq5)
    (hCquart_nonneg : 0 ≤ Cquart)
    (hgauss2 : ∀ t : ℝ, 1 ≤ t →
      ∫ mu : Cn3Torus.Edge n → ℝ,
        Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
          * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
          ≤ (Cgauss2 / t ^ (2 : Nat)) * gaussianF (dim n) t) :
    |((∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (correctedCoreIntegrand n t mu))
        - (∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (quarticCoreIntegrand n t mu)))|
      ≤ (4 * Real.exp 1 * Cq5 * Cgauss2 * (t : ℝ) ^ (-(1 : ℝ)))
          * gaussianF (dim n) (t : ℝ) := by
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  have hmoment2_int :
      MeasureTheory.Integrable
        (fun mu : Cn3Torus.Edge n → ℝ =>
          Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
    simpa using sqNorm_moment_gaussian_integrable_edge n 2 (by norm_num) (t : ℝ) ht_pos
  have hmoment2_inner_le :
      ∫ mu in inner,
          Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
        ≤ (Cgauss2 / (t : ℝ) ^ (2 : Nat)) * gaussianF (dim n) (t : ℝ) := by
    have hpoint_nonneg :
        ∀ mu : Cn3Torus.Edge n → ℝ,
          0 ≤ Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
      intro mu
      positivity
    calc
      ∫ mu in inner,
          Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
          ≤ ∫ mu : Cn3Torus.Edge n → ℝ,
              Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
                simpa [inner] using
                  (integralOn_mono_of_nonneg (by intro _ _; simp)
                    (measurableSet_edgeEuclidBall n (fixedCountDelta t))
                    MeasurableSet.univ hmoment2_int.integrableOn
                    (Filter.Eventually.of_forall hpoint_nonneg))
      _ ≤ (Cgauss2 / (t : ℝ) ^ (2 : Nat)) * gaussianF (dim n) (t : ℝ) := by
            simpa using hgauss2 (t : ℝ) (by exact_mod_cast ht1)
  calc
    |((∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (correctedCoreIntegrand n t mu))
        - (∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (quarticCoreIntegrand n t mu)))|
        ≤ (4 * Real.exp 1 * Cq5 * (t : ℝ))
            * ∫ mu in edgeEuclidBall n (fixedCountDelta t),
                Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                  * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
            exact fixed_n_corrected_to_quartic_integral_raw (n := n) (t := t) ht1
              (Cq5 := Cq5) (Cquart := Cquart) hquart_small_t hquintic_pt hquart_pt
              hCq5_nonneg hCquart_nonneg
    _ ≤ (4 * Real.exp 1 * Cq5 * (t : ℝ))
          * ((Cgauss2 / (t : ℝ) ^ (2 : Nat)) * gaussianF (dim n) (t : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hmoment2_inner_le (by positivity)
    _ = (4 * Real.exp 1 * Cq5 * Cgauss2 * (t : ℝ) ^ (-(1 : ℝ)))
          * gaussianF (dim n) (t : ℝ) := by
          have hpow : 1 / (t : ℝ) = (t : ℝ) ^ (-(1 : ℝ)) := by
            symm
            simpa using (rpow_neg_nat_eq_inv_pow ht_pos 1)
          rw [← hpow]
          field_simp [ht_pos.ne']

set_option maxHeartbeats 4000000 in
private lemma fixed_n_corrected_to_quartic_scaled
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℕ in Filter.atTop,
        |Cn3Torus.texPrefactor n
            * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
                Complex.re (correctedCoreIntegrand n t mu))
          - Cn3Torus.texPrefactor n
            * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
                Complex.re (quarticCoreIntegrand n t mu))|
          ≤ ε * gaussianScale n (t : ℝ) := by
  intro ε hε
  obtain ⟨Cq5, hCq5_pos, hquintic_pt⟩ := quinticP5_pointwise_bound n
  obtain ⟨Cquart, hCquart_pos, hquart_pt⟩ := quarticCorr_pointwise_bound_uniform
  obtain ⟨Cgauss2, hCgauss2_pos, hgauss2⟩ := gaussian_radial_moments_edge n 2
  let K₂ : ℝ := 4 * Real.exp 1 * Cq5 * Cgauss2
  have hK₂_nonneg : 0 ≤ K₂ := by
    unfold K₂
    positivity
  have hquart_small :
      ∀ᶠ t : ℕ in Filter.atTop,
        4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) ≤ 1 := by
    simpa using
      const_mul_t_mul_fixedCountDelta_pow_eventually_le (4 * Cquart) 1 4 (by norm_num)
        (by positivity) (by norm_num)
  have hstep2_small_coeff :=
    const_mul_nat_rpow_neg_eventually_le K₂ 1 ε
      hK₂_nonneg (by positivity) hε
  filter_upwards
    [Filter.eventually_ge_atTop 1, hquart_small, hstep2_small_coeff]
    with t ht1 hquart_small_t hstep2_small_coeff_t
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  let T : ℝ := Cn3Torus.texPrefactor n
  let Jcorr : ℝ := ∫ mu in inner, Complex.re (correctedCoreIntegrand n t mu)
  let Jquart : ℝ := ∫ mu in inner, Complex.re (quarticCoreIntegrand n t mu)
  have hscale_pos : 0 < gaussianScale n (t : ℝ) := gaussianScale_pos n ht_pos
  have hscale_eq :
      T * gaussianF (dim n) (t : ℝ) = gaussianScale n (t : ℝ) := by
    simpa [T] using gaussianScale_eq_texPrefactor_mul_gaussianF n hn (t : ℝ) ht_pos
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact texPrefactor_nonneg n
  have hbound :
      |Jcorr - Jquart| ≤ (K₂ * (t : ℝ) ^ (-(1 : ℝ))) * gaussianF (dim n) (t : ℝ) := by
    simpa [K₂] using
      fixed_n_corrected_to_quartic_raw_gaussianF (n := n) (t := t) ht1
        (Cq5 := Cq5) (Cquart := Cquart) (Cgauss2 := Cgauss2)
        hquart_small_t hquintic_pt hquart_pt hCq5_pos.le hCquart_pos.le hgauss2
  have hstep2_scaled :
      |T * Jcorr - T * Jquart| ≤ ε * gaussianScale n (t : ℝ) := by
    exact scaled_gap_le_of_gap_le_gaussianF_and_coeff hT_nonneg (le_of_lt hscale_pos)
      hscale_eq hbound hstep2_small_coeff_t
  calc
    |Cn3Torus.texPrefactor n
          * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Complex.re (correctedCoreIntegrand n t mu))
        - Cn3Torus.texPrefactor n
          * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Complex.re (quarticCoreIntegrand n t mu))|
      = |T * Jcorr - T * Jquart| := by
          simp [T, Jcorr, Jquart, inner]
    _ ≤ ε * gaussianScale n (t : ℝ) := hstep2_scaled

private lemma fixed_n_quartic_to_cubic_pointwise
    (n t : ℕ) {Cquart : ℝ}
    (ht1 : 1 ≤ t)
    (hquart_small_t : 4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) ≤ 1)
    (hquart_pt : ∀ n : ℕ, ∀ lam : Fin n → Fin n → ℝ,
      |quarticCorr n lam| ≤ Cquart * sNorm n lam ^ (2 : Nat))
    (hCquart_nonneg : 0 ≤ Cquart)
    {mu : Cn3Torus.Edge n → ℝ}
    (hmu : mu ∈ edgeEuclidBall n (fixedCountDelta t)) :
    ‖quarticCoreIntegrand n t mu - cubicCoreIntegrand n t mu‖
      ≤ (8 * Cquart * (t : ℝ))
          * (Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
              * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  set s : ℝ := Cn3Torus.sqNormEdge n mu
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Cn3Torus.sqNormEdge_nonneg n mu
  have hs_inner : s ≤ fixedCountDelta t ^ (2 : Nat) := by
    simpa [s] using (mem_edgeEuclidBall_iff n (fixedCountDelta t) mu).1 hmu
  have hquart_abs :
      |quarticCorr n (matrixOfEdge n mu)| ≤ Cquart * s ^ (2 : Nat) := by
    simpa [s, sNorm_matrixOfEdge_eq] using hquart_pt n (matrixOfEdge n mu)
  calc
    ‖quarticCoreIntegrand n t mu - cubicCoreIntegrand n t mu‖
        = Real.exp (-2 * (t : ℝ) * s)
            * |Real.exp (4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)) - 1| := by
              simpa [s] using quarticCoreIntegrand_sub_cubicCoreIntegrand_norm_eq n t mu
    _ ≤ Real.exp (-2 * (t : ℝ) * s)
          * (2 * |4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)|) := by
            gcongr
            simpa using abs_exp_sub_one_le
              (x := 4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu))
              (by
                calc
                  |4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)|
                      ≤ 4 * (t : ℝ) * |quarticCorr n (matrixOfEdge n mu)| := by
                            rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg ht_pos.le]
                  _ ≤ 4 * (t : ℝ) * (Cquart * s ^ (2 : Nat)) := by
                            exact mul_le_mul_of_nonneg_left hquart_abs (by positivity)
                  _ ≤ 4 * (t : ℝ) * (Cquart * fixedCountDelta t ^ (4 : Nat)) := by
                            have hs_sq :
                                s ^ (2 : Nat) ≤ fixedCountDelta t ^ (4 : Nat) := by
                              calc
                                s ^ (2 : Nat) ≤ (fixedCountDelta t ^ (2 : Nat)) ^ (2 : Nat) := by
                                  exact pow_le_pow_left₀ hs_nonneg hs_inner 2
                                _ = fixedCountDelta t ^ (4 : Nat) := by ring
                            exact mul_le_mul_of_nonneg_left
                              (mul_le_mul_of_nonneg_left hs_sq (by positivity))
                              (by positivity)
                  _ = 4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) := by ring
                  _ ≤ 1 := hquart_small_t)
    _ ≤ Real.exp (-2 * (t : ℝ) * s)
          * (2 * (4 * (t : ℝ) * (Cquart * s ^ (2 : Nat)))) := by
            have habs :
                |4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)|
                  ≤ 4 * (t : ℝ) * (Cquart * s ^ (2 : Nat)) := by
              calc
                |4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)|
                    = 4 * (t : ℝ) * |quarticCorr n (matrixOfEdge n mu)| := by
                        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg ht_pos.le]
                _ ≤ 4 * (t : ℝ) * (Cquart * s ^ (2 : Nat)) := by
                        exact mul_le_mul_of_nonneg_left hquart_abs (by positivity)
            have hinner :
                2 * |4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)|
                  ≤ 2 * (4 * (t : ℝ) * (Cquart * s ^ (2 : Nat))) := by
              exact mul_le_mul_of_nonneg_left habs (by positivity)
            exact mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (8 * Cquart * (t : ℝ))
          * (s ^ (2 : Nat) * Real.exp (-2 * (t : ℝ) * s)) := by
            ring
    _ = (8 * Cquart * (t : ℝ))
          * (Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
              * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
            simp [s]

private lemma fixed_n_quartic_to_cubic_integral_raw
    (n t : ℕ) (ht1 : 1 ≤ t) {Cquart : ℝ}
    (hquart_small_t : 4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) ≤ 1)
    (hquart_pt : ∀ n : ℕ, ∀ lam : Fin n → Fin n → ℝ,
      |quarticCorr n lam| ≤ Cquart * sNorm n lam ^ (2 : Nat))
    (hCquart_nonneg : 0 ≤ Cquart) :
    |((∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (quarticCoreIntegrand n t mu))
        - (∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (cubicCoreIntegrand n t mu)))|
      ≤ (8 * Cquart * (t : ℝ))
          * ∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  have hinner_meas : MeasurableSet inner := measurableSet_edgeEuclidBall n (fixedCountDelta t)
  have hinner_subset_box : inner ⊆ edgeBox n (fixedCountDelta t) := by
    exact edgeEuclidBall_subset_edgeBox n (fixedCountDelta_pos t).le le_rfl
  have hquart_inner_int :
      MeasureTheory.IntegrableOn (fun mu => quarticCoreIntegrand n t mu) inner := by
    simpa [MeasureTheory.IntegrableOn] using
      (((continuous_quarticCoreIntegrand n t).continuousOn.integrableOn_compact
          (edgeBox_isCompact n (fixedCountDelta t))).mono_set hinner_subset_box)
  have hcubic_inner_int :
      MeasureTheory.IntegrableOn (fun mu => cubicCoreIntegrand n t mu) inner := by
    simpa [MeasureTheory.IntegrableOn] using
      (((continuous_cubicCoreIntegrand n t).continuousOn.integrableOn_compact
          (edgeBox_isCompact n (fixedCountDelta t))).mono_set hinner_subset_box)
  have hmoment2_int :
      MeasureTheory.IntegrableOn
        (fun mu =>
          Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) inner := by
    have hfull :
        MeasureTheory.Integrable
          (fun mu : Cn3Torus.Edge n → ℝ =>
            Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
              * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
      have ht_pos_nat : 0 < t := by omega
      have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
      simpa using sqNorm_moment_gaussian_integrable_edge n 2 (by norm_num) (t : ℝ) ht_pos
    exact hfull.integrableOn
  have habs := abs_integral_re_sub_le_integral_norm
    (n := n) (s := inner) (f := fun mu => quarticCoreIntegrand n t mu)
    (g := fun mu => cubicCoreIntegrand n t mu) hquart_inner_int hcubic_inner_int
  have hleft_int :
      MeasureTheory.IntegrableOn
        (fun mu => ‖quarticCoreIntegrand n t mu - cubicCoreIntegrand n t mu‖) inner := by
    exact (hquart_inner_int.sub hcubic_inner_int).norm
  have hright_int :
      MeasureTheory.IntegrableOn
        (fun mu =>
          (8 * Cquart * (t : ℝ))
            * (Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))) inner := by
    exact hmoment2_int.const_mul _
  calc
    |((∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (quarticCoreIntegrand n t mu))
        - (∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (cubicCoreIntegrand n t mu)))|
        = |(∫ mu in inner, Complex.re (quarticCoreIntegrand n t mu))
            - (∫ mu in inner, Complex.re (cubicCoreIntegrand n t mu))| := by
            simp [inner]
    _ ≤ ∫ mu in inner, ‖quarticCoreIntegrand n t mu - cubicCoreIntegrand n t mu‖ := by
            simpa [inner] using habs
    _ ≤ ∫ mu in inner,
          (8 * Cquart * (t : ℝ))
            * (Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
            have hmono :
                ∀ᵐ mu ∂MeasureTheory.volume.restrict inner,
                  ‖quarticCoreIntegrand n t mu - cubicCoreIntegrand n t mu‖
                    ≤ (8 * Cquart * (t : ℝ))
                        * (Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
              rw [MeasureTheory.ae_restrict_iff' hinner_meas]
              exact Filter.Eventually.of_forall (fun mu hmu =>
                fixed_n_quartic_to_cubic_pointwise (n := n) (t := t) (Cquart := Cquart)
                  ht1 hquart_small_t hquart_pt hCquart_nonneg hmu)
            exact MeasureTheory.integral_mono_ae hleft_int hright_int hmono
    _ = (8 * Cquart * (t : ℝ))
          * ∫ mu in inner,
              Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
            rw [MeasureTheory.integral_const_mul]
    _ = (8 * Cquart * (t : ℝ))
          * ∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
            simp [inner]

private lemma fixed_n_quartic_to_cubic_raw_gaussianF
    (n t : ℕ) (ht1 : 1 ≤ t) {Cquart Cgauss2 : ℝ}
    (hquart_small_t : 4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) ≤ 1)
    (hquart_pt : ∀ n : ℕ, ∀ lam : Fin n → Fin n → ℝ,
      |quarticCorr n lam| ≤ Cquart * sNorm n lam ^ (2 : Nat))
    (hCquart_nonneg : 0 ≤ Cquart)
    (hgauss2 : ∀ t : ℝ, 1 ≤ t →
      ∫ mu : Cn3Torus.Edge n → ℝ,
        Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
          * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
          ≤ (Cgauss2 / t ^ (2 : Nat)) * gaussianF (dim n) t) :
    |((∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (quarticCoreIntegrand n t mu))
        - (∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (cubicCoreIntegrand n t mu)))|
      ≤ (8 * Cquart * Cgauss2 * (t : ℝ) ^ (-(1 : ℝ)))
          * gaussianF (dim n) (t : ℝ) := by
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  have hmoment2_int :
      MeasureTheory.Integrable
        (fun mu : Cn3Torus.Edge n → ℝ =>
          Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
    simpa using sqNorm_moment_gaussian_integrable_edge n 2 (by norm_num) (t : ℝ) ht_pos
  have hmoment2_inner_le :
      ∫ mu in inner,
          Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
        ≤ (Cgauss2 / (t : ℝ) ^ (2 : Nat)) * gaussianF (dim n) (t : ℝ) := by
    have hpoint_nonneg :
        ∀ mu : Cn3Torus.Edge n → ℝ,
          0 ≤ Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
      intro mu
      positivity
    calc
      ∫ mu in inner,
          Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
          ≤ ∫ mu : Cn3Torus.Edge n → ℝ,
              Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
                simpa [inner] using
                  (integralOn_mono_of_nonneg (by intro _ _; simp)
                    (measurableSet_edgeEuclidBall n (fixedCountDelta t))
                    MeasurableSet.univ hmoment2_int.integrableOn
                    (Filter.Eventually.of_forall hpoint_nonneg))
      _ ≤ (Cgauss2 / (t : ℝ) ^ (2 : Nat)) * gaussianF (dim n) (t : ℝ) := by
            simpa using hgauss2 (t : ℝ) (by exact_mod_cast ht1)
  calc
    |((∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (quarticCoreIntegrand n t mu))
        - (∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (cubicCoreIntegrand n t mu)))|
        ≤ (8 * Cquart * (t : ℝ))
            * ∫ mu in edgeEuclidBall n (fixedCountDelta t),
                Cn3Torus.sqNormEdge n mu ^ (2 : Nat)
                  * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
            exact fixed_n_quartic_to_cubic_integral_raw (n := n) (t := t) ht1
              (Cquart := Cquart) hquart_small_t hquart_pt hCquart_nonneg
    _ ≤ (8 * Cquart * (t : ℝ))
          * ((Cgauss2 / (t : ℝ) ^ (2 : Nat)) * gaussianF (dim n) (t : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hmoment2_inner_le (by positivity)
    _ = (8 * Cquart * Cgauss2 * (t : ℝ) ^ (-(1 : ℝ)))
          * gaussianF (dim n) (t : ℝ) := by
          have hpow : 1 / (t : ℝ) = (t : ℝ) ^ (-(1 : ℝ)) := by
            symm
            simpa using (rpow_neg_nat_eq_inv_pow ht_pos 1)
          rw [← hpow]
          field_simp [ht_pos.ne']

set_option maxHeartbeats 4000000 in
private lemma fixed_n_quartic_to_cubic_scaled
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℕ in Filter.atTop,
        |Cn3Torus.texPrefactor n
            * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
                Complex.re (quarticCoreIntegrand n t mu))
          - Cn3Torus.texPrefactor n
            * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
                Complex.re (cubicCoreIntegrand n t mu))|
          ≤ ε * gaussianScale n (t : ℝ) := by
  intro ε hε
  obtain ⟨Cquart, hCquart_pos, hquart_pt⟩ := quarticCorr_pointwise_bound_uniform
  obtain ⟨Cgauss2, hCgauss2_pos, hgauss2⟩ := gaussian_radial_moments_edge n 2
  let K₃ : ℝ := 8 * Cquart * Cgauss2
  have hK₃_nonneg : 0 ≤ K₃ := by
    unfold K₃
    positivity
  have hquart_small :
      ∀ᶠ t : ℕ in Filter.atTop,
        4 * Cquart * ((t : ℝ) * fixedCountDelta t ^ (4 : Nat)) ≤ 1 := by
    simpa using
      const_mul_t_mul_fixedCountDelta_pow_eventually_le (4 * Cquart) 1 4 (by norm_num)
        (by positivity) (by norm_num)
  have hstep3_small_coeff :=
    const_mul_nat_rpow_neg_eventually_le K₃ 1 ε
      hK₃_nonneg (by positivity) hε
  filter_upwards [Filter.eventually_ge_atTop 1, hquart_small, hstep3_small_coeff]
    with t ht1 hquart_small_t hstep3_small_coeff_t
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  let T : ℝ := Cn3Torus.texPrefactor n
  let Jquart : ℝ := ∫ mu in inner, Complex.re (quarticCoreIntegrand n t mu)
  let Jcubic : ℝ := ∫ mu in inner, Complex.re (cubicCoreIntegrand n t mu)
  have hscale_pos : 0 < gaussianScale n (t : ℝ) := gaussianScale_pos n ht_pos
  have hscale_eq :
      T * gaussianF (dim n) (t : ℝ) = gaussianScale n (t : ℝ) := by
    simpa [T] using gaussianScale_eq_texPrefactor_mul_gaussianF n hn (t : ℝ) ht_pos
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact texPrefactor_nonneg n
  have hbound :
      |Jquart - Jcubic| ≤ (K₃ * (t : ℝ) ^ (-(1 : ℝ))) * gaussianF (dim n) (t : ℝ) := by
    simpa [K₃] using
      fixed_n_quartic_to_cubic_raw_gaussianF (n := n) (t := t) ht1
        (Cquart := Cquart) (Cgauss2 := Cgauss2)
        hquart_small_t hquart_pt hCquart_pos.le hgauss2
  have hstep3_scaled :
      |T * Jquart - T * Jcubic| ≤ ε * gaussianScale n (t : ℝ) := by
    exact scaled_gap_le_of_gap_le_gaussianF_and_coeff hT_nonneg (le_of_lt hscale_pos)
      hscale_eq hbound hstep3_small_coeff_t
  calc
    |Cn3Torus.texPrefactor n
          * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Complex.re (quarticCoreIntegrand n t mu))
        - Cn3Torus.texPrefactor n
          * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Complex.re (cubicCoreIntegrand n t mu))|
      = |T * Jquart - T * Jcubic| := by
          simp [T, Jquart, Jcubic, inner]
    _ ≤ ε * gaussianScale n (t : ℝ) := hstep3_scaled

private lemma fixed_n_cubic_to_gaussian_pointwise
    (n t : ℕ) {CT : ℝ}
    (ht1 : 1 ≤ t)
    (hcubic_small_t : 4 * CT * ((t : ℝ) * fixedCountDelta t ^ (3 : Nat)) ≤ 1)
    (hcubic_pt : ∀ n : ℕ, ∀ lam : Fin n → Fin n → ℝ,
      |cubicT n lam| ≤ CT * sNorm n lam ^ (3 / 2 : ℝ))
    (hCT_nonneg : 0 ≤ CT)
    {mu : Cn3Torus.Edge n → ℝ}
    (hmu : mu ∈ edgeEuclidBall n (fixedCountDelta t)) :
    |Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
      * Real.cos (4 * (t : ℝ) * cubicT n (matrixOfEdge n mu))
      - Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)|
      ≤ ((16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat))
            * (Cn3Torus.sqNormEdge n mu ^ (3 : Nat))
          + (256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat)
              * (Cn3Torus.sqNormEdge n mu ^ (6 : Nat)))
          * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  set s : ℝ := Cn3Torus.sqNormEdge n mu
  set u : ℝ := 4 * (t : ℝ) * cubicT n (matrixOfEdge n mu)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Cn3Torus.sqNormEdge_nonneg n mu
  have hs_inner : s ≤ fixedCountDelta t ^ (2 : Nat) := by
    simpa [s] using (mem_edgeEuclidBall_iff n (fixedCountDelta t) mu).1 hmu
  have hs32_le :
      s ^ (3 / 2 : ℝ) ≤ fixedCountDelta t ^ (3 : Nat) := by
    have hdelta_nonneg : 0 ≤ fixedCountDelta t := (fixedCountDelta_pos t).le
    have htmp :
        s ^ (3 / 2 : ℝ)
          ≤ (fixedCountDelta t ^ (2 : Nat) : ℝ) ^ (3 / 2 : ℝ) := by
      exact Real.rpow_le_rpow hs_nonneg hs_inner (by positivity)
    have hpow :
        (fixedCountDelta t ^ (2 : Nat) : ℝ) ^ (3 / 2 : ℝ) = fixedCountDelta t ^ (3 : Nat) := by
      rw [show (fixedCountDelta t ^ (2 : Nat) : ℝ) = fixedCountDelta t ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul hdelta_nonneg]
      norm_num
    exact htmp.trans_eq hpow
  have hcubic_abs :
      |cubicT n (matrixOfEdge n mu)| ≤ CT * s ^ (3 / 2 : ℝ) := by
    simpa [s, sNorm_matrixOfEdge_eq] using hcubic_pt n (matrixOfEdge n mu)
  have hu_abs : |u| ≤ 1 := by
    calc
          |u| = 4 * (t : ℝ) * |cubicT n (matrixOfEdge n mu)| := by
                dsimp [u]
                rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg ht_pos.le]
      _ ≤ 4 * (t : ℝ) * (CT * s ^ (3 / 2 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hcubic_abs (by positivity)
      _ ≤ 4 * (t : ℝ) * (CT * fixedCountDelta t ^ (3 : Nat)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hs32_le hCT_nonneg)
              (by positivity)
      _ = 4 * CT * ((t : ℝ) * fixedCountDelta t ^ (3 : Nat)) := by ring
      _ ≤ 1 := hcubic_small_t
  have hcos_aux := abs_cos_sub_one_add_sq_div_two_le_pow_four_div_twentyfour u
  have hcos :
      |Real.cos u - 1| ≤ u ^ (2 : Nat) + u ^ (4 : Nat) / 24 := by
    have hu2_nonneg : 0 ≤ u ^ (2 : Nat) / 2 := by positivity
    have hcos_aux0 : |Real.cos u - (1 - u ^ (2 : Nat) / 2)| ≤ u ^ (4 : Nat) / 24 := by
      have habs4 : |u| ^ (4 : Nat) = u ^ (4 : Nat) := by
        calc
          |u| ^ (4 : Nat) = (|u| ^ (2 : Nat)) ^ (2 : Nat) := by ring
          _ = (u ^ (2 : Nat)) ^ (2 : Nat) := by rw [sq_abs]
          _ = u ^ (4 : Nat) := by ring
      calc
        |Real.cos u - (1 - u ^ (2 : Nat) / 2)| ≤ |u| ^ (4 : Nat) / 24 := hcos_aux
        _ = u ^ (4 : Nat) / 24 := by rw [habs4]
    have hcos_aux' : |Real.cos u - 1 + u ^ (2 : Nat) / 2| ≤ u ^ (4 : Nat) / 24 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcos_aux0
    calc
      |Real.cos u - 1| = |(Real.cos u - 1 + u ^ (2 : Nat) / 2) - u ^ (2 : Nat) / 2| := by ring
      _ ≤ |Real.cos u - 1 + u ^ (2 : Nat) / 2| + |u ^ (2 : Nat) / 2| := by
            simpa using abs_sub (Real.cos u - 1 + u ^ (2 : Nat) / 2) (u ^ (2 : Nat) / 2)
      _ ≤ u ^ (4 : Nat) / 24 + u ^ (2 : Nat) / 2 := by
            rw [abs_of_nonneg hu2_nonneg]
            exact add_le_add hcos_aux' le_rfl
      _ ≤ u ^ (2 : Nat) + u ^ (4 : Nat) / 24 := by
            nlinarith [sq_nonneg u]
  have hu_sq :
      u ^ (2 : Nat) ≤ 16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat) * s ^ (3 : Nat) := by
    have hu_linear : |u| ≤ 4 * (t : ℝ) * (CT * s ^ (3 / 2 : ℝ)) := by
      calc
        |u| = 4 * (t : ℝ) * |cubicT n (matrixOfEdge n mu)| := by
              dsimp [u]
              rw [abs_mul, abs_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        _ ≤ 4 * (t : ℝ) * (CT * s ^ (3 / 2 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hcubic_abs (by positivity)
    have hs_rpow : (s ^ (3 / 2 : ℝ)) ^ (2 : Nat) = s ^ (3 : Nat) := by
      rw [show (s ^ (3 / 2 : ℝ)) ^ (2 : Nat) = (s ^ (3 / 2 : ℝ)) ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul hs_nonneg]
      norm_num
    calc
      u ^ (2 : Nat) = |u| ^ (2 : Nat) := by rw [sq_abs]
      _ ≤ (4 * (t : ℝ) * (CT * s ^ (3 / 2 : ℝ))) ^ (2 : Nat) := by
            exact pow_le_pow_left₀ (abs_nonneg u) hu_linear 2
      _ = 16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat) * s ^ (3 : Nat) := by
            rw [show (4 * (t : ℝ) * (CT * s ^ (3 / 2 : ℝ))) ^ (2 : Nat)
                = 16 * (t : ℝ) ^ (2 : Nat) * CT ^ (2 : Nat) * (s ^ (3 / 2 : ℝ)) ^ (2 : Nat) by
                  ring]
            rw [hs_rpow]
            ring
  have hu_four :
      u ^ (4 : Nat) ≤ 256 * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat) * s ^ (6 : Nat) := by
    have hu_sq_sq :
        (u ^ (2 : Nat)) ^ (2 : Nat)
          ≤ (16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat) * s ^ (3 : Nat)) ^ (2 : Nat) := by
      exact pow_le_pow_left₀ (by positivity : 0 ≤ u ^ (2 : Nat)) hu_sq 2
    calc
      u ^ (4 : Nat) = (u ^ (2 : Nat)) ^ (2 : Nat) := by ring
      _ ≤ (16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat) * s ^ (3 : Nat)) ^ (2 : Nat) := hu_sq_sq
      _ = 256 * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat) * s ^ (6 : Nat) := by ring
  have hmain :
      |Real.exp (-2 * (t : ℝ) * s) * Real.cos u - Real.exp (-2 * (t : ℝ) * s)|
        ≤ ((16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat)) * s ^ (3 : Nat)
              + (256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat) * s ^ (6 : Nat))
            * Real.exp (-2 * (t : ℝ) * s) := by
    have hexp_nonneg : 0 ≤ Real.exp (-2 * (t : ℝ) * s) := by positivity
    calc
      |Real.exp (-2 * (t : ℝ) * s) * Real.cos u - Real.exp (-2 * (t : ℝ) * s)|
          = Real.exp (-2 * (t : ℝ) * s) * |Real.cos u - 1| := by
              calc
                |Real.exp (-2 * (t : ℝ) * s) * Real.cos u - Real.exp (-2 * (t : ℝ) * s)|
                    = |Real.exp (-2 * (t : ℝ) * s) * (Real.cos u - 1)| := by ring_nf
                _ = |Real.exp (-2 * (t : ℝ) * s)| * |Real.cos u - 1| := by rw [abs_mul]
                _ = Real.exp (-2 * (t : ℝ) * s) * |Real.cos u - 1| := by
                      rw [abs_of_nonneg hexp_nonneg]
      _ ≤ Real.exp (-2 * (t : ℝ) * s) * (u ^ (2 : Nat) + u ^ (4 : Nat) / 24) := by
            gcongr
      _ ≤ Real.exp (-2 * (t : ℝ) * s) *
            ((16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat)) * s ^ (3 : Nat)
              + (256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat) * s ^ (6 : Nat)) := by
            have hu_four_div :
                u ^ (4 : Nat) / 24
                  ≤ (256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat) * s ^ (6 : Nat) := by
              have h24 : (0 : ℝ) < 24 := by positivity
              have htmp :
                  u ^ (4 : Nat) / 24
                    ≤ (256 * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat) * s ^ (6 : Nat)) / 24 := by
                exact div_le_div_of_nonneg_right hu_four h24.le
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
            have hsum_bound :
                u ^ (2 : Nat) + u ^ (4 : Nat) / 24
                  ≤ (16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat)) * s ^ (3 : Nat)
                      + (256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat) * s ^ (6 : Nat) := by
              exact add_le_add hu_sq hu_four_div
            exact mul_le_mul_of_nonneg_left hsum_bound hexp_nonneg
      _ = ((16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat)) * s ^ (3 : Nat)
              + (256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat) * s ^ (6 : Nat))
            * Real.exp (-2 * (t : ℝ) * s) := by
              ring
  simpa [s, u, mul_assoc, mul_left_comm, mul_comm] using hmain

private lemma fixed_n_cubic_to_gaussian_integral_raw
    (n t : ℕ) (ht1 : 1 ≤ t) {CT : ℝ}
    (hcubic_small_t : 4 * CT * ((t : ℝ) * fixedCountDelta t ^ (3 : Nat)) ≤ 1)
    (hcubic_pt : ∀ n : ℕ, ∀ lam : Fin n → Fin n → ℝ,
      |cubicT n lam| ≤ CT * sNorm n lam ^ (3 / 2 : ℝ))
    (hCT_nonneg : 0 ≤ CT) :
    |((∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (cubicCoreIntegrand n t mu))
        - (∫ mu in edgeEuclidBall n (fixedCountDelta t),
            Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)))|
      ≤ ∫ mu in edgeEuclidBall n (fixedCountDelta t),
          ((16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat))
                * (Cn3Torus.sqNormEdge n mu ^ (3 : Nat))
              + (256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat)
                  * (Cn3Torus.sqNormEdge n mu ^ (6 : Nat)))
              * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  have hinner_meas : MeasurableSet inner := measurableSet_edgeEuclidBall n (fixedCountDelta t)
  have hinner_subset_box : inner ⊆ edgeBox n (fixedCountDelta t) := by
    exact edgeEuclidBall_subset_edgeBox n (fixedCountDelta_pos t).le le_rfl
  have hmoment3_int :
      MeasureTheory.Integrable
        (fun mu : Cn3Torus.Edge n → ℝ =>
          Cn3Torus.sqNormEdge n mu ^ (3 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
    simpa using sqNorm_moment_gaussian_integrable_edge n 3 (by norm_num) (t : ℝ) ht_pos
  have hmoment6_int :
      MeasureTheory.Integrable
        (fun mu : Cn3Torus.Edge n → ℝ =>
          Cn3Torus.sqNormEdge n mu ^ (6 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
    simpa using sqNorm_moment_gaussian_integrable_edge n 6 (by norm_num) (t : ℝ) ht_pos
  have hJcubic_eq :
      (∫ mu in inner, Complex.re (cubicCoreIntegrand n t mu))
        = ∫ mu in inner,
            Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
              * Real.cos (4 * (t : ℝ) * cubicT n (matrixOfEdge n mu)) := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall (fun mu => by
      simpa using (cubicCoreIntegrand_re n t mu))
  have hcos_int :
      MeasureTheory.IntegrableOn
        (fun mu =>
          Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
            * Real.cos (4 * (t : ℝ) * cubicT n (matrixOfEdge n mu))) inner := by
    have hcont :
        Continuous
          (fun mu : Cn3Torus.Edge n → ℝ =>
            Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
              * Real.cos (4 * (t : ℝ) * cubicT n (matrixOfEdge n mu))) := by
      have hsq : Continuous (fun mu : Cn3Torus.Edge n → ℝ => Cn3Torus.sqNormEdge n mu) :=
        Cn3Torus.continuous_sqNormEdge n
      have hcub : Continuous (fun mu : Cn3Torus.Edge n → ℝ => cubicT n (matrixOfEdge n mu)) :=
        (continuous_cubicT n).comp (continuous_matrixOfEdge n)
      fun_prop
    simpa [MeasureTheory.IntegrableOn] using
      ((hcont.continuousOn.integrableOn_compact (edgeBox_isCompact n (fixedCountDelta t))).mono_set
        hinner_subset_box)
  have hgauss_int :
      MeasureTheory.IntegrableOn
        (fun mu => Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) inner := by
    simpa [MeasureTheory.IntegrableOn] using
      (((Real.continuous_exp.comp
          ((continuous_const.mul (Cn3Torus.continuous_sqNormEdge n)).neg)).continuousOn.integrableOn_compact
          (edgeBox_isCompact n (fixedCountDelta t))).mono_set hinner_subset_box)
  have hEq :
      (∫ mu in inner,
          Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
            * Real.cos (4 * (t : ℝ) * cubicT n (matrixOfEdge n mu)))
        - ∫ mu in inner,
            Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
        =
      ∫ mu in inner,
          (Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
            * Real.cos (4 * (t : ℝ) * cubicT n (matrixOfEdge n mu))
            - Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
    exact (MeasureTheory.integral_sub hcos_int hgauss_int).symm
  have hraw_cos :
      |(∫ mu in inner,
          Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
            * Real.cos (4 * (t : ℝ) * cubicT n (matrixOfEdge n mu)))
        - ∫ mu in inner,
            Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)|
        ≤ ∫ mu in inner,
            |Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
              * Real.cos (4 * (t : ℝ) * cubicT n (matrixOfEdge n mu))
              - Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)| := by
    rw [hEq]
    simpa using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume.restrict inner)
        (f := fun mu =>
          (Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
            * Real.cos (4 * (t : ℝ) * cubicT n (matrixOfEdge n mu))
            - Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))))
  have hleft_int :
      MeasureTheory.IntegrableOn
        (fun mu =>
          |Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
            * Real.cos (4 * (t : ℝ) * cubicT n (matrixOfEdge n mu))
            - Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)|) inner := by
    have hcont :
        Continuous
          (fun mu : Cn3Torus.Edge n → ℝ =>
            |Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
              * Real.cos (4 * (t : ℝ) * cubicT n (matrixOfEdge n mu))
              - Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)|) := by
      have hsq : Continuous (fun mu : Cn3Torus.Edge n → ℝ => Cn3Torus.sqNormEdge n mu) :=
        Cn3Torus.continuous_sqNormEdge n
      have hcub : Continuous (fun mu : Cn3Torus.Edge n → ℝ => cubicT n (matrixOfEdge n mu)) :=
        (continuous_cubicT n).comp (continuous_matrixOfEdge n)
      fun_prop
    simpa [MeasureTheory.IntegrableOn] using
      ((hcont.continuousOn.integrableOn_compact (edgeBox_isCompact n (fixedCountDelta t))).mono_set
        hinner_subset_box)
  have hright_int :
      MeasureTheory.IntegrableOn
        (fun mu =>
          ((16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat))
              * (Cn3Torus.sqNormEdge n mu ^ (3 : Nat))
            + (256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat)
                * (Cn3Torus.sqNormEdge n mu ^ (6 : Nat)))
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) inner := by
    simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using
      (((hmoment3_int.const_mul (16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat))).add
        (hmoment6_int.const_mul ((256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat)))).integrableOn)
  calc
    |(∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (cubicCoreIntegrand n t mu))
        - ∫ mu in edgeEuclidBall n (fixedCountDelta t),
            Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)|
        = |(∫ mu in inner, Complex.re (cubicCoreIntegrand n t mu))
            - ∫ mu in inner,
                Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)| := by
            simp [inner]
    _ = |(∫ mu in inner,
            Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
              * Real.cos (4 * (t : ℝ) * cubicT n (matrixOfEdge n mu)))
          - ∫ mu in inner,
              Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)| := by
            rw [hJcubic_eq]
    _ ≤ ∫ mu in inner,
          |Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
            * Real.cos (4 * (t : ℝ) * cubicT n (matrixOfEdge n mu))
            - Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)| := hraw_cos
    _ ≤ ∫ mu in inner,
          ((16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat))
              * (Cn3Torus.sqNormEdge n mu ^ (3 : Nat))
            + (256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat)
                * (Cn3Torus.sqNormEdge n mu ^ (6 : Nat)))
              * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
          have hmono :
              ∀ᵐ mu ∂MeasureTheory.volume.restrict inner,
                |Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
                  * Real.cos (4 * (t : ℝ) * cubicT n (matrixOfEdge n mu))
                  - Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)|
                  ≤ ((16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat))
                        * (Cn3Torus.sqNormEdge n mu ^ (3 : Nat))
                      + (256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat)
                          * (Cn3Torus.sqNormEdge n mu ^ (6 : Nat)))
                      * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
            rw [MeasureTheory.ae_restrict_iff' hinner_meas]
            exact Filter.Eventually.of_forall (fun mu hmu =>
              fixed_n_cubic_to_gaussian_pointwise (n := n) (t := t) (CT := CT)
                ht1 hcubic_small_t hcubic_pt hCT_nonneg hmu)
          exact MeasureTheory.integral_mono_ae hleft_int hright_int hmono

set_option maxHeartbeats 4000000 in
private lemma fixed_n_cubic_to_gaussian_raw_gaussianF
    (n t : ℕ) (ht1 : 1 ≤ t) {CT Cgauss3 Cgauss6 : ℝ}
    (hcubic_small_t : 4 * CT * ((t : ℝ) * fixedCountDelta t ^ (3 : Nat)) ≤ 1)
    (hcubic_pt : ∀ n : ℕ, ∀ lam : Fin n → Fin n → ℝ,
      |cubicT n lam| ≤ CT * sNorm n lam ^ (3 / 2 : ℝ))
    (hCT_nonneg : 0 ≤ CT)
    (hgauss3 : ∀ t : ℝ, 1 ≤ t →
      ∫ mu : Cn3Torus.Edge n → ℝ,
        Cn3Torus.sqNormEdge n mu ^ (3 : Nat)
          * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
          ≤ (Cgauss3 / t ^ (3 : Nat)) * gaussianF (dim n) t)
    (hgauss6 : ∀ t : ℝ, 1 ≤ t →
      ∫ mu : Cn3Torus.Edge n → ℝ,
        Cn3Torus.sqNormEdge n mu ^ (6 : Nat)
          * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
          ≤ (Cgauss6 / t ^ (6 : Nat)) * gaussianF (dim n) t) :
    |((∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (cubicCoreIntegrand n t mu))
        - (∫ mu in edgeEuclidBall n (fixedCountDelta t),
            Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)))|
      ≤ (((16 * CT ^ (2 : Nat) * Cgauss3) * (t : ℝ) ^ (-(1 : ℝ)))
            + (((256 / 24 : ℝ) * CT ^ (4 : Nat) * Cgauss6) * (t : ℝ) ^ (-(2 : ℝ))))
          * gaussianF (dim n) (t : ℝ) := by
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  have hmoment3_int :
      MeasureTheory.Integrable
        (fun mu : Cn3Torus.Edge n → ℝ =>
          Cn3Torus.sqNormEdge n mu ^ (3 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
    simpa using sqNorm_moment_gaussian_integrable_edge n 3 (by norm_num) (t : ℝ) ht_pos
  have hmoment6_int :
      MeasureTheory.Integrable
        (fun mu : Cn3Torus.Edge n → ℝ =>
          Cn3Torus.sqNormEdge n mu ^ (6 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
    simpa using sqNorm_moment_gaussian_integrable_edge n 6 (by norm_num) (t : ℝ) ht_pos
  have hmoment3_inner_le :
      ∫ mu in inner,
          Cn3Torus.sqNormEdge n mu ^ (3 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
        ≤ (Cgauss3 / (t : ℝ) ^ (3 : Nat)) * gaussianF (dim n) (t : ℝ) := by
    have hpoint_nonneg :
        ∀ mu : Cn3Torus.Edge n → ℝ,
          0 ≤ Cn3Torus.sqNormEdge n mu ^ (3 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
      intro mu
      exact mul_nonneg
        (pow_nonneg (Cn3Torus.sqNormEdge_nonneg n mu) _)
        (by positivity)
    calc
      ∫ mu in inner,
          Cn3Torus.sqNormEdge n mu ^ (3 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
        ≤ ∫ mu : Cn3Torus.Edge n → ℝ,
            Cn3Torus.sqNormEdge n mu ^ (3 : Nat)
              * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
              simpa [inner] using
                (integralOn_mono_of_nonneg (by intro _ _; simp)
                  (measurableSet_edgeEuclidBall n (fixedCountDelta t))
                  MeasurableSet.univ hmoment3_int.integrableOn
                  (Filter.Eventually.of_forall hpoint_nonneg))
      _ ≤ (Cgauss3 / (t : ℝ) ^ (3 : Nat)) * gaussianF (dim n) (t : ℝ) := by
            simpa using hgauss3 (t : ℝ) (by exact_mod_cast ht1)
  have hmoment6_inner_le :
      ∫ mu in inner,
          Cn3Torus.sqNormEdge n mu ^ (6 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
        ≤ (Cgauss6 / (t : ℝ) ^ (6 : Nat)) * gaussianF (dim n) (t : ℝ) := by
    have hpoint_nonneg :
        ∀ mu : Cn3Torus.Edge n → ℝ,
          0 ≤ Cn3Torus.sqNormEdge n mu ^ (6 : Nat)
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
      intro mu
      positivity
    calc
      ∫ mu in inner,
          Cn3Torus.sqNormEdge n mu ^ (6 : Nat)
            * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
        ≤ ∫ mu : Cn3Torus.Edge n → ℝ,
            Cn3Torus.sqNormEdge n mu ^ (6 : Nat)
              * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
              simpa [inner] using
                (integralOn_mono_of_nonneg (by intro _ _; simp)
                  (measurableSet_edgeEuclidBall n (fixedCountDelta t))
                  MeasurableSet.univ hmoment6_int.integrableOn
                  (Filter.Eventually.of_forall hpoint_nonneg))
      _ ≤ (Cgauss6 / (t : ℝ) ^ (6 : Nat)) * gaussianF (dim n) (t : ℝ) := by
            simpa using hgauss6 (t : ℝ) (by exact_mod_cast ht1)
  calc
    |(∫ mu in edgeEuclidBall n (fixedCountDelta t), Complex.re (cubicCoreIntegrand n t mu))
        - ∫ mu in edgeEuclidBall n (fixedCountDelta t),
            Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)|
        ≤ ∫ mu in inner,
            ((16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat))
                  * (Cn3Torus.sqNormEdge n mu ^ (3 : Nat))
                + (256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat)
                    * (Cn3Torus.sqNormEdge n mu ^ (6 : Nat)))
                * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
            simpa [inner] using
              fixed_n_cubic_to_gaussian_integral_raw (n := n) (t := t) ht1
                (CT := CT) hcubic_small_t hcubic_pt hCT_nonneg
    _ = ((16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat))
            * ∫ mu in inner,
                Cn3Torus.sqNormEdge n mu ^ (3 : Nat)
                  * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))
          + (((256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat))
              * ∫ mu in inner,
                  Cn3Torus.sqNormEdge n mu ^ (6 : Nat)
                    * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)) := by
          have hEqInt :
              (fun mu : Cn3Torus.Edge n → ℝ =>
                ((16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat))
                    * (Cn3Torus.sqNormEdge n mu ^ (3 : Nat))
                  + (256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat)
                      * (Cn3Torus.sqNormEdge n mu ^ (6 : Nat)))
                  * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))
                =
              (fun mu : Cn3Torus.Edge n → ℝ =>
                (16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat))
                  * (Cn3Torus.sqNormEdge n mu ^ (3 : Nat)
                      * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))
                + ((256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat))
                    * (Cn3Torus.sqNormEdge n mu ^ (6 : Nat)
                        * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))) := by
            funext mu
            ring
          have hEqInt' :
              (∫ mu in inner,
                  ((16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat))
                      * (Cn3Torus.sqNormEdge n mu ^ (3 : Nat))
                    + (256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat)
                        * (Cn3Torus.sqNormEdge n mu ^ (6 : Nat)))
                    * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))
                =
              ∫ mu in inner,
                ((16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat))
                  * (Cn3Torus.sqNormEdge n mu ^ (3 : Nat)
                      * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))
                + ((256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat))
                    * (Cn3Torus.sqNormEdge n mu ^ (6 : Nat)
                        * Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))) := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun mu => by
              simpa using congrFun hEqInt mu)
          rw [hEqInt']
          rw [MeasureTheory.integral_add]
          · simp_rw [MeasureTheory.integral_const_mul]
          · exact ((hmoment3_int.const_mul _).integrableOn)
          · exact ((hmoment6_int.const_mul _).integrableOn)
    _ ≤ ((16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat))
            * ((Cgauss3 / (t : ℝ) ^ (3 : Nat)) * gaussianF (dim n) (t : ℝ)))
          + (((256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat))
              * ((Cgauss6 / (t : ℝ) ^ (6 : Nat)) * gaussianF (dim n) (t : ℝ))) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left hmoment3_inner_le
              (by positivity : 0 ≤ 16 * CT ^ (2 : Nat) * (t : ℝ) ^ (2 : Nat))
          · exact mul_le_mul_of_nonneg_left hmoment6_inner_le
              (by positivity : 0 ≤ (256 / 24 : ℝ) * CT ^ (4 : Nat) * (t : ℝ) ^ (4 : Nat))
    _ = (((16 * CT ^ (2 : Nat) * Cgauss3) * (t : ℝ) ^ (-(1 : ℝ)))
            + (((256 / 24 : ℝ) * CT ^ (4 : Nat) * Cgauss6) * (t : ℝ) ^ (-(2 : ℝ))))
          * gaussianF (dim n) (t : ℝ) := by
          have hpow1 : (t : ℝ) ^ (-(1 : ℝ)) = 1 / (t : ℝ) := by
            simpa using (rpow_neg_nat_eq_inv_pow ht_pos 1)
          have hpow2 : (t : ℝ) ^ (-(2 : ℝ)) = 1 / (t : ℝ) ^ (2 : Nat) := by
            simpa using (rpow_neg_nat_eq_inv_pow ht_pos 2)
          rw [hpow1, hpow2]
          field_simp [ht_pos.ne']

private lemma fixed_n_cubic_to_gaussian_scaled
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℕ in Filter.atTop,
        |Cn3Torus.texPrefactor n
            * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
                Complex.re (cubicCoreIntegrand n t mu))
          - Cn3Torus.texPrefactor n
            * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
                Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))|
          ≤ ε * gaussianScale n (t : ℝ) := by
  intro ε hε
  let ε₀ : ℝ := ε / 2
  have hε₀ : 0 < ε₀ := by
    unfold ε₀
    positivity
  obtain ⟨CT, hCT_pos, hcubic_pt⟩ := cubicT_pointwise_bound_uniform
  obtain ⟨Cgauss3, hCgauss3_pos, hgauss3⟩ := gaussian_radial_moments_edge n 3
  obtain ⟨Cgauss6, hCgauss6_pos, hgauss6⟩ := gaussian_radial_moments_edge n 6
  let K₄ : ℝ := 16 * CT ^ (2 : Nat) * Cgauss3
  let K₄' : ℝ := (256 / 24 : ℝ) * CT ^ (4 : Nat) * Cgauss6
  have hK₄_nonneg : 0 ≤ K₄ := by
    unfold K₄
    positivity
  have hK₄'_nonneg : 0 ≤ K₄' := by
    unfold K₄'
    positivity
  have hcubic_small :
      ∀ᶠ t : ℕ in Filter.atTop,
        4 * CT * ((t : ℝ) * fixedCountDelta t ^ (3 : Nat)) ≤ 1 := by
    simpa using
      const_mul_t_mul_fixedCountDelta_pow_eventually_le (4 * CT) 1 3 (by norm_num)
        (by positivity) (by norm_num)
  have hstep4_small_coeff :=
    const_mul_nat_rpow_neg_eventually_le K₄ 1 ε₀
      hK₄_nonneg (by positivity) hε₀
  have hstep4_quartic_small :=
    const_mul_nat_rpow_neg_eventually_le K₄' 2 ε₀
      hK₄'_nonneg (by positivity) hε₀
  filter_upwards
    [Filter.eventually_ge_atTop 1, hcubic_small, hstep4_small_coeff, hstep4_quartic_small]
    with t ht1 hcubic_small_t hstep4_small_coeff_t hstep4_quartic_small_t
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  let T : ℝ := Cn3Torus.texPrefactor n
  let Jcubic : ℝ := ∫ mu in inner, Complex.re (cubicCoreIntegrand n t mu)
  let Jgauss : ℝ := ∫ mu in inner, Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
  have hscale_pos : 0 < gaussianScale n (t : ℝ) := gaussianScale_pos n ht_pos
  have hscale_eq :
      T * gaussianF (dim n) (t : ℝ) = gaussianScale n (t : ℝ) := by
    simpa [T] using gaussianScale_eq_texPrefactor_mul_gaussianF n hn (t : ℝ) ht_pos
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact texPrefactor_nonneg n
  have hbound :
      |Jcubic - Jgauss|
        ≤ ((K₄ * (t : ℝ) ^ (-(1 : ℝ))) + (K₄' * (t : ℝ) ^ (-(2 : ℝ))))
            * gaussianF (dim n) (t : ℝ) := by
    simpa [inner, Jcubic, Jgauss, K₄, K₄'] using
      fixed_n_cubic_to_gaussian_raw_gaussianF (n := n) (t := t) ht1
        (CT := CT) (Cgauss3 := Cgauss3) (Cgauss6 := Cgauss6)
        hcubic_small_t hcubic_pt hCT_pos.le hgauss3 hgauss6
  have hcoeff :
      (K₄ * (t : ℝ) ^ (-(1 : ℝ))) + (K₄' * (t : ℝ) ^ (-(2 : ℝ))) ≤ ε₀ + ε₀ := by
    exact add_le_add hstep4_small_coeff_t hstep4_quartic_small_t
  have hstep4_raw :
      |T * Jcubic - T * Jgauss| ≤ (ε₀ + ε₀) * gaussianScale n (t : ℝ) := by
    exact scaled_gap_le_of_gap_le_gaussianF_and_coeff hT_nonneg (le_of_lt hscale_pos)
      hscale_eq hbound hcoeff
  calc
    |Cn3Torus.texPrefactor n
          * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Complex.re (cubicCoreIntegrand n t mu))
        - Cn3Torus.texPrefactor n
          * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))|
      = |T * Jcubic - T * Jgauss| := by
          simp [T, Jcubic, Jgauss, inner]
    _ ≤ (ε₀ + ε₀) * gaussianScale n (t : ℝ) := hstep4_raw
    _ = ε * gaussianScale n (t : ℝ) := by
          unfold ε₀
          ring

private lemma fixed_n_gaussian_tail_scaled
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℕ in Filter.atTop,
        |Cn3Torus.texPrefactor n
            * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
                Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))
          - gaussianScale n (t : ℝ)|
          ≤ ε * gaussianScale n (t : ℝ) := by
  intro ε hε
  obtain ⟨Ctail, hCtail_pos, htail⟩ := fixedCount_gaussian_tail_bound n hn
  have htail_small :=
    const_mul_nat_rpow_neg_eventually_le Ctail (1 / 5 : ℝ) ε
      (by positivity) (by positivity) hε
  filter_upwards [Filter.eventually_ge_atTop 2, htail_small] with t ht2 htail_small_t
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos_nat
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  let T : ℝ := Cn3Torus.texPrefactor n
  let Jgauss : ℝ := ∫ mu in inner, Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
  have hscale_pos : 0 < gaussianScale n (t : ℝ) := gaussianScale_pos n ht_pos
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    exact texPrefactor_nonneg n
  have hscale_eq :
      T * gaussianF (dim n) (t : ℝ) = gaussianScale n (t : ℝ) := by
    simpa [T] using gaussianScale_eq_texPrefactor_mul_gaussianF n hn (t : ℝ) ht_pos
  calc
    |Cn3Torus.texPrefactor n
          * (∫ mu in edgeEuclidBall n (fixedCountDelta t),
              Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu))
        - gaussianScale n (t : ℝ)|
      = |T * Jgauss - gaussianScale n (t : ℝ)| := by
          simp [T, Jgauss, inner]
    _ = T * |Jgauss - gaussianF (dim n) (t : ℝ)| := by
          rw [← hscale_eq]
          rw [show T * Jgauss - T * gaussianF (dim n) (t : ℝ)
                = T * (Jgauss - gaussianF (dim n) (t : ℝ)) by ring]
          rw [abs_mul, abs_of_nonneg hT_nonneg]
    _ ≤ (Ctail * (t : ℝ) ^ (-(1 / 5 : ℝ))) * gaussianScale n (t : ℝ) := by
          simpa [inner, Jgauss, T] using htail t ht2
    _ ≤ ε * gaussianScale n (t : ℝ) := by
          exact mul_le_mul_of_nonneg_right htail_small_t (le_of_lt hscale_pos)

set_option maxHeartbeats 4000000 in
/-- For fixed `n ≥ 2`, the shrinking primary box contribution converges to the Gaussian
main term when the box radius is `fixedCountDelta t = t^{-2/5}`. -/
private lemma fixed_n_primaryBox_gap_negligible
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ t : ℕ in Filter.atTop,
        |Cn3Torus.texPrefactor n
            * (∫ mu in edgeBox n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
            - gaussianScale n (t : ℝ)|
          ≤ ε * gaussianScale n (t : ℝ) := by
  intro ε hε
  let ε₁ : ℝ := ε / 6
  have hε₁ : 0 < ε₁ := by
    unfold ε₁
    positivity
  have hbox_event := fixed_n_box_shell_scaled n hn ε₁ hε₁
  have hstep1_event := fixed_n_exact_to_corrected_scaled n hn ε₁ hε₁
  have hstep2_event := fixed_n_corrected_to_quartic_scaled n hn ε₁ hε₁
  have hstep3_event := fixed_n_quartic_to_cubic_scaled n hn ε₁ hε₁
  have hstep4_event := fixed_n_cubic_to_gaussian_scaled n hn ε₁ hε₁
  have htail_event := fixed_n_gaussian_tail_scaled n hn ε₁ hε₁
  filter_upwards
    [hbox_event, hstep1_event, hstep2_event, hstep3_event, hstep4_event, htail_event]
    with t hbox_t hstep1_t hstep2_t hstep3_t hstep4_t htail_t
  let inner : Set (Cn3Torus.Edge n → ℝ) := edgeEuclidBall n (fixedCountDelta t)
  let box : Set (Cn3Torus.Edge n → ℝ) := edgeBox n (fixedCountDelta t)
  let T : ℝ := Cn3Torus.texPrefactor n
  let Jbox : ℝ := ∫ mu in box, Complex.re (Cn3Torus.psi n mu ^ (4 * t))
  let Jψ : ℝ := ∫ mu in inner, Complex.re (Cn3Torus.psi n mu ^ (4 * t))
  let Jcorr : ℝ := ∫ mu in inner, Complex.re (correctedCoreIntegrand n t mu)
  let Jquart : ℝ := ∫ mu in inner, Complex.re (quarticCoreIntegrand n t mu)
  let Jcubic : ℝ := ∫ mu in inner, Complex.re (cubicCoreIntegrand n t mu)
  let Jgauss : ℝ := ∫ mu in inner, Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
  have hbox_scaled :
      |T * Jbox - T * Jψ| ≤ ε₁ * gaussianScale n (t : ℝ) := by
    simpa [T, Jbox, Jψ, box, inner] using hbox_t
  have hstep1_scaled :
      |T * Jψ - T * Jcorr| ≤ ε₁ * gaussianScale n (t : ℝ) := by
    simpa [T, Jψ, Jcorr, inner] using hstep1_t
  have hstep2_scaled :
      |T * Jcorr - T * Jquart| ≤ ε₁ * gaussianScale n (t : ℝ) := by
    simpa [T, Jcorr, Jquart, inner] using hstep2_t
  have hstep3_scaled :
      |T * Jquart - T * Jcubic| ≤ ε₁ * gaussianScale n (t : ℝ) := by
    simpa [T, Jquart, Jcubic, inner] using hstep3_t
  have hstep4_scaled :
      |T * Jcubic - T * Jgauss| ≤ ε₁ * gaussianScale n (t : ℝ) := by
    simpa [T, Jcubic, Jgauss, inner] using hstep4_t
  have htail_scaled :
      |T * Jgauss - gaussianScale n (t : ℝ)| ≤ ε₁ * gaussianScale n (t : ℝ) := by
    simpa [T, Jgauss, inner] using htail_t
  have hgap :
      |T * Jbox - gaussianScale n (t : ℝ)|
        ≤ (6 * ε₁) * gaussianScale n (t : ℝ) := by
    calc
      |T * Jbox - gaussianScale n (t : ℝ)|
        ≤ |T * Jbox - T * Jψ|
            + |T * Jψ - T * Jcorr|
            + |T * Jcorr - T * Jquart|
            + |T * Jquart - T * Jcubic|
            + |T * Jcubic - T * Jgauss|
            + |T * Jgauss - gaussianScale n (t : ℝ)| := by
              have htele := abs_sub_le_sum_abs_sub_six
                (T * Jbox) (T * Jψ) (T * Jcorr) (T * Jquart)
                (T * Jcubic) (T * Jgauss) (gaussianScale n (t : ℝ))
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htele
      _ ≤ (ε₁ + ε₁ + ε₁ + ε₁ + ε₁ + ε₁) * gaussianScale n (t : ℝ) := by
              have hsum1 :
                  |T * Jbox - T * Jψ| + |T * Jψ - T * Jcorr|
                    ≤ ε₁ * gaussianScale n (t : ℝ) + ε₁ * gaussianScale n (t : ℝ) := by
                exact add_le_add hbox_scaled hstep1_scaled
              have hsum2 :
                  |T * Jcorr - T * Jquart| + |T * Jquart - T * Jcubic|
                    ≤ ε₁ * gaussianScale n (t : ℝ) + ε₁ * gaussianScale n (t : ℝ) := by
                exact add_le_add hstep2_scaled hstep3_scaled
              have hsum3 :
                  |T * Jcubic - T * Jgauss| + |T * Jgauss - gaussianScale n (t : ℝ)|
                    ≤ ε₁ * gaussianScale n (t : ℝ) + ε₁ * gaussianScale n (t : ℝ) := by
                exact add_le_add hstep4_scaled htail_scaled
              calc
                |T * Jbox - T * Jψ|
                    + |T * Jψ - T * Jcorr|
                    + |T * Jcorr - T * Jquart|
                    + |T * Jquart - T * Jcubic|
                    + |T * Jcubic - T * Jgauss|
                    + |T * Jgauss - gaussianScale n (t : ℝ)|
                    =
                  (|T * Jbox - T * Jψ| + |T * Jψ - T * Jcorr|)
                    + (|T * Jcorr - T * Jquart| + |T * Jquart - T * Jcubic|)
                    + (|T * Jcubic - T * Jgauss| + |T * Jgauss - gaussianScale n (t : ℝ)|) := by ring
                _ ≤ (ε₁ * gaussianScale n (t : ℝ) + ε₁ * gaussianScale n (t : ℝ))
                      + (ε₁ * gaussianScale n (t : ℝ) + ε₁ * gaussianScale n (t : ℝ))
                      + (ε₁ * gaussianScale n (t : ℝ) + ε₁ * gaussianScale n (t : ℝ)) := by
                      gcongr
                _ = (ε₁ + ε₁ + ε₁ + ε₁ + ε₁ + ε₁) * gaussianScale n (t : ℝ) := by ring
      _ = (6 * ε₁) * gaussianScale n (t : ℝ) := by ring
  have hε₁_eq : (6 : ℝ) * ε₁ = ε := by
    unfold ε₁
    ring
  calc
    |Cn3Torus.texPrefactor n
          * (∫ mu in edgeBox n (fixedCountDelta t),
              Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
        - gaussianScale n (t : ℝ)|
        = |T * Jbox - gaussianScale n (t : ℝ)| := by
            simp [T, Jbox, box]
    _ ≤ (6 * ε₁) * gaussianScale n (t : ℝ) := hgap
    _ = ε * gaussianScale n (t : ℝ) := by rw [hε₁_eq]
/-- The fixed-`n` primary box, normalized by the Gaussian scale, converges to `1`. -/
private theorem fixed_n_primary_ratio_tendsto_one (n : ℕ) (hn : 2 ≤ n) :
    Tendsto
      (fun t : ℕ =>
        (Cn3Torus.texPrefactor n
          * ∫ mu in edgeBox n (fixedCountDelta t),
              Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
          / gaussianScale n (t : ℝ))
      Filter.atTop (𝓝 1) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let ε' : ℝ := ε / 2
  have hε' : 0 < ε' := by
    unfold ε'
    positivity
  have hε'_lt : ε' < ε := by
    unfold ε'
    linarith
  have hgap_event := fixed_n_primaryBox_gap_negligible n hn ε' hε'
  rw [Filter.eventually_atTop] at hgap_event
  rcases hgap_event with ⟨T, hT⟩
  refine ⟨max 1 T, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have hT_le : T ≤ t := le_trans (le_max_right _ _) ht
  have hgap := hT t hT_le
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : 0 < (t : ℝ) := by exact_mod_cast ht_pos_nat
  have hscale_pos : 0 < gaussianScale n (t : ℝ) := gaussianScale_pos n ht_pos
  have hratio :
      |(Cn3Torus.texPrefactor n
            * ∫ mu in edgeBox n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
          / gaussianScale n (t : ℝ)
          - 1|
        =
      |Cn3Torus.texPrefactor n
            * (∫ mu in edgeBox n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
          - gaussianScale n (t : ℝ)|
        / gaussianScale n (t : ℝ) := by
    rw [show (Cn3Torus.texPrefactor n
          * ∫ mu in edgeBox n (fixedCountDelta t),
              Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
        / gaussianScale n (t : ℝ) - 1
        =
      (Cn3Torus.texPrefactor n
          * (∫ mu in edgeBox n (fixedCountDelta t),
              Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
        - gaussianScale n (t : ℝ))
        / gaussianScale n (t : ℝ) by
          field_simp [hscale_pos.ne']]
    rw [abs_div, abs_of_pos hscale_pos]
  calc
    dist
        ((Cn3Torus.texPrefactor n
            * ∫ mu in edgeBox n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
          / gaussianScale n (t : ℝ))
        1
      = |(Cn3Torus.texPrefactor n
            * ∫ mu in edgeBox n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
          / gaussianScale n (t : ℝ)
          - 1| := by
            rw [Real.dist_eq]
    _ =
        |Cn3Torus.texPrefactor n
            * (∫ mu in edgeBox n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
          - gaussianScale n (t : ℝ)|
          / gaussianScale n (t : ℝ) := hratio
    _ ≤ ε' := by
          exact (div_le_iff₀ hscale_pos).2 hgap
    _ < ε := hε'_lt

/-- The fixed-`n` residual contribution, normalized by the Gaussian scale, converges
to `0`. -/
private theorem fixed_n_residual_ratio_tendsto_zero (n : ℕ) (hn : 2 ≤ n) :
    Tendsto
      (fun t : ℕ =>
        ((1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
          * ∫ lam in Cn3Torus.edgeResidualTorusRegion n (fixedCountDelta t),
              Complex.re (Cn3Torus.psi n lam ^ (4 * t)))
          / gaussianScale n (t : ℝ))
      Filter.atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let ε' : ℝ := ε / 2
  have hε' : 0 < ε' := by
    unfold ε'
    positivity
  have hε'_lt : ε' < ε := by
    unfold ε'
    linarith
  have hres_event := fixedCount_residualContribution_bound n hn ε' hε'
  rw [Filter.eventually_atTop] at hres_event
  rcases hres_event with ⟨T, hT⟩
  refine ⟨max 1 T, ?_⟩
  intro t ht
  have hT_le : T ≤ t := le_trans (le_max_right _ _) ht
  have hres := hT t hT_le
  have ht_pos_nat : 0 < t := by
    have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
    omega
  have ht_pos : 0 < (t : ℝ) := by exact_mod_cast ht_pos_nat
  have hscale_pos : 0 < gaussianScale n (t : ℝ) := gaussianScale_pos n ht_pos
  have hratio :
      |(((1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
            * ∫ lam in Cn3Torus.edgeResidualTorusRegion n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n lam ^ (4 * t)))
          / gaussianScale n (t : ℝ))
          - 0|
        =
      |(1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
            * ∫ lam in Cn3Torus.edgeResidualTorusRegion n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n lam ^ (4 * t))|
        / gaussianScale n (t : ℝ) := by
    rw [sub_zero, abs_div, abs_of_pos hscale_pos]
  calc
    dist
        (((1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
            * ∫ lam in Cn3Torus.edgeResidualTorusRegion n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n lam ^ (4 * t)))
          / gaussianScale n (t : ℝ))
        0
      =
        |(((1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
            * ∫ lam in Cn3Torus.edgeResidualTorusRegion n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n lam ^ (4 * t)))
          / gaussianScale n (t : ℝ))
          - 0| := by
            rw [Real.dist_eq]
    _ =
        |(1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
            * ∫ lam in Cn3Torus.edgeResidualTorusRegion n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n lam ^ (4 * t))|
        / gaussianScale n (t : ℝ) := hratio
    _ ≤ ε' := by
          exact (div_le_iff₀ hscale_pos).2 hres
    _ < ε := hε'_lt

/-- Fixed-`n` normalized-count asymptotic, replacing the external DL10 patch on
the normalized-count side. -/
theorem fixed_n_normalizedCount_asymptotic (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun t : ℕ => normalizedCount n (4 * t) / gaussianScale n (t : ℝ))
      Filter.atTop (𝓝 1) := by
  let P : ℕ → ℝ := fun t =>
    (Cn3Torus.texPrefactor n
      * ∫ mu in edgeBox n (fixedCountDelta t), Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
      / gaussianScale n (t : ℝ)
  let R : ℕ → ℝ := fun t =>
    ((1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
      * ∫ lam in Cn3Torus.edgeResidualTorusRegion n (fixedCountDelta t),
          Complex.re (Cn3Torus.psi n lam ^ (4 * t)))
      / gaussianScale n (t : ℝ)
  have hP : Tendsto P Filter.atTop (𝓝 1) := fixed_n_primary_ratio_tendsto_one n hn
  have hR : Tendsto R Filter.atTop (𝓝 0) := fixed_n_residual_ratio_tendsto_zero n hn
  have hsum : Tendsto (fun t : ℕ => P t + R t) Filter.atTop (𝓝 1) := by
    simpa using hP.add hR
  refine hsum.congr' ?_
  have hdelta_event := fixedCountDelta_eventually_le (3 / 4 : ℝ) (by positivity)
  filter_upwards [Filter.eventually_ge_atTop 1, hdelta_event] with t ht1 hdelta_t
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : 0 < (t : ℝ) := by exact_mod_cast ht_pos_nat
  have hscale_pos : 0 < gaussianScale n (t : ℝ) := gaussianScale_pos n ht_pos
  have hdelta_lt : fixedCountDelta t < Real.pi / 4 := by
    linarith [hdelta_t, Real.pi_gt_three]
  have hdecomp :=
    normalizedCount_primary_secondary_decomposition n t (delta := fixedCountDelta t) hdelta_lt
  have hcoeff :
      (((Cn3Torus.lambdaShifts n).card : ℝ) / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
        = Cn3Torus.texPrefactor n := by
      rw [Cn3Torus.texPrefactor, Cn3Torus.card_lambdaShifts_eq_pow_of_two_le n hn, Nat.cast_pow]
      norm_num
  have hret :
      normalizedCount n (4 * t)
        = Cn3Torus.texPrefactor n
            * (∫ mu in edgeBox n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
          + (1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
              * (∫ lam in Cn3Torus.edgeResidualTorusRegion n (fixedCountDelta t),
                  Complex.re (Cn3Torus.psi n lam ^ (4 * t))) := by
    simpa [hcoeff] using hdecomp
  dsimp [P, R]
  have hcombine :
      (Cn3Torus.texPrefactor n
            * ∫ mu in edgeBox n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
          / gaussianScale n (t : ℝ)
        + ((1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
            * ∫ lam in Cn3Torus.edgeResidualTorusRegion n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n lam ^ (4 * t)))
            / gaussianScale n (t : ℝ)
        =
      ((Cn3Torus.texPrefactor n
            * ∫ mu in edgeBox n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
          + (1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
              * ∫ lam in Cn3Torus.edgeResidualTorusRegion n (fixedCountDelta t),
                  Complex.re (Cn3Torus.psi n lam ^ (4 * t)))
        / gaussianScale n (t : ℝ) := by
    field_simp [hscale_pos.ne']
  calc
    (Cn3Torus.texPrefactor n
          * ∫ mu in edgeBox n (fixedCountDelta t),
              Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
        / gaussianScale n (t : ℝ)
      + ((1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
          * ∫ lam in Cn3Torus.edgeResidualTorusRegion n (fixedCountDelta t),
              Complex.re (Cn3Torus.psi n lam ^ (4 * t)))
          / gaussianScale n (t : ℝ)
        =
      ((Cn3Torus.texPrefactor n
            * ∫ mu in edgeBox n (fixedCountDelta t),
                Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
          + (1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
              * ∫ lam in Cn3Torus.edgeResidualTorusRegion n (fixedCountDelta t),
                  Complex.re (Cn3Torus.psi n lam ^ (4 * t)))
        / gaussianScale n (t : ℝ) := hcombine
    _ = normalizedCount n (4 * t) / gaussianScale n (t : ℝ) := by
          rw [hret]

/-- Fixed-`n` count asymptotic for the small-dimension branch of `cor_uniform`. -/
theorem fixed_n_count_asymptotic (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun t : ℕ => (hadamardCount n (4 * t) : ℝ) / countScale n t)
      Filter.atTop (𝓝 1) := by
  have hret := fixed_n_normalizedCount_asymptotic n hn
  refine hret.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with t ht
  have ht_pos_nat : 0 < t := by omega
  have ht_pos : 0 < (t : ℝ) := by exact_mod_cast ht_pos_nat
  have hscale_pos : 0 < gaussianScale n ↑t := gaussianScale_pos n ht_pos
  have hpow_ne : (2 : ℝ) ^ (4 * n * t) ≠ 0 := by positivity
  have hgauss_ne : gaussianScale n ↑t ≠ 0 := hscale_pos.ne'
  have hratio :
      (hadamardCount n (4 * t) : ℝ) / countScale n t =
        normalizedCount n (4 * t) / gaussianScale n ↑t := by
    have hmul : n * (4 * t) = 4 * n * t := by ac_rfl
    rw [countScale, normalizedCount, hmul]
    field_simp [hpow_ne, hgauss_ne]
  simpa [hratio]

end
