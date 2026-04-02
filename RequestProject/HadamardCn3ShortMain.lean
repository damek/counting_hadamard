import RequestProject.HadamardCn3Asymptotics

noncomputable section

open Real MeasureTheory Filter Finset Topology
open scoped Pointwise

/-!
# Paper-Facing Count Theorems

This file contains only the final count-facing statements from the arXiv paper
`https://arxiv.org/pdf/2603.30013`.

The reader-facing quantities are:

- `paperCount n s = N_{n,s}`, the number of `n × s` partial Hadamard matrices
- `paperAsymptoticCount n t = A_{n,4t}`, the asymptotic scale from the paper

The endpoint theorems are:

- `thm_main_intro`, the formal analogue of Theorem `\ref{thm:main-intro}`
- `cor_uniform`, the formal analogue of Corollary `\ref{cor:uniform}`

The intermediate normalized-count and integral statements live in
`RequestProject.HadamardCn3Asymptotics`.
-/

/-- Paper notation `N_{n,s}`: the number of `n × s` partial Hadamard matrices. -/
def paperCount (n s : ℕ) : ℕ :=
  (Finset.univ.filter (fun M : Fin n → Fin s → Fin 2 =>
    ∀ i j : Fin n, i ≠ j →
      (∑ k : Fin s, (signOf (M i k) : ℝ) * (signOf (M j k) : ℝ)) = 0)).card

/-- Paper notation `A_{n,4t}` for the asymptotic count scale. -/
def paperAsymptoticCount (n t : ℕ) : ℝ :=
  (2 : ℝ) ^ (4 * n * t) *
    (2 ^ (2 * Nat.choose n 2 - n + 1 : ℤ) * (8 * π * (t : ℝ)) ^ (-(Nat.choose n 2 : ℝ) / 2))

private def paperCenterTerm (n t : ℕ) : ℝ :=
  (1 : ℝ) - ((Nat.choose n 3 : ℝ) / (8 * (t : ℝ)))

private def paperCountRatioTerm (n t : ℕ) : ℝ :=
  (paperCount n (4 * t) : ℝ) / paperAsymptoticCount n t

@[simp] private theorem paperCount_eq_hadamardCount (n s : ℕ) :
    paperCount n s = hadamardCount n s := by
  rfl

private theorem paperAsymptoticCount_eq_pow_mul_mainScale (n t : ℕ) :
    paperAsymptoticCount n t = (2 : ℝ) ^ (4 * n * t) * paperMainScale n t := by
  simp [paperAsymptoticCount, paperMainScale]

private theorem paperAsymptoticCount_eq_countScale (n t : ℕ) :
    paperAsymptoticCount n t = countScale n t := by
  simp [paperAsymptoticCount, countScale, gaussianScale, dim]

private theorem paperCountRatioTerm_eq_countScale_ratio (n t : ℕ) :
    paperCountRatioTerm n t = ((paperCount n (4 * t) : ℝ) / countScale n t) := by
  rw [paperCountRatioTerm, paperAsymptoticCount_eq_countScale]

/-- Count theorem matching the main asymptotic theorem in the arXiv paper.

This is the main paper asymptotic for the number `N_{n,4t}` of `n × 4t`
partial Hadamard matrices. -/
theorem thm_main_intro :
    ∃ c K C : ℝ, 0 < c ∧ 0 < K ∧ 0 < C ∧
      ∀ n : ℕ, 3 ≤ n →
      ∀ t : ℕ, (t : ℝ) ≥ C * ↑n ^ (3 : Nat) →
        |((paperCount n (4 * t) : ℝ) / paperAsymptoticCount n t)
            - ((1 : ℝ) - ((Nat.choose n 3 : ℝ) / (8 * (t : ℝ))))|
          ≤ K * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
              + K * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
              + K * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
              + K * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) := by
  obtain ⟨c, K, C, hc_pos, hK_pos, hC_pos, hret⟩ := normalizedCount_asymptotic
  refine ⟨c, K, C, hc_pos, hK_pos, hC_pos, ?_⟩
  intro n hn3 t ht
  have ht_pos : (0 : ℝ) < (t : ℝ) := by
    have : 0 < C * (n : ℝ) ^ (3 : Nat) := by positivity [hC_pos]
    linarith
  have hmain_scale_eq : paperMainScale n t = gaussianScale n ↑t := by
    simp [paperMainScale, gaussianScale, dim]
  have hmain_scale_pos : 0 < paperMainScale n t := by
    simpa [hmain_scale_eq] using gaussianScale_pos n ht_pos
  have hpaper_norm_eq :
      paperNormalizedCount n t = (paperCount n (4 * t) : ℝ) / (2 : ℝ) ^ (4 * n * t) := by
    simp [paperNormalizedCount, paperCount_eq_hadamardCount]
  have hratio :
      paperCountRatioTerm n t = paperNormalizedCount n t / paperMainScale n t := by
    have hpow_ne : (2 : ℝ) ^ (4 * n * t) ≠ 0 := by positivity
    rw [paperCountRatioTerm, paperAsymptoticCount_eq_pow_mul_mainScale, hpaper_norm_eq]
    field_simp [hpow_ne, hmain_scale_pos.ne']
  have hret0 := hret n hn3 t ht
  have hdiv :
      |paperNormalizedCount n t / paperMainScale n t - paperCenterTerm n t|
        ≤ K * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
            + K * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
            + K * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
            + K * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) := by
    have hrew :
        paperNormalizedCount n t / paperMainScale n t - paperCenterTerm n t
          = (paperNormalizedCount n t - paperMainScale n t * paperCenterTerm n t) / paperMainScale n t := by
      field_simp [hmain_scale_pos.ne']
    rw [hrew, abs_div, abs_of_pos hmain_scale_pos]
    exact (div_le_iff₀ hmain_scale_pos).2 (by
      simpa [paperCenterTerm, paperMainTerm, mul_comm] using hret0)
  have hratio_explicit :
      ((paperCount n (4 * t) : ℝ) / paperAsymptoticCount n t)
        = paperNormalizedCount n t / paperMainScale n t := by
    simpa [paperCountRatioTerm] using hratio
  rw [hratio_explicit]
  simpa [paperCenterTerm] using hdiv

set_option maxHeartbeats 20000000 in
/-- Lean wrapper for the uniform corollary in the arXiv paper.

For sufficiently large `t ≥ K n^3`, the normalized paper count ratio
`N_{n,4t} / A_{n,4t}` is uniformly close to `1`. -/
theorem cor_uniform :
    ∀ ε : ℝ, 0 < ε →
      ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n →
        ∀ t : ℕ, (t : ℝ) ≥ K * ↑n ^ 3 →
          |((paperCount n (4 * t) : ℝ) / paperAsymptoticCount n t) - 1| < ε := by
  intro ε hε
  obtain ⟨c, K0, C0, hc_pos, hK0_pos, hC0_pos, hmain⟩ := thm_main_intro
  have hK0_nonneg : 0 ≤ K0 := hK0_pos.le
  have hε_six : 0 < ε / 6 := by positivity
  have hexp_event :
      ∀ᶠ n : ℕ in Filter.atTop,
        K0 * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) ≤ ε / 6 := by
    simpa using
      (const_mul_nat_rpow_mul_exp_neg_mul_nat_rpow_eventually_le
        K0 0 c 2 (ε / 6) hK0_nonneg hc_pos (by norm_num) hε_six)
  rw [Filter.eventually_atTop] at hexp_event
  rcases hexp_event with ⟨Nexp, hNexp⟩
  let N : ℕ := max 3 Nexp
  have hfix_threshold :
      ∀ n : ℕ, 2 ≤ n →
        ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
          |paperCountRatioTerm n t - 1| < ε := by
    intro n hn2
    have hlim := fixed_n_count_asymptotic n hn2
    have hnear : ∀ᶠ t : ℕ in Filter.atTop,
        |paperCountRatioTerm n t - 1| < ε := by
      have hnhds : {x : ℝ | |x - 1| < ε} ∈ nhds (1 : ℝ) := by
        simpa [Metric.ball, Real.dist_eq, abs_sub_comm] using
          (Metric.ball_mem_nhds (1 : ℝ) hε)
      simpa [paperCountRatioTerm_eq_countScale_ratio, paperCount_eq_hadamardCount] using
        (tendsto_def.1 hlim) _ hnhds
    rw [Filter.eventually_atTop] at hnear
    exact hnear
  let Kfix : ℕ → ℕ := fun n =>
    if hn2 : 2 ≤ n then Nat.succ (Classical.choose (hfix_threshold n hn2)) else 1
  have hKfix :
      ∀ n : ℕ, 2 ≤ n → ∀ t : ℕ, Kfix n ≤ t →
        |paperCountRatioTerm n t - 1| < ε := by
    intro n hn2 t ht
    have hKfix_eq :
        Kfix n = Nat.succ (Classical.choose (hfix_threshold n hn2)) := by
      simp [Kfix, hn2]
    have hbase :
        Classical.choose (hfix_threshold n hn2) ≤ t := by
      rw [hKfix_eq] at ht
      omega
    exact (Classical.choose_spec (hfix_threshold n hn2)) t hbase
  let Kmain : ℝ := max C0 (max 1 (6 * (K0 + 1) / ε))
  let Ksmall : ℝ := (Finset.Icc 2 (N - 1)).sum (fun m => ((Kfix m : ℝ) + 1))
  let K : ℝ := max Kmain Ksmall
  have hKmain_le_K : Kmain ≤ K := by
    unfold K
    exact le_max_left _ _
  have hKsmall_le_K : Ksmall ≤ K := by
    unfold K
    exact le_max_right _ _
  have hC0_le_K : C0 ≤ K := by
    have hC0_le_Kmain : C0 ≤ Kmain := by
      unfold Kmain
      exact le_max_left _ _
    exact le_trans hC0_le_Kmain hKmain_le_K
  have hone_le_Kmain : (1 : ℝ) ≤ Kmain := by
    unfold Kmain
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hone_le_K : (1 : ℝ) ≤ K := le_trans hone_le_Kmain hKmain_le_K
  have hscaled : 6 * (K0 + 1) / ε ≤ K := by
    have hscaled_main : 6 * (K0 + 1) / ε ≤ Kmain := by
      unfold Kmain
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact le_trans hscaled_main hKmain_le_K
  have hK_pos : 0 < K := by
    have hC0_le : C0 ≤ K := hC0_le_K
    exact lt_of_lt_of_le hC0_pos hC0_le
  have hKsum_div : (K0 + 1) / K ≤ ε / 6 :=
    div_le_eps_six_of_scaled_bound hK_pos hε hscaled
  have hK0_div : K0 / K ≤ ε / 6 := by
    have hle : K0 ≤ K0 + 1 := by linarith
    exact le_trans (div_le_div_of_nonneg_right hle hK_pos.le) hKsum_div
  have hone_div : (1 : ℝ) / K ≤ ε / 6 := by
    have hle : (1 : ℝ) ≤ K0 + 1 := by linarith
    exact le_trans (div_le_div_of_nonneg_right hle hK_pos.le) hKsum_div
  refine ⟨K, hK_pos, ?_⟩
  intro n hn2 t ht
  by_cases hlarge : N ≤ n
  · have hn3 : 3 ≤ n := by
      exact le_trans (by unfold N; exact le_max_left _ _) hlarge
    have hNexp_le : Nexp ≤ n := by
      exact le_trans (by unfold N; exact le_max_right _ _) hlarge
    have ht_main : (t : ℝ) ≥ C0 * ↑n ^ (3 : Nat) := by
      nlinarith [ht, hC0_le_K]
    have hmain0 := hmain n hn3 t ht_main
    have hn_one_nat : 1 ≤ n := by omega
    have hn_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_one_nat
    have hn_pos : (0 : ℝ) < (n : ℝ) := by positivity
    have ht_pos : (0 : ℝ) < (t : ℝ) := by
      have hKn_pos : 0 < K * (n : ℝ) ^ (3 : Nat) := by positivity
      linarith
    have hcube_div :
        (n : ℝ) ^ (3 : Nat) / (t : ℝ) ≤ (1 : ℝ) / K := by
      calc
        (n : ℝ) ^ (3 : Nat) / (t : ℝ) ≤ (n : ℝ) ^ (3 : Nat) / (K * (n : ℝ) ^ (3 : Nat)) := by
          exact div_le_div_of_nonneg_left (by positivity) (by positivity [hK_pos, hn_pos]) ht
        _ = (1 : ℝ) / K := by field_simp [hK_pos.ne', hn_pos.ne']
    have hKinv_le_one : (1 : ℝ) / K ≤ 1 := by
      have htmp : (1 : ℝ) / K ≤ (1 : ℝ) / 1 := by
        exact one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hone_le_K
      simpa using htmp
    have hcube_div_le_one :
        (n : ℝ) ^ (3 : Nat) / (t : ℝ) ≤ 1 := le_trans hcube_div hKinv_le_one
    have hpoly2_small :
        K0 * (n : ℝ) ^ (2 : Nat) / (t : ℝ) ≤ ε / 6 := by
      have hn_sq_le_cube : (n : ℝ) ^ (2 : Nat) ≤ (n : ℝ) ^ (3 : Nat) := by
        nlinarith [hn_one]
      calc
        K0 * (n : ℝ) ^ (2 : Nat) / (t : ℝ) = K0 * (((n : ℝ) ^ (2 : Nat)) / (t : ℝ)) := by ring
        _ ≤ K0 * (((n : ℝ) ^ (3 : Nat)) / (t : ℝ)) := by gcongr
        _ ≤ K0 * ((1 : ℝ) / K) := by exact mul_le_mul_of_nonneg_left hcube_div hK0_nonneg
        _ = K0 / K := by ring
        _ ≤ ε / 6 := hK0_div
    have ht_one : (1 : ℝ) ≤ (t : ℝ) := by
      have hKn_one : (1 : ℝ) ≤ K * (n : ℝ) ^ (3 : Nat) := by
        have hn_cube_ge_one : (1 : ℝ) ≤ (n : ℝ) ^ (3 : Nat) := by
          calc
            (1 : ℝ) = 1 * 1 := by ring
            _ ≤ (n : ℝ) * (n : ℝ) ^ (2 : Nat) := by
                  have hsquare_ge_one : (1 : ℝ) ≤ (n : ℝ) ^ (2 : Nat) := by nlinarith [hn_one]
                  have hmul := mul_le_mul hn_one hsquare_ge_one (by positivity) (by positivity)
                  simpa using hmul
            _ = (n : ℝ) ^ (3 : Nat) := by ring
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ K * (n : ℝ) ^ (3 : Nat) := by
                have hmul := mul_le_mul hone_le_K hn_cube_ge_one (by positivity) (by positivity)
                simpa using hmul
      linarith
    have htpow_ge : (t : ℝ) ≤ (t : ℝ) ^ (3 / 2 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_le ht_one (by norm_num : (1 : ℝ) ≤ 3 / 2)
      simpa [Real.rpow_natCast] using this
    have hinv_tpow : (1 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ) ≤ (1 : ℝ) / (t : ℝ) := by
      exact one_div_le_one_div_of_le ht_pos htpow_ge
    have hnpow_le :
        (n : ℝ) ^ (5 / 2 : ℝ) ≤ (n : ℝ) ^ (3 : Nat) := by
      simpa [Real.rpow_natCast] using
        (Real.rpow_le_rpow_of_exponent_le hn_one (by norm_num : (5 / 2 : ℝ) ≤ 3))
    have hpoly32_le :
        (n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ) ≤ (n : ℝ) ^ (3 : Nat) / (t : ℝ) := by
      calc
        (n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ)
          = (n : ℝ) ^ (5 / 2 : ℝ) * ((1 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ)) := by ring
        _ ≤ (n : ℝ) ^ (3 : Nat) * ((1 : ℝ) / (t : ℝ)) := by gcongr
        _ = (n : ℝ) ^ (3 : Nat) / (t : ℝ) := by ring
    have hpoly32_small :
        K0 * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ)) ≤ ε / 6 := by
      calc
        K0 * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
          ≤ K0 * ((n : ℝ) ^ (3 : Nat) / (t : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hpoly32_le hK0_nonneg
        _ ≤ K0 * ((1 : ℝ) / K) := by
              exact mul_le_mul_of_nonneg_left hcube_div hK0_nonneg
        _ = K0 / K := by ring
        _ ≤ ε / 6 := hK0_div
    have hpoly6_le :
        (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat) ≤ (n : ℝ) ^ (3 : Nat) / (t : ℝ) := by
      have hcube_div_nonneg : 0 ≤ (n : ℝ) ^ (3 : Nat) / (t : ℝ) := by positivity
      calc
        (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
          = (((n : ℝ) ^ (3 : Nat)) / (t : ℝ)) ^ (2 : Nat) := by
              field_simp [ht_pos.ne']
        _ ≤ (((n : ℝ) ^ (3 : Nat)) / (t : ℝ)) * 1 := by
              have hmul := mul_le_mul_of_nonneg_left hcube_div_le_one hcube_div_nonneg
              simpa [sq] using hmul
        _ = (n : ℝ) ^ (3 : Nat) / (t : ℝ) := by ring
    have hpoly6_small :
        K0 * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat) ≤ ε / 6 := by
      calc
        K0 * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
          = K0 * (((n : ℝ) ^ (6 : Nat)) / (t : ℝ) ^ (2 : Nat)) := by ring
        _ ≤ K0 * (((n : ℝ) ^ (3 : Nat)) / (t : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hpoly6_le hK0_nonneg
        _ ≤ K0 * ((1 : ℝ) / K) := by
              exact mul_le_mul_of_nonneg_left hcube_div hK0_nonneg
        _ = K0 / K := by ring
        _ ≤ ε / 6 := hK0_div
    have hexp_small :
        K0 * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) ≤ ε / 6 := by
      simpa using hNexp n hNexp_le
    have hchoose_nonneg :
        0 ≤ (Nat.choose n 3 : ℝ) / (8 * (t : ℝ)) := by positivity
    have hchoose_le_cube :
        (Nat.choose n 3 : ℝ) ≤ (n : ℝ) ^ (3 : Nat) := by
      exact_mod_cast Nat.choose_le_pow n 3
    have hcorr_small :
        (Nat.choose n 3 : ℝ) / (8 * (t : ℝ)) ≤ ε / 6 := by
      calc
        (Nat.choose n 3 : ℝ) / (8 * (t : ℝ))
          ≤ (Nat.choose n 3 : ℝ) / (t : ℝ) := by
              exact div_le_div_of_nonneg_left (by positivity) ht_pos (by nlinarith)
        _ ≤ (n : ℝ) ^ (3 : Nat) / (t : ℝ) := by
              exact div_le_div_of_nonneg_right hchoose_le_cube ht_pos.le
        _ ≤ (1 : ℝ) / K := hcube_div
        _ ≤ ε / 6 := hone_div
    have htri :
        |paperCountRatioTerm n t - 1|
          ≤ |paperCountRatioTerm n t - paperCenterTerm n t| + |paperCenterTerm n t - 1| := by
      have hrew :
          paperCountRatioTerm n t - 1
            = (paperCountRatioTerm n t - paperCenterTerm n t) + (paperCenterTerm n t - 1) := by
        ring
      calc
        |paperCountRatioTerm n t - 1| = ‖paperCountRatioTerm n t - 1‖ := by rw [Real.norm_eq_abs]
        _ = ‖(paperCountRatioTerm n t - paperCenterTerm n t) + (paperCenterTerm n t - 1)‖ := by rw [hrew]
        _ ≤ ‖paperCountRatioTerm n t - paperCenterTerm n t‖ + ‖paperCenterTerm n t - 1‖ := norm_add_le _ _
        _ = |paperCountRatioTerm n t - paperCenterTerm n t| + |paperCenterTerm n t - 1| := by
              rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hcenter_abs :
        |paperCenterTerm n t - 1| = (Nat.choose n 3 : ℝ) / (8 * (t : ℝ)) := by
      dsimp [paperCenterTerm]
      have hrew :
          ((1 : ℝ) - (Nat.choose n 3 : ℝ) / (8 * (t : ℝ))) - 1
            = -((Nat.choose n 3 : ℝ) / (8 * (t : ℝ))) := by ring
      rw [hrew, abs_neg, abs_of_nonneg hchoose_nonneg]
    have hmain_gap :
        |paperCountRatioTerm n t - paperCenterTerm n t|
          ≤ K0 * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
              + K0 * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
              + K0 * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
              + K0 * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) := by
      simpa [paperCountRatioTerm, paperAsymptoticCount, paperCenterTerm] using hmain0
    have hsum_small :
        K0 * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
            + K0 * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
            + K0 * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
            + K0 * Real.exp (-(c * (n : ℝ) ^ (2 : Nat)))
            + (Nat.choose n 3 : ℝ) / (8 * (t : ℝ))
          ≤ 5 * (ε / 6) := by
      nlinarith [hpoly2_small, hpoly32_small, hpoly6_small, hexp_small, hcorr_small]
    have hfive_small : 5 * (ε / 6) < ε := by
      nlinarith
    have hbound :
        |paperCountRatioTerm n t - 1|
          ≤ K0 * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
              + K0 * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
              + K0 * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
              + K0 * Real.exp (-(c * (n : ℝ) ^ (2 : Nat)))
              + (Nat.choose n 3 : ℝ) / (8 * (t : ℝ)) := by
      rw [hcenter_abs] at htri
      nlinarith [htri, hmain_gap]
    simpa [paperCountRatioTerm, paperAsymptoticCount] using
      (lt_of_le_of_lt (le_trans hbound hsum_small) hfive_small)
  · have hsmall : n < N := lt_of_not_ge hlarge
    have hmem : n ∈ Finset.Icc 2 (N - 1) := by
      simp [hn2]
      omega
    have hKfix_le_small : (Kfix n : ℝ) ≤ Ksmall := by
      have hterm : (Kfix n : ℝ) + 1 ≤ Ksmall := by
        have hrest_nonneg :
            0 ≤ ((Finset.Icc 2 (N - 1)).erase n).sum (fun m => ((Kfix m : ℝ) + 1)) := by
          refine Finset.sum_nonneg ?_
          intro m hm
          positivity
        have hsum_eq :
            ((Finset.Icc 2 (N - 1)).erase n).sum (fun m => ((Kfix m : ℝ) + 1)) + ((Kfix n : ℝ) + 1) = Ksmall := by
          unfold Ksmall
          simpa [add_comm, add_left_comm, add_assoc] using
            (Finset.sum_erase_add (s := Finset.Icc 2 (N - 1)) (a := n)
              (f := fun m => ((Kfix m : ℝ) + 1)) hmem)
        have hle :
            (Kfix n : ℝ) + 1 ≤
              ((Finset.Icc 2 (N - 1)).erase n).sum (fun m => ((Kfix m : ℝ) + 1)) + ((Kfix n : ℝ) + 1) := by
          linarith
        rw [hsum_eq] at hle
        exact hle
      have hstep : (Kfix n : ℝ) ≤ (Kfix n : ℝ) + 1 := by linarith
      exact le_trans hstep hterm
    have hKfix_le_K : (Kfix n : ℝ) ≤ K := by
      exact le_trans hKfix_le_small hKsmall_le_K
    have hn_one_nat : 1 ≤ n := by omega
    have hn_cube_ge_one : (1 : ℝ) ≤ (↑n : ℝ) ^ 3 := by
      have hn_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_one_nat
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (↑n : ℝ) * (↑n : ℝ) ^ 2 := by
              have hsquare_ge_one : (1 : ℝ) ≤ (↑n : ℝ) ^ 2 := by
                nlinarith [hn_one]
              have hmul := mul_le_mul hn_one hsquare_ge_one (by positivity) (by positivity)
              simpa using hmul
        _ = (↑n : ℝ) ^ 3 := by ring
    have hthreshold : (Kfix n : ℝ) ≤ K * ↑n ^ 3 := by
      have hstep : (Kfix n : ℝ) * 1 ≤ K * ↑n ^ 3 := by
        have h1 : (Kfix n : ℝ) * 1 ≤ (Kfix n : ℝ) * ↑n ^ 3 := by
          exact mul_le_mul_of_nonneg_left hn_cube_ge_one (by positivity)
        have h2 : (Kfix n : ℝ) * ↑n ^ 3 ≤ K * ↑n ^ 3 := by
          exact mul_le_mul_of_nonneg_right hKfix_le_K (by positivity)
        exact le_trans h1 h2
      simpa using hstep
    have hKfix_le_t_real : (Kfix n : ℝ) ≤ t := by
      exact le_trans hthreshold ht
    have hKfix_le_t : Kfix n ≤ t := by
      exact_mod_cast hKfix_le_t_real
    simpa [paperCountRatioTerm, paperAsymptoticCount] using hKfix n hn2 t hKfix_le_t

end
