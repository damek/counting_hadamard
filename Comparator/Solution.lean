import RequestProject.HadamardCn3ShortMain

noncomputable section

theorem main_intro :
    ∃ c K C : ℝ, 0 < c ∧ 0 < K ∧ 0 < C ∧
      ∀ n : ℕ, 3 ≤ n →
      ∀ t : ℕ, (t : ℝ) ≥ C * ↑n ^ (3 : Nat) →
        |((paperCount n (4 * t) : ℝ) / paperAsymptoticCount n t)
            - ((1 : ℝ) - ((Nat.choose n 3 : ℝ) / (8 * (t : ℝ))))|
          ≤ K * (n : ℝ) ^ (2 : Nat) / (t : ℝ)
              + K * ((n : ℝ) ^ (5 / 2 : ℝ) / (t : ℝ) ^ (3 / 2 : ℝ))
              + K * (n : ℝ) ^ (6 : Nat) / (t : ℝ) ^ (2 : Nat)
              + K * Real.exp (-(c * (n : ℝ) ^ (2 : Nat))) := by
  simpa using thm_main_intro

theorem uniform_cor :
    ∀ ε : ℝ, 0 < ε →
      ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 2 ≤ n →
        ∀ t : ℕ, (t : ℝ) ≥ K * ↑n ^ 3 →
          |((paperCount n (4 * t) : ℝ) / paperAsymptoticCount n t) - 1| < ε := by
  simpa using cor_uniform
