import RequestProject.HadamardCn3ShortMain
import RequestProject.HadamardCn3WeakInvariance

noncomputable section

open Real MeasureTheory Filter Finset Topology
open scoped Pointwise

/-!
# Paper Specification Layer

This file keeps only the genuinely useful paper-notation bridge facts that are
not already transparent from the main theorem file.

For the literal paper quantities

- `paperCount n s = N_{n,s}`,

start in `RequestProject.HadamardCn3ShortMain`.

For the weak comparison surface, inspect

- `quadraticForm_lindeberg_comparison_C3`
- `psi_sub_gaussianPsi_le_threeHalfInfluenceSum`

in `RequestProject.HadamardCn3WeakInvariance`.

This file retains only the nontrivial normalization lemma comparing the project
statistic `threeHalfInfluenceSum` with the paper's kernel-influence notation.
-/

/-- The project statistic `threeHalfInfluenceSum` is exactly eight times the paper
kernel-influence sum `\sum_k \operatorname{Inf}_k(f)^{3/2}` for `f = mooKernel`. -/
theorem paper_threeHalfInfluenceSum_eq_eight_kernelInfluence_sum
    (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    threeHalfInfluenceSum n lam
      = 8 * ∑ k : Fin n,
          kernelInfluence n (mooKernel n lam) k
            * Real.sqrt (kernelInfluence n (mooKernel n lam) k) := by
  unfold threeHalfInfluenceSum
  calc
    ∑ k : Fin n, rowInfluence n lam k * Real.sqrt (rowInfluence n lam k)
      = ∑ k : Fin n,
          8 * (kernelInfluence n (mooKernel n lam) k
            * Real.sqrt (kernelInfluence n (mooKernel n lam) k)) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [kernelInfluence_mooKernel]
          have hsqrt :
              Real.sqrt
                  ((1 / 4 : ℝ) *
                    ∑ i : Fin n, if i ≠ k then lam (min i k) (max i k) ^ (2 : Nat) else 0)
                =
                  (1 / 2 : ℝ) * Real.sqrt
                    (∑ i : Fin n, if i ≠ k then lam (min i k) (max i k) ^ (2 : Nat) else 0) := by
            rw [Real.sqrt_mul (show 0 ≤ (1 / 4 : ℝ) by positivity),
              show Real.sqrt (1 / 4 : ℝ) = (1 / 2 : ℝ) by norm_num]
          rw [rowInfluence, hsqrt]
          ring
    _ = 8 * ∑ k : Fin n,
          kernelInfluence n (mooKernel n lam) k
            * Real.sqrt (kernelInfluence n (mooKernel n lam) k) := by
          rw [Finset.mul_sum]
