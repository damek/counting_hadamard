import RequestProject.HadamardCn3Defs
import RequestProject.HadamardCn3TorusCount
import RequestProject.HadamardCn3Moments
import RequestProject.HadamardCn3MOO
import RequestProject.HadamardCn3ResidualBase

/-!
# Quartic Fiber Reduction

This file isolates the quartic peeling argument used in the local-gap bridge.

The public theorems a reader should inspect are:

- `gaussian_integral_with_perturbation_bound`
- `quarticCoreTrunc_bound`
- `quartic_exponential_core_bound`

Most of the intermediate linear-algebra, matrix-factorization, and fiber
transport lemmas are internal implementation detail and are kept private.
-/

open MeasureTheory
open Classical

/-- Diagonal Gaussian integral on `Fin d → ℝ`. -/
private theorem gaussian_integral_diagonal_formula :
    ∀ (d : ℕ) (a : Fin d → ℝ), (∀ i, 0 < a i) →
      ∫ x : Fin d → ℝ, Real.exp (-∑ i : Fin d, a i * x i ^ (2 : Nat))
        = ∏ i : Fin d, Real.sqrt (Real.pi / a i)
  | 0, a, ha => by
      rw [MeasureTheory.integral_unique]
      have hvol : (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) Set.univ = 1 := by
        rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
        simp
      rw [MeasureTheory.Measure.real_def, hvol]
      simp
  | n + 1, a, ha => by
      let e : Fin (n + 1) ≃ Unit ⊕ Fin n := {
        toFun := fun i => by
          by_cases hi : i = Fin.last n
          · exact Sum.inl ()
          · exact Sum.inr (i.castLT (by
              have hi_le_n : (i : ℕ) ≤ n := Nat.le_of_lt_succ i.is_lt
              have hi_ne_n : (i : ℕ) ≠ n := by
                intro h
                apply hi
                exact Fin.ext h
              exact lt_of_le_of_ne hi_le_n hi_ne_n))
        invFun := fun s => by
          rcases s with _ | i
          · exact Fin.last n
          · exact i.castSucc
        left_inv := by
          intro i
          dsimp
          by_cases hi : i = Fin.last n
          · simp [hi]
          · simp [hi]
        right_inv := by
          intro s
          rcases s with _ | i
          · simp
          · simp }
      let reindex1 : (Fin (n + 1) → ℝ) ≃ᵐ ((s : Unit ⊕ Fin n) → ℝ) :=
        MeasurableEquiv.piCongrLeft (fun _ : Unit ⊕ Fin n => ℝ) e
      let reindex2 : ((s : Unit ⊕ Fin n) → ℝ) ≃ᵐ (Unit → ℝ) × (Fin n → ℝ) :=
        MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ Fin n => ℝ)
      let reindex3 : (Unit → ℝ) × (Fin n → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
        MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique Unit ℝ)
          (MeasurableEquiv.refl (Fin n → ℝ))
      let split : (Fin (n + 1) → ℝ) → ℝ × (Fin n → ℝ) :=
        fun x => reindex3 (reindex2 (reindex1 x))
      have hpres1 :
          MeasureTheory.MeasurePreserving reindex1 MeasureTheory.volume MeasureTheory.volume := by
        simpa [reindex1] using
          (MeasureTheory.volume_measurePreserving_piCongrLeft
            (fun _ : Unit ⊕ Fin n => ℝ) e)
      have hpres2 :
          MeasureTheory.MeasurePreserving reindex2 MeasureTheory.volume MeasureTheory.volume := by
        simpa [reindex2] using
          (MeasureTheory.volume_measurePreserving_sumPiEquivProdPi
            (fun _ : Unit ⊕ Fin n => ℝ))
      have hpres3 :
          MeasureTheory.MeasurePreserving reindex3 MeasureTheory.volume MeasureTheory.volume := by
        simpa [reindex3, MeasurableEquiv.prodCongr] using
          (volume_measurePreserving_funUnique_real.prod
            (MeasureTheory.MeasurePreserving.id
              (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℝ))))
      have hpres :
          MeasureTheory.MeasurePreserving split MeasureTheory.volume MeasureTheory.volume := by
        exact hpres3.comp (hpres2.comp hpres1)
      have hsplit_meas : MeasurableEmbedding split := by
        exact reindex3.measurableEmbedding.comp
          (reindex2.measurableEmbedding.comp reindex1.measurableEmbedding)
      have elast :
          e (Fin.last n) = Sum.inl () := by
        simp [e]
      have ecast :
          ∀ i : Fin n, e i.castSucc = Sum.inr i := by
        intro i
        simp [e]
      have esymm_left : e.symm (Sum.inl ()) = Fin.last n := by
        simp [e]
      have esymm_right :
          ∀ i : Fin n, e.symm (Sum.inr i) = i.castSucc := by
        intro i
        simp [e]
      have hreindex1_apply :
          ∀ (x : Fin (n + 1) → ℝ) (s : Unit ⊕ Fin n), reindex1 x s = x (e.symm s) := by
        intro x s
        simpa using
          (Equiv.piCongrLeft_apply (P := fun _ : Unit ⊕ Fin n => ℝ) e x s)
      have hsum :
          ∀ x : Fin (n + 1) → ℝ,
            (∑ i : Fin (n + 1), a i * x i ^ (2 : Nat))
              = a (Fin.last n) * (split x).1 ^ (2 : Nat)
                  + ∑ i : Fin n, a i.castSucc * (split x).2 i ^ (2 : Nat) := by
        intro x
        have hsum1 :
            ∑ i : Fin (n + 1), a i * x i ^ (2 : Nat)
              = ∑ s : Unit ⊕ Fin n, a (e.symm s) * (x (e.symm s)) ^ (2 : Nat) := by
          exact Fintype.sum_equiv e
            (fun i : Fin (n + 1) => a i * x i ^ (2 : Nat))
            (fun s : Unit ⊕ Fin n => a (e.symm s) * (x (e.symm s)) ^ (2 : Nat))
            (by
              intro i
              simp)
        calc
          ∑ i : Fin (n + 1), a i * x i ^ (2 : Nat)
              = ∑ s : Unit ⊕ Fin n, a (e.symm s) * (x (e.symm s)) ^ (2 : Nat) := hsum1
          _ = a (Fin.last n) * (reindex2 (reindex1 x)).1 PUnit.unit ^ (2 : Nat)
                + ∑ i : Fin n, a i.castSucc * (reindex2 (reindex1 x)).2 i ^ (2 : Nat) := by
                  have hfst0 : (reindex2 (reindex1 x)).1 PUnit.unit = reindex1 x (Sum.inl ()) := by
                    rfl
                  have hsnd0 : ∀ i : Fin n, (reindex2 (reindex1 x)).2 i = reindex1 x (Sum.inr i) := by
                    intro i
                    rfl
                  have hfst : (reindex2 (reindex1 x)).1 PUnit.unit = x (Fin.last n) := by
                    rw [hfst0]
                    rw [hreindex1_apply, esymm_left]
                  have hsnd : ∀ i : Fin n, (reindex2 (reindex1 x)).2 i = x i.castSucc := by
                    intro i
                    rw [hsnd0]
                    rw [hreindex1_apply, esymm_right]
                  rw [Fintype.sum_sum_type]
                  simp [hfst, hsnd]
                  simp [esymm_left, esymm_right]
          _ = a (Fin.last n) * (split x).1 ^ (2 : Nat)
                + ∑ i : Fin n, a i.castSucc * (split x).2 i ^ (2 : Nat) := by
                  rfl
      have htransport :=
        MeasureTheory.MeasurePreserving.integral_comp hpres hsplit_meas
          (fun p : ℝ × (Fin n → ℝ) =>
            Real.exp (-(a (Fin.last n) * p.1 ^ (2 : Nat)
              + ∑ i : Fin n, a i.castSucc * p.2 i ^ (2 : Nat))))
      calc
        ∫ x : Fin (n + 1) → ℝ, Real.exp (-∑ i : Fin (n + 1), a i * x i ^ (2 : Nat))
            = ∫ x : Fin (n + 1) → ℝ,
                Real.exp (-(a (Fin.last n) * (split x).1 ^ (2 : Nat)
                  + ∑ i : Fin n, a i.castSucc * (split x).2 i ^ (2 : Nat))) := by
                  congr with x
                  rw [hsum x]
        _ = ∫ p : ℝ × (Fin n → ℝ),
              Real.exp (-(a (Fin.last n) * p.1 ^ (2 : Nat)
                + ∑ i : Fin n, a i.castSucc * p.2 i ^ (2 : Nat))) := by
                simpa [split] using htransport
        _ = ∫ p : ℝ × (Fin n → ℝ),
              Real.exp (-(a (Fin.last n) * p.1 ^ (2 : Nat)))
                * Real.exp (-∑ i : Fin n, a i.castSucc * p.2 i ^ (2 : Nat)) := by
                  congr with p
                  rw [← Real.exp_add]
                  congr 1
                  ring
        _ = (∫ z : ℝ, Real.exp (-(a (Fin.last n) * z ^ (2 : Nat))))
              * ∫ y : Fin n → ℝ, Real.exp (-∑ i : Fin n, a i.castSucc * y i ^ (2 : Nat)) := by
                change
                  ∫ p : ℝ × (Fin n → ℝ),
                    Real.exp (-(a (Fin.last n) * p.1 ^ (2 : Nat)))
                      * Real.exp (-∑ i : Fin n, a i.castSucc * p.2 i ^ (2 : Nat))
                      ∂ (MeasureTheory.volume.prod MeasureTheory.volume)
                    = _
                rw [← MeasureTheory.integral_prod_mul]
        _ = Real.sqrt (Real.pi / a (Fin.last n))
              * ∏ i : Fin n, Real.sqrt (Real.pi / a i.castSucc) := by
                have hgauss :
                    (∫ z : ℝ, Real.exp (-(a (Fin.last n) * z ^ (2 : Nat))))
                      = Real.sqrt (Real.pi / a (Fin.last n)) := by
                  simpa [neg_mul, mul_assoc, mul_left_comm, mul_comm] using
                    (integral_gaussian (a (Fin.last n)))
                have hind :
                    ∫ y : Fin n → ℝ, Real.exp (-∑ i : Fin n, a i.castSucc * y i ^ (2 : Nat))
                      = ∏ i : Fin n, Real.sqrt (Real.pi / a i.castSucc) :=
                  gaussian_integral_diagonal_formula n (fun i : Fin n => a i.castSucc)
                    (fun i => ha i.castSucc)
                rw [hgauss]
                rw [hind]
        _ = ∏ i : Fin (n + 1), Real.sqrt (Real.pi / a i) := by
              rw [Fin.prod_univ_castSucc]
              rw [mul_comm]

private theorem gaussian_integral_diagonal_formula_lp
    (d : ℕ) (a : Fin d → ℝ) (ha : ∀ i, 0 < a i) :
    ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-∑ i : Fin d, a i * y.ofLp i ^ (2 : Nat))
      = ∏ i : Fin d, Real.sqrt (Real.pi / a i) := by
  have hpres :
      MeasureTheory.MeasurePreserving
        (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ))
        MeasureTheory.volume MeasureTheory.volume := by
    simpa using PiLp.volume_preserving_ofLp (ι := Fin d)
  have hmeas :
      MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) := by
    exact
      (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin d => ℝ)).measurableEmbedding
        (WithLp.ofLp_injective (p := (2 : ENNReal)))
  have htransport :=
    MeasureTheory.MeasurePreserving.integral_comp hpres hmeas
      (fun x : Fin d → ℝ => Real.exp (-∑ i : Fin d, a i * x i ^ (2 : Nat)))
  calc
    ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-∑ i : Fin d, a i * y.ofLp i ^ (2 : Nat))
        = ∫ x : Fin d → ℝ, Real.exp (-∑ i : Fin d, a i * x i ^ (2 : Nat)) := by
            simpa using htransport
    _ = ∏ i : Fin d, Real.sqrt (Real.pi / a i) :=
      gaussian_integral_diagonal_formula d a ha

private lemma matrix_isHermitian_of_isSymm_real
    {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsSymm) :
    A.IsHermitian := by
  simpa using hA

private theorem hermitian_trace_mul_self_eq_sum_eigenvalues_sq
    {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    Matrix.trace (A * A) = ∑ i, (hA.eigenvalues i) ^ (2 : Nat) := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  let D : Matrix n n ℝ := Matrix.diagonal (fun i => hA.eigenvalues i)
  have hspec : A = U * D * Matrix.conjTranspose U := by
    simpa [U, D, Unitary.conjStarAlgAut, Matrix.conjTranspose] using hA.spectral_theorem
  have hU_left : Matrix.conjTranspose U * U = 1 := by
    change star U * U = 1
    exact hA.eigenvectorUnitary.2.1
  have hU_right : U * Matrix.conjTranspose U = 1 := by
    change U * star U = 1
    exact hA.eigenvectorUnitary.2.2
  calc
    Matrix.trace (A * A)
        = Matrix.trace ((U * D * Matrix.conjTranspose U) * (U * D * Matrix.conjTranspose U)) := by
            rw [hspec]
    _ = Matrix.trace (U * (D * (Matrix.conjTranspose U * U) * D) * Matrix.conjTranspose U) := by
          simp [Matrix.mul_assoc]
    _ = Matrix.trace (Matrix.conjTranspose U * U * (D * (Matrix.conjTranspose U * U) * D)) := by
          simpa [Matrix.mul_assoc] using
            (Matrix.trace_mul_cycle U (D * (Matrix.conjTranspose U * U) * D) (Matrix.conjTranspose U))
    _ = Matrix.trace (((Matrix.conjTranspose U * U) * D) * ((Matrix.conjTranspose U * U) * D)) := by
          simp [Matrix.mul_assoc]
    _ = Matrix.trace (D * D) := by
          calc
            Matrix.trace (((Matrix.conjTranspose U * U) * D) * ((Matrix.conjTranspose U * U) * D))
                = Matrix.trace ((1 * D) * (1 * D)) := by rw [hU_left]
            _ = Matrix.trace (D * D) := by simp
    _ = ∑ i, (hA.eigenvalues i) ^ (2 : Nat) := by
          simpa [pow_two] using (by simp [D])

private theorem hermitian_det_one_add_smul_eq_prod
    {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (c : ℝ) :
    Matrix.det ((1 : Matrix n n ℝ) + c • A) = ∏ i, (1 + c * hA.eigenvalues i) := by
  let U : Matrix n n ℝ := hA.eigenvectorUnitary
  let D : Matrix n n ℝ := Matrix.diagonal (fun i => hA.eigenvalues i)
  have hspec : A = U * D * Matrix.conjTranspose U := by
    simpa [U, D, Unitary.conjStarAlgAut, Matrix.conjTranspose] using hA.spectral_theorem
  have hU_left : Matrix.conjTranspose U * U = 1 := by
    change star U * U = 1
    exact hA.eigenvectorUnitary.2.1
  have hU_right : U * Matrix.conjTranspose U = 1 := by
    change U * star U = 1
    exact hA.eigenvectorUnitary.2.2
  have hI : (1 : Matrix n n ℝ) = U * (1 : Matrix n n ℝ) * Matrix.conjTranspose U := by
    calc
      (1 : Matrix n n ℝ) = U * Matrix.conjTranspose U := by simpa using hU_right.symm
      _ = U * (1 : Matrix n n ℝ) * Matrix.conjTranspose U := by simp [Matrix.mul_assoc]
  have hdecomp :
      ((1 : Matrix n n ℝ) + c • A)
        = U * (((1 : Matrix n n ℝ) + c • D)) * Matrix.conjTranspose U := by
    calc
      ((1 : Matrix n n ℝ) + c • A)
          = U * (1 : Matrix n n ℝ) * Matrix.conjTranspose U + c • (U * D * Matrix.conjTranspose U) := by
              conv_lhs => rw [hI, hspec]
      _ = U * (1 : Matrix n n ℝ) * Matrix.conjTranspose U
            + U * (c • D) * Matrix.conjTranspose U := by
              simp [Matrix.mul_assoc]
      _ = U * (((1 : Matrix n n ℝ) + c • D)) * Matrix.conjTranspose U := by
            simp [Matrix.mul_add, add_mul, Matrix.mul_assoc]
  have hdiag_shift :
      ((1 : Matrix n n ℝ) + c • D) = Matrix.diagonal (fun i => 1 + c * hA.eigenvalues i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [D]
    · simp [D, hij]
  calc
    Matrix.det ((1 : Matrix n n ℝ) + c • A)
        = Matrix.det (U * (((1 : Matrix n n ℝ) + c • D)) * Matrix.conjTranspose U) := by
            rw [hdecomp]
    _ = Matrix.det U * Matrix.det (((1 : Matrix n n ℝ) + c • D)) * Matrix.det (Matrix.conjTranspose U) := by
          rw [Matrix.det_mul, Matrix.det_mul]
    _ = Matrix.det (((1 : Matrix n n ℝ) + c • D)) := by
          have hdetU :
              Matrix.det U * Matrix.det (Matrix.conjTranspose U) = 1 := by
            have hdet := congrArg Matrix.det hU_right
            simpa [Matrix.det_mul] using hdet
          have hdetU' : Matrix.det U * Matrix.det U = 1 := by
            simpa using hdetU
          have hdet_conj : Matrix.det (Matrix.conjTranspose U) = Matrix.det U := by
            simpa using Matrix.det_transpose U
          calc
            Matrix.det U * Matrix.det (((1 : Matrix n n ℝ) + c • D)) * Matrix.det (Matrix.conjTranspose U)
                = Matrix.det U * Matrix.det (((1 : Matrix n n ℝ) + c • D)) * Matrix.det U := by
                    rw [hdet_conj]
            _ = (Matrix.det U * Matrix.det U) * Matrix.det (((1 : Matrix n n ℝ) + c • D)) := by ring
            _ = Matrix.det (((1 : Matrix n n ℝ) + c • D)) := by simp [hdetU']
    _ = ∏ i, (1 + c * hA.eigenvalues i) := by
          rw [hdiag_shift]
          simpa using Matrix.det_diagonal (fun i => 1 + c * hA.eigenvalues i)

/-!
Local quartic compatibility layer.

These declarations were removed from the old monolithic foundational file during API
slimming, but the quartic bridge still uses them internally. Keep them local here so
that support code compiles without re-bloating the public Base API.
-/

/-- Finite-dimensional Cauchy-Schwarz for coordinate sums on real functions. -/
private lemma sum_mul_sq_le_sum_sq_mul_sum_sq {α : Type} [Fintype α] [DecidableEq α]
    (f g : α → ℝ) :
    (∑ i : α, f i * g i) ^ (2 : Nat)
      ≤ (∑ i : α, f i ^ (2 : Nat)) * ∑ i : α, g i ^ (2 : Nat) := by
  let x : EuclideanSpace ℝ α := WithLp.toLp 2 f
  let y : EuclideanSpace ℝ α := WithLp.toLp 2 g
  have hinner : inner ℝ x y = ∑ i : α, f i * g i := by
    simp [x, y, PiLp.inner_apply, mul_comm]
  have hx_sq : ‖x‖ ^ (2 : Nat) = ∑ i : α, f i ^ (2 : Nat) := by
    rw [← real_inner_self_eq_norm_sq x, PiLp.inner_apply]
    simp [x]
  have hy_sq : ‖y‖ ^ (2 : Nat) = ∑ i : α, g i ^ (2 : Nat) := by
    rw [← real_inner_self_eq_norm_sq y, PiLp.inner_apply]
    simp [y]
  have habs : |∑ i : α, f i * g i| ≤ ‖x‖ * ‖y‖ := by
    calc
      |∑ i : α, f i * g i| = ‖inner ℝ x y‖ := by
        rw [← hinner]
        simp
      _ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm x y
  have hxy_nonneg : 0 ≤ ‖x‖ * ‖y‖ := by positivity
  have hsq : (∑ i : α, f i * g i) ^ (2 : Nat) ≤ (‖x‖ * ‖y‖) ^ (2 : Nat) := by
    have hmul :
        |∑ i : α, f i * g i| * |∑ i : α, f i * g i|
          ≤ (‖x‖ * ‖y‖) * (‖x‖ * ‖y‖) := by
      exact mul_le_mul habs habs (abs_nonneg _) hxy_nonneg
    simpa [sq_abs, pow_two, abs_of_nonneg hxy_nonneg] using hmul
  calc
    (∑ i : α, f i * g i) ^ (2 : Nat) ≤ (‖x‖ * ‖y‖) ^ (2 : Nat) := hsq
    _ = (‖x‖ ^ (2 : Nat)) * (‖y‖ ^ (2 : Nat)) := by rw [mul_pow]
    _ = (∑ i : α, f i ^ (2 : Nat)) * ∑ i : α, g i ^ (2 : Nat) := by
          rw [hx_sq, hy_sq]

/-- The symmetric row coefficient associated to the strict upper-triangular data `B`. -/
private def triangleRowCoeff (n : ℕ) (B : Fin n → Fin n → ℝ) (i k : Fin n) : ℝ :=
  if k < i then B k i else if i < k then B i k else 0

/-- The squared Euclidean row norm of the symmetric zero-diagonal matrix encoded by `B`. -/
private def triangleRowSq (n : ℕ) (B : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ k : Fin n, triangleRowCoeff n B i k ^ (2 : Nat)

private lemma triangleThroughPair_eq_sum_triangleRowCoeff (n : ℕ) (B : Fin n → Fin n → ℝ)
    {u v : Fin n} (huv : u < v) :
    triangleThroughPair n B u v
      = ∑ k : Fin n, triangleRowCoeff n B u k * triangleRowCoeff n B v k := by
  unfold triangleThroughPair
  calc
    (∑ k : Fin n, if k < u then B k u * B k v else 0)
        + (∑ k : Fin n, if u < k ∧ k < v then B u k * B k v else 0)
        + (∑ k : Fin n, if v < k then B u k * B v k else 0)
      =
    ∑ k : Fin n,
      ((if k < u then B k u * B k v else 0)
        + (if u < k ∧ k < v then B u k * B k v else 0)
        + (if v < k then B u k * B v k else 0)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    _ = ∑ k : Fin n, triangleRowCoeff n B u k * triangleRowCoeff n B v k := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          unfold triangleRowCoeff
          by_cases hku : k < u
          · have hkv : k < v := lt_trans hku huv
            have huk : ¬ u < k := not_lt_of_ge hku.le
            have hvk : ¬ v < k := not_lt_of_ge hkv.le
            simp [hku, hkv, huk, hvk]
          · by_cases huk : u < k
            · by_cases hkv : k < v
              · have hvk : ¬ v < k := not_lt_of_ge hkv.le
                simp [hku, huk, hkv, hvk]
              · by_cases hvk : v < k
                · simp [hku, huk, hkv, hvk]
                · have hEq : k = v := le_antisymm (le_of_not_gt hvk) (le_of_not_gt hkv)
                  subst hEq
                  simp [huv, not_lt_of_ge huv.le]
            · have hEq : k = u := le_antisymm (le_of_not_gt huk) (le_of_not_gt hku)
              subst hEq
              simp [huv, not_lt_of_ge huv.le]

private lemma triangleRowSq_nonneg (n : ℕ) (B : Fin n → Fin n → ℝ) (i : Fin n) :
    0 ≤ triangleRowSq n B i := by
  unfold triangleRowSq
  refine Finset.sum_nonneg ?_
  intro k hk
  positivity

private lemma triangleThroughPair_sq_le_triangleRowSq_mul (n : ℕ) (B : Fin n → Fin n → ℝ)
    {u v : Fin n} (huv : u < v) :
    triangleThroughPair n B u v ^ (2 : Nat)
      ≤ triangleRowSq n B u * triangleRowSq n B v := by
  calc
    triangleThroughPair n B u v ^ (2 : Nat)
      = (∑ k : Fin n, triangleRowCoeff n B u k * triangleRowCoeff n B v k) ^ (2 : Nat) := by
          rw [triangleThroughPair_eq_sum_triangleRowCoeff n B huv]
    _ ≤ (∑ k : Fin n, triangleRowCoeff n B u k ^ (2 : Nat))
          * ∑ k : Fin n, triangleRowCoeff n B v k ^ (2 : Nat) := by
            exact sum_mul_sq_le_sum_sq_mul_sum_sq
              (fun k : Fin n => triangleRowCoeff n B u k)
              (fun k : Fin n => triangleRowCoeff n B v k)
    _ = triangleRowSq n B u * triangleRowSq n B v := by
          simp [triangleRowSq]

private lemma triangleRowSq_sum_eq_two_sNorm (n : ℕ) (B : Fin n → Fin n → ℝ) :
    ∑ i : Fin n, triangleRowSq n B i = 2 * sNorm n B := by
  let upper : Fin n × Fin n → ℝ := fun p =>
    if p.1 < p.2 then B p.1 p.2 ^ (2 : Nat) else 0
  let lower : Fin n × Fin n → ℝ := fun p =>
    if p.2 < p.1 then B p.2 p.1 ^ (2 : Nat) else 0
  have hsplit :
      ∑ i : Fin n, triangleRowSq n B i
        = (∑ p : Fin n × Fin n, upper p) + (∑ p : Fin n × Fin n, lower p) := by
    calc
      ∑ i : Fin n, triangleRowSq n B i
          = ∑ i : Fin n, ∑ k : Fin n, triangleRowCoeff n B i k ^ (2 : Nat) := by
              simp [triangleRowSq]
      _ = ∑ p : Fin n × Fin n, triangleRowCoeff n B p.1 p.2 ^ (2 : Nat) := by
            rw [Fintype.sum_prod_type]
      _ = ∑ p : Fin n × Fin n, (upper p + lower p) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            rcases p with ⟨i, k⟩
            by_cases hki : k < i
            · have hik : ¬ i < k := not_lt_of_ge hki.le
              simp [triangleRowCoeff, upper, lower, hki, hik]
            · by_cases hik : i < k
              · simp [triangleRowCoeff, upper, lower, hki, hik]
              · have hEq : i = k := by omega
                subst hEq
                simp [triangleRowCoeff, upper, lower]
      _ = (∑ p : Fin n × Fin n, upper p) + (∑ p : Fin n × Fin n, lower p) := by
            rw [Finset.sum_add_distrib]
  have hswap :
      (∑ p : Fin n × Fin n, lower p) = ∑ p : Fin n × Fin n, upper p := by
    refine Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n)) lower upper ?_
    intro p
    rcases p with ⟨i, k⟩
    simp [upper, lower]
  calc
    ∑ i : Fin n, triangleRowSq n B i
        = (∑ p : Fin n × Fin n, upper p) + (∑ p : Fin n × Fin n, lower p) := hsplit
    _ = (∑ p : Fin n × Fin n, upper p) + (∑ p : Fin n × Fin n, upper p) := by
          rw [hswap]
    _ = 2 * ∑ p : Fin n × Fin n, upper p := by ring
    _ = 2 * sNorm n B := by
          rw [Fintype.sum_prod_type]
          simp [upper, sNorm]

private lemma triangleThroughPair_sq_sum_le_four_mul_sNorm_sq
    (n : ℕ) (B : Fin n → Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
        if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0)
      ≤ 4 * sNorm n B ^ (2 : Nat) := by
  have hpair :
      ∀ i j : Fin n,
        (if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0)
          ≤ if i < j then triangleRowSq n B i * triangleRowSq n B j else 0 := by
    intro i j
    by_cases hij : i < j
    · simpa [hij] using triangleThroughPair_sq_le_triangleRowSq_mul n B hij
    · simp [hij]
  have hsum_le :
      (∑ i : Fin n, ∑ j : Fin n,
          if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0)
        ≤
      (∑ i : Fin n, ∑ j : Fin n,
          if i < j then triangleRowSq n B i * triangleRowSq n B j else 0) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    refine Finset.sum_le_sum ?_
    intro j hj
    exact hpair i j
  have hupper_le_total :
      (∑ i : Fin n, ∑ j : Fin n,
          if i < j then triangleRowSq n B i * triangleRowSq n B j else 0)
        ≤
      (∑ i : Fin n, ∑ j : Fin n, triangleRowSq n B i * triangleRowSq n B j) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    refine Finset.sum_le_sum ?_
    intro j hj
    by_cases hij : i < j
    · simp [hij]
    · have hnonneg : 0 ≤ triangleRowSq n B i * triangleRowSq n B j := by
        exact mul_nonneg (triangleRowSq_nonneg n B i) (triangleRowSq_nonneg n B j)
      simp [hij, hnonneg]
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0)
      ≤
    (∑ i : Fin n, ∑ j : Fin n,
        if i < j then triangleRowSq n B i * triangleRowSq n B j else 0) := hsum_le
    _ ≤ (∑ i : Fin n, ∑ j : Fin n, triangleRowSq n B i * triangleRowSq n B j) := hupper_le_total
    _ = (∑ i : Fin n, triangleRowSq n B i) * ∑ j : Fin n, triangleRowSq n B j := by
          rw [Finset.sum_mul_sum]
    _ = (2 * sNorm n B) * (2 * sNorm n B) := by
          rw [triangleRowSq_sum_eq_two_sNorm]
    _ = 4 * sNorm n B ^ (2 : Nat) := by
          ring

/-- The symmetric zero-diagonal matrix controlling the peeled quartic cross term. -/
private def quarticPeelMatrix (n : ℕ) (B : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    if i < j then triangleThroughPair n B i j
    else if j < i then triangleThroughPair n B j i
    else 0

private lemma quarticPeelMatrix_apply_lt (n : ℕ) (B : Fin n → Fin n → ℝ)
    {i j : Fin n} (hij : i < j) :
    quarticPeelMatrix n B i j = triangleThroughPair n B i j := by
  simp [quarticPeelMatrix, hij]

private lemma quarticPeelMatrix_apply_gt (n : ℕ) (B : Fin n → Fin n → ℝ)
    {i j : Fin n} (hji : j < i) :
    quarticPeelMatrix n B i j = triangleThroughPair n B j i := by
  have hij : ¬ i < j := not_lt_of_ge hji.le
  simp [quarticPeelMatrix, hij, hji]

private lemma quarticPeelMatrix_apply_diag (n : ℕ) (B : Fin n → Fin n → ℝ) (i : Fin n) :
    quarticPeelMatrix n B i i = 0 := by
  simp [quarticPeelMatrix]

private lemma quarticPeelMatrix_isSymm (n : ℕ) (B : Fin n → Fin n → ℝ) :
    (quarticPeelMatrix n B).IsSymm := by
  unfold Matrix.IsSymm
  ext i j
  by_cases hij : i < j
  · rw [Matrix.transpose_apply]
    rw [quarticPeelMatrix_apply_gt (n := n) (B := B) (i := j) (j := i) hij]
    rw [quarticPeelMatrix_apply_lt (n := n) (B := B) (i := i) (j := j) hij]
  · by_cases hji : j < i
    · rw [Matrix.transpose_apply]
      rw [quarticPeelMatrix_apply_lt (n := n) (B := B) (i := j) (j := i) hji]
      rw [quarticPeelMatrix_apply_gt (n := n) (B := B) (i := i) (j := j) hji]
    · have hEq : i = j := by omega
      subst hEq
      simp [Matrix.transpose_apply, quarticPeelMatrix_apply_diag]

private lemma quarticPeelMatrix_trace_eq_zero (n : ℕ) (B : Fin n → Fin n → ℝ) :
    Matrix.trace (quarticPeelMatrix n B) = 0 := by
  simp [Matrix.trace, quarticPeelMatrix_apply_diag]

private lemma quarticPeelMatrix_trace_mul_self_eq_sq_sum
    (n : ℕ) (B : Fin n → Fin n → ℝ) :
    Matrix.trace (quarticPeelMatrix n B * quarticPeelMatrix n B)
      = ∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j ^ (2 : Nat) := by
  let M : Matrix (Fin n) (Fin n) ℝ := quarticPeelMatrix n B
  calc
    Matrix.trace (quarticPeelMatrix n B * quarticPeelMatrix n B)
      = ∑ i : Fin n, ∑ j : Fin n, M i j * M j i := by
          simp [Matrix.trace, Matrix.mul_apply, M]
    _ = ∑ i : Fin n, ∑ j : Fin n, M i j * M i j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hsymm : M j i = M i j := by
            simpa [M] using (quarticPeelMatrix_isSymm n B).apply i j
          rw [hsymm]
    _ = ∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j ^ (2 : Nat) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [M, pow_two]

private lemma quarticPeelMatrix_quadraticForm_eq_two_mul_simpleCycle4LastCross
    (n : ℕ) (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j * x i * x j
      = 2 * simpleCycle4LastCross n B x := by
  have hpoint :
      ∀ i j : Fin n,
        quarticPeelMatrix n B i j * x i * x j
          =
        (if i < j then x i * x j * triangleThroughPair n B i j else 0)
          + (if j < i then x i * x j * triangleThroughPair n B j i else 0) := by
    intro i j
    by_cases hij : i < j
    · rw [quarticPeelMatrix_apply_lt n B hij]
      simp [hij, not_lt_of_ge hij.le]
      ring
    · by_cases hji : j < i
      · rw [quarticPeelMatrix_apply_gt n B hji]
        simp [hij, hji]
        ring
      · have hEq : i = j := by omega
        subst hEq
        simp [quarticPeelMatrix_apply_diag]
  have hsplit :
      (∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j * x i * x j)
        =
      (∑ i : Fin n, ∑ j : Fin n,
          if i < j then x i * x j * triangleThroughPair n B i j else 0)
        +
      (∑ i : Fin n, ∑ j : Fin n,
          if j < i then x i * x j * triangleThroughPair n B j i else 0) := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j * x i * x j)
          =
        ∑ i : Fin n, ∑ j : Fin n,
          ((if i < j then x i * x j * triangleThroughPair n B i j else 0)
            + (if j < i then x i * x j * triangleThroughPair n B j i else 0)) := by
              simp_rw [hpoint]
      _ =
        ∑ i : Fin n,
          ((∑ j : Fin n, if i < j then x i * x j * triangleThroughPair n B i j else 0)
            + ∑ j : Fin n, if j < i then x i * x j * triangleThroughPair n B j i else 0) := by
              simp_rw [Finset.sum_add_distrib]
      _ =
        (∑ i : Fin n, ∑ j : Fin n,
          if i < j then x i * x j * triangleThroughPair n B i j else 0)
        +
        (∑ i : Fin n, ∑ j : Fin n,
          if j < i then x i * x j * triangleThroughPair n B j i else 0) := by
              rw [Finset.sum_add_distrib]
  have hswap :
      (∑ i : Fin n, ∑ j : Fin n,
          if j < i then x i * x j * triangleThroughPair n B j i else 0)
        =
      (∑ i : Fin n, ∑ j : Fin n,
          if i < j then x i * x j * triangleThroughPair n B i j else 0) := by
    calc
      (∑ i : Fin n, ∑ j : Fin n,
          if j < i then x i * x j * triangleThroughPair n B j i else 0)
        = simpleCycle4LastCross n B x := by
              rw [Finset.sum_comm]
              simpa [mul_comm] using pair_triangleThroughPair_eq_simpleCycle4LastCross n B x
      _ = simpleCycle4LastCross n B x := by
            rfl
      _ =
        (∑ i : Fin n, ∑ j : Fin n,
          if i < j then x i * x j * triangleThroughPair n B i j else 0) := by
            exact (pair_triangleThroughPair_eq_simpleCycle4LastCross n B x).symm
  calc
    ∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j * x i * x j
        =
      (∑ i : Fin n, ∑ j : Fin n,
          if i < j then x i * x j * triangleThroughPair n B i j else 0)
        +
      (∑ i : Fin n, ∑ j : Fin n,
          if j < i then x i * x j * triangleThroughPair n B j i else 0) := hsplit
    _ =
      (∑ i : Fin n, ∑ j : Fin n,
          if i < j then x i * x j * triangleThroughPair n B i j else 0)
        +
      (∑ i : Fin n, ∑ j : Fin n,
          if i < j then x i * x j * triangleThroughPair n B i j else 0) := by
            rw [hswap]
    _ = 2 * (∑ i : Fin n, ∑ j : Fin n,
          if i < j then x i * x j * triangleThroughPair n B i j else 0) := by
            ring
    _ = 2 * simpleCycle4LastCross n B x := by
          rw [pair_triangleThroughPair_eq_simpleCycle4LastCross]

private lemma log_approx_near_one (u : ℝ) (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - u| ≤ 2 * u ^ (2 : Nat) := by
  have hpos : 0 < 1 + u := by
    linarith [abs_le.mp hu]
  have hupper : Real.log (1 + u) ≤ u := by
    simpa using Real.log_le_sub_one_of_pos hpos
  have hlower : u / (1 + u) ≤ Real.log (1 + u) := by
    have h' : 1 - (1 + u)⁻¹ ≤ Real.log (1 + u) := Real.one_sub_inv_le_log_of_pos hpos
    have hrew : 1 - (1 + u)⁻¹ = u / (1 + u) := by
      field_simp [hpos.ne']
      ring
    rw [hrew] at h'
    exact h'
  have hden_inv : (1 + u)⁻¹ ≤ 2 := by
    have : (1 : ℝ) ≤ 2 * (1 + u) := by
      linarith [abs_le.mp hu]
    simpa [one_div] using (div_le_iff₀ hpos).2 this
  have hnonneg : 0 ≤ u - Real.log (1 + u) := by
    linarith
  calc
    |Real.log (1 + u) - u| = u - Real.log (1 + u) := by
          rw [abs_sub_comm, abs_of_nonneg hnonneg]
    _ ≤ u - u / (1 + u) := by
          linarith
    _ = u ^ (2 : Nat) * (1 + u)⁻¹ := by
          field_simp [hpos.ne']
          ring
    _ ≤ u ^ (2 : Nat) * 2 := by
          exact mul_le_mul_of_nonneg_left hden_inv (by positivity : 0 ≤ u ^ (2 : Nat))
    _ = 2 * u ^ (2 : Nat) := by ring

private lemma quarticPeelMatrix_sq_sum_le_eight_sNorm_sq
    (n : ℕ) (B : Fin n → Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j ^ (2 : Nat)
      ≤ 8 * sNorm n B ^ (2 : Nat) := by
  have hpoint :
      ∀ i j : Fin n,
        quarticPeelMatrix n B i j ^ (2 : Nat)
          =
        (if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0)
          + (if j < i then triangleThroughPair n B j i ^ (2 : Nat) else 0) := by
    intro i j
    by_cases hij : i < j
    · rw [quarticPeelMatrix_apply_lt n B hij]
      simp [hij, not_lt_of_ge hij.le]
    · by_cases hji : j < i
      · rw [quarticPeelMatrix_apply_gt n B hji]
        simp [hij, hji]
      · have hEq : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
        subst hEq
        simp [quarticPeelMatrix]
  have hsplit :
      (∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j ^ (2 : Nat))
        =
      (∑ i : Fin n, ∑ j : Fin n,
          if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0)
        +
      (∑ i : Fin n, ∑ j : Fin n,
          if j < i then triangleThroughPair n B j i ^ (2 : Nat) else 0) := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j ^ (2 : Nat))
          = ∑ i : Fin n, ∑ j : Fin n,
              ((if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0)
                + (if j < i then triangleThroughPair n B j i ^ (2 : Nat) else 0)) := by
                  simp_rw [hpoint]
      _ = ∑ i : Fin n,
            ((∑ j : Fin n, if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0)
              + ∑ j : Fin n, if j < i then triangleThroughPair n B j i ^ (2 : Nat) else 0) := by
                simp_rw [Finset.sum_add_distrib]
      _ =
          (∑ i : Fin n, ∑ j : Fin n,
            if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0)
          +
          (∑ i : Fin n, ∑ j : Fin n,
            if j < i then triangleThroughPair n B j i ^ (2 : Nat) else 0) := by
              rw [Finset.sum_add_distrib]
  have hswap :
      (∑ i : Fin n, ∑ j : Fin n,
          if j < i then triangleThroughPair n B j i ^ (2 : Nat) else 0)
        =
      (∑ i : Fin n, ∑ j : Fin n,
          if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0) := by
    calc
      (∑ i : Fin n, ∑ j : Fin n,
          if j < i then triangleThroughPair n B j i ^ (2 : Nat) else 0)
        = ∑ j : Fin n, ∑ i : Fin n,
            if j < i then triangleThroughPair n B j i ^ (2 : Nat) else 0 := by
              rw [Finset.sum_comm]
      _ = (∑ i : Fin n, ∑ j : Fin n,
            if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0) := by
            simp
  calc
    ∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j ^ (2 : Nat)
        =
      (∑ i : Fin n, ∑ j : Fin n,
          if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0)
        +
      (∑ i : Fin n, ∑ j : Fin n,
          if j < i then triangleThroughPair n B j i ^ (2 : Nat) else 0) := hsplit
    _ =
      (∑ i : Fin n, ∑ j : Fin n,
          if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0)
        +
      (∑ i : Fin n, ∑ j : Fin n,
          if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0) := by
            rw [hswap]
    _ = 2 * (∑ i : Fin n, ∑ j : Fin n,
          if i < j then triangleThroughPair n B i j ^ (2 : Nat) else 0) := by
            ring
    _ ≤ 2 * (2 * sNorm n B) ^ (2 : Nat) := by
          have htri := triangleThroughPair_sq_sum_le_four_mul_sNorm_sq n B
          have hrewrite : 4 * sNorm n B ^ (2 : Nat) = (2 * sNorm n B) ^ (2 : Nat) := by
            ring
          simpa [hrewrite] using htri
    _ = 8 * sNorm n B ^ (2 : Nat) := by
          ring

private lemma quarticPeelMatrix_trace_mul_self_le_eight_sNorm_sq
    (n : ℕ) (B : Fin n → Fin n → ℝ) :
    Matrix.trace (quarticPeelMatrix n B * quarticPeelMatrix n B)
      ≤ 8 * sNorm n B ^ (2 : Nat) := by
  rw [quarticPeelMatrix_trace_mul_self_eq_sq_sum]
  exact quarticPeelMatrix_sq_sum_le_eight_sNorm_sq n B

private lemma sqrt_inv_one_sub_le_exp (u : ℝ) (hu : |u| ≤ 1 / 2) :
    Real.sqrt ((1 - u)⁻¹) ≤ Real.exp (u / 2 + u ^ (2 : Nat)) := by
  have hpos : 0 < 1 - u := by
    linarith [abs_le.mp hu]
  have hu_neg : |(-u)| ≤ 1 / 2 := by
    simpa [abs_neg] using hu
  have hlog :
      Real.log (1 - u) ≥ -u - 2 * u ^ (2 : Nat) := by
    have h := log_approx_near_one (-u) hu_neg
    have hleft : -(2 * u ^ (2 : Nat)) ≤ Real.log (1 - u) + u := by
      simpa [sub_eq_add_neg, pow_two, add_comm, add_left_comm, add_assoc] using (abs_le.mp h).1
    nlinarith
  have hexp :
      Real.exp (-(1 / 2 : ℝ) * Real.log (1 - u))
        ≤ Real.exp (u / 2 + u ^ (2 : Nat)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hrewrite :
      Real.exp (-(1 / 2 : ℝ) * Real.log (1 - u))
        = Real.sqrt ((1 - u)⁻¹) := by
    calc
      Real.exp (-(1 / 2 : ℝ) * Real.log (1 - u))
          = Real.exp (Real.log (1 - u) * (-(1 / 2 : ℝ))) := by
              congr 1
              ring
      _ = (1 - u) ^ (-(1 / 2 : ℝ)) := by
            simp [Real.rpow_def_of_pos hpos]
      _ = ((1 - u) ^ (1 / 2 : ℝ))⁻¹ := by
            rw [Real.rpow_neg hpos.le]
      _ = ((1 - u)⁻¹) ^ (1 / 2 : ℝ) := by
            rw [Real.inv_rpow hpos.le]
      _ = Real.sqrt ((1 - u)⁻¹) := by
            rw [← Real.sqrt_eq_rpow]
  calc
    Real.sqrt ((1 - u)⁻¹) = Real.exp (-(1 / 2 : ℝ) * Real.log (1 - u)) := hrewrite.symm
    _ ≤ Real.exp (u / 2 + u ^ (2 : Nat)) := hexp

private lemma eigenvalue_sq_le_trace_mul_self
    {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (i : n) :
    (hA.eigenvalues i) ^ (2 : Nat) ≤ Matrix.trace (A * A) := by
  rw [hermitian_trace_mul_self_eq_sum_eigenvalues_sq hA]
  have hnonneg : ∀ j ∈ (Finset.univ : Finset n), 0 ≤ (hA.eigenvalues j) ^ (2 : Nat) := by
    intro j hj
    positivity
  simpa using
    (Finset.single_le_sum hnonneg (show i ∈ (Finset.univ : Finset n) by simp))

private lemma quarticPeelMatrix_eigen_abs_le_four_sNorm
    (n : ℕ) (B : Fin n → Fin n → ℝ) (i : Fin n) :
    |(matrix_isHermitian_of_isSymm_real (quarticPeelMatrix_isSymm n B)).eigenvalues i|
      ≤ 4 * sNorm n B := by
  have hsq :
      ((matrix_isHermitian_of_isSymm_real (quarticPeelMatrix_isSymm n B)).eigenvalues i) ^ (2 : Nat)
        ≤ 8 * sNorm n B ^ (2 : Nat) := by
    exact (eigenvalue_sq_le_trace_mul_self
      (matrix_isHermitian_of_isSymm_real (quarticPeelMatrix_isSymm n B)) i).trans
      (quarticPeelMatrix_trace_mul_self_le_eight_sNorm_sq n B)
  have hnonneg : 0 ≤ sNorm n B := sNorm_nonneg n B
  have habs_sq :
      |(matrix_isHermitian_of_isSymm_real (quarticPeelMatrix_isSymm n B)).eigenvalues i| ^ (2 : Nat)
        ≤ 8 * sNorm n B ^ (2 : Nat) := by
    simpa [sq_abs] using hsq
  nlinarith

private lemma quarticPeelMatrix_factor_bound
    (n : ℕ) (β D t : ℝ) (hβ : 0 ≤ β) (_ht : 0 < t)
    (hsmall : β * (D / t) ≤ 1 / 2) (B : Fin n → Fin n → ℝ)
    (hB : sNorm n B ≤ D / t) :
    ∏ i : Fin n,
      Real.sqrt
        ((1 - (β / 4)
          * (matrix_isHermitian_of_isSymm_real (quarticPeelMatrix_isSymm n B)).eigenvalues i)⁻¹)
      ≤ Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat)) := by
  let hM : (quarticPeelMatrix n B).IsHermitian :=
    matrix_isHermitian_of_isSymm_real (quarticPeelMatrix_isSymm n B)
  let u : Fin n → ℝ := fun i => (β / 4) * hM.eigenvalues i
  change ∏ i : Fin n, Real.sqrt ((1 - u i)⁻¹)
      ≤ Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat))
  have hDt_nonneg : 0 ≤ D / t := by
    have hs_nonneg : 0 ≤ sNorm n B := sNorm_nonneg n B
    exact hs_nonneg.trans hB
  have hu_small : ∀ i : Fin n, |u i| ≤ 1 / 2 := by
    intro i
    have hLam : |hM.eigenvalues i| ≤ 4 * sNorm n B := quarticPeelMatrix_eigen_abs_le_four_sNorm n B i
    have hβ4_nonneg : 0 ≤ β / 4 := by
      nlinarith
    calc
      |u i| = |β / 4| * |hM.eigenvalues i| := by
        simp [u, abs_mul]
      _ = (β / 4) * |hM.eigenvalues i| := by
        simp [abs_of_nonneg hβ4_nonneg]
      _ ≤ (β / 4) * (4 * sNorm n B) := by
        exact mul_le_mul_of_nonneg_left hLam hβ4_nonneg
      _ = β * sNorm n B := by ring
      _ ≤ β * (D / t) := by
        exact mul_le_mul_of_nonneg_left hB hβ
      _ ≤ 1 / 2 := hsmall
  have hu_pos : ∀ i : Fin n, 0 < 1 - u i := by
    intro i
    have := hu_small i
    linarith [abs_le.mp this]
  have hsumLambda : ∑ i : Fin n, hM.eigenvalues i = 0 := by
    have htrace := hM.trace_eq_sum_eigenvalues
    simpa [hM, quarticPeelMatrix_trace_eq_zero n B] using htrace.symm
  have hsumu : ∑ i : Fin n, u i = 0 := by
    unfold u
    calc
      ∑ i : Fin n, (β / 4) * hM.eigenvalues i = (β / 4) * ∑ i : Fin n, hM.eigenvalues i := by
        rw [Finset.mul_sum]
      _ = 0 := by simp [hsumLambda]
  have hsumsq_le : ∑ i : Fin n, hM.eigenvalues i ^ (2 : Nat) ≤ 8 * (D / t) ^ (2 : Nat) := by
    have hs_nonneg : 0 ≤ sNorm n B := sNorm_nonneg n B
    have hsq_le : sNorm n B ^ (2 : Nat) ≤ (D / t) ^ (2 : Nat) := by
      exact pow_le_pow_left₀ hs_nonneg hB 2
    have htracele :
        Matrix.trace (quarticPeelMatrix n B * quarticPeelMatrix n B)
          ≤ 8 * (D / t) ^ (2 : Nat) := by
      calc
        Matrix.trace (quarticPeelMatrix n B * quarticPeelMatrix n B)
            ≤ 8 * sNorm n B ^ (2 : Nat) :=
              quarticPeelMatrix_trace_mul_self_le_eight_sNorm_sq n B
        _ ≤ 8 * (D / t) ^ (2 : Nat) := by
              nlinarith
    simpa [hM] using
      (hermitian_trace_mul_self_eq_sum_eigenvalues_sq hM).symm ▸ htracele
  have hsum_exp :
      ∑ i : Fin n, (u i / 2 + u i ^ (2 : Nat))
        = (β ^ (2 : Nat) / 16) * ∑ i : Fin n, hM.eigenvalues i ^ (2 : Nat) := by
    calc
      ∑ i : Fin n, (u i / 2 + u i ^ (2 : Nat))
          = (∑ i : Fin n, u i) / 2 + ∑ i : Fin n, u i ^ (2 : Nat) := by
              rw [Finset.sum_add_distrib, Finset.sum_div]
      _ = ∑ i : Fin n, u i ^ (2 : Nat) := by simp [hsumu]
      _ = ∑ i : Fin n, ((β ^ (2 : Nat) / 16) * hM.eigenvalues i ^ (2 : Nat)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            unfold u
            ring
      _ = (β ^ (2 : Nat) / 16) * ∑ i : Fin n, hM.eigenvalues i ^ (2 : Nat) := by
            rw [Finset.mul_sum]
  calc
    ∏ i : Fin n, Real.sqrt ((1 - u i)⁻¹)
        ≤ ∏ i : Fin n, Real.exp (u i / 2 + u i ^ (2 : Nat)) := by
            refine Finset.prod_le_prod ?_ ?_
            · intro i hi
              positivity
            · intro i hi
              exact sqrt_inv_one_sub_le_exp (u i) (hu_small i)
    _ = Real.exp (∑ i : Fin n, (u i / 2 + u i ^ (2 : Nat))) := by
          rw [← Real.exp_sum]
    _ = Real.exp ((β ^ (2 : Nat) / 16) * ∑ i : Fin n, hM.eigenvalues i ^ (2 : Nat)) := by
          rw [hsum_exp]
    _ ≤ Real.exp ((β ^ (2 : Nat) / 16) * (8 * (D / t) ^ (2 : Nat))) := by
          apply Real.exp_le_exp.mpr
          gcongr
    _ = Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat)) := by
          ring

private theorem toEuclideanLin_isSymmetric_of_isHermitian_real
    {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    (Matrix.toEuclideanLin A).IsSymmetric := by
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Matrix.toLpLin_apply, RCLike.inner_apply, WithLp.ofLp_toLp, starRingEnd_apply]
  simpa using calc
    y.ofLp ⬝ᵥ A.mulVec x.ofLp = Matrix.vecMul y.ofLp A ⬝ᵥ x.ofLp := by
      rw [Matrix.dotProduct_mulVec]
    _ = A.transpose.mulVec y.ofLp ⬝ᵥ x.ofLp := by
      rw [Matrix.mulVec_transpose]
    _ = A.mulVec y.ofLp ⬝ᵥ x.ofLp := by
      congr 1
      ext i
      have hrowcol : (fun j => A j i) = fun j => A i j := by
        funext j
        simpa using (hA.apply i j)
      simpa [Matrix.mulVec, hrowcol]

private theorem quadratic_form_eigenbasis_diag
    {n : Type} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (y : EuclideanSpace ℝ n) :
    inner ℝ ((Matrix.toEuclideanLin A) (hA.eigenvectorBasis.repr.symm y)) (hA.eigenvectorBasis.repr.symm y)
      = ∑ i, hA.eigenvalues i * (y.ofLp i) ^ (2 : Nat) := by
  let b := hA.eigenvectorBasis
  have hbasis : ∀ i : n, (Matrix.toEuclideanLin A) (b i) = hA.eigenvalues i • b i := by
    intro i
    ext j
    simp [b, Matrix.toLpLin_apply, hA.mulVec_eigenvectorBasis]
  have hdiagAct :
      (Matrix.toEuclideanLin A) (b.repr.symm y)
        = b.repr.symm (WithLp.toLp 2 (fun i => hA.eigenvalues i * y.ofLp i)) := by
    calc
      (Matrix.toEuclideanLin A) (b.repr.symm y)
          = (Matrix.toEuclideanLin A) (∑ i, y.ofLp i • b i) := by
              rw [b.sum_repr_symm]
      _ = ∑ i, y.ofLp i • (Matrix.toEuclideanLin A) (b i) := by
            simp
      _ = ∑ i, y.ofLp i • (hA.eigenvalues i • b i) := by
            simp [hbasis]
      _ = ∑ i, (hA.eigenvalues i * y.ofLp i) • b i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [smul_smul]
            ring
      _ = b.repr.symm (WithLp.toLp 2 (fun i => hA.eigenvalues i * y.ofLp i)) := by
            rw [← b.sum_repr_symm (WithLp.toLp 2 (fun i => hA.eigenvalues i * y.ofLp i))]
  have hinner :
      inner ℝ ((Matrix.toEuclideanLin A) (b.repr.symm y)) (b.repr.symm y)
        = inner ℝ (b.repr ((Matrix.toEuclideanLin A) (b.repr.symm y))) y := by
    rw [← b.repr.inner_map_map ((Matrix.toEuclideanLin A) (b.repr.symm y)) (b.repr.symm y)]
    simp
  rw [hinner, hdiagAct]
  rw [PiLp.inner_apply]
  simp [RCLike.inner_apply, pow_two, mul_assoc, mul_left_comm, mul_comm]

private theorem gaussian_integral_with_perturbation_bound_euclidean
    (n : ℕ) (β D t : ℝ) (hβ : 0 ≤ β) (ht : 0 < t)
    (hsmall : β * (D / t) ≤ 1 / 2) (B : Fin n → Fin n → ℝ)
    (hB : sNorm n B ≤ D / t) :
    ∫ y : EuclideanSpace ℝ (Fin n),
      Real.exp
        (-(2 * t * inner ℝ y y)
          + (β * t / 2)
              * inner ℝ ((Matrix.toEuclideanLin (quarticPeelMatrix n B)) y) y)
      ≤ Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat))
          * (Real.pi / (2 * t)) ^ ((n : ℝ) / 2) := by
  let hM : (quarticPeelMatrix n B).IsHermitian :=
    matrix_isHermitian_of_isSymm_real (quarticPeelMatrix_isSymm n B)
  let b := hM.eigenvectorBasis
  let u : Fin n → ℝ := fun i => (β / 4) * hM.eigenvalues i
  let a : Fin n → ℝ := fun i => (2 * t) * (1 - u i)
  have hu_small : ∀ i : Fin n, |u i| ≤ 1 / 2 := by
    intro i
    have hLam : |hM.eigenvalues i| ≤ 4 * sNorm n B := quarticPeelMatrix_eigen_abs_le_four_sNorm n B i
    have hβ4_nonneg : 0 ≤ β / 4 := by
      nlinarith
    calc
      |u i| = |β / 4| * |hM.eigenvalues i| := by
        simp [u, abs_mul]
      _ = (β / 4) * |hM.eigenvalues i| := by
        simp [abs_of_nonneg hβ4_nonneg]
      _ ≤ (β / 4) * (4 * sNorm n B) := by
        exact mul_le_mul_of_nonneg_left hLam hβ4_nonneg
      _ = β * sNorm n B := by ring
      _ ≤ β * (D / t) := by
        exact mul_le_mul_of_nonneg_left hB hβ
      _ ≤ 1 / 2 := hsmall
  have ha_pos : ∀ i : Fin n, 0 < a i := by
    intro i
    have hu := hu_small i
    have h1u : 0 < 1 - u i := by
      linarith [abs_le.mp hu]
    exact mul_pos (by positivity) h1u
  have hnorm_diag :
      ∀ y : EuclideanSpace ℝ (Fin n),
        inner ℝ (b.repr.symm y) (b.repr.symm y) = ∑ i : Fin n, y.ofLp i ^ (2 : Nat) := by
    intro y
    rw [← b.repr.inner_map_map (b.repr.symm y) (b.repr.symm y)]
    rw [PiLp.inner_apply]
    simp [RCLike.inner_apply, pow_two]
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    Real.exp
      (-(2 * t * inner ℝ y y)
        + (β * t / 2)
            * inner ℝ ((Matrix.toEuclideanLin (quarticPeelMatrix n B)) y) y)
  have hcomp :
      ∀ y : EuclideanSpace ℝ (Fin n),
        f (b.repr.symm y) = Real.exp (-∑ i : Fin n, a i * y.ofLp i ^ (2 : Nat)) := by
    intro y
    dsimp [f]
    rw [hnorm_diag]
    rw [quadratic_form_eigenbasis_diag hM]
    congr 1
    have hterm :
        ∀ i : Fin n,
          (-(2 * t * y.ofLp i ^ (2 : Nat))
            + (β * t / 2) * (hM.eigenvalues i * y.ofLp i ^ (2 : Nat)))
            = -(a i * y.ofLp i ^ (2 : Nat)) := by
      intro i
      dsimp [a, u]
      ring
    exact
      calc
      -(2 * t * ∑ i : Fin n, y.ofLp i ^ (2 : Nat))
          + (β * t / 2) * ∑ i : Fin n, hM.eigenvalues i * y.ofLp i ^ (2 : Nat)
        = ∑ i : Fin n,
            (-(2 * t * y.ofLp i ^ (2 : Nat))
              + (β * t / 2) * (hM.eigenvalues i * y.ofLp i ^ (2 : Nat))) := by
                rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      _ = ∑ i : Fin n, -(a i * y.ofLp i ^ (2 : Nat)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact hterm i
      _ = -∑ i : Fin n, a i * y.ofLp i ^ (2 : Nat) := by
            rw [Finset.sum_neg_distrib]
  have hpres :
      MeasureTheory.MeasurePreserving b.repr.symm MeasureTheory.volume MeasureTheory.volume := by
    simpa [b] using b.measurePreserving_repr_symm
  have htransport :=
    MeasureTheory.MeasurePreserving.integral_comp hpres
      (b.repr.symm.continuous.measurableEmbedding b.repr.symm.injective) f
  have hprod_eq :
      (∏ i : Fin n, Real.sqrt (Real.pi / a i))
        = (Real.pi / (2 * t)) ^ ((n : ℝ) / 2)
            * ∏ i : Fin n, Real.sqrt ((1 - u i)⁻¹) := by
    have hterm :
        ∀ i : Fin n,
          Real.sqrt (Real.pi / a i)
            = Real.sqrt (Real.pi / (2 * t)) * Real.sqrt ((1 - u i)⁻¹) := by
      intro i
      have h2t_pos : 0 < 2 * t := by positivity
      have h1u_pos : 0 < 1 - u i := by
        linarith [abs_le.mp (hu_small i)]
      calc
        Real.sqrt (Real.pi / a i)
            = Real.sqrt ((Real.pi / (2 * t)) * ((1 - u i)⁻¹)) := by
                congr 1
                field_simp [a, h2t_pos.ne', h1u_pos.ne']
                ring
        _ = Real.sqrt (Real.pi / (2 * t)) * Real.sqrt ((1 - u i)⁻¹) := by
              rw [Real.sqrt_mul (show 0 ≤ Real.pi / (2 * t) by positivity [Real.pi_pos, ht])]
    calc
      (∏ i : Fin n, Real.sqrt (Real.pi / a i))
          = ∏ i : Fin n, (Real.sqrt (Real.pi / (2 * t)) * Real.sqrt ((1 - u i)⁻¹)) := by
                refine Finset.prod_congr rfl ?_
                intro i hi
                exact hterm i
      _ = (∏ i : Fin n, Real.sqrt (Real.pi / (2 * t)))
            * ∏ i : Fin n, Real.sqrt ((1 - u i)⁻¹) := by
                rw [Finset.prod_mul_distrib]
      _ = (Real.sqrt (Real.pi / (2 * t))) ^ n
            * ∏ i : Fin n, Real.sqrt ((1 - u i)⁻¹) := by
                simp
      _ = (Real.pi / (2 * t)) ^ ((n : ℝ) / 2)
            * ∏ i : Fin n, Real.sqrt ((1 - u i)⁻¹) := by
                congr 1
                have hbase_pos : 0 < Real.pi / (2 * t) := by positivity [Real.pi_pos, ht]
                calc
                  (Real.sqrt (Real.pi / (2 * t))) ^ n
                      = ((Real.pi / (2 * t)) ^ (1 / 2 : ℝ)) ^ n := by
                          rw [Real.sqrt_eq_rpow]
                  _ = (Real.pi / (2 * t)) ^ ((1 / 2 : ℝ) * (n : ℝ)) := by
                        rw [← Real.rpow_natCast, ← Real.rpow_mul hbase_pos.le]
                  _ = (Real.pi / (2 * t)) ^ ((n : ℝ) / 2) := by
                        congr 1
                        ring
  change ∫ y : EuclideanSpace ℝ (Fin n), f y
      ≤ Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat))
          * (Real.pi / (2 * t)) ^ ((n : ℝ) / 2)
  calc
    ∫ y : EuclideanSpace ℝ (Fin n), f y
        = ∫ y : EuclideanSpace ℝ (Fin n), f (b.repr.symm y) := by
              symm
              simpa [f, b] using htransport
    _ = ∫ y : EuclideanSpace ℝ (Fin n), Real.exp (-∑ i : Fin n, a i * y.ofLp i ^ (2 : Nat)) := by
          refine MeasureTheory.integral_congr_ae ?_
          exact Filter.Eventually.of_forall hcomp
    _ = ∏ i : Fin n, Real.sqrt (Real.pi / a i) := by
          exact gaussian_integral_diagonal_formula_lp n a ha_pos
    _ = (Real.pi / (2 * t)) ^ ((n : ℝ) / 2)
          * ∏ i : Fin n, Real.sqrt ((1 - u i)⁻¹) := hprod_eq
    _ ≤ (Real.pi / (2 * t)) ^ ((n : ℝ) / 2)
          * Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat)) := by
            have hbase_nonneg : 0 ≤ (Real.pi / (2 * t)) ^ ((n : ℝ) / 2) := by
              positivity [Real.pi_pos, ht]
            exact mul_le_mul_of_nonneg_left
              (quarticPeelMatrix_factor_bound n β D t hβ ht hsmall B hB)
              hbase_nonneg
    _ = Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat))
          * (Real.pi / (2 * t)) ^ ((n : ℝ) / 2) := by
            ring

/-- Gaussian integral bound after inserting the quartic perturbation matrix.

This is the basic quadratic-form estimate used to control the peeled quartic
core by a Gaussian main term with an explicit exponential correction. -/
theorem gaussian_integral_with_perturbation_bound
    (n : ℕ) (β D t : ℝ) (hβ : 0 ≤ β) (ht : 0 < t)
    (hsmall : β * (D / t) ≤ 1 / 2) (B : Fin n → Fin n → ℝ)
    (hB : sNorm n B ≤ D / t) :
    ∫ x : Fin n → ℝ,
      Real.exp
        (-(2 * t * ∑ i : Fin n, x i ^ (2 : Nat))
          + (β * t / 2)
              * ∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j * x i * x j)
      ≤ Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat))
          * (Real.pi / (2 * t)) ^ ((n : ℝ) / 2) := by
  let F : (Fin n → ℝ) → ℝ := fun x =>
    Real.exp
      (-(2 * t * ∑ i : Fin n, x i ^ (2 : Nat))
        + (β * t / 2)
            * ∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j * x i * x j)
  let G : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    Real.exp
      (-(2 * t * inner ℝ y y)
        + (β * t / 2)
            * inner ℝ ((Matrix.toEuclideanLin (quarticPeelMatrix n B)) y) y)
  have hpres :
      MeasureTheory.MeasurePreserving
        (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ))
        MeasureTheory.volume MeasureTheory.volume := by
    simpa using PiLp.volume_preserving_ofLp (ι := Fin n)
  have hmeas :
      MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) := by
    exact
      (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ)).measurableEmbedding
        (WithLp.ofLp_injective (p := (2 : ENNReal)))
  have hcomp : ∀ y : EuclideanSpace ℝ (Fin n), F (WithLp.ofLp y) = G y := by
    intro y
    dsimp [F, G]
    have hnorm : inner ℝ y y = ∑ i : Fin n, y.ofLp i ^ (2 : Nat) := by
      rw [PiLp.inner_apply]
      simp [pow_two]
    have hquad :
        inner ℝ ((Matrix.toEuclideanLin (quarticPeelMatrix n B)) y) y
          = ∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j * y.ofLp i * y.ofLp j := by
      calc
        inner ℝ ((Matrix.toEuclideanLin (quarticPeelMatrix n B)) y) y
            = ∑ i : Fin n, y.ofLp i * ((quarticPeelMatrix n B).mulVec y.ofLp i) := by
                rw [PiLp.inner_apply]
                simp [Matrix.toLpLin_apply, RCLike.inner_apply]
        _ = ∑ i : Fin n, ((quarticPeelMatrix n B).mulVec y.ofLp i) * y.ofLp i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = ∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j * y.ofLp j * y.ofLp i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              change
                (∑ j : Fin n, quarticPeelMatrix n B i j * y.ofLp j) * y.ofLp i
                  = ∑ j : Fin n, quarticPeelMatrix n B i j * y.ofLp j * y.ofLp i
              rw [Finset.sum_mul]
        _ = ∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n B i j * y.ofLp i * y.ofLp j := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
    rw [hquad, hnorm]
  have htransport :=
    MeasureTheory.MeasurePreserving.integral_comp hpres hmeas F
  change ∫ x : Fin n → ℝ, F x
      ≤ Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat))
          * (Real.pi / (2 * t)) ^ ((n : ℝ) / 2)
  calc
    ∫ x : Fin n → ℝ, F x
        = ∫ y : EuclideanSpace ℝ (Fin n), F (WithLp.ofLp y) := by
              simpa [F] using htransport.symm
    _ = ∫ y : EuclideanSpace ℝ (Fin n), G y := by
          refine MeasureTheory.integral_congr_ae ?_
          exact Filter.Eventually.of_forall hcomp
    _ ≤ Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat))
          * (Real.pi / (2 * t)) ^ ((n : ℝ) / 2) := by
            exact gaussian_integral_with_perturbation_bound_euclidean n β D t hβ ht hsmall B hB

private lemma simpleCycle4LastCross_abs_le_two_mul_sNorm_mul_sum_sq
    (n : ℕ) (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    |simpleCycle4LastCross n B x|
      ≤ (2 * sNorm n B) * ∑ i : Fin n, x i ^ (2 : Nat) := by
  let M : Matrix (Fin n) (Fin n) ℝ := quarticPeelMatrix n B
  let hM : M.IsHermitian := matrix_isHermitian_of_isSymm_real (quarticPeelMatrix_isSymm n B)
  let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  let z : EuclideanSpace ℝ (Fin n) := hM.eigenvectorBasis.repr y
  have hnorm_x :
      inner ℝ y y = ∑ i : Fin n, x i ^ (2 : Nat) := by
    rw [PiLp.inner_apply]
    simp [y, pow_two]
  have hnorm_z :
      ∑ i : Fin n, z.ofLp i ^ (2 : Nat) = ∑ i : Fin n, x i ^ (2 : Nat) := by
    calc
      ∑ i : Fin n, z.ofLp i ^ (2 : Nat) = inner ℝ z z := by
            rw [PiLp.inner_apply]
            simp [z, pow_two]
      _ = inner ℝ y y := by
            simpa [z] using (hM.eigenvectorBasis.repr.inner_map_map y y)
      _ = ∑ i : Fin n, x i ^ (2 : Nat) := hnorm_x
  have hquad_sum :
      inner ℝ ((Matrix.toEuclideanLin M) y) y
        = ∑ i : Fin n, ∑ j : Fin n, M i j * x i * x j := by
    calc
      inner ℝ ((Matrix.toEuclideanLin M) y) y
          = ∑ i : Fin n, y.ofLp i * (M.mulVec y.ofLp i) := by
              rw [PiLp.inner_apply]
              simp [Matrix.toLpLin_apply, RCLike.inner_apply]
      _ = ∑ i : Fin n, (M.mulVec y.ofLp i) * y.ofLp i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = ∑ i : Fin n, ∑ j : Fin n, M i j * y.ofLp j * y.ofLp i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            change (∑ j : Fin n, M i j * y.ofLp j) * y.ofLp i
              = ∑ j : Fin n, M i j * y.ofLp j * y.ofLp i
            rw [Finset.sum_mul]
      _ = ∑ i : Fin n, ∑ j : Fin n, M i j * y.ofLp i * y.ofLp j := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
      _ = ∑ i : Fin n, ∑ j : Fin n, M i j * x i * x j := by
            simp [y]
  have hdiag :
      inner ℝ ((Matrix.toEuclideanLin M) y) y
        = ∑ i : Fin n, hM.eigenvalues i * z.ofLp i ^ (2 : Nat) := by
    simpa [M, y, z] using quadratic_form_eigenbasis_diag hM z
  have hquad_abs :
      |inner ℝ ((Matrix.toEuclideanLin M) y) y|
        ≤ 4 * sNorm n B * ∑ i : Fin n, x i ^ (2 : Nat) := by
    calc
      |inner ℝ ((Matrix.toEuclideanLin M) y) y|
          = |∑ i : Fin n, hM.eigenvalues i * z.ofLp i ^ (2 : Nat)| := by rw [hdiag]
      _ ≤ ∑ i : Fin n, |hM.eigenvalues i * z.ofLp i ^ (2 : Nat)| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin n, |hM.eigenvalues i| * z.ofLp i ^ (2 : Nat) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ z.ofLp i ^ (2 : Nat))]
      _ ≤ ∑ i : Fin n, (4 * sNorm n B) * z.ofLp i ^ (2 : Nat) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact mul_le_mul_of_nonneg_right
              (quarticPeelMatrix_eigen_abs_le_four_sNorm n B i)
              (by positivity : 0 ≤ z.ofLp i ^ (2 : Nat))
      _ = 4 * sNorm n B * ∑ i : Fin n, z.ofLp i ^ (2 : Nat) := by
            rw [Finset.mul_sum]
      _ = 4 * sNorm n B * ∑ i : Fin n, x i ^ (2 : Nat) := by
            rw [hnorm_z]
  have hcross :
      inner ℝ ((Matrix.toEuclideanLin M) y) y = 2 * simpleCycle4LastCross n B x := by
    calc
      inner ℝ ((Matrix.toEuclideanLin M) y) y
          = ∑ i : Fin n, ∑ j : Fin n, M i j * x i * x j := hquad_sum
      _ = 2 * simpleCycle4LastCross n B x := by
            simpa [M] using quarticPeelMatrix_quadraticForm_eq_two_mul_simpleCycle4LastCross n B x
  have hcross_abs :
      |2 * simpleCycle4LastCross n B x|
        ≤ 4 * sNorm n B * ∑ i : Fin n, x i ^ (2 : Nat) := by
    simpa [hcross] using hquad_abs
  have hsumsq_nonneg : 0 ≤ ∑ i : Fin n, x i ^ (2 : Nat) := by
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ))] at hcross_abs
  nlinarith [hcross_abs, sNorm_nonneg n B, hsumsq_nonneg]

private noncomputable def edgeSuccSplitEquiv (n : ℕ) :
    Cn3Torus.Edge (n + 1) ≃ Cn3Torus.Edge n ⊕ Fin n where
  toFun e := by
    rcases e with ⟨⟨i, j⟩, hij⟩
    by_cases hj : j = Fin.last n
    · exact Sum.inr (i.castLT (by
        show (i : ℕ) < n
        simpa [hj] using hij))
    · have hj_lt_n : (j : ℕ) < n := by
        have hj_le_n : (j : ℕ) ≤ n := Nat.le_of_lt_succ j.is_lt
        have hj_ne_n : (j : ℕ) ≠ n := by
          intro h
          apply hj
          apply Fin.ext
          simpa [Fin.last, h]
        exact lt_of_le_of_ne hj_le_n hj_ne_n
      exact
        Sum.inl
          ⟨(i.castLT (lt_trans hij hj_lt_n), j.castLT hj_lt_n), by simpa using hij⟩
  invFun s := by
    rcases s with e | i
    · exact ⟨(e.1.1.castSucc, e.1.2.castSucc), by simpa using e.2⟩
    · exact ⟨(i.castSucc, Fin.last n), by simpa using i.is_lt⟩
  left_inv := by
    intro e
    rcases e with ⟨⟨i, j⟩, hij⟩
    dsimp
    by_cases hj : j = Fin.last n <;> simp [hj]
  right_inv := by
    intro s
    rcases s with e | i
    · rcases e with ⟨⟨u, v⟩, huv⟩
      dsimp
      simp
    · dsimp
      simp

private noncomputable def edgeSplit (n : ℕ) :
    (Cn3Torus.Edge (n + 1) → ℝ) → (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) :=
  fun mu =>
    let reindex1 : (Cn3Torus.Edge (n + 1) → ℝ) ≃ᵐ ((Cn3Torus.Edge n ⊕ Fin n) → ℝ) :=
      MeasurableEquiv.piCongrLeft (fun _ : Cn3Torus.Edge n ⊕ Fin n => ℝ) (edgeSuccSplitEquiv n)
    let reindex2 : ((Cn3Torus.Edge n ⊕ Fin n) → ℝ) ≃ᵐ (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) :=
      MeasurableEquiv.sumPiEquivProdPi (fun _ : Cn3Torus.Edge n ⊕ Fin n => ℝ)
    reindex2 (reindex1 mu)

private lemma edgeSplit_fst_apply (n : ℕ) (mu : Cn3Torus.Edge (n + 1) → ℝ)
    (e : Cn3Torus.Edge n) :
    (edgeSplit n mu).1 e = mu ((edgeSuccSplitEquiv n).symm (Sum.inl e)) := by
  dsimp [edgeSplit]
  change
    ((MeasurableEquiv.piCongrLeft (fun _ : Cn3Torus.Edge n ⊕ Fin n => ℝ)
        (edgeSuccSplitEquiv n) mu) (Sum.inl e)) = _
  simpa using
    (Equiv.piCongrLeft_apply
      (P := fun _ : Cn3Torus.Edge n ⊕ Fin n => ℝ) (edgeSuccSplitEquiv n) mu (Sum.inl e))

private lemma edgeSplit_snd_apply (n : ℕ) (mu : Cn3Torus.Edge (n + 1) → ℝ)
    (i : Fin n) :
    (edgeSplit n mu).2 i = mu ((edgeSuccSplitEquiv n).symm (Sum.inr i)) := by
  dsimp [edgeSplit]
  change
    ((MeasurableEquiv.piCongrLeft (fun _ : Cn3Torus.Edge n ⊕ Fin n => ℝ)
        (edgeSuccSplitEquiv n) mu) (Sum.inr i)) = _
  simpa using
    (Equiv.piCongrLeft_apply
      (P := fun _ : Cn3Torus.Edge n ⊕ Fin n => ℝ) (edgeSuccSplitEquiv n) mu (Sum.inr i))

private lemma edgeSplit_measurePreserving (n : ℕ) :
    MeasureTheory.MeasurePreserving (edgeSplit n)
      MeasureTheory.volume MeasureTheory.volume := by
  let reindex1 : (Cn3Torus.Edge (n + 1) → ℝ) ≃ᵐ ((Cn3Torus.Edge n ⊕ Fin n) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Cn3Torus.Edge n ⊕ Fin n => ℝ) (edgeSuccSplitEquiv n)
  let reindex2 : ((Cn3Torus.Edge n ⊕ Fin n) → ℝ) ≃ᵐ (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : Cn3Torus.Edge n ⊕ Fin n => ℝ)
  have hpres1 :
      MeasureTheory.MeasurePreserving reindex1 MeasureTheory.volume MeasureTheory.volume := by
    simpa [reindex1] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Cn3Torus.Edge n ⊕ Fin n => ℝ) (edgeSuccSplitEquiv n))
  have hpres2 :
      MeasureTheory.MeasurePreserving reindex2 MeasureTheory.volume MeasureTheory.volume := by
    simpa [reindex2] using
      (MeasureTheory.volume_measurePreserving_sumPiEquivProdPi
        (fun _ : Cn3Torus.Edge n ⊕ Fin n => ℝ))
  simpa [edgeSplit, reindex1, reindex2] using hpres2.comp hpres1

private lemma edgeSplit_measurableEmbedding (n : ℕ) :
    MeasurableEmbedding (edgeSplit n) := by
  let reindex1 : (Cn3Torus.Edge (n + 1) → ℝ) ≃ᵐ ((Cn3Torus.Edge n ⊕ Fin n) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Cn3Torus.Edge n ⊕ Fin n => ℝ) (edgeSuccSplitEquiv n)
  let reindex2 : ((Cn3Torus.Edge n ⊕ Fin n) → ℝ) ≃ᵐ (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : Cn3Torus.Edge n ⊕ Fin n => ℝ)
  exact reindex2.measurableEmbedding.comp reindex1.measurableEmbedding

private lemma edgeSplit_minor_eq (n : ℕ) (mu : Cn3Torus.Edge (n + 1) → ℝ) :
    minorLamLast (matrixOfEdge (n + 1) mu) = matrixOfEdge n (edgeSplit n mu).1 := by
  ext i j
  by_cases hij : i < j
  · simp [minorLamLast, matrixOfEdge, hij]
    rw [edgeSplit_fst_apply n mu ⟨(i, j), hij⟩]
    simp [edgeSuccSplitEquiv]
  · simp [minorLamLast, matrixOfEdge, hij]

private lemma edgeSplit_last_eq (n : ℕ) (mu : Cn3Torus.Edge (n + 1) → ℝ) :
    lastColLam (matrixOfEdge (n + 1) mu) = (edgeSplit n mu).2 := by
  ext i
  rw [edgeSplit_snd_apply]
  simp [lastColLam, matrixOfEdge, edgeSuccSplitEquiv]

private lemma sqNormEdge_edgeSplit (n : ℕ) (mu : Cn3Torus.Edge (n + 1) → ℝ) :
    Cn3Torus.sqNormEdge (n + 1) mu
      = Cn3Torus.sqNormEdge n (edgeSplit n mu).1
          + ∑ i : Fin n, (edgeSplit n mu).2 i ^ (2 : Nat) := by
  simpa [sNorm_matrixOfEdge_eq, edgeSplit_minor_eq, edgeSplit_last_eq] using
    sNorm_peel_last n (matrixOfEdge (n + 1) mu)

private lemma quarticCorr_edgeSplit (n : ℕ) (mu : Cn3Torus.Edge (n + 1) → ℝ) :
    quarticCorr (n + 1) (matrixOfEdge (n + 1) mu)
      = quarticCorr n (matrixOfEdge n (edgeSplit n mu).1)
          + simpleCycle4LastCross n (matrixOfEdge n (edgeSplit n mu).1) (edgeSplit n mu).2
          - (1 / 12 : ℝ) * ∑ i : Fin n, (edgeSplit n mu).2 i ^ (4 : Nat) := by
  simpa [edgeSplit_minor_eq, edgeSplit_last_eq] using
    quarticCorr_peel_last n (matrixOfEdge (n + 1) mu)

private lemma gaussian_integrable_fin (n : ℕ) (a : ℝ) (ha : 0 < a) :
    MeasureTheory.Integrable
      (fun x : Fin n → ℝ => Real.exp (-a * ∑ i : Fin n, x i ^ (2 : Nat))) := by
  by_contra hnot
  have hformula := gaussian_integral_formula n a ha
  rw [MeasureTheory.integral_undef hnot] at hformula
  have hpos : 0 < (Real.pi / a) ^ ((n : ℝ) / 2) := by
    positivity [Real.pi_pos, ha]
  linarith

private lemma dim_succ (n : ℕ) : dim (n + 1) = dim n + n := by
  unfold dim
  simpa [Nat.add_comm] using (Nat.choose_succ_succ n 1)

private lemma gaussianF_mul (d₁ d₂ : ℕ) (t : ℝ) (ht : 0 < t) :
    gaussianF d₁ t * gaussianF d₂ t = gaussianF (d₁ + d₂) t := by
  unfold gaussianF
  have hbase_pos : 0 < Real.pi / (2 * t) := by
    positivity [Real.pi_pos, ht]
  rw [← Real.rpow_add hbase_pos]
  congr 1
  norm_num [Nat.cast_add]
  ring

def edgeCoreRegionD (n : ℕ) (D t : ℝ) : Set (Cn3Torus.Edge n → ℝ) :=
  {mu | Cn3Torus.sqNormEdge n mu ≤ D / t}

noncomputable def quarticCoreDensity (β t : ℝ) (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) : ℝ :=
  Real.exp (β * t * quarticCorr n (matrixOfEdge n mu)) *
    Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)

noncomputable def quarticCoreTrunc (β D t : ℝ) (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) : ℝ :=
  Set.indicator (edgeCoreRegionD n D t) (quarticCoreDensity β t n) mu

private def peeledCoreRegionD (n : ℕ) (D t : ℝ) :
    Set ((Cn3Torus.Edge n → ℝ) × (Fin n → ℝ)) :=
  {p | Cn3Torus.sqNormEdge n p.1 + ∑ i : Fin n, p.2 i ^ (2 : Nat) ≤ D / t}

noncomputable def peeledQuarticDensity (β t : ℝ) (n : ℕ)
    (p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ)) : ℝ :=
  Real.exp
      (β * t *
        (quarticCorr n (matrixOfEdge n p.1)
          + simpleCycle4LastCross n (matrixOfEdge n p.1) p.2
          - (1 / 12 : ℝ) * ∑ i : Fin n, p.2 i ^ (4 : Nat))) *
    Real.exp
      (-2 * t * (Cn3Torus.sqNormEdge n p.1 + ∑ i : Fin n, p.2 i ^ (2 : Nat)))

noncomputable def peeledQuarticTrunc (β D t : ℝ) (n : ℕ)
    (p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ)) : ℝ :=
  Set.indicator (peeledCoreRegionD n D t) (peeledQuarticDensity β t n) p

lemma measurableSet_edgeCoreRegionD (n : ℕ) (D t : ℝ) :
    MeasurableSet (edgeCoreRegionD n D t) := by
  exact (Cn3Torus.continuous_sqNormEdge n).measurable measurableSet_Iic

private lemma measurableSet_peeledCoreRegionD (n : ℕ) (D t : ℝ) :
    MeasurableSet (peeledCoreRegionD n D t) := by
  have hsq :
      Continuous (fun x : Fin n → ℝ => ∑ i : Fin n, x i ^ (2 : Nat)) := by
    refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
    intro i hi
    exact (continuous_apply i).pow 2
  have hcont :
      Continuous (fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) =>
        Cn3Torus.sqNormEdge n p.1 + ∑ i : Fin n, p.2 i ^ (2 : Nat)) := by
    exact ((Cn3Torus.continuous_sqNormEdge n).comp continuous_fst).add
      (hsq.comp continuous_snd)
  exact hcont.measurable measurableSet_Iic

private lemma continuous_sNorm (n : ℕ) : Continuous (sNorm n) := by
  unfold sNorm
  refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro i hi
  refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro j hj
  by_cases hij : i < j
  · let fij : Continuous fun lam : Fin n → Fin n → ℝ => lam i j :=
      (continuous_apply j).comp (continuous_apply i)
    simpa [hij] using fij.pow 2
  · simpa [hij] using (continuous_const : Continuous fun _ : Fin n → Fin n → ℝ => (0 : ℝ))

private lemma continuous_quarticCorr (n : ℕ) : Continuous (quarticCorr n) := by
  have hs : Continuous (fun lam : Fin n → Fin n → ℝ => sNorm n lam ^ (2 : Nat)) :=
    (continuous_sNorm n).pow 2
  have hmain :
      Continuous (fun lam : Fin n → Fin n → ℝ =>
        momentX n lam 4 - 3 * sNorm n lam ^ (2 : Nat)) := by
    simpa using (continuous_momentX n 4).sub ((continuous_const.mul hs))
  have htmp :
      Continuous (fun lam : Fin n → Fin n → ℝ =>
        ((24 : ℝ)⁻¹) * (momentX n lam 4 - 3 * sNorm n lam ^ (2 : Nat))) := by
    exact continuous_const.mul hmain
  have hscaled :
      Continuous (fun lam : Fin n → Fin n → ℝ =>
        ((momentX n lam 4 - 3 * sNorm n lam ^ (2 : Nat)) / 24 : ℝ)) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using htmp
  have hEq :
      (fun lam : Fin n → Fin n → ℝ => quarticCorr n lam)
        =
      (fun lam : Fin n → Fin n → ℝ =>
        ((momentX n lam 4 - 3 * sNorm n lam ^ (2 : Nat)) / 24 : ℝ)) := by
    funext lam
    symm
    exact fourth_cumulant_identity n lam
  simpa [hEq] using hscaled

private lemma continuous_quarticCorr_edge (n : ℕ) :
    Continuous (fun mu : Cn3Torus.Edge n → ℝ => quarticCorr n (matrixOfEdge n mu)) := by
  exact (continuous_quarticCorr n).comp (continuous_matrixOfEdge n)

private lemma continuous_simpleCycle4LastCross_pair (n : ℕ) :
    Continuous (fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) =>
      simpleCycle4LastCross n (matrixOfEdge n p.1) p.2) := by
  unfold simpleCycle4LastCross
  refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro i hi
  refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro j hj
  refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro k hk
  by_cases hijk : i < j ∧ j < k
  · have hij : i < j := hijk.1
    have hjk : j < k := hijk.2
    have hik : i < k := lt_trans hij hjk
    let hM : Continuous fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) => matrixOfEdge n p.1 :=
      (continuous_matrixOfEdge n).comp continuous_fst
    let hijc : Continuous fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) => matrixOfEdge n p.1 i j :=
      (continuous_apply j).comp ((continuous_apply i).comp hM)
    let hjkc : Continuous fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) => matrixOfEdge n p.1 j k :=
      (continuous_apply k).comp ((continuous_apply j).comp hM)
    let hikc : Continuous fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) => matrixOfEdge n p.1 i k :=
      (continuous_apply k).comp ((continuous_apply i).comp hM)
    let xic : Continuous fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) => p.2 i :=
      (continuous_apply i).comp continuous_snd
    let xjc : Continuous fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) => p.2 j :=
      (continuous_apply j).comp continuous_snd
    let xkc : Continuous fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) => p.2 k :=
      (continuous_apply k).comp continuous_snd
    have h1 :
        Continuous (fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) =>
          matrixOfEdge n p.1 i j * matrixOfEdge n p.1 j k * p.2 k * p.2 i) := by
      simpa [mul_assoc] using (((hijc.mul hjkc).mul xkc).mul xic)
    have h2 :
        Continuous (fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) =>
          matrixOfEdge n p.1 i j * p.2 j * p.2 k * matrixOfEdge n p.1 i k) := by
      simpa [mul_assoc] using (((hijc.mul xjc).mul xkc).mul hikc)
    have h3 :
        Continuous (fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) =>
          matrixOfEdge n p.1 i k * matrixOfEdge n p.1 j k * p.2 j * p.2 i) := by
      simpa [mul_assoc] using (((hikc.mul hjkc).mul xjc).mul xic)
    simpa [hijk, add_assoc] using h1.add (h2.add h3)
  · simpa [hijk] using
      (continuous_const : Continuous fun _ : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) => (0 : ℝ))

private lemma continuous_sum_sq_fin (n : ℕ) :
    Continuous (fun x : Fin n → ℝ => ∑ i : Fin n, x i ^ (2 : Nat)) := by
  refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro i hi
  exact (continuous_apply i).pow 2

private lemma continuous_sum_four_fin (n : ℕ) :
    Continuous (fun x : Fin n → ℝ => ∑ i : Fin n, x i ^ (4 : Nat)) := by
  refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro i hi
  exact (continuous_apply i).pow 4

private lemma quarticCoreTrunc_nonneg (β D t : ℝ) (n : ℕ) :
    ∀ mu : Cn3Torus.Edge n → ℝ, 0 ≤ quarticCoreTrunc β D t n mu := by
  intro mu
  unfold quarticCoreTrunc quarticCoreDensity
  by_cases hmu : mu ∈ edgeCoreRegionD n D t
  · simp [hmu]
    positivity
  · simp [hmu]

private lemma quarticCoreTrunc_measurable (β D t : ℝ) (n : ℕ) :
    Measurable (quarticCoreTrunc β D t n) := by
  unfold quarticCoreTrunc quarticCoreDensity
  refine Measurable.indicator ?_ (measurableSet_edgeCoreRegionD n D t)
  have hquartic' :
      Measurable (fun mu : Cn3Torus.Edge n → ℝ =>
        Real.exp ((β * t) * quarticCorr n (matrixOfEdge n mu))) := by
    exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_quarticCorr_edge n))).measurable
  have hquartic :
      Measurable (fun mu : Cn3Torus.Edge n → ℝ =>
        Real.exp (β * t * quarticCorr n (matrixOfEdge n mu))) := by
    simpa [mul_assoc] using hquartic'
  have hgauss' :
      Measurable (fun mu : Cn3Torus.Edge n → ℝ =>
        Real.exp (-((2 * t) * Cn3Torus.sqNormEdge n mu))) := by
    exact (Real.continuous_exp.comp
      ((continuous_const.mul (Cn3Torus.continuous_sqNormEdge n)).neg)).measurable
  have hgauss :
      Measurable (fun mu : Cn3Torus.Edge n → ℝ =>
        Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)) := by
    simpa [mul_assoc] using hgauss'
  exact hquartic.mul hgauss

private lemma peeledQuarticTrunc_nonneg (β D t : ℝ) (n : ℕ) :
    ∀ p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ), 0 ≤ peeledQuarticTrunc β D t n p := by
  intro p
  unfold peeledQuarticTrunc peeledQuarticDensity
  by_cases hp : p ∈ peeledCoreRegionD n D t
  · simp [hp]
    positivity
  · simp [hp]

private lemma peeledQuarticTrunc_measurable (β D t : ℝ) (n : ℕ) :
    Measurable (peeledQuarticTrunc β D t n) := by
  unfold peeledQuarticTrunc peeledQuarticDensity
  refine Measurable.indicator ?_ (measurableSet_peeledCoreRegionD n D t)
  have hsumSq :
      Continuous (fun x : Fin n → ℝ => ∑ i : Fin n, x i ^ (2 : Nat)) := by
    refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
    intro i hi
    exact (continuous_apply i).pow 2
  have hsumFour :
      Continuous (fun x : Fin n → ℝ => ∑ i : Fin n, x i ^ (4 : Nat)) := by
    refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
    intro i hi
    exact (continuous_apply i).pow 4
  have hquarticPart :
      Continuous (fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) =>
        quarticCorr n (matrixOfEdge n p.1)
          + simpleCycle4LastCross n (matrixOfEdge n p.1) p.2
          - (1 / 12 : ℝ) * ∑ i : Fin n, p.2 i ^ (4 : Nat)) := by
    exact (((continuous_quarticCorr_edge n).comp continuous_fst).add
      (continuous_simpleCycle4LastCross_pair n)).sub
        (continuous_const.mul (hsumFour.comp continuous_snd))
  have hquartic' :
      Measurable (fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) =>
        Real.exp ((β * t) *
          (quarticCorr n (matrixOfEdge n p.1)
            + simpleCycle4LastCross n (matrixOfEdge n p.1) p.2
            - (1 / 12 : ℝ) * ∑ i : Fin n, p.2 i ^ (4 : Nat)))) := by
    exact (Real.continuous_exp.comp (continuous_const.mul hquarticPart)).measurable
  have hquartic :
      Measurable (fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) =>
        Real.exp
          (β * t *
            (quarticCorr n (matrixOfEdge n p.1)
              + simpleCycle4LastCross n (matrixOfEdge n p.1) p.2
              - (1 / 12 : ℝ) * ∑ i : Fin n, p.2 i ^ (4 : Nat)))) := by
    simpa [mul_assoc] using hquartic'
  have hgaussPart :
      Continuous (fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) =>
        Cn3Torus.sqNormEdge n p.1 + ∑ i : Fin n, p.2 i ^ (2 : Nat)) := by
    exact ((Cn3Torus.continuous_sqNormEdge n).comp continuous_fst).add
      (hsumSq.comp continuous_snd)
  have hgauss' :
      Measurable (fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) =>
        Real.exp (-((2 * t) *
          (Cn3Torus.sqNormEdge n p.1 + ∑ i : Fin n, p.2 i ^ (2 : Nat))))) := by
    exact (Real.continuous_exp.comp ((continuous_const.mul hgaussPart).neg)).measurable
  have hgauss :
      Measurable (fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) =>
        Real.exp (-2 * t * (Cn3Torus.sqNormEdge n p.1 + ∑ i : Fin n, p.2 i ^ (2 : Nat)))) := by
    simpa [mul_assoc] using hgauss'
  exact hquartic.mul hgauss

private lemma quarticCoreTrunc_succ_comp_edgeSplit
    (β D t : ℝ) (n : ℕ) (mu : Cn3Torus.Edge (n + 1) → ℝ) :
    quarticCoreTrunc β D t (n + 1) mu
      = peeledQuarticTrunc β D t n (edgeSplit n mu) := by
  have hsq := sqNormEdge_edgeSplit n mu
  have hquart := quarticCorr_edgeSplit n mu
  have hmem :
      mu ∈ edgeCoreRegionD (n + 1) D t ↔ edgeSplit n mu ∈ peeledCoreRegionD n D t := by
    simpa [edgeCoreRegionD, peeledCoreRegionD, hsq]
  by_cases hcore : mu ∈ edgeCoreRegionD (n + 1) D t
  · have hsplit : edgeSplit n mu ∈ peeledCoreRegionD n D t := (hmem.mp hcore)
    simp [quarticCoreTrunc, quarticCoreDensity, peeledQuarticTrunc, peeledQuarticDensity,
      hcore, hsplit, hsq, hquart]
  · have hsplit : edgeSplit n mu ∉ peeledCoreRegionD n D t := by
      intro hsplit
      exact hcore (hmem.mpr hsplit)
    simp [quarticCoreTrunc, peeledQuarticTrunc, hcore, hsplit]

private lemma peeledQuarticTrunc_le_dom
    (β D t : ℝ) (n : ℕ) (hβ : 0 ≤ β) (ht : 0 < t)
    (hsmall : β * (D / t) ≤ 1 / 2) :
    ∀ p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ),
      peeledQuarticTrunc β D t n p
        ≤ quarticCoreTrunc β D t n p.1
            * Real.exp (-t * ∑ i : Fin n, p.2 i ^ (2 : Nat)) := by
  intro p
  rcases p with ⟨mu, x⟩
  by_cases hp : (mu, x) ∈ peeledCoreRegionD n D t
  · have hsumSq_nonneg : 0 ≤ ∑ i : Fin n, x i ^ (2 : Nat) := by
      exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
    have hsumFour_nonneg : 0 ≤ ∑ i : Fin n, x i ^ (4 : Nat) := by
      exact Finset.sum_nonneg (fun i _ => by positivity)
    have hmu_core : mu ∈ edgeCoreRegionD n D t := by
      dsimp [peeledCoreRegionD, edgeCoreRegionD] at hp ⊢
      linarith
    have hmu_le : Cn3Torus.sqNormEdge n mu ≤ D / t := hmu_core
    have hsmall' : β * D ≤ t / 2 := by
      have ht_ne : t ≠ 0 := ne_of_gt ht
      field_simp [ht_ne] at hsmall
      nlinarith
    have hcross_abs :
        |simpleCycle4LastCross n (matrixOfEdge n mu) x|
          ≤ (2 * Cn3Torus.sqNormEdge n mu) * ∑ i : Fin n, x i ^ (2 : Nat) := by
      simpa [sNorm_matrixOfEdge_eq] using
        (simpleCycle4LastCross_abs_le_two_mul_sNorm_mul_sum_sq n (matrixOfEdge n mu) x)
    have hcross_le :
        simpleCycle4LastCross n (matrixOfEdge n mu) x
          ≤ (2 * Cn3Torus.sqNormEdge n mu) * ∑ i : Fin n, x i ^ (2 : Nat) := by
      exact le_trans (le_abs_self _) hcross_abs
    have hcross_main :
        β * t * simpleCycle4LastCross n (matrixOfEdge n mu) x
          ≤ t * ∑ i : Fin n, x i ^ (2 : Nat) := by
      have hβt_nonneg : 0 ≤ β * t := mul_nonneg hβ (le_of_lt ht)
      have hmul1 :
          β * t * simpleCycle4LastCross n (matrixOfEdge n mu) x
            ≤ β * t * ((2 * Cn3Torus.sqNormEdge n mu) * ∑ i : Fin n, x i ^ (2 : Nat)) := by
        exact mul_le_mul_of_nonneg_left hcross_le hβt_nonneg
      have hmul2 :
          β * t * ((2 * Cn3Torus.sqNormEdge n mu) * ∑ i : Fin n, x i ^ (2 : Nat))
            ≤ β * t * ((2 * (D / t)) * ∑ i : Fin n, x i ^ (2 : Nat)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by linarith) hsumSq_nonneg) hβt_nonneg
      have hmul3 :
          β * t * ((2 * (D / t)) * ∑ i : Fin n, x i ^ (2 : Nat))
            ≤ t * ∑ i : Fin n, x i ^ (2 : Nat) := by
        have ht_ne : t ≠ 0 := ne_of_gt ht
        rw [show
              β * t * ((2 * (D / t)) * ∑ i : Fin n, x i ^ (2 : Nat))
                = 2 * β * D * ∑ i : Fin n, x i ^ (2 : Nat) by
              field_simp [ht_ne]]
        nlinarith [hsmall', hsumSq_nonneg]
      exact le_trans hmul1 (le_trans hmul2 hmul3)
    have hexp_arg :
        β * t *
            (quarticCorr n (matrixOfEdge n mu)
              + simpleCycle4LastCross n (matrixOfEdge n mu) x
              - (1 / 12 : ℝ) * ∑ i : Fin n, x i ^ (4 : Nat))
          - 2 * t * (Cn3Torus.sqNormEdge n mu + ∑ i : Fin n, x i ^ (2 : Nat))
          ≤ β * t * quarticCorr n (matrixOfEdge n mu)
              - 2 * t * Cn3Torus.sqNormEdge n mu
              - t * ∑ i : Fin n, x i ^ (2 : Nat) := by
      have hquartic_nonneg :
          0 ≤ β * t * ((1 / 12 : ℝ) * ∑ i : Fin n, x i ^ (4 : Nat)) := by
        positivity
      nlinarith [hcross_main, hquartic_nonneg]
    have hexp_le :
        Real.exp
            (β * t *
                (quarticCorr n (matrixOfEdge n mu)
                  + simpleCycle4LastCross n (matrixOfEdge n mu) x
                  - (1 / 12 : ℝ) * ∑ i : Fin n, x i ^ (4 : Nat))
              - 2 * t * (Cn3Torus.sqNormEdge n mu + ∑ i : Fin n, x i ^ (2 : Nat)))
          ≤ Real.exp
                (β * t * quarticCorr n (matrixOfEdge n mu)
                  - 2 * t * Cn3Torus.sqNormEdge n mu
                  - t * ∑ i : Fin n, x i ^ (2 : Nat)) := by
      exact Real.exp_le_exp.mpr hexp_arg
    have hsplit :
        peeledQuarticTrunc β D t n (mu, x)
          = peeledQuarticDensity β t n (mu, x) := by
      simp [peeledQuarticTrunc, hp]
    have hcore :
        quarticCoreTrunc β D t n mu = quarticCoreDensity β t n mu := by
      simp [quarticCoreTrunc, hmu_core]
    rw [hsplit, hcore]
    unfold peeledQuarticDensity quarticCoreDensity
    calc
      Real.exp
          (β * t *
              (quarticCorr n (matrixOfEdge n mu)
                + simpleCycle4LastCross n (matrixOfEdge n mu) x
                - (1 / 12 : ℝ) * ∑ i : Fin n, x i ^ (4 : Nat))) *
        Real.exp (-2 * t * (Cn3Torus.sqNormEdge n mu + ∑ i : Fin n, x i ^ (2 : Nat)))
          = Real.exp
              (β * t *
                  (quarticCorr n (matrixOfEdge n mu)
                    + simpleCycle4LastCross n (matrixOfEdge n mu) x
                    - (1 / 12 : ℝ) * ∑ i : Fin n, x i ^ (4 : Nat))
                - 2 * t * (Cn3Torus.sqNormEdge n mu + ∑ i : Fin n, x i ^ (2 : Nat))) := by
              rw [← Real.exp_add]
              ring
      _ ≤ Real.exp
            (β * t * quarticCorr n (matrixOfEdge n mu)
              - 2 * t * Cn3Torus.sqNormEdge n mu
              - t * ∑ i : Fin n, x i ^ (2 : Nat)) := hexp_le
      _ = Real.exp (β * t * quarticCorr n (matrixOfEdge n mu))
            * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
            * Real.exp (-t * ∑ i : Fin n, x i ^ (2 : Nat)) := by
              have hrew :
                  β * t * quarticCorr n (matrixOfEdge n mu)
                      - 2 * t * Cn3Torus.sqNormEdge n mu
                      - t * ∑ i : Fin n, x i ^ (2 : Nat)
                    =
                      (β * t * quarticCorr n (matrixOfEdge n mu))
                        + ((-2 * t * Cn3Torus.sqNormEdge n mu)
                            + (-t * ∑ i : Fin n, x i ^ (2 : Nat))) := by
                ring
              rw [hrew, Real.exp_add, Real.exp_add]
              ring
  · have hnonneg :
        0 ≤ quarticCoreTrunc β D t n mu * Real.exp (-t * ∑ i : Fin n, x i ^ (2 : Nat)) := by
      have hcore_nonneg := quarticCoreTrunc_nonneg β D t n mu
      positivity
    simpa [peeledQuarticTrunc, hp] using hnonneg

private lemma peeledFiber_integral_bound
    (β D t : ℝ) (n : ℕ) (hβ : 0 ≤ β) (ht : 0 < t)
    (hsmall : β * (D / t) ≤ 1 / 2) (mu : Cn3Torus.Edge n → ℝ) :
    ∫ x : Fin n → ℝ, peeledQuarticTrunc β D t n (mu, x)
      ≤ quarticCoreTrunc β D t n mu
          * (Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat)) * gaussianF n t) := by
  by_cases hmu_core : mu ∈ edgeCoreRegionD n D t
  · have hmu_le : Cn3Torus.sqNormEdge n mu ≤ D / t := hmu_core
    have hsmall' : β * D ≤ t / 2 := by
      have ht_ne : t ≠ 0 := ne_of_gt ht
      have hsmall0 := hsmall
      field_simp [ht_ne] at hsmall0
      nlinarith
    let F : (Fin n → ℝ) → ℝ := fun x =>
      Real.exp
        (-(2 * t * ∑ i : Fin n, x i ^ (2 : Nat))
          + (β * t / 2)
              * ∑ i : Fin n, ∑ j : Fin n,
                  quarticPeelMatrix n (matrixOfEdge n mu) i j * x i * x j)
    have hF_meas : Measurable F := by
      dsimp [F]
      fun_prop
    have hF_dom :
        ∀ x : Fin n → ℝ, F x ≤ Real.exp (-t * ∑ i : Fin n, x i ^ (2 : Nat)) := by
      intro x
      dsimp [F]
      have hsumSq_nonneg : 0 ≤ ∑ i : Fin n, x i ^ (2 : Nat) := by
        exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
      have hcross_abs :
          |simpleCycle4LastCross n (matrixOfEdge n mu) x|
            ≤ (2 * Cn3Torus.sqNormEdge n mu) * ∑ i : Fin n, x i ^ (2 : Nat) := by
        simpa [sNorm_matrixOfEdge_eq] using
          (simpleCycle4LastCross_abs_le_two_mul_sNorm_mul_sum_sq n (matrixOfEdge n mu) x)
      have hcross_le :
          simpleCycle4LastCross n (matrixOfEdge n mu) x
            ≤ (2 * Cn3Torus.sqNormEdge n mu) * ∑ i : Fin n, x i ^ (2 : Nat) := by
        exact le_trans (le_abs_self _) hcross_abs
      have hcross_main :
          β * t * simpleCycle4LastCross n (matrixOfEdge n mu) x
            ≤ t * ∑ i : Fin n, x i ^ (2 : Nat) := by
        have hβt_nonneg : 0 ≤ β * t := mul_nonneg hβ (le_of_lt ht)
        have hmul1 :
            β * t * simpleCycle4LastCross n (matrixOfEdge n mu) x
              ≤ β * t * ((2 * Cn3Torus.sqNormEdge n mu) * ∑ i : Fin n, x i ^ (2 : Nat)) := by
          exact mul_le_mul_of_nonneg_left hcross_le hβt_nonneg
        have hmul2 :
            β * t * ((2 * Cn3Torus.sqNormEdge n mu) * ∑ i : Fin n, x i ^ (2 : Nat))
              ≤ β * t * ((2 * (D / t)) * ∑ i : Fin n, x i ^ (2 : Nat)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by linarith) hsumSq_nonneg) hβt_nonneg
        have hmul3 :
            β * t * ((2 * (D / t)) * ∑ i : Fin n, x i ^ (2 : Nat))
              ≤ t * ∑ i : Fin n, x i ^ (2 : Nat) := by
          have ht_ne : t ≠ 0 := ne_of_gt ht
          rw [show
                β * t * ((2 * (D / t)) * ∑ i : Fin n, x i ^ (2 : Nat))
                  = 2 * β * D * ∑ i : Fin n, x i ^ (2 : Nat) by
                field_simp [ht_ne]]
          nlinarith [hsmall', hsumSq_nonneg]
        exact le_trans hmul1 (le_trans hmul2 hmul3)
      have hquad :
          (β * t / 2)
              * ∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n (matrixOfEdge n mu) i j * x i * x j
            = β * t * simpleCycle4LastCross n (matrixOfEdge n mu) x := by
        rw [quarticPeelMatrix_quadraticForm_eq_two_mul_simpleCycle4LastCross]
        ring
      have hexp_arg :
          -(2 * t * ∑ i : Fin n, x i ^ (2 : Nat))
            + (β * t / 2)
                * ∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n (matrixOfEdge n mu) i j * x i * x j
          ≤ -t * ∑ i : Fin n, x i ^ (2 : Nat) := by
        rw [hquad]
        nlinarith [hcross_main]
      exact Real.exp_le_exp.mpr hexp_arg
    have hF_int : MeasureTheory.Integrable F := by
      have hgauss_int := gaussian_integrable_fin n t ht
      refine hgauss_int.mono hF_meas.aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall (fun x => by
        have hFx := hF_dom x
        have hFx_nonneg : 0 ≤ F x := by
          positivity
        simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le,
          abs_of_nonneg hFx_nonneg] using hFx)
    have hupper_int :
        MeasureTheory.Integrable (fun x : Fin n → ℝ => quarticCoreDensity β t n mu * F x) := by
      exact hF_int.const_mul (quarticCoreDensity β t n mu)
    have hpeeled_int :
        MeasureTheory.Integrable (fun x : Fin n → ℝ => peeledQuarticTrunc β D t n (mu, x)) := by
      have hgauss_int := gaussian_integrable_fin n t ht
      have hdom_int :
          MeasureTheory.Integrable
            (fun x : Fin n → ℝ =>
              quarticCoreTrunc β D t n mu * Real.exp (-t * ∑ i : Fin n, x i ^ (2 : Nat))) := by
        exact hgauss_int.const_mul (quarticCoreTrunc β D t n mu)
      have hpeeled_meas :
          Measurable (fun x : Fin n → ℝ => peeledQuarticTrunc β D t n (mu, x)) := by
        let g : (Fin n → ℝ) → (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) := fun x => (mu, x)
        have hg : Measurable g := by
          dsimp [g]
          fun_prop
        exact (peeledQuarticTrunc_measurable β D t n).comp hg
      refine hdom_int.mono
        hpeeled_meas.aestronglyMeasurable ?_
      exact Filter.Eventually.of_forall (fun x => by
        have hx := peeledQuarticTrunc_le_dom β D t n hβ ht hsmall (mu, x)
        have hcore_nonneg := quarticCoreTrunc_nonneg β D t n mu
        simpa [Real.norm_eq_abs, abs_of_nonneg (peeledQuarticTrunc_nonneg β D t n (mu, x)),
          abs_of_nonneg hcore_nonneg, abs_of_nonneg (Real.exp_pos _).le] using hx)
    have hpoint :
        ∀ x : Fin n → ℝ,
          peeledQuarticTrunc β D t n (mu, x)
            ≤ quarticCoreDensity β t n mu * F x := by
      intro x
      by_cases hp : (mu, x) ∈ peeledCoreRegionD n D t
      · have hsumFour_nonneg : 0 ≤ ∑ i : Fin n, x i ^ (4 : Nat) := by
          exact Finset.sum_nonneg (fun i _ => by positivity)
        have hdrop_arg :
            β * t *
                (quarticCorr n (matrixOfEdge n mu)
                  + simpleCycle4LastCross n (matrixOfEdge n mu) x
                  - (1 / 12 : ℝ) * ∑ i : Fin n, x i ^ (4 : Nat))
              ≤ β * t * quarticCorr n (matrixOfEdge n mu)
                  + β * t * simpleCycle4LastCross n (matrixOfEdge n mu) x := by
          have hquartic_nonneg :
              0 ≤ β * t * ((1 / 12 : ℝ) * ∑ i : Fin n, x i ^ (4 : Nat)) := by
            positivity
          nlinarith
        have hdrop :
            Real.exp
                (β * t *
                  (quarticCorr n (matrixOfEdge n mu)
                    + simpleCycle4LastCross n (matrixOfEdge n mu) x
                    - (1 / 12 : ℝ) * ∑ i : Fin n, x i ^ (4 : Nat)))
              ≤ Real.exp (β * t * quarticCorr n (matrixOfEdge n mu))
                  * Real.exp (β * t * simpleCycle4LastCross n (matrixOfEdge n mu) x) := by
          have := Real.exp_le_exp.mpr hdrop_arg
          simpa [Real.exp_add] using this
        have hquad :
            (β * t / 2)
                * ∑ i : Fin n, ∑ j : Fin n, quarticPeelMatrix n (matrixOfEdge n mu) i j * x i * x j
              = β * t * simpleCycle4LastCross n (matrixOfEdge n mu) x := by
          rw [quarticPeelMatrix_quadraticForm_eq_two_mul_simpleCycle4LastCross]
          ring
        have hmul :
            Real.exp
                (β * t *
                  (quarticCorr n (matrixOfEdge n mu)
                    + simpleCycle4LastCross n (matrixOfEdge n mu) x
                    - (1 / 12 : ℝ) * ∑ i : Fin n, x i ^ (4 : Nat))) *
              Real.exp (-2 * t * (Cn3Torus.sqNormEdge n mu + ∑ i : Fin n, x i ^ (2 : Nat)))
              ≤ (Real.exp (β * t * quarticCorr n (matrixOfEdge n mu))
                    * Real.exp (β * t * simpleCycle4LastCross n (matrixOfEdge n mu) x))
                    * Real.exp (-2 * t * (Cn3Torus.sqNormEdge n mu + ∑ i : Fin n, x i ^ (2 : Nat))) := by
          gcongr
        simpa [peeledQuarticTrunc, hp, peeledQuarticDensity] using
          hmul.trans_eq (by
            dsimp [quarticCoreDensity, F]
            rw [hquad]
            have hrew1 :
                -2 * t * (Cn3Torus.sqNormEdge n mu + ∑ i : Fin n, x i ^ (2 : Nat))
                  =
                    (-2 * t * Cn3Torus.sqNormEdge n mu)
                      + (-2 * t * ∑ i : Fin n, x i ^ (2 : Nat)) := by
              ring
            have hrew2 :
                (-2 * t * ∑ i : Fin n, x i ^ (2 : Nat))
                    + β * t * simpleCycle4LastCross n (matrixOfEdge n mu) x
                  =
                    -(2 * t * ∑ i : Fin n, x i ^ (2 : Nat))
                      + β * t * simpleCycle4LastCross n (matrixOfEdge n mu) x := by
              ring
            rw [hrew1, Real.exp_add, ← hrew2, Real.exp_add]
            ring)
      · simp [peeledQuarticTrunc, hp]
        have hnonneg : 0 ≤ quarticCoreDensity β t n mu * F x := by
          have hq_nonneg : 0 ≤ quarticCoreDensity β t n mu := by
            unfold quarticCoreDensity
            positivity
          have hF_nonneg : 0 ≤ F x := by positivity
          exact mul_nonneg hq_nonneg hF_nonneg
        exact hnonneg
    have hmono :
        ∫ x : Fin n → ℝ, peeledQuarticTrunc β D t n (mu, x)
          ≤ ∫ x : Fin n → ℝ, quarticCoreDensity β t n mu * F x := by
      exact MeasureTheory.integral_mono_ae hpeeled_int hupper_int
        (Filter.Eventually.of_forall hpoint)
    have hFG :
        ∫ x : Fin n → ℝ, quarticCoreDensity β t n mu * F x
          = quarticCoreDensity β t n mu * ∫ x : Fin n → ℝ, F x := by
      simpa using MeasureTheory.integral_const_mul (quarticCoreDensity β t n mu) F
    have hF_bound :
        ∫ x : Fin n → ℝ, F x
          ≤ Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat))
              * gaussianF n t := by
      have hgauss :=
        gaussian_integral_with_perturbation_bound n β D t hβ ht hsmall
          (matrixOfEdge n mu) (by simpa [sNorm_matrixOfEdge_eq] using hmu_le)
      simpa [gaussianF] using hgauss
    have hcore_eq :
        quarticCoreTrunc β D t n mu = quarticCoreDensity β t n mu := by
      simp [quarticCoreTrunc, hmu_core]
    have hcore_nonneg : 0 ≤ quarticCoreDensity β t n mu := by
      unfold quarticCoreDensity
      positivity
    rw [hcore_eq]
    calc
      ∫ x : Fin n → ℝ, peeledQuarticTrunc β D t n (mu, x)
          ≤ ∫ x : Fin n → ℝ, quarticCoreDensity β t n mu * F x := hmono
      _ = quarticCoreDensity β t n mu * ∫ x : Fin n → ℝ, F x := hFG
      _ ≤ quarticCoreDensity β t n mu
            * (Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat)) * gaussianF n t) := by
            exact mul_le_mul_of_nonneg_left hF_bound hcore_nonneg
  · have hzero :
        ∀ x : Fin n → ℝ, peeledQuarticTrunc β D t n (mu, x) = 0 := by
      intro x
      have hpx : (mu, x) ∉ peeledCoreRegionD n D t := by
        intro hp
        have : mu ∈ edgeCoreRegionD n D t := by
          dsimp [peeledCoreRegionD, edgeCoreRegionD] at hp ⊢
          have hsumSq_nonneg : 0 ≤ ∑ i : Fin n, x i ^ (2 : Nat) := by
            exact Finset.sum_nonneg (fun i _ => sq_nonneg (x i))
          linarith
        exact hmu_core this
      simp [peeledQuarticTrunc, hpx]
    simp [quarticCoreTrunc, hmu_core, hzero]

private theorem quarticCoreTrunc_step
    (β D t A : ℝ) (n : ℕ) (hβ : 0 ≤ β) (ht : 0 < t)
    (hsmall : β * (D / t) ≤ 1 / 2)
    (hbase_int : MeasureTheory.Integrable (quarticCoreTrunc β D t n))
    (hbase_bound : ∫ mu : Cn3Torus.Edge n → ℝ, quarticCoreTrunc β D t n mu ≤ A) :
    MeasureTheory.Integrable (quarticCoreTrunc β D t (n + 1)) ∧
      ∫ mu : Cn3Torus.Edge (n + 1) → ℝ, quarticCoreTrunc β D t (n + 1) mu
        ≤ (Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat)) * gaussianF n t) * A := by
  let C : ℝ := Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat)) * gaussianF n t
  have hgauss_int : MeasureTheory.Integrable
      (fun x : Fin n → ℝ => Real.exp (-t * ∑ i : Fin n, x i ^ (2 : Nat))) :=
    gaussian_integrable_fin n t ht
  have hdom_int :
      MeasureTheory.Integrable
        (fun p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ) =>
          quarticCoreTrunc β D t n p.1 * Real.exp (-t * ∑ i : Fin n, p.2 i ^ (2 : Nat))) := by
    exact hbase_int.mul_prod hgauss_int
  have hpeeled_int : MeasureTheory.Integrable (peeledQuarticTrunc β D t n) := by
    refine hdom_int.mono (peeledQuarticTrunc_measurable β D t n).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall (fun p => by
      have hp := peeledQuarticTrunc_le_dom β D t n hβ ht hsmall p
      have hdom_nonneg :
          0 ≤ quarticCoreTrunc β D t n p.1 * Real.exp (-t * ∑ i : Fin n, p.2 i ^ (2 : Nat)) := by
        have hcore_nonneg := quarticCoreTrunc_nonneg β D t n p.1
        positivity
      have hcore_nonneg := quarticCoreTrunc_nonneg β D t n p.1
      simpa [Real.norm_eq_abs, abs_of_nonneg (peeledQuarticTrunc_nonneg β D t n p),
        abs_of_nonneg hcore_nonneg, abs_of_nonneg (Real.exp_pos _).le,
        abs_of_nonneg hdom_nonneg] using hp)
  have hsucc_int_comp :
      MeasureTheory.Integrable (fun mu : Cn3Torus.Edge (n + 1) → ℝ =>
        peeledQuarticTrunc β D t n (edgeSplit n mu)) := by
    exact
      (MeasureTheory.MeasurePreserving.integrable_comp (edgeSplit_measurePreserving n)
        (peeledQuarticTrunc_measurable β D t n).aestronglyMeasurable).2 hpeeled_int
  have hsucc_int : MeasureTheory.Integrable (quarticCoreTrunc β D t (n + 1)) := by
    refine hsucc_int_comp.congr ?_
    exact Filter.Eventually.of_forall
      (fun mu => (quarticCoreTrunc_succ_comp_edgeSplit β D t n mu).symm)
  refine ⟨hsucc_int, ?_⟩
  have htransport :
      ∫ mu : Cn3Torus.Edge (n + 1) → ℝ, quarticCoreTrunc β D t (n + 1) mu
        = ∫ p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ), peeledQuarticTrunc β D t n p := by
    calc
      ∫ mu : Cn3Torus.Edge (n + 1) → ℝ, quarticCoreTrunc β D t (n + 1) mu
          = ∫ mu : Cn3Torus.Edge (n + 1) → ℝ, peeledQuarticTrunc β D t n (edgeSplit n mu) := by
              refine MeasureTheory.integral_congr_ae ?_
              exact Filter.Eventually.of_forall (quarticCoreTrunc_succ_comp_edgeSplit β D t n)
      _ = ∫ p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ), peeledQuarticTrunc β D t n p := by
            simpa using MeasureTheory.MeasurePreserving.integral_comp
              (edgeSplit_measurePreserving n) (edgeSplit_measurableEmbedding n)
              (peeledQuarticTrunc β D t n)
  have houter_int :
      MeasureTheory.Integrable
        (fun mu : Cn3Torus.Edge n → ℝ =>
          ∫ x : Fin n → ℝ, peeledQuarticTrunc β D t n (mu, x)) := by
    exact hpeeled_int.integral_prod_left
  have hupper_outer_int :
      MeasureTheory.Integrable (fun mu : Cn3Torus.Edge n → ℝ => quarticCoreTrunc β D t n mu * C) := by
    exact hbase_int.mul_const C
  have houter_bound :
      ∫ mu : Cn3Torus.Edge n → ℝ, ∫ x : Fin n → ℝ, peeledQuarticTrunc β D t n (mu, x)
        ≤ ∫ mu : Cn3Torus.Edge n → ℝ, quarticCoreTrunc β D t n mu * C := by
    exact MeasureTheory.integral_mono_ae houter_int hupper_outer_int
      (Filter.Eventually.of_forall
        (fun mu => by
          simpa [C] using peeledFiber_integral_bound β D t n hβ ht hsmall mu))
  have hpair_eq :
      ∫ p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ), peeledQuarticTrunc β D t n p
        = ∫ mu : Cn3Torus.Edge n → ℝ, ∫ x : Fin n → ℝ, peeledQuarticTrunc β D t n (mu, x) := by
    symm
    simpa [Function.uncurry] using
      (MeasureTheory.integral_integral
        (f := fun mu x => peeledQuarticTrunc β D t n (mu, x)) hpeeled_int)
  have hconst :
      ∫ mu : Cn3Torus.Edge n → ℝ, quarticCoreTrunc β D t n mu * C
        = C * ∫ mu : Cn3Torus.Edge n → ℝ, quarticCoreTrunc β D t n mu := by
    simpa [C, mul_comm, mul_left_comm, mul_assoc] using
      (MeasureTheory.integral_const_mul C (quarticCoreTrunc β D t n))
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    unfold gaussianF
    positivity [Real.pi_pos, ht]
  calc
    ∫ mu : Cn3Torus.Edge (n + 1) → ℝ, quarticCoreTrunc β D t (n + 1) mu
        = ∫ p : (Cn3Torus.Edge n → ℝ) × (Fin n → ℝ), peeledQuarticTrunc β D t n p := htransport
    _ = ∫ mu : Cn3Torus.Edge n → ℝ, ∫ x : Fin n → ℝ, peeledQuarticTrunc β D t n (mu, x) := hpair_eq
    _ ≤ ∫ mu : Cn3Torus.Edge n → ℝ, quarticCoreTrunc β D t n mu * C := houter_bound
    _ = C * ∫ mu : Cn3Torus.Edge n → ℝ, quarticCoreTrunc β D t n mu := hconst
    _ ≤ C * A := by
          exact mul_le_mul_of_nonneg_left hbase_bound hC_nonneg

/-- Integrability and global bound for the truncated quartic core density. -/
theorem quarticCoreTrunc_bound
    (β D t : ℝ) (hβ : 0 ≤ β) (hD : 0 ≤ D) (ht : 0 < t)
    (hsmall : β * (D / t) ≤ 1 / 2) :
    ∀ n : ℕ,
      MeasureTheory.Integrable (quarticCoreTrunc β D t n) ∧
        ∫ mu : Cn3Torus.Edge n → ℝ, quarticCoreTrunc β D t n mu
          ≤ Real.exp ((β ^ (2 : Nat) / 2) * (n : ℝ) * (D / t) ^ (2 : Nat))
              * gaussianF (dim n) t := by
  intro n
  induction n with
  | zero =>
      have hDt_nonneg : 0 ≤ D / t := div_nonneg hD (le_of_lt ht)
      have hfun :
          quarticCoreTrunc β D t 0
            = fun mu : Cn3Torus.Edge 0 → ℝ =>
                Real.exp (-((2 * t) * Cn3Torus.sqNormEdge 0 mu)) := by
        funext mu
        have hsq : Cn3Torus.sqNormEdge 0 mu = 0 := by
          have hEdge_empty : (Finset.univ : Finset (Cn3Torus.Edge 0)) = ∅ := by
            ext e
            simp [Cn3Torus.Edge]
          simp [Cn3Torus.sqNormEdge, hEdge_empty]
        have hquart : quarticCorr 0 (matrixOfEdge 0 mu) = 0 := by
          simp [quarticCorr, orderedCycle4, simpleCycle4]
        have hcore : mu ∈ edgeCoreRegionD 0 D t := by
          dsimp [edgeCoreRegionD]
          rw [hsq]
          exact hDt_nonneg
        simp [quarticCoreTrunc, quarticCoreDensity, hcore, hquart, hsq]
      refine ⟨?_, ?_⟩
      · simpa [hfun] using (gaussian_integrable_edge 0 (2 * t) (by positivity))
      · have hformula :
            ∫ mu : Cn3Torus.Edge 0 → ℝ, quarticCoreTrunc β D t 0 mu
              = gaussianF (dim 0) t := by
            simpa [hfun, gaussianF, dim, mul_comm, mul_left_comm, mul_assoc] using
              (gaussian_integral_formula_edge 0 (2 * t) (by positivity))
        simpa [gaussianF, dim] using (le_of_eq hformula)
  | succ n ih =>
      let A : ℝ :=
        Real.exp ((β ^ (2 : Nat) / 2) * (n : ℝ) * (D / t) ^ (2 : Nat))
          * gaussianF (dim n) t
      obtain ⟨hstep_int, hstep_bound⟩ :=
        quarticCoreTrunc_step β D t A n hβ ht hsmall ih.1 (by simpa [A] using ih.2)
      refine ⟨hstep_int, ?_⟩
      have hA :
          (Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat)) * gaussianF n t) * A
            =
          Real.exp ((β ^ (2 : Nat) / 2) * ((n + 1 : ℕ) : ℝ) * (D / t) ^ (2 : Nat))
            * gaussianF (dim (n + 1)) t := by
        dsimp [A]
        have hexp :
            Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat))
                * Real.exp ((β ^ (2 : Nat) / 2) * (n : ℝ) * (D / t) ^ (2 : Nat))
              =
            Real.exp ((β ^ (2 : Nat) / 2) * ((n + 1 : ℕ) : ℝ) * (D / t) ^ (2 : Nat)) := by
          rw [← Real.exp_add]
          congr 1
          norm_num [Nat.cast_add]
          ring
        calc
          (Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat)) * gaussianF n t)
              * (Real.exp ((β ^ (2 : Nat) / 2) * (n : ℝ) * (D / t) ^ (2 : Nat))
                  * gaussianF (dim n) t)
              =
                (Real.exp ((β ^ (2 : Nat) / 2) * (D / t) ^ (2 : Nat))
                    * Real.exp ((β ^ (2 : Nat) / 2) * (n : ℝ) * (D / t) ^ (2 : Nat)))
                  * (gaussianF n t * gaussianF (dim n) t) := by
                    ring
          _ =
                Real.exp ((β ^ (2 : Nat) / 2) * ((n + 1 : ℕ) : ℝ) * (D / t) ^ (2 : Nat))
                  * gaussianF (n + dim n) t := by
                    rw [hexp, gaussianF_mul n (dim n) t ht]
          _ =
                Real.exp ((β ^ (2 : Nat) / 2) * ((n + 1 : ℕ) : ℝ) * (D / t) ^ (2 : Nat))
                  * gaussianF (dim (n + 1)) t := by
                    rw [dim_succ]
                    simp [Nat.add_comm]
      simpa [hA] using hstep_bound

/-- Uniform quartic-core bound on the geometric edge core region.

This upgrades `quarticCoreTrunc_bound` from the peeled Gaussian model to the
actual edge-core integral used in the local-gap bridge. -/
theorem quartic_exponential_core_bound
    (β : ℝ) (hβ : 0 < β) :
    ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧
      ∀ n : ℕ, ∀ t : ℝ, 0 < t →
        (dim n : ℝ) / t ≤ c₁ →
        (n : ℝ) * (dim n : ℝ) ^ (2 : Nat) / t ^ (2 : Nat) ≤ c₁ →
        ∫ mu in edgeCoreRegion n t,
          Real.exp (β * t * quarticCorr n (matrixOfEdge n mu))
            * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
          ≤ C₁ * coreMass (dim n) t := by
  obtain ⟨Ccore, hCcore_pos, hcore⟩ := gaussianF_le_const_mul_coreMass
  let c₁ : ℝ := min (1 / (2 * β)) 1
  let baseC : ℝ := Real.exp ((β ^ (2 : Nat) / 2) * c₁) * Ccore
  let C₁ : ℝ := max 1 baseC
  refine ⟨c₁, C₁, ?_, ?_, ?_⟩
  · dsimp [c₁]
    positivity
  · dsimp [C₁]
    positivity [hCcore_pos]
  · intro n t ht hdim hcube
    have hsmall : β * ((dim n : ℝ) / t) ≤ 1 / 2 := by
      have hdim' : (dim n : ℝ) / t ≤ 1 / (2 * β) := le_trans hdim (min_le_left _ _)
      have hmul := mul_le_mul_of_nonneg_left hdim' (le_of_lt hβ)
      have hhalf : β * (1 / (2 * β)) = (1 / 2 : ℝ) := by
        field_simp [hβ.ne']
      rw [hhalf] at hmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    have hset : edgeCoreRegionD n (dim n : ℝ) t = edgeCoreRegion n t := by
      ext mu
      simp [edgeCoreRegionD, edgeCoreRegion, coreRegion, sNorm_matrixOfEdge_eq]
    have hcube' :
        (n : ℝ) * ((dim n : ℝ) / t) ^ (2 : Nat) ≤ c₁ := by
      have ht_ne : t ≠ 0 := ne_of_gt ht
      dsimp [c₁] at hcube ⊢
      field_simp [pow_two, ht_ne] at hcube ⊢
      linarith
    have hmain :
        ∫ mu : Cn3Torus.Edge n → ℝ,
          (edgeCoreRegion n t).indicator (quarticCoreDensity β t n) mu
        ≤ C₁ * coreMass (dim n) t := by
      by_cases hdim1 : 1 ≤ dim n
      · have hbound :=
          (quarticCoreTrunc_bound β (dim n : ℝ) t hβ.le (by positivity) ht hsmall n).2
        have hexp_le :
            Real.exp ((β ^ (2 : Nat) / 2) * (n : ℝ) * ((dim n : ℝ) / t) ^ (2 : Nat))
              ≤ Real.exp ((β ^ (2 : Nat) / 2) * c₁) := by
          apply Real.exp_le_exp.mpr
          have hcoef_nonneg : 0 ≤ β ^ (2 : Nat) / 2 := by positivity
          have hmul :
              (β ^ (2 : Nat) / 2) * ((n : ℝ) * ((dim n : ℝ) / t) ^ (2 : Nat))
                ≤ (β ^ (2 : Nat) / 2) * c₁ :=
            mul_le_mul_of_nonneg_left hcube' hcoef_nonneg
          simpa [mul_assoc] using hmul
        have hdim_one : (dim n : ℝ) / t ≤ 1 := le_trans hdim (min_le_right _ _)
        have hdim1R : (1 : ℝ) ≤ dim n := by exact_mod_cast hdim1
        have ht_one : 1 ≤ t := by
          have hmul : (dim n : ℝ) ≤ t := by
            have ht_ne : t ≠ 0 := ne_of_gt ht
            have htmp := hdim_one
            field_simp [ht_ne] at htmp
            linarith
          nlinarith
        have hgauss_le :
            gaussianF (dim n) t ≤ Ccore * coreMass (dim n) t :=
          hcore (dim n) t hdim1 ht_one
        have hgauss_nonneg : 0 ≤ gaussianF (dim n) t := by
          unfold gaussianF
          positivity [Real.pi_pos, ht]
        have hcoreMass_nonneg : 0 ≤ coreMass (dim n) t := by
          unfold coreMass
          refine MeasureTheory.integral_nonneg_of_ae ?_
          exact Filter.Eventually.of_forall (fun x => by
            by_cases hx : ∑ i : Fin (dim n), x i ^ (2 : Nat) ≤ (dim n : ℝ) / t
            · simp [hx]
              positivity
            · simp [hx])
        rw [← hset]
        calc
          ∫ mu : Cn3Torus.Edge n → ℝ, quarticCoreTrunc β (dim n : ℝ) t n mu
              ≤ Real.exp ((β ^ (2 : Nat) / 2) * (n : ℝ) * ((dim n : ℝ) / t) ^ (2 : Nat))
                  * gaussianF (dim n) t := by
                    simpa [quarticCoreTrunc] using hbound
          _ ≤ Real.exp ((β ^ (2 : Nat) / 2) * c₁) * gaussianF (dim n) t := by
                exact mul_le_mul_of_nonneg_right hexp_le hgauss_nonneg
          _ ≤ Real.exp ((β ^ (2 : Nat) / 2) * c₁) * (Ccore * coreMass (dim n) t) := by
                exact mul_le_mul_of_nonneg_left hgauss_le (by positivity)
          _ = baseC * coreMass (dim n) t := by
                dsimp [baseC]
                ring
          _ ≤ C₁ * coreMass (dim n) t := by
                dsimp [C₁]
                exact mul_le_mul_of_nonneg_right (le_max_right _ _) hcoreMass_nonneg
      · have hdim0 : dim n = 0 := by
          omega
        have hbound :=
          (quarticCoreTrunc_bound β (dim n : ℝ) t hβ.le (by positivity) ht hsmall n).2
        have hcore_zero : coreMass (dim n) t = 1 := by
          rw [hdim0]
          convert gaussian_integral_formula 0 (2 * t) (by positivity) using 1
          · simp [coreMass]
          · simp
        have hbase :
            ∫ mu : Cn3Torus.Edge n → ℝ, quarticCoreTrunc β (dim n : ℝ) t n mu ≤ 1 := by
          simpa [hdim0, gaussianF] using hbound
        rw [← hset, hcore_zero]
        have hC₁_ge_one : 1 ≤ C₁ := by
          dsimp [C₁]
          exact le_max_left _ _
        have hC₁_ge_one' : 1 ≤ C₁ * 1 := by
          simpa using hC₁_ge_one
        exact le_trans hbase hC₁_ge_one'
    have hs_meas : MeasurableSet (edgeCoreRegion n t) := by
      rw [← hset]
      exact measurableSet_edgeCoreRegionD n (dim n : ℝ) t
    calc
      ∫ mu in edgeCoreRegion n t,
          Real.exp (β * t * quarticCorr n (matrixOfEdge n mu))
            * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
          = ∫ mu : Cn3Torus.Edge n → ℝ,
              Set.indicator (edgeCoreRegion n t) (quarticCoreDensity β t n) mu := by
                symm
                simpa [quarticCoreDensity] using
                  (MeasureTheory.integral_indicator (μ := MeasureTheory.volume)
                    (f := quarticCoreDensity β t n) hs_meas)
      _ ≤ C₁ * coreMass (dim n) t := hmain
