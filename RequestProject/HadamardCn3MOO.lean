import RequestProject.HadamardCn3DiscreteMoments

/-!
# MOO / Influence Layer For The Cn^3 Formalization

This module contains the influence statistics and the base analytic estimates
that feed the weak invariance theorem based on the
Mossel-O'Donnell-Oleszkiewicz invariance principle.

Here `MOO` abbreviates Mossel, O'Donnell, and Oleszkiewicz; see
"Noise stability of functions with low influences: Invariance and optimality",
Annals of Mathematics 171 (2010), 295-341.

The public objects here are the influence quantities used in the comparison
theorems:

- `rowInfluence`
- `threeHalfInfluenceSum`
- `mooKernel`
- `paperThreeHalfInfluenceSum`

The reusable discrete sign-moment machinery now lives in
`RequestProject.HadamardCn3DiscreteMoments`.
-/

noncomputable section

open Real MeasureTheory Filter Finset Topology
open scoped Pointwise

set_option linter.unusedVariables false

/-!
## Influence Quantities
These definitions give the matrix and edge-coordinate influence statistics that
feed into the weak invariance estimates and the final
`threeHalfInfluenceSum` bounds.
-/

/-- The max influence I_max(λ) = max_k Σ_{i≠k} λ_{ik}². -/
def maxInfluence (n : ℕ) (lam : Fin n → Fin n → ℝ) : ℝ :=
  if h : 0 < n then
    Finset.univ.sup' ⟨⟨0, h⟩, Finset.mem_univ _⟩
      (fun k : Fin n => ∑ i : Fin n, if i ≠ k then lam (min i k) (max i k) ^ 2 else 0)
  else 0

/-- Row influence `I_k(λ) = Σ_{i≠k} λ_{ik}²`. -/
def rowInfluence (n : ℕ) (lam : Fin n → Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ i : Fin n, if i ≠ k then lam (min i k) (max i k) ^ 2 else 0

/-- The `ℓ^{3/2}`-row statistic `J(λ) = Σ_k I_k(λ)^{3/2}`, written using `sqrt`. -/
def threeHalfInfluenceSum (n : ℕ) (lam : Fin n → Fin n → ℝ) : ℝ :=
  ∑ k : Fin n, rowInfluence n lam k * Real.sqrt (rowInfluence n lam k)

lemma rowInfluence_nonneg (n : ℕ) (lam : Fin n → Fin n → ℝ) (k : Fin n) :
    0 ≤ rowInfluence n lam k := by
  unfold rowInfluence
  exact Finset.sum_nonneg (fun i hi => by split_ifs <;> positivity)

lemma exists_rowInfluence_eq_maxInfluence
    (n : ℕ) (hn : 0 < n) (lam : Fin n → Fin n → ℝ) :
    ∃ k : Fin n, rowInfluence n lam k = maxInfluence n lam := by
  rw [maxInfluence, dif_pos hn]
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin n)))
    (H := ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
    (f := fun k : Fin n => rowInfluence n lam k)
  exact ⟨k, hk.symm⟩

lemma le_of_mul_sqrt_le_mul_sqrt {x y : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x * Real.sqrt x ≤ y * Real.sqrt y) :
    x ≤ y := by
  by_contra h
  have hyx : y < x := lt_of_not_ge h
  have hx_pos : 0 < x := lt_of_le_of_lt hy hyx
  have hsqrt_le : Real.sqrt y ≤ Real.sqrt x := Real.sqrt_le_sqrt hyx.le
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
  have h1 : y * Real.sqrt y ≤ y * Real.sqrt x := by
    exact mul_le_mul_of_nonneg_left hsqrt_le hy
  have h2 : y * Real.sqrt x < x * Real.sqrt x := by
    exact mul_lt_mul_of_pos_right hyx hsqrt_pos
  exact not_lt_of_ge hxy (lt_of_le_of_lt h1 h2)

private lemma threeHalfInfluenceSum_le_card_mul_maxInfluence
    (n : ℕ) (hn : 0 < n) (lam : Fin n → Fin n → ℝ) :
    threeHalfInfluenceSum n lam
      ≤ (n : ℝ) * (maxInfluence n lam * Real.sqrt (maxInfluence n lam)) := by
  have hmax_nonneg : 0 ≤ maxInfluence n lam := by
    have hrow_le : rowInfluence n lam ⟨0, hn⟩ ≤ maxInfluence n lam := by
      rw [maxInfluence, dif_pos hn]
      exact Finset.le_sup' (s := (Finset.univ : Finset (Fin n)))
        (f := fun k : Fin n => rowInfluence n lam k)
        (Finset.mem_univ _)
    exact le_trans (rowInfluence_nonneg n lam ⟨0, hn⟩) hrow_le
  calc
    threeHalfInfluenceSum n lam
      = ∑ k : Fin n, rowInfluence n lam k * Real.sqrt (rowInfluence n lam k) := by
          rfl
    _ ≤ ∑ k : Fin n, maxInfluence n lam * Real.sqrt (maxInfluence n lam) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          have hrow_le : rowInfluence n lam k ≤ maxInfluence n lam := by
            rw [maxInfluence, dif_pos hn]
            exact Finset.le_sup' (s := (Finset.univ : Finset (Fin n)))
              (f := fun j : Fin n => rowInfluence n lam j)
              (Finset.mem_univ k)
          have hrow_nonneg : 0 ≤ rowInfluence n lam k := rowInfluence_nonneg n lam k
          have hsqrt_le : Real.sqrt (rowInfluence n lam k) ≤ Real.sqrt (maxInfluence n lam) :=
            Real.sqrt_le_sqrt hrow_le
          calc
            rowInfluence n lam k * Real.sqrt (rowInfluence n lam k)
              ≤ rowInfluence n lam k * Real.sqrt (maxInfluence n lam) := by
                  exact mul_le_mul_of_nonneg_left hsqrt_le hrow_nonneg
            _ ≤ maxInfluence n lam * Real.sqrt (maxInfluence n lam) := by
                  exact mul_le_mul_of_nonneg_right hrow_le (Real.sqrt_nonneg _)
    _ = (n : ℝ) * (maxInfluence n lam * Real.sqrt (maxInfluence n lam)) := by
          simp

/-- Ordered-sum quadratic form in Rademacher variables. This matches the normalization used in the
manuscript's degree-`2` invariance principle. -/
def Q2Signs (n : ℕ) (f : Fin n → Fin n → ℝ) (σ : Fin n → Fin 2) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, f i j * (((signOf (σ i) : ℤ) : ℝ)) * (((signOf (σ j) : ℤ) : ℝ))

/-- Ordered-sum quadratic form in Gaussian variables. This matches the normalization used in the
manuscript's degree-`2` invariance principle. -/
def Q2Gauss (n : ℕ) (f : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, f i j * x i * x j

/-- Row influence for the ordered-sum kernel formulation of the degree-`2` invariance principle. -/
def kernelInfluence (n : ℕ) (f : Fin n → Fin n → ℝ) (k : Fin n) : ℝ :=
  ∑ j : Fin n, f k j ^ (2 : Nat)

/-- The symmetric kernel attached to `lam` in the manuscript normalization. -/
def mooKernel (n : ℕ) (lam : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if i = j then 0 else lam (min i j) (max i j) / 2

lemma mooKernel_symm (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    ∀ i j, mooKernel n lam i j = mooKernel n lam j i := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [mooKernel]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [mooKernel, hij, hji, min_comm, max_comm]

lemma mooKernel_diag (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    ∀ i, mooKernel n lam i i = 0 := by
  intro i
  simp [mooKernel]

private lemma q2_mooKernel_eq_upper (n : ℕ) (lam : Fin n → Fin n → ℝ) (α : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, mooKernel n lam i j * α i * α j)
      =
    ∑ i : Fin n, ∑ j : Fin n, if i < j then lam i j * α i * α j else 0 := by
  have hsplit :
      ∀ i j : Fin n,
        mooKernel n lam i j * α i * α j
          =
        (if i < j then (lam i j / 2) * α i * α j else 0)
          +
        (if j < i then (lam j i / 2) * α i * α j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · have hijne : i ≠ j := ne_of_lt hij
      have hnotji : ¬ j < i := not_lt_of_ge (le_of_lt hij)
      calc
        mooKernel n lam i j * α i * α j = (lam i j / 2) * α i * α j := by
          simp [mooKernel, hijne, min_eq_left (le_of_lt hij), max_eq_right (le_of_lt hij)]
        _ =
            (if i < j then (lam i j / 2) * α i * α j else 0)
              + (if j < i then (lam j i / 2) * α i * α j else 0) := by
                simp [hij, hnotji]
    · simp [mooKernel]
    · have hijne : i ≠ j := ne_of_gt hji
      have hnotij : ¬ i < j := not_lt_of_ge (le_of_lt hji)
      calc
        mooKernel n lam i j * α i * α j = (lam j i / 2) * α i * α j := by
          simp [mooKernel, hijne, min_eq_right (le_of_lt hji), max_eq_left (le_of_lt hji)]
        _ =
            (if i < j then (lam i j / 2) * α i * α j else 0)
              + (if j < i then (lam j i / 2) * α i * α j else 0) := by
                simp [hji, hnotij]
  have hswap :
      (∑ i : Fin n, ∑ j : Fin n, if j < i then (lam j i / 2) * α i * α j else 0)
        =
      (∑ i : Fin n, ∑ j : Fin n, if i < j then (lam i j / 2) * α i * α j else 0) := by
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    refine Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n)) _ _ ?_
    intro p
    rcases p with ⟨i, j⟩
    simp [mul_left_comm, mul_comm]
  calc
    (∑ i : Fin n, ∑ j : Fin n, mooKernel n lam i j * α i * α j)
      =
        ∑ i : Fin n, ∑ j : Fin n,
          ((if i < j then (lam i j / 2) * α i * α j else 0)
            + (if j < i then (lam j i / 2) * α i * α j else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              exact hsplit i j
    _ =
        (∑ i : Fin n, ∑ j : Fin n, if i < j then (lam i j / 2) * α i * α j else 0)
          +
        (∑ i : Fin n, ∑ j : Fin n, if j < i then (lam j i / 2) * α i * α j else 0) := by
              simp_rw [Finset.sum_add_distrib]
    _ =
        ∑ i : Fin n, ∑ j : Fin n,
          ((if i < j then (lam i j / 2) * α i * α j else 0)
            + (if i < j then (lam i j / 2) * α i * α j else 0)) := by
              rw [hswap]
              rw [← Finset.sum_add_distrib]
              simp_rw [← Finset.sum_add_distrib]
    _ =
        ∑ i : Fin n, ∑ j : Fin n, if i < j then lam i j * α i * α j else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              by_cases hij : i < j
              · simp [hij]
                ring
              · simp [hij]

lemma q2Gauss_mooKernel_eq_gaussianInnerX
    (n : ℕ) (lam : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    Q2Gauss n (mooKernel n lam) x = gaussianInnerX n lam x := by
  unfold Q2Gauss gaussianInnerX
  simpa using q2_mooKernel_eq_upper n lam x

lemma q2Signs_mooKernel_eq_innerX
    (n : ℕ) (lam : Fin n → Fin n → ℝ) (σ : Fin n → Fin 2) :
    Q2Signs n (mooKernel n lam) σ = innerX n lam σ := by
  unfold Q2Signs innerX
  simpa using q2_mooKernel_eq_upper n lam (fun i => (((signOf (σ i) : ℤ) : ℝ)))

lemma kernelInfluence_mooKernel
    (n : ℕ) (lam : Fin n → Fin n → ℝ) (k : Fin n) :
    kernelInfluence n (mooKernel n lam) k
      =
    (1 / 4 : ℝ) * ∑ i : Fin n,
      if i ≠ k then lam (min i k) (max i k) ^ (2 : Nat) else 0 := by
  unfold kernelInfluence
  calc
    ∑ j : Fin n, mooKernel n lam k j ^ (2 : Nat)
      = ∑ j : Fin n, (1 / 4 : ℝ) * (if j ≠ k then lam (min j k) (max j k) ^ (2 : Nat) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          by_cases hjk : j = k
          · simp [mooKernel, hjk]
          · have hkj : k ≠ j := fun h => hjk h.symm
            calc
              mooKernel n lam k j ^ (2 : Nat)
                = (lam (min j k) (max j k) / 2) ^ (2 : Nat) := by
                    simp [mooKernel, hjk, hkj, min_comm, max_comm]
              _ = (1 / 4 : ℝ) * (if j ≠ k then lam (min j k) (max j k) ^ (2 : Nat) else 0) := by
                    simp [hjk]
                    ring
    _ = (1 / 4 : ℝ) * ∑ j : Fin n, if j ≠ k then lam (min j k) (max j k) ^ (2 : Nat) else 0 := by
          rw [← Finset.mul_sum]

lemma maxInfluence_nonneg (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    0 ≤ maxInfluence n lam := by
  unfold maxInfluence
  split_ifs with h
  · let k : Fin n := ⟨0, h⟩
    have hrow_nonneg :
        0 ≤ ∑ i : Fin n, if i ≠ k then lam (min i k) (max i k) ^ (2 : Nat) else 0 := by
          exact Finset.sum_nonneg (fun i hi => by split_ifs <;> positivity)
    have hk : k ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
    have hs :
        (∑ i : Fin n, if i ≠ k then lam (min i k) (max i k) ^ (2 : Nat) else 0)
          ≤
        Finset.univ.sup' ⟨k, hk⟩
          (fun k : Fin n => ∑ i : Fin n, if i ≠ k then lam (min i k) (max i k) ^ (2 : Nat) else 0) :=
      Finset.le_sup' (s := (Finset.univ : Finset (Fin n)))
        (f := fun k : Fin n => ∑ i : Fin n, if i ≠ k then lam (min i k) (max i k) ^ (2 : Nat) else 0)
        hk
    exact le_trans hrow_nonneg hs
  · simp

/-- Edge-coordinate row influence, transported from the matrix model. -/
def rowInfluenceEdge (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) (k : Fin n) : ℝ :=
  rowInfluence n (matrixOfEdge n mu) k

/-- Edge-coordinate maximal row influence. -/
def rowInfluenceMaxEdge (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) : ℝ :=
  maxInfluence n (matrixOfEdge n mu)

/-- Edge-coordinate `ℓ^{3/2}` row statistic. -/
def threeHalfInfluenceSumEdge (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) : ℝ :=
  threeHalfInfluenceSum n (matrixOfEdge n mu)

lemma rowInfluenceEdge_eq (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) (k : Fin n) :
    rowInfluenceEdge n mu k = rowInfluence n (matrixOfEdge n mu) k := rfl

lemma rowInfluenceMaxEdge_eq (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    rowInfluenceMaxEdge n mu = maxInfluence n (matrixOfEdge n mu) := rfl

lemma threeHalfInfluenceSumEdge_eq (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    threeHalfInfluenceSumEdge n mu = threeHalfInfluenceSum n (matrixOfEdge n mu) := rfl

lemma threeHalfInfluenceSumEdge_le_card_mul_maxInfluence
    (n : ℕ) (hn : 0 < n) (mu : Cn3Torus.Edge n → ℝ) :
    threeHalfInfluenceSumEdge n mu
      ≤ (n : ℝ) * (rowInfluenceMaxEdge n mu * Real.sqrt (rowInfluenceMaxEdge n mu)) := by
  simpa [threeHalfInfluenceSumEdge, rowInfluenceMaxEdge] using
    threeHalfInfluenceSum_le_card_mul_maxInfluence n hn (matrixOfEdge n mu)

/-- The Gaussian characteristic-function bound used after the MOO comparison:
`|ψ_G(λ)| ≤ (1 + 2 sNorm(λ))^{-1/4}`. This is the separate Gaussian calculation
from the text, distinct from the invariance-principle input. -/
theorem gaussianPsi_norm_bound (n : ℕ) (lam : Fin n → Fin n → ℝ) :
  ‖gaussianPsi n lam‖ ≤ (1 + 2 * sNorm n lam) ^ (-(1 : ℝ) / 4) := by
  classical
  rw [gaussianPsi_eq_gaussianPsiComplex]
  let M : Matrix (Fin n) (Fin n) ℝ := gaussianMatrix n lam
  let hHerm : M.IsHermitian := gaussianMatrix_isHermitian n lam
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := Matrix.toEuclideanLin M
  let hSymm : T.IsSymmetric := (Matrix.isHermitian_iff_isSymmetric (A := M)).1 hHerm
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    hSymm.eigenvectorBasis finrank_euclideanSpace_fin
  let μ : Fin n → ℝ := hSymm.eigenvalues finrank_euclideanSpace_fin
  let e : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).trans
      ((b.repr.toHomeomorph.toMeasurableEquiv).trans
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm)
  let xOf : (Fin n → ℝ) → (Fin n → ℝ) := fun y => WithLp.ofLp (b.repr.symm (WithLp.toLp 2 y))
  let β : Fin n → ℂ := fun i => (((1 : ℂ) - (μ i : ℂ) * Complex.I) / 2)
  have he_mp : MeasureTheory.MeasurePreserving e.symm MeasureTheory.volume MeasureTheory.volume := by
    dsimp [e]
    exact (PiLp.volume_preserving_ofLp (Fin n)).comp
      (b.measurePreserving_repr_symm.comp (PiLp.volume_preserving_toLp (Fin n)))
  have hsum_sq : ∀ y : Fin n → ℝ, ∑ i : Fin n, (xOf y i) ^ (2 : Nat) = ∑ i : Fin n, y i ^ (2 : Nat) := by
    intro y
    have hcoord : WithLp.toLp 2 (xOf y) = b.repr.symm (WithLp.toLp 2 y) := by
      rfl
    calc
      ∑ i : Fin n, (xOf y i) ^ (2 : Nat)
          = ‖WithLp.toLp 2 (xOf y)‖ ^ (2 : Nat) := by
              symm
              simpa [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 (xOf y)))
      _ = ‖b.repr.symm (WithLp.toLp 2 y)‖ ^ (2 : Nat) := by rw [hcoord]
      _ = ‖WithLp.toLp 2 y‖ ^ (2 : Nat) := by simp
      _ = ∑ i : Fin n, y i ^ (2 : Nat) := by
            simpa [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq (WithLp.toLp 2 y))
  have hTdiag :
      ∀ y : Fin n → ℝ,
        T (b.repr.symm (WithLp.toLp 2 y)) = b.repr.symm (WithLp.toLp 2 fun i => μ i * y i) := by
    intro y
    calc
      T (b.repr.symm (WithLp.toLp 2 y)) = T (∑ i : Fin n, y i • b i) := by
        congr 1
        symm
        simpa using (OrthonormalBasis.sum_repr_symm b (WithLp.toLp 2 y))
      _ = ∑ i : Fin n, y i • T (b i) := by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [map_smul]
      _ = ∑ i : Fin n, y i • (μ i • b i) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simpa [μ, b] using
          congrArg (fun v => y i • v)
            (hSymm.apply_eigenvectorBasis finrank_euclideanSpace_fin i)
      _ = ∑ i : Fin n, (μ i * y i) • b i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
      _ = b.repr.symm (WithLp.toLp 2 fun i => μ i * y i) := by
        simpa using (OrthonormalBasis.sum_repr_symm b (WithLp.toLp 2 fun i => μ i * y i))
  have hquad :
      ∀ y : Fin n → ℝ, gaussianInnerX n lam (xOf y) = (1 / 2 : ℝ) * ∑ i : Fin n, μ i * y i ^ (2 : Nat) := by
    intro y
    have hcoord : WithLp.toLp 2 (xOf y) = b.repr.symm (WithLp.toLp 2 y) := by
      rfl
    calc
      gaussianInnerX n lam (xOf y)
          = (1 / 2 : ℝ) *
              inner ℝ (WithLp.toLp 2 (xOf y))
                (Matrix.toEuclideanLin (gaussianMatrix n lam) (WithLp.toLp 2 (xOf y))) := by
                  simpa using gaussianInnerX_eq_half_inner_toEuclideanLin n lam (xOf y)
      _ = (1 / 2 : ℝ) *
            inner ℝ (b.repr.symm (WithLp.toLp 2 y))
              (T (b.repr.symm (WithLp.toLp 2 y))) := by
                simp [hcoord, M, T]
      _ = (1 / 2 : ℝ) *
            inner ℝ (b.repr.symm (WithLp.toLp 2 y))
              (b.repr.symm (WithLp.toLp 2 fun i => μ i * y i)) := by
                rw [hTdiag]
      _ = (1 / 2 : ℝ) *
            inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 fun i => μ i * y i) := by
              simpa using
                (b.repr.inner_map_map
                  (b.repr.symm (WithLp.toLp 2 y))
                  (b.repr.symm (WithLp.toLp 2 fun i => μ i * y i))).symm
      _ = (1 / 2 : ℝ) * ∑ i : Fin n, μ i * y i ^ (2 : Nat) := by
            simp [PiLp.inner_apply, RCLike.inner_apply, dotProduct, pow_two, mul_assoc, mul_left_comm, mul_comm]
  have hdiag_integrand :
      ∀ y : Fin n → ℝ,
        gaussianPsiIntegrand n lam (xOf y)
          = Complex.exp (-∑ i : Fin n, β i * (y i : ℂ) ^ (2 : Nat)) := by
    intro y
    let a : Fin n → ℝ := fun i => μ i * y i ^ (2 : Nat)
    unfold gaussianPsiIntegrand
    rw [hsum_sq y, hquad y]
    congr 1
    have hs1 :
        ((((-∑ i : Fin n, y i ^ (2 : Nat)) / 2 : ℝ) : ℂ))
          = ∑ i : Fin n, (((-(y i ^ (2 : Nat)) / 2 : ℝ) : ℂ)) := by
      calc
        ((((-∑ i : Fin n, y i ^ (2 : Nat)) / 2 : ℝ) : ℂ))
            = (((∑ i : Fin n, (-y i ^ (2 : Nat)) * (1 / 2 : ℝ) : ℝ)) : ℂ) := by
                congr 1
                rw [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.sum_neg_distrib]
                norm_num
        _ = ∑ i : Fin n, ((((-y i ^ (2 : Nat)) * (1 / 2 : ℝ) : ℝ) : ℂ)) := by
              simp
        _ = ∑ i : Fin n, (((-(y i ^ (2 : Nat)) / 2 : ℝ) : ℂ)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
    have hs2 :
        ((((1 / 2 : ℝ) * ∑ i : Fin n, a i : ℝ) : ℂ) * Complex.I)
          = ∑ i : Fin n, ((((a i) / 2 : ℝ) : ℂ) * Complex.I) := by
      calc
        ((((1 / 2 : ℝ) * ∑ i : Fin n, a i : ℝ) : ℂ) * Complex.I)
            = ((((∑ i : Fin n, (1 / 2 : ℝ) * a i : ℝ)) : ℂ) * Complex.I) := by
                congr 2
                rw [Finset.mul_sum]
        _ = (∑ i : Fin n, (((1 / 2 : ℝ) * a i : ℂ)) ) * Complex.I := by
              simp
        _ = ∑ i : Fin n, ((((1 / 2 : ℝ) * a i : ℂ)) * Complex.I) := by
              rw [Finset.sum_mul]
        _ = ∑ i : Fin n, ((((a i) / 2 : ℝ) : ℂ) * Complex.I) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa [div_eq_mul_inv, mul_comm]
    rw [hs1, hs2]
    rw [← Finset.sum_add_distrib]
    calc
      ∑ i : Fin n, (((-(y i ^ (2 : Nat)) / 2 : ℝ) : ℂ) + ((((a i) / 2 : ℝ) : ℂ) * Complex.I))
          = ∑ i : Fin n, -(β i * (y i : ℂ) ^ (2 : Nat)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              dsimp [a, β]
              norm_num [pow_two, div_eq_mul_inv]
              ring
      _ = -∑ i : Fin n, β i * (y i : ℂ) ^ (2 : Nat) := by
            rw [Finset.sum_neg_distrib]
  have htransport :
      ∫ x : Fin n → ℝ, gaussianPsiIntegrand n lam x
        = ∫ y : Fin n → ℝ, Complex.exp (-∑ i : Fin n, β i * (y i : ℂ) ^ (2 : Nat)) := by
    have hcomp :=
      MeasureTheory.MeasurePreserving.integral_comp he_mp e.symm.measurableEmbedding
        (gaussianPsiIntegrand n lam)
    calc
      ∫ x : Fin n → ℝ, gaussianPsiIntegrand n lam x
          = ∫ y : Fin n → ℝ, gaussianPsiIntegrand n lam (xOf y) := by
              symm
              simpa [xOf, e] using hcomp
      _ = ∫ y : Fin n → ℝ, Complex.exp (-∑ i : Fin n, β i * (y i : ℂ) ^ (2 : Nat)) := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall hdiag_integrand
  have hbeta_pos : ∀ i : Fin n, 0 < (β i).re := by
    intro i
    simp [β]
  have hgauss :
      ∫ y : Fin n → ℝ, Complex.exp (-∑ i : Fin n, β i * (y i : ℂ) ^ (2 : Nat))
        = ∏ i : Fin n, (((Real.pi : ℂ) / β i) ^ ((1 / 2 : ℝ) : ℂ)) := by
    simpa using
      (GaussianFourier.integral_cexp_neg_sum_mul_add (ι := Fin n) (b := β) hbeta_pos (fun _ => (0 : ℂ)))
  have hformula :
      gaussianPsiComplex n lam
        = (∏ i : Fin n, (((Real.pi : ℂ) / β i) ^ ((1 / 2 : ℝ) : ℂ))) /
            ((((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)) := by
    unfold gaussianPsiComplex
    rw [htransport, hgauss]
  have hfacnorm :
      ∀ i : Fin n,
        ‖(((Real.pi : ℂ) / β i) ^ ((1 / 2 : ℝ) : ℂ))‖
          = Real.sqrt (2 * Real.pi) * (1 + μ i ^ (2 : Nat)) ^ (-(1 : ℝ) / 4) := by
    intro i
    have hβnorm : ‖β i‖ = Real.sqrt (1 + μ i ^ (2 : Nat)) / 2 := by
      have hnormsq :
          Complex.normSq ((1 : ℂ) - (μ i : ℂ) * Complex.I) = 1 + μ i ^ (2 : Nat) := by
        simpa [sub_eq_add_neg, pow_two] using (Complex.normSq_add_mul_I (1 : ℝ) (-μ i))
      dsimp [β]
      rw [norm_div, Complex.norm_def, hnormsq]
      norm_num [Complex.norm_real, Real.norm_eq_abs]
    have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + μ i ^ (2 : Nat)) := Real.sqrt_nonneg _
    have hbase_nonneg : 0 ≤ 1 + μ i ^ (2 : Nat) := by positivity
    calc
      ‖(((Real.pi : ℂ) / β i) ^ ((1 / 2 : ℝ) : ℂ))‖
          = ‖((Real.pi : ℂ) / β i)‖ ^ (1 / 2 : ℝ) := by
              rw [Complex.norm_cpow_real]
      _ = (Real.pi / ‖β i‖) ^ (1 / 2 : ℝ) := by
            rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      _ = ((2 * Real.pi) / Real.sqrt (1 + μ i ^ (2 : Nat))) ^ (1 / 2 : ℝ) := by
            rw [hβnorm]
            field_simp [Real.sqrt_ne_zero'.2 (by positivity : 0 < Real.sqrt (1 + μ i ^ (2 : Nat)))]
      _ = (2 * Real.pi) ^ (1 / 2 : ℝ) / (Real.sqrt (1 + μ i ^ (2 : Nat))) ^ (1 / 2 : ℝ) := by
            rw [Real.div_rpow (by positivity) hsqrt_nonneg]
      _ = Real.sqrt (2 * Real.pi) / (1 + μ i ^ (2 : Nat)) ^ (1 / 4 : ℝ) := by
            rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
            rw [← Real.rpow_mul hbase_nonneg]
            norm_num
      _ = Real.sqrt (2 * Real.pi) * (1 + μ i ^ (2 : Nat)) ^ (-(1 : ℝ) / 4) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg hbase_nonneg]
            ring_nf
  have hsqrt_prod :
      (∏ _i : Fin n, Real.sqrt (2 * Real.pi)) = (2 * Real.pi) ^ ((n : ℝ) / 2) := by
    calc
      ∏ _i : Fin n, Real.sqrt (2 * Real.pi)
          = ∏ i : Fin n, (2 * Real.pi) ^ (1 / 2 : ℝ) := by
              simp [Real.sqrt_eq_rpow]
      _ = (∏ i : Fin n, (2 * Real.pi)) ^ (1 / 2 : ℝ) := by
            simpa using
              (Real.finset_prod_rpow Finset.univ (fun _ : Fin n => 2 * Real.pi)
                (by
                  intro i hi
                  positivity)
                (1 / 2 : ℝ))
      _ = (((2 * Real.pi : ℝ) ^ n)) ^ (1 / 2 : ℝ) := by
            simp [Finset.prod_const]
      _ = (2 * Real.pi) ^ ((n : ℝ) / 2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ 2 * Real.pi)]
            congr 1
            ring
  have hnorm_eq :
      ‖gaussianPsiComplex n lam‖ = ∏ i : Fin n, (1 + μ i ^ (2 : Nat)) ^ (-(1 : ℝ) / 4) := by
    have hden_pos : 0 < (2 * Real.pi) ^ ((n : ℝ) / 2) := by positivity
    calc
      ‖gaussianPsiComplex n lam‖
          = ‖(∏ i : Fin n, (((Real.pi : ℂ) / β i) ^ ((1 / 2 : ℝ) : ℂ))) /
              ((((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ))‖ := by
                rw [hformula]
      _ = ‖∏ i : Fin n, (((Real.pi : ℂ) / β i) ^ ((1 / 2 : ℝ) : ℂ))‖ /
            (2 * Real.pi) ^ ((n : ℝ) / 2) := by
              rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden_pos]
      _ = (∏ i : Fin n, ‖(((Real.pi : ℂ) / β i) ^ ((1 / 2 : ℝ) : ℂ))‖) /
            (2 * Real.pi) ^ ((n : ℝ) / 2) := by
              rw [norm_prod]
      _ = (∏ i : Fin n,
              Real.sqrt (2 * Real.pi) * (1 + μ i ^ (2 : Nat)) ^ (-(1 : ℝ) / 4)) /
            (2 * Real.pi) ^ ((n : ℝ) / 2) := by
              congr 1
              refine Finset.prod_congr rfl ?_
              intro i hi
              exact hfacnorm i
      _ = ((∏ _i : Fin n, Real.sqrt (2 * Real.pi)) *
              ∏ i : Fin n, (1 + μ i ^ (2 : Nat)) ^ (-(1 : ℝ) / 4)) /
            (2 * Real.pi) ^ ((n : ℝ) / 2) := by
              rw [Finset.prod_mul_distrib]
      _ = (∏ i : Fin n, (1 + μ i ^ (2 : Nat)) ^ (-(1 : ℝ) / 4)) := by
            rw [hsqrt_prod]
            field_simp [hden_pos.ne']
  have hprod_bound :
      ∏ i : Fin n, (1 + μ i ^ (2 : Nat)) ^ (-(1 : ℝ) / 4)
        ≤ (1 + ∑ i : Fin n, μ i ^ (2 : Nat)) ^ (-(1 : ℝ) / 4) := by
    have hone :
        1 + ∑ i : Fin n, μ i ^ (2 : Nat) ≤ ∏ i : Fin n, (1 + μ i ^ (2 : Nat)) := by
      classical
      induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
      | empty =>
          simp
      | @insert a s ha ih =>
          have hfa : 0 ≤ μ a ^ (2 : Nat) := by positivity
          have hs_nonneg : 0 ≤ s.sum (fun i => μ i ^ (2 : Nat)) := by
            exact Finset.sum_nonneg (by intro b hb; positivity)
          calc
            1 + (insert a s).sum (fun i => μ i ^ (2 : Nat))
                = (1 + μ a ^ (2 : Nat)) + s.sum (fun i => μ i ^ (2 : Nat)) := by
                    simp [ha, add_assoc, add_left_comm, add_comm]
            _ ≤ (1 + μ a ^ (2 : Nat)) * (1 + s.sum (fun i => μ i ^ (2 : Nat))) := by
                  nlinarith
            _ ≤ (1 + μ a ^ (2 : Nat)) * s.prod (fun i => 1 + μ i ^ (2 : Nat)) := by
                  gcongr
            _ = (insert a s).prod (fun i => 1 + μ i ^ (2 : Nat)) := by
                  simp [ha, mul_comm]
    calc
      ∏ i : Fin n, (1 + μ i ^ (2 : Nat)) ^ (-(1 : ℝ) / 4)
          = (∏ i : Fin n, (1 + μ i ^ (2 : Nat))) ^ (-(1 : ℝ) / 4) := by
              simpa using
                (Real.finset_prod_rpow Finset.univ (fun i : Fin n => 1 + μ i ^ (2 : Nat))
                  (by
                    intro i hi
                    positivity)
                  (-(1 : ℝ) / 4))
      _ ≤ (1 + ∑ i : Fin n, μ i ^ (2 : Nat)) ^ (-(1 : ℝ) / 4) := by
            exact Real.rpow_le_rpow_of_nonpos
              (by positivity : 0 < 1 + ∑ i : Fin n, μ i ^ (2 : Nat))
              hone
              (show (-(1 : ℝ) / 4) ≤ 0 by norm_num)
  calc
    ‖gaussianPsiComplex n lam‖
        = ∏ i : Fin n, (1 + μ i ^ (2 : Nat)) ^ (-(1 : ℝ) / 4) := hnorm_eq
    _ ≤ (1 + ∑ i : Fin n, μ i ^ (2 : Nat)) ^ (-(1 : ℝ) / 4) := hprod_bound
    _ = (1 + 2 * sNorm n lam) ^ (-(1 : ℝ) / 4) := by
          have hsumsq : ∑ i : Fin n, μ i ^ (2 : Nat) = 2 * sNorm n lam := by
            simpa [μ, T, hSymm, M] using gaussianMatrix_eigenvalue_sq_sum n lam
          rw [hsumsq]

lemma avgSigns_sub (n : ℕ) (f g : (Fin n → Fin 2) → ℝ) :
    avgSigns n (fun σ => f σ - g σ) = avgSigns n f - avgSigns n g := by
  unfold avgSigns
  rw [Finset.sum_sub_distrib]
  ring

lemma avgSigns_mono (n : ℕ) {f g : (Fin n → Fin 2) → ℝ} (hfg : ∀ σ, f σ ≤ g σ) :
    avgSigns n f ≤ avgSigns n g := by
  unfold avgSigns
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · exact Finset.sum_le_sum (fun σ _ => hfg σ)
  · positivity

lemma psi_re_eq_avgSigns_cos (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    (psi n lam).re = avgSigns n (fun σ => Real.cos (innerX n lam σ)) := by
  let S : ℂ := ∑ σ : Fin n → Fin 2, Complex.exp (Complex.I * ↑(innerX n lam σ))
  have hsum_re :
      S.re = ∑ σ : Fin n → Fin 2, Real.cos (innerX n lam σ) := by
    calc
      S.re = ∑ σ : Fin n → Fin 2, (Complex.exp (Complex.I * ↑(innerX n lam σ))).re := by
          simp [S]
      _ = ∑ σ : Fin n → Fin 2, Real.cos (innerX n lam σ) := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (Complex.exp_ofReal_mul_I_re (innerX n lam σ))
  have hcast : ((2 ^ n : ℂ)) = ((2 ^ n : ℝ) : ℂ) := by
    norm_num
  have hpsi : psi n lam = S / (2 ^ n : ℂ) := by
    simp [psi, S, div_eq_mul_inv, mul_comm]
  rw [hpsi, avgSigns]
  calc
    Complex.re (S / (2 ^ n : ℂ))
        = S.re / (2 ^ n : ℝ) := by
            rw [hcast]
            simpa using (Complex.div_ofReal_re S (2 ^ n : ℝ))
    _ = (∑ σ : Fin n → Fin 2, Real.cos (innerX n lam σ)) / (2 ^ n : ℝ) := by
          rw [hsum_re]
    _ = avgSigns n (fun σ => Real.cos (innerX n lam σ)) := by
          simp [avgSigns, div_eq_mul_inv, mul_comm]

lemma psi_im_eq_avgSigns_sin (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    (psi n lam).im = avgSigns n (fun σ => Real.sin (innerX n lam σ)) := by
  let S : ℂ := ∑ σ : Fin n → Fin 2, Complex.exp (Complex.I * ↑(innerX n lam σ))
  have hsum_im :
      S.im = ∑ σ : Fin n → Fin 2, Real.sin (innerX n lam σ) := by
    calc
      S.im = ∑ σ : Fin n → Fin 2, (Complex.exp (Complex.I * ↑(innerX n lam σ))).im := by
          simp [S]
      _ = ∑ σ : Fin n → Fin 2, Real.sin (innerX n lam σ) := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (Complex.exp_ofReal_mul_I_im (innerX n lam σ))
  have hcast : ((2 ^ n : ℂ)) = ((2 ^ n : ℝ) : ℂ) := by
    norm_num
  have hpsi : psi n lam = S / (2 ^ n : ℂ) := by
    simp [psi, S, div_eq_mul_inv, mul_comm]
  rw [hpsi, avgSigns]
  calc
    Complex.im (S / (2 ^ n : ℂ))
        = S.im / (2 ^ n : ℝ) := by
            rw [hcast]
            simpa using (Complex.div_ofReal_im S (2 ^ n : ℝ))
    _ = (∑ σ : Fin n → Fin 2, Real.sin (innerX n lam σ)) / (2 ^ n : ℝ) := by
          rw [hsum_im]
    _ = avgSigns n (fun σ => Real.sin (innerX n lam σ)) := by
          simp [avgSigns, div_eq_mul_inv, mul_comm]

private lemma abs_sin_sub_self_le_cube_div_six_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    |Real.sin x - x| ≤ x ^ (3 : Nat) / 6 := by
  have hsin_le : Real.sin x ≤ x := Real.sin_le hx
  have habs :
      |Real.sin x - x| = x - Real.sin x := by
    have hneg : Real.sin x - x ≤ 0 := sub_nonpos.mpr hsin_le
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using (abs_of_nonpos hneg)
  have hf_int : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 x := by
    exact intervalIntegrable_const
  have hcos_int : IntervalIntegrable (fun u : ℝ => Real.cos u) MeasureTheory.volume 0 x := by
    exact Real.continuous_cos.intervalIntegrable 0 x
  have hsub_int :
      x - Real.sin x = ∫ u in (0 : ℝ)..x, (1 - Real.cos u) := by
    calc
      x - Real.sin x
          = (∫ _u in (0 : ℝ)..x, (1 : ℝ)) - ∫ u in (0 : ℝ)..x, Real.cos u := by
              simp [integral_one, integral_cos]
      _ = ∫ u in (0 : ℝ)..x, (1 - Real.cos u) := by
            symm
            simpa using (intervalIntegral.integral_sub (a := (0 : ℝ)) (b := x)
              hf_int hcos_int)
  have hquad_int :
      IntervalIntegrable (fun u : ℝ => u ^ (2 : Nat) / 2) MeasureTheory.volume 0 x := by
    exact ((continuous_id.pow 2).div_const (2 : ℝ)).intervalIntegrable 0 x
  have hpoint :
      ∀ u ∈ Set.Icc (0 : ℝ) x, (1 - Real.cos u) ≤ u ^ (2 : Nat) / 2 := by
    intro u hu
    linarith [Real.one_sub_sq_div_two_le_cos (x := u)]
  have hmono :
      (∫ u in (0 : ℝ)..x, (1 - Real.cos u))
        ≤ ∫ u in (0 : ℝ)..x, u ^ (2 : Nat) / 2 := by
    exact intervalIntegral.integral_mono_on hx
      ((continuous_const.sub Real.continuous_cos).intervalIntegrable 0 x)
      hquad_int
      hpoint
  have hpow_int :
      (∫ u in (0 : ℝ)..x, u ^ (2 : Nat) / 2) = x ^ (3 : Nat) / 6 := by
    have hpow_base :
        (∫ u in (0 : ℝ)..x, u ^ (2 : Nat))
          = (x ^ (2 + 1) - (0 : ℝ) ^ (2 + 1)) / ((2 : ℝ) + 1) := by
      simpa using (integral_pow (a := (0 : ℝ)) (b := x) (n := 2))
    calc
      (∫ u in (0 : ℝ)..x, u ^ (2 : Nat) / 2)
          = (∫ u in (0 : ℝ)..x, u ^ (2 : Nat)) / 2 := by
              simpa using (intervalIntegral.integral_div (a := (0 : ℝ)) (b := x)
                (r := (2 : ℝ)) (f := fun u : ℝ => u ^ (2 : Nat)))
      _ = ((x ^ (3 : Nat) - (0 : ℝ) ^ (3 : Nat)) / 3) / 2 := by
            rw [hpow_base]
            ring
      _ = x ^ (3 : Nat) / 6 := by ring
  rw [habs]
  exact (hsub_int ▸ hmono).trans (le_of_eq hpow_int)

private lemma abs_sin_sub_self_le_cube_div_six (x : ℝ) :
    |Real.sin x - x| ≤ |x| ^ (3 : Nat) / 6 := by
  by_cases hx : 0 ≤ x
  · have h := abs_sin_sub_self_le_cube_div_six_of_nonneg (x := x) hx
    simpa [abs_of_nonneg hx] using h
  · have hx' : 0 ≤ -x := by linarith
    have h := abs_sin_sub_self_le_cube_div_six_of_nonneg (x := -x) hx'
    have hrew :
        |Real.sin x - x| = |Real.sin (-x) - (-x)| := by
      calc
        |Real.sin x - x| = |x - Real.sin x| := by
              simpa using (abs_sub_comm (Real.sin x) x)
        _ = |Real.sin (-x) - (-x)| := by
              simp [Real.sin_neg, sub_eq_add_neg, add_comm]
    have habs : |x| = -x := abs_of_nonpos (le_of_not_ge hx)
    simpa [habs] using (hrew.trans_le h)

lemma abs_cos_sub_one_add_sq_div_two_le_pow_four_div_twentyfour (x : ℝ) :
    |Real.cos x - (1 - x ^ (2 : Nat) / 2)| ≤ |x| ^ (4 : Nat) / 24 := by
  have hdecomp :
      Real.cos x - (1 - x ^ (2 : Nat) / 2)
        = -2 * (Real.sin (x / 2) - x / 2) * (Real.sin (x / 2) + x / 2) := by
    have hcos_sq : Real.cos x = 2 * Real.cos (x / 2) ^ (2 : Nat) - 1 := by
      simpa [pow_two, two_mul, mul_assoc] using (Real.cos_two_mul (x / 2))
    have hsin_sq : Real.sin (x / 2) ^ (2 : Nat) + Real.cos (x / 2) ^ (2 : Nat) = 1 := by
      simpa [pow_two, add_comm] using (Real.sin_sq_add_cos_sq (x / 2))
    rw [hcos_sq]
    nlinarith
  have hsin :
      |Real.sin (x / 2) - x / 2| ≤ |x / 2| ^ (3 : Nat) / 6 :=
    abs_sin_sub_self_le_cube_div_six (x / 2)
  have hsum : |Real.sin (x / 2) + x / 2| ≤ 2 * |x / 2| := by
    calc
      |Real.sin (x / 2) + x / 2| ≤ |Real.sin (x / 2)| + |x / 2| := by
            simpa [sub_eq_add_neg] using abs_sub (Real.sin (x / 2)) (-(x / 2))
      _ ≤ |x / 2| + |x / 2| := by
            have hsin_abs : |Real.sin (x / 2)| ≤ |x / 2| := by
              simpa using (Real.abs_sin_le_abs : |Real.sin (x / 2)| ≤ |x / 2|)
            nlinarith
      _ = 2 * |x / 2| := by ring
  have hx_div_abs : |x / 2| = |x| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    |Real.cos x - (1 - x ^ (2 : Nat) / 2)|
        = |(-2 : ℝ) * (Real.sin (x / 2) - x / 2) * (Real.sin (x / 2) + x / 2)| := by
            rw [hdecomp]
    _ = 2 * |Real.sin (x / 2) - x / 2| * |Real.sin (x / 2) + x / 2| := by
          rw [abs_mul, abs_mul]
          norm_num
    _ ≤ 2 * (|x / 2| ^ (3 : Nat) / 6) * (2 * |x / 2|) := by
          gcongr
    _ = |x| ^ (4 : Nat) / 24 := by
          rw [hx_div_abs]
          ring

private lemma taylorWithinEval_sin_six_at_zero {x : ℝ} (hx : 0 < x) :
    taylorWithinEval Real.sin 6 (Set.Icc (0 : ℝ) x) 0 x
      = x - x ^ (3 : Nat) / 6 + x ^ (5 : Nat) / 120 := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) x := ⟨le_rfl, hx.le⟩
  have hwithin (k : ℕ) :
      iteratedDerivWithin k Real.sin (Set.Icc (0 : ℝ) x) 0 = iteratedDeriv k Real.sin 0 := by
    exact iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc hx) Real.contDiff_sin.contDiffAt hmem0
  have h0 : iteratedDerivWithin 0 Real.sin (Set.Icc (0 : ℝ) x) 0 = 0 := by
    simpa [hwithin 0] using (Real.sin_zero : Real.sin 0 = 0)
  have h1 : iteratedDerivWithin 1 Real.sin (Set.Icc (0 : ℝ) x) 0 = 1 := by
    have hodd := congrArg (fun f : ℝ → ℝ => f (0 : ℝ)) (Real.iteratedDeriv_odd_sin (n := 0))
    simpa [hwithin 1] using hodd
  have h2 : iteratedDerivWithin 2 Real.sin (Set.Icc (0 : ℝ) x) 0 = 0 := by
    have heven := congrArg (fun f : ℝ → ℝ => f (0 : ℝ)) (Real.iteratedDeriv_even_sin (n := 1))
    simpa [hwithin 2] using heven
  have h3 : iteratedDerivWithin 3 Real.sin (Set.Icc (0 : ℝ) x) 0 = -1 := by
    have hodd := congrArg (fun f : ℝ → ℝ => f (0 : ℝ)) (Real.iteratedDeriv_odd_sin (n := 1))
    simpa [hwithin 3] using hodd
  have h4 : iteratedDerivWithin 4 Real.sin (Set.Icc (0 : ℝ) x) 0 = 0 := by
    have heven := congrArg (fun f : ℝ → ℝ => f (0 : ℝ)) (Real.iteratedDeriv_even_sin (n := 2))
    simpa [hwithin 4] using heven
  have h5 : iteratedDerivWithin 5 Real.sin (Set.Icc (0 : ℝ) x) 0 = 1 := by
    have hodd := congrArg (fun f : ℝ → ℝ => f (0 : ℝ)) (Real.iteratedDeriv_odd_sin (n := 2))
    simpa [hwithin 5] using hodd
  have h6 : iteratedDerivWithin 6 Real.sin (Set.Icc (0 : ℝ) x) 0 = 0 := by
    have heven := congrArg (fun f : ℝ → ℝ => f (0 : ℝ)) (Real.iteratedDeriv_even_sin (n := 3))
    simpa [hwithin 6] using heven
  rw [taylor_within_apply]
  simp [Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, h6, Nat.factorial]
  ring

private lemma abs_sin_sub_taylor5_le_pow7_div_5040_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    |Real.sin x - (x - x ^ (3 : Nat) / 6 + x ^ (5 : Nat) / 120)| ≤ x ^ (7 : Nat) / 5040 := by
  rcases eq_or_lt_of_le hx with rfl | hpos
  · simp
  ·
    rcases taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.sin) (x := x) (x₀ := (0 : ℝ)) (n := 6) hpos
      Real.contDiff_sin.contDiffOn with ⟨ξ, hξ, hrem⟩
    have htaylor :
        taylorWithinEval Real.sin 6 (Set.Icc (0 : ℝ) x) 0 x
          = x - x ^ (3 : Nat) / 6 + x ^ (5 : Nat) / 120 :=
      taylorWithinEval_sin_six_at_zero hpos
    have hodd :
        iteratedDeriv (7 : Nat) Real.sin ξ = (-1 : ℝ) ^ (3 : Nat) * Real.cos ξ := by
      exact congrArg (fun f : ℝ → ℝ => f ξ) (Real.iteratedDeriv_odd_sin (n := 3))
    have hrem' :
        Real.sin x - (x - x ^ (3 : Nat) / 6 + x ^ (5 : Nat) / 120)
          = -(Real.cos ξ * x ^ (7 : Nat)) / ((Nat.factorial 7 : Nat) : ℝ) := by
      have hrem0 := hrem
      rw [htaylor, hodd] at hrem0
      have hsign : ((-1 : ℝ) ^ (3 : Nat)) = -1 := by norm_num
      rw [hsign] at hrem0
      have hrem1 :
          Real.sin x - (x - x ^ (3 : Nat) / 6 + x ^ (5 : Nat) / 120)
            = ((-1 : ℝ) * (Real.cos ξ * x ^ (7 : Nat))) / ((Nat.factorial 7 : Nat) : ℝ) := by
        simpa [mul_assoc] using hrem0
      calc
        Real.sin x - (x - x ^ (3 : Nat) / 6 + x ^ (5 : Nat) / 120)
            = ((-1 : ℝ) * (Real.cos ξ * x ^ (7 : Nat))) / ((Nat.factorial 7 : Nat) : ℝ) := hrem1
        _ = -(Real.cos ξ * x ^ (7 : Nat)) / ((Nat.factorial 7 : Nat) : ℝ) := by ring
    have hxpow_nonneg : 0 ≤ x ^ (7 : Nat) := by positivity
    have hfac : (((Nat.factorial 7 : Nat) : ℝ)) = 5040 := by norm_num
    rw [hrem', abs_div, abs_neg, abs_mul, abs_of_nonneg hxpow_nonneg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((Nat.factorial 7 : Nat) : ℝ)), hfac]
    have hmul :
        |Real.cos ξ| * x ^ (7 : Nat) ≤ 1 * x ^ (7 : Nat) :=
      mul_le_mul_of_nonneg_right (Real.abs_cos_le_one ξ) hxpow_nonneg
    nlinarith

private lemma abs_sin_sub_taylor5_le_pow7_div_5040 (x : ℝ) :
    |Real.sin x - (x - x ^ (3 : Nat) / 6 + x ^ (5 : Nat) / 120)| ≤ |x| ^ (7 : Nat) / 5040 := by
  by_cases hx : 0 ≤ x
  · have h := abs_sin_sub_taylor5_le_pow7_div_5040_of_nonneg (x := x) hx
    simpa [abs_of_nonneg hx] using h
  · have hxneg : 0 ≤ -x := by linarith
    have h := abs_sin_sub_taylor5_le_pow7_div_5040_of_nonneg (x := -x) hxneg
    have habs : |x| = -x := abs_of_nonpos (le_of_not_ge hx)
    have hinner :
        Real.sin (-x) - ((-x) - (-x) ^ (3 : Nat) / 6 + (-x) ^ (5 : Nat) / 120)
          = -(Real.sin x - (x - x ^ (3 : Nat) / 6 + x ^ (5 : Nat) / 120)) := by
      calc
        Real.sin (-x) - ((-x) - (-x) ^ (3 : Nat) / 6 + (-x) ^ (5 : Nat) / 120)
            = -Real.sin x - ((-x) - (-x) ^ (3 : Nat) / 6 + (-x) ^ (5 : Nat) / 120) := by
              simp [Real.sin_neg]
        _ = -Real.sin x - (-(x - x ^ (3 : Nat) / 6 + x ^ (5 : Nat) / 120)) := by ring
        _ = -(Real.sin x - (x - x ^ (3 : Nat) / 6 + x ^ (5 : Nat) / 120)) := by ring
    have h' :
        |Real.sin x - (x - x ^ (3 : Nat) / 6 + x ^ (5 : Nat) / 120)| ≤ (-x) ^ (7 : Nat) / 5040 := by
      have h0 := h
      rw [hinner, abs_neg] at h0
      exact h0
    simpa [habs] using h'

private lemma taylorWithinEval_cos_five_at_zero {x : ℝ} (hx : 0 < x) :
    taylorWithinEval Real.cos 5 (Set.Icc (0 : ℝ) x) 0 x
      = 1 - x ^ (2 : Nat) / 2 + x ^ (4 : Nat) / 24 := by
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) x := ⟨le_rfl, hx.le⟩
  have hwithin (k : ℕ) :
      iteratedDerivWithin k Real.cos (Set.Icc (0 : ℝ) x) 0 = iteratedDeriv k Real.cos 0 := by
    exact iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc hx) Real.contDiff_cos.contDiffAt hmem0
  have h0 : iteratedDerivWithin 0 Real.cos (Set.Icc (0 : ℝ) x) 0 = 1 := by
    simpa [hwithin 0] using (Real.cos_zero : Real.cos 0 = 1)
  have h1 : iteratedDerivWithin 1 Real.cos (Set.Icc (0 : ℝ) x) 0 = 0 := by
    have hodd := congrArg (fun f : ℝ → ℝ => f (0 : ℝ)) (Real.iteratedDeriv_odd_cos (n := 0))
    simpa [hwithin 1] using hodd
  have h2 : iteratedDerivWithin 2 Real.cos (Set.Icc (0 : ℝ) x) 0 = -1 := by
    have heven := congrArg (fun f : ℝ → ℝ => f (0 : ℝ)) (Real.iteratedDeriv_even_cos (n := 1))
    simpa [hwithin 2] using heven
  have h3 : iteratedDerivWithin 3 Real.cos (Set.Icc (0 : ℝ) x) 0 = 0 := by
    have hodd := congrArg (fun f : ℝ → ℝ => f (0 : ℝ)) (Real.iteratedDeriv_odd_cos (n := 1))
    simpa [hwithin 3] using hodd
  have h4 : iteratedDerivWithin 4 Real.cos (Set.Icc (0 : ℝ) x) 0 = 1 := by
    have heven := congrArg (fun f : ℝ → ℝ => f (0 : ℝ)) (Real.iteratedDeriv_even_cos (n := 2))
    simpa [hwithin 4] using heven
  have h5 : iteratedDerivWithin 5 Real.cos (Set.Icc (0 : ℝ) x) 0 = 0 := by
    have hodd := congrArg (fun f : ℝ → ℝ => f (0 : ℝ)) (Real.iteratedDeriv_odd_cos (n := 2))
    simpa [hwithin 5] using hodd
  rw [taylor_within_apply]
  simp [Finset.sum_range_succ, h0, h1, h2, h3, h4, h5, Nat.factorial]
  ring

private lemma abs_cos_sub_taylor4_le_pow6_div_720_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    |Real.cos x - (1 - x ^ (2 : Nat) / 2 + x ^ (4 : Nat) / 24)| ≤ x ^ (6 : Nat) / 720 := by
  rcases eq_or_lt_of_le hx with rfl | hpos
  · simp
  ·
    rcases taylor_mean_remainder_lagrange_iteratedDeriv
      (f := Real.cos) (x := x) (x₀ := (0 : ℝ)) (n := 5) hpos
      Real.contDiff_cos.contDiffOn with ⟨ξ, hξ, hrem⟩
    have htaylor :
        taylorWithinEval Real.cos 5 (Set.Icc (0 : ℝ) x) 0 x
          = 1 - x ^ (2 : Nat) / 2 + x ^ (4 : Nat) / 24 :=
      taylorWithinEval_cos_five_at_zero hpos
    have heven :
        iteratedDeriv (6 : Nat) Real.cos ξ = (-1 : ℝ) ^ (3 : Nat) * Real.cos ξ := by
      exact congrArg (fun f : ℝ → ℝ => f ξ) (Real.iteratedDeriv_even_cos (n := 3))
    have hrem' :
        Real.cos x - (1 - x ^ (2 : Nat) / 2 + x ^ (4 : Nat) / 24)
          = -(Real.cos ξ * x ^ (6 : Nat)) / ((Nat.factorial 6 : Nat) : ℝ) := by
      have hrem0 := hrem
      rw [htaylor, heven] at hrem0
      have hsign : ((-1 : ℝ) ^ (3 : Nat)) = -1 := by norm_num
      rw [hsign] at hrem0
      have hrem1 :
          Real.cos x - (1 - x ^ (2 : Nat) / 2 + x ^ (4 : Nat) / 24)
            = ((-1 : ℝ) * (Real.cos ξ * x ^ (6 : Nat))) / ((Nat.factorial 6 : Nat) : ℝ) := by
        simpa [mul_assoc] using hrem0
      calc
        Real.cos x - (1 - x ^ (2 : Nat) / 2 + x ^ (4 : Nat) / 24)
            = ((-1 : ℝ) * (Real.cos ξ * x ^ (6 : Nat))) / ((Nat.factorial 6 : Nat) : ℝ) := hrem1
        _ = -(Real.cos ξ * x ^ (6 : Nat)) / ((Nat.factorial 6 : Nat) : ℝ) := by ring
    have hxpow_nonneg : 0 ≤ x ^ (6 : Nat) := by positivity
    have hfac : (((Nat.factorial 6 : Nat) : ℝ)) = 720 := by norm_num
    rw [hrem', abs_div, abs_neg, abs_mul, abs_of_nonneg hxpow_nonneg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((Nat.factorial 6 : Nat) : ℝ)), hfac]
    have hmul :
        |Real.cos ξ| * x ^ (6 : Nat) ≤ 1 * x ^ (6 : Nat) :=
      mul_le_mul_of_nonneg_right (Real.abs_cos_le_one ξ) hxpow_nonneg
    nlinarith

private lemma abs_cos_sub_taylor4_le_pow6_div_720 (x : ℝ) :
    |Real.cos x - (1 - x ^ (2 : Nat) / 2 + x ^ (4 : Nat) / 24)| ≤ |x| ^ (6 : Nat) / 720 := by
  by_cases hx : 0 ≤ x
  · have h := abs_cos_sub_taylor4_le_pow6_div_720_of_nonneg (x := x) hx
    simpa [abs_of_nonneg hx] using h
  · have hxneg : 0 ≤ -x := by linarith
    have h := abs_cos_sub_taylor4_le_pow6_div_720_of_nonneg (x := -x) hxneg
    have habs : |x| = -x := abs_of_nonpos (le_of_not_ge hx)
    have hpow2 : (-x) ^ (2 : Nat) = x ^ (2 : Nat) := by ring
    have hpow4 : (-x) ^ (4 : Nat) = x ^ (4 : Nat) := by ring
    have hrew :
        |Real.cos x - (1 - x ^ (2 : Nat) / 2 + x ^ (4 : Nat) / 24)|
          = |Real.cos (-x) - (1 - (-x) ^ (2 : Nat) / 2 + (-x) ^ (4 : Nat) / 24)| := by
      simp [Real.cos_neg, hpow2, hpow4]
    exact hrew.trans_le (by simpa [habs] using h)

lemma re_psi_taylor4_decomposition (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    ∃ eps : ℝ,
      (psi n lam).re = 1 - momentX n lam 2 / 2 + momentX n lam 4 / 24 + eps ∧
      |eps| ≤ avgSigns n (fun σ => |innerX n lam σ| ^ (6 : Nat) / 720) := by
  let xs : (Fin n → Fin 2) → ℝ := fun σ => innerX n lam σ
  let R : (Fin n → Fin 2) → ℝ :=
    fun σ => Real.cos (xs σ) - (1 - (xs σ) ^ (2 : Nat) / 2 + (xs σ) ^ (4 : Nat) / 24)
  refine ⟨avgSigns n R, ?_, ?_⟩
  · have hsplit :
        avgSigns n (fun σ => Real.cos (xs σ))
          = avgSigns n (fun σ => 1 - (xs σ) ^ (2 : Nat) / 2 + (xs σ) ^ (4 : Nat) / 24)
              + avgSigns n R := by
      have hfun :
          (fun σ => Real.cos (xs σ))
            = (fun σ => (1 - (xs σ) ^ (2 : Nat) / 2 + (xs σ) ^ (4 : Nat) / 24) + R σ) := by
        funext σ
        dsimp [R]
        ring
      rw [hfun, avgSigns_add]
    have hpoly :
        avgSigns n (fun σ => 1 - (xs σ) ^ (2 : Nat) / 2 + (xs σ) ^ (4 : Nat) / 24)
          = 1 - momentX n lam 2 / 2 + momentX n lam 4 / 24 := by
      calc
        avgSigns n (fun σ => 1 - (xs σ) ^ (2 : Nat) / 2 + (xs σ) ^ (4 : Nat) / 24)
            = avgSigns n (fun σ => 1 - (xs σ) ^ (2 : Nat) / 2)
                + avgSigns n (fun σ => (xs σ) ^ (4 : Nat) / 24) := by
                  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                    (avgSigns_add n
                      (fun σ => 1 - (xs σ) ^ (2 : Nat) / 2)
                      (fun σ => (xs σ) ^ (4 : Nat) / 24))
        _ = (1 - momentX n lam 2 / 2) + avgSigns n (fun σ => (xs σ) ^ (4 : Nat) / 24) := by
              rw [show avgSigns n (fun σ => 1 - (xs σ) ^ (2 : Nat) / 2) = 1 - momentX n lam 2 / 2 by
                    calc
                      avgSigns n (fun σ => 1 - (xs σ) ^ (2 : Nat) / 2)
                          = avgSigns n (fun _ : Fin n → Fin 2 => (1 : ℝ))
                              - avgSigns n (fun σ => (xs σ) ^ (2 : Nat) / 2) := by
                                simpa using
                                  (avgSigns_sub n
                                    (fun _ : Fin n → Fin 2 => (1 : ℝ))
                                    (fun σ => (xs σ) ^ (2 : Nat) / 2))
                      _ = 1 - avgSigns n (fun σ => (xs σ) ^ (2 : Nat) / 2) := by
                            simp [avgSigns_const]
                      _ = 1 - avgSigns n (fun σ => (xs σ) ^ (2 : Nat)) / 2 := by
                            simp [avgSigns_div_const]
                      _ = 1 - momentX n lam 2 / 2 := by
                            simp [xs, momentX, avgSigns]]
        _ = (1 - momentX n lam 2 / 2) + avgSigns n (fun σ => (xs σ) ^ (4 : Nat)) / 24 := by
              simp [avgSigns_div_const]
        _ = 1 - momentX n lam 2 / 2 + momentX n lam 4 / 24 := by
              simp [xs, momentX, avgSigns]
    calc
      (psi n lam).re = avgSigns n (fun σ => Real.cos (xs σ)) := by
          simp [xs, psi_re_eq_avgSigns_cos]
      _ = avgSigns n (fun σ => 1 - (xs σ) ^ (2 : Nat) / 2 + (xs σ) ^ (4 : Nat) / 24)
            + avgSigns n R := hsplit
      _ = 1 - momentX n lam 2 / 2 + momentX n lam 4 / 24 + avgSigns n R := by
            rw [hpoly]
  · have habs : |avgSigns n R| ≤ avgSigns n (fun σ => |R σ|) :=
      abs_avgSigns_le_avgSigns_abs n R
    have havg :
        avgSigns n (fun σ => |R σ|)
          ≤ avgSigns n (fun σ => |innerX n lam σ| ^ (6 : Nat) / 720) := by
      apply avgSigns_mono
      intro σ
      dsimp [R, xs]
      exact abs_cos_sub_taylor4_le_pow6_div_720 (innerX n lam σ)
    exact habs.trans havg

lemma im_psi_taylor5_decomposition (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    ∃ eps : ℝ,
      (psi n lam).im = momentX n lam 1 - momentX n lam 3 / 6 + momentX n lam 5 / 120 + eps ∧
      |eps| ≤ avgSigns n (fun σ => |innerX n lam σ| ^ (7 : Nat) / 5040) := by
  let xs : (Fin n → Fin 2) → ℝ := fun σ => innerX n lam σ
  let R : (Fin n → Fin 2) → ℝ :=
    fun σ => Real.sin (xs σ) - (xs σ - (xs σ) ^ (3 : Nat) / 6 + (xs σ) ^ (5 : Nat) / 120)
  refine ⟨avgSigns n R, ?_, ?_⟩
  · have hsplit :
        avgSigns n (fun σ => Real.sin (xs σ))
          = avgSigns n (fun σ => xs σ - (xs σ) ^ (3 : Nat) / 6 + (xs σ) ^ (5 : Nat) / 120)
              + avgSigns n R := by
      have hfun :
          (fun σ => Real.sin (xs σ))
            = (fun σ => (xs σ - (xs σ) ^ (3 : Nat) / 6 + (xs σ) ^ (5 : Nat) / 120) + R σ) := by
        funext σ
        dsimp [R]
        ring
      rw [hfun, avgSigns_add]
    have hpoly :
        avgSigns n (fun σ => xs σ - (xs σ) ^ (3 : Nat) / 6 + (xs σ) ^ (5 : Nat) / 120)
          = momentX n lam 1 - momentX n lam 3 / 6 + momentX n lam 5 / 120 := by
      calc
        avgSigns n (fun σ => xs σ - (xs σ) ^ (3 : Nat) / 6 + (xs σ) ^ (5 : Nat) / 120)
            = avgSigns n (fun σ => xs σ - (xs σ) ^ (3 : Nat) / 6)
                + avgSigns n (fun σ => (xs σ) ^ (5 : Nat) / 120) := by
                  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                    (avgSigns_add n
                      (fun σ => xs σ - (xs σ) ^ (3 : Nat) / 6)
                      (fun σ => (xs σ) ^ (5 : Nat) / 120))
        _ = (avgSigns n xs - avgSigns n (fun σ => (xs σ) ^ (3 : Nat) / 6))
              + avgSigns n (fun σ => (xs σ) ^ (5 : Nat) / 120) := by
                rw [avgSigns_sub]
        _ = (avgSigns n xs - avgSigns n (fun σ => (xs σ) ^ (3 : Nat)) / 6)
              + avgSigns n (fun σ => (xs σ) ^ (5 : Nat) / 120) := by
                simp [avgSigns_div_const]
        _ = (avgSigns n xs - avgSigns n (fun σ => (xs σ) ^ (3 : Nat)) / 6)
              + avgSigns n (fun σ => (xs σ) ^ (5 : Nat)) / 120 := by
                simp [avgSigns_div_const]
        _ = momentX n lam 1 - momentX n lam 3 / 6 + momentX n lam 5 / 120 := by
              simp [xs, momentX, avgSigns]
    calc
      (psi n lam).im = avgSigns n (fun σ => Real.sin (xs σ)) := by
          simp [xs, psi_im_eq_avgSigns_sin]
      _ = avgSigns n (fun σ => xs σ - (xs σ) ^ (3 : Nat) / 6 + (xs σ) ^ (5 : Nat) / 120)
            + avgSigns n R := hsplit
      _ = momentX n lam 1 - momentX n lam 3 / 6 + momentX n lam 5 / 120 + avgSigns n R := by
            rw [hpoly]
  · have habs : |avgSigns n R| ≤ avgSigns n (fun σ => |R σ|) :=
      abs_avgSigns_le_avgSigns_abs n R
    have havg :
        avgSigns n (fun σ => |R σ|)
          ≤ avgSigns n (fun σ => |innerX n lam σ| ^ (7 : Nat) / 5040) := by
      apply avgSigns_mono
      intro σ
      dsimp [R, xs]
      exact abs_sin_sub_taylor5_le_pow7_div_5040 (innerX n lam σ)
    exact habs.trans havg
