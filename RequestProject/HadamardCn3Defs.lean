import Mathlib

/-!
# Foundational Definitions For The Cn^3 Formalization

This module contains the basic combinatorial, Gaussian, and coordinate-level
objects used throughout the active development.

It is intentionally definition-heavy: the later analytic and counting bridges
live in the split follow-on modules

- `RequestProject.HadamardCn3TorusCount`
- `RequestProject.HadamardCn3Moments`
- `RequestProject.HadamardCn3MOO`
- `RequestProject.HadamardCn3ResidualBase`

## Architecture

We model edge data using symmetric matrices `Fin n → Fin n → ℝ` rather than an
explicit `Fin (n.choose 2)` coordinate system. This keeps the basic
definitions, influence statistics, and Gaussian support quantities closer to
the mathematical notation used downstream.
-/

noncomputable section

open Real MeasureTheory Filter Finset Topology
open scoped Pointwise

set_option linter.unusedVariables false

/-!
## Setup and Core Definitions
-/

/-- The dimension d = n choose 2, the number of edges of the complete graph K_n. -/
def dim (n : ℕ) : ℕ := n.choose 2

/-- The set of all sign vectors in {-1,1}^n, represented via Fin 2.
    We encode: 0 ↦ -1, 1 ↦ 1. -/
def signOf (b : Fin 2) : ℤ := 2 * (b : ℤ) - 1

/-- The quadratic form `X_λ(σ) = Σ_{i<j} λ_{ij} σ_i σ_j` on sign vectors. -/
def innerX (n : ℕ) (lam : Fin n → Fin n → ℝ) (σ : Fin n → Fin 2) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i < j then lam i j * (signOf (σ i)) * (signOf (σ j)) else 0

/-- The same quadratic form evaluated on real coordinates, used for the Gaussian
comparison side of the Mossel-O'Donnell-Oleszkiewicz invariance principle. -/
def gaussianInnerX (n : ℕ) (lam : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i < j then lam i j * x i * x j else 0

/-- The discrete Fourier average
`ψ_n(λ) = 2^{-n} Σ_{σ ∈ {-1,1}^n} exp(i X_λ(σ))`. -/
def psi (n : ℕ) (lam : Fin n → Fin n → ℝ) : ℂ :=
  (↑(2 ^ n : ℕ) : ℂ)⁻¹ * ∑ σ : Fin n → Fin 2,
    Complex.exp (Complex.I * ↑(innerX n lam σ))

/-- s(λ) = ‖λ‖² = Σ_{i<j} λ_{ij}², the squared norm of the edge vector. -/
def sNorm (n : ℕ) (lam : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then lam i j ^ 2 else 0

/-- T(λ) = Σ_{i<j<k} λ_{ij} λ_{ik} λ_{jk}, the triangle sum. -/
def cubicT (n : ℕ) (lam : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    if i < j ∧ j < k then lam i j * lam i k * lam j k else 0

/-- The Gaussian integral F(d,t) = (π/(2t))^{d/2}. -/
def gaussianF (d : ℕ) (t : ℝ) : ℝ :=
  (π / (2 * t)) ^ ((d : ℝ) / 2)

/-- The inner-core Gaussian mass G_core(d,t) = ∫_{‖λ‖²≤d/t} e^{-2t‖λ‖²} dλ.
    Defined as the Lebesgue integral with indicator. -/
def coreMass (d : ℕ) (t : ℝ) : ℝ :=
  ∫ x : Fin d → ℝ,
    Set.indicator {x : Fin d → ℝ | ∑ i, x i ^ 2 ≤ (d : ℝ) / t}
      (fun x => Real.exp (-2 * t * ∑ i, x i ^ 2)) x

/-- The number N_{n,s} of n × s partial Hadamard matrices.
    An n × s partial Hadamard matrix has entries ±1 with pairwise orthogonal rows. -/
def hadamardCount (n s : ℕ) : ℕ :=
  (Finset.univ.filter (fun M : Fin n → Fin s → Fin 2 =>
    ∀ i j : Fin n, i ≠ j →
      (∑ k : Fin s, (signOf (M i k) : ℝ) * (signOf (M j k) : ℝ)) = 0)).card

/-- The normalized count `N_{n,s} / 2^{ns}`.
    This is the combinatorial quantity directly identified with the normalized
    torus integral. -/
def normalizedCount (n s : ℕ) : ℝ := (hadamardCount n s : ℝ) / (2 : ℝ) ^ (n * s)

/-- Read an unordered edge from a matrix by always taking the strict
upper-triangular coordinate. -/
private def edgeVal {n : ℕ} (lam : Fin n → Fin n → ℝ) (i j : Fin n) : ℝ :=
  if hij : i < j then lam i j else if hji : j < i then lam j i else 0

private lemma edgeVal_eq_of_lt {n : ℕ} (lam : Fin n → Fin n → ℝ) {i j : Fin n} (hij : i < j) :
    edgeVal lam i j = lam i j := by
  unfold edgeVal
  simp [hij]

private lemma edgeVal_eq_of_gt {n : ℕ} (lam : Fin n → Fin n → ℝ) {i j : Fin n} (hji : j < i) :
    edgeVal lam i j = lam j i := by
  unfold edgeVal
  simp [hji, not_lt_of_gt hji]

private lemma edgeVal_self {n : ℕ} (lam : Fin n → Fin n → ℝ) (i : Fin n) :
    edgeVal lam i i = 0 := by
  unfold edgeVal
  simp

private lemma edgeVal_comm {n : ℕ} (lam : Fin n → Fin n → ℝ) (i j : Fin n) :
    edgeVal lam i j = edgeVal lam j i := by
  by_cases hij : i < j
  · rw [edgeVal_eq_of_lt _ hij, edgeVal_eq_of_gt _ hij]
  · by_cases hji : j < i
    · rw [edgeVal_eq_of_gt _ hji, edgeVal_eq_of_lt _ hji]
    · have hij_eq : i = j := by omega
      subst hij_eq
      simp [edgeVal_self]

/-- The symmetric zero-diagonal matrix attached to `lam`, obtained by reflecting
the strict upper-triangular coordinates across the diagonal. -/
def gaussianMatrix (n : ℕ) (lam : Fin n → Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => edgeVal lam i j

private lemma gaussianMatrix_apply_lt {n : ℕ} (lam : Fin n → Fin n → ℝ) {i j : Fin n} (hij : i < j) :
    gaussianMatrix n lam i j = lam i j := by
  simp [gaussianMatrix, edgeVal_eq_of_lt, hij]

private lemma gaussianMatrix_apply_gt {n : ℕ} (lam : Fin n → Fin n → ℝ) {i j : Fin n} (hji : j < i) :
    gaussianMatrix n lam i j = lam j i := by
  simp [gaussianMatrix, edgeVal_eq_of_gt, hji]

private lemma gaussianMatrix_apply_diag {n : ℕ} (lam : Fin n → Fin n → ℝ) (i : Fin n) :
    gaussianMatrix n lam i i = 0 := by
  simp [gaussianMatrix, edgeVal_self]

private lemma gaussianMatrix_isSymm (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    (gaussianMatrix n lam).IsSymm := by
  ext i j
  simp [gaussianMatrix, edgeVal_comm]

lemma gaussianMatrix_isHermitian (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    (gaussianMatrix n lam).IsHermitian := by
  show Matrix.conjTranspose (gaussianMatrix n lam) = gaussianMatrix n lam
  ext i j
  simp [gaussianMatrix, edgeVal_comm]

private lemma gaussianMatrix_trace_mul_self_eq_sq_sum
    (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    Matrix.trace (gaussianMatrix n lam * gaussianMatrix n lam)
      = ∑ i : Fin n, ∑ j : Fin n, gaussianMatrix n lam i j ^ (2 : Nat) := by
  let M : Matrix (Fin n) (Fin n) ℝ := gaussianMatrix n lam
  calc
    Matrix.trace (gaussianMatrix n lam * gaussianMatrix n lam)
      = ∑ i : Fin n, ∑ j : Fin n, M i j * M j i := by
          simp [Matrix.trace, Matrix.mul_apply, M]
    _ = ∑ i : Fin n, ∑ j : Fin n, M i j * M j i := by
          rfl
    _ = ∑ i : Fin n, ∑ j : Fin n, M i j * M i j := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          have hsymm : M j i = M i j := by
            simpa [M] using (gaussianMatrix_isSymm n lam).apply i j
          rw [hsymm]
    _ = ∑ i : Fin n, ∑ j : Fin n, gaussianMatrix n lam i j ^ (2 : Nat) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [M, pow_two]

private lemma gaussianMatrix_trace_mul_self_eq_two_sNorm
    (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    Matrix.trace (gaussianMatrix n lam * gaussianMatrix n lam) = 2 * sNorm n lam := by
  let upper : Fin n × Fin n → ℝ := fun p =>
    if p.1 < p.2 then lam p.1 p.2 ^ (2 : Nat) else 0
  let lower : Fin n × Fin n → ℝ := fun p =>
    if p.2 < p.1 then lam p.2 p.1 ^ (2 : Nat) else 0
  have hsplit :
      ∑ i : Fin n, ∑ j : Fin n, gaussianMatrix n lam i j ^ (2 : Nat)
        = (∑ p : Fin n × Fin n, upper p) + (∑ p : Fin n × Fin n, lower p) := by
    calc
      ∑ i : Fin n, ∑ j : Fin n, gaussianMatrix n lam i j ^ (2 : Nat)
          = ∑ p : Fin n × Fin n, gaussianMatrix n lam p.1 p.2 ^ (2 : Nat) := by
              rw [Fintype.sum_prod_type]
      ∑ p : Fin n × Fin n, gaussianMatrix n lam p.1 p.2 ^ (2 : Nat)
          = ∑ p : Fin n × Fin n, (upper p + lower p) := by
              refine Finset.sum_congr rfl ?_
              intro p hp
              rcases p with ⟨i, j⟩
              by_cases hij : i < j
              · simp [upper, lower, gaussianMatrix_apply_lt, hij, not_lt_of_gt hij]
              · by_cases hji : j < i
                · simp [upper, lower, gaussianMatrix_apply_gt, hij, hji]
                · have hij_eq : i = j := by omega
                  subst hij_eq
                  simp [upper, lower, gaussianMatrix_apply_diag]
      _ = (∑ p : Fin n × Fin n, upper p) + (∑ p : Fin n × Fin n, lower p) := by
            rw [Finset.sum_add_distrib]
  have hswap :
      (∑ p : Fin n × Fin n, lower p) = ∑ p : Fin n × Fin n, upper p := by
    refine Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n)) lower upper ?_
    intro p
    rcases p with ⟨i, j⟩
    simp [upper, lower]
  calc
    Matrix.trace (gaussianMatrix n lam * gaussianMatrix n lam)
      = ∑ i : Fin n, ∑ j : Fin n, gaussianMatrix n lam i j ^ (2 : Nat) := by
          exact gaussianMatrix_trace_mul_self_eq_sq_sum n lam
    _ = (∑ p : Fin n × Fin n, upper p) + (∑ p : Fin n × Fin n, lower p) := hsplit
    _ = (∑ p : Fin n × Fin n, upper p) + (∑ p : Fin n × Fin n, upper p) := by rw [hswap]
    _ = 2 * ∑ p : Fin n × Fin n, upper p := by ring
    _ = 2 * sNorm n lam := by
          rw [Fintype.sum_prod_type]
          simp [upper, sNorm]

lemma gaussianMatrix_eigenvalue_sq_sum
    (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
      Matrix.toEuclideanLin (gaussianMatrix n lam)
    let hSymm : T.IsSymmetric :=
      (Matrix.isHermitian_iff_isSymmetric (A := gaussianMatrix n lam)).1
        (gaussianMatrix_isHermitian n lam)
    ∑ i : Fin n, (hSymm.eigenvalues finrank_euclideanSpace_fin i) ^ (2 : Nat) = 2 * sNorm n lam := by
  classical
  dsimp
  let M : Matrix (Fin n) (Fin n) ℝ := gaussianMatrix n lam
  let hHerm : M.IsHermitian := gaussianMatrix_isHermitian n lam
  let T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := Matrix.toEuclideanLin M
  let hSymm : T.IsSymmetric := (Matrix.isHermitian_iff_isSymmetric (A := M)).1 hHerm
  let b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    hSymm.eigenvectorBasis finrank_euclideanSpace_fin
  let μ : Fin n → ℝ := hSymm.eigenvalues finrank_euclideanSpace_fin
  have htrace_sum :
      LinearMap.trace ℝ _ (T.comp T) = ∑ i : Fin n, μ i ^ (2 : Nat) := by
    rw [LinearMap.trace_eq_sum_inner (T := T.comp T) b]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi_eig : T (b i) = μ i • b i := by
      exact hSymm.apply_eigenvectorBasis finrank_euclideanSpace_fin i
    calc
      inner ℝ (b i) ((T.comp T) (b i))
          = inner ℝ (b i) (μ i • (μ i • b i)) := by
              simp [LinearMap.comp_apply, hi_eig, map_smul]
      _ = μ i ^ (2 : Nat) := by
            calc
              inner ℝ (b i) (μ i • (μ i • b i))
                  = μ i * μ i * inner ℝ (b i) (b i) := by
                      simp [inner_smul_right]
              _ = μ i * μ i := by
                    simp [b.orthonormal.1 i]
              _ = μ i ^ (2 : Nat) := by
                    ring
  have hcomp :
      T.comp T = Matrix.toEuclideanLin (M * M) := by
    ext v i
    simp [T, Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  have htrace_matrix :
      LinearMap.trace ℝ _ (T.comp T) = Matrix.trace (M * M) := by
    rw [hcomp]
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    exact Matrix.trace_toLin_eq (A := M * M) ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
  calc
    ∑ i : Fin n, μ i ^ (2 : Nat) = LinearMap.trace ℝ _ (T.comp T) := by
          symm
          exact htrace_sum
    _ = Matrix.trace (M * M) := htrace_matrix
    _ = 2 * sNorm n lam := by
          simpa [M] using gaussianMatrix_trace_mul_self_eq_two_sNorm n lam

/-- Rewrites the Gaussian quadratic phase into matrix/dot-product form. This is
useful local structure, not just a cosmetic alias. -/
private lemma gaussianInnerX_eq_half_dotProduct_mulVec (n : ℕ)
    (lam : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    gaussianInnerX n lam x
      = (1 / 2 : ℝ) * (dotProduct x (Matrix.mulVec (gaussianMatrix n lam) x)) := by
  classical
  let upper : Fin n × Fin n → ℝ := fun p =>
    if p.1 < p.2 then lam p.1 p.2 * x p.1 * x p.2 else 0
  let lower : Fin n × Fin n → ℝ := fun p =>
    if p.2 < p.1 then lam p.2 p.1 * x p.1 * x p.2 else 0
  have hdot_expand :
      dotProduct x (Matrix.mulVec (gaussianMatrix n lam) x)
        = ∑ p : Fin n × Fin n, (gaussianMatrix n lam p.1 p.2 * x p.1 * x p.2) := by
    unfold dotProduct Matrix.mulVec
    calc
      ∑ i : Fin n, x i * ∑ j : Fin n, gaussianMatrix n lam i j * x j
          = ∑ i : Fin n, ∑ j : Fin n, gaussianMatrix n lam i j * x i * x j := by
              simp_rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = ∑ p : Fin n × Fin n, (gaussianMatrix n lam p.1 p.2 * x p.1 * x p.2) := by
            rw [Fintype.sum_prod_type]
  have hpair :
      (∑ p : Fin n × Fin n, (gaussianMatrix n lam p.1 p.2 * x p.1 * x p.2))
        = ∑ p : Fin n × Fin n, (upper p + lower p) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    rcases p with ⟨i, j⟩
    by_cases hij : i < j
    · simp [upper, lower, gaussianMatrix_apply_lt, hij, not_lt_of_gt hij]
    · by_cases hji : j < i
      · simp [upper, lower, gaussianMatrix_apply_gt, hij, hji]
      
      · have hij_eq : i = j := by omega
        subst hij_eq
        simp [upper, lower, gaussianMatrix_apply_diag]
  have hsplit :
      dotProduct x (Matrix.mulVec (gaussianMatrix n lam) x)
        = (∑ p : Fin n × Fin n, upper p) + (∑ p : Fin n × Fin n, lower p) := by
    calc
      dotProduct x (Matrix.mulVec (gaussianMatrix n lam) x)
          = ∑ p : Fin n × Fin n, (gaussianMatrix n lam p.1 p.2 * x p.1 * x p.2) := hdot_expand
      _ = ∑ p : Fin n × Fin n, (upper p + lower p) := by
            exact hpair
      _ = (∑ p : Fin n × Fin n, upper p) + (∑ p : Fin n × Fin n, lower p) := by
            rw [Finset.sum_add_distrib]
  have hswap :
      (∑ p : Fin n × Fin n, lower p) = ∑ p : Fin n × Fin n, upper p := by
    refine Fintype.sum_equiv (Equiv.prodComm (Fin n) (Fin n)) lower upper ?_
    intro p
    rcases p with ⟨i, j⟩
    simp [upper, lower, mul_comm, mul_left_comm]
  calc
    gaussianInnerX n lam x
        = ∑ p : Fin n × Fin n, upper p := by
            rw [Fintype.sum_prod_type]
            rfl
    _ = (1 / 2 : ℝ) * ((∑ p : Fin n × Fin n, upper p) + (∑ p : Fin n × Fin n, lower p)) := by
          rw [hswap]
          ring
    _ = (1 / 2 : ℝ) * (dotProduct x (Matrix.mulVec (gaussianMatrix n lam) x)) := by
          rw [hsplit]

/-- The simple 4-cycle sum over increasing quadruples of vertices. -/
def simpleCycle4 (n : ℕ) (lam : Fin n → Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
    if i < j ∧ j < k ∧ k < l then
      lam i j * lam j k * lam k l * lam i l +
      lam i j * lam j l * lam k l * lam i k +
      lam i k * lam j k * lam j l * lam i l
    else 0

/-- The ordered 4-cycle form C_4^ord(λ) = Σ over ordered 4-cycles. -/
def orderedCycle4 (n : ℕ) (lam : Fin n → Fin n → ℝ) : ℝ :=
  8 * simpleCycle4 n lam

/-- The corrected quartic polynomial Q_4^corr(λ) = -(1/12) Σ_e λ_e⁴ + (1/8) C_4^ord(λ). -/
def quarticCorr (n : ℕ) (lam : Fin n → Fin n → ℝ) : ℝ :=
  -(1/12) * (∑ i : Fin n, ∑ j : Fin n, if i < j then lam i j ^ 4 else 0) +
    (1/8) * orderedCycle4 n lam

/-- The upper-left minor obtained by deleting the last vertex. -/
def minorLamLast {n : ℕ} (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => lam i.castSucc j.castSucc

/-- The last-column edge weights obtained by deleting the last vertex. -/
def lastColLam {n : ℕ} (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin n → ℝ :=
  fun i => lam i.castSucc (Fin.last n)

/-- The simple 4-cycle contribution coming from cycles that use the last vertex. -/
def simpleCycle4LastCross (n : ℕ) (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
    if i < j ∧ j < k then
      B i j * B j k * x k * x i +
      B i j * x j * x k * B i k +
      B i k * B j k * x j * x i
    else 0

/-- The triangle contribution coming from triangles that use the last vertex. -/
def cubicTLastCross (n : ℕ) (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then B i j * x i * x j else 0

/-- Split a strict upper-triangular double sum by whether the second index is the
last vertex or not. -/
lemma strictUpper_sum_split_last {n : ℕ}
    (f : Fin (n + 1) → Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), if i < j then f i j else 0)
      =
    (∑ i : Fin n, ∑ j : Fin n, if i < j then f i.castSucc j.castSucc else 0)
      +
    ∑ i : Fin n, f i.castSucc (Fin.last n) := by
  simp_rw [Fin.sum_univ_castSucc]
  simp [not_lt_of_ge (Fin.le_last _)]
  simp_rw [Finset.sum_add_distrib]

/-- Split a chained three-index sum by whether the last index is the last vertex
or not. Terms with the last vertex in an earlier slot vanish. -/
private lemma chainThreeSum_split_last {n : ℕ}
    (f : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1),
        if i < j ∧ j < k then f i j k else 0)
      =
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        if i < j ∧ j < k then f i.castSucc j.castSucc k.castSucc else 0)
      +
    (∑ i : Fin n, ∑ j : Fin n,
        if i < j then f i.castSucc j.castSucc (Fin.last n) else 0) := by
  simp_rw [Fin.sum_univ_castSucc]
  simp [not_lt_of_ge (Fin.le_last _)]
  simp_rw [Finset.sum_add_distrib]

/-- Split a chained four-index sum by whether the last index is the last vertex
or not. Terms with the last vertex in any earlier slot vanish automatically. -/
private lemma chainFourSum_split_last {n : ℕ}
    (f : Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), ∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
        if i < j ∧ j < k ∧ k < l then f i j k l else 0)
      =
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        if i < j ∧ j < k ∧ k < l then
          f i.castSucc j.castSucc k.castSucc l.castSucc
        else 0)
      +
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        if i < j ∧ j < k then
          f i.castSucc j.castSucc k.castSucc (Fin.last n)
        else 0) := by
  simp_rw [Fin.sum_univ_castSucc]
  simp [not_lt_of_ge (Fin.le_last _)]
  simp_rw [Finset.sum_add_distrib]

/-- Manuscript `lem:quartic-peeling` in the simple-cycle normalization. -/
private lemma simpleCycle4_peel_last (n : ℕ) (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    simpleCycle4 (n + 1) lam
      = simpleCycle4 n (minorLamLast lam)
          + simpleCycle4LastCross n (minorLamLast lam) (lastColLam lam) := by
  unfold simpleCycle4 minorLamLast lastColLam simpleCycle4LastCross
  rw [chainFourSum_split_last]

/-- Ordered 4-cycles peel by separating those through the last vertex. -/
private lemma orderedCycle4_peel_last (n : ℕ) (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    orderedCycle4 (n + 1) lam
      = orderedCycle4 n (minorLamLast lam)
          + 8 * simpleCycle4LastCross n (minorLamLast lam) (lastColLam lam) := by
  unfold orderedCycle4
  rw [simpleCycle4_peel_last]
  ring

/-- Split the diagonal quartic term by whether an edge uses the last vertex. -/
private lemma quarticDiagonal_split_last (n : ℕ) (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), if i < j then lam i j ^ (4 : Nat) else 0)
      =
    (∑ i : Fin n, ∑ j : Fin n,
        if i < j then (minorLamLast lam i j) ^ (4 : Nat) else 0)
      +
    ∑ i : Fin n, (lastColLam lam i) ^ (4 : Nat) := by
  unfold minorLamLast lastColLam
  rw [strictUpper_sum_split_last]

/-- The squared edge norm splits into the peeled minor and the last column. -/
lemma sNorm_peel_last (n : ℕ) (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    sNorm (n + 1) lam
      = sNorm n (minorLamLast lam) + ∑ i : Fin n, (lastColLam lam i) ^ (2 : Nat) := by
  unfold sNorm minorLamLast lastColLam
  rw [strictUpper_sum_split_last]

/-- The triangle form splits by whether a triangle uses the last vertex. -/
lemma cubicT_peel_last (n : ℕ) (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    cubicT (n + 1) lam
      = cubicT n (minorLamLast lam)
          + cubicTLastCross n (minorLamLast lam) (lastColLam lam) := by
  unfold cubicT minorLamLast lastColLam cubicTLastCross
  rw [chainThreeSum_split_last]

/-- Manuscript `lem:quartic-peeling` in corrected-quartic form. -/
lemma quarticCorr_peel_last (n : ℕ) (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    quarticCorr (n + 1) lam
      = quarticCorr n (minorLamLast lam)
          + simpleCycle4LastCross n (minorLamLast lam) (lastColLam lam)
          - (1 / 12 : ℝ) * ∑ i : Fin n, (lastColLam lam i) ^ (4 : Nat) := by
  unfold quarticCorr
  rw [quarticDiagonal_split_last, orderedCycle4_peel_last]
  ring

/-- Averaging over all sign vectors in `(Fin n → Fin 2)`. -/
def avgSigns (n : ℕ) (f : (Fin n → Fin 2) → ℝ) : ℝ :=
  (↑(2 ^ n : ℕ) : ℝ)⁻¹ * ∑ σ : Fin n → Fin 2, f σ

/-- Expectation against the standard Gaussian law on `ℝ^n`, written as a
normalized Lebesgue integral. -/
def stdGaussianAvg (n : ℕ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ *
    ∫ x : Fin n → ℝ, f x * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2)

/-! ### Internal Gaussian characteristic-function support -/

/-- The complex Gaussian integrand for the quadratic phase `gaussianInnerX`. -/
def gaussianPsiIntegrand (n : ℕ) (lam : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℂ :=
  Complex.exp
    (((( -(∑ i : Fin n, x i ^ (2 : Nat)) / 2 : ℝ)) : ℂ)
      + (gaussianInnerX n lam x : ℂ) * Complex.I)

private lemma complexSquareSum_re (n : ℕ) (x : Fin n → ℝ) :
    ∑ i : Fin n, ((x i : ℂ) ^ (2 : Nat)).re = ∑ i : Fin n, x i ^ (2 : Nat) := by
  refine Finset.sum_congr rfl ?_
  intro i hi
  calc
    (((x i : ℂ) ^ (2 : Nat)).re) = (((x i : ℂ) * (x i : ℂ)).re) := by simp [pow_two]
    _ = x i * x i := by simp
    _ = x i ^ (2 : Nat) := by ring

private lemma complexSquareSum_im (n : ℕ) (x : Fin n → ℝ) :
    ∑ i : Fin n, ((x i : ℂ) ^ (2 : Nat)).im = 0 := by
  refine Finset.sum_eq_zero ?_
  intro i hi
  calc
    (((x i : ℂ) ^ (2 : Nat)).im) = (((x i : ℂ) * (x i : ℂ)).im) := by simp [pow_two]
    _ = 0 := by simp

private lemma continuous_gaussianInnerX (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    Continuous (fun x : Fin n → ℝ => gaussianInnerX n lam x) := by
  unfold gaussianInnerX
  refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro i hi
  refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro j hj
  by_cases hij : i < j
  · simpa [hij, mul_assoc, mul_left_comm, mul_comm] using
      (continuous_const.mul ((continuous_apply i).mul (continuous_apply j)))
  · simpa [hij] using (continuous_const : Continuous fun _ : Fin n → ℝ => (0 : ℝ))

private lemma continuous_gaussianPsiIntegrand (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    Continuous (gaussianPsiIntegrand n lam) := by
  unfold gaussianPsiIntegrand
  have hsq :
      Continuous (fun x : Fin n → ℝ => ((-∑ i : Fin n, x i ^ (2 : Nat)) / 2 : ℝ)) := by
    fun_prop
  have hphase :
      Continuous (fun x : Fin n → ℝ => (gaussianInnerX n lam x : ℂ)) := by
    exact Complex.continuous_ofReal.comp (continuous_gaussianInnerX n lam)
  have harg :
      Continuous (fun x : Fin n → ℝ =>
        (((((-∑ i : Fin n, x i ^ (2 : Nat)) / 2 : ℝ)) : ℂ)
          + (gaussianInnerX n lam x : ℂ) * Complex.I)) := by
    exact (Complex.continuous_ofReal.comp hsq).add (hphase.mul continuous_const)
  exact Complex.continuous_exp.comp harg

private lemma gaussianPsiIntegrand_norm (n : ℕ) (lam : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    ‖gaussianPsiIntegrand n lam x‖ = Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2) := by
  have hre :
      (((((-∑ i : Fin n, x i ^ (2 : Nat)) / 2 : ℝ)) : ℂ)
        + (gaussianInnerX n lam x : ℂ) * Complex.I).re
        = (((-∑ i : Fin n, x i ^ (2 : Nat)) / 2 : ℝ)) := by
    simp [complexSquareSum_re]
  rw [gaussianPsiIntegrand, Complex.norm_exp, hre]

/-- The complex-valued Gaussian characteristic function corresponding to
`gaussianInnerX`. -/
def gaussianPsiComplex (n : ℕ) (lam : Fin n → Fin n → ℝ) : ℂ :=
  (∫ x : Fin n → ℝ, gaussianPsiIntegrand n lam x) /
    ((((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ))

lemma integrable_stdGaussianDensity (n : ℕ) :
    Integrable (fun x : Fin n → ℝ => Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2)) := by
  have hcomplex :
      Integrable (fun x : Fin n → ℝ =>
        Complex.exp (-(1 / 2 : ℂ) * ∑ i : Fin n, (x i : ℂ) ^ (2 : Nat))) := by
    simpa [mul_assoc] using
      (GaussianFourier.integrable_cexp_neg_mul_sum_add (ι := Fin n) (b := (1 / 2 : ℂ))
        (c := fun _ => 0) (by norm_num : 0 < ((1 / 2 : ℂ).re)))
  have hEq :
      (fun x : Fin n → ℝ =>
        ‖Complex.exp (-(1 / 2 : ℂ) * ∑ i : Fin n, (x i : ℂ) ^ (2 : Nat))‖)
        = fun x : Fin n → ℝ => Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2) := by
    funext x
    rw [Complex.norm_exp]
    simp [complexSquareSum_re, div_eq_mul_inv]
    ring
  convert hcomplex.norm using 1
  ext x
  exact (congrFun hEq x).symm

private lemma integrable_gaussianPsiIntegrand (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    Integrable (gaussianPsiIntegrand n lam) := by
  have hnorm :
      Integrable (fun x : Fin n → ℝ => ‖gaussianPsiIntegrand n lam x‖) := by
    simpa [gaussianPsiIntegrand_norm] using integrable_stdGaussianDensity n
  exact (integrable_norm_iff (continuous_gaussianPsiIntegrand n lam).aestronglyMeasurable).1 hnorm

private lemma gaussianPsiIntegrand_re (n : ℕ) (lam : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    (gaussianPsiIntegrand n lam x).re
      = Real.cos (gaussianInnerX n lam x) * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2) := by
  have hre :
      (((( (-∑ i : Fin n, x i ^ (2 : Nat)) / 2 : ℝ)) : ℂ)
        + (gaussianInnerX n lam x : ℂ) * Complex.I).re
        = (((-∑ i : Fin n, x i ^ (2 : Nat)) / 2 : ℝ)) := by
    simp [complexSquareSum_re]
  have him :
      (((( (-∑ i : Fin n, x i ^ (2 : Nat)) / 2 : ℝ)) : ℂ)
        + (gaussianInnerX n lam x : ℂ) * Complex.I).im
        = gaussianInnerX n lam x := by
    simp [complexSquareSum_im]
  rw [gaussianPsiIntegrand, Complex.exp_re]
  rw [hre, him]
  simp [mul_comm]

private lemma gaussianPsiIntegrand_im (n : ℕ) (lam : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    (gaussianPsiIntegrand n lam x).im
      = Real.sin (gaussianInnerX n lam x) * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2) := by
  have hre :
      (((( (-∑ i : Fin n, x i ^ (2 : Nat)) / 2 : ℝ)) : ℂ)
        + (gaussianInnerX n lam x : ℂ) * Complex.I).re
        = (((-∑ i : Fin n, x i ^ (2 : Nat)) / 2 : ℝ)) := by
    simp [complexSquareSum_re]
  have him :
      (((( (-∑ i : Fin n, x i ^ (2 : Nat)) / 2 : ℝ)) : ℂ)
        + (gaussianInnerX n lam x : ℂ) * Complex.I).im
        = gaussianInnerX n lam x := by
    simp [complexSquareSum_im]
  rw [gaussianPsiIntegrand, Complex.exp_im]
  rw [hre, him]
  simp [mul_comm]

private lemma gaussianPsiComplex_re (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    (gaussianPsiComplex n lam).re
      = stdGaussianAvg n (fun x => Real.cos (gaussianInnerX n lam x)) := by
  have hint : Integrable (gaussianPsiIntegrand n lam) := integrable_gaussianPsiIntegrand n lam
  unfold gaussianPsiComplex stdGaussianAvg
  calc
    Complex.re
        ((∫ x : Fin n → ℝ, gaussianPsiIntegrand n lam x) /
          ((((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)))
      = (∫ x : Fin n → ℝ, gaussianPsiIntegrand n lam x).re / ((2 * Real.pi) ^ ((n : ℝ) / 2)) := by
          exact
            Complex.div_ofReal_re
              (∫ x : Fin n → ℝ, gaussianPsiIntegrand n lam x)
              ((2 * Real.pi) ^ ((n : ℝ) / 2))
    _ = (∫ x : Fin n → ℝ, (gaussianPsiIntegrand n lam x).re) / ((2 * Real.pi) ^ ((n : ℝ) / 2)) := by
          have hreInt :
              (∫ x : Fin n → ℝ, gaussianPsiIntegrand n lam x).re
                = ∫ x : Fin n → ℝ, (gaussianPsiIntegrand n lam x).re := by
            simpa using (integral_re hint).symm
          rw [hreInt]
    _ = (∫ x : Fin n → ℝ,
            Real.cos (gaussianInnerX n lam x)
              * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2))
          / ((2 * Real.pi) ^ ((n : ℝ) / 2)) := by
            congr 1
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun x => gaussianPsiIntegrand_re n lam x)
    _ = ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ *
          ∫ x : Fin n → ℝ,
            Real.cos (gaussianInnerX n lam x)
              * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2) := by
            rw [div_eq_mul_inv, mul_comm]
    _ = stdGaussianAvg n (fun x => Real.cos (gaussianInnerX n lam x)) := by
          rfl

private lemma gaussianPsiComplex_im (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    (gaussianPsiComplex n lam).im
      = stdGaussianAvg n (fun x => Real.sin (gaussianInnerX n lam x)) := by
  have hint : Integrable (gaussianPsiIntegrand n lam) := integrable_gaussianPsiIntegrand n lam
  unfold gaussianPsiComplex stdGaussianAvg
  calc
    Complex.im
        ((∫ x : Fin n → ℝ, gaussianPsiIntegrand n lam x) /
          ((((2 * Real.pi) ^ ((n : ℝ) / 2) : ℝ) : ℂ)))
      = (∫ x : Fin n → ℝ, gaussianPsiIntegrand n lam x).im / ((2 * Real.pi) ^ ((n : ℝ) / 2)) := by
          exact
            Complex.div_ofReal_im
              (∫ x : Fin n → ℝ, gaussianPsiIntegrand n lam x)
              ((2 * Real.pi) ^ ((n : ℝ) / 2))
    _ = (∫ x : Fin n → ℝ, (gaussianPsiIntegrand n lam x).im) / ((2 * Real.pi) ^ ((n : ℝ) / 2)) := by
          have himInt :
              (∫ x : Fin n → ℝ, gaussianPsiIntegrand n lam x).im
                = ∫ x : Fin n → ℝ, (gaussianPsiIntegrand n lam x).im := by
            simpa using (integral_im hint).symm
          rw [himInt]
    _ = (∫ x : Fin n → ℝ,
            Real.sin (gaussianInnerX n lam x)
              * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2))
          / ((2 * Real.pi) ^ ((n : ℝ) / 2)) := by
            congr 1
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun x => gaussianPsiIntegrand_im n lam x)
    _ = ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ *
          ∫ x : Fin n → ℝ,
            Real.sin (gaussianInnerX n lam x)
              * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2) := by
            rw [div_eq_mul_inv, mul_comm]
    _ = stdGaussianAvg n (fun x => Real.sin (gaussianInnerX n lam x)) := by
          rfl

/-- The Gaussian quadratic-characteristic function used in the MOO comparison,
written via its real and imaginary parts:
`E[cos(gaussianInnerX)] + i E[sin(gaussianInnerX)]`. This is the exact package
needed to combine the MOO cosine/sine comparison with the Gaussian modulus
estimate from the text. -/
def gaussianPsi (n : ℕ) (lam : Fin n → Fin n → ℝ) : ℂ :=
  stdGaussianAvg n (fun x => Real.cos (gaussianInnerX n lam x)) +
    stdGaussianAvg n (fun x => Real.sin (gaussianInnerX n lam x)) * Complex.I

lemma gaussianPsi_re (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    (gaussianPsi n lam).re = stdGaussianAvg n (fun x => Real.cos (gaussianInnerX n lam x)) := by
  simp [gaussianPsi]

lemma gaussianPsi_im (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    (gaussianPsi n lam).im = stdGaussianAvg n (fun x => Real.sin (gaussianInnerX n lam x)) := by
  simp [gaussianPsi]

lemma gaussianPsi_eq_gaussianPsiComplex (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    gaussianPsi n lam = gaussianPsiComplex n lam := by
  apply Complex.ext <;> simp [gaussianPsi_re, gaussianPsi_im, gaussianPsiComplex_re, gaussianPsiComplex_im]

lemma gaussianInnerX_eq_half_inner_toEuclideanLin (n : ℕ)
    (lam : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    gaussianInnerX n lam
        x =
      (1 / 2 : ℝ) *
        inner ℝ (WithLp.toLp 2 x)
          (Matrix.toEuclideanLin (gaussianMatrix n lam) (WithLp.toLp 2 x)) := by
  rw [Matrix.toLpLin_toLp]
  rw [gaussianInnerX_eq_half_dotProduct_mulVec]
  simp [PiLp.inner_apply, RCLike.inner_apply, dotProduct, mul_comm]

/-- The k-th moment of X_λ over Rademacher signs: μ_k(λ) = E[X_λ^k]. -/
def momentX (n : ℕ) (lam : Fin n → Fin n → ℝ) (k : ℕ) : ℝ :=
  (↑(2 ^ n : ℕ) : ℝ)⁻¹ * ∑ σ : Fin n → Fin 2, (innerX n lam σ) ^ k

/-- The matrix-model phase `innerX` is continuous in the edge weights. -/
private lemma continuous_innerX (n : ℕ) (σ : Fin n → Fin 2) :
    Continuous (fun lam : Fin n → Fin n → ℝ => innerX n lam σ) := by
  unfold innerX
  refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro i hi
  refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro j hj
  by_cases hij : i < j
  · let fij : Continuous fun lam : Fin n → Fin n → ℝ => lam i j :=
      (continuous_apply j).comp (continuous_apply i)
    simpa [hij, mul_assoc] using
      (fij.mul continuous_const).mul continuous_const
  · simpa [hij] using (continuous_const : Continuous fun _ : Fin n → Fin n → ℝ => (0 : ℝ))

/-- The matrix-model moments vary continuously with the edge weights. -/
lemma continuous_momentX (n k : ℕ) :
    Continuous (fun lam : Fin n → Fin n → ℝ => momentX n lam k) := by
  unfold momentX
  have hsum :
      Continuous (fun lam : Fin n → Fin n → ℝ =>
        ∑ σ : Fin n → Fin 2, (innerX n lam σ) ^ k) := by
    refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n → Fin 2))) ?_
    intro σ hσ
    exact (continuous_innerX n σ).pow k
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    continuous_const.mul hsum

/-- The cubic triangle sum is a continuous polynomial in the matrix entries. -/
lemma continuous_cubicT (n : ℕ) :
    Continuous (cubicT n) := by
  unfold cubicT
  refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro i hi
  refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro j hj
  refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n))) ?_
  intro k hk
  by_cases hijk : i < j ∧ j < k
  · let fij : Continuous fun lam : Fin n → Fin n → ℝ => lam i j :=
      (continuous_apply j).comp (continuous_apply i)
    let fik : Continuous fun lam : Fin n → Fin n → ℝ => lam i k :=
      (continuous_apply k).comp (continuous_apply i)
    let fjk : Continuous fun lam : Fin n → Fin n → ℝ => lam j k :=
      (continuous_apply k).comp (continuous_apply j)
    simpa [hijk, mul_assoc, mul_left_comm, mul_comm] using
      (fij.mul fik).mul fjk
  · simpa [hijk] using
      (continuous_const : Continuous fun _ : Fin n → Fin n → ℝ => (0 : ℝ))

/-- Linear Rademacher form on vertex weights. -/
def linearX (n : ℕ) (x : Fin n → ℝ) (σ : Fin n → Fin 2) : ℝ :=
  ∑ i : Fin n, x i * (signOf (σ i) : ℝ)

/-- The strict-upper indicator supported on a single edge `(u,v)`. -/
def singleEdgeLam {n : ℕ} (u v : Fin n) : Fin n → Fin n → ℝ :=
  fun i j => if i = u ∧ j = v then 1 else 0

/-- Sum of the two-edge products over triangles containing the ordered pair `(u,v)`. -/
def triangleThroughPair (n : ℕ) (B : Fin n → Fin n → ℝ) (u v : Fin n) : ℝ :=
  (∑ k : Fin n, if k < u then B k u * B k v else 0)
    + (∑ k : Fin n, if u < k ∧ k < v then B u k * B k v else 0)
    + (∑ k : Fin n, if v < k then B u k * B v k else 0)

/-! ### Internal last-coordinate peeling identities -/

/-- Split a sign vector on `Fin (n+1)` into its first `n` coordinates and last
coordinate. -/
private def signVecLastEquiv (n : ℕ) : (Fin (n + 1) → Fin 2) ≃ (Fin n → Fin 2) × Fin 2 where
  toFun := fun τ => (Fin.init (α := fun _ => Fin 2) τ, τ (Fin.last n))
  invFun := fun p => Fin.snoc (α := fun _ => Fin 2) p.1 p.2
  left_inv := by
    intro τ
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc]
    · intro j
      simp [Fin.snoc, Fin.init]
  right_inv := by
    intro p
    rcases p with ⟨σ, b⟩
    refine Prod.ext ?_ ?_
    · funext i
      simp [Fin.init]
    · simp [Fin.snoc]

/-- Expand a sum over sign vectors on `Fin (n+1)` by the last coordinate. -/
lemma sum_signVec_split_last (n : ℕ) (g : (Fin (n + 1) → Fin 2) → ℝ) :
    (∑ τ : Fin (n + 1) → Fin 2, g τ)
      = ∑ σ : Fin n → Fin 2, ∑ b : Fin 2, g (Fin.snoc (α := fun _ => Fin 2) σ b) := by
  calc
    (∑ τ : Fin (n + 1) → Fin 2, g τ)
        = ∑ p : (Fin n → Fin 2) × Fin 2, g ((signVecLastEquiv n).symm p) := by
            exact Fintype.sum_equiv (signVecLastEquiv n)
              (fun τ : Fin (n + 1) → Fin 2 => g τ)
              (fun p : (Fin n → Fin 2) × Fin 2 => g ((signVecLastEquiv n).symm p))
              (by intro τ; simp [signVecLastEquiv])
    _ = ∑ σ : Fin n → Fin 2, ∑ b : Fin 2, g (Fin.snoc (α := fun _ => Fin 2) σ b) := by
          simpa [signVecLastEquiv] using
            (Fintype.sum_prod_type
              (f := fun p : (Fin n → Fin 2) × Fin 2 => g ((signVecLastEquiv n).symm p)))

/-- Average over sign vectors by first averaging over the last sign. -/
lemma avgSigns_split_last (n : ℕ) (g : (Fin (n + 1) → Fin 2) → ℝ) :
    avgSigns (n + 1) g
      = avgSigns n
          (fun σ => ((∑ b : Fin 2, g (Fin.snoc (α := fun _ => Fin 2) σ b)) / 2 : ℝ)) := by
  unfold avgSigns
  rw [sum_signVec_split_last]
  have hpow : (↑(2 ^ (n + 1) : ℕ) : ℝ) = (↑(2 ^ n : ℕ) : ℝ) * 2 := by
    norm_num [pow_succ]
  rw [hpow, mul_inv_rev]
  calc
    (2 : ℝ)⁻¹ * (↑(2 ^ n : ℕ) : ℝ)⁻¹ * ∑ σ : Fin n → Fin 2, ∑ b : Fin 2, g (Fin.snoc (α := fun _ => Fin 2) σ b)
        = (↑(2 ^ n : ℕ) : ℝ)⁻¹ * ((2 : ℝ)⁻¹ * ∑ σ : Fin n → Fin 2, ∑ b : Fin 2, g (Fin.snoc (α := fun _ => Fin 2) σ b)) := by
            ring
    _ = (↑(2 ^ n : ℕ) : ℝ)⁻¹ * (∑ σ : Fin n → Fin 2, ((∑ b : Fin 2, g (Fin.snoc (α := fun _ => Fin 2) σ b)) / 2 : ℝ)) := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          simp [div_eq_mul_inv, mul_comm]

lemma linearX_snoc_last (n : ℕ) (x : Fin n → ℝ) (a : ℝ)
    (σ : Fin n → Fin 2) (b : Fin 2) :
    linearX (n + 1) (Fin.snoc (α := fun _ => ℝ) x a) (Fin.snoc (α := fun _ => Fin 2) σ b)
      = linearX n x σ + a * (signOf b : ℝ) := by
  unfold linearX
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc, add_comm]

lemma signOf_sq (b : Fin 2) : ((signOf b : ℝ) ^ (2 : Nat)) = 1 := by
  fin_cases b <;> norm_num [signOf]

lemma sum_linear_over_last_sign (A Y : ℝ) :
    (∑ b : Fin 2, (A + (signOf b : ℝ) * Y)) = 2 * A := by
  rw [Fin.sum_univ_two]
  norm_num [signOf]
  ring

lemma sum_square_over_last_sign (A Y : ℝ) :
    (∑ b : Fin 2, (A + (signOf b : ℝ) * Y) ^ (2 : Nat))
      = 2 * (A ^ (2 : Nat) + Y ^ (2 : Nat)) := by
  rw [Fin.sum_univ_two]
  norm_num [signOf]
  ring

lemma sum_cube_over_last_sign (A Y : ℝ) :
    (∑ b : Fin 2, (A + (signOf b : ℝ) * Y) ^ (3 : Nat))
      = 2 * (A ^ (3 : Nat) + 3 * A * Y ^ (2 : Nat)) := by
  rw [Fin.sum_univ_two]
  norm_num [signOf]
  ring

lemma sum_sq_snoc (n : ℕ) (x : Fin n → ℝ) (a : ℝ) :
    (∑ i : Fin (n + 1), (Fin.snoc (α := fun _ => ℝ) x a i) ^ (2 : Nat))
      = (∑ i : Fin n, x i ^ (2 : Nat)) + a ^ (2 : Nat) := by
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc]

lemma sum_fourth_snoc (n : ℕ) (x : Fin n → ℝ) (a : ℝ) :
    (∑ i : Fin (n + 1), (Fin.snoc (α := fun _ => ℝ) x a i) ^ (4 : Nat))
      = (∑ i : Fin n, x i ^ (4 : Nat)) + a ^ (4 : Nat) := by
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc]

lemma innerX_snoc_last (n : ℕ) (lam : Fin (n + 1) → Fin (n + 1) → ℝ)
    (σ : Fin n → Fin 2) (b : Fin 2) :
    innerX (n + 1) lam (Fin.snoc (α := fun _ => Fin 2) σ b)
      = innerX n (minorLamLast lam) σ
          + (signOf b : ℝ) * linearX n (lastColLam lam) σ := by
  unfold innerX linearX minorLamLast lastColLam
  rw [strictUpper_sum_split_last]
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        if i < j then
          lam i.castSucc j.castSucc * (signOf ((Fin.snoc (α := fun _ => Fin 2) σ b) i.castSucc) : ℝ)
            * (signOf ((Fin.snoc (α := fun _ => Fin 2) σ b) j.castSucc) : ℝ)
        else 0)
      + ∑ i : Fin n,
          lam i.castSucc (Fin.last n) * (signOf ((Fin.snoc (α := fun _ => Fin 2) σ b) i.castSucc) : ℝ)
            * (signOf ((Fin.snoc (α := fun _ => Fin 2) σ b) (Fin.last n)) : ℝ)
        =
      (∑ i : Fin n, ∑ j : Fin n,
        if i < j then lam i.castSucc j.castSucc * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0)
      + ∑ i : Fin n, lam i.castSucc (Fin.last n) * (signOf (σ i) : ℝ) * (signOf b : ℝ) := by
          simp [Fin.snoc]
    _ = innerX n (minorLamLast lam) σ
          + ∑ i : Fin n, lastColLam lam i * (signOf (σ i) : ℝ) * (signOf b : ℝ) := by
            rfl
    _ = innerX n (minorLamLast lam) σ
          + (signOf b : ℝ) * linearX n (lastColLam lam) σ := by
            congr 1
            calc
              ∑ i : Fin n, lastColLam lam i * (signOf (σ i) : ℝ) * (signOf b : ℝ)
                  = (signOf b : ℝ) * ∑ i : Fin n, lastColLam lam i * (signOf (σ i) : ℝ) := by
                      rw [Finset.mul_sum]
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      ring
              _ = (signOf b : ℝ) * linearX n (lastColLam lam) σ := by
                    rfl

lemma sum_fourth_over_last_sign (A Y : ℝ) :
    (∑ b : Fin 2, (A + (signOf b : ℝ) * Y) ^ (4 : Nat))
      = 2 * (A ^ (4 : Nat) + 6 * A ^ (2 : Nat) * Y ^ (2 : Nat) + Y ^ (4 : Nat)) := by
  rw [Fin.sum_univ_two]
  norm_num [signOf]
  ring

lemma sum_sixth_over_last_sign (A Y : ℝ) :
    (∑ b : Fin 2, (A + (signOf b : ℝ) * Y) ^ (6 : Nat))
      = 2 * (A ^ (6 : Nat) + 15 * A ^ (4 : Nat) * Y ^ (2 : Nat)
          + 15 * A ^ (2 : Nat) * Y ^ (4 : Nat) + Y ^ (6 : Nat)) := by
  rw [Fin.sum_univ_two]
  norm_num [signOf]
  ring

lemma sum_eighth_over_last_sign (A Y : ℝ) :
    (∑ b : Fin 2, (A + (signOf b : ℝ) * Y) ^ (8 : Nat))
      = 2 * (A ^ (8 : Nat) + 28 * A ^ (6 : Nat) * Y ^ (2 : Nat)
          + 70 * A ^ (4 : Nat) * Y ^ (4 : Nat)
          + 28 * A ^ (2 : Nat) * Y ^ (6 : Nat) + Y ^ (8 : Nat)) := by
  rw [Fin.sum_univ_two]
  norm_num [signOf]
  ring

lemma avgSigns_congr (n : ℕ) {f g : (Fin n → Fin 2) → ℝ} (hfg : ∀ σ, f σ = g σ) :
    avgSigns n f = avgSigns n g := by
  unfold avgSigns
  refine congrArg ((↑(2 ^ n : ℕ) : ℝ)⁻¹ * ·) ?_
  refine Finset.sum_congr rfl ?_
  intro σ hσ
  exact hfg σ

lemma avgSigns_const_aux (n : ℕ) (c : ℝ) :
    avgSigns n (fun _ : Fin n → Fin 2 => c) = c := by
  unfold avgSigns
  simp

lemma avgSigns_add_aux (n : ℕ) (f g : (Fin n → Fin 2) → ℝ) :
    avgSigns n (fun σ => f σ + g σ) = avgSigns n f + avgSigns n g := by
  unfold avgSigns
  rw [Finset.sum_add_distrib]
  ring

private lemma avgSigns_cos_linearX_eq_prod (n : ℕ) (x : Fin n → ℝ) :
    avgSigns n (fun σ => Real.cos (linearX n x σ)) = ∏ i : Fin n, Real.cos (x i) := by
  induction n with
  | zero =>
      simp [avgSigns, linearX]
  | succ n ih =>
      let x₀ : Fin n → ℝ := Fin.init (α := fun _ => ℝ) x
      let a : ℝ := x (Fin.last n)
      have hx : Fin.snoc (α := fun _ => ℝ) x₀ a = x := by
        funext i
        refine Fin.lastCases ?_ ?_ i
        · simp [a, Fin.snoc]
        · intro j
          simp [x₀, Fin.snoc, Fin.init]
      rw [← hx, avgSigns_split_last]
      have hpoint :
          (fun σ : Fin n → Fin 2 =>
            ((∑ b : Fin 2,
                Real.cos
                  (linearX (n + 1) (Fin.snoc (α := fun _ => ℝ) x₀ a)
                    (Fin.snoc (α := fun _ => Fin 2) σ b))) / 2 : ℝ))
            =
          (fun σ : Fin n → Fin 2 => Real.cos (linearX n x₀ σ) * Real.cos a) := by
        funext σ
        have hsum_cos :
            (∑ b : Fin 2, Real.cos (linearX n x₀ σ + (signOf b : ℝ) * a))
              = 2 * Real.cos (linearX n x₀ σ) * Real.cos a := by
          rw [Fin.sum_univ_two]
          norm_num [signOf]
          have h := Real.cos_add_cos (linearX n x₀ σ - a) (linearX n x₀ σ + a)
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, Real.cos_neg] using h
        have hs := congrArg (fun t : ℝ => t / 2) hsum_cos
        simpa [linearX_snoc_last, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs
      have hmul_const :
          avgSigns n (fun σ => Real.cos (linearX n x₀ σ) * Real.cos a)
            = avgSigns n (fun σ => Real.cos (linearX n x₀ σ)) * Real.cos a := by
        unfold avgSigns
        rw [show (∑ σ, (fun σ => Real.cos (linearX n x₀ σ) * Real.cos a) σ)
              = (∑ σ, Real.cos (linearX n x₀ σ)) * Real.cos a by
                symm
                exact Finset.sum_mul Finset.univ (fun σ => Real.cos (linearX n x₀ σ)) (Real.cos a)]
        ring
      rw [avgSigns_congr _ (fun σ => congrFun hpoint σ), hmul_const, ih]
      symm
      simpa [x₀, a] using
        (Fin.prod_univ_castSucc
          (f := fun i : Fin (n + 1) => Real.cos ((Fin.snoc (α := fun _ => ℝ) x₀ a) i)))

lemma avgSigns_cos_sq_linearX_eq_half_one_add_half_prod (n : ℕ) (x : Fin n → ℝ) :
    avgSigns n (fun σ => Real.cos (linearX n x σ) ^ (2 : Nat))
      = 1 / 2 + 1 / 2 * ∏ i : Fin n, Real.cos (2 * x i) := by
  have hrew :
      avgSigns n (fun σ => Real.cos (linearX n x σ) ^ (2 : Nat))
        = avgSigns n (fun σ => (1 + Real.cos (2 * linearX n x σ)) / 2) := by
    apply avgSigns_congr
    intro σ
    have hcos_two :
        Real.cos (2 * linearX n x σ) = 2 * Real.cos (linearX n x σ) ^ (2 : Nat) - 1 := by
      simpa [pow_two, two_mul, mul_assoc] using (Real.cos_two_mul (linearX n x σ))
    nlinarith
  have hdouble :
      avgSigns n (fun σ => Real.cos (2 * linearX n x σ))
        = avgSigns n (fun σ => Real.cos (linearX n (fun i => 2 * x i) σ)) := by
    apply avgSigns_congr
    intro σ
    have hlin : linearX n (fun i => 2 * x i) σ = 2 * linearX n x σ := by
      unfold linearX
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    rw [hlin]
  have hdiv :
      avgSigns n (fun σ => (1 + Real.cos (2 * linearX n x σ)) / 2)
        = avgSigns n (fun σ => 1 + Real.cos (2 * linearX n x σ)) / 2 := by
    simp [avgSigns, div_eq_mul_inv, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
  rw [hrew, hdiv, avgSigns_add_aux, avgSigns_const_aux]
  rw [hdouble, avgSigns_cos_linearX_eq_prod (n := n) (x := fun i => 2 * x i)]
  ring

lemma momentX_four_peel_last_raw (n : ℕ) (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    momentX (n + 1) lam 4
      = avgSigns n (fun σ =>
          innerX n (minorLamLast lam) σ ^ (4 : Nat)
            + 6 * innerX n (minorLamLast lam) σ ^ (2 : Nat)
                * linearX n (lastColLam lam) σ ^ (2 : Nat)
            + linearX n (lastColLam lam) σ ^ (4 : Nat)) := by
  let B : Fin n → Fin n → ℝ := minorLamLast lam
  let x : Fin n → ℝ := lastColLam lam
  have hsplit :
      (∑ τ : Fin (n + 1) → Fin 2, (innerX (n + 1) lam τ) ^ (4 : Nat))
        =
      ∑ σ : Fin n → Fin 2, ∑ b : Fin 2,
        (innerX (n + 1) lam (Fin.snoc (α := fun _ => Fin 2) σ b)) ^ (4 : Nat) := by
    simpa using
      (sum_signVec_split_last n (fun τ : Fin (n + 1) → Fin 2 => (innerX (n + 1) lam τ) ^ (4 : Nat)))
  unfold momentX avgSigns
  rw [hsplit]
  calc
    (↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹
        * ∑ σ : Fin n → Fin 2, ∑ b : Fin 2,
            (innerX (n + 1) lam (Fin.snoc (α := fun _ => Fin 2) σ b)) ^ (4 : Nat)
      =
    (↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹
        * ∑ σ : Fin n → Fin 2, ∑ b : Fin 2,
            (innerX n B σ + (signOf b : ℝ) * linearX n x σ) ^ (4 : Nat) := by
              refine congrArg ((↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹ * ·) ?_
              refine Finset.sum_congr rfl ?_
              intro σ hσ
              refine Finset.sum_congr rfl ?_
              intro b hb
              rw [innerX_snoc_last]
    _ =
      (↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹
        * ∑ σ : Fin n → Fin 2,
            2 * (innerX n B σ ^ (4 : Nat)
              + 6 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (2 : Nat)
              + linearX n x σ ^ (4 : Nat)) := by
                refine congrArg ((↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹ * ·) ?_
                refine Finset.sum_congr rfl ?_
                intro σ hσ
                rw [sum_fourth_over_last_sign]
    _ =
      (↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹
        * (2 * ∑ σ : Fin n → Fin 2,
            (innerX n B σ ^ (4 : Nat)
              + 6 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (2 : Nat)
              + linearX n x σ ^ (4 : Nat))) := by
                congr 1
                rw [Finset.mul_sum]
    _ =
      ((↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹ * 2)
        * ∑ σ : Fin n → Fin 2,
            (innerX n B σ ^ (4 : Nat)
              + 6 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (2 : Nat)
              + linearX n x σ ^ (4 : Nat)) := by
                ring
    _ =
      (↑(2 ^ n : ℕ) : ℝ)⁻¹
        * ∑ σ : Fin n → Fin 2,
            (innerX n B σ ^ (4 : Nat)
              + 6 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (2 : Nat)
              + linearX n x σ ^ (4 : Nat)) := by
                have hpow : (↑(2 ^ (n + 1) : ℕ) : ℝ) = (↑(2 ^ n : ℕ) : ℝ) * 2 := by
                  norm_num [pow_succ]
                rw [hpow]
                field_simp
    _ =
      avgSigns n (fun σ =>
        innerX n B σ ^ (4 : Nat)
          + 6 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (2 : Nat)
          + linearX n x σ ^ (4 : Nat)) := by
            rfl

lemma abs_pow_even (x : ℝ) (k : ℕ) : |x| ^ (2 * k) = x ^ (2 * k) := by
  rw [pow_mul, pow_mul]
  rw [sq_abs]

/-- The 5th cumulant phase P_5(λ) = κ_5(λ)/120.
    Using the moment-cumulant relation (for zero-mean):
    κ_5 = μ_5 - 10·μ_3·μ_2. -/
def quinticP5 (n : ℕ) (lam : Fin n → Fin n → ℝ) : ℝ :=
  (momentX n lam 5 - 10 * momentX n lam 3 * momentX n lam 2) / 120

/-- The quintic correction is a continuous polynomial in the matrix entries. -/
lemma continuous_quinticP5 (n : ℕ) :
    Continuous (quinticP5 n) := by
  unfold quinticP5
  have hmain :
      Continuous (fun lam : Fin n → Fin n → ℝ =>
        momentX n lam 5 - 10 * momentX n lam 3 * momentX n lam 2) := by
    exact (continuous_momentX n 5).sub
      ((continuous_const.mul (continuous_momentX n 3)).mul (continuous_momentX n 2))
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    ((continuous_const : Continuous fun _ : Fin n → Fin n → ℝ => ((120 : ℝ)⁻¹)).mul hmain)

/-- The Gaussian scale A_n(t) = 2^{2d-n+1} (8πt)^{-d/2}. -/
def gaussianScale (n : ℕ) (t : ℝ) : ℝ :=
  2 ^ (2 * dim n - n + 1 : ℤ) * (8 * π * t) ^ (-(dim n : ℝ) / 2)

/-- The count scale 2^{4nt} A_n(t) appearing in `cor:cn3-count-asym`. -/
def countScale (n t : ℕ) : ℝ :=
  (2 : ℝ) ^ (4 * n * t) * gaussianScale n ↑t

lemma gaussianScale_pos (n : ℕ) {t : ℝ} (ht : 0 < t) : 0 < gaussianScale n t := by
  unfold gaussianScale
  positivity
