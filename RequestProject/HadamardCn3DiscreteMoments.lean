import RequestProject.HadamardCn3Moments

/-!
# Discrete Sign Moment Layer For The Cn^3 Formalization

This module packages the reusable discrete sign-average identities and low-order
moment estimates that feed the residual, local-gap, and fixed-`n` layers.

It contains the cubic and quintic pointwise controls for the discrete statistics
attached to `innerX`, but it does not contain the
Mossel-O'Donnell-Oleszkiewicz invariance-principle material itself.
-/

noncomputable section

open Real MeasureTheory Filter Finset Topology
open scoped Pointwise

set_option linter.unusedVariables false

lemma sNorm_nonneg (n : ℕ) (lam : Fin n → Fin n → ℝ) : 0 ≤ sNorm n lam := by
  unfold sNorm
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> positivity

lemma avgSigns_const (n : ℕ) (c : ℝ) :
    avgSigns n (fun _ : Fin n → Fin 2 => c) = c := by
  unfold avgSigns
  simp

/-!
## Basic Discrete Averages
-/

lemma avgSigns_add (n : ℕ) (f g : (Fin n → Fin 2) → ℝ) :
    avgSigns n (fun σ => f σ + g σ) = avgSigns n f + avgSigns n g := by
  unfold avgSigns
  rw [Finset.sum_add_distrib]
  ring

lemma avgSigns_mul_const_left (n : ℕ) (c : ℝ) (f : (Fin n → Fin 2) → ℝ) :
    avgSigns n (fun σ => c * f σ) = c * avgSigns n f := by
  simp [avgSigns, Finset.mul_sum, mul_assoc, mul_comm]

lemma avgSigns_sum {n : ℕ} {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → (Fin n → Fin 2) → ℝ) :
    avgSigns n (fun σ => s.sum (fun a => f a σ)) = s.sum (fun a => avgSigns n (f a)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [avgSigns_const]
  | @insert a s ha ih =>
      simp [ha, avgSigns_add, ih]

lemma avgSigns_linearX_sq (n : ℕ) (x : Fin n → ℝ) :
    avgSigns n (fun σ => linearX n x σ ^ (2 : Nat))
      = ∑ i : Fin n, x i ^ (2 : Nat) := by
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
      rw [← hx]
      rw [avgSigns_split_last]
      have hpoint :
          (fun σ : Fin n → Fin 2 =>
            ((∑ b : Fin 2,
                (linearX (n + 1) (Fin.snoc (α := fun _ => ℝ) x₀ a)
                  (Fin.snoc (α := fun _ => Fin 2) σ b)) ^ (2 : Nat)) / 2 : ℝ))
            =
          (fun σ : Fin n → Fin 2 => linearX n x₀ σ ^ (2 : Nat) + a ^ (2 : Nat)) := by
        funext σ
        have hs :=
          congrArg (fun t : ℝ => t / 2) (sum_square_over_last_sign (linearX n x₀ σ) a)
        simpa [linearX_snoc_last, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hs
      rw [hpoint, avgSigns_add, avgSigns_const, ih]
      symm
      simpa [x₀, a] using sum_sq_snoc n x₀ a

lemma avgSigns_linearX_four (n : ℕ) (x : Fin n → ℝ) :
    avgSigns n (fun σ => linearX n x σ ^ (4 : Nat))
      = 3 * (∑ i : Fin n, x i ^ (2 : Nat)) ^ (2 : Nat)
          - 2 * (∑ i : Fin n, x i ^ (4 : Nat)) := by
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
      rw [← hx]
      rw [avgSigns_split_last]
      have hpoint :
          (fun σ : Fin n → Fin 2 =>
            ((∑ b : Fin 2,
                (linearX (n + 1) (Fin.snoc (α := fun _ => ℝ) x₀ a)
                  (Fin.snoc (α := fun _ => Fin 2) σ b)) ^ (4 : Nat)) / 2 : ℝ))
            =
          (fun σ : Fin n → Fin 2 =>
            linearX n x₀ σ ^ (4 : Nat)
              + 6 * a ^ (2 : Nat) * linearX n x₀ σ ^ (2 : Nat)
              + a ^ (4 : Nat)) := by
        funext σ
        have hs :=
          congrArg (fun t : ℝ => t / 2) (sum_fourth_over_last_sign (linearX n x₀ σ) a)
        simpa [linearX_snoc_last, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hs
      rw [hpoint]
      rw [avgSigns_add, avgSigns_add, avgSigns_const, avgSigns_mul_const_left, avgSigns_linearX_sq, ih]
      symm
      have hs2 : (∑ i : Fin (n + 1), (Fin.snoc (α := fun _ => ℝ) x₀ a i) ^ (2 : Nat))
            = (∑ i : Fin n, x₀ i ^ (2 : Nat)) + a ^ (2 : Nat) := sum_sq_snoc n x₀ a
      have hs4 : (∑ i : Fin (n + 1), (Fin.snoc (α := fun _ => ℝ) x₀ a i) ^ (4 : Nat))
            = (∑ i : Fin n, x₀ i ^ (4 : Nat)) + a ^ (4 : Nat) := sum_fourth_snoc n x₀ a
      rw [hs2, hs4]
      ring

lemma linearX_sq_eq_diag_add_offdiag (n : ℕ) (x : Fin n → ℝ) (σ : Fin n → Fin 2) :
    linearX n x σ ^ (2 : Nat)
      = (∑ i : Fin n, x i ^ (2 : Nat))
          + 2 * (∑ i : Fin n, ∑ j : Fin n,
              if i < j then
                x i * x j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ)
              else 0) := by
  induction n with
  | zero =>
      simp [linearX]
  | succ n ih =>
      let x₀ : Fin n → ℝ := Fin.init (α := fun _ => ℝ) x
      let a : ℝ := x (Fin.last n)
      let σ₀ : Fin n → Fin 2 := Fin.init (α := fun _ => Fin 2) σ
      let b : Fin 2 := σ (Fin.last n)
      have hx : Fin.snoc (α := fun _ => ℝ) x₀ a = x := by
        funext i
        refine Fin.lastCases ?_ ?_ i
        · simp [a, Fin.snoc]
        · intro j
          simp [x₀, Fin.snoc, Fin.init]
      have hσ : Fin.snoc (α := fun _ => Fin 2) σ₀ b = σ := by
        funext i
        refine Fin.lastCases ?_ ?_ i
        · simp [b, Fin.snoc]
        · intro j
          simp [σ₀, Fin.snoc, Fin.init]
      rw [← hx, ← hσ]
      have hcross :
          linearX n x₀ σ₀ * (a * (signOf b : ℝ))
            = ∑ i : Fin n, x₀ i * a * (signOf (σ₀ i) : ℝ) * (signOf b : ℝ) := by
        unfold linearX
        calc
          (∑ i : Fin n, x₀ i * (signOf (σ₀ i) : ℝ)) * (a * (signOf b : ℝ))
              = ∑ i : Fin n, (x₀ i * (signOf (σ₀ i) : ℝ)) * (a * (signOf b : ℝ)) := by
                  rw [Finset.sum_mul]
          _ = ∑ i : Fin n, x₀ i * a * (signOf (σ₀ i) : ℝ) * (signOf b : ℝ) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
      calc
        linearX (n + 1) (Fin.snoc (α := fun _ => ℝ) x₀ a) (Fin.snoc (α := fun _ => Fin 2) σ₀ b) ^ (2 : Nat)
            = (linearX n x₀ σ₀ + a * (signOf b : ℝ)) ^ (2 : Nat) := by
                rw [linearX_snoc_last]
        _ = linearX n x₀ σ₀ ^ (2 : Nat)
              + 2 * (linearX n x₀ σ₀ * (a * (signOf b : ℝ)))
              + (a * (signOf b : ℝ)) ^ (2 : Nat) := by
                ring
        _ = linearX n x₀ σ₀ ^ (2 : Nat)
              + 2 * (linearX n x₀ σ₀ * (a * (signOf b : ℝ)))
              + a ^ (2 : Nat) := by
                have hsq : (a * (signOf b : ℝ)) ^ (2 : Nat) = a ^ (2 : Nat) := by
                  calc
                    (a * (signOf b : ℝ)) ^ (2 : Nat)
                        = a ^ (2 : Nat) * (signOf b : ℝ) ^ (2 : Nat) := by ring
                    _ = a ^ (2 : Nat) := by simp [signOf_sq]
                rw [hsq]
        _ = (∑ i : Fin n, x₀ i ^ (2 : Nat)
                + 2 * (∑ i : Fin n, ∑ j : Fin n,
                    if i < j then
                      x₀ i * x₀ j * (signOf (σ₀ i) : ℝ) * (signOf (σ₀ j) : ℝ)
                    else 0))
              + 2 * (∑ i : Fin n, x₀ i * a * (signOf (σ₀ i) : ℝ) * (signOf b : ℝ))
              + a ^ (2 : Nat) := by
                rw [ih, hcross]
        _ = (∑ i : Fin (n + 1), (Fin.snoc (α := fun _ => ℝ) x₀ a i) ^ (2 : Nat))
              + 2 * (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                  if i < j then
                    Fin.snoc (α := fun _ => ℝ) x₀ a i * Fin.snoc (α := fun _ => ℝ) x₀ a j *
                        (signOf ((Fin.snoc (α := fun _ => Fin 2) σ₀ b) i) : ℝ) *
                        (signOf ((Fin.snoc (α := fun _ => Fin 2) σ₀ b) j) : ℝ)
                  else 0) := by
                  have hsdiag : ∑ i : Fin (n + 1), (Fin.snoc (α := fun _ => ℝ) x₀ a i) ^ (2 : Nat)
                      = (∑ i : Fin n, x₀ i ^ (2 : Nat)) + a ^ (2 : Nat) := by
                    simpa using sum_sq_snoc n x₀ a
                  have hoff :
                      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
                          if i < j then
                            Fin.snoc (α := fun _ => ℝ) x₀ a i * Fin.snoc (α := fun _ => ℝ) x₀ a j *
                                (signOf ((Fin.snoc (α := fun _ => Fin 2) σ₀ b) i) : ℝ) *
                                (signOf ((Fin.snoc (α := fun _ => Fin 2) σ₀ b) j) : ℝ)
                          else 0)
                        =
                      (∑ i : Fin n, ∑ j : Fin n,
                          if i < j then
                            x₀ i * x₀ j * (signOf (σ₀ i) : ℝ) * (signOf (σ₀ j) : ℝ)
                          else 0)
                        + ∑ i : Fin n, x₀ i * a * (signOf (σ₀ i) : ℝ) * (signOf b : ℝ) := by
                    rw [strictUpper_sum_split_last]
                    simp [Fin.snoc]
                  rw [hsdiag, hoff]
                  ring

lemma abs_avgSigns_le_avgSigns_abs (n : ℕ) (f : (Fin n → Fin 2) → ℝ) :
    |avgSigns n f| ≤ avgSigns n (fun σ => |f σ|) := by
  have hsum :
      |∑ σ : Fin n → Fin 2, f σ| ≤ ∑ σ : Fin n → Fin 2, |f σ| := by
    simpa using
      (Finset.abs_sum_le_sum_abs
        (s := (Finset.univ : Finset (Fin n → Fin 2)))
        (f := fun σ : Fin n → Fin 2 => f σ))
  unfold avgSigns
  calc
    |(↑(2 ^ n : ℕ) : ℝ)⁻¹ * ∑ σ : Fin n → Fin 2, f σ|
        = (↑(2 ^ n : ℕ) : ℝ)⁻¹ * |∑ σ : Fin n → Fin 2, f σ| := by
            rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (↑(2 ^ n : ℕ) : ℝ)⁻¹)]
    _ ≤ (↑(2 ^ n : ℕ) : ℝ)⁻¹ * ∑ σ : Fin n → Fin 2, |f σ| := by
          gcongr

lemma momentX_four_peel_last (n : ℕ) (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    momentX (n + 1) lam 4
      = momentX n (minorLamLast lam) 4
          + 6 * avgSigns n
              (fun σ =>
                innerX n (minorLamLast lam) σ ^ (2 : Nat)
                  * linearX n (lastColLam lam) σ ^ (2 : Nat))
          + (3 * (∑ i : Fin n, (lastColLam lam i) ^ (2 : Nat)) ^ (2 : Nat)
              - 2 * ∑ i : Fin n, (lastColLam lam i) ^ (4 : Nat)) := by
  have hfun :
      (fun σ =>
        innerX n (minorLamLast lam) σ ^ (4 : Nat)
          + 6 * innerX n (minorLamLast lam) σ ^ (2 : Nat) * linearX n (lastColLam lam) σ ^ (2 : Nat)
          + linearX n (lastColLam lam) σ ^ (4 : Nat))
        =
      (fun σ =>
        innerX n (minorLamLast lam) σ ^ (4 : Nat)
          + (6 * innerX n (minorLamLast lam) σ ^ (2 : Nat) * linearX n (lastColLam lam) σ ^ (2 : Nat)
              + linearX n (lastColLam lam) σ ^ (4 : Nat))) := by
    funext σ
    ring
  have hmul :
      avgSigns n
          (fun σ =>
            6 * innerX n (minorLamLast lam) σ ^ (2 : Nat) * linearX n (lastColLam lam) σ ^ (2 : Nat))
        =
      6 * avgSigns n
          (fun σ =>
            innerX n (minorLamLast lam) σ ^ (2 : Nat) * linearX n (lastColLam lam) σ ^ (2 : Nat)) := by
    have hpoint :
        (fun σ =>
          6 * innerX n (minorLamLast lam) σ ^ (2 : Nat) * linearX n (lastColLam lam) σ ^ (2 : Nat))
          =
        (fun σ =>
          6 * (innerX n (minorLamLast lam) σ ^ (2 : Nat)
            * linearX n (lastColLam lam) σ ^ (2 : Nat))) := by
      funext σ
      ring
    rw [hpoint, avgSigns_mul_const_left]
  rw [momentX_four_peel_last_raw, hfun, avgSigns_add, avgSigns_add, hmul, avgSigns_linearX_four]
  simp [momentX, avgSigns]
  ring

private lemma sum_mul_sq_le_sum_sq_mul_sum_sq_early {α : Type} [Fintype α] [DecidableEq α]
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

private lemma avgSigns_sq_mul_sq_le_fourth_mul_fourth (n : ℕ)
    (f g : (Fin n → Fin 2) → ℝ) :
    (avgSigns n (fun σ => f σ ^ (2 : Nat) * g σ ^ (2 : Nat))) ^ (2 : Nat)
      ≤ avgSigns n (fun σ => f σ ^ (4 : Nat))
          * avgSigns n (fun σ => g σ ^ (4 : Nat)) := by
  let A : ℝ := ∑ σ : Fin n → Fin 2, f σ ^ (2 : Nat) * g σ ^ (2 : Nat)
  let B : ℝ := ∑ σ : Fin n → Fin 2, f σ ^ (4 : Nat)
  let C : ℝ := ∑ σ : Fin n → Fin 2, g σ ^ (4 : Nat)
  let M : ℝ := ((↑(2 ^ n : ℕ) : ℝ)⁻¹)
  have hB :
      (∑ σ : Fin n → Fin 2, (f σ ^ (2 : Nat)) ^ (2 : Nat)) = B := by
    dsimp [B]
    refine Finset.sum_congr rfl ?_
    intro σ hσ
    ring_nf
  have hC :
      (∑ σ : Fin n → Fin 2, (g σ ^ (2 : Nat)) ^ (2 : Nat)) = C := by
    dsimp [C]
    refine Finset.sum_congr rfl ?_
    intro σ hσ
    ring_nf
  have hsum :
      A ^ (2 : Nat) ≤ B * C := by
    have hraw :=
      (sum_mul_sq_le_sum_sq_mul_sum_sq_early
        (fun σ : Fin n → Fin 2 => f σ ^ (2 : Nat))
        (fun σ : Fin n → Fin 2 => g σ ^ (2 : Nat)))
    have hsum' :
        (∑ σ : Fin n → Fin 2, f σ ^ (2 : Nat) * g σ ^ (2 : Nat)) ^ (2 : Nat) ≤ B * C := by
      rw [← hB, ← hC]
      exact hraw
    simpa [A] using hsum'
  have hcoeff_nonneg : 0 ≤ M ^ (2 : Nat) := by
    dsimp [M]
    positivity
  have hmul :
      M ^ (2 : Nat) * A ^ (2 : Nat)
        ≤ M ^ (2 : Nat) * (B * C) := by
    exact mul_le_mul_of_nonneg_left hsum hcoeff_nonneg
  calc
    (avgSigns n (fun σ => f σ ^ (2 : Nat) * g σ ^ (2 : Nat))) ^ (2 : Nat)
        = (M * A) ^ (2 : Nat) := by
            dsimp [M]
            dsimp [A]
            unfold avgSigns
            rfl
    _ = M ^ (2 : Nat) * A ^ (2 : Nat) := by
          ring
    _ ≤ M ^ (2 : Nat) * (B * C) := hmul
    _ = (M * B) * (M * C) := by
          ring
    _ = avgSigns n (fun σ => f σ ^ (4 : Nat))
          * avgSigns n (fun σ => g σ ^ (4 : Nat)) := by
            dsimp [M]
            dsimp [B, C]
            unfold avgSigns
            rfl

/-- Internal proof of the degree-2 `L^4` hypercontractive bound used downstream. -/
theorem fixedDegreeHC_degree2_W_fourth (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (4 : Nat))
      ≤ (3 : ℝ) ^ (4 : Nat) * Cn3Torus.sqNormEdge n mu ^ (2 : Nat) := by
  have hmoment :
      ∀ m : ℕ, ∀ lam : Fin m → Fin m → ℝ,
        momentX m lam 4 ≤ (81 : ℝ) * sNorm m lam ^ (2 : Nat) := by
    intro m
    induction m with
    | zero =>
        intro lam
        simp [momentX, innerX, sNorm]
    | succ m ih =>
        intro lam
        let B : Fin m → Fin m → ℝ := minorLamLast lam
        let x : Fin m → ℝ := lastColLam lam
        let sB : ℝ := sNorm m B
        let X : ℝ := ∑ i : Fin m, x i ^ (2 : Nat)
        let mixed : ℝ :=
          avgSigns m (fun σ => innerX m B σ ^ (2 : Nat) * linearX m x σ ^ (2 : Nat))
        have hsB_nonneg : 0 ≤ sB := by
          dsimp [sB, B]
          exact sNorm_nonneg m (minorLamLast lam)
        have hX_nonneg : 0 ≤ X := by
          dsimp [X, x]
          exact Finset.sum_nonneg (fun _ _ => by positivity)
        have hμ4B :
            momentX m B 4 ≤ (81 : ℝ) * sB ^ (2 : Nat) := by
          simpa [B, sB] using ih B
        have hlin4_eq :
            avgSigns m (fun σ => linearX m x σ ^ (4 : Nat))
              = 3 * X ^ (2 : Nat) - 2 * ∑ i : Fin m, x i ^ (4 : Nat) := by
          simpa [x, X] using avgSigns_linearX_four m x
        have hlin4_le :
            avgSigns m (fun σ => linearX m x σ ^ (4 : Nat)) ≤ 3 * X ^ (2 : Nat) := by
          have hsum4_nonneg : 0 ≤ ∑ i : Fin m, x i ^ (4 : Nat) := by
            exact Finset.sum_nonneg (fun _ _ => by positivity)
          rw [hlin4_eq]
          nlinarith
        have hlin4_nonneg :
            0 ≤ avgSigns m (fun σ => linearX m x σ ^ (4 : Nat)) := by
          unfold avgSigns
          positivity
        have hmixed_nonneg : 0 ≤ mixed := by
          dsimp [mixed]
          unfold avgSigns
          positivity
        have hmixed_sq :
            mixed ^ (2 : Nat)
              ≤ avgSigns m (fun σ => innerX m B σ ^ (4 : Nat))
                  * avgSigns m (fun σ => linearX m x σ ^ (4 : Nat)) := by
          dsimp [mixed]
          have hmain :=
            avgSigns_sq_mul_sq_le_fourth_mul_fourth m
              (fun σ => innerX m B σ) (fun σ => linearX m x σ)
          simpa using hmain
        have hmixed_le :
            mixed ≤ 27 * sB * X := by
          have hμ4B' :
              avgSigns m (fun σ => innerX m B σ ^ (4 : Nat))
                ≤ (81 : ℝ) * sB ^ (2 : Nat) := by
            simpa [momentX, avgSigns] using hμ4B
          have hmixed_sq' :
              mixed ^ (2 : Nat) ≤ (27 * sB * X) ^ (2 : Nat) := by
            have hbound :
                mixed ^ (2 : Nat) ≤ ((81 : ℝ) * sB ^ (2 : Nat)) * (3 * X ^ (2 : Nat)) := by
              calc
                mixed ^ (2 : Nat)
                    ≤ avgSigns m (fun σ => innerX m B σ ^ (4 : Nat))
                        * avgSigns m (fun σ => linearX m x σ ^ (4 : Nat)) := hmixed_sq
                _ ≤ ((81 : ℝ) * sB ^ (2 : Nat)) * (3 * X ^ (2 : Nat)) := by
                      exact mul_le_mul hμ4B' hlin4_le hlin4_nonneg
                        (by positivity : 0 ≤ (81 : ℝ) * sB ^ (2 : Nat))
            have hconst : ((81 : ℝ) * sB ^ (2 : Nat)) * (3 * X ^ (2 : Nat))
                ≤ (27 * sB * X) ^ (2 : Nat) := by
              nlinarith [hsB_nonneg, hX_nonneg]
            exact le_trans hbound hconst
          have hright_nonneg : 0 ≤ 27 * sB * X := by positivity
          nlinarith [hmixed_sq', hmixed_nonneg, hright_nonneg]
        have hlast_le :
            3 * X ^ (2 : Nat) - 2 * ∑ i : Fin m, x i ^ (4 : Nat) ≤ 3 * X ^ (2 : Nat) := by
          have hsum4_nonneg : 0 ≤ ∑ i : Fin m, x i ^ (4 : Nat) := by
            exact Finset.sum_nonneg (fun _ _ => by positivity)
          nlinarith
        calc
          momentX (m + 1) lam 4
              = momentX m B 4 + 6 * mixed
                  + (3 * X ^ (2 : Nat) - 2 * ∑ i : Fin m, x i ^ (4 : Nat)) := by
                    simpa [B, x, X, mixed] using momentX_four_peel_last m lam
          _ ≤ (81 : ℝ) * sB ^ (2 : Nat) + 6 * (27 * sB * X) + 3 * X ^ (2 : Nat) := by
                nlinarith [hμ4B, hmixed_le, hlast_le]
          _ ≤ (81 : ℝ) * (sB + X) ^ (2 : Nat) := by
                nlinarith [hsB_nonneg, hX_nonneg]
          _ = (81 : ℝ) * sNorm (m + 1) lam ^ (2 : Nat) := by
                have hs :
                    sB + X = sNorm (m + 1) lam := by
                  simpa [sB, B, X, x] using (sNorm_peel_last m lam).symm
                rw [hs]
  have habs :
      (fun y => |Cn3Torus.W mu y| ^ (4 : Nat))
        = (fun y => (Cn3Torus.W mu y) ^ (4 : Nat)) := by
    funext y
    simpa using (abs_pow_even (Cn3Torus.W mu y) 2)
  rw [habs]
  have hmoment_mu :
      momentX n (matrixOfEdge n mu) 4
        ≤ (81 : ℝ) * sNorm n (matrixOfEdge n mu) ^ (2 : Nat) := by
    exact hmoment n (matrixOfEdge n mu)
  rw [momentX_eq_avgOver_W_pow, edgeLam_matrixOfEdge, sNorm_matrixOfEdge_eq] at hmoment_mu
  norm_num at hmoment_mu ⊢
  exact hmoment_mu

lemma Cn3Torus.avgOver_abs_five_le_1125_mul_sqNormEdge_fiveHalves
    (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (5 : Nat))
      ≤ (1125 : ℝ) * (Cn3Torus.sqNormEdge n mu) ^ (5 / 2 : ℝ) := by
  have hs_nonneg : 0 ≤ Cn3Torus.sqNormEdge n mu := Cn3Torus.sqNormEdge_nonneg n mu
  have havg_sq :
      (Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (5 : Nat))) ^ (2 : Nat)
        ≤
          Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (4 : Nat))
            * Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (6 : Nat)) :=
    Cn3Torus.avgOver_abs_five_sq_le_avgOver_abs_four_mul_avgOver_abs_sixth n mu
  have hfour :
      Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (4 : Nat))
        ≤ (3 : ℝ) ^ (4 : Nat) * Cn3Torus.sqNormEdge n mu ^ (2 : Nat) :=
    fixedDegreeHC_degree2_W_fourth n mu
  have hsix :
      Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (6 : Nat))
        ≤ (5 : ℝ) ^ (6 : Nat) * Cn3Torus.sqNormEdge n mu ^ (3 : Nat) :=
    fixedDegreeHC_degree2_W_sixth n mu
  have havg_nonneg : 0 ≤ Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (5 : Nat)) := by
    unfold Cn3Torus.avgOver
    exact div_nonneg
      (Finset.sum_nonneg (fun _ _ => by positivity))
      (by positivity)
  have hs52_sq :
      ((Cn3Torus.sqNormEdge n mu) ^ (5 / 2 : ℝ)) ^ (2 : Nat)
        = Cn3Torus.sqNormEdge n mu ^ (5 : Nat) := by
    calc
      ((Cn3Torus.sqNormEdge n mu) ^ (5 / 2 : ℝ)) ^ (2 : Nat)
          = (Cn3Torus.sqNormEdge n mu) ^ (5 / 2 : ℝ)
              * (Cn3Torus.sqNormEdge n mu) ^ (5 / 2 : ℝ) := by
                rw [pow_two]
      _ = (Cn3Torus.sqNormEdge n mu) ^ (5 / 2 + 5 / 2 : ℝ) := by
            rw [← Real.rpow_add_of_nonneg hs_nonneg (by positivity) (by positivity)]
      _ = (Cn3Torus.sqNormEdge n mu) ^ (5 : ℝ) := by
            have hexp : (5 / 2 + 5 / 2 : ℝ) = 5 := by norm_num
            rw [hexp]
      _ = Cn3Torus.sqNormEdge n mu ^ (5 : Nat) := by
            simp
  have hbound_sq :
      (Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (5 : Nat))) ^ (2 : Nat)
        ≤ ((1125 : ℝ) * (Cn3Torus.sqNormEdge n mu) ^ (5 / 2 : ℝ)) ^ (2 : Nat) := by
    have hfour_nonneg :
        0 ≤ Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (4 : Nat)) := by
      unfold Cn3Torus.avgOver
      exact div_nonneg
        (Finset.sum_nonneg (fun _ _ => by positivity))
        (by positivity)
    have hsix_nonneg :
        0 ≤ Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (6 : Nat)) := by
      unfold Cn3Torus.avgOver
      exact div_nonneg
        (Finset.sum_nonneg (fun _ _ => by positivity))
        (by positivity)
    calc
      (Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (5 : Nat))) ^ (2 : Nat)
          ≤
            Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (4 : Nat))
              * Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (6 : Nat)) := havg_sq
      _ ≤ ((3 : ℝ) ^ (4 : Nat) * Cn3Torus.sqNormEdge n mu ^ (2 : Nat))
            * ((5 : ℝ) ^ (6 : Nat) * Cn3Torus.sqNormEdge n mu ^ (3 : Nat)) := by
              exact mul_le_mul hfour hsix hsix_nonneg
                (by positivity : 0 ≤ (3 : ℝ) ^ (4 : Nat) * Cn3Torus.sqNormEdge n mu ^ (2 : Nat))
      _ = ((1125 : ℝ) * (Cn3Torus.sqNormEdge n mu) ^ (5 / 2 : ℝ)) ^ (2 : Nat) := by
            have hconst : (3 : ℝ) ^ (4 : Nat) * (5 : ℝ) ^ (6 : Nat) = (1125 : ℝ) ^ (2 : Nat) := by
              norm_num
            calc
              ((3 : ℝ) ^ (4 : Nat) * Cn3Torus.sqNormEdge n mu ^ (2 : Nat))
                  * ((5 : ℝ) ^ (6 : Nat) * Cn3Torus.sqNormEdge n mu ^ (3 : Nat))
                = ((3 : ℝ) ^ (4 : Nat) * (5 : ℝ) ^ (6 : Nat))
                    * Cn3Torus.sqNormEdge n mu ^ (5 : Nat) := by
                      ring
              _ = ((1125 : ℝ) ^ (2 : Nat)) * Cn3Torus.sqNormEdge n mu ^ (5 : Nat) := by
                    rw [hconst]
              _ = ((1125 : ℝ) * (Cn3Torus.sqNormEdge n mu) ^ (5 / 2 : ℝ)) ^ (2 : Nat) := by
                    calc
                      ((1125 : ℝ) ^ (2 : Nat)) * Cn3Torus.sqNormEdge n mu ^ (5 : Nat)
                          = ((1125 : ℝ) * (Cn3Torus.sqNormEdge n mu) ^ (5 / 2 : ℝ))
                              * ((1125 : ℝ) * (Cn3Torus.sqNormEdge n mu) ^ (5 / 2 : ℝ)) := by
                                rw [← hs52_sq, pow_two]
                                ring
                      _ = ((1125 : ℝ) * (Cn3Torus.sqNormEdge n mu) ^ (5 / 2 : ℝ)) ^ (2 : Nat) := by
                            rw [pow_two]
  have hright_nonneg : 0 ≤ (1125 : ℝ) * (Cn3Torus.sqNormEdge n mu) ^ (5 / 2 : ℝ) := by
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hs_nonneg _)
  nlinarith [hbound_sq, havg_nonneg, hright_nonneg]

theorem momentX_five_abs_le (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    |momentX n lam 5| ≤ (1125 : ℝ) * sNorm n lam ^ (5 / 2 : ℝ) := by
  have habs :
      |momentX n lam 5|
        ≤ avgSigns n (fun σ => |innerX n lam σ| ^ (5 : Nat)) := by
    calc
      |momentX n lam 5|
          = |avgSigns n (fun σ => innerX n lam σ ^ (5 : Nat))| := rfl
      _ ≤ avgSigns n (fun σ => |(innerX n lam σ) ^ (5 : Nat)|) :=
            abs_avgSigns_le_avgSigns_abs n (fun σ => innerX n lam σ ^ (5 : Nat))
      _ = avgSigns n (fun σ => |innerX n lam σ| ^ (5 : Nat)) := by
            congr 1
            funext σ
            rw [abs_pow]
  have havg :
      avgSigns n (fun σ => |innerX n lam σ| ^ (5 : Nat))
        = Cn3Torus.avgOver n (fun y => |Cn3Torus.W (edgeLam n lam) y| ^ (5 : Nat)) := by
    simpa using (avgSigns_abs_innerX_pow_eq_avgOver_abs_W_pow n lam 5)
  have hfive :=
    Cn3Torus.avgOver_abs_five_le_1125_mul_sqNormEdge_fiveHalves n (edgeLam n lam)
  rw [havg] at habs
  simpa [sNorm_eq_sqNormEdge] using habs.trans hfive

private lemma momentX_one_eq_zero_internal (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    momentX n lam 1 = 0 := by
  induction n with
  | zero =>
      simp [momentX, innerX]
  | succ n ih =>
      let B : Fin n → Fin n → ℝ := minorLamLast lam
      let x : Fin n → ℝ := lastColLam lam
      have hpoint :
          (fun σ : Fin n → Fin 2 =>
            ((∑ b : Fin 2,
                innerX (n + 1) lam (Fin.snoc (α := fun _ => Fin 2) σ b) ^ (1 : Nat)) / 2 : ℝ))
            =
          (fun σ : Fin n → Fin 2 => innerX n B σ) := by
        funext σ
        have hs :=
          congrArg (fun t : ℝ => t / 2)
            (sum_linear_over_last_sign (A := innerX n B σ) (Y := linearX n x σ))
        simpa [B, x, innerX_snoc_last, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hs
      change avgSigns (n + 1) (fun τ : Fin (n + 1) → Fin 2 => innerX (n + 1) lam τ ^ (1 : Nat)) = 0
      rw [avgSigns_split_last, hpoint]
      simpa [momentX, avgSigns, B] using ih B

/-!
## Discrete Sign Moment Identities

These lemmas compute the low-order discrete sign moments used later in the
cubic statistic `cubicT` and the quintic correction term `quinticP5`.
-/

/-- Weaker `2·` variants used in the third-moment computation for `innerX`. -/
private lemma avgSigns_innerX_mul_signPair (n : ℕ) (B : Fin n → Fin n → ℝ) {u v : Fin n}
    (huv : u < v) :
    avgSigns n
        (fun σ =>
          innerX n B σ * (signOf (σ u) : ℝ) * (signOf (σ v) : ℝ)) = B u v := by
  let e : Cn3Torus.Edge n := ⟨(u, v), huv⟩
  have hsum :
      ∑ σ : Fin n → Fin 2,
        innerX n B σ * (signOf (σ u) : ℝ) * (signOf (σ v) : ℝ)
          =
      ∑ y : Fin n → Bool,
        Cn3Torus.W (edgeLam n B) y * Cn3Torus.Z y e := by
    exact Fintype.sum_equiv (signVecEquivBoolVec n)
      (fun σ : Fin n → Fin 2 =>
        innerX n B σ * (signOf (σ u) : ℝ) * (signOf (σ v) : ℝ))
      (fun y : Fin n → Bool =>
        Cn3Torus.W (edgeLam n B) y * Cn3Torus.Z y e)
      (by
        intro σ
        change
          innerX n B σ * (signOf (σ u) : ℝ) * (signOf (σ v) : ℝ)
            =
          Cn3Torus.W (edgeLam n B) (signVecToBoolVec σ) * Cn3Torus.Z (signVecToBoolVec σ) e
        rw [innerX_eq_edgePhase, Cn3Torus.phase_eq_W]
        change
          Cn3Torus.W (edgeLam n B) (signVecToBoolVec σ) * (signOf (σ u) : ℝ) * (signOf (σ v) : ℝ)
            =
          Cn3Torus.W (edgeLam n B) (signVecToBoolVec σ)
            * (Cn3Torus.spin ((signVecToBoolVec σ) u) * Cn3Torus.spin ((signVecToBoolVec σ) v))
        simp [signVecToBoolVec, spin_fin2ToBool_eq_signOf]
        ring)
  calc
    avgSigns n
        (fun σ =>
          innerX n B σ * (signOf (σ u) : ℝ) * (signOf (σ v) : ℝ))
        = Cn3Torus.avgOver n (fun y => Cn3Torus.W (edgeLam n B) y * Cn3Torus.Z y e) := by
            unfold avgSigns Cn3Torus.avgOver
            rw [hsum]
            simp [div_eq_mul_inv, mul_comm]
    _ = edgeLam n B e := Cn3Torus.avgOver_weighted_prod_Z_two n (edgeLam n B) e
    _ = B u v := by
          rfl

private lemma avgSigns_innerX_mul_linearX_sq (n : ℕ) (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    avgSigns n (fun σ => innerX n B σ * linearX n x σ ^ (2 : Nat))
      = 2 * cubicTLastCross n B x := by
  let s : ℝ := ∑ i : Fin n, x i ^ (2 : Nat)
  let off : (Fin n → Fin 2) → ℝ :=
    fun σ =>
      ∑ i : Fin n, ∑ j : Fin n,
        if i < j then
          x i * x j * innerX n B σ * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ)
        else 0
  have hpoint :
      (fun σ => innerX n B σ * linearX n x σ ^ (2 : Nat))
        =
      (fun σ => s * innerX n B σ + 2 * off σ) := by
    funext σ
    rw [linearX_sq_eq_diag_add_offdiag]
    dsimp [s, off]
    have hmul :
        innerX n B σ *
            (∑ i : Fin n, ∑ j : Fin n,
                if i < j then x i * x j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0)
          =
        ∑ i : Fin n, ∑ j : Fin n,
          if i < j then
            x i * x j * innerX n B σ * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ)
          else 0 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases hij : i < j
            · simp [hij]
              ring
            · simp [hij]
    calc
      innerX n B σ *
          ((∑ i : Fin n, x i ^ (2 : Nat))
            + 2 * (∑ i : Fin n, ∑ j : Fin n,
                if i < j then x i * x j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0))
          =
        s * innerX n B σ
          + 2 * (innerX n B σ *
              (∑ i : Fin n, ∑ j : Fin n,
                  if i < j then x i * x j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0)) := by
                    ring
      _ = s * innerX n B σ + 2 * off σ := by
            rw [hmul]
  have hm1 : avgSigns n (fun σ => innerX n B σ) = 0 := by
    simpa [momentX, avgSigns] using momentX_one_eq_zero_internal n B
  have hoff_expand :
      avgSigns n off
        = ∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j * B i j else 0 := by
    dsimp [off]
    rw [avgSigns_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [avgSigns_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    by_cases hij : i < j
    · simp [hij]
      have hfun :
          (fun σ =>
            x i * x j * innerX n B σ * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ))
            =
          (fun σ =>
            (x i * x j)
              * (innerX n B σ * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ))) := by
                funext σ
                ring
      rw [hfun, avgSigns_mul_const_left, avgSigns_innerX_mul_signPair n B hij]
    · simp [hij, avgSigns_const]
  have hoff : avgSigns n off = cubicTLastCross n B x := by
    simpa [cubicTLastCross, mul_comm, mul_left_comm, mul_assoc] using hoff_expand
  rw [hpoint, avgSigns_add, avgSigns_mul_const_left, avgSigns_mul_const_left, hm1, hoff]
  ring

lemma momentX_one_eq_zero (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    momentX n lam 1 = 0 := by
  induction n with
  | zero =>
      simp [momentX, innerX]
  | succ n ih =>
      let B : Fin n → Fin n → ℝ := minorLamLast lam
      let x : Fin n → ℝ := lastColLam lam
      have hpoint :
          (fun σ : Fin n → Fin 2 =>
            ((∑ b : Fin 2,
                innerX (n + 1) lam (Fin.snoc (α := fun _ => Fin 2) σ b) ^ (1 : Nat)) / 2 : ℝ))
            =
          (fun σ : Fin n → Fin 2 => innerX n B σ) := by
        funext σ
        have hs :=
          congrArg (fun t : ℝ => t / 2)
            (sum_linear_over_last_sign (A := innerX n B σ) (Y := linearX n x σ))
        simpa [B, x, innerX_snoc_last, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hs
      change avgSigns (n + 1) (fun τ : Fin (n + 1) → Fin 2 => innerX (n + 1) lam τ ^ (1 : Nat)) = 0
      rw [avgSigns_split_last, hpoint]
      simpa [momentX, avgSigns, B] using ih B

lemma momentX_two_eq_sNorm (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    momentX n lam 2 = sNorm n lam := by
  induction n with
  | zero =>
      simp [momentX, innerX, sNorm]
  | succ n ih =>
      let B : Fin n → Fin n → ℝ := minorLamLast lam
      let x : Fin n → ℝ := lastColLam lam
      have hpoint :
          (fun σ : Fin n → Fin 2 =>
            ((∑ b : Fin 2,
                innerX (n + 1) lam (Fin.snoc (α := fun _ => Fin 2) σ b) ^ (2 : Nat)) / 2 : ℝ))
            =
          (fun σ : Fin n → Fin 2 =>
            innerX n B σ ^ (2 : Nat) + linearX n x σ ^ (2 : Nat)) := by
        funext σ
        have hs :=
          congrArg (fun t : ℝ => t / 2)
            (sum_square_over_last_sign (A := innerX n B σ) (Y := linearX n x σ))
        simpa [B, x, innerX_snoc_last, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hs
      change avgSigns (n + 1) (fun τ : Fin (n + 1) → Fin 2 => innerX (n + 1) lam τ ^ (2 : Nat))
        = sNorm (n + 1) lam
      rw [avgSigns_split_last, hpoint, avgSigns_add, avgSigns_linearX_sq]
      change momentX n B 2 + ∑ i : Fin n, x i ^ (2 : Nat) = sNorm (n + 1) lam
      have ihB : momentX n B 2 = sNorm n B := by
        simpa [B] using ih B
      rw [ihB]
      symm
      simpa [B, x] using sNorm_peel_last n lam

lemma momentX_three_eq_six_cubicT (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    momentX n lam 3 = 6 * cubicT n lam := by
  induction n with
  | zero =>
      simp [momentX, innerX, cubicT]
  | succ n ih =>
      let B : Fin n → Fin n → ℝ := minorLamLast lam
      let x : Fin n → ℝ := lastColLam lam
      have hpoint :
          (fun σ : Fin n → Fin 2 =>
            ((∑ b : Fin 2,
                innerX (n + 1) lam (Fin.snoc (α := fun _ => Fin 2) σ b) ^ (3 : Nat)) / 2 : ℝ))
            =
          (fun σ : Fin n → Fin 2 =>
            innerX n B σ ^ (3 : Nat) + 3 * (innerX n B σ * linearX n x σ ^ (2 : Nat))) := by
        funext σ
        have hs :=
          congrArg (fun t : ℝ => t / 2)
            (sum_cube_over_last_sign (A := innerX n B σ) (Y := linearX n x σ))
        simpa [B, x, innerX_snoc_last, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hs
      change avgSigns (n + 1) (fun τ : Fin (n + 1) → Fin 2 => innerX (n + 1) lam τ ^ (3 : Nat))
        = 6 * cubicT (n + 1) lam
      rw [avgSigns_split_last, hpoint, avgSigns_add, avgSigns_mul_const_left]
      change momentX n B 3 + 3 * avgSigns n (fun σ => innerX n B σ * linearX n x σ ^ (2 : Nat))
        = 6 * cubicT (n + 1) lam
      have ihB : momentX n B 3 = 6 * cubicT n B := by
        simpa [B] using ih B
      rw [ihB, avgSigns_innerX_mul_linearX_sq]
      rw [cubicT_peel_last]
      ring

/-- The sixth sign moment coincides with the sixth discrete moment `momentX n lam 6`. -/
lemma avgSigns_abs_innerX_six_eq_momentX_six (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    avgSigns n (fun σ => |innerX n lam σ| ^ (6 : Nat)) = momentX n lam 6 := by
  unfold avgSigns momentX
  congr 1
  refine Finset.sum_congr rfl ?_
  intro σ hσ
  simpa using (abs_pow_even (innerX n lam σ) 3)

lemma avgSigns_mul_const_right (n : ℕ) (f : (Fin n → Fin 2) → ℝ) (c : ℝ) :
    avgSigns n (fun σ => f σ * c) = avgSigns n f * c := by
  unfold avgSigns
  calc
    (↑(2 ^ n : ℕ) : ℝ)⁻¹ * ∑ σ : Fin n → Fin 2, f σ * c
        = (↑(2 ^ n : ℕ) : ℝ)⁻¹ * ((∑ σ : Fin n → Fin 2, f σ) * c) := by
            rw [Finset.sum_mul]
    _ = ((↑(2 ^ n : ℕ) : ℝ)⁻¹ * ∑ σ : Fin n → Fin 2, f σ) * c := by
          ring

lemma avgSigns_div_const (n : ℕ) (f : (Fin n → Fin 2) → ℝ) (c : ℝ) :
    avgSigns n (fun σ => f σ / c) = avgSigns n f / c := by
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (avgSigns_mul_const_right n f c⁻¹)

private lemma fourth_cumulant_peel_last_reduced
    (n : ℕ) (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    ((momentX (n + 1) lam 4 - 3 * sNorm (n + 1) lam ^ (2 : Nat)) / 24 : ℝ)
      =
    ((momentX n (minorLamLast lam) 4 - 3 * sNorm n (minorLamLast lam) ^ (2 : Nat)) / 24 : ℝ)
      + ((avgSigns n
            (fun σ =>
              innerX n (minorLamLast lam) σ ^ (2 : Nat)
                * linearX n (lastColLam lam) σ ^ (2 : Nat))
          - sNorm n (minorLamLast lam) * ∑ i : Fin n, (lastColLam lam i) ^ (2 : Nat)) / 4 : ℝ)
      - (1 / 12 : ℝ) * ∑ i : Fin n, (lastColLam lam i) ^ (4 : Nat) := by
  rw [momentX_four_peel_last, sNorm_peel_last]
  ring

lemma fourth_cumulant_identity_of_mixed_peel
    (hmixed :
      ∀ n : ℕ, ∀ lam : Fin (n + 1) → Fin (n + 1) → ℝ,
        avgSigns n
            (fun σ =>
              innerX n (minorLamLast lam) σ ^ (2 : Nat)
                * linearX n (lastColLam lam) σ ^ (2 : Nat))
          = sNorm n (minorLamLast lam) * ∑ i : Fin n, (lastColLam lam i) ^ (2 : Nat)
              + 4 * simpleCycle4LastCross n (minorLamLast lam) (lastColLam lam)) :
    ∀ n : ℕ, ∀ lam : Fin n → Fin n → ℝ,
      ((momentX n lam 4 - 3 * sNorm n lam ^ (2 : Nat)) / 24 : ℝ) = quarticCorr n lam := by
  intro n
  induction n with
  | zero =>
      intro lam
      simp [momentX, innerX, sNorm, quarticCorr, orderedCycle4, simpleCycle4]
  | succ n ih =>
      intro lam
      calc
        ((momentX (n + 1) lam 4 - 3 * sNorm (n + 1) lam ^ (2 : Nat)) / 24 : ℝ)
            =
          ((momentX n (minorLamLast lam) 4 - 3 * sNorm n (minorLamLast lam) ^ (2 : Nat)) / 24 : ℝ)
            + ((avgSigns n
                  (fun σ =>
                    innerX n (minorLamLast lam) σ ^ (2 : Nat)
                      * linearX n (lastColLam lam) σ ^ (2 : Nat))
                - sNorm n (minorLamLast lam) * ∑ i : Fin n, (lastColLam lam i) ^ (2 : Nat)) / 4 : ℝ)
            - (1 / 12 : ℝ) * ∑ i : Fin n, (lastColLam lam i) ^ (4 : Nat) :=
              fourth_cumulant_peel_last_reduced n lam
        _ =
          quarticCorr n (minorLamLast lam)
            + ((avgSigns n
                  (fun σ =>
                    innerX n (minorLamLast lam) σ ^ (2 : Nat)
                      * linearX n (lastColLam lam) σ ^ (2 : Nat))
                - sNorm n (minorLamLast lam) * ∑ i : Fin n, (lastColLam lam i) ^ (2 : Nat)) / 4 : ℝ)
            - (1 / 12 : ℝ) * ∑ i : Fin n, (lastColLam lam i) ^ (4 : Nat) := by
                rw [ih (minorLamLast lam)]
        _ =
          quarticCorr n (minorLamLast lam)
            + simpleCycle4LastCross n (minorLamLast lam) (lastColLam lam)
            - (1 / 12 : ℝ) * ∑ i : Fin n, (lastColLam lam i) ^ (4 : Nat) := by
                rw [hmixed n lam]
                ring
        _ = quarticCorr (n + 1) lam := by
              rw [quarticCorr_peel_last]

/-- Internal proof of the cubic bound `|T(λ)| ≤ (125/6)·s(λ)^{3/2}`. -/
private theorem fourth_moment_bound_internal (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : Fin n → Fin n → ℝ,
      |cubicT n lam| ≤ C * sNorm n lam ^ (3/2 : ℝ) := by
  refine ⟨(125 : ℝ) / 6, by positivity, ?_⟩
  intro lam
  have hcubic : cubicT n lam = momentX n lam 3 / 6 := by
    have h := momentX_three_eq_six_cubicT n lam
    linarith
  have habs_avg :
      |momentX n lam 3| ≤ avgSigns n (fun σ => |innerX n lam σ| ^ (3 : Nat)) := by
    calc
      |momentX n lam 3|
          = |avgSigns n (fun σ => innerX n lam σ ^ (3 : Nat))| := rfl
      _ ≤ avgSigns n (fun σ => |(innerX n lam σ) ^ (3 : Nat)|) :=
            abs_avgSigns_le_avgSigns_abs n (fun σ => innerX n lam σ ^ (3 : Nat))
      _ = avgSigns n (fun σ => |innerX n lam σ| ^ (3 : Nat)) := by
            congr 1
            funext σ
            rw [abs_pow]
  have havg :
      avgSigns n (fun σ => |innerX n lam σ| ^ (3 : Nat))
        = Cn3Torus.avgOver n (fun y => |Cn3Torus.W (edgeLam n lam) y| ^ (3 : Nat)) := by
    simpa using (avgSigns_abs_innerX_pow_eq_avgOver_abs_W_pow n lam 3)
  have hcube :=
    Cn3Torus.avgOver_abs_cube_le_125_mul_sqNormEdge_threeHalves n (edgeLam n lam)
  have hμ3 :
      |momentX n lam 3| ≤ (125 : ℝ) * sNorm n lam ^ (3 / 2 : ℝ) := by
    have hle := habs_avg
    rw [havg] at hle
    simpa [sNorm_eq_sqNormEdge] using hle.trans hcube
  rw [hcubic]
  have habs_div :
      |momentX n lam 3 / (6 : ℝ)| = |momentX n lam 3| / (6 : ℝ) := by
    rw [abs_div]
    norm_num
  rw [habs_div]
  convert div_le_div_of_nonneg_right hμ3 (show (0 : ℝ) ≤ (6 : ℝ) from by positivity) using 1
  ring_nf

/-- Crude pointwise quintic control used later in the fixed-`n` and local-gap estimates. -/
theorem quinticP5_pointwise_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : Fin n → Fin n → ℝ,
      |quinticP5 n lam| ≤ C * sNorm n lam ^ (5 / 2 : ℝ) := by
  obtain ⟨C_T, hCT_pos, hCT⟩ := fourth_moment_bound_internal n
  refine ⟨(1125 : ℝ) / 120 + C_T / 2, ?_, ?_⟩
  · have hfirst_nonneg : 0 ≤ (1125 : ℝ) / 120 := by
      positivity
    nlinarith
  · intro lam
    have hs_nonneg : 0 ≤ sNorm n lam := sNorm_nonneg n lam
    have hμ5 : |momentX n lam 5| ≤
        (1125 : ℝ) * sNorm n lam ^ (5 / 2 : ℝ) :=
      momentX_five_abs_le n lam
    have hT : |cubicT n lam| ≤ C_T * sNorm n lam ^ (3 / 2 : ℝ) := hCT lam
    have hs_mul :
        sNorm n lam * sNorm n lam ^ (3 / 2 : ℝ) = sNorm n lam ^ (5 / 2 : ℝ) := by
      calc
        sNorm n lam * sNorm n lam ^ (3 / 2 : ℝ)
            = sNorm n lam ^ (1 : ℝ) * sNorm n lam ^ (3 / 2 : ℝ) := by simp
        _ = sNorm n lam ^ (5 / 2 : ℝ) := by
              rw [← Real.rpow_add_of_nonneg hs_nonneg (by positivity) (by positivity)]
              norm_num
    have hmix :
        |sNorm n lam * cubicT n lam / 2| ≤ (C_T / 2) * sNorm n lam ^ (5 / 2 : ℝ) := by
      have h_eq : |sNorm n lam * cubicT n lam / 2| = sNorm n lam * |cubicT n lam| / 2 := by
        rw [div_eq_mul_inv, abs_mul, abs_mul, abs_of_nonneg hs_nonneg,
          abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹)]
        ring
      rw [h_eq]
      calc
        sNorm n lam * |cubicT n lam| / 2
            ≤ sNorm n lam * (C_T * sNorm n lam ^ (3 / 2 : ℝ)) / 2 := by
                gcongr
        _ = (C_T / 2) * (sNorm n lam * sNorm n lam ^ (3 / 2 : ℝ)) := by ring
        _ = (C_T / 2) * sNorm n lam ^ (5 / 2 : ℝ) := by rw [hs_mul]
    have hquintic :
        quinticP5 n lam = momentX n lam 5 / 120 - sNorm n lam * cubicT n lam / 2 := by
      rw [quinticP5, momentX_three_eq_six_cubicT n lam, momentX_two_eq_sNorm n lam]
      ring
    rw [hquintic]
    calc
      |momentX n lam 5 / 120 - sNorm n lam * cubicT n lam / 2|
          ≤ |momentX n lam 5 / 120| + |sNorm n lam * cubicT n lam / 2| := by
            have h := abs_sub (momentX n lam 5 / 120) (sNorm n lam * cubicT n lam / 2)
            simpa using h
      _ = |momentX n lam 5| / 120 + |sNorm n lam * cubicT n lam / 2| := by
            rw [abs_div]
            norm_num
      _ ≤ ((1125 : ℝ) / 120) * sNorm n lam ^ (5 / 2 : ℝ)
              + (C_T / 2) * sNorm n lam ^ (5 / 2 : ℝ) := by
                have hμ5' :
                    |momentX n lam 5| / 120
                      ≤ ((1125 : ℝ) / 120) * sNorm n lam ^ (5 / 2 : ℝ) := by
                  exact (div_le_iff₀ (show (0 : ℝ) < 120 by norm_num)).2 <| by
                    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hμ5
                exact add_le_add hμ5' hmix
      _ = (((1125 : ℝ) / 120) + C_T / 2) * sNorm n lam ^ (5 / 2 : ℝ) := by
              ring
