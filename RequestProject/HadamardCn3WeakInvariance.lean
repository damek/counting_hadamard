import RequestProject.HadamardCn3Defs
import RequestProject.HadamardCn3TorusCount
import RequestProject.HadamardCn3Moments
import RequestProject.HadamardCn3MOO
import RequestProject.HadamardCn3ResidualBase

noncomputable section

open Real MeasureTheory Filter Finset Topology
open scoped Pointwise

/-!
# Weak Invariance Input

This file isolates the weak invariance statement, in the sense of
Mossel-O'Donnell-Oleszkiewicz, that is sufficient for the far-shell integral
replacement.

It is kept separate so the comparison theorem and its influence hypotheses can
be read independently of the later counting arguments.
-/

/-- Real-valued linear form on `Fin n → ℝ`. -/
private def linForm (n : ℕ) (c : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, c i * x i

/-- Hybrid point with a Boolean sign block followed by a Gaussian block. -/
private def hybridPoint (n m : ℕ) (σ : Fin n → Fin 2) (x : Fin m → ℝ) : Fin (n + m) → ℝ :=
  Fin.append (fun i => (signOf (σ i) : ℝ)) x

/-- Hybrid average with `n` sign coordinates followed by `m` Gaussian coordinates. -/
private def hybridAvg (n m : ℕ) (f : (Fin (n + m) → ℝ) → ℝ) : ℝ :=
  stdGaussianAvg m (fun x => avgSigns n (fun σ => f (hybridPoint n m σ x)))

/-- The unnormalized Gaussian weight on `ℝ^n`. -/
private def gaussianWeight (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2)

private lemma gaussianWeight_nonneg (n : ℕ) (x : Fin n → ℝ) : 0 ≤ gaussianWeight n x := by
  unfold gaussianWeight
  positivity

/-- The sign-block coefficients inside a hybrid linear form. -/
private def signBlockCoeffs (n m : ℕ) (c : Fin (n + m) → ℝ) : Fin n → ℝ :=
  fun i => c (Fin.castAdd m i)

/-- The Gaussian-block coefficients inside a hybrid linear form. -/
private def gaussBlockCoeffs (n m : ℕ) (c : Fin (n + m) → ℝ) : Fin m → ℝ :=
  fun j => c (Fin.natAdd n j)

@[fun_prop] private lemma continuous_hybridPoint
    (n m : ℕ) (σ : Fin n → Fin 2) :
    Continuous (fun x : Fin m → ℝ => hybridPoint n m σ x) := by
  rw [continuous_pi_iff]
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa [hybridPoint, Fin.append_left] using
      (continuous_const : Continuous (fun _ : Fin m → ℝ => (((signOf (σ j) : ℤ) : ℝ))))
  · intro j
    simpa [hybridPoint, Fin.append_right] using
      (continuous_apply j : Continuous (fun x : Fin m → ℝ => x j))

@[fun_prop] private lemma continuous_linForm
    (n : ℕ) (c : Fin n → ℝ) :
    Continuous (fun x : Fin n → ℝ => linForm n c x) := by
  unfold linForm
  fun_prop

@[fun_prop] private lemma continuous_finCons
    (m : ℕ) (x : Fin m → ℝ) :
    Continuous (fun z : ℝ => (Fin.cons z x : Fin (m + 1) → ℝ)) := by
  rw [continuous_pi_iff]
  intro i
  refine Fin.cases ?_ ?_ i
  · simpa using (continuous_id : Continuous (fun z : ℝ => z))
  · intro j
    simpa [Fin.cons_succ] using
      (continuous_const : Continuous (fun _ : ℝ => x j))

@[fun_prop] private lemma continuous_Q2Gauss
    (n : ℕ) (f : Fin n → Fin n → ℝ) :
    Continuous (fun x : Fin n → ℝ => Q2Gauss n f x) := by
  unfold Q2Gauss
  fun_prop

@[fun_prop] private lemma continuous_gaussianWeight
    (n : ℕ) :
    Continuous (fun x : Fin n → ℝ => gaussianWeight n x) := by
  unfold gaussianWeight
  fun_prop

private lemma gaussianWeight_zero (x : Fin 0 → ℝ) : gaussianWeight 0 x = 1 := by
  simp [gaussianWeight]

private lemma gaussianWeight_cons (m : ℕ) (z : ℝ) (x : Fin m → ℝ) :
    gaussianWeight (m + 1) (Fin.cons z x) = Real.exp (-(z ^ (2 : Nat)) / 2) * gaussianWeight m x := by
  unfold gaussianWeight
  rw [Fin.sum_univ_succ]
  simp
  rw [show (((-∑ x_1 : Fin m, x x_1 ^ (2 : Nat)) + -z ^ (2 : Nat)) / 2 : ℝ)
      = -(z ^ (2 : Nat) / 2) + ((-∑ x_1 : Fin m, x x_1 ^ (2 : Nat)) / 2 : ℝ) by ring]
  rw [Real.exp_add]
  have hz : (-(z ^ (2 : Nat) / 2 : ℝ)) = (-z ^ (2 : Nat)) / 2 := by ring
  simpa [hz]

private lemma stdGaussianAvg_zero (f : (Fin 0 → ℝ) → ℝ) :
    stdGaussianAvg 0 f = f Fin.elim0 := by
  have hfun : (fun x : Fin 0 → ℝ => f x * Real.exp (-(∑ i : Fin 0, x i ^ (2 : Nat)) / 2))
      = fun _ : Fin 0 → ℝ => f Fin.elim0 := by
    funext x
    have : x = Fin.elim0 := Subsingleton.elim _ _
    subst this
    simp
  unfold stdGaussianAvg
  rw [hfun, MeasureTheory.integral_unique]
  have hμ : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
    have hdirac : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac Fin.elim0 := by
      simpa using (Measure.volume_pi_eq_dirac (α := fun _ : Fin 0 => ℝ) (x := Fin.elim0))
    have hμ' : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
      rw [hdirac]
      simp
    simpa [MeasureTheory.measureReal_def] using congrArg ENNReal.toReal hμ'
  simp [hμ]

private lemma integral_comp_cons_real (m : ℕ) (f : (Fin (m + 1) → ℝ) → ℝ) :
    ∫ y : Fin (m + 1) → ℝ, f y = ∫ p : ℝ × (Fin m → ℝ), f (Fin.cons p.1 p.2) := by
  rw [← ((volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm).integral_comp']
  refine integral_congr_ae ?_
  exact Filter.Eventually.of_forall (fun p => by
    have hcons : ((Fin.consEquiv fun _ : Fin (m + 1) => ℝ) p) = Fin.cons p.1 p.2 := by
      ext j
      simp [Fin.consEquiv, Fin.insertNth_zero']
    simpa [MeasurableEquiv.piFinSuccAbove_symm_apply] using congrArg f hcons)

/-- The normalized one-dimensional Gaussian average. -/
private def stdGaussianAvg1 (f : ℝ → ℝ) : ℝ :=
  ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹ * ∫ z : ℝ, f z * Real.exp (-(z ^ (2 : Nat)) / 2)

private lemma stdGaussian_normFactor_succ (m : ℕ) :
    ((2 * Real.pi) ^ (((m + 1 : ℕ) : ℝ) / 2))⁻¹
      = ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹ * ((2 * Real.pi) ^ ((m : ℝ) / 2))⁻¹ := by
  have hbase_pos : 0 < 2 * Real.pi := by positivity [Real.pi_pos]
  have hsplit :
      (((m + 1 : ℕ) : ℝ) / 2) = (1 : ℝ) / 2 + (m : ℝ) / 2 := by
    norm_num
    ring
  rw [hsplit, Real.rpow_add hbase_pos, mul_inv_rev]
  ring

private lemma integral_odd_gaussianWeight_zero (f : ℝ → ℝ)
    (hfodd : ∀ z : ℝ, f (-z) = -f z) :
    ∫ z : ℝ, f z * Real.exp (-(z ^ (2 : Nat)) / 2) = 0 := by
  let g : ℝ → ℝ := fun z => f z * Real.exp (-(z ^ (2 : Nat)) / 2)
  have hcomp :
      ∫ z : ℝ, g z = ∫ z : ℝ, g (-z) := by
        symm
        simpa [g] using
          (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp'
            (f := MeasurableEquiv.neg ℝ) (g := g)
  have hneg :
      g = fun z : ℝ => -g (-z) := by
    funext z
    change f z * Real.exp (-(z ^ (2 : Nat)) / 2) =
      -(f (-z) * Real.exp (-((-z) ^ (2 : Nat)) / 2))
    rw [hfodd z]
    ring_nf
  have hzero : ∫ z : ℝ, g z = -∫ z : ℝ, g z := by
    calc
      ∫ z : ℝ, g z = ∫ z : ℝ, -g (-z) := by
        refine MeasureTheory.integral_congr_ae ?_
        exact Filter.Eventually.of_forall (fun z => by
          have hz := congrFun hneg z
          simpa using hz)
      _ = -∫ z : ℝ, g (-z) := by rw [MeasureTheory.integral_neg]
      _ = -∫ z : ℝ, g z := by rw [← hcomp]
  have hsum := congrArg (fun t : ℝ => t + ∫ z : ℝ, g z) hzero
  simpa [g] using hsum

private lemma stdGaussianAvg1_mass :
    stdGaussianAvg1 (fun _ : ℝ => 1) = 1 := by
  unfold stdGaussianAvg1
  have hmoment :=
    (gaussian_one_dim_even_moment 0 (1 / 2 : ℝ) (by positivity : 0 < (1 / 2 : ℝ)))
  have hsqrt2pi : Real.sqrt (Real.pi / (1 / 2 : ℝ)) = Real.sqrt (2 * Real.pi) := by
    congr 1
    field_simp [Real.pi_ne_zero]
  have hrpow : (2 * Real.pi) ^ ((1 : ℝ) / 2) = Real.sqrt (2 * Real.pi) := by
    symm
    rw [Real.sqrt_eq_rpow]
  have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 (by positivity [Real.pi_pos])
  calc
    ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹
        * ∫ z : ℝ, (1 : ℝ) * Real.exp (-(z ^ (2 : Nat)) / 2)
      = ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹ * Real.sqrt (Real.pi / (1 / 2 : ℝ)) := by
          simpa [one_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using congrArg
            (fun r : ℝ => ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹ * r) hmoment
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (2 * Real.pi) := by rw [hsqrt2pi, hrpow]
    _ = 1 := by field_simp [hsqrt_ne]

private lemma stdGaussianAvg1_id :
    stdGaussianAvg1 (fun z : ℝ => z) = 0 := by
  unfold stdGaussianAvg1
  rw [integral_odd_gaussianWeight_zero (fun z => z) (by intro z; ring)]
  ring

private lemma stdGaussianAvg1_sq :
    stdGaussianAvg1 (fun z : ℝ => z ^ (2 : Nat)) = 1 := by
  unfold stdGaussianAvg1
  have hmoment :=
    gaussian_one_dim_even_moment 1 (1 / 2 : ℝ) (by positivity : 0 < (1 / 2 : ℝ))
  have hsqrt2pi : Real.sqrt (Real.pi / (1 / 2 : ℝ)) = Real.sqrt (2 * Real.pi) := by
    congr 1
    field_simp [Real.pi_ne_zero]
  have hrpow : (2 * Real.pi) ^ ((1 : ℝ) / 2) = Real.sqrt (2 * Real.pi) := by
    symm
    rw [Real.sqrt_eq_rpow]
  have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 (by positivity [Real.pi_pos])
  calc
    ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹ *
        ∫ z : ℝ, z ^ (2 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)
      =
        ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹ *
          (((Nat.doubleFactorial (2 * 1 - 1) : ℕ) : ℝ) /
            (2 ^ 1 * (1 / 2 : ℝ) ^ 1)) * Real.sqrt (Real.pi / (1 / 2 : ℝ)) := by
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using congrArg
              (fun r : ℝ => ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹ * r) hmoment
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (2 * Real.pi) := by
          norm_num [Nat.doubleFactorial, hsqrt2pi, hrpow]
    _ = 1 := by field_simp [hsqrt_ne]

private lemma stdGaussianAvg1_four :
    stdGaussianAvg1 (fun z : ℝ => z ^ (4 : Nat)) = 3 := by
  unfold stdGaussianAvg1
  have hmoment :=
    gaussian_one_dim_even_moment 2 (1 / 2 : ℝ) (by positivity : 0 < (1 / 2 : ℝ))
  have hsqrt2pi : Real.sqrt (Real.pi / (1 / 2 : ℝ)) = Real.sqrt (2 * Real.pi) := by
    congr 1
    field_simp [Real.pi_ne_zero]
  have hrpow : (2 * Real.pi) ^ ((1 : ℝ) / 2) = Real.sqrt (2 * Real.pi) := by
    symm
    rw [Real.sqrt_eq_rpow]
  have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 (by positivity [Real.pi_pos])
  calc
    ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹ *
        ∫ z : ℝ, z ^ (4 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)
      =
        ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹ *
          (((Nat.doubleFactorial (2 * 2 - 1) : ℕ) : ℝ) /
            (2 ^ 2 * (1 / 2 : ℝ) ^ 2)) * Real.sqrt (Real.pi / (1 / 2 : ℝ)) := by
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using congrArg
              (fun r : ℝ => ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹ * r) hmoment
    _ = 3 * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (2 * Real.pi)) := by
          norm_num [Nat.doubleFactorial, hsqrt2pi, hrpow]
          ring
    _ = 3 := by field_simp [hsqrt_ne]

private lemma one_dim_gaussian_integral :
    ∫ z : ℝ, Real.exp (-(z ^ (2 : Nat)) / 2) = (2 * Real.pi) ^ ((1 : ℝ) / 2) := by
  have h := stdGaussianAvg1_mass
  unfold stdGaussianAvg1 at h
  let A : ℝ := (2 * Real.pi) ^ ((1 : ℝ) / 2)
  have hne : A ≠ 0 := by
    positivity [Real.pi_pos]
  field_simp [A, hne] at h
  have harg (z : ℝ) : -(z ^ (2 : Nat) / 2 : ℝ) = (-(z ^ (2 : Nat) : ℝ)) / 2 := by ring
  simpa [A, harg, mul_comm, mul_left_comm, mul_assoc] using h

private lemma one_dim_gaussian_sq_integral :
    ∫ z : ℝ, z ^ (2 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)
      = (2 * Real.pi) ^ ((1 : ℝ) / 2) := by
  have h := stdGaussianAvg1_sq
  unfold stdGaussianAvg1 at h
  let A : ℝ := (2 * Real.pi) ^ ((1 : ℝ) / 2)
  have hne : A ≠ 0 := by
    positivity [Real.pi_pos]
  field_simp [A, hne] at h
  have harg (z : ℝ) : -(z ^ (2 : Nat) / 2 : ℝ) = (-(z ^ (2 : Nat) : ℝ)) / 2 := by ring
  simpa [A, harg, mul_comm, mul_left_comm, mul_assoc] using h

private lemma one_dim_gaussian_four_integral :
    ∫ z : ℝ, z ^ (4 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)
      = 3 * (2 * Real.pi) ^ ((1 : ℝ) / 2) := by
  have h := stdGaussianAvg1_four
  unfold stdGaussianAvg1 at h
  let A : ℝ := (2 * Real.pi) ^ ((1 : ℝ) / 2)
  have hne : A ≠ 0 := by
    positivity [Real.pi_pos]
  field_simp [A, hne] at h
  have harg (z : ℝ) : -(z ^ (2 : Nat) / 2 : ℝ) = (-(z ^ (2 : Nat) : ℝ)) / 2 := by ring
  simpa [A, harg, mul_comm, mul_left_comm, mul_assoc] using h

private lemma integrable_one_dim_gaussianWeight :
    MeasureTheory.Integrable (fun z : ℝ => Real.exp (-(z ^ (2 : Nat)) / 2)) := by
  refine ⟨(by fun_prop), ?_⟩
  have hnonneg :
      0 ≤ᵐ[MeasureTheory.volume] fun z : ℝ => Real.exp (-(z ^ (2 : Nat)) / 2) :=
    Filter.Eventually.of_forall (fun z => Real.exp_nonneg _)
  have htoReal :
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z ^ (2 : Nat)) / 2))).toReal
        = (2 * Real.pi) ^ ((1 : ℝ) / 2) := by
    calc
      (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z ^ (2 : Nat)) / 2))).toReal
          = ∫ z : ℝ, Real.exp (-(z ^ (2 : Nat)) / 2) := by
              symm
              exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg
                (by fun_prop)
      _ = (2 * Real.pi) ^ ((1 : ℝ) / 2) := one_dim_gaussian_integral
  have hlt :
      ∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z ^ (2 : Nat)) / 2)) < ⊤ := by
    have hne_top :
        (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z ^ (2 : Nat)) / 2))) ≠ ⊤ := by
      intro htop
      have : ((∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-(z ^ (2 : Nat)) / 2))).toReal) = 0 := by
        simpa [htop]
      have hpos : 0 < (2 * Real.pi) ^ ((1 : ℝ) / 2) := by positivity [Real.pi_pos]
      linarith [htoReal]
    exact lt_of_le_of_ne le_top hne_top
  exact (MeasureTheory.hasFiniteIntegral_iff_ofReal hnonneg).2 hlt

private lemma integrable_one_dim_sq_gaussianWeight :
    MeasureTheory.Integrable (fun z : ℝ => z ^ (2 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
  refine ⟨(by fun_prop), ?_⟩
  have hnonneg :
      0 ≤ᵐ[MeasureTheory.volume] fun z : ℝ => z ^ (2 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2) :=
    Filter.Eventually.of_forall (fun z => by positivity)
  have htoReal :
      (∫⁻ z : ℝ, ENNReal.ofReal (z ^ (2 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2))).toReal
        = (2 * Real.pi) ^ ((1 : ℝ) / 2) := by
    calc
      (∫⁻ z : ℝ, ENNReal.ofReal (z ^ (2 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2))).toReal
          = ∫ z : ℝ, z ^ (2 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2) := by
              symm
              exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg
                (by fun_prop)
      _ = (2 * Real.pi) ^ ((1 : ℝ) / 2) := one_dim_gaussian_sq_integral
  have hlt :
      ∫⁻ z : ℝ, ENNReal.ofReal (z ^ (2 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)) < ⊤ := by
    have hne_top :
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ (2 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2))) ≠ ⊤ := by
      intro htop
      have : ((∫⁻ z : ℝ, ENNReal.ofReal (z ^ (2 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2))).toReal) = 0 := by
        simpa [htop]
      have hpos : 0 < (2 * Real.pi) ^ ((1 : ℝ) / 2) := by positivity [Real.pi_pos]
      linarith [htoReal]
    exact lt_of_le_of_ne le_top hne_top
  exact (MeasureTheory.hasFiniteIntegral_iff_ofReal hnonneg).2 hlt

private lemma integrable_one_dim_four_gaussianWeight :
    MeasureTheory.Integrable (fun z : ℝ => z ^ (4 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
  refine ⟨(by fun_prop), ?_⟩
  have hnonneg :
      0 ≤ᵐ[MeasureTheory.volume] fun z : ℝ => z ^ (4 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2) :=
    Filter.Eventually.of_forall (fun z => by positivity)
  have htoReal :
      (∫⁻ z : ℝ, ENNReal.ofReal (z ^ (4 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2))).toReal
        = 3 * (2 * Real.pi) ^ ((1 : ℝ) / 2) := by
    calc
      (∫⁻ z : ℝ, ENNReal.ofReal (z ^ (4 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2))).toReal
          = ∫ z : ℝ, z ^ (4 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2) := by
              symm
              exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg
                (by fun_prop)
      _ = 3 * (2 * Real.pi) ^ ((1 : ℝ) / 2) := one_dim_gaussian_four_integral
  have hlt :
      ∫⁻ z : ℝ, ENNReal.ofReal (z ^ (4 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)) < ⊤ := by
    have hne_top :
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ (4 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2))) ≠ ⊤ := by
      intro htop
      have : ((∫⁻ z : ℝ, ENNReal.ofReal (z ^ (4 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2))).toReal) = 0 := by
        simpa [htop]
      have hpos : 0 < 3 * (2 * Real.pi) ^ ((1 : ℝ) / 2) := by positivity [Real.pi_pos]
      linarith [htoReal]
    exact lt_of_le_of_ne le_top hne_top
  exact (MeasureTheory.hasFiniteIntegral_iff_ofReal hnonneg).2 hlt

private lemma integrable_one_dim_linear_gaussianWeight :
    MeasureTheory.Integrable (fun z : ℝ => z * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
  refine MeasureTheory.Integrable.mono'
    (integrable_one_dim_gaussianWeight.add integrable_one_dim_sq_gaussianWeight)
    (by fun_prop) ?_
  exact Filter.Eventually.of_forall (fun z => by
    have hexp_nonneg : 0 ≤ Real.exp (-(z ^ (2 : Nat)) / 2) := Real.exp_nonneg _
    have habs_le : |z| ≤ 1 + z ^ (2 : Nat) := by
      have hsq : 0 ≤ (|z| - (1 / 2 : ℝ)) ^ (2 : Nat) := sq_nonneg _
      have hsqabs : z ^ (2 : Nat) = |z| ^ (2 : Nat) := by rw [sq_abs]
      nlinarith [hsq, hsqabs]
    calc
      ‖z * Real.exp (-(z ^ (2 : Nat)) / 2)‖
          = |z| * Real.exp (-(z ^ (2 : Nat)) / 2) := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hexp_nonneg]
      _ ≤ (1 + z ^ (2 : Nat)) * Real.exp (-(z ^ (2 : Nat)) / 2) := by
            gcongr
      _ = Real.exp (-(z ^ (2 : Nat)) / 2)
            + z ^ (2 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2) := by ring)

private lemma integrable_one_dim_cube_gaussianWeight :
    MeasureTheory.Integrable (fun z : ℝ => z ^ (3 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
  refine MeasureTheory.Integrable.mono'
    (integrable_one_dim_gaussianWeight.add integrable_one_dim_four_gaussianWeight)
    (by fun_prop) ?_
  exact Filter.Eventually.of_forall (fun z => by
    have hexp_nonneg : 0 ≤ Real.exp (-(z ^ (2 : Nat)) / 2) := Real.exp_nonneg _
    have habs_le : |z| ^ (3 : Nat) ≤ 1 + z ^ (4 : Nat) := by
      by_cases hz : |z| ≤ 1
      · have hpow : |z| ^ (3 : Nat) ≤ (1 : ℝ) ^ (3 : Nat) := by
            gcongr
        have hz4_nonneg : 0 ≤ z ^ (4 : Nat) := by positivity
        calc
          |z| ^ (3 : Nat) ≤ 1 := by simpa using hpow
          _ ≤ 1 + z ^ (4 : Nat) := by linarith
      · have hz1 : 1 ≤ |z| := le_of_not_ge hz
        have hmul :
            |z| ^ (3 : Nat) * 1 ≤ |z| ^ (3 : Nat) * |z| := by
          exact mul_le_mul_of_nonneg_left hz1 (pow_nonneg (abs_nonneg z) 3)
        have hpow : |z| ^ (3 : Nat) ≤ |z| ^ (4 : Nat) := by
          simpa [pow_succ, pow_three, mul_comm, mul_left_comm, mul_assoc] using hmul
        have habs_pow : |z| ^ (4 : Nat) = z ^ (4 : Nat) := by
          calc
            |z| ^ (4 : Nat) = |z ^ (4 : Nat)| := by simpa [abs_pow]
            _ = z ^ (4 : Nat) := by rw [abs_of_nonneg (by positivity)]
        have hz4_nonneg : 0 ≤ z ^ (4 : Nat) := by positivity
        calc
          |z| ^ (3 : Nat) ≤ |z| ^ (4 : Nat) := hpow
          _ = z ^ (4 : Nat) := habs_pow
          _ ≤ 1 + z ^ (4 : Nat) := by linarith
    calc
      ‖z ^ (3 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)‖
          = |z| ^ (3 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2) := by
              rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hexp_nonneg]
      _ ≤ (1 + z ^ (4 : Nat)) * Real.exp (-(z ^ (2 : Nat)) / 2) := by
            gcongr
      _ = Real.exp (-(z ^ (2 : Nat)) / 2)
            + z ^ (4 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2) := by ring)

private lemma integrable_one_dim_abs_cube_gaussianWeight :
    MeasureTheory.Integrable (fun z : ℝ => |z| ^ (3 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
  refine MeasureTheory.Integrable.mono'
    (integrable_one_dim_gaussianWeight.add integrable_one_dim_four_gaussianWeight)
    (by fun_prop) ?_
  exact Filter.Eventually.of_forall (fun z => by
    have hexp_nonneg : 0 ≤ Real.exp (-(z ^ (2 : Nat)) / 2) := Real.exp_nonneg _
    have habs_le : |z| ^ (3 : Nat) ≤ 1 + z ^ (4 : Nat) := by
      by_cases hz : |z| ≤ 1
      · have hpow : |z| ^ (3 : Nat) ≤ (1 : ℝ) ^ (3 : Nat) := by
          gcongr
        have hz4_nonneg : 0 ≤ z ^ (4 : Nat) := by positivity
        calc
          |z| ^ (3 : Nat) ≤ 1 := by simpa using hpow
          _ ≤ 1 + z ^ (4 : Nat) := by linarith
      · have hz1 : 1 ≤ |z| := le_of_not_ge hz
        have hmul :
            |z| ^ (3 : Nat) * 1 ≤ |z| ^ (3 : Nat) * |z| := by
          exact mul_le_mul_of_nonneg_left hz1 (pow_nonneg (abs_nonneg z) 3)
        have hpow : |z| ^ (3 : Nat) ≤ |z| ^ (4 : Nat) := by
          simpa [pow_succ, pow_three, mul_comm, mul_left_comm, mul_assoc] using hmul
        have habs_pow : |z| ^ (4 : Nat) = z ^ (4 : Nat) := by
          calc
            |z| ^ (4 : Nat) = |z ^ (4 : Nat)| := by simpa [abs_pow]
            _ = z ^ (4 : Nat) := by rw [abs_of_nonneg (by positivity)]
        have hz4_nonneg : 0 ≤ z ^ (4 : Nat) := by positivity
        calc
          |z| ^ (3 : Nat) ≤ |z| ^ (4 : Nat) := hpow
          _ = z ^ (4 : Nat) := habs_pow
          _ ≤ 1 + z ^ (4 : Nat) := by linarith
    calc
      ‖|z| ^ (3 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)‖
          = |z| ^ (3 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2) := by
              rw [Real.norm_eq_abs, abs_of_nonneg]
              positivity
      _ ≤ (1 + z ^ (4 : Nat)) * Real.exp (-(z ^ (2 : Nat)) / 2) := by
            gcongr
      _ = Real.exp (-(z ^ (2 : Nat)) / 2)
            + z ^ (4 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2) := by ring)

private lemma stdGaussianAvg_cons_mul (m : ℕ) (g : ℝ → ℝ) (h : (Fin m → ℝ) → ℝ) :
    stdGaussianAvg (m + 1) (fun y => g (y 0) * h (Fin.tail y))
      = stdGaussianAvg1 g * stdGaussianAvg m h := by
  unfold stdGaussianAvg stdGaussianAvg1
  rw [stdGaussian_normFactor_succ]
  have hcomp :
      ∫ y : Fin (m + 1) → ℝ,
          (g (y 0) * h (Fin.tail y)) * Real.exp (-(∑ i : Fin (m + 1), y i ^ (2 : Nat)) / 2)
        =
      ∫ p : ℝ × (Fin m → ℝ),
          (g p.1 * Real.exp (-(p.1 ^ (2 : Nat)) / 2))
            * (h p.2 * Real.exp (-(∑ i : Fin m, p.2 i ^ (2 : Nat)) / 2)) := by
        rw [integral_comp_cons_real]
        refine integral_congr_ae ?_
        exact Filter.Eventually.of_forall (fun p => by
          rcases p with ⟨z, x⟩
          have hw :
              Real.exp (-(∑ i : Fin (m + 1), (Fin.cons z x i) ^ (2 : Nat)) / 2)
                = Real.exp (-(z ^ (2 : Nat)) / 2) *
                    Real.exp (-(∑ i : Fin m, x i ^ (2 : Nat)) / 2) := by
                  simpa [gaussianWeight] using (gaussianWeight_cons m z x)
          simpa [hw, mul_assoc, mul_left_comm, mul_comm])
  have hprod :
      ∫ p : ℝ × (Fin m → ℝ),
          (g p.1 * Real.exp (-(p.1 ^ (2 : Nat)) / 2))
            * (h p.2 * Real.exp (-(∑ i : Fin m, p.2 i ^ (2 : Nat)) / 2))
        =
      (∫ z : ℝ, g z * Real.exp (-(z ^ (2 : Nat)) / 2))
        * ∫ x : Fin m → ℝ, h x * Real.exp (-(∑ i : Fin m, x i ^ (2 : Nat)) / 2) := by
        have hshape :
            (fun p : ℝ × (Fin m → ℝ) =>
              (g p.1 * Real.exp (-(p.1 ^ (2 : Nat)) / 2))
                * (h p.2 * Real.exp (-(∑ i : Fin m, p.2 i ^ (2 : Nat)) / 2)))
              =
            (fun p : ℝ × (Fin m → ℝ) =>
              (fun z : ℝ => g z * Real.exp (-(z ^ (2 : Nat)) / 2)) p.1
                * (fun x : Fin m → ℝ => h x * Real.exp (-(∑ i : Fin m, x i ^ (2 : Nat)) / 2)) p.2) := by
              funext p
              rfl
        rw [hshape]
        simpa using
          (MeasureTheory.integral_prod_mul
            (μ := (MeasureTheory.volume : Measure ℝ))
            (ν := (MeasureTheory.volume : Measure (Fin m → ℝ)))
            (f := fun z : ℝ => g z * Real.exp (-(z ^ (2 : Nat)) / 2))
            (g := fun x : Fin m → ℝ => h x * Real.exp (-(∑ i : Fin m, x i ^ (2 : Nat)) / 2)))
  rw [hcomp, hprod]
  ring

private lemma stdGaussianAvg_split_first (m : ℕ) (F : (Fin (m + 1) → ℝ) → ℝ)
    (hF : MeasureTheory.Integrable (fun y : Fin (m + 1) → ℝ => F y * gaussianWeight (m + 1) y)) :
    stdGaussianAvg (m + 1) F
      = stdGaussianAvg m (fun x => stdGaussianAvg1 (fun z : ℝ => F (Fin.cons z x))) := by
  let e : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  let G : ℝ × (Fin m → ℝ) → ℝ :=
    fun p => F (Fin.cons p.1 p.2) * Real.exp (-(p.1 ^ (2 : Nat)) / 2) * gaussianWeight m p.2
  have hG_int : MeasureTheory.Integrable G := by
    let hpres := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have hcomp :
        MeasureTheory.Integrable
          ((fun y : Fin (m + 1) → ℝ => F y * gaussianWeight (m + 1) y) ∘ e.symm) := by
      exact (MeasurePreserving.symm e hpres).integrable_comp_of_integrable hF
    refine hcomp.congr ?_
    exact Filter.Eventually.of_forall (fun p => by
      rcases p with ⟨z, x⟩
      have he : e.symm (z, x) = Fin.cons z x := by
        ext i <;> simp [e, MeasurableEquiv.piFinSuccAbove]
      calc
        ((fun y : Fin (m + 1) → ℝ => F y * gaussianWeight (m + 1) y) ∘ e.symm) (z, x)
            = F (Fin.cons z x) * gaussianWeight (m + 1) (Fin.cons z x) := by
              simpa [Function.comp] using congrArg (fun y => F y * gaussianWeight (m + 1) y) he
        _ = F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) * gaussianWeight m x := by
              rw [gaussianWeight_cons]
              ring
        _ = G (z, x) := by
              simp [G])
  unfold stdGaussianAvg stdGaussianAvg1
  have hnf :
      (((2 * Real.pi) ^ (((m + 1 : ℕ) : ℝ) / 2))⁻¹)
        =
      (((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹)
        * (((2 * Real.pi) ^ ((m : ℝ) / 2))⁻¹) := by
    exact stdGaussian_normFactor_succ m
  rw [hnf]
  change
    (((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹) * (((2 * Real.pi) ^ ((m : ℝ) / 2))⁻¹)
        * ∫ y : Fin (m + 1) → ℝ, F y * gaussianWeight (m + 1) y
      =
    (((2 * Real.pi) ^ ((m : ℝ) / 2))⁻¹)
      * ∫ x : Fin m → ℝ,
          stdGaussianAvg1 (fun z : ℝ => F (Fin.cons z x)) * gaussianWeight m x
  have hcomp :
      ∫ y : Fin (m + 1) → ℝ, F y * gaussianWeight (m + 1) y
        =
      ∫ p : ℝ × (Fin m → ℝ),
        F (Fin.cons p.1 p.2) * Real.exp (-(p.1 ^ (2 : Nat)) / 2) * gaussianWeight m p.2 := by
    rw [integral_comp_cons_real]
    refine integral_congr_ae ?_
    exact Filter.Eventually.of_forall (fun p => by
      rcases p with ⟨z, x⟩
      simp [gaussianWeight_cons, mul_assoc])
  have hprod :
      ∫ p : ℝ × (Fin m → ℝ),
        F (Fin.cons p.1 p.2) * Real.exp (-(p.1 ^ (2 : Nat)) / 2) * gaussianWeight m p.2
        =
      ∫ x : Fin m → ℝ,
        (∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume)
          * gaussianWeight m x := by
    calc
      ∫ p : ℝ × (Fin m → ℝ),
          F (Fin.cons p.1 p.2) * Real.exp (-(p.1 ^ (2 : Nat)) / 2) * gaussianWeight m p.2
          =
        ∫ x : Fin m → ℝ,
          ∫ z : ℝ, F (Fin.cons z x) * (Real.exp (-(z ^ (2 : Nat)) / 2) * gaussianWeight m x) := by
            simpa [G, mul_assoc] using (MeasureTheory.integral_prod_symm G hG_int)
      _ =
        ∫ x : Fin m → ℝ,
          (∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume)
            * gaussianWeight m x := by
              refine integral_congr_ae ?_
              exact Filter.Eventually.of_forall (fun x => by
                have hinner :
                    ∫ z : ℝ, F (Fin.cons z x) * (Real.exp (-(z ^ (2 : Nat)) / 2) * gaussianWeight m x)
                      =
                    (∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume)
                      * gaussianWeight m x := by
                        rw [show
                            (fun z : ℝ =>
                              F (Fin.cons z x) * (Real.exp (-(z ^ (2 : Nat)) / 2) * gaussianWeight m x))
                              =
                            (fun z : ℝ =>
                              gaussianWeight m x
                                * (F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2))) by
                              funext z
                              ring]
                        rw [MeasureTheory.integral_const_mul]
                        ring
                simpa using hinner)
  rw [hcomp, hprod]
  let c1 : ℝ := ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹
  let c2 : ℝ := ((2 * Real.pi) ^ ((m : ℝ) / 2))⁻¹
  calc
    c1 * c2
        * ∫ x : Fin m → ℝ,
            (∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume)
              * gaussianWeight m x
      = c2 * (c1 *
          ∫ x : Fin m → ℝ,
            (∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume)
              * gaussianWeight m x) := by
            ring
    _ = c2 *
          ∫ x : Fin m → ℝ,
            (c1 * ∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume)
              * gaussianWeight m x := by
            congr 1
            symm
            rw [show
                (fun x : Fin m → ℝ =>
                  (c1 * ∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume)
                    * gaussianWeight m x)
                  =
                (fun x : Fin m → ℝ =>
                  c1 * ((∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume)
                    * gaussianWeight m x)) by
                      funext x
                      ring]
            exact MeasureTheory.integral_const_mul c1
              (fun x : Fin m → ℝ =>
                (∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume)
                  * gaussianWeight m x)
    _ = c2 *
          ∫ x : Fin m → ℝ,
            stdGaussianAvg1 (fun z : ℝ => F (Fin.cons z x)) * gaussianWeight m x := by
            simp [stdGaussianAvg1, c1]
    _ = stdGaussianAvg m (fun x => stdGaussianAvg1 (fun z : ℝ => F (Fin.cons z x))) := by
            simp [stdGaussianAvg, gaussianWeight, c2]

private lemma stdGaussianAvg_one (n : ℕ) :
    stdGaussianAvg n (fun _ : Fin n → ℝ => (1 : ℝ)) = 1 := by
  induction n with
  | zero =>
      simpa using stdGaussianAvg_zero (fun _ : Fin 0 → ℝ => (1 : ℝ))
  | succ n ih =>
      calc
        stdGaussianAvg (n + 1) (fun _ : Fin (n + 1) → ℝ => (1 : ℝ))
            = stdGaussianAvg1 (fun _ : ℝ => (1 : ℝ)) * stdGaussianAvg n (fun _ : Fin n → ℝ => (1 : ℝ)) := by
                simpa using stdGaussianAvg_cons_mul n (fun _ : ℝ => (1 : ℝ)) (fun _ => (1 : ℝ))
        _ = 1 := by simp [stdGaussianAvg1_mass, ih]

private lemma stdGaussianAvg1_mul_const (c : ℝ) (f : ℝ → ℝ) :
    stdGaussianAvg1 (fun z : ℝ => c * f z) = c * stdGaussianAvg1 f := by
  unfold stdGaussianAvg1
  rw [show (fun z : ℝ => (c * f z) * Real.exp (-(z ^ (2 : Nat)) / 2))
      = fun z : ℝ => c * (f z * Real.exp (-(z ^ (2 : Nat)) / 2)) by
        funext z
        ring]
  rw [MeasureTheory.integral_const_mul]
  ring

private lemma stdGaussianAvg1_add (f g : ℝ → ℝ)
    (hf : MeasureTheory.Integrable (fun z : ℝ => f z * Real.exp (-(z ^ (2 : Nat)) / 2)))
    (hg : MeasureTheory.Integrable (fun z : ℝ => g z * Real.exp (-(z ^ (2 : Nat)) / 2))) :
    stdGaussianAvg1 (fun z => f z + g z) = stdGaussianAvg1 f + stdGaussianAvg1 g := by
  unfold stdGaussianAvg1
  change (((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹)
      * (∫ z : ℝ, (f z + g z) * Real.exp (-(z ^ (2 : Nat)) / 2))
    =
    (((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹)
      * (∫ z : ℝ, f z * Real.exp (-(z ^ (2 : Nat)) / 2))
      +
      (((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹)
        * (∫ z : ℝ, g z * Real.exp (-(z ^ (2 : Nat)) / 2))
  rw [show (fun z : ℝ => (f z + g z) * Real.exp (-(z ^ (2 : Nat)) / 2))
      = fun z : ℝ =>
          f z * Real.exp (-(z ^ (2 : Nat)) / 2)
            + g z * Real.exp (-(z ^ (2 : Nat)) / 2) by
        funext z
        ring]
  rw [MeasureTheory.integral_add hf hg]
  ring

private lemma stdGaussianAvg1_sub (f g : ℝ → ℝ)
    (hf : MeasureTheory.Integrable (fun z : ℝ => f z * Real.exp (-(z ^ (2 : Nat)) / 2)))
    (hg : MeasureTheory.Integrable (fun z : ℝ => g z * Real.exp (-(z ^ (2 : Nat)) / 2))) :
    stdGaussianAvg1 (fun z => f z - g z) = stdGaussianAvg1 f - stdGaussianAvg1 g := by
  have hneg :
      MeasureTheory.Integrable
        (fun z : ℝ => ((-1 : ℝ) * g z) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    simpa [mul_assoc] using hg.const_mul (-1 : ℝ)
  calc
    stdGaussianAvg1 (fun z => f z - g z)
      = stdGaussianAvg1 (fun z => f z + (-1 : ℝ) * g z) := by
          congr 1
          funext z
          ring
    _ = stdGaussianAvg1 f + stdGaussianAvg1 (fun z => (-1 : ℝ) * g z) := by
          rw [stdGaussianAvg1_add f (fun z => (-1 : ℝ) * g z) hf hneg]
    _ = stdGaussianAvg1 f - stdGaussianAvg1 g := by
          rw [stdGaussianAvg1_mul_const]
          ring

private lemma stdGaussianAvg_mul_const (n : ℕ) (c : ℝ) (f : (Fin n → ℝ) → ℝ) :
    stdGaussianAvg n (fun x => c * f x) = c * stdGaussianAvg n f := by
  unfold stdGaussianAvg
  have hint :
      ∫ x : Fin n → ℝ, (c * f x) * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2)
        = c * ∫ x : Fin n → ℝ, f x * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2) := by
    rw [show (fun x : Fin n → ℝ => (c * f x) * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2))
        = fun x : Fin n → ℝ => c * (f x * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2)) by
          funext x
          ring]
    rw [MeasureTheory.integral_const_mul]
  rw [hint]
  ring

private lemma stdGaussianAvg_const (n : ℕ) (c : ℝ) :
    stdGaussianAvg n (fun _ : Fin n → ℝ => c) = c := by
  calc
    stdGaussianAvg n (fun _ : Fin n → ℝ => c)
      = stdGaussianAvg n (fun x : Fin n → ℝ => c * (1 : ℝ)) := by
          congr with x
          ring
    _ = c * stdGaussianAvg n (fun _ : Fin n → ℝ => (1 : ℝ)) := stdGaussianAvg_mul_const n c _
    _ = c := by simp [stdGaussianAvg_one]

private lemma stdGaussianAvg_add (n : ℕ) (f g : (Fin n → ℝ) → ℝ)
    (hf : MeasureTheory.Integrable (fun x : Fin n → ℝ => f x * gaussianWeight n x))
    (hg : MeasureTheory.Integrable (fun x : Fin n → ℝ => g x * gaussianWeight n x)) :
    stdGaussianAvg n (fun x => f x + g x) = stdGaussianAvg n f + stdGaussianAvg n g := by
  have hff :
      MeasureTheory.Integrable
        (fun x : Fin n → ℝ => f x * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2)) := by
    simpa [gaussianWeight] using hf
  have hgg :
      MeasureTheory.Integrable
        (fun x : Fin n → ℝ => g x * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2)) := by
    simpa [gaussianWeight] using hg
  unfold stdGaussianAvg
  change (((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹)
      * (∫ x : Fin n → ℝ, (f x + g x) * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2))
    =
    (((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹)
      * (∫ x : Fin n → ℝ, f x * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2))
      +
      (((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹)
        * (∫ x : Fin n → ℝ, g x * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2))
  rw [show (fun x : Fin n → ℝ => (f x + g x) * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2))
      = fun x : Fin n → ℝ =>
          f x * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2)
            + g x * Real.exp (-(∑ i : Fin n, x i ^ (2 : Nat)) / 2) by
        funext x
        ring]
  rw [MeasureTheory.integral_add hff hgg]
  ring

private lemma stdGaussianAvg_sub (n : ℕ) (f g : (Fin n → ℝ) → ℝ)
    (hf : MeasureTheory.Integrable (fun x : Fin n → ℝ => f x * gaussianWeight n x))
    (hg : MeasureTheory.Integrable (fun x : Fin n → ℝ => g x * gaussianWeight n x)) :
    stdGaussianAvg n (fun x => f x - g x) = stdGaussianAvg n f - stdGaussianAvg n g := by
  calc
    stdGaussianAvg n (fun x => f x - g x)
      = stdGaussianAvg n (fun x => f x + (-1 : ℝ) * g x) := by
          congr 1
          funext x
          ring
    _ = stdGaussianAvg n f + stdGaussianAvg n (fun x => (-1 : ℝ) * g x) := by
          rw [stdGaussianAvg_add n f (fun x => (-1 : ℝ) * g x) hf]
          simpa [gaussianWeight, mul_assoc] using hg.const_mul (-1 : ℝ)
    _ = stdGaussianAvg n f - stdGaussianAvg n g := by
          rw [stdGaussianAvg_mul_const]
          ring

private lemma integrable_weighted_cons_mul (m : ℕ) (g : ℝ → ℝ) (h : (Fin m → ℝ) → ℝ)
    (hg : MeasureTheory.Integrable (fun z : ℝ => g z * Real.exp (-(z ^ (2 : Nat)) / 2)))
    (hh : MeasureTheory.Integrable (fun x : Fin m → ℝ => h x * gaussianWeight m x)) :
    MeasureTheory.Integrable
      (fun y : Fin (m + 1) → ℝ => g (y 0) * h (Fin.tail y) * gaussianWeight (m + 1) y) := by
  let e : (Fin (m + 1) → ℝ) → ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  let F : ℝ × (Fin m → ℝ) → ℝ :=
    fun p =>
      (g p.1 * Real.exp (-(p.1 ^ (2 : Nat)) / 2)) * (h p.2 * gaussianWeight m p.2)
  have hF : MeasureTheory.Integrable F := by
    simpa [F] using hg.mul_prod hh
  have hcomp : MeasureTheory.Integrable (F ∘ e) := by
    let hpres := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    exact hpres.integrable_comp_of_integrable hF
  refine hcomp.congr ?_
  exact Filter.Eventually.of_forall (fun y => by
    have he : e y = (y 0, Fin.tail y) := by
      ext i <;> simp [e, MeasurableEquiv.piFinSuccAbove]
    calc
      (F ∘ e) y = F (y 0, Fin.tail y) := by simpa [Function.comp] using congrArg F he
      _ = (g (y 0) * Real.exp (-(y 0 ^ (2 : Nat)) / 2))
            * (h (Fin.tail y) * gaussianWeight m (Fin.tail y)) := by simp [F]
      _ = g (y 0) * h (Fin.tail y) * gaussianWeight (m + 1) y := by
            have hy : Fin.cons (y 0) (Fin.tail y) = y := by
              ext i
              cases i using Fin.cases with
              | zero => simp
              | succ i => simp [Fin.tail]
            rw [← hy, gaussianWeight_cons]
            simp [Fin.tail]
            ring)

private lemma integrable_linForm_gaussianWeight (n : ℕ) (c : Fin n → ℝ) :
    MeasureTheory.Integrable (fun x : Fin n → ℝ => linForm n c x * gaussianWeight n x) := by
  induction n with
  | zero =>
      have hfun :
          (fun x : Fin 0 → ℝ => linForm 0 c x * gaussianWeight 0 x)
            = fun _ : Fin 0 → ℝ => (0 : ℝ) := by
              funext x
              simp [linForm, gaussianWeight_zero]
      rw [hfun]
      simpa using (MeasureTheory.integrable_const (c := (0 : ℝ)))
  | succ n ih =>
      let a : ℝ := c 0
      let c₀ : Fin n → ℝ := Fin.tail c
      have hc : c = Fin.cons a c₀ := by
        ext i
        cases i using Fin.cases with
        | zero => simp [a]
        | succ i => rfl
      rw [hc]
      have hterm1 :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ =>
              (a * y 0) * (1 : ℝ) * gaussianWeight (n + 1) y) := by
        apply integrable_weighted_cons_mul n (fun z => a * z) (fun _ => (1 : ℝ))
        · simpa [mul_assoc] using integrable_one_dim_linear_gaussianWeight.const_mul a
        · simpa using integrable_stdGaussianDensity n
      have hterm2 :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ =>
              (1 : ℝ) * linForm n c₀ (Fin.tail y) * gaussianWeight (n + 1) y) := by
        apply integrable_weighted_cons_mul n (fun _ => (1 : ℝ)) (fun x => linForm n c₀ x)
        · simpa using integrable_one_dim_gaussianWeight
        · simpa using ih c₀
      have hsum :
          (fun y : Fin (n + 1) → ℝ => linForm (n + 1) (Fin.cons a c₀) y * gaussianWeight (n + 1) y)
            =
          (fun y : Fin (n + 1) → ℝ =>
            (a * y 0) * (1 : ℝ) * gaussianWeight (n + 1) y
              + (1 : ℝ) * linForm n c₀ (Fin.tail y) * gaussianWeight (n + 1) y) := by
          funext y
          have hlin :
              linForm (n + 1) (Fin.cons a c₀) y = a * y 0 + linForm n c₀ (Fin.tail y) := by
            unfold linForm
            rw [Fin.sum_univ_succ]
            simp [Fin.cons, Fin.tail]
          rw [hlin]
          ring
      rw [hsum]
      exact hterm1.add hterm2

private lemma integrable_linForm_sq_gaussianWeight (n : ℕ) (c : Fin n → ℝ) :
    MeasureTheory.Integrable (fun x : Fin n → ℝ => linForm n c x ^ (2 : Nat) * gaussianWeight n x) := by
  induction n with
  | zero =>
      have hfun :
          (fun x : Fin 0 → ℝ => linForm 0 c x ^ (2 : Nat) * gaussianWeight 0 x)
            = fun _ : Fin 0 → ℝ => (0 : ℝ) := by
              funext x
              simp [linForm, gaussianWeight_zero]
      rw [hfun]
      simpa using (MeasureTheory.integrable_const (c := (0 : ℝ)))
  | succ n ih =>
      let a : ℝ := c 0
      let c₀ : Fin n → ℝ := Fin.tail c
      have hc : c = Fin.cons a c₀ := by
        ext i
        cases i using Fin.cases with
        | zero => simp [a]
        | succ i => rfl
      rw [hc]
      have hterm1 :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ =>
              (a ^ (2 : Nat) * y 0 ^ (2 : Nat)) * gaussianWeight (n + 1) y) := by
        simpa [mul_assoc] using
          (integrable_weighted_cons_mul n (fun z => a ^ (2 : Nat) * z ^ (2 : Nat)) (fun _ => (1 : ℝ))
            (by simpa [mul_assoc] using integrable_one_dim_sq_gaussianWeight.const_mul (a ^ (2 : Nat)))
            (by simpa using integrable_stdGaussianDensity n))
      have hterm2 :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ =>
              ((2 * a * y 0) * linForm n c₀ (Fin.tail y)) * gaussianWeight (n + 1) y) := by
        apply integrable_weighted_cons_mul n (fun z => 2 * a * z) (fun x => linForm n c₀ x)
        · simpa [mul_assoc] using integrable_one_dim_linear_gaussianWeight.const_mul (2 * a)
        · simpa using integrable_linForm_gaussianWeight n c₀
      have hterm3 :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ =>
              (linForm n c₀ (Fin.tail y) ^ (2 : Nat)) * gaussianWeight (n + 1) y) := by
        simpa [mul_assoc] using
          (integrable_weighted_cons_mul n (fun _ => (1 : ℝ)) (fun x => linForm n c₀ x ^ (2 : Nat))
            (by simpa using integrable_one_dim_gaussianWeight)
            (by simpa using ih c₀))
      have hsum :
          (fun y : Fin (n + 1) → ℝ =>
            linForm (n + 1) (Fin.cons a c₀) y ^ (2 : Nat) * gaussianWeight (n + 1) y)
            =
          (fun y : Fin (n + 1) → ℝ =>
            (a ^ (2 : Nat) * y 0 ^ (2 : Nat)) * gaussianWeight (n + 1) y
              + (((2 * a * y 0) * linForm n c₀ (Fin.tail y)) * gaussianWeight (n + 1) y
                + (linForm n c₀ (Fin.tail y) ^ (2 : Nat)) * gaussianWeight (n + 1) y)) := by
          funext y
          have hlin :
              linForm (n + 1) (Fin.cons a c₀) y = a * y 0 + linForm n c₀ (Fin.tail y) := by
            unfold linForm
            rw [Fin.sum_univ_succ]
            simp [Fin.cons, Fin.tail]
          rw [hlin]
          ring
      rw [hsum]
      exact hterm1.add (hterm2.add hterm3)

private lemma stdGaussianAvg_linForm_sq_eq_sum_sq (n : ℕ) (c : Fin n → ℝ) :
    stdGaussianAvg n (fun x => linForm n c x ^ (2 : Nat)) = ∑ i : Fin n, c i ^ (2 : Nat) := by
  induction n with
  | zero =>
      simp [stdGaussianAvg_zero, linForm]
  | succ n ih =>
      let a : ℝ := c 0
      let c₀ : Fin n → ℝ := Fin.tail c
      have hc : c = Fin.cons a c₀ := by
        ext i
        cases i using Fin.cases with
        | zero => simp [a]
        | succ i => rfl
      rw [hc]
      let F1 : (Fin (n + 1) → ℝ) → ℝ := fun y => a ^ (2 : Nat) * y 0 ^ (2 : Nat)
      let F2 : (Fin (n + 1) → ℝ) → ℝ := fun y => (2 * a * y 0) * linForm n c₀ (Fin.tail y)
      let F3 : (Fin (n + 1) → ℝ) → ℝ := fun y => linForm n c₀ (Fin.tail y) ^ (2 : Nat)
      have h1int :
          MeasureTheory.Integrable (fun y : Fin (n + 1) → ℝ => F1 y * gaussianWeight (n + 1) y) := by
        simpa [F1, mul_assoc] using
          (integrable_weighted_cons_mul n (fun z => a ^ (2 : Nat) * z ^ (2 : Nat)) (fun _ => (1 : ℝ))
            (by simpa [mul_assoc] using integrable_one_dim_sq_gaussianWeight.const_mul (a ^ (2 : Nat)))
            (by simpa using integrable_stdGaussianDensity n))
      have h2int :
          MeasureTheory.Integrable (fun y : Fin (n + 1) → ℝ => F2 y * gaussianWeight (n + 1) y) := by
        simpa [F2, mul_assoc] using
          (integrable_weighted_cons_mul n (fun z => 2 * a * z) (fun x => linForm n c₀ x)
            (by simpa [mul_assoc] using integrable_one_dim_linear_gaussianWeight.const_mul (2 * a))
            (by simpa using integrable_linForm_gaussianWeight n c₀))
      have h3int :
          MeasureTheory.Integrable (fun y : Fin (n + 1) → ℝ => F3 y * gaussianWeight (n + 1) y) := by
        simpa [F3, mul_assoc] using
          (integrable_weighted_cons_mul n (fun _ => (1 : ℝ)) (fun x => linForm n c₀ x ^ (2 : Nat))
            (by simpa using integrable_one_dim_gaussianWeight)
            (by simpa using integrable_linForm_sq_gaussianWeight n c₀))
      have h23int :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ => (F2 y + F3 y) * gaussianWeight (n + 1) y) := by
        simpa [F2, F3, mul_add, add_mul, add_assoc] using h2int.add h3int
      have hfun :
          (fun y : Fin (n + 1) → ℝ => linForm (n + 1) (Fin.cons a c₀) y ^ (2 : Nat))
            =
          (fun y : Fin (n + 1) → ℝ => F1 y + (F2 y + F3 y)) := by
          funext y
          have hlin :
              linForm (n + 1) (Fin.cons a c₀) y = a * y 0 + linForm n c₀ (Fin.tail y) := by
            unfold linForm
            rw [Fin.sum_univ_succ]
            simp [Fin.cons, Fin.tail]
          rw [hlin]
          ring
      rw [hfun]
      rw [stdGaussianAvg_add (n + 1) F1 (fun y => F2 y + F3 y) h1int h23int]
      rw [stdGaussianAvg_add (n + 1) F2 F3 h2int h3int]
      have h1 :
          stdGaussianAvg (n + 1) F1 = a ^ (2 : Nat) := by
        calc
          stdGaussianAvg (n + 1) F1
              = stdGaussianAvg1 (fun z => a ^ (2 : Nat) * z ^ (2 : Nat)) * stdGaussianAvg n (fun _ => (1 : ℝ)) := by
                  simpa [F1] using
                    (stdGaussianAvg_cons_mul n (fun z => a ^ (2 : Nat) * z ^ (2 : Nat))
                      (fun _ => (1 : ℝ)))
          _ = (a ^ (2 : Nat) * stdGaussianAvg1 (fun z => z ^ (2 : Nat))) * 1 := by
                rw [stdGaussianAvg_one, stdGaussianAvg1_mul_const]
          _ = a ^ (2 : Nat) := by simp [stdGaussianAvg1_sq]
      have h2 :
          stdGaussianAvg (n + 1) F2 = 0 := by
        have hzero :
            stdGaussianAvg n (fun x => linForm n c₀ x) = 0 := by
          have hint :
              ∫ x : Fin n → ℝ, linForm n c₀ x * gaussianWeight n x = 0 :=
            by
              let g : (Fin n → ℝ) → ℝ := fun x => linForm n c₀ x * gaussianWeight n x
              have hcomp :
                  ∫ x : Fin n → ℝ, g x = ∫ x : Fin n → ℝ, g (-x) := by
                    symm
                    simpa [g] using
                      (Measure.measurePreserving_neg (volume : Measure (Fin n → ℝ))).integral_comp'
                        (f := MeasurableEquiv.neg (Fin n → ℝ)) (g := g)
              have hneg :
                  g = fun x : Fin n → ℝ => -g (-x) := by
                funext x
                have hgw : gaussianWeight n (-x) = gaussianWeight n x := by
                  unfold gaussianWeight
                  have hsum : ∑ i : Fin n, (-x i) ^ (2 : Nat) = ∑ i : Fin n, x i ^ (2 : Nat) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    simp
                  simp [hsum]
                have hlin : linForm n c₀ (-x) = -linForm n c₀ x := by
                  unfold linForm
                  simp
                simp [g, hgw, hlin, mul_comm]
              have hzero' : ∫ x : Fin n → ℝ, g x = -∫ x : Fin n → ℝ, g x := by
                calc
                  ∫ x : Fin n → ℝ, g x = ∫ x : Fin n → ℝ, -g (-x) := by
                    refine MeasureTheory.integral_congr_ae ?_
                    exact Filter.Eventually.of_forall (fun x => by
                      have hx := congrFun hneg x
                      simpa using hx)
                  _ = -∫ x : Fin n → ℝ, g (-x) := by rw [MeasureTheory.integral_neg]
                  _ = -∫ x : Fin n → ℝ, g x := by rw [← hcomp]
              have hsum := congrArg (fun t : ℝ => t + ∫ x : Fin n → ℝ, g x) hzero'
              simpa [g] using hsum
          calc
            stdGaussianAvg n (fun x => linForm n c₀ x)
              = ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ *
                  ∫ x : Fin n → ℝ, linForm n c₀ x * gaussianWeight n x := by
                    simp [stdGaussianAvg, gaussianWeight]
            _ = ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ * 0 := by rw [hint]
            _ = 0 := by ring
        calc
          stdGaussianAvg (n + 1) F2
              = stdGaussianAvg1 (fun z => 2 * a * z) * stdGaussianAvg n (fun x => linForm n c₀ x) := by
                  simpa [F2] using
                    (stdGaussianAvg_cons_mul n (fun z => 2 * a * z) (fun x => linForm n c₀ x))
          _ = 0 := by
                rw [hzero]
                ring
      have h3 :
          stdGaussianAvg (n + 1) F3 = ∑ i : Fin n, c₀ i ^ (2 : Nat) := by
        calc
          stdGaussianAvg (n + 1) F3
              = stdGaussianAvg1 (fun _ => (1 : ℝ)) * stdGaussianAvg n (fun x => linForm n c₀ x ^ (2 : Nat)) := by
                    simpa [F3] using
                      (stdGaussianAvg_cons_mul n (fun _ => (1 : ℝ))
                        (fun x => linForm n c₀ x ^ (2 : Nat)))
          _ = ∑ i : Fin n, c₀ i ^ (2 : Nat) := by simpa [stdGaussianAvg1_mass, ih]
      rw [h1, h2, h3]
      rw [Fin.sum_univ_succ]
      simpa [a, c₀]

/-- The boundary coordinate separating the sign block from the Gaussian block, written in the
canonical type `Fin ((n + m) + 1)` as the first Gaussian slot. -/
private def boundaryIndex (n m : ℕ) : Fin ((n + m) + 1) :=
  Fin.natAdd n (0 : Fin (m + 1))

private lemma boundaryIndex_eq_fin (n m : ℕ) :
    boundaryIndex n m = ⟨n, by omega⟩ := by
  apply Fin.ext
  simp [boundaryIndex]

private lemma kernelInfluence_cast_eq {N M : ℕ} (h : N = M)
    (f : Fin M → Fin M → ℝ) (k : Fin N) :
    kernelInfluence N (fun i j : Fin N => f (Fin.cast h i) (Fin.cast h j)) k
      = kernelInfluence M f (Fin.cast h k) := by
  subst h
  simp [kernelInfluence]

private lemma succAbove_boundaryIndex_castAdd (n m : ℕ) (i : Fin n) :
    (boundaryIndex n m).succAbove (Fin.castAdd m i) = Fin.castAdd (m + 1) i := by
  rw [Fin.succAbove_of_castSucc_lt]
  · simp [Fin.castSucc_castAdd]
  · simp [boundaryIndex, Fin.lt_def]

private lemma succAbove_boundaryIndex_natAdd (n m : ℕ) (j : Fin m) :
    (boundaryIndex n m).succAbove (Fin.natAdd n j) = Fin.natAdd n j.succ := by
  rw [Fin.succAbove_of_le_castSucc]
  · simp [Fin.succ_natAdd]
  · simp [boundaryIndex, Fin.le_def]

/-- Remove one coordinate from a quadratic kernel by restricting along `succAbove`. -/
private def minorKernelAt {n : ℕ} (k : Fin (n + 1)) (f : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => f (k.succAbove i) (k.succAbove j)

/-- The linear coefficients created by exposing the `k`-th coordinate in an ordered quadratic
form. -/
private def rowKernelAt {n : ℕ} (k : Fin (n + 1)) (f : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin n → ℝ :=
  fun i => 2 * f k (k.succAbove i)

private lemma minorKernelAt_symm {n : ℕ} (k : Fin (n + 1))
    (f : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsymm : ∀ i j, f i j = f j i) :
    ∀ i j, minorKernelAt k f i j = minorKernelAt k f j i := by
  intro i j
  exact hsymm _ _

private lemma minorKernelAt_diag {n : ℕ} (k : Fin (n + 1))
    (f : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hdiag : ∀ i, f i i = 0) :
    ∀ i, minorKernelAt k f i i = 0 := by
  intro i
  exact hdiag _

private lemma Q2Gauss_insertNth {n : ℕ} (k : Fin (n + 1))
    (f : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0)
    (ξ : ℝ) (y : Fin n → ℝ) :
    Q2Gauss (n + 1) f (Fin.insertNth k ξ y)
      = Q2Gauss n (minorKernelAt k f) y + ξ * linForm n (rowKernelAt k f) y := by
  let x : Fin (n + 1) → ℝ := Fin.insertNth k ξ y
  have hxk : x k = ξ := by
    simp [x]
  have hxs : ∀ i : Fin n, x (k.succAbove i) = y i := by
    intro i
    simp [x]
  unfold Q2Gauss linForm minorKernelAt rowKernelAt
  calc
    ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), f i j * x i * x j
      = (∑ j : Fin (n + 1), f k j * x k * x j)
          + ∑ i : Fin n, ∑ j : Fin (n + 1), f (k.succAbove i) j * x (k.succAbove i) * x j := by
            rw [Fin.sum_univ_succAbove _ k]
    _ = (f k k * ξ * ξ
          + ∑ j : Fin n, f k (k.succAbove j) * ξ * y j)
          + (∑ i : Fin n, f (k.succAbove i) k * y i * ξ
              + ∑ i : Fin n, ∑ j : Fin n,
                  f (k.succAbove i) (k.succAbove j) * y i * y j) := by
            rw [Fin.sum_univ_succAbove _ k]
            simp [hxk, hxs]
            have hsplit_inner :
                (∑ i : Fin n, ∑ j : Fin (n + 1), f (k.succAbove i) j * y i * x j)
                  =
                ∑ i : Fin n,
                  (f (k.succAbove i) k * y i * ξ
                    + ∑ j : Fin n, f (k.succAbove i) (k.succAbove j) * y i * y j) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      rw [Fin.sum_univ_succAbove _ k]
                      simp [hxk, hxs]
            rw [hsplit_inner, Finset.sum_add_distrib]
    _ = (∑ i : Fin n, ∑ j : Fin n,
            f (k.succAbove i) (k.succAbove j) * y i * y j)
          + ξ * (∑ i : Fin n, (2 * f k (k.succAbove i)) * y i) := by
            have hdiagk : f k k = 0 := hdiag k
            have hsymm' : ∀ i : Fin n, f (k.succAbove i) k = f k (k.succAbove i) := by
              intro i
              exact hsymm _ _
            calc
              (f k k * ξ * ξ + ∑ j : Fin n, f k (k.succAbove j) * ξ * y j)
                  + (∑ i : Fin n, f (k.succAbove i) k * y i * ξ
                      + ∑ i : Fin n, ∑ j : Fin n,
                          f (k.succAbove i) (k.succAbove j) * y i * y j)
                =
              (∑ i : Fin n, ∑ j : Fin n,
                  f (k.succAbove i) (k.succAbove j) * y i * y j)
                + (f k k * ξ * ξ
                    + ((∑ j : Fin n, f k (k.succAbove j) * ξ * y j)
                        + ∑ i : Fin n, f (k.succAbove i) k * y i * ξ)) := by
                    ring
              _ =
              (∑ i : Fin n, ∑ j : Fin n,
                  f (k.succAbove i) (k.succAbove j) * y i * y j)
                + ((∑ j : Fin n, f k (k.succAbove j) * ξ * y j)
                    + ∑ i : Fin n, f (k.succAbove i) k * y i * ξ) := by
                      rw [hdiagk]
                      ring
              _ =
              (∑ i : Fin n, ∑ j : Fin n,
                  f (k.succAbove i) (k.succAbove j) * y i * y j)
                + ξ * (∑ i : Fin n, (2 * f k (k.succAbove i)) * y i) := by
                    congr 1
                    calc
                      (∑ j : Fin n, f k (k.succAbove j) * ξ * y j)
                          + ∑ i : Fin n, f (k.succAbove i) k * y i * ξ
                        = ∑ i : Fin n,
                            (f k (k.succAbove i) * ξ * y i + f (k.succAbove i) k * y i * ξ) := by
                              rw [← Finset.sum_add_distrib]
                      _ = ∑ i : Fin n, ξ * ((2 * f k (k.succAbove i)) * y i) := by
                            refine Finset.sum_congr rfl ?_
                            intro i hi
                            rw [hsymm' i]
                            ring
                      _ = ξ * (∑ i : Fin n, (2 * f k (k.succAbove i)) * y i) := by
                            rw [Finset.mul_sum]
    _ = Q2Gauss n (minorKernelAt k f) y + ξ * linForm n (rowKernelAt k f) y := by
          rfl

private lemma insert_boundary_gaussian_hybridPoint (n m : ℕ) (σ : Fin n → Fin 2)
    (x : Fin m → ℝ) (z : ℝ) :
    Fin.insertNth (boundaryIndex n m) z (hybridPoint n m σ x)
      = hybridPoint n (m + 1) σ (Fin.cons z x) := by
  refine (Fin.insertNth_eq_iff).2 ?_
  constructor
  · simp [boundaryIndex, hybridPoint, Fin.append_right]
  · change hybridPoint n m σ x
        = Fin.removeNth (boundaryIndex n m) (hybridPoint n (m + 1) σ (Fin.cons z x))
    rw [funext_iff, Fin.forall_fin_add]
    constructor
    · intro i
      simp [Fin.removeNth, hybridPoint, succAbove_boundaryIndex_castAdd]
    · intro j
      rw [Fin.removeNth_apply, succAbove_boundaryIndex_natAdd]
      simp [hybridPoint, Fin.succ_natAdd, Fin.append_right]

/-- The sign-side hybrid point with the new sign inserted at the boundary index, but viewed in the
canonical type `Fin (n + m + 1) → ℝ`. -/
private def boundarySignHybridPoint (n m : ℕ) (σ : Fin n → Fin 2)
    (b : Fin 2) (x : Fin m → ℝ) : Fin (n + m + 1) → ℝ :=
  fun j => hybridPoint (n + 1) m (Fin.snoc σ b) x (Fin.cast (by omega) j)

private lemma cast_boundaryIndex_boundarySign (n m : ℕ) :
    Fin.cast (by omega : n + m + 1 = (n + 1) + m) (boundaryIndex n m)
      = Fin.castAdd m (Fin.last n) := by
  apply Fin.ext
  simp [boundaryIndex]

private lemma cast_castAdd_boundarySign (n m : ℕ) (i : Fin n) :
    Fin.cast (by omega : n + m + 1 = (n + 1) + m) (Fin.castAdd (m + 1) i)
      = Fin.castAdd m (Fin.castSucc i) := by
  apply Fin.ext
  simp

private lemma cast_natAdd_boundarySign (n m : ℕ) (j : Fin m) :
    Fin.cast (by omega : n + m + 1 = (n + 1) + m) (Fin.natAdd n j.succ)
      = Fin.natAdd (n + 1) j := by
  apply Fin.ext
  simp
  omega

private lemma insert_boundary_sign_hybridPoint (n m : ℕ) (σ : Fin n → Fin 2)
    (x : Fin m → ℝ) (b : Fin 2) :
    Fin.insertNth (boundaryIndex n m) (((signOf b : ℤ) : ℝ)) (hybridPoint n m σ x)
      = boundarySignHybridPoint n m σ b x := by
  refine (Fin.insertNth_eq_iff).2 ?_
  constructor
  · rw [boundarySignHybridPoint, cast_boundaryIndex_boundarySign]
    simp [boundaryIndex, hybridPoint]
  · change hybridPoint n m σ x
        = Fin.removeNth (boundaryIndex n m) (boundarySignHybridPoint n m σ b x)
    rw [funext_iff, Fin.forall_fin_add]
    constructor
    · intro i
      rw [Fin.removeNth_apply, succAbove_boundaryIndex_castAdd]
      rw [boundarySignHybridPoint, cast_castAdd_boundarySign]
      simp [hybridPoint]
    · intro j
      rw [Fin.removeNth_apply, succAbove_boundaryIndex_natAdd]
      rw [boundarySignHybridPoint, cast_natAdd_boundarySign]
      simp [hybridPoint, Fin.append_right]

private lemma Q2Gauss_boundary_gaussian (n m : ℕ)
    (lam : Fin (n + m + 1) → Fin (n + m + 1) → ℝ)
    (hsymm : ∀ i j, lam i j = lam j i) (hdiag : ∀ i, lam i i = 0)
    (σ : Fin n → Fin 2) (x : Fin m → ℝ) (z : ℝ) :
    Q2Gauss (n + m + 1) lam (hybridPoint n (m + 1) σ (Fin.cons z x))
      =
    Q2Gauss (n + m) (minorKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)
      + z * linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x) := by
  rw [← insert_boundary_gaussian_hybridPoint n m σ x z]
  simpa using
    (Q2Gauss_insertNth (boundaryIndex n m) lam hsymm hdiag z (hybridPoint n m σ x))

private lemma Q2Gauss_boundary_sign (n m : ℕ)
    (lam : Fin (n + m + 1) → Fin (n + m + 1) → ℝ)
    (hsymm : ∀ i j, lam i j = lam j i) (hdiag : ∀ i, lam i i = 0)
    (σ : Fin n → Fin 2) (x : Fin m → ℝ) (b : Fin 2) :
    Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)
      =
    Q2Gauss (n + m) (minorKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)
      + (((signOf b : ℤ) : ℝ))
          * linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x) := by
  rw [← insert_boundary_sign_hybridPoint n m σ x b]
  simpa using
    (Q2Gauss_insertNth (boundaryIndex n m) lam hsymm hdiag (((signOf b : ℤ) : ℝ))
      (hybridPoint n m σ x))

private lemma Q2Gauss_castKernel_eq {N M : ℕ} (h : N = M)
    (lam : Fin M → Fin M → ℝ) (x : Fin N → ℝ) :
    Q2Gauss N (fun i j : Fin N => lam (Fin.cast h i) (Fin.cast h j)) x
      = Q2Gauss M lam (fun i : Fin M => x (Fin.cast h.symm i)) := by
  subst h
  simp [Q2Gauss]

private lemma linForm_neg (n : ℕ) (c : Fin n → ℝ) (x : Fin n → ℝ) :
    linForm n c (-x) = -linForm n c x := by
  unfold linForm
  simp

private lemma gaussianWeight_neg (n : ℕ) (x : Fin n → ℝ) :
    gaussianWeight n (-x) = gaussianWeight n x := by
  unfold gaussianWeight
  have hsum : ∑ i : Fin n, (-x i) ^ (2 : Nat) = ∑ i : Fin n, x i ^ (2 : Nat) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp
  simp [hsum]

private lemma integral_odd_gaussianWeight_zero_fin (n : ℕ) (f : (Fin n → ℝ) → ℝ)
    (hfodd : ∀ x : Fin n → ℝ, f (-x) = -f x) :
    ∫ x : Fin n → ℝ, f x * gaussianWeight n x = 0 := by
  let g : (Fin n → ℝ) → ℝ := fun x => f x * gaussianWeight n x
  have hcomp :
      ∫ x : Fin n → ℝ, g x = ∫ x : Fin n → ℝ, g (-x) := by
        symm
        simpa [g] using
          (Measure.measurePreserving_neg (volume : Measure (Fin n → ℝ))).integral_comp'
            (f := MeasurableEquiv.neg (Fin n → ℝ)) (g := g)
  have hneg :
      g = fun x : Fin n → ℝ => -g (-x) := by
    funext x
    simp [g, hfodd x, gaussianWeight_neg]
  have hzero : ∫ x : Fin n → ℝ, g x = -∫ x : Fin n → ℝ, g x := by
    calc
      ∫ x : Fin n → ℝ, g x = ∫ x : Fin n → ℝ, -g (-x) := by
        refine MeasureTheory.integral_congr_ae ?_
        exact Filter.Eventually.of_forall (fun x => by
          have hx := congrFun hneg x
          simpa using hx)
      _ = -∫ x : Fin n → ℝ, g (-x) := by rw [MeasureTheory.integral_neg]
      _ = -∫ x : Fin n → ℝ, g x := by rw [← hcomp]
  have hsum := congrArg (fun t : ℝ => t + ∫ x : Fin n → ℝ, g x) hzero
  simpa [g] using hsum

private lemma stdGaussianAvg_linForm_zero (n : ℕ) (c : Fin n → ℝ) :
    stdGaussianAvg n (fun x => linForm n c x) = 0 := by
  have hint :
      ∫ x : Fin n → ℝ, linForm n c x * gaussianWeight n x = 0 :=
    integral_odd_gaussianWeight_zero_fin n (fun x => linForm n c x) (by
      intro x
      simpa using linForm_neg n c x)
  calc
    stdGaussianAvg n (fun x => linForm n c x)
      = ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ *
          ∫ x : Fin n → ℝ, linForm n c x * gaussianWeight n x := by
            simp [stdGaussianAvg, gaussianWeight]
    _ = ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ * 0 := by rw [hint]
    _ = 0 := by ring

private lemma integrable_linForm_cube_gaussianWeight (n : ℕ) (c : Fin n → ℝ) :
    MeasureTheory.Integrable (fun x : Fin n → ℝ => linForm n c x ^ (3 : Nat) * gaussianWeight n x) := by
  induction n with
  | zero =>
      have hfun :
          (fun x : Fin 0 → ℝ => linForm 0 c x ^ (3 : Nat) * gaussianWeight 0 x)
            = fun _ : Fin 0 → ℝ => (0 : ℝ) := by
              funext x
              simp [linForm, gaussianWeight_zero]
      rw [hfun]
      simpa using (MeasureTheory.integrable_const (c := (0 : ℝ)))
  | succ n ih =>
      let a : ℝ := c 0
      let c₀ : Fin n → ℝ := Fin.tail c
      have hc : c = Fin.cons a c₀ := by
        ext i
        cases i using Fin.cases with
        | zero => simp [a]
        | succ i => rfl
      rw [hc]
      have hterm1 :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ =>
              (a ^ (3 : Nat) * y 0 ^ (3 : Nat)) * gaussianWeight (n + 1) y) := by
        simpa [mul_assoc] using
          (integrable_weighted_cons_mul n (fun z => a ^ (3 : Nat) * z ^ (3 : Nat)) (fun _ => (1 : ℝ))
            (by
              simpa [mul_assoc] using
                integrable_one_dim_cube_gaussianWeight.const_mul (a ^ (3 : Nat)))
            (by simpa using integrable_stdGaussianDensity n))
      have hterm2 :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ =>
              ((3 * a ^ (2 : Nat) * y 0 ^ (2 : Nat)) * linForm n c₀ (Fin.tail y))
                * gaussianWeight (n + 1) y) := by
        simpa [mul_assoc] using
          (integrable_weighted_cons_mul n
            (fun z => 3 * a ^ (2 : Nat) * z ^ (2 : Nat))
            (fun x => linForm n c₀ x)
            (by
              simpa [mul_assoc] using
                integrable_one_dim_sq_gaussianWeight.const_mul (3 * a ^ (2 : Nat)))
            (by simpa using integrable_linForm_gaussianWeight n c₀))
      have hterm3 :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ =>
              ((3 * a * y 0) * linForm n c₀ (Fin.tail y) ^ (2 : Nat))
                * gaussianWeight (n + 1) y) := by
        simpa [mul_assoc] using
          (integrable_weighted_cons_mul n
            (fun z => 3 * a * z)
            (fun x => linForm n c₀ x ^ (2 : Nat))
            (by
              simpa [mul_assoc] using
                integrable_one_dim_linear_gaussianWeight.const_mul (3 * a))
            (by simpa using integrable_linForm_sq_gaussianWeight n c₀))
      have hterm4 :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ =>
              (linForm n c₀ (Fin.tail y) ^ (3 : Nat)) * gaussianWeight (n + 1) y) := by
        simpa [mul_assoc] using
          (integrable_weighted_cons_mul n (fun _ => (1 : ℝ)) (fun x => linForm n c₀ x ^ (3 : Nat))
            (by simpa using integrable_one_dim_gaussianWeight)
            (by simpa using ih c₀))
      have hsum :
          (fun y : Fin (n + 1) → ℝ =>
            linForm (n + 1) (Fin.cons a c₀) y ^ (3 : Nat) * gaussianWeight (n + 1) y)
            =
          (fun y : Fin (n + 1) → ℝ =>
            (a ^ (3 : Nat) * y 0 ^ (3 : Nat)) * gaussianWeight (n + 1) y
              + ((((3 * a ^ (2 : Nat) * y 0 ^ (2 : Nat)) * linForm n c₀ (Fin.tail y))
                    * gaussianWeight (n + 1) y)
                + ((((3 * a * y 0) * linForm n c₀ (Fin.tail y) ^ (2 : Nat))
                      * gaussianWeight (n + 1) y)
                  + (linForm n c₀ (Fin.tail y) ^ (3 : Nat)) * gaussianWeight (n + 1) y))) := by
          funext y
          have hlin :
              linForm (n + 1) (Fin.cons a c₀) y = a * y 0 + linForm n c₀ (Fin.tail y) := by
            unfold linForm
            rw [Fin.sum_univ_succ]
            simp [Fin.cons, Fin.tail]
          rw [hlin]
          ring
      rw [hsum]
      exact hterm1.add (hterm2.add (hterm3.add hterm4))

private lemma stdGaussianAvg_linForm_cube_zero (n : ℕ) (c : Fin n → ℝ) :
    stdGaussianAvg n (fun x => linForm n c x ^ (3 : Nat)) = 0 := by
  have hint :
      ∫ x : Fin n → ℝ, linForm n c x ^ (3 : Nat) * gaussianWeight n x = 0 := by
    apply integral_odd_gaussianWeight_zero_fin n (fun x => linForm n c x ^ (3 : Nat))
    intro x
    have hlin : linForm n c (-x) = -linForm n c x := by
      unfold linForm
      simp
    rw [hlin]
    ring
  calc
    stdGaussianAvg n (fun x => linForm n c x ^ (3 : Nat))
      = ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ *
          ∫ x : Fin n → ℝ, linForm n c x ^ (3 : Nat) * gaussianWeight n x := by
            simp [stdGaussianAvg, gaussianWeight]
    _ = ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ * 0 := by rw [hint]
    _ = 0 := by ring

private lemma integrable_linForm_four_gaussianWeight (n : ℕ) (c : Fin n → ℝ) :
    MeasureTheory.Integrable (fun x : Fin n → ℝ => linForm n c x ^ (4 : Nat) * gaussianWeight n x) := by
  induction n with
  | zero =>
      have hfun :
          (fun x : Fin 0 → ℝ => linForm 0 c x ^ (4 : Nat) * gaussianWeight 0 x)
            = fun _ : Fin 0 → ℝ => (0 : ℝ) := by
              funext x
              simp [linForm, gaussianWeight_zero]
      rw [hfun]
      simpa using (MeasureTheory.integrable_const (c := (0 : ℝ)))
  | succ n ih =>
      let a : ℝ := c 0
      let c₀ : Fin n → ℝ := Fin.tail c
      have hc : c = Fin.cons a c₀ := by
        ext i
        cases i using Fin.cases with
        | zero => simp [a]
        | succ i => rfl
      rw [hc]
      have hterm1 :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ =>
              (a ^ (4 : Nat) * y 0 ^ (4 : Nat)) * gaussianWeight (n + 1) y) := by
        simpa [mul_assoc] using
          (integrable_weighted_cons_mul n (fun z => a ^ (4 : Nat) * z ^ (4 : Nat)) (fun _ => (1 : ℝ))
            (by
              simpa [mul_assoc] using
                integrable_one_dim_four_gaussianWeight.const_mul (a ^ (4 : Nat)))
            (by simpa using integrable_stdGaussianDensity n))
      have hterm2 :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ =>
              ((4 * a ^ (3 : Nat) * y 0 ^ (3 : Nat)) * linForm n c₀ (Fin.tail y))
                * gaussianWeight (n + 1) y) := by
        simpa [mul_assoc] using
          (integrable_weighted_cons_mul n
            (fun z => 4 * a ^ (3 : Nat) * z ^ (3 : Nat))
            (fun x => linForm n c₀ x)
            (by
              simpa [mul_assoc] using
                integrable_one_dim_cube_gaussianWeight.const_mul (4 * a ^ (3 : Nat)))
            (by simpa using integrable_linForm_gaussianWeight n c₀))
      have hterm3 :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ =>
              ((6 * a ^ (2 : Nat) * y 0 ^ (2 : Nat)) * linForm n c₀ (Fin.tail y) ^ (2 : Nat))
                * gaussianWeight (n + 1) y) := by
        simpa [mul_assoc] using
          (integrable_weighted_cons_mul n
            (fun z => 6 * a ^ (2 : Nat) * z ^ (2 : Nat))
            (fun x => linForm n c₀ x ^ (2 : Nat))
            (by
              simpa [mul_assoc] using
                integrable_one_dim_sq_gaussianWeight.const_mul (6 * a ^ (2 : Nat)))
            (by simpa using integrable_linForm_sq_gaussianWeight n c₀))
      have hterm4 :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ =>
              ((4 * a * y 0) * linForm n c₀ (Fin.tail y) ^ (3 : Nat))
                * gaussianWeight (n + 1) y) := by
        simpa [mul_assoc] using
          (integrable_weighted_cons_mul n
            (fun z => 4 * a * z)
            (fun x => linForm n c₀ x ^ (3 : Nat))
            (by
              simpa [mul_assoc] using
                integrable_one_dim_linear_gaussianWeight.const_mul (4 * a))
            (by simpa using integrable_linForm_cube_gaussianWeight n c₀))
      have hterm5 :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ =>
              (linForm n c₀ (Fin.tail y) ^ (4 : Nat)) * gaussianWeight (n + 1) y) := by
        simpa [mul_assoc] using
          (integrable_weighted_cons_mul n (fun _ => (1 : ℝ)) (fun x => linForm n c₀ x ^ (4 : Nat))
            (by simpa using integrable_one_dim_gaussianWeight)
            (by simpa using ih c₀))
      have hsum :
          (fun y : Fin (n + 1) → ℝ =>
            linForm (n + 1) (Fin.cons a c₀) y ^ (4 : Nat) * gaussianWeight (n + 1) y)
            =
          (fun y : Fin (n + 1) → ℝ =>
            (a ^ (4 : Nat) * y 0 ^ (4 : Nat)) * gaussianWeight (n + 1) y
              + ((((4 * a ^ (3 : Nat) * y 0 ^ (3 : Nat)) * linForm n c₀ (Fin.tail y))
                    * gaussianWeight (n + 1) y)
                + ((((6 * a ^ (2 : Nat) * y 0 ^ (2 : Nat)) * linForm n c₀ (Fin.tail y) ^ (2 : Nat))
                      * gaussianWeight (n + 1) y)
                  + ((((4 * a * y 0) * linForm n c₀ (Fin.tail y) ^ (3 : Nat))
                        * gaussianWeight (n + 1) y)
                    + (linForm n c₀ (Fin.tail y) ^ (4 : Nat)) * gaussianWeight (n + 1) y)))) := by
          funext y
          have hlin :
              linForm (n + 1) (Fin.cons a c₀) y = a * y 0 + linForm n c₀ (Fin.tail y) := by
            unfold linForm
            rw [Fin.sum_univ_succ]
            simp [Fin.cons, Fin.tail]
          rw [hlin]
          ring
      rw [hsum]
      exact hterm1.add (hterm2.add (hterm3.add (hterm4.add hterm5)))

private lemma integrable_abs_affine_linForm_cube_gaussianWeight
    (n : ℕ) (a : ℝ) (c : Fin n → ℝ) :
    MeasureTheory.Integrable
      (fun x : Fin n → ℝ => |a + linForm n c x| ^ (3 : Nat) * gaussianWeight n x) := by
  have hpoly :
      MeasureTheory.Integrable
        (fun x : Fin n → ℝ => (a + linForm n c x) ^ (3 : Nat) * gaussianWeight n x) := by
    have h1 :
        MeasureTheory.Integrable
          (fun x : Fin n → ℝ => a ^ (3 : Nat) * gaussianWeight n x) := by
      simpa [mul_assoc] using (integrable_stdGaussianDensity n).const_mul (a ^ (3 : Nat))
    have h2 :
        MeasureTheory.Integrable
          (fun x : Fin n → ℝ => (3 * a ^ (2 : Nat) * linForm n c x) * gaussianWeight n x) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (integrable_linForm_gaussianWeight n c).const_mul (3 * a ^ (2 : Nat))
    have h3 :
        MeasureTheory.Integrable
          (fun x : Fin n → ℝ => (3 * a * linForm n c x ^ (2 : Nat)) * gaussianWeight n x) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (integrable_linForm_sq_gaussianWeight n c).const_mul (3 * a)
    have h4 :
        MeasureTheory.Integrable
          (fun x : Fin n → ℝ => linForm n c x ^ (3 : Nat) * gaussianWeight n x) := by
      simpa using integrable_linForm_cube_gaussianWeight n c
    have hsum :
        (fun x : Fin n → ℝ => (a + linForm n c x) ^ (3 : Nat) * gaussianWeight n x)
          =
        (fun x : Fin n → ℝ =>
          a ^ (3 : Nat) * gaussianWeight n x
            + ((3 * a ^ (2 : Nat) * linForm n c x) * gaussianWeight n x
              + ((3 * a * linForm n c x ^ (2 : Nat)) * gaussianWeight n x
                + linForm n c x ^ (3 : Nat) * gaussianWeight n x))) := by
          funext x
          ring
    rw [hsum]
    exact h1.add (h2.add (h3.add h4))
  have hnorm := hpoly.norm
  have hnorm_eq :
      (fun x : Fin n → ℝ => ‖(a + linForm n c x) ^ (3 : Nat) * gaussianWeight n x‖)
        =
      (fun x : Fin n → ℝ => |a + linForm n c x| ^ (3 : Nat) * gaussianWeight n x) := by
        funext x
        have hgw : 0 ≤ gaussianWeight n x := gaussianWeight_nonneg n x
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hgw, abs_pow]
  have hnorm' :
      MeasureTheory.Integrable
        (fun x : Fin n → ℝ => |a + linForm n c x| ^ (3 : Nat) * |gaussianWeight n x|) := by
    simpa [Real.norm_eq_abs, abs_mul, abs_pow] using hnorm
  have habs :
      (fun x : Fin n → ℝ => |a + linForm n c x| ^ (3 : Nat) * |gaussianWeight n x|)
        =
      (fun x : Fin n → ℝ => |a + linForm n c x| ^ (3 : Nat) * gaussianWeight n x) := by
        funext x
        rw [abs_of_nonneg (gaussianWeight_nonneg n x)]
  simpa [habs] using hnorm'

/- The boundary-specialized cubic integrability wrapper will be reintroduced
later in the file, after `linForm_hybridPoint_eq_add` is available. The
affine lemma above is the actual dependency needed for that wrapper. -/

private lemma stdGaussianAvg_linForm_four_eq_three_sum_sq_sq (n : ℕ) (c : Fin n → ℝ) :
    stdGaussianAvg n (fun x => linForm n c x ^ (4 : Nat))
      = 3 * (∑ i : Fin n, c i ^ (2 : Nat)) ^ (2 : Nat) := by
  induction n with
  | zero =>
      simp [stdGaussianAvg_zero, linForm]
  | succ n ih =>
      let a : ℝ := c 0
      let c₀ : Fin n → ℝ := Fin.tail c
      have hc : c = Fin.cons a c₀ := by
        ext i
        cases i using Fin.cases with
        | zero => simp [a]
        | succ i => rfl
      rw [hc]
      let F1 : (Fin (n + 1) → ℝ) → ℝ := fun y => a ^ (4 : Nat) * y 0 ^ (4 : Nat)
      let F2 : (Fin (n + 1) → ℝ) → ℝ := fun y => (4 * a ^ (3 : Nat) * y 0 ^ (3 : Nat)) * linForm n c₀ (Fin.tail y)
      let F3 : (Fin (n + 1) → ℝ) → ℝ := fun y => (6 * a ^ (2 : Nat) * y 0 ^ (2 : Nat)) * linForm n c₀ (Fin.tail y) ^ (2 : Nat)
      let F4 : (Fin (n + 1) → ℝ) → ℝ := fun y => (4 * a * y 0) * linForm n c₀ (Fin.tail y) ^ (3 : Nat)
      let F5 : (Fin (n + 1) → ℝ) → ℝ := fun y => linForm n c₀ (Fin.tail y) ^ (4 : Nat)
      have h1int :
          MeasureTheory.Integrable (fun y : Fin (n + 1) → ℝ => F1 y * gaussianWeight (n + 1) y) := by
        simpa [F1, mul_assoc] using
          (integrable_weighted_cons_mul n (fun z => a ^ (4 : Nat) * z ^ (4 : Nat)) (fun _ => (1 : ℝ))
            (by
              simpa [mul_assoc] using
                integrable_one_dim_four_gaussianWeight.const_mul (a ^ (4 : Nat)))
            (by simpa using integrable_stdGaussianDensity n))
      have h2int :
          MeasureTheory.Integrable (fun y : Fin (n + 1) → ℝ => F2 y * gaussianWeight (n + 1) y) := by
        simpa [F2, mul_assoc] using
          (integrable_weighted_cons_mul n
            (fun z => 4 * a ^ (3 : Nat) * z ^ (3 : Nat))
            (fun x => linForm n c₀ x)
            (by
              simpa [mul_assoc] using
                integrable_one_dim_cube_gaussianWeight.const_mul (4 * a ^ (3 : Nat)))
            (by simpa using integrable_linForm_gaussianWeight n c₀))
      have h3int :
          MeasureTheory.Integrable (fun y : Fin (n + 1) → ℝ => F3 y * gaussianWeight (n + 1) y) := by
        simpa [F3, mul_assoc] using
          (integrable_weighted_cons_mul n
            (fun z => 6 * a ^ (2 : Nat) * z ^ (2 : Nat))
            (fun x => linForm n c₀ x ^ (2 : Nat))
            (by
              simpa [mul_assoc] using
                integrable_one_dim_sq_gaussianWeight.const_mul (6 * a ^ (2 : Nat)))
            (by simpa using integrable_linForm_sq_gaussianWeight n c₀))
      have h4int :
          MeasureTheory.Integrable (fun y : Fin (n + 1) → ℝ => F4 y * gaussianWeight (n + 1) y) := by
        simpa [F4, mul_assoc] using
          (integrable_weighted_cons_mul n
            (fun z => 4 * a * z)
            (fun x => linForm n c₀ x ^ (3 : Nat))
            (by
              simpa [mul_assoc] using
                integrable_one_dim_linear_gaussianWeight.const_mul (4 * a))
            (by simpa using integrable_linForm_cube_gaussianWeight n c₀))
      have h5int :
          MeasureTheory.Integrable (fun y : Fin (n + 1) → ℝ => F5 y * gaussianWeight (n + 1) y) := by
        simpa [F5, mul_assoc] using
          (integrable_weighted_cons_mul n (fun _ => (1 : ℝ)) (fun x => linForm n c₀ x ^ (4 : Nat))
            (by simpa using integrable_one_dim_gaussianWeight)
            (by simpa using integrable_linForm_four_gaussianWeight n c₀))
      have h45int :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ => (F4 y + F5 y) * gaussianWeight (n + 1) y) := by
        simpa [F4, F5, mul_add, add_mul, add_assoc] using h4int.add h5int
      have h345int :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ => (F3 y + (F4 y + F5 y)) * gaussianWeight (n + 1) y) := by
        simpa [F3, mul_add, add_mul, add_assoc] using h3int.add h45int
      have h2345int :
          MeasureTheory.Integrable
            (fun y : Fin (n + 1) → ℝ => (F2 y + (F3 y + (F4 y + F5 y))) * gaussianWeight (n + 1) y) := by
        simpa [F2, mul_add, add_mul, add_assoc] using h2int.add h345int
      have hfun :
          (fun y : Fin (n + 1) → ℝ => linForm (n + 1) (Fin.cons a c₀) y ^ (4 : Nat))
            =
          (fun y : Fin (n + 1) → ℝ => F1 y + (F2 y + (F3 y + (F4 y + F5 y)))) := by
          funext y
          have hlin :
              linForm (n + 1) (Fin.cons a c₀) y = a * y 0 + linForm n c₀ (Fin.tail y) := by
            unfold linForm
            rw [Fin.sum_univ_succ]
            simp [Fin.cons, Fin.tail]
          rw [hlin]
          ring
      rw [hfun]
      rw [stdGaussianAvg_add (n + 1) F1 (fun y => F2 y + (F3 y + (F4 y + F5 y))) h1int h2345int]
      rw [stdGaussianAvg_add (n + 1) F2 (fun y => F3 y + (F4 y + F5 y)) h2int h345int]
      rw [stdGaussianAvg_add (n + 1) F3 (fun y => F4 y + F5 y) h3int h45int]
      rw [stdGaussianAvg_add (n + 1) F4 F5 h4int h5int]
      have h1 :
          stdGaussianAvg (n + 1) F1 = 3 * a ^ (4 : Nat) := by
        calc
          stdGaussianAvg (n + 1) F1
              = stdGaussianAvg1 (fun z => a ^ (4 : Nat) * z ^ (4 : Nat)) * stdGaussianAvg n (fun _ => (1 : ℝ)) := by
                  simpa [F1] using
                    (stdGaussianAvg_cons_mul n (fun z => a ^ (4 : Nat) * z ^ (4 : Nat))
                      (fun _ => (1 : ℝ)))
          _ = (a ^ (4 : Nat) * stdGaussianAvg1 (fun z => z ^ (4 : Nat))) * 1 := by
                rw [stdGaussianAvg_one, stdGaussianAvg1_mul_const]
          _ = 3 * a ^ (4 : Nat) := by
                simp [stdGaussianAvg1_four]
                ring
      have h2 :
          stdGaussianAvg (n + 1) F2 = 0 := by
        calc
          stdGaussianAvg (n + 1) F2
              = stdGaussianAvg1 (fun z => 4 * a ^ (3 : Nat) * z ^ (3 : Nat))
                  * stdGaussianAvg n (fun x => linForm n c₀ x) := by
                    simpa [F2] using
                      (stdGaussianAvg_cons_mul n
                        (fun z => 4 * a ^ (3 : Nat) * z ^ (3 : Nat))
                        (fun x => linForm n c₀ x))
          _ = 0 := by
                rw [stdGaussianAvg_linForm_zero]
                ring
      have h3 :
          stdGaussianAvg (n + 1) F3 = 6 * a ^ (2 : Nat) * (∑ i : Fin n, c₀ i ^ (2 : Nat)) := by
        calc
          stdGaussianAvg (n + 1) F3
              = stdGaussianAvg1 (fun z => 6 * a ^ (2 : Nat) * z ^ (2 : Nat))
                  * stdGaussianAvg n (fun x => linForm n c₀ x ^ (2 : Nat)) := by
                    simpa [F3] using
                      (stdGaussianAvg_cons_mul n
                        (fun z => 6 * a ^ (2 : Nat) * z ^ (2 : Nat))
                        (fun x => linForm n c₀ x ^ (2 : Nat)))
          _ = (6 * a ^ (2 : Nat) * stdGaussianAvg1 (fun z => z ^ (2 : Nat)))
                * stdGaussianAvg n (fun x => linForm n c₀ x ^ (2 : Nat)) := by
                  rw [stdGaussianAvg1_mul_const]
          _ = 6 * a ^ (2 : Nat) * (∑ i : Fin n, c₀ i ^ (2 : Nat)) := by
                simp [stdGaussianAvg1_sq, stdGaussianAvg_linForm_sq_eq_sum_sq]
      have h4 :
          stdGaussianAvg (n + 1) F4 = 0 := by
        calc
          stdGaussianAvg (n + 1) F4
              = stdGaussianAvg1 (fun z => 4 * a * z)
                  * stdGaussianAvg n (fun x => linForm n c₀ x ^ (3 : Nat)) := by
                    simpa [F4] using
                      (stdGaussianAvg_cons_mul n (fun z => 4 * a * z)
                        (fun x => linForm n c₀ x ^ (3 : Nat)))
          _ = 0 := by
                rw [stdGaussianAvg_linForm_cube_zero]
                ring
      have h5 :
          stdGaussianAvg (n + 1) F5 = 3 * (∑ i : Fin n, c₀ i ^ (2 : Nat)) ^ (2 : Nat) := by
        calc
          stdGaussianAvg (n + 1) F5
              = stdGaussianAvg1 (fun _ => (1 : ℝ))
                  * stdGaussianAvg n (fun x => linForm n c₀ x ^ (4 : Nat)) := by
                    simpa [F5] using
                      (stdGaussianAvg_cons_mul n (fun _ => (1 : ℝ))
                        (fun x => linForm n c₀ x ^ (4 : Nat)))
          _ = 3 * (∑ i : Fin n, c₀ i ^ (2 : Nat)) ^ (2 : Nat) := by
                simp [stdGaussianAvg1_mass, ih]
      rw [h1, h2, h3, h4, h5]
      rw [Fin.sum_univ_succ]
      simp [a, c₀]
      ring

private lemma avgSigns_linearX_zero (n : ℕ) (x : Fin n → ℝ) :
    avgSigns n (fun σ => linearX n x σ) = 0 := by
  induction n with
  | zero =>
      simp [avgSigns, linearX]
  | succ n ih =>
      let x₀ : Fin n → ℝ := Fin.init x
      let a : ℝ := x (Fin.last n)
      have hx : x = Fin.snoc x₀ a := by
        ext i <;> simp [x₀, a]
      rw [hx, avgSigns_split_last]
      have hpoint :
          (fun σ : Fin n → Fin 2 =>
            ((∑ b : Fin 2,
                linearX (n + 1) (Fin.snoc x₀ a) (Fin.snoc σ b)) / 2 : ℝ))
            = fun σ : Fin n → Fin 2 => linearX n x₀ σ := by
          funext σ
          have hs := congrArg (fun t : ℝ => t / 2)
            (sum_linear_over_last_sign (linearX n x₀ σ) a)
          simpa [linearX_snoc_last, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs
      rw [hpoint, ih]

private lemma avgSigns_linearX_cube_zero (n : ℕ) (x : Fin n → ℝ) :
    avgSigns n (fun σ => linearX n x σ ^ (3 : Nat)) = 0 := by
  induction n with
  | zero =>
      simp [avgSigns, linearX]
  | succ n ih =>
      let x₀ : Fin n → ℝ := Fin.init x
      let a : ℝ := x (Fin.last n)
      have hx : x = Fin.snoc x₀ a := by
        ext i <;> simp [x₀, a]
      rw [hx, avgSigns_split_last]
      have hpoint :
          (fun σ : Fin n → Fin 2 =>
            ((∑ b : Fin 2,
                linearX (n + 1) (Fin.snoc x₀ a) (Fin.snoc σ b) ^ (3 : Nat)) / 2 : ℝ))
            =
          (fun σ : Fin n → Fin 2 =>
            linearX n x₀ σ ^ (3 : Nat) + 3 * linearX n x₀ σ * a ^ (2 : Nat)) := by
        funext σ
        have hs :=
          congrArg (fun t : ℝ => t / 2) (sum_cube_over_last_sign (linearX n x₀ σ) a)
        simpa [linearX_snoc_last, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hs
      rw [hpoint, avgSigns_add, avgSigns_mul_const_right, avgSigns_mul_const_left,
        avgSigns_linearX_zero, ih]
      ring

private lemma linForm_hybridPoint_eq_add (n m : ℕ) (c : Fin (n + m) → ℝ)
    (σ : Fin n → Fin 2) (x : Fin m → ℝ) :
    linForm (n + m) c (hybridPoint n m σ x)
      = linearX n (signBlockCoeffs n m c) σ + linForm m (gaussBlockCoeffs n m c) x := by
  unfold linForm hybridPoint signBlockCoeffs gaussBlockCoeffs linearX
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right, mul_add, add_mul, add_assoc]

private lemma integrable_boundary_cube_gaussianWeight
    (n m : ℕ) (c : Fin (n + m) → ℝ) (σ : Fin n → Fin 2) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ =>
        |linForm (n + m) c (hybridPoint n m σ x)| ^ (3 : Nat) * gaussianWeight m x) := by
  let a : ℝ := linearX n (signBlockCoeffs n m c) σ
  let cg : Fin m → ℝ := gaussBlockCoeffs n m c
  have hrew :
      (fun x : Fin m → ℝ =>
        |linForm (n + m) c (hybridPoint n m σ x)| ^ (3 : Nat) * gaussianWeight m x)
        =
      (fun x : Fin m → ℝ => |a + linForm m cg x| ^ (3 : Nat) * gaussianWeight m x) := by
        funext x
        rw [linForm_hybridPoint_eq_add]
  rw [hrew]
  exact integrable_abs_affine_linForm_cube_gaussianWeight m a cg

private lemma integrable_boundary_cube_avgSigns_gaussianWeight
    (n m : ℕ) (c : Fin (n + m) → ℝ) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => |linForm (n + m) c (hybridPoint n m σ x)| ^ (3 : Nat))
          * gaussianWeight m x) := by
  classical
  have hsum :
      ∀ s : Finset (Fin n → Fin 2),
        MeasureTheory.Integrable
          (fun x : Fin m → ℝ =>
            s.sum (fun σ =>
              |linForm (n + m) c (hybridPoint n m σ x)| ^ (3 : Nat) * gaussianWeight m x)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using (MeasureTheory.integrable_const (c := (0 : ℝ)))
    | @insert σ s hσ ih =>
        have hσint :
            MeasureTheory.Integrable
              (fun x : Fin m → ℝ =>
                |linForm (n + m) c (hybridPoint n m σ x)| ^ (3 : Nat) * gaussianWeight m x) :=
          integrable_boundary_cube_gaussianWeight n m c σ
        simpa [Finset.sum_insert hσ] using hσint.add ih
  have huniv := hsum Finset.univ
  have hrew :
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => |linForm (n + m) c (hybridPoint n m σ x)| ^ (3 : Nat))
          * gaussianWeight m x)
        =
      (fun x : Fin m → ℝ =>
        (↑(2 ^ n : ℕ) : ℝ)⁻¹
          * (Finset.univ.sum fun σ : Fin n → Fin 2 =>
              |linForm (n + m) c (hybridPoint n m σ x)| ^ (3 : Nat) * gaussianWeight m x)) := by
        funext x
        unfold avgSigns
        calc
          ((↑(2 ^ n : ℕ) : ℝ)⁻¹
              * ∑ σ : Fin n → Fin 2,
                  |linForm (n + m) c (hybridPoint n m σ x)| ^ (3 : Nat))
              * gaussianWeight m x
              =
              (↑(2 ^ n : ℕ) : ℝ)⁻¹
                * ((∑ σ : Fin n → Fin 2,
                    |linForm (n + m) c (hybridPoint n m σ x)| ^ (3 : Nat))
                    * gaussianWeight m x) := by ring
          _ =
              (↑(2 ^ n : ℕ) : ℝ)⁻¹
                * ∑ σ : Fin n → Fin 2,
                    (|linForm (n + m) c (hybridPoint n m σ x)| ^ (3 : Nat))
                      * gaussianWeight m x := by
                rw [Finset.sum_mul]
          _ =
              (↑(2 ^ n : ℕ) : ℝ)⁻¹
                * (Finset.univ.sum fun σ : Fin n → Fin 2 =>
                    |linForm (n + m) c (hybridPoint n m σ x)| ^ (3 : Nat)
                      * gaussianWeight m x) := by
                rfl
  rw [hrew]
  exact huniv.const_mul ((↑(2 ^ n : ℕ) : ℝ)⁻¹)

private lemma abs_add_mul_pow_three_le_four (a z b : ℝ) :
    |a + z * b| ^ (3 : Nat)
      ≤ 4 * (|a| ^ (3 : Nat) + |z| ^ (3 : Nat) * |b| ^ (3 : Nat)) := by
  let u : ℝ := |a|
  let v : ℝ := |z| * |b|
  have hmul : |z * b| = |z| * |b| := by rw [abs_mul]
  have hadd : |a + z * b| ≤ |a| + |z| * |b| := by
    calc
      |a + z * b| ≤ |a| + |z * b| := by simpa using (norm_add_le a (z * b))
      _ = |a| + |z| * |b| := by rw [hmul]
  have hpow :
      |a + z * b| ^ (3 : Nat) ≤ (|a| + |z| * |b|) ^ (3 : Nat) := by
    exact pow_le_pow_left₀ (abs_nonneg _) hadd 3
  have hu : 0 ≤ u := abs_nonneg a
  have hv : 0 ≤ v := mul_nonneg (abs_nonneg z) (abs_nonneg b)
  have hpoly :
      (u + v) ^ (3 : Nat) ≤ 4 * (u ^ (3 : Nat) + v ^ (3 : Nat)) := by
    have hnonneg : 0 ≤ 3 * (u - v) ^ (2 : Nat) * (u + v) := by positivity
    nlinarith
  have hmulpow : v ^ (3 : Nat) = |z| ^ (3 : Nat) * |b| ^ (3 : Nat) := by
    ring
  calc
    |a + z * b| ^ (3 : Nat) ≤ (|a| + |z| * |b|) ^ (3 : Nat) := hpow
    _ = (u + v) ^ (3 : Nat) := by simp [u, v]
    _ ≤ 4 * (u ^ (3 : Nat) + v ^ (3 : Nat)) := hpoly
    _ = 4 * (|a| ^ (3 : Nat) + |z| ^ (3 : Nat) * |b| ^ (3 : Nat)) := by
          simpa [u, v] using congrArg (fun t : ℝ => 4 * (u ^ (3 : Nat) + t)) hmulpow

private lemma integrable_hybrid_q2_cube_gaussianWeight
    (n m : ℕ)
    (lam : Fin (n + m) → Fin (n + m) → ℝ)
    (hsymm : ∀ i j, lam i j = lam j i)
    (hdiag : ∀ i, lam i i = 0)
    (σ : Fin n → Fin 2) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ =>
        |Q2Gauss (n + m) lam (hybridPoint n m σ x)| ^ (3 : Nat) * gaussianWeight m x) := by
  induction m generalizing n with
  | zero =>
      have hfun :
          (fun x : Fin 0 → ℝ =>
            |Q2Gauss (n + 0) lam (hybridPoint n 0 σ x)| ^ (3 : Nat) * gaussianWeight 0 x)
            =
          (fun _ : Fin 0 → ℝ =>
            |Q2Gauss n lam (fun i : Fin n => (((signOf (σ i) : ℤ) : ℝ)))| ^ (3 : Nat)) := by
        funext x
        have hhyb : hybridPoint n 0 σ x = (fun i : Fin n => (((signOf (σ i) : ℤ) : ℝ))) := by
          funext i
          simpa [hybridPoint] using
            (Fin.append_left (fun j : Fin n => (((signOf (σ j) : ℤ) : ℝ))) x i)
        simp [gaussianWeight_zero, hhyb]
      rw [hfun]
      simpa using
        (MeasureTheory.integrable_const
          (c := |Q2Gauss n lam (fun i : Fin n => (((signOf (σ i) : ℤ) : ℝ)))| ^ (3 : Nat)))
  | succ m ih =>
      let k : Fin (n + m + 1) := boundaryIndex n m
      let U : (Fin m → ℝ) → ℝ :=
        fun x =>
          Q2Gauss (n + m) (minorKernelAt k lam) (hybridPoint n m σ x)
      let V : (Fin m → ℝ) → ℝ :=
        fun x =>
          linForm (n + m) (rowKernelAt k lam) (hybridPoint n m σ x)
      have hU_int :
          MeasureTheory.Integrable
            (fun x : Fin m → ℝ => |U x| ^ (3 : Nat) * gaussianWeight m x) := by
        simpa [U] using
          ih n (minorKernelAt k lam) (minorKernelAt_symm k lam hsymm) (minorKernelAt_diag k lam hdiag) σ
      have hV_int :
          MeasureTheory.Integrable
            (fun x : Fin m → ℝ => |V x| ^ (3 : Nat) * gaussianWeight m x) := by
        simpa [V] using integrable_boundary_cube_gaussianWeight n m (rowKernelAt k lam) σ
      have htermU :
          MeasureTheory.Integrable
            (fun y : Fin (m + 1) → ℝ =>
              (4 * |U (Fin.tail y)| ^ (3 : Nat)) * gaussianWeight (m + 1) y) := by
        simpa [mul_assoc, mul_left_comm, mul_comm, U] using
          (integrable_weighted_cons_mul m (fun _ : ℝ => (4 : ℝ)) (fun x : Fin m → ℝ => |U x| ^ (3 : Nat))
            (by simpa using integrable_one_dim_gaussianWeight.const_mul (4 : ℝ))
            hU_int)
      have htermV :
          MeasureTheory.Integrable
            (fun y : Fin (m + 1) → ℝ =>
              (4 * |y 0| ^ (3 : Nat) * |V (Fin.tail y)| ^ (3 : Nat)) * gaussianWeight (m + 1) y) := by
        simpa [mul_assoc, mul_left_comm, mul_comm, V] using
          (integrable_weighted_cons_mul m
            (fun z : ℝ => 4 * |z| ^ (3 : Nat))
            (fun x : Fin m → ℝ => |V x| ^ (3 : Nat))
            (by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                integrable_one_dim_abs_cube_gaussianWeight.const_mul (4 : ℝ))
            hV_int)
      have hdom :
          MeasureTheory.Integrable
            (fun y : Fin (m + 1) → ℝ =>
              (4 * |U (Fin.tail y)| ^ (3 : Nat)) * gaussianWeight (m + 1) y
                + (4 * |y 0| ^ (3 : Nat) * |V (Fin.tail y)| ^ (3 : Nat)) * gaussianWeight (m + 1) y) := by
        exact htermU.add htermV
      refine hdom.mono' ?_ ?_
      · have hcontQ :
            Continuous
              (fun y : Fin (m + 1) → ℝ => Q2Gauss (n + (m + 1)) lam (hybridPoint n (m + 1) σ y)) := by
          exact (continuous_Q2Gauss (n + (m + 1)) lam).comp (continuous_hybridPoint n (m + 1) σ)
        simpa using ((hcontQ.abs.pow 3).mul (continuous_gaussianWeight (m + 1))).aestronglyMeasurable
      · exact Filter.Eventually.of_forall (fun y => by
          have hy : Fin.cons (y 0) (Fin.tail y) = y := by
            ext i
            cases i using Fin.cases with
            | zero => simp
            | succ i => simp [Fin.tail]
          have hQ :
              Q2Gauss (n + (m + 1)) lam (hybridPoint n (m + 1) σ y)
                =
              U (Fin.tail y) + y 0 * V (Fin.tail y) := by
            simpa [hy, U, V] using
              (Q2Gauss_boundary_gaussian n m lam hsymm hdiag σ (Fin.tail y) (y 0))
          have hgw_nonneg : 0 ≤ gaussianWeight (m + 1) y := gaussianWeight_nonneg (m + 1) y
          have hmain :
              |Q2Gauss (n + (m + 1)) lam (hybridPoint n (m + 1) σ y)| ^ (3 : Nat)
                ≤ 4 * (|U (Fin.tail y)| ^ (3 : Nat)
                    + |y 0| ^ (3 : Nat) * |V (Fin.tail y)| ^ (3 : Nat)) := by
            rw [hQ]
            exact abs_add_mul_pow_three_le_four (U (Fin.tail y)) (y 0) (V (Fin.tail y))
          calc
            ‖|Q2Gauss (n + (m + 1)) lam (hybridPoint n (m + 1) σ y)| ^ (3 : Nat)
                * gaussianWeight (m + 1) y‖
                =
            |Q2Gauss (n + (m + 1)) lam (hybridPoint n (m + 1) σ y)| ^ (3 : Nat)
                * gaussianWeight (m + 1) y := by
                  rw [Real.norm_eq_abs, abs_of_nonneg]
                  positivity
            _ ≤
            (4 * (|U (Fin.tail y)| ^ (3 : Nat)
                + |y 0| ^ (3 : Nat) * |V (Fin.tail y)| ^ (3 : Nat)))
              * gaussianWeight (m + 1) y := by
                  exact mul_le_mul_of_nonneg_right hmain hgw_nonneg
            _ =
            (4 * |U (Fin.tail y)| ^ (3 : Nat)) * gaussianWeight (m + 1) y
              + (4 * |y 0| ^ (3 : Nat) * |V (Fin.tail y)| ^ (3 : Nat))
                  * gaussianWeight (m + 1) y := by
                    ring
          )

private lemma integrable_hybrid_q2_cube_avgSigns_gaussianWeight
    (n m : ℕ)
    (lam : Fin (n + m) → Fin (n + m) → ℝ)
    (hsymm : ∀ i j, lam i j = lam j i)
    (hdiag : ∀ i, lam i i = 0) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => |Q2Gauss (n + m) lam (hybridPoint n m σ x)| ^ (3 : Nat))
          * gaussianWeight m x) := by
  classical
  have hsum :
      ∀ s : Finset (Fin n → Fin 2),
        MeasureTheory.Integrable
          (fun x : Fin m → ℝ =>
            s.sum (fun σ =>
              |Q2Gauss (n + m) lam (hybridPoint n m σ x)| ^ (3 : Nat) * gaussianWeight m x)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using (MeasureTheory.integrable_const (c := (0 : ℝ)))
    | @insert σ s hσ ih =>
        have hσint :
            MeasureTheory.Integrable
              (fun x : Fin m → ℝ =>
                |Q2Gauss (n + m) lam (hybridPoint n m σ x)| ^ (3 : Nat) * gaussianWeight m x) :=
          integrable_hybrid_q2_cube_gaussianWeight n m lam hsymm hdiag σ
        simpa [Finset.sum_insert hσ] using hσint.add ih
  have huniv := hsum Finset.univ
  have hrew :
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => |Q2Gauss (n + m) lam (hybridPoint n m σ x)| ^ (3 : Nat))
          * gaussianWeight m x)
        =
      (fun x : Fin m → ℝ =>
        (↑(2 ^ n : ℕ) : ℝ)⁻¹
          * (Finset.univ.sum fun σ : Fin n → Fin 2 =>
              |Q2Gauss (n + m) lam (hybridPoint n m σ x)| ^ (3 : Nat) * gaussianWeight m x)) := by
        funext x
        unfold avgSigns
        calc
          ((↑(2 ^ n : ℕ) : ℝ)⁻¹
              * ∑ σ : Fin n → Fin 2,
                  |Q2Gauss (n + m) lam (hybridPoint n m σ x)| ^ (3 : Nat))
              * gaussianWeight m x
              =
              (↑(2 ^ n : ℕ) : ℝ)⁻¹
                * ((∑ σ : Fin n → Fin 2,
                    |Q2Gauss (n + m) lam (hybridPoint n m σ x)| ^ (3 : Nat))
                    * gaussianWeight m x) := by ring
          _ =
              (↑(2 ^ n : ℕ) : ℝ)⁻¹
                * ∑ σ : Fin n → Fin 2,
                    (|Q2Gauss (n + m) lam (hybridPoint n m σ x)| ^ (3 : Nat))
                      * gaussianWeight m x := by
                rw [Finset.sum_mul]
          _ =
              (↑(2 ^ n : ℕ) : ℝ)⁻¹
                * (Finset.univ.sum fun σ : Fin n → Fin 2 =>
                    |Q2Gauss (n + m) lam (hybridPoint n m σ x)| ^ (3 : Nat)
                      * gaussianWeight m x) := by
                rfl
  rw [hrew]
  exact huniv.const_mul ((↑(2 ^ n : ℕ) : ℝ)⁻¹)

private lemma integrable_boundary_sign_q2_cube_gaussianWeight
    (n m : ℕ) (lam : Fin (n + m + 1) → Fin (n + m + 1) → ℝ)
    (hsymm : ∀ i j, lam i j = lam j i) (hdiag : ∀ i, lam i i = 0)
    (σ : Fin n → Fin 2) (b : Fin 2) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ =>
        |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)
          * gaussianWeight m x) := by
  let k : Fin (n + m + 1) := boundaryIndex n m
  let U : (Fin m → ℝ) → ℝ :=
    fun x => Q2Gauss (n + m) (minorKernelAt k lam) (hybridPoint n m σ x)
  let V : (Fin m → ℝ) → ℝ :=
    fun x => linForm (n + m) (rowKernelAt k lam) (hybridPoint n m σ x)
  have hU_int :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ => |U x| ^ (3 : Nat) * gaussianWeight m x) := by
    simpa [U] using
      integrable_hybrid_q2_cube_gaussianWeight n m (minorKernelAt k lam)
        (minorKernelAt_symm k lam hsymm) (minorKernelAt_diag k lam hdiag) σ
  have hV_int :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ => |V x| ^ (3 : Nat) * gaussianWeight m x) := by
    simpa [V] using integrable_boundary_cube_gaussianWeight n m (rowKernelAt k lam) σ
  have htermU :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ => (4 * |U x| ^ (3 : Nat)) * gaussianWeight m x) := by
    simpa [mul_assoc, mul_left_comm, mul_comm, U] using hU_int.const_mul (4 : ℝ)
  have htermV :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ => (4 * |V x| ^ (3 : Nat)) * gaussianWeight m x) := by
    simpa [mul_assoc, mul_left_comm, mul_comm, V] using hV_int.const_mul (4 : ℝ)
  have hdom :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ =>
          (4 * |U x| ^ (3 : Nat)) * gaussianWeight m x
            + (4 * |V x| ^ (3 : Nat)) * gaussianWeight m x) := by
    exact htermU.add htermV
  refine hdom.mono' ?_ ?_
  · have hcontQ :
        Continuous
          (fun x : Fin m → ℝ => Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)) := by
      have hcontBS :
          Continuous (fun x : Fin m → ℝ => boundarySignHybridPoint n m σ b x) := by
        have hcast :
            Continuous
              (fun y : Fin ((n + 1) + m) → ℝ =>
                fun j : Fin (n + m + 1) => y (Fin.cast (by omega) j)) := by
          rw [continuous_pi_iff]
          intro j
          exact continuous_apply (Fin.cast (by omega) j)
        simpa [boundarySignHybridPoint] using
          hcast.comp (continuous_hybridPoint (n + 1) m (Fin.snoc σ b))
      exact (continuous_Q2Gauss (n + m + 1) lam).comp hcontBS
    simpa using ((hcontQ.abs.pow 3).mul (continuous_gaussianWeight m)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      have hQ :
          Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)
            =
          U x + (((signOf b : ℤ) : ℝ)) * V x := by
        simpa [U, V] using (Q2Gauss_boundary_sign n m lam hsymm hdiag σ x b)
      have hsign :
          |(((signOf b : ℤ) : ℝ))| ^ (3 : Nat) = 1 := by
        fin_cases b <;> norm_num [signOf]
      have hmain :
          |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)
            ≤ 4 * (|U x| ^ (3 : Nat) + |V x| ^ (3 : Nat)) := by
        rw [hQ]
        calc
          |U x + (((signOf b : ℤ) : ℝ)) * V x| ^ (3 : Nat)
              ≤ 4 * (|U x| ^ (3 : Nat)
                  + |(((signOf b : ℤ) : ℝ))| ^ (3 : Nat) * |V x| ^ (3 : Nat)) := by
                    exact abs_add_mul_pow_three_le_four (U x) (((signOf b : ℤ) : ℝ)) (V x)
          _ = 4 * (|U x| ^ (3 : Nat) + |V x| ^ (3 : Nat)) := by
                rw [hsign]
                ring
      have hgw_nonneg : 0 ≤ gaussianWeight m x := gaussianWeight_nonneg m x
      calc
        ‖|Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)
            * gaussianWeight m x‖
            =
        |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)
            * gaussianWeight m x := by
              rw [Real.norm_eq_abs, abs_of_nonneg]
              positivity
        _ ≤
        (4 * (|U x| ^ (3 : Nat) + |V x| ^ (3 : Nat))) * gaussianWeight m x := by
              exact mul_le_mul_of_nonneg_right hmain hgw_nonneg
        _ =
        (4 * |U x| ^ (3 : Nat)) * gaussianWeight m x
          + (4 * |V x| ^ (3 : Nat)) * gaussianWeight m x := by
              ring)

private lemma integrable_boundary_sign_q2_cube_avgSigns_gaussianWeight
    (n m : ℕ) (lam : Fin (n + m + 1) → Fin (n + m + 1) → ℝ)
    (hsymm : ∀ i j, lam i j = lam j i) (hdiag : ∀ i, lam i i = 0) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ =>
        avgSigns n
          (fun σ =>
            (((∑ b : Fin 2,
                |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)) / 2 : ℝ)))
          * gaussianWeight m x) := by
  classical
  have hsum :
      ∀ s : Finset (Fin n → Fin 2),
        MeasureTheory.Integrable
          (fun x : Fin m → ℝ =>
            s.sum (fun σ =>
              (((∑ b : Fin 2,
                  |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)) / 2 : ℝ))
                * gaussianWeight m x)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simpa using (MeasureTheory.integrable_const (c := (0 : ℝ)))
    | @insert σ s hσ ih =>
        have hσint :
            MeasureTheory.Integrable
              (fun x : Fin m → ℝ =>
                (((∑ b : Fin 2,
                    |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)) / 2 : ℝ))
                  * gaussianWeight m x) := by
          have h0 := integrable_boundary_sign_q2_cube_gaussianWeight n m lam hsymm hdiag σ (0 : Fin 2)
          have h1 := integrable_boundary_sign_q2_cube_gaussianWeight n m lam hsymm hdiag σ (1 : Fin 2)
          have hrewσ :
              (fun x : Fin m → ℝ =>
                (((∑ b : Fin 2,
                    |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)) / 2 : ℝ))
                  * gaussianWeight m x)
                =
              (fun x : Fin m → ℝ =>
                (((|Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 0 x)| ^ (3 : Nat)
                    + |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 1 x)| ^ (3 : Nat)) / 2 : ℝ))
                  * gaussianWeight m x) := by
            funext x
            rw [Fin.sum_univ_two]
          rw [hrewσ]
          have hsum01 :
              MeasureTheory.Integrable
                (fun x : Fin m → ℝ =>
                  (((|Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 0 x)| ^ (3 : Nat)
                    + |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 1 x)| ^ (3 : Nat)) / 2 : ℝ))
                    * gaussianWeight m x) := by
            have hadd := h0.add h1
            simpa [div_eq_mul_inv, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using
              hadd.const_mul ((2 : ℝ)⁻¹)
          exact hsum01
        simpa [Finset.sum_insert hσ] using hσint.add ih
  have huniv := hsum Finset.univ
  have hrew :
      (fun x : Fin m → ℝ =>
        avgSigns n
          (fun σ =>
            (((∑ b : Fin 2,
                |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)) / 2 : ℝ)))
          * gaussianWeight m x)
        =
      (fun x : Fin m → ℝ =>
        (↑(2 ^ n : ℕ) : ℝ)⁻¹
          * (Finset.univ.sum fun σ : Fin n → Fin 2 =>
              ((((∑ b : Fin 2,
                  |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)) / 2 : ℝ))
                * gaussianWeight m x))) := by
    funext x
    unfold avgSigns
    calc
      ((↑(2 ^ n : ℕ) : ℝ)⁻¹
          * ∑ σ : Fin n → Fin 2,
              (((∑ b : Fin 2,
                  |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)) / 2 : ℝ)))
          * gaussianWeight m x
          =
        (↑(2 ^ n : ℕ) : ℝ)⁻¹
          * ((∑ σ : Fin n → Fin 2,
              (((∑ b : Fin 2,
                  |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)) / 2 : ℝ)))
              * gaussianWeight m x) := by ring
      _ =
        (↑(2 ^ n : ℕ) : ℝ)⁻¹
          * ∑ σ : Fin n → Fin 2,
              ((((∑ b : Fin 2,
                  |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)) / 2 : ℝ))
                * gaussianWeight m x) := by
              rw [Finset.sum_mul]
      _ =
        (↑(2 ^ n : ℕ) : ℝ)⁻¹
          * (Finset.univ.sum fun σ : Fin n → Fin 2 =>
              ((((∑ b : Fin 2,
                  |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)) / 2 : ℝ))
                * gaussianWeight m x)) := by
              rfl
  rw [hrew]
  exact huniv.const_mul ((↑(2 ^ n : ℕ) : ℝ)⁻¹)

private lemma stdGaussianAvg_mono_of_nonneg
    (m : ℕ) {f g : (Fin m → ℝ) → ℝ}
    (hf_nonneg : ∀ x : Fin m → ℝ, 0 ≤ f x)
    (hg_int : MeasureTheory.Integrable (fun x : Fin m → ℝ => g x * gaussianWeight m x))
    (hfg : ∀ x : Fin m → ℝ, f x ≤ g x) :
    stdGaussianAvg m f ≤ stdGaussianAvg m g := by
  unfold stdGaussianAvg
  have hfac_nonneg : 0 ≤ ((2 * Real.pi) ^ ((m : ℝ) / 2))⁻¹ := by
    positivity [Real.pi_pos]
  have hint :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun x => mul_nonneg (hf_nonneg x) (gaussianWeight_nonneg m x)))
      hg_int <|
      Filter.Eventually.of_forall (fun x => by
        have hgw_nonneg : 0 ≤ gaussianWeight m x := gaussianWeight_nonneg m x
        exact mul_le_mul_of_nonneg_right (hfg x) hgw_nonneg)
  exact mul_le_mul_of_nonneg_left hint hfac_nonneg

private lemma integral_sqrt_mul_le_sqrt_integral_mul
    (m : ℕ) {F G : (Fin m → ℝ) → ℝ}
    (hF_nonneg : ∀ x : Fin m → ℝ, 0 ≤ F x)
    (hG_nonneg : ∀ x : Fin m → ℝ, 0 ≤ G x)
    (hF_int : MeasureTheory.Integrable F) (hG_int : MeasureTheory.Integrable G) :
    (∫ x : Fin m → ℝ, Real.sqrt (F x) * Real.sqrt (G x))
      ≤ Real.sqrt (∫ x : Fin m → ℝ, F x) * Real.sqrt (∫ x : Fin m → ℝ, G x) := by
  let f : (Fin m → ℝ) → ℝ := fun x => Real.sqrt (F x)
  let g : (Fin m → ℝ) → ℝ := fun x => Real.sqrt (G x)
  have hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume := by
    simpa [f] using
      ((hF_int.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable :
        MeasureTheory.AEStronglyMeasurable (fun x : Fin m → ℝ => Real.sqrt (F x))
          MeasureTheory.volume)
  have hg_meas : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume := by
    simpa [g] using
      ((hG_int.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable :
        MeasureTheory.AEStronglyMeasurable (fun x : Fin m → ℝ => Real.sqrt (G x))
          MeasureTheory.volume)
  have hf_sq_int : MeasureTheory.Integrable (fun x : Fin m → ℝ => f x ^ (2 : Nat)) := by
    simpa [f, Real.sq_sqrt, hF_nonneg] using hF_int
  have hg_sq_int : MeasureTheory.Integrable (fun x : Fin m → ℝ => g x ^ (2 : Nat)) := by
    simpa [g, Real.sq_sqrt, hG_nonneg] using hG_int
  have hf_mem : MeasureTheory.MemLp f (ENNReal.ofReal 2) MeasureTheory.volume := by
    simpa using
      ((MeasureTheory.memLp_two_iff_integrable_sq hf_meas).2 hf_sq_int :
        MeasureTheory.MemLp f 2 MeasureTheory.volume)
  have hg_mem : MeasureTheory.MemLp g (ENNReal.ofReal 2) MeasureTheory.volume := by
    simpa using
      ((MeasureTheory.memLp_two_iff_integrable_sq hg_meas).2 hg_sq_int :
        MeasureTheory.MemLp g 2 MeasureTheory.volume)
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hcs :=
    (MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := (MeasureTheory.volume : Measure (Fin m → ℝ)))
      (f := f) (g := g) hpq
      (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _)
      (Filter.Eventually.of_forall fun x => Real.sqrt_nonneg _)
      hf_mem hg_mem)
  have hf_pow :
      (∫ x : Fin m → ℝ, f x ^ (2 : ℝ)) = ∫ x : Fin m → ℝ, F x := by
    refine MeasureTheory.integral_congr_ae <| Filter.Eventually.of_forall ?_
    intro x
    dsimp [f]
    simpa [Real.rpow_natCast] using (Real.sq_sqrt (hF_nonneg x))
  have hg_pow :
      (∫ x : Fin m → ℝ, g x ^ (2 : ℝ)) = ∫ x : Fin m → ℝ, G x := by
    refine MeasureTheory.integral_congr_ae <| Filter.Eventually.of_forall ?_
    intro x
    dsimp [g]
    simpa [Real.rpow_natCast] using (Real.sq_sqrt (hG_nonneg x))
  calc
    (∫ x : Fin m → ℝ, Real.sqrt (F x) * Real.sqrt (G x))
      = ∫ x : Fin m → ℝ, f x * g x := by rfl
    _ ≤ (∫ x : Fin m → ℝ, f x ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)
          * (∫ x : Fin m → ℝ, g x ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := hcs
    _ = Real.sqrt (∫ x : Fin m → ℝ, F x) * Real.sqrt (∫ x : Fin m → ℝ, G x) := by
      rw [hf_pow, hg_pow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

private lemma integrable_sqrt_mul
    (m : ℕ) {F G : (Fin m → ℝ) → ℝ}
    (hF_nonneg : ∀ x : Fin m → ℝ, 0 ≤ F x)
    (hG_nonneg : ∀ x : Fin m → ℝ, 0 ≤ G x)
    (hF_int : MeasureTheory.Integrable F) (hG_int : MeasureTheory.Integrable G) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ => Real.sqrt (F x) * Real.sqrt (G x)) := by
  let f : (Fin m → ℝ) → ℝ := fun x => Real.sqrt (F x)
  let g : (Fin m → ℝ) → ℝ := fun x => Real.sqrt (G x)
  have hf_meas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume := by
    simpa [f] using
      ((hF_int.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable :
        MeasureTheory.AEStronglyMeasurable (fun x : Fin m → ℝ => Real.sqrt (F x))
          MeasureTheory.volume)
  have hg_meas : MeasureTheory.AEStronglyMeasurable g MeasureTheory.volume := by
    simpa [g] using
      ((hG_int.aestronglyMeasurable.aemeasurable.sqrt).aestronglyMeasurable :
        MeasureTheory.AEStronglyMeasurable (fun x : Fin m → ℝ => Real.sqrt (G x))
          MeasureTheory.volume)
  have hf_sq_int : MeasureTheory.Integrable (fun x : Fin m → ℝ => f x ^ (2 : Nat)) := by
    simpa [f, Real.sq_sqrt, hF_nonneg] using hF_int
  have hg_sq_int : MeasureTheory.Integrable (fun x : Fin m → ℝ => g x ^ (2 : Nat)) := by
    simpa [g, Real.sq_sqrt, hG_nonneg] using hG_int
  have hf_mem : MeasureTheory.MemLp f 2 MeasureTheory.volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq hf_meas).2 hf_sq_int
  have hg_mem : MeasureTheory.MemLp g 2 MeasureTheory.volume :=
    (MeasureTheory.memLp_two_iff_integrable_sq hg_meas).2 hg_sq_int
  letI : ENNReal.HolderConjugate 2 2 := ENNReal.HolderConjugate.instTwoTwo
  simpa [f, g] using
    (hf_mem.integrable_mul hg_mem :
      MeasureTheory.Integrable (f * g) MeasureTheory.volume)

private lemma avgSigns_abs_cube_le_sqrt_second_fourth
    (n : ℕ) (u : (Fin n → Fin 2) → ℝ) :
    avgSigns n (fun σ => |u σ| ^ (3 : Nat))
      ≤
    Real.sqrt
      (avgSigns n (fun σ => u σ ^ (2 : Nat))
        * avgSigns n (fun σ => u σ ^ (4 : Nat))) := by
  have hsq :=
    avgSigns_mul_sq_le_avgSigns_sq_mul_avgSigns_sq n
      (fun σ => |u σ|) (fun σ => u σ ^ (2 : Nat))
  have hL :
      (fun σ : Fin n → Fin 2 => |u σ| * u σ ^ (2 : Nat))
        =
      (fun σ : Fin n → Fin 2 => |u σ| ^ (3 : Nat)) := by
    funext σ
    rw [← sq_abs (u σ)]
    ring
  have hR1 :
      (fun σ : Fin n → Fin 2 => |u σ| ^ (2 : Nat))
        =
      (fun σ : Fin n → Fin 2 => u σ ^ (2 : Nat)) := by
    funext σ
    rw [sq_abs]
  have hR2 :
      (fun σ : Fin n → Fin 2 => (u σ ^ (2 : Nat)) ^ (2 : Nat))
        =
      (fun σ : Fin n → Fin 2 => u σ ^ (4 : Nat)) := by
    funext σ
    ring_nf
  have hsq' :
      (avgSigns n (fun σ => |u σ| ^ (3 : Nat))) ^ (2 : Nat)
        ≤
      avgSigns n (fun σ => u σ ^ (2 : Nat))
        * avgSigns n (fun σ => u σ ^ (4 : Nat)) := by
    simpa [hL, hR1, hR2] using hsq
  have hnonneg :
      0 ≤ avgSigns n (fun σ => |u σ| ^ (3 : Nat)) := by
    unfold avgSigns
    positivity
  have hrhs_nonneg :
      0 ≤ avgSigns n (fun σ => u σ ^ (2 : Nat))
            * avgSigns n (fun σ => u σ ^ (4 : Nat)) := by
    have h2_nonneg : 0 ≤ avgSigns n (fun σ => u σ ^ (2 : Nat)) := by
      unfold avgSigns
      positivity
    have h4_nonneg : 0 ≤ avgSigns n (fun σ => u σ ^ (4 : Nat)) := by
      unfold avgSigns
      positivity
    exact mul_nonneg h2_nonneg h4_nonneg
  have hsqr :
      (avgSigns n (fun σ => |u σ| ^ (3 : Nat))) ^ (2 : Nat)
        ≤
      (Real.sqrt
        (avgSigns n (fun σ => u σ ^ (2 : Nat))
          * avgSigns n (fun σ => u σ ^ (4 : Nat)))) ^ (2 : Nat) := by
    simpa [Real.sq_sqrt hrhs_nonneg] using hsq'
  have hsqrt_nonneg :
      0 ≤
        Real.sqrt
          (avgSigns n (fun σ => u σ ^ (2 : Nat))
            * avgSigns n (fun σ => u σ ^ (4 : Nat))) := Real.sqrt_nonneg _
  nlinarith [hsqr, hnonneg, hsqrt_nonneg]

private lemma integrable_hybrid_second_avgSigns_gaussianWeight
    (n m : ℕ) (c : Fin (n + m) → ℝ) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => linForm (n + m) c (hybridPoint n m σ x) ^ (2 : Nat))
          * gaussianWeight m x) := by
  let cs : Fin n → ℝ := signBlockCoeffs n m c
  let cg : Fin m → ℝ := gaussBlockCoeffs n m c
  have hpoint :
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => linForm (n + m) c (hybridPoint n m σ x) ^ (2 : Nat)))
        =
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat))
          + linForm m cg x ^ (2 : Nat)) := by
        funext x
        have hfun :
            (fun σ : Fin n → Fin 2 => linForm (n + m) c (hybridPoint n m σ x) ^ (2 : Nat))
              =
            (fun σ : Fin n → Fin 2 =>
              linearX n cs σ ^ (2 : Nat)
                + (2 * linForm m cg x) * linearX n cs σ
                + linForm m cg x ^ (2 : Nat)) := by
                  funext σ
                  rw [linForm_hybridPoint_eq_add]
                  ring
        rw [hfun, avgSigns_add, avgSigns_add, avgSigns_mul_const_left,
          avgSigns_linearX_zero, avgSigns_const]
        ring
  have hconst_int :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ =>
          avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat)) * gaussianWeight m x) := by
    simpa [mul_assoc] using
      integrable_stdGaussianDensity m |>.const_mul
        (avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat)))
  have hsq_int :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ => linForm m cg x ^ (2 : Nat) * gaussianWeight m x) := by
    simpa using integrable_linForm_sq_gaussianWeight m cg
  have hsum_int :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ =>
          (avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat)) + linForm m cg x ^ (2 : Nat))
            * gaussianWeight m x) := by
    simpa [mul_add, add_mul, add_assoc] using hconst_int.add hsq_int
  have hpoint_mul :
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => linForm (n + m) c (hybridPoint n m σ x) ^ (2 : Nat))
          * gaussianWeight m x)
        =
      (fun x : Fin m → ℝ =>
        (avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat)) + linForm m cg x ^ (2 : Nat))
          * gaussianWeight m x) := by
    funext x
    have hx := congrArg (fun f : (Fin m → ℝ) → ℝ => f x) hpoint
    simpa using congrArg (fun t : ℝ => t * gaussianWeight m x) hx
  simpa [hpoint_mul] using hsum_int

private lemma integrable_hybrid_fourth_avgSigns_gaussianWeight
    (n m : ℕ) (c : Fin (n + m) → ℝ) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => linForm (n + m) c (hybridPoint n m σ x) ^ (4 : Nat))
          * gaussianWeight m x) := by
  let cs : Fin n → ℝ := signBlockCoeffs n m c
  let cg : Fin m → ℝ := gaussBlockCoeffs n m c
  let A : ℝ := avgSigns n (fun σ => linearX n cs σ ^ (4 : Nat))
  let B : ℝ := 6 * avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat))
  have hpoint :
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => linForm (n + m) c (hybridPoint n m σ x) ^ (4 : Nat)))
        =
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => linearX n cs σ ^ (4 : Nat))
          + (6 * linForm m cg x ^ (2 : Nat)) * avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat))
          + linForm m cg x ^ (4 : Nat)) := by
        funext x
        have hfun :
            (fun σ : Fin n → Fin 2 => linForm (n + m) c (hybridPoint n m σ x) ^ (4 : Nat))
              =
            (fun σ : Fin n → Fin 2 =>
              linearX n cs σ ^ (4 : Nat)
                + 4 * linForm m cg x * linearX n cs σ ^ (3 : Nat)
                + 6 * linForm m cg x ^ (2 : Nat) * linearX n cs σ ^ (2 : Nat)
                + 4 * linForm m cg x ^ (3 : Nat) * linearX n cs σ
                + linForm m cg x ^ (4 : Nat)) := by
                  funext σ
                  rw [linForm_hybridPoint_eq_add]
                  ring
        rw [hfun]
        rw [avgSigns_add, avgSigns_add, avgSigns_add, avgSigns_add,
          avgSigns_mul_const_left, avgSigns_mul_const_left, avgSigns_mul_const_left,
          avgSigns_linearX_cube_zero, avgSigns_linearX_zero, avgSigns_const]
        ring
  have hrew :
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => linearX n cs σ ^ (4 : Nat))
          + (6 * linForm m cg x ^ (2 : Nat)) * avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat))
          + linForm m cg x ^ (4 : Nat))
        =
      (fun x : Fin m → ℝ => A + (B * linForm m cg x ^ (2 : Nat) + linForm m cg x ^ (4 : Nat))) := by
        funext x
        ring
  have hA_int :
      MeasureTheory.Integrable (fun x : Fin m → ℝ => A * gaussianWeight m x) := by
    simpa [A, mul_assoc] using integrable_stdGaussianDensity m |>.const_mul A
  have hBsq_int :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ => (B * linForm m cg x ^ (2 : Nat)) * gaussianWeight m x) := by
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using
      (integrable_linForm_sq_gaussianWeight m cg).const_mul B
  have h4_int :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ => linForm m cg x ^ (4 : Nat) * gaussianWeight m x) := by
    simpa using integrable_linForm_four_gaussianWeight m cg
  have hrest_int :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ =>
          (B * linForm m cg x ^ (2 : Nat) + linForm m cg x ^ (4 : Nat))
            * gaussianWeight m x) := by
    simpa [mul_add, add_mul, add_assoc] using hBsq_int.add h4_int
  have hsum_int :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ =>
          (A + (B * linForm m cg x ^ (2 : Nat) + linForm m cg x ^ (4 : Nat)))
            * gaussianWeight m x) := by
    simpa [mul_add, add_mul, add_assoc] using hA_int.add hrest_int
  have hpoint_mul :
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => linForm (n + m) c (hybridPoint n m σ x) ^ (4 : Nat))
          * gaussianWeight m x)
        =
      (fun x : Fin m → ℝ =>
        (A + (B * linForm m cg x ^ (2 : Nat) + linForm m cg x ^ (4 : Nat)))
          * gaussianWeight m x) := by
    funext x
    have hx1 :
        avgSigns n (fun σ => linForm (n + m) c (hybridPoint n m σ x) ^ (4 : Nat))
          =
        (avgSigns n (fun σ => linearX n cs σ ^ (4 : Nat))
          + (6 * linForm m cg x ^ (2 : Nat)) * avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat))
          + linForm m cg x ^ (4 : Nat)) := by
      simpa using congrArg (fun f : (Fin m → ℝ) → ℝ => f x) hpoint
    have hx2 :
        (avgSigns n (fun σ => linearX n cs σ ^ (4 : Nat))
          + (6 * linForm m cg x ^ (2 : Nat)) * avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat))
          + linForm m cg x ^ (4 : Nat))
          =
        A + (B * linForm m cg x ^ (2 : Nat) + linForm m cg x ^ (4 : Nat)) := by
      simpa using congrArg (fun f : (Fin m → ℝ) → ℝ => f x) hrew
    calc
      avgSigns n (fun σ => linForm (n + m) c (hybridPoint n m σ x) ^ (4 : Nat))
          * gaussianWeight m x
          =
        ((avgSigns n (fun σ => linearX n cs σ ^ (4 : Nat))
          + (6 * linForm m cg x ^ (2 : Nat)) * avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat))
          + linForm m cg x ^ (4 : Nat))) * gaussianWeight m x := by rw [hx1]
      _ =
        (A + (B * linForm m cg x ^ (2 : Nat) + linForm m cg x ^ (4 : Nat)))
          * gaussianWeight m x := by rw [hx2]
  simpa [hpoint_mul] using hsum_int

private lemma hybridAvg_linForm_sq_eq_sum_sq (n m : ℕ) (c : Fin (n + m) → ℝ) :
    hybridAvg n m (fun y => linForm (n + m) c y ^ (2 : Nat))
      = ∑ i : Fin (n + m), c i ^ (2 : Nat) := by
  let cs : Fin n → ℝ := signBlockCoeffs n m c
  let cg : Fin m → ℝ := gaussBlockCoeffs n m c
  unfold hybridAvg
  have hpoint :
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => linForm (n + m) c (hybridPoint n m σ x) ^ (2 : Nat)))
        =
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat))
          + linForm m cg x ^ (2 : Nat)) := by
        funext x
        have hfun :
            (fun σ : Fin n → Fin 2 => linForm (n + m) c (hybridPoint n m σ x) ^ (2 : Nat))
              =
            (fun σ : Fin n → Fin 2 =>
              linearX n cs σ ^ (2 : Nat)
                + (2 * linForm m cg x) * linearX n cs σ
                + linForm m cg x ^ (2 : Nat)) := by
                  funext σ
                  rw [linForm_hybridPoint_eq_add]
                  ring
        rw [hfun, avgSigns_add, avgSigns_add, avgSigns_mul_const_left,
          avgSigns_linearX_zero, avgSigns_const]
        ring
  rw [hpoint]
  have hconst_int :
      MeasureTheory.Integrable (fun x : Fin m → ℝ => avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat)) * gaussianWeight m x) := by
    simpa [mul_assoc] using
      integrable_stdGaussianDensity m |>.const_mul (avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat)))
  have hsq_int :
      MeasureTheory.Integrable (fun x : Fin m → ℝ => linForm m cg x ^ (2 : Nat) * gaussianWeight m x) := by
    simpa using integrable_linForm_sq_gaussianWeight m cg
  rw [stdGaussianAvg_add m _ _ hconst_int hsq_int]
  rw [stdGaussianAvg_const, stdGaussianAvg_linForm_sq_eq_sum_sq, avgSigns_linearX_sq]
  rw [Fin.sum_univ_add]
  simp [cs, cg, signBlockCoeffs, gaussBlockCoeffs]

private lemma hybridAvg_linForm_four_le_three_sum_sq_sq (n m : ℕ) (c : Fin (n + m) → ℝ) :
    hybridAvg n m (fun y => linForm (n + m) c y ^ (4 : Nat))
      ≤ 3 * (∑ i : Fin (n + m), c i ^ (2 : Nat)) ^ (2 : Nat) := by
  let cs : Fin n → ℝ := signBlockCoeffs n m c
  let cg : Fin m → ℝ := gaussBlockCoeffs n m c
  let Ss : ℝ := ∑ i : Fin n, cs i ^ (2 : Nat)
  let Sg : ℝ := ∑ i : Fin m, cg i ^ (2 : Nat)
  unfold hybridAvg
  have hpoint :
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => linForm (n + m) c (hybridPoint n m σ x) ^ (4 : Nat)))
        =
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => linearX n cs σ ^ (4 : Nat))
          + (6 * linForm m cg x ^ (2 : Nat)) * avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat))
          + linForm m cg x ^ (4 : Nat)) := by
        funext x
        have hfun :
            (fun σ : Fin n → Fin 2 => linForm (n + m) c (hybridPoint n m σ x) ^ (4 : Nat))
              =
            (fun σ : Fin n → Fin 2 =>
              linearX n cs σ ^ (4 : Nat)
                + 4 * linForm m cg x * linearX n cs σ ^ (3 : Nat)
                + 6 * linForm m cg x ^ (2 : Nat) * linearX n cs σ ^ (2 : Nat)
                + 4 * linForm m cg x ^ (3 : Nat) * linearX n cs σ
                + linForm m cg x ^ (4 : Nat)) := by
                  funext σ
                  rw [linForm_hybridPoint_eq_add]
                  ring
        rw [hfun]
        rw [avgSigns_add, avgSigns_add, avgSigns_add, avgSigns_add,
          avgSigns_mul_const_left, avgSigns_mul_const_left, avgSigns_mul_const_left,
          avgSigns_linearX_cube_zero, avgSigns_linearX_zero, avgSigns_const]
        ring
  rw [hpoint]
  let A : ℝ := avgSigns n (fun σ => linearX n cs σ ^ (4 : Nat))
  let B : ℝ := 6 * avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat))
  have hrew :
      (fun x : Fin m → ℝ =>
        avgSigns n (fun σ => linearX n cs σ ^ (4 : Nat))
          + (6 * linForm m cg x ^ (2 : Nat)) * avgSigns n (fun σ => linearX n cs σ ^ (2 : Nat))
          + linForm m cg x ^ (4 : Nat))
        =
      (fun x : Fin m → ℝ => A + B * linForm m cg x ^ (2 : Nat) + linForm m cg x ^ (4 : Nat)) := by
        funext x
        simp [A, B, mul_assoc, mul_left_comm, mul_comm]
  have hgroup :
      (fun x : Fin m → ℝ => A + B * linForm m cg x ^ (2 : Nat) + linForm m cg x ^ (4 : Nat))
        =
      (fun x : Fin m → ℝ => A + (B * linForm m cg x ^ (2 : Nat) + linForm m cg x ^ (4 : Nat))) := by
        funext x
        ring
  have hA_int :
      MeasureTheory.Integrable (fun x : Fin m → ℝ => A * gaussianWeight m x) := by
    simpa [A, mul_assoc] using integrable_stdGaussianDensity m |>.const_mul A
  have hBsq_int :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ => (B * linForm m cg x ^ (2 : Nat)) * gaussianWeight m x) := by
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using
      (integrable_linForm_sq_gaussianWeight m cg).const_mul B
  have h4_int :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ => linForm m cg x ^ (4 : Nat) * gaussianWeight m x) := by
    simpa using integrable_linForm_four_gaussianWeight m cg
  rw [hrew]
  rw [hgroup]
  rw [stdGaussianAvg_add m (fun _ => A) (fun x => B * linForm m cg x ^ (2 : Nat) + linForm m cg x ^ (4 : Nat))
        hA_int (by
          simpa [mul_add, add_mul, add_assoc] using hBsq_int.add h4_int)]
  rw [stdGaussianAvg_add m (fun x => B * linForm m cg x ^ (2 : Nat))
        (fun x => linForm m cg x ^ (4 : Nat)) hBsq_int h4_int]
  rw [stdGaussianAvg_const, stdGaussianAvg_mul_const, stdGaussianAvg_linForm_sq_eq_sum_sq,
    stdGaussianAvg_linForm_four_eq_three_sum_sq_sq]
  have hA_le : A ≤ 3 * Ss ^ (2 : Nat) := by
    dsimp [A, Ss, cs]
    have hsum4_nonneg : 0 ≤ ∑ i : Fin n, signBlockCoeffs n m c i ^ (4 : Nat) := by
      exact Finset.sum_nonneg (fun _ _ => by positivity)
    rw [avgSigns_linearX_four]
    nlinarith
  have hB_eq : B = 6 * Ss := by
    dsimp [B, Ss, cs]
    rw [avgSigns_linearX_sq]
  have hsplit : ∑ i : Fin (n + m), c i ^ (2 : Nat) = Ss + Sg := by
    rw [Fin.sum_univ_add]
    simp [Ss, Sg, cs, cg, signBlockCoeffs, gaussBlockCoeffs]
  have hfinal :
      A + (B * Sg + 3 * Sg ^ (2 : Nat))
        ≤ 3 * (∑ i : Fin (n + m), c i ^ (2 : Nat)) ^ (2 : Nat) := by
    calc
      A + (B * Sg + 3 * Sg ^ (2 : Nat))
        ≤ 3 * Ss ^ (2 : Nat) + ((6 * Ss) * Sg + 3 * Sg ^ (2 : Nat)) := by
            rw [hB_eq]
            gcongr
      _ = 3 * (Ss + Sg) ^ (2 : Nat) := by ring
      _ = 3 * (∑ i : Fin (n + m), c i ^ (2 : Nat)) ^ (2 : Nat) := by rw [hsplit]
  simpa [add_assoc] using hfinal

private lemma sqrt_mul_mul_eq_weighted_sqrt_mul
    {a b w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hw : 0 ≤ w) :
    Real.sqrt (a * b) * w = Real.sqrt (a * w) * Real.sqrt (b * w) := by
  have hleft_nonneg : 0 ≤ Real.sqrt (a * b) * w := by
    exact mul_nonneg (Real.sqrt_nonneg _) hw
  have hright_nonneg : 0 ≤ Real.sqrt (a * w) * Real.sqrt (b * w) := by
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq :
      (Real.sqrt (a * b) * w) ^ (2 : Nat)
        = (Real.sqrt (a * w) * Real.sqrt (b * w)) ^ (2 : Nat) := by
    calc
      (Real.sqrt (a * b) * w) ^ (2 : Nat)
          = (Real.sqrt (a * b) * Real.sqrt (a * b)) * (w * w) := by
              ring
      _ = (a * b) * (w * w) := by
            rw [show Real.sqrt (a * b) * Real.sqrt (a * b) = a * b by
              rw [← sq, Real.sq_sqrt (mul_nonneg ha hb)]]
      _ = (a * w) * (b * w) := by ring
      _ = (Real.sqrt (a * w) * Real.sqrt (b * w)) ^ (2 : Nat) := by
            rw [pow_two]
            symm
            calc
              Real.sqrt (a * w) * Real.sqrt (b * w) * (Real.sqrt (a * w) * Real.sqrt (b * w))
                  = (Real.sqrt (a * w) * Real.sqrt (a * w))
                      * (Real.sqrt (b * w) * Real.sqrt (b * w)) := by
                        ring
              _ = (a * w) * (b * w) := by
                    rw [show Real.sqrt (a * w) * Real.sqrt (a * w) = a * w by
                          rw [← sq, Real.sq_sqrt (mul_nonneg ha hw)]]
                    rw [show Real.sqrt (b * w) * Real.sqrt (b * w) = b * w by
                          rw [← sq, Real.sq_sqrt (mul_nonneg hb hw)]]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hEq | hEq
  · exact hEq
  · linarith

private lemma integrable_gaussianWeight_sqrt_mul
    (m : ℕ) {A B : (Fin m → ℝ) → ℝ}
    (hA_nonneg : ∀ x : Fin m → ℝ, 0 ≤ A x)
    (hB_nonneg : ∀ x : Fin m → ℝ, 0 ≤ B x)
    (hA_int : MeasureTheory.Integrable (fun x : Fin m → ℝ => A x * gaussianWeight m x))
    (hB_int : MeasureTheory.Integrable (fun x : Fin m → ℝ => B x * gaussianWeight m x)) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ => Real.sqrt (A x * B x) * gaussianWeight m x) := by
  let F : (Fin m → ℝ) → ℝ := fun x => A x * gaussianWeight m x
  let G : (Fin m → ℝ) → ℝ := fun x => B x * gaussianWeight m x
  have hF_nonneg : ∀ x : Fin m → ℝ, 0 ≤ F x := by
    intro x
    dsimp [F]
    positivity [hA_nonneg x, gaussianWeight_nonneg m x]
  have hG_nonneg : ∀ x : Fin m → ℝ, 0 ≤ G x := by
    intro x
    dsimp [G]
    positivity [hB_nonneg x, gaussianWeight_nonneg m x]
  have hsqrt_int :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ => Real.sqrt (F x) * Real.sqrt (G x)) :=
    integrable_sqrt_mul m hF_nonneg hG_nonneg hA_int hB_int
  have hrew :
      (fun x : Fin m → ℝ => Real.sqrt (A x * B x) * gaussianWeight m x)
        =
      (fun x : Fin m → ℝ => Real.sqrt (F x) * Real.sqrt (G x)) := by
    funext x
    dsimp [F, G]
    exact sqrt_mul_mul_eq_weighted_sqrt_mul (hA_nonneg x) (hB_nonneg x) (gaussianWeight_nonneg m x)
  simpa [hrew] using hsqrt_int

private lemma stdGaussianAvg_sqrt_mul_le
    (m : ℕ) {A B : (Fin m → ℝ) → ℝ}
    (hA_nonneg : ∀ x : Fin m → ℝ, 0 ≤ A x)
    (hB_nonneg : ∀ x : Fin m → ℝ, 0 ≤ B x)
    (hA_int : MeasureTheory.Integrable (fun x : Fin m → ℝ => A x * gaussianWeight m x))
    (hB_int : MeasureTheory.Integrable (fun x : Fin m → ℝ => B x * gaussianWeight m x)) :
    stdGaussianAvg m (fun x => Real.sqrt (A x * B x))
      ≤ Real.sqrt (stdGaussianAvg m A * stdGaussianAvg m B) := by
  let F : (Fin m → ℝ) → ℝ := fun x => A x * gaussianWeight m x
  let G : (Fin m → ℝ) → ℝ := fun x => B x * gaussianWeight m x
  let α : ℝ := ((2 * Real.pi) ^ ((m : ℝ) / 2))⁻¹
  have hF_nonneg : ∀ x : Fin m → ℝ, 0 ≤ F x := by
    intro x
    dsimp [F]
    positivity [hA_nonneg x, gaussianWeight_nonneg m x]
  have hG_nonneg : ∀ x : Fin m → ℝ, 0 ≤ G x := by
    intro x
    dsimp [G]
    positivity [hB_nonneg x, gaussianWeight_nonneg m x]
  have hcs := integral_sqrt_mul_le_sqrt_integral_mul m hF_nonneg hG_nonneg hA_int hB_int
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    positivity [Real.pi_pos]
  have hFint_nonneg : 0 ≤ ∫ x : Fin m → ℝ, F x := MeasureTheory.integral_nonneg hF_nonneg
  have hGint_nonneg : 0 ≤ ∫ x : Fin m → ℝ, G x := MeasureTheory.integral_nonneg hG_nonneg
  unfold stdGaussianAvg
  calc
    α * ∫ x : Fin m → ℝ, Real.sqrt (A x * B x) * gaussianWeight m x
      = α * ∫ x : Fin m → ℝ, Real.sqrt (F x) * Real.sqrt (G x) := by
          congr 2
          funext x
          dsimp [F, G]
          exact sqrt_mul_mul_eq_weighted_sqrt_mul (hA_nonneg x) (hB_nonneg x) (gaussianWeight_nonneg m x)
    _ ≤ α * (Real.sqrt (∫ x : Fin m → ℝ, F x) * Real.sqrt (∫ x : Fin m → ℝ, G x)) := by
          exact mul_le_mul_of_nonneg_left hcs hα_nonneg
    _ = Real.sqrt ((α * ∫ x : Fin m → ℝ, F x) * (α * ∫ x : Fin m → ℝ, G x)) := by
          have hsqrtFG :
              Real.sqrt (∫ x : Fin m → ℝ, F x) * Real.sqrt (∫ x : Fin m → ℝ, G x)
                = Real.sqrt ((∫ x : Fin m → ℝ, F x) * (∫ x : Fin m → ℝ, G x)) := by
            rw [Real.sqrt_mul hFint_nonneg]
          rw [hsqrtFG, mul_comm]
          calc
            Real.sqrt ((∫ x : Fin m → ℝ, F x) * (∫ x : Fin m → ℝ, G x)) * α
                = Real.sqrt ((∫ x : Fin m → ℝ, F x) * α)
                    * Real.sqrt ((∫ x : Fin m → ℝ, G x) * α) := by
                    exact sqrt_mul_mul_eq_weighted_sqrt_mul hFint_nonneg hGint_nonneg hα_nonneg
            _ = Real.sqrt (((∫ x : Fin m → ℝ, F x) * α) * ((∫ x : Fin m → ℝ, G x) * α)) := by
                    symm
                    rw [Real.sqrt_mul (mul_nonneg hFint_nonneg hα_nonneg)]
            _ = Real.sqrt ((α * ∫ x : Fin m → ℝ, F x) * (α * ∫ x : Fin m → ℝ, G x)) := by
                    congr 1
                    ring
    _ = Real.sqrt (stdGaussianAvg m A * stdGaussianAvg m B) := by
          rfl

private lemma hybridAvg_abs_linForm_cube_le_sqrt_second_fourth (n m : ℕ) (c : Fin (n + m) → ℝ) :
    hybridAvg n m (fun y => |linForm (n + m) c y| ^ (3 : Nat))
      ≤
    Real.sqrt
      (hybridAvg n m (fun y => linForm (n + m) c y ^ (2 : Nat))
        * hybridAvg n m (fun y => linForm (n + m) c y ^ (4 : Nat))) := by
  let A : (Fin m → ℝ) → ℝ :=
    fun x => avgSigns n (fun σ => linForm (n + m) c (hybridPoint n m σ x) ^ (2 : Nat))
  let B : (Fin m → ℝ) → ℝ :=
    fun x => avgSigns n (fun σ => linForm (n + m) c (hybridPoint n m σ x) ^ (4 : Nat))
  let C : (Fin m → ℝ) → ℝ :=
    fun x => avgSigns n (fun σ => |linForm (n + m) c (hybridPoint n m σ x)| ^ (3 : Nat))
  let g : (Fin m → ℝ) → ℝ := fun x => Real.sqrt (A x * B x)
  have hA_nonneg : ∀ x : Fin m → ℝ, 0 ≤ A x := by
    intro x
    dsimp [A, avgSigns]
    positivity
  have hB_nonneg : ∀ x : Fin m → ℝ, 0 ≤ B x := by
    intro x
    dsimp [B, avgSigns]
    positivity
  have hC_nonneg : ∀ x : Fin m → ℝ, 0 ≤ C x := by
    intro x
    dsimp [C, avgSigns]
    positivity
  have hg_int :
      MeasureTheory.Integrable (fun x : Fin m → ℝ => g x * gaussianWeight m x) := by
    apply integrable_gaussianWeight_sqrt_mul m hA_nonneg hB_nonneg
    · simpa [A] using integrable_hybrid_second_avgSigns_gaussianWeight n m c
    · simpa [B] using integrable_hybrid_fourth_avgSigns_gaussianWeight n m c
  have hCg : ∀ x : Fin m → ℝ, C x ≤ g x := by
    intro x
    dsimp [C, g, A, B]
    exact avgSigns_abs_cube_le_sqrt_second_fourth n
      (fun σ => linForm (n + m) c (hybridPoint n m σ x))
  calc
    hybridAvg n m (fun y => |linForm (n + m) c y| ^ (3 : Nat))
      ≤ stdGaussianAvg m g := by
          simpa [hybridAvg, C] using stdGaussianAvg_mono_of_nonneg m hC_nonneg hg_int hCg
    _ ≤
      Real.sqrt
        (hybridAvg n m (fun y => linForm (n + m) c y ^ (2 : Nat))
          * hybridAvg n m (fun y => linForm (n + m) c y ^ (4 : Nat))) := by
          apply stdGaussianAvg_sqrt_mul_le m hA_nonneg hB_nonneg
          · simpa [A] using integrable_hybrid_second_avgSigns_gaussianWeight n m c
          · simpa [B] using integrable_hybrid_fourth_avgSigns_gaussianWeight n m c

private lemma hybridAvg_abs_linForm_cube_le_sqrt_three_mul_sum_sq_mul_sqrt_sum_sq
    (n m : ℕ) (c : Fin (n + m) → ℝ) :
    hybridAvg n m (fun y => |linForm (n + m) c y| ^ (3 : Nat))
      ≤
    Real.sqrt 3
      * (∑ i : Fin (n + m), c i ^ (2 : Nat))
      * Real.sqrt (∑ i : Fin (n + m), c i ^ (2 : Nat)) := by
  let S : ℝ := ∑ i : Fin (n + m), c i ^ (2 : Nat)
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    positivity
  calc
    hybridAvg n m (fun y => |linForm (n + m) c y| ^ (3 : Nat))
      ≤
    Real.sqrt
      (hybridAvg n m (fun y => linForm (n + m) c y ^ (2 : Nat))
        * hybridAvg n m (fun y => linForm (n + m) c y ^ (4 : Nat))) :=
      hybridAvg_abs_linForm_cube_le_sqrt_second_fourth n m c
    _ = Real.sqrt (S * hybridAvg n m (fun y => linForm (n + m) c y ^ (4 : Nat))) := by
      rw [hybridAvg_linForm_sq_eq_sum_sq n m c]
    _ ≤ Real.sqrt (S * (3 * S ^ (2 : Nat))) := by
      apply Real.sqrt_le_sqrt
      gcongr
      exact hybridAvg_linForm_four_le_three_sum_sq_sq n m c
    _ = Real.sqrt (3 * S ^ (2 : Nat)) * Real.sqrt S := by
      rw [show S * (3 * S ^ (2 : Nat)) = (3 * S ^ (2 : Nat)) * S by ring]
      rw [Real.sqrt_mul (by positivity)]
    _ = (Real.sqrt 3 * S) * Real.sqrt S := by
      rw [Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hS_nonneg]
    _ = Real.sqrt 3 * S * Real.sqrt S := by ring

private lemma kernelInfluence_nonneg
    (n : ℕ) (f : Fin n → Fin n → ℝ) (k : Fin n) :
    0 ≤ kernelInfluence n f k := by
  unfold kernelInfluence
  positivity

private lemma sum_sq_rowKernelAt_eq_four_kernelInfluence
    {n : ℕ} (k : Fin (n + 1)) (f : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hdiag : ∀ i, f i i = 0) :
    ∑ i : Fin n, rowKernelAt k f i ^ (2 : Nat)
      = 4 * kernelInfluence (n + 1) f k := by
  have hsum :
      ∑ i : Fin n, rowKernelAt k f i ^ (2 : Nat)
        =
      4 * ∑ i : Fin n, f k (k.succAbove i) ^ (2 : Nat) := by
    unfold rowKernelAt
    calc
      ∑ i : Fin n, (2 * f k (k.succAbove i)) ^ (2 : Nat)
          =
        ∑ i : Fin n, 4 * (f k (k.succAbove i) ^ (2 : Nat)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
      _ = 4 * ∑ i : Fin n, f k (k.succAbove i) ^ (2 : Nat) := by
            rw [← Finset.mul_sum]
  have hkernel :
      kernelInfluence (n + 1) f k
        = ∑ i : Fin n, f k (k.succAbove i) ^ (2 : Nat) := by
    unfold kernelInfluence
    rw [Fin.sum_univ_succAbove (f := fun j : Fin (n + 1) => f k j ^ (2 : Nat)) k]
    simp [hdiag]
  calc
    ∑ i : Fin n, rowKernelAt k f i ^ (2 : Nat)
        = 4 * ∑ i : Fin n, f k (k.succAbove i) ^ (2 : Nat) := hsum
    _ = 4 * kernelInfluence (n + 1) f k := by rw [hkernel]

private lemma abs_stdGaussianAvg_le_stdGaussianAvg_abs
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    |stdGaussianAvg n f| ≤ stdGaussianAvg n (fun x => |f x|) := by
  unfold stdGaussianAvg
  have hfac_nonneg : 0 ≤ ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹ := by
    positivity [Real.pi_pos]
  calc
    |((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹
        * ∫ x : Fin n → ℝ, f x * gaussianWeight n x|
      = ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹
          * |∫ x : Fin n → ℝ, f x * gaussianWeight n x| := by
            rw [abs_mul, abs_of_nonneg hfac_nonneg]
    _ ≤ ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹
          * ∫ x : Fin n → ℝ, |f x * gaussianWeight n x| := by
            gcongr
            exact MeasureTheory.norm_integral_le_integral_norm
              (fun x : Fin n → ℝ => f x * gaussianWeight n x)
    _ = ((2 * Real.pi) ^ ((n : ℝ) / 2))⁻¹
          * ∫ x : Fin n → ℝ, |f x| * gaussianWeight n x := by
            congr 2
            funext x
            have hgw_nonneg : 0 ≤ gaussianWeight n x := gaussianWeight_nonneg n x
            rw [abs_mul, abs_of_nonneg hgw_nonneg]
    _ = stdGaussianAvg n (fun x => |f x|) := by
            simp [stdGaussianAvg, gaussianWeight]

private lemma stdGaussianAvg1_avgSigns_commute
    (n : ℕ) (H : (Fin n → Fin 2) → ℝ → ℝ)
    (hH_int : ∀ σ : Fin n → Fin 2,
      MeasureTheory.Integrable (fun z : ℝ => H σ z * Real.exp (-(z ^ (2 : Nat)) / 2))) :
    stdGaussianAvg1 (fun z : ℝ => avgSigns n (fun σ => H σ z))
      = avgSigns n (fun σ => stdGaussianAvg1 (fun z : ℝ => H σ z)) := by
  let c0 : ℝ := ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹
  let c1 : ℝ := (↑(2 ^ n : ℕ) : ℝ)⁻¹
  unfold stdGaussianAvg1 avgSigns
  have hsum :
      ∫ z : ℝ, ∑ σ : Fin n → Fin 2, c1 * (H σ z * Real.exp (-(z ^ (2 : Nat)) / 2))
        =
      ∑ σ : Fin n → Fin 2, ∫ z : ℝ, c1 * (H σ z * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    simpa using
      (MeasureTheory.integral_finset_sum (Finset.univ)
        (fun σ _ => (hH_int σ).const_mul c1))
  calc
    c0 * ∫ z : ℝ, avgSigns n (fun σ => H σ z) * Real.exp (-(z ^ (2 : Nat)) / 2)
      =
    c0 * ∫ z : ℝ,
      ∑ σ : Fin n → Fin 2, c1 * (H σ z * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
        congr 2 with z
        calc
          (avgSigns n (fun σ => H σ z)) * Real.exp (-(z ^ (2 : Nat)) / 2)
            = (((↑(2 ^ n : ℕ) : ℝ)⁻¹) * ∑ σ : Fin n → Fin 2, H σ z)
                * Real.exp (-(z ^ (2 : Nat)) / 2) := by
                  rfl
          _ = (((↑(2 ^ n : ℕ) : ℝ)⁻¹))
                * ∑ σ : Fin n → Fin 2, H σ z * Real.exp (-(z ^ (2 : Nat)) / 2) := by
                  rw [mul_assoc, Finset.sum_mul]
          _ = ∑ σ : Fin n → Fin 2,
                (((↑(2 ^ n : ℕ) : ℝ)⁻¹) * (H σ z * Real.exp (-(z ^ (2 : Nat)) / 2))) := by
                  rw [Finset.mul_sum]
          _ = ∑ σ : Fin n → Fin 2, c1 * (H σ z * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
                  refine Finset.sum_congr rfl ?_
                  intro σ hσ
                  simp [c1]
    _ = c0 * ∑ σ : Fin n → Fin 2, ∫ z : ℝ, c1 * (H σ z * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
          rw [hsum]
    _ = c0 * ∑ σ : Fin n → Fin 2, c1 * ∫ z : ℝ, H σ z * Real.exp (-(z ^ (2 : Nat)) / 2) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          rw [MeasureTheory.integral_const_mul]
    _ = ∑ σ : Fin n → Fin 2, c0 * (c1 * ∫ z : ℝ, H σ z * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
          rw [Finset.mul_sum]
    _ = ∑ σ : Fin n → Fin 2, c1 * (c0 * ∫ z : ℝ, H σ z * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
          refine Finset.sum_congr rfl ?_
          intro σ hσ
          ring
    _ = c1 * ∑ σ : Fin n → Fin 2, c0 * ∫ z : ℝ, H σ z * Real.exp (-(z ^ (2 : Nat)) / 2) := by
          rw [← Finset.mul_sum]
    _ = avgSigns n (fun σ => stdGaussianAvg1 (fun z : ℝ => H σ z)) := by
          unfold avgSigns stdGaussianAvg1
          simp [c0, c1, mul_assoc, mul_left_comm, mul_comm]

private lemma stdGaussianAvg1_mono_of_nonneg
    {f g : ℝ → ℝ}
    (hf_nonneg : ∀ z : ℝ, 0 ≤ f z)
    (hg_int : MeasureTheory.Integrable (fun z : ℝ => g z * Real.exp (-(z ^ (2 : Nat)) / 2)))
    (hfg : ∀ z : ℝ, f z ≤ g z) :
    stdGaussianAvg1 f ≤ stdGaussianAvg1 g := by
  unfold stdGaussianAvg1
  have hfac_nonneg : 0 ≤ ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹ := by
    positivity [Real.pi_pos]
  have hint :=
    MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => mul_nonneg (hf_nonneg z) (Real.exp_nonneg _)))
      hg_int
      (Filter.Eventually.of_forall (fun z => by
        exact mul_le_mul_of_nonneg_right (hfg z) (Real.exp_nonneg _)))
  exact mul_le_mul_of_nonneg_left hint hfac_nonneg

private lemma abs_stdGaussianAvg1_le_stdGaussianAvg1_abs (f : ℝ → ℝ) :
    |stdGaussianAvg1 f| ≤ stdGaussianAvg1 (fun z => |f z|) := by
  unfold stdGaussianAvg1
  have hfac_nonneg : 0 ≤ ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹ := by
    positivity [Real.pi_pos]
  calc
    |((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹
        * ∫ z : ℝ, f z * Real.exp (-(z ^ (2 : Nat)) / 2)|
      = ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹
          * |∫ z : ℝ, f z * Real.exp (-(z ^ (2 : Nat)) / 2)| := by
            rw [abs_mul, abs_of_nonneg hfac_nonneg]
    _ ≤ ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹
          * ∫ z : ℝ, |f z * Real.exp (-(z ^ (2 : Nat)) / 2)| := by
            exact mul_le_mul_of_nonneg_left
              (MeasureTheory.norm_integral_le_integral_norm (fun z : ℝ => f z * Real.exp (-(z ^ (2 : Nat)) / 2)))
              hfac_nonneg
    _ = ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹
          * ∫ z : ℝ, |f z| * Real.exp (-(z ^ (2 : Nat)) / 2) := by
            congr 1
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall (fun z => by
              simp [Real.exp_nonneg])
    _ = stdGaussianAvg1 (fun z => |f z|) := by
            simp [stdGaussianAvg1]

private lemma abs_stdGaussianAvg1_le_of_abs_le
    {f g : ℝ → ℝ}
    (_hg_nonneg : ∀ z : ℝ, 0 ≤ g z)
    (hg_int : MeasureTheory.Integrable (fun z : ℝ => g z * Real.exp (-(z ^ (2 : Nat)) / 2)))
    (hfg : ∀ z : ℝ, |f z| ≤ g z) :
    |stdGaussianAvg1 f| ≤ stdGaussianAvg1 g := by
  refine le_trans (abs_stdGaussianAvg1_le_stdGaussianAvg1_abs f) ?_
  exact stdGaussianAvg1_mono_of_nonneg (fun z => abs_nonneg (f z)) hg_int hfg


private lemma stdGaussianAvg1_abs_cube_eq :
    stdGaussianAvg1 (fun z : ℝ => |z| ^ (3 : Nat)) = 4 / Real.sqrt (2 * Real.pi) := by
  unfold stdGaussianAvg1
  have hfabs :
      ∫ z : ℝ, |z| ^ (3 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)
        =
      ∫ z : ℝ, (fun t : ℝ => t ^ (3 : Nat) * Real.exp (-(t ^ (2 : Nat)) / 2)) |z| := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall (fun z => by simp)
  have hIoi :=
    (integral_rpow_mul_exp_neg_mul_rpow
      (by norm_num : (0 : ℝ) < 2)
      (by norm_num : -1 < (3 : ℝ))
      (by positivity : 0 < (1 / 2 : ℝ)) :
        ∫ x in Set.Ioi (0 : ℝ), x ^ (3 : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ))
          = (1 / 2 : ℝ) ^ (-((3 : ℝ) + 1) / 2) * (1 / 2 : ℝ) * Real.Gamma (((3 : ℝ) + 1) / 2))
  have hpowIoi :
      ∫ x in Set.Ioi (0 : ℝ), x ^ (3 : Nat) * Real.exp (-(x ^ (2 : Nat)) / 2)
        =
      ∫ x in Set.Ioi (0 : ℝ), x ^ (3 : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [Set.mem_Ioi] at hx
    rw [show (x ^ (3 : Nat) : ℝ) = x ^ (3 : ℝ) by
      symm
      exact Real.rpow_natCast x 3]
    rw [show (x ^ (2 : Nat) : ℝ) = x ^ (2 : ℝ) by
      symm
      exact Real.rpow_natCast x 2]
    ring
  have hmass :
      ∫ z : ℝ, |z| ^ (3 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2) = 4 := by
    let f : ℝ → ℝ := fun t => t ^ (3 : Nat) * Real.exp (-(t ^ (2 : Nat)) / 2)
    have hcomp_abs : ∫ z : ℝ, f |z| = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := by
      rw [integral_comp_abs]
    calc
      ∫ z : ℝ, |z| ^ (3 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)
          = ∫ z : ℝ, f |z| := hfabs
      _ = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := hcomp_abs
      _ = 2 * ∫ x in Set.Ioi (0 : ℝ), x ^ (3 : Nat) * Real.exp (-(x ^ (2 : Nat)) / 2) := by
            simp [f]
      _ = 2 * ∫ x in Set.Ioi (0 : ℝ), x ^ (3 : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ)) := by
            simpa using congrArg (fun r : ℝ => 2 * r) hpowIoi
      _ = 2 * ((1 / 2 : ℝ) ^ (-((3 : ℝ) + 1) / 2) * (1 / 2 : ℝ) * Real.Gamma (((3 : ℝ) + 1) / 2)) := by
            simpa using congrArg (fun r : ℝ => 2 * r) hIoi
      _ = 4 := by
            norm_num [Real.Gamma_two]
  have hrpow : (2 * Real.pi) ^ ((1 : ℝ) / 2) = Real.sqrt (2 * Real.pi) := by
    symm
    rw [Real.sqrt_eq_rpow]
  calc
    ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹
        * ∫ z : ℝ, |z| ^ (3 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)
      = ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹ * 4 := by rw [hmass]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * 4 := by rw [hrpow]
    _ = 4 / Real.sqrt (2 * Real.pi) := by
          rw [div_eq_mul_inv, mul_comm]

private lemma lindeberg_scalar_constant_le_three_quarters :
    (((1 + 4 / Real.sqrt (2 * Real.pi)) * Real.sqrt 3) / 6 : ℝ) ≤ 3 / 4 := by
  have hs2 : (Real.sqrt 2) ^ (2 : Nat) = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
  have hs3 : (Real.sqrt 3) ^ (2 : Nat) = 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by positivity)]
  have hspi : (Real.sqrt (2 * Real.pi)) ^ (2 : Nat) = 2 * Real.pi := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 * Real.pi by positivity [Real.pi_pos])]
  have hpi : (3.1415 : ℝ) < Real.pi := Real.pi_gt_d4
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) := by
    positivity [Real.pi_pos]
  have hsqrt3_lt : Real.sqrt 3 < (1733 / 1000 : ℝ) := by
    have hnum : (3 : ℝ) < (1733 / 1000 : ℝ) ^ (2 : Nat) := by norm_num
    nlinarith [hs3, hnum]
  have hsqrt3_ge_one : (1 : ℝ) ≤ Real.sqrt 3 := by
    have hsqrt3_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
    nlinarith [hs3]
  have hrhs_nonneg : 0 ≤ (3 * Real.sqrt 3 / 2 - 1 : ℝ) := by
    nlinarith [hsqrt3_ge_one]
  have hbound : 4 / Real.sqrt (2 * Real.pi) ≤ 3 * Real.sqrt 3 / 2 - 1 := by
    have hbound_sq :
        16 ≤ (3 * Real.sqrt 3 / 2 - 1) ^ (2 : Nat) * (Real.sqrt (2 * Real.pi) ^ (2 : Nat)) := by
      nlinarith [hpi, hspi, hs3, hsqrt3_lt]
    have hprod : 4 ≤ (3 * Real.sqrt 3 / 2 - 1) * Real.sqrt (2 * Real.pi) := by
      nlinarith [hbound_sq, hsqrt_pos, hrhs_nonneg]
    have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt hsqrt_pos
    calc
      4 / Real.sqrt (2 * Real.pi) = 4 * (Real.sqrt (2 * Real.pi))⁻¹ := by
        rw [div_eq_mul_inv]
      _ ≤ ((3 * Real.sqrt 3 / 2 - 1) * Real.sqrt (2 * Real.pi)) * (Real.sqrt (2 * Real.pi))⁻¹ := by
        gcongr
      _ = 3 * Real.sqrt 3 / 2 - 1 := by
        field_simp [hsqrt_ne]
  have hsqrt3_nonneg : 0 ≤ Real.sqrt 3 := by positivity
  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := by
    nlinarith [hs3]
  have hmain :
      (1 + 4 / Real.sqrt (2 * Real.pi)) * Real.sqrt 3
        ≤ (3 * Real.sqrt 3 / 2) * Real.sqrt 3 := by
    gcongr
    linarith [hbound]
  calc
    (((1 + 4 / Real.sqrt (2 * Real.pi)) * Real.sqrt 3) / 6 : ℝ)
        ≤ ((3 * Real.sqrt 3 / 2) * Real.sqrt 3) / 6 := by
              exact div_le_div_of_nonneg_right hmain (by positivity)
    _ = 3 / 4 := by
          nlinarith [hs3]

private lemma hybridAvg_all_gaussian (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    hybridAvg 0 n
      (fun y : Fin (0 + n) → ℝ => f (fun i : Fin n => y (Fin.cast (by omega) i)))
      = stdGaussianAvg n f := by
  unfold hybridAvg
  congr 1
  funext x
  unfold avgSigns
  have hsum :
      ∑ σ : Fin 0 → Fin 2, f (fun i : Fin n => hybridPoint 0 n σ x (Fin.cast (by omega) i))
        =
      f (fun i : Fin n => hybridPoint 0 n Fin.elim0 x (Fin.cast (by omega) i)) := by
        rw [Fintype.sum_unique]
        exact congrArg
          (fun σ : Fin 0 → Fin 2 =>
            f (fun i : Fin n => hybridPoint 0 n σ x (Fin.cast (by omega) i)))
          (Subsingleton.elim _ _)
  have hhyb :
      (fun i : Fin n => hybridPoint 0 n Fin.elim0 x (Fin.cast (by omega) i)) = x := by
    funext i
    simpa [hybridPoint] using
      (Fin.append_right
        (u := fun j : Fin 0 => (((signOf (Fin.elim0 j) : ℤ) : ℝ)))
        (v := x) i)
  rw [hsum]
  simpa [hhyb]

private lemma hybridAvg_q2_all_sign
    (n : ℕ) (f : Fin n → Fin n → ℝ) (φ : ℝ → ℝ) :
    hybridAvg n 0 (fun y => φ (Q2Gauss n f y))
      = avgSigns n (fun σ => φ (Q2Signs n f σ)) := by
  unfold hybridAvg
  rw [stdGaussianAvg_zero]
  congr 1
  funext σ
  congr 1
  ext i
  simp [hybridPoint, Q2Signs]

private lemma third_order_taylor_remainder_abs_le_of_nonneg
    (φ : ℝ → ℝ) (a b M : ℝ)
    (_hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M)
    (hb : 0 ≤ b) :
    |φ (a + b) - φ a - b * deriv φ a - (b ^ (2 : Nat) / 2) * iteratedDeriv 2 φ a|
      ≤ M * |b| ^ (3 : Nat) / 6 := by
  rcases eq_or_lt_of_le hb with rfl | hb'
  · simp
  have hmema : a ∈ Set.Icc a (a + b) := ⟨le_rfl, by linarith⟩
  have hφ0 : ContDiffAt ℝ (0 : ℕ∞) φ a := hφ.contDiffAt.of_le (by norm_num)
  have hφ1 : ContDiffAt ℝ (1 : ℕ∞) φ a := hφ.contDiffAt.of_le (by norm_num)
  have hφ2 : ContDiffAt ℝ (2 : ℕ∞) φ a := hφ.contDiffAt.of_le (by norm_num)
  have h0 :
      iteratedDerivWithin 0 φ (Set.Icc a (a + b)) a = φ a := by
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith)) hφ0 hmema
  have h1 :
      iteratedDerivWithin 1 φ (Set.Icc a (a + b)) a = deriv φ a := by
    have h1' :
        iteratedDerivWithin 1 φ (Set.Icc a (a + b)) a = iteratedDeriv 1 φ a :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith)) hφ1 hmema
    simpa [iteratedDerivWithin_one, iteratedDeriv_one] using h1'
  have h2 :
      iteratedDerivWithin 2 φ (Set.Icc a (a + b)) a = iteratedDeriv 2 φ a := by
    exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith)) hφ2 hmema
  obtain ⟨ξ, hξ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := φ) (x := a + b) (x₀ := a) (n := 2) (by linarith)
      (by simpa using hφ.contDiffOn)
  have htaylor :
      taylorWithinEval φ 2 (Set.Icc a (a + b)) a (a + b)
        = φ a + b * deriv φ a + (b ^ (2 : Nat) / 2) * iteratedDeriv 2 φ a := by
    have hab : a + b - a = b := by ring
    rw [taylor_within_apply, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero]
    rw [h0, h1, h2, hab]
    simp [Nat.factorial, smul_eq_mul]
    ring_nf
    simp
  have hmain :
      φ (a + b) - (φ a + b * deriv φ a + (b ^ (2 : Nat) / 2) * iteratedDeriv 2 φ a)
        = iteratedDeriv 3 φ ξ * b ^ (3 : Nat) / 6 := by
    rw [htaylor] at hrem
    simpa [Nat.factorial] using hrem
  have hmain' :
      φ (a + b) - φ a - b * deriv φ a - (b ^ (2 : Nat) / 2) * iteratedDeriv 2 φ a
        = iteratedDeriv 3 φ ξ * b ^ (3 : Nat) / 6 := by
    calc
      φ (a + b) - φ a - b * deriv φ a - (b ^ (2 : Nat) / 2) * iteratedDeriv 2 φ a
        = φ (a + b) - (φ a + b * deriv φ a + (b ^ (2 : Nat) / 2) * iteratedDeriv 2 φ a) := by
            ring
      _ = iteratedDeriv 3 φ ξ * b ^ (3 : Nat) / 6 := hmain
  have hsplit :
      iteratedDeriv 3 φ ξ * b ^ (3 : Nat) / 6
        = iteratedDeriv 3 φ ξ * (b ^ (3 : Nat) / 6) := by
    ring
  have hb3_nonneg : 0 ≤ b ^ (3 : Nat) / 6 := by positivity
  calc
    |φ (a + b) - φ a - b * deriv φ a - (b ^ (2 : Nat) / 2) * iteratedDeriv 2 φ a|
      = |iteratedDeriv 3 φ ξ * b ^ (3 : Nat) / 6| := by
          rw [hmain']
    _ = |iteratedDeriv 3 φ ξ * (b ^ (3 : Nat) / 6)| := by rw [hsplit]
    _ = |iteratedDeriv 3 φ ξ| * (b ^ (3 : Nat) / 6) := by
          rw [abs_mul, abs_of_nonneg hb3_nonneg]
    _ ≤ M * (b ^ (3 : Nat) / 6) := by
          gcongr
          exact hφ3 ξ
    _ = M * |b| ^ (3 : Nat) / 6 := by
          rw [abs_of_nonneg hb]
          ring

private lemma third_order_taylor_remainder_abs_le
    (φ : ℝ → ℝ) (a b M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    |φ (a + b) - φ a - b * deriv φ a - (b ^ (2 : Nat) / 2) * iteratedDeriv 2 φ a|
      ≤ M * |b| ^ (3 : Nat) / 6 := by
  by_cases hb : 0 ≤ b
  · exact third_order_taylor_remainder_abs_le_of_nonneg φ a b M hM_nonneg hφ hφ3 hb
  · let g : ℝ → ℝ := fun t => φ (a - t)
    have hneg : 0 ≤ -b := by linarith
    have hg : ContDiff ℝ 3 g := by
      fun_prop
    have hg3 : ∀ x : ℝ, |iteratedDeriv 3 g x| ≤ M := by
      intro x
      have hcomp := congrFun (iteratedDeriv_comp_const_sub (n := 3) (f := φ) (s := a)) x
      have hcomp' : iteratedDeriv 3 g x = -iteratedDeriv 3 φ (a - x) := by
        calc
          iteratedDeriv 3 g x = (-1 : ℝ) ^ (3 : Nat) * iteratedDeriv 3 φ (a - x) := by
            simpa [g, smul_eq_mul] using hcomp
          _ = -iteratedDeriv 3 φ (a - x) := by norm_num
      rw [hcomp', abs_neg]
      exact hφ3 (a - x)
    have hg1 : deriv g 0 = -deriv φ a := by
      simpa [g] using (deriv_comp_const_sub (f := φ) a 0)
    have hg2 : iteratedDeriv 2 g 0 = iteratedDeriv 2 φ a := by
      have hcomp := congrFun (iteratedDeriv_comp_const_sub (n := 2) (f := φ) (s := a)) 0
      simpa [g, smul_eq_mul] using hcomp
    have hpos :=
      third_order_taylor_remainder_abs_le_of_nonneg g 0 (-b) M hM_nonneg hg hg3 hneg
    have hleft :
        |g (0 + -b) - g 0 - (-b) * deriv g 0 - (((-b) ^ (2 : Nat) / 2) * iteratedDeriv 2 g 0)|
          =
        |φ (a + b) - φ a - b * deriv φ a - (b ^ (2 : Nat) / 2) * iteratedDeriv 2 φ a| := by
      congr 1
      simp [g, hg1, hg2]
    calc
      |φ (a + b) - φ a - b * deriv φ a - (b ^ (2 : Nat) / 2) * iteratedDeriv 2 φ a|
        = |g (0 + -b) - g 0 - (-b) * deriv g 0 - (((-b) ^ (2 : Nat) / 2) * iteratedDeriv 2 g 0)| := by
            rw [hleft]
      _ ≤ M * |-b| ^ (3 : Nat) / 6 := hpos
      _ = M * |b| ^ (3 : Nat) / 6 := by simp

private lemma third_order_taylor_abs_le_cubic_polynomial
    (φ : ℝ → ℝ) (t M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    |φ t|
      ≤
    |φ 0|
      + |deriv φ 0| * |t|
      + (|iteratedDeriv 2 φ 0| / 2) * |t| ^ (2 : Nat)
      + M * |t| ^ (3 : Nat) / 6 := by
  have hrem :=
    third_order_taylor_remainder_abs_le φ 0 t M hM_nonneg hφ hφ3
  have hmain :
      |φ t - φ 0 - t * deriv φ 0 - (t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0|
        ≤ M * |t| ^ (3 : Nat) / 6 := by
    simpa using hrem
  have habs :
      |φ t|
        ≤
      |φ t - φ 0 - t * deriv φ 0 - (t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0|
        + |φ 0|
        + |t * deriv φ 0|
        + |(t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0| := by
    calc
      |φ t|
        =
      |(φ t - φ 0 - t * deriv φ 0 - (t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0)
        + φ 0 + t * deriv φ 0 + (t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0| := by
            congr 1
            ring
      _ ≤
        |φ t - φ 0 - t * deriv φ 0 - (t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0|
          + |φ 0 + t * deriv φ 0 + (t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0| := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using (norm_add_le
              (φ t - φ 0 - t * deriv φ 0 - (t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0)
              (φ 0 + t * deriv φ 0 + (t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0))
      _ ≤
        |φ t - φ 0 - t * deriv φ 0 - (t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0|
          + (|φ 0| + |t * deriv φ 0 + (t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0|) := by
            gcongr
            simpa [add_assoc] using
              (norm_add_le (φ 0) (t * deriv φ 0 + (t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0))
      _ ≤
        |φ t - φ 0 - t * deriv φ 0 - (t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0|
          + (|φ 0| + (|t * deriv φ 0| + |(t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0|)) := by
            have hquad_nonneg : 0 ≤ t ^ (2 : Nat) / 2 := by positivity
            gcongr
            simpa [abs_mul, abs_of_nonneg hquad_nonneg] using
              (norm_add_le (t * deriv φ 0) ((t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0))
      _ =
        |φ t - φ 0 - t * deriv φ 0 - (t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0|
          + |φ 0|
          + |t * deriv φ 0|
          + |(t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0| := by
            ring
  calc
    |φ t|
      ≤
    |φ t - φ 0 - t * deriv φ 0 - (t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0|
      + |φ 0|
      + |t * deriv φ 0|
      + |(t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0| := habs
    _ ≤
      M * |t| ^ (3 : Nat) / 6
      + |φ 0|
      + |t * deriv φ 0|
      + |(t ^ (2 : Nat) / 2) * iteratedDeriv 2 φ 0| := by
        gcongr
    _ =
      |φ 0|
        + |deriv φ 0| * |t|
        + (|iteratedDeriv 2 φ 0| / 2) * |t| ^ (2 : Nat)
        + M * |t| ^ (3 : Nat) / 6 := by
          rw [abs_mul, abs_mul]
          rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by positivity), abs_pow]
          ring_nf

private lemma third_order_taylor_abs_le_const_one_add_abs_cube
    (φ : ℝ → ℝ) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |φ t| ≤ C * (1 + |t| ^ (3 : Nat)) := by
  let C :=
    |φ 0| + |deriv φ 0| + |iteratedDeriv 2 φ 0| / 2 + M / 6
  refine ⟨C, by positivity, ?_⟩
  intro t
  have hpoly :=
    third_order_taylor_abs_le_cubic_polynomial φ t M hM_nonneg hφ hφ3
  have ht1 : |t| ≤ 1 + |t| ^ (3 : Nat) := by
    by_cases ht : |t| ≤ 1
    · linarith [pow_nonneg (abs_nonneg t) 3]
    · have hsq : |t| ^ (2 : Nat) ≥ 1 := by
        have ht' : 1 < |t| := lt_of_not_ge ht
        nlinarith [sq_nonneg (|t|), ht']
      have hcube_ge : |t| ^ (3 : Nat) ≥ |t| := by
        have hone : 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
        calc
          |t| = |t| * 1 := by ring
          _ ≤ |t| * (|t| ^ (2 : Nat)) := by
                gcongr
          _ = |t| ^ (3 : Nat) := by ring
      linarith
  have ht2 : |t| ^ (2 : Nat) ≤ 1 + |t| ^ (3 : Nat) := by
    by_cases ht : |t| ≤ 1
    · nlinarith [pow_nonneg (abs_nonneg t) 3]
    · have hcube_ge : |t| ^ (3 : Nat) ≥ |t| ^ (2 : Nat) := by
        have hone : 1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
        calc
          |t| ^ (2 : Nat) = |t| ^ (2 : Nat) * 1 := by ring
          _ ≤ |t| ^ (2 : Nat) * |t| := by
                gcongr
          _ = |t| ^ (3 : Nat) := by ring
      linarith
  have hconst0 : |φ 0| ≤ |φ 0| * (1 + |t| ^ (3 : Nat)) := by
    have hfac : 1 ≤ 1 + |t| ^ (3 : Nat) := by
      nlinarith [pow_nonneg (abs_nonneg t) 3]
    nlinarith [abs_nonneg (φ 0)]
  have hconst1 : |deriv φ 0| * |t| ≤ |deriv φ 0| * (1 + |t| ^ (3 : Nat)) := by
    gcongr
  have hconst2 :
      (|iteratedDeriv 2 φ 0| / 2) * |t| ^ (2 : Nat)
        ≤ (|iteratedDeriv 2 φ 0| / 2) * (1 + |t| ^ (3 : Nat)) := by
    have hcoef_nonneg : 0 ≤ |iteratedDeriv 2 φ 0| / 2 := by positivity
    gcongr
  have hconst3 :
      M * |t| ^ (3 : Nat) / 6 ≤ (M / 6) * (1 + |t| ^ (3 : Nat)) := by
    have hfac : |t| ^ (3 : Nat) ≤ 1 + |t| ^ (3 : Nat) := by
      nlinarith [pow_nonneg (abs_nonneg t) 3]
    calc
      M * |t| ^ (3 : Nat) / 6 = (M / 6) * |t| ^ (3 : Nat) := by ring
      _ ≤ (M / 6) * (1 + |t| ^ (3 : Nat)) := by gcongr
  calc
    |φ t|
      ≤
    |φ 0|
      + |deriv φ 0| * |t|
      + (|iteratedDeriv 2 φ 0| / 2) * |t| ^ (2 : Nat)
      + M * |t| ^ (3 : Nat) / 6 := hpoly
    _ ≤
      |φ 0| * (1 + |t| ^ (3 : Nat))
        + |deriv φ 0| * (1 + |t| ^ (3 : Nat))
        + (|iteratedDeriv 2 φ 0| / 2) * (1 + |t| ^ (3 : Nat))
        + (M / 6) * (1 + |t| ^ (3 : Nat)) := by
          gcongr
    _ = C * (1 + |t| ^ (3 : Nat)) := by
          simp [C]
          ring

private lemma abs_phi_le_const_one_add_abs_cube
    (φ : ℝ → ℝ) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |φ t| ≤ C * (1 + |t| ^ (3 : Nat)) := by
  simpa using third_order_taylor_abs_le_const_one_add_abs_cube φ M hM_nonneg hφ hφ3

private lemma abs_sub_zero_le_sum_range_abs_sub
    (H : ℕ → ℝ) :
    ∀ N : ℕ, |H N - H 0| ≤ Finset.sum (Finset.range N) (fun i => |H (i + 1) - H i|) := by
  intro N
  induction N with
  | zero =>
      simp
  | succ N ih =>
      have hsplit : H (N + 1) - H 0 = (H (N + 1) - H N) + (H N - H 0) := by
        ring
      calc
        |H (N + 1) - H 0| = |(H (N + 1) - H N) + (H N - H 0)| := by
          rw [hsplit]
        _ ≤ |H (N + 1) - H N| + |H N - H 0| := by
          exact abs_add_le _ _
        _ ≤ |H (N + 1) - H N| + Finset.sum (Finset.range N) (fun i => |H (i + 1) - H i|) := by
          gcongr
        _ = Finset.sum (Finset.range (N + 1)) (fun i => |H (i + 1) - H i|) := by
          rw [Finset.sum_range_succ]
          ring

private lemma integrable_one_dim_phi_affine_gaussianWeight_C3
    (φ : ℝ → ℝ) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M)
    (U V : ℝ) :
    MeasureTheory.Integrable
      (fun z : ℝ => φ (U + z * V) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
  obtain ⟨C, hC_nonneg, hC⟩ := abs_phi_le_const_one_add_abs_cube φ M hM_nonneg hφ hφ3
  let A : ℝ := C * (1 + 4 * |U| ^ (3 : Nat))
  let B : ℝ := 4 * C * |V| ^ (3 : Nat)
  have hA_int :
      MeasureTheory.Integrable
        (fun z : ℝ => A * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    simpa [A, mul_assoc] using integrable_one_dim_gaussianWeight.const_mul A
  have hB_int :
      MeasureTheory.Integrable
        (fun z : ℝ => B * |z| ^ (3 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using
      integrable_one_dim_abs_cube_gaussianWeight.const_mul B
  have hdom_int :
      MeasureTheory.Integrable
        (fun z : ℝ => (A + B * |z| ^ (3 : Nat)) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    have hadd := hA_int.add hB_int
    simpa [A, B, add_mul, mul_assoc, mul_left_comm, mul_comm] using hadd
  refine hdom_int.mono' ?_ ?_
  · have hcont :
        Continuous (fun z : ℝ => φ (U + z * V) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
      exact (hφ.continuous.comp (by fun_prop :
        Continuous (fun z : ℝ => U + z * V))).mul
          (by fun_prop : Continuous (fun z : ℝ => Real.exp (-(z ^ (2 : Nat)) / 2)))
    simpa using hcont.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun z => by
      have hphi :
          |φ (U + z * V)| ≤ C * (1 + |U + z * V| ^ (3 : Nat)) := hC (U + z * V)
      have hcubic :
          |U + z * V| ^ (3 : Nat)
            ≤ 4 * (|U| ^ (3 : Nat) + |z| ^ (3 : Nat) * |V| ^ (3 : Nat)) := by
        exact abs_add_mul_pow_three_le_four U z V
      have hexp_nonneg : 0 ≤ Real.exp (-(z ^ (2 : Nat)) / 2) := Real.exp_nonneg _
      have hbound :
          |φ (U + z * V)| ≤ A + B * |z| ^ (3 : Nat) := by
        calc
          |φ (U + z * V)| ≤ C * (1 + |U + z * V| ^ (3 : Nat)) := hphi
          _ ≤ C * (1 + 4 * (|U| ^ (3 : Nat) + |z| ^ (3 : Nat) * |V| ^ (3 : Nat))) := by
                gcongr
          _ = A + B * |z| ^ (3 : Nat) := by
                simp [A, B]
                ring
      calc
        |φ (U + z * V) * Real.exp (-(z ^ (2 : Nat)) / 2)|
            = |φ (U + z * V)| * Real.exp (-(z ^ (2 : Nat)) / 2) := by
                rw [abs_mul, abs_of_nonneg hexp_nonneg]
        _ ≤ (A + B * |z| ^ (3 : Nat)) * Real.exp (-(z ^ (2 : Nat)) / 2) := by
              exact mul_le_mul_of_nonneg_right hbound hexp_nonneg)

private def hybridQuadraticFormAvg
    (n m : ℕ) (f : Fin (n + m) → Fin (n + m) → ℝ) (φ : ℝ → ℝ) : ℝ :=
  hybridAvg n m (fun y => φ (Q2Gauss (n + m) f y))

private lemma hybridQuadraticFormAvg_all_sign
    (n : ℕ) (f : Fin n → Fin n → ℝ) (φ : ℝ → ℝ) :
    hybridQuadraticFormAvg n 0 f φ = avgSigns n (fun σ => φ (Q2Signs n f σ)) := by
  unfold hybridQuadraticFormAvg
  simpa using hybridAvg_q2_all_sign n f φ

private lemma hybridQuadraticFormAvg_all_gaussian
    (n : ℕ) (f : Fin n → Fin n → ℝ) (φ : ℝ → ℝ) :
    hybridQuadraticFormAvg 0 n
      (fun i j : Fin (0 + n) => f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
      = stdGaussianAvg n (fun x => φ (Q2Gauss n f x)) := by
  calc
    hybridQuadraticFormAvg 0 n
      (fun i j : Fin (0 + n) => f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
      =
    stdGaussianAvg n
      (fun x : Fin n → ℝ =>
        φ
          (Q2Gauss (0 + n)
            (fun i j : Fin (0 + n) => f (Fin.cast (by omega) i) (Fin.cast (by omega) j))
            (fun i : Fin (0 + n) => x (Fin.cast (by omega) i)))) := by
          unfold hybridQuadraticFormAvg
          simpa using
            (hybridAvg_all_gaussian n
              (fun x : Fin n → ℝ =>
                φ
                  (Q2Gauss (0 + n)
                    (fun i j : Fin (0 + n) => f (Fin.cast (by omega) i) (Fin.cast (by omega) j))
                    (fun i : Fin (0 + n) => x (Fin.cast (by omega) i)))))
    _ = stdGaussianAvg n (fun x => φ (Q2Gauss n f x)) := by
          congr 1 with x
          congr 1
          simpa using
            (Q2Gauss_castKernel_eq (h := by omega) f (fun i : Fin (0 + n) => x (Fin.cast (by omega) i)))

private lemma boundary_sign_taylor_step
    (φ : ℝ → ℝ) (U V M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    |(((φ (U - V) + φ (U + V)) / 2 : ℝ)
        - (φ U + (V ^ (2 : Nat) / 2) * iteratedDeriv 2 φ U))|
      ≤ M * |V| ^ (3 : Nat) / 6 := by
  let A : ℝ :=
    φ (U - V) - φ U + V * deriv φ U - (V ^ (2 : Nat) / 2) * iteratedDeriv 2 φ U
  let B : ℝ :=
    φ (U + V) - φ U - V * deriv φ U - (V ^ (2 : Nat) / 2) * iteratedDeriv 2 φ U
  have hminus :
      |A| ≤ M * |V| ^ (3 : Nat) / 6 := by
    dsimp [A]
    simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
      (third_order_taylor_remainder_abs_le φ U (-V) M hM_nonneg hφ hφ3)
  have hplus :
      |B| ≤ M * |V| ^ (3 : Nat) / 6 := by
    dsimp [B]
    simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using
      (third_order_taylor_remainder_abs_le φ U V M hM_nonneg hφ hφ3)
  have hrew :
      (((φ (U - V) + φ (U + V)) / 2 : ℝ)
          - (φ U + (V ^ (2 : Nat) / 2) * iteratedDeriv 2 φ U))
        = (A + B) / 2 := by
    dsimp [A, B]
    ring
  have hAB :
      |A + B| ≤ |A| + |B| := by
    simpa using (norm_add_le A B)
  calc
    |(((φ (U - V) + φ (U + V)) / 2 : ℝ)
        - (φ U + (V ^ (2 : Nat) / 2) * iteratedDeriv 2 φ U))|
      = |(A + B) / 2| := by rw [hrew]
    _ = |A + B| / 2 := by
          rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by positivity)]
    _ ≤ (|A| + |B|) / 2 := by
          gcongr
    _ ≤ (M * |V| ^ (3 : Nat) / 6 + M * |V| ^ (3 : Nat) / 6) / 2 := by
          gcongr
    _ = M * |V| ^ (3 : Nat) / 6 := by ring

private lemma boundary_gaussian_taylor_step
    (φ : ℝ → ℝ) (U V M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    |stdGaussianAvg1 (fun z : ℝ => φ (U + z * V))
        - (φ U + (V ^ (2 : Nat) / 2) * iteratedDeriv 2 φ U)|
      ≤ (4 / Real.sqrt (2 * Real.pi)) * (M * |V| ^ (3 : Nat) / 6) := by
  let c : ℝ := M * |V| ^ (3 : Nat) / 6
  let a : ℝ := V * deriv φ U
  let b : ℝ := (V ^ (2 : Nat) / 2) * iteratedDeriv 2 φ U
  let P : ℝ → ℝ := fun z => φ U + a * z + b * z ^ (2 : Nat)
  let R : ℝ → ℝ := fun z => φ (U + z * V) - P z
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    positivity
  have hR_bound :
      ∀ z : ℝ, |R z| ≤ c * |z| ^ (3 : Nat) := by
    intro z
    have hz :=
      third_order_taylor_remainder_abs_le φ U (z * V) M hM_nonneg hφ hφ3
    have hR_eq :
        R z
          = φ (U + z * V) - φ U - (z * V) * deriv φ U
              - (((z * V) ^ (2 : Nat)) / 2) * iteratedDeriv 2 φ U := by
      dsimp [R, P, a, b]
      ring
    have hz' : |R z| ≤ M * |z * V| ^ (3 : Nat) / 6 := by
      rw [hR_eq]
      simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using hz
    calc
      |R z| ≤ M * |z * V| ^ (3 : Nat) / 6 := hz'
      _ = c * |z| ^ (3 : Nat) := by
            dsimp [c]
            rw [abs_mul]
            ring
  have hg_int :
      MeasureTheory.Integrable
        (fun z : ℝ => (c * |z| ^ (3 : Nat)) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    simpa [c, mul_assoc, mul_left_comm, mul_comm] using
      (integrable_one_dim_abs_cube_gaussianWeight.const_mul c)
  have hφcont : Continuous φ := hφ.continuous
  have hP_cont : Continuous P := by
    dsimp [P, a, b]
    fun_prop
  have hR_cont : Continuous R := by
    have hleft : Continuous (fun z : ℝ => φ (U + z * V)) :=
      hφcont.comp (by fun_prop : Continuous (fun z : ℝ => U + z * V))
    dsimp [R]
    exact hleft.sub hP_cont
  have hR_int :
      MeasureTheory.Integrable
        (fun z : ℝ => R z * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    refine hg_int.mono' ?_ ?_
    · simpa using
        (hR_cont.mul (by fun_prop :
          Continuous (fun z : ℝ => Real.exp (-(z ^ (2 : Nat)) / 2)))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun z => by
        have hbound := hR_bound z
        have hweight_nonneg : 0 ≤ Real.exp (-(z ^ (2 : Nat)) / 2) := Real.exp_nonneg _
        calc
          |R z * Real.exp (-(z ^ (2 : Nat)) / 2)|
              = |R z| * Real.exp (-(z ^ (2 : Nat)) / 2) := by
                  rw [abs_mul, abs_of_nonneg hweight_nonneg]
          _ ≤ (c * |z| ^ (3 : Nat)) * Real.exp (-(z ^ (2 : Nat)) / 2) := by
                gcongr
          _ = c * |z| ^ (3 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2) := by ring)
  have hconst_int :
      MeasureTheory.Integrable
        (fun z : ℝ => φ U * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    simpa [mul_assoc] using integrable_one_dim_gaussianWeight.const_mul (φ U)
  have hlin_int :
      MeasureTheory.Integrable
        (fun z : ℝ => (a * z) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    simpa [a, mul_assoc, mul_left_comm, mul_comm] using
      integrable_one_dim_linear_gaussianWeight.const_mul a
  have hsq_int :
      MeasureTheory.Integrable
        (fun z : ℝ => (b * z ^ (2 : Nat)) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    simpa [b, mul_assoc, mul_left_comm, mul_comm] using
      integrable_one_dim_sq_gaussianWeight.const_mul b
  have hlinsq_int :
      MeasureTheory.Integrable
        (fun z : ℝ => (a * z + b * z ^ (2 : Nat)) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    refine (hlin_int.add hsq_int).congr ?_
    exact Filter.Eventually.of_forall (fun z => by
      change
        a * z * Real.exp (-(z ^ (2 : Nat)) / 2)
          + b * z ^ (2 : Nat) * Real.exp (-(z ^ (2 : Nat)) / 2)
          =
        (a * z + b * z ^ (2 : Nat)) * Real.exp (-(z ^ (2 : Nat)) / 2)
      ring)
  have hP_int :
      MeasureTheory.Integrable
        (fun z : ℝ => P z * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    refine (hconst_int.add hlinsq_int).congr ?_
    exact Filter.Eventually.of_forall (fun z => by
      dsimp [P]
      ring)
  have hphi_int :
      MeasureTheory.Integrable
        (fun z : ℝ => φ (U + z * V) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    refine (hR_int.add hP_int).congr ?_
    exact Filter.Eventually.of_forall (fun z => by
      dsimp [R, P]
      ring)
  have hP_avg :
      stdGaussianAvg1 P
        = φ U + (V ^ (2 : Nat) / 2) * iteratedDeriv 2 φ U := by
    have hconst_avg : stdGaussianAvg1 (fun _ : ℝ => φ U) = φ U := by
      calc
        stdGaussianAvg1 (fun _ : ℝ => φ U)
            = φ U * stdGaussianAvg1 (fun _ : ℝ => (1 : ℝ)) := by
                simpa using stdGaussianAvg1_mul_const (φ U) (fun _ : ℝ => (1 : ℝ))
        _ = φ U := by simp [stdGaussianAvg1_mass]
    have hlin_avg : stdGaussianAvg1 (fun z : ℝ => a * z) = 0 := by
      calc
        stdGaussianAvg1 (fun z : ℝ => a * z) = a * stdGaussianAvg1 (fun z : ℝ => z) := by
          simpa using stdGaussianAvg1_mul_const a (fun z : ℝ => z)
        _ = 0 := by simp [stdGaussianAvg1_id]
    have hsq_avg : stdGaussianAvg1 (fun z : ℝ => b * z ^ (2 : Nat)) = b := by
      calc
        stdGaussianAvg1 (fun z : ℝ => b * z ^ (2 : Nat))
            = b * stdGaussianAvg1 (fun z : ℝ => z ^ (2 : Nat)) := by
                simpa using stdGaussianAvg1_mul_const b (fun z : ℝ => z ^ (2 : Nat))
        _ = b := by simp [stdGaussianAvg1_sq]
    have hP_split : P = (fun z : ℝ => φ U + (a * z + b * z ^ (2 : Nat))) := by
      funext z
      dsimp [P]
      ring
    calc
      stdGaussianAvg1 P
        = stdGaussianAvg1 (fun _ : ℝ => φ U)
            + stdGaussianAvg1 (fun z : ℝ => a * z + b * z ^ (2 : Nat)) := by
              rw [hP_split]
              rw [stdGaussianAvg1_add (fun _ : ℝ => φ U) (fun z : ℝ => a * z + b * z ^ (2 : Nat))
                hconst_int hlinsq_int]
      _ = stdGaussianAvg1 (fun _ : ℝ => φ U)
            + (stdGaussianAvg1 (fun z : ℝ => a * z) + stdGaussianAvg1 (fun z : ℝ => b * z ^ (2 : Nat))) := by
              rw [stdGaussianAvg1_add (fun z : ℝ => a * z) (fun z : ℝ => b * z ^ (2 : Nat))
                hlin_int hsq_int]
      _ = φ U + (V ^ (2 : Nat) / 2) * iteratedDeriv 2 φ U := by
              simp [hconst_avg, hlin_avg, hsq_avg, b]
  have hsub :
      stdGaussianAvg1 R
        = stdGaussianAvg1 (fun z : ℝ => φ (U + z * V)) - stdGaussianAvg1 P := by
    simpa [R] using stdGaussianAvg1_sub (fun z : ℝ => φ (U + z * V)) P hphi_int hP_int
  have hR_avg :
      |stdGaussianAvg1 R| ≤ stdGaussianAvg1 (fun z : ℝ => c * |z| ^ (3 : Nat)) := by
    refine abs_stdGaussianAvg1_le_of_abs_le (fun z => by positivity) hg_int ?_
    intro z
    exact hR_bound z
  calc
    |stdGaussianAvg1 (fun z : ℝ => φ (U + z * V))
        - (φ U + (V ^ (2 : Nat) / 2) * iteratedDeriv 2 φ U)|
      = |stdGaussianAvg1 R| := by rw [hsub, hP_avg]
    _ ≤ stdGaussianAvg1 (fun z : ℝ => c * |z| ^ (3 : Nat)) := hR_avg
    _ = c * stdGaussianAvg1 (fun z : ℝ => |z| ^ (3 : Nat)) := by
          rw [stdGaussianAvg1_mul_const]
    _ = c * (4 / Real.sqrt (2 * Real.pi)) := by
          rw [stdGaussianAvg1_abs_cube_eq]
    _ = (4 / Real.sqrt (2 * Real.pi)) * (M * |V| ^ (3 : Nat) / 6) := by
          dsimp [c]
          ring

private lemma boundary_one_step_taylor_pointwise
    (φ : ℝ → ℝ) (U V M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    |(((φ (U - V) + φ (U + V)) / 2 : ℝ)
        - stdGaussianAvg1 (fun z : ℝ => φ (U + z * V)))|
      ≤ ((1 + 4 / Real.sqrt (2 * Real.pi)) / 6 : ℝ) * M * |V| ^ (3 : Nat) := by
  let A : ℝ := ((φ (U - V) + φ (U + V)) / 2 : ℝ)
  let B : ℝ := stdGaussianAvg1 (fun z : ℝ => φ (U + z * V))
  let C : ℝ := φ U + (V ^ (2 : Nat) / 2) * iteratedDeriv 2 φ U
  have hsign :=
    boundary_sign_taylor_step φ U V M hM_nonneg hφ hφ3
  have hgauss :=
    boundary_gaussian_taylor_step φ U V M hM_nonneg hφ hφ3
  have htri :
      |A - B| ≤ |A - C| + |C - B| := by
    simpa [A, B, C, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (abs_sub_le A C B)
  have hgauss' :
      |C - B| ≤ (4 / Real.sqrt (2 * Real.pi)) * (M * |V| ^ (3 : Nat) / 6) := by
    simpa [B, C, abs_sub_comm] using hgauss
  calc
    |(((φ (U - V) + φ (U + V)) / 2 : ℝ)
        - stdGaussianAvg1 (fun z : ℝ => φ (U + z * V)))|
      = |A - B| := by rfl
    _ ≤ |A - C| + |C - B| := htri
    _ ≤ M * |V| ^ (3 : Nat) / 6
          + (4 / Real.sqrt (2 * Real.pi)) * (M * |V| ^ (3 : Nat) / 6) := by
            nlinarith [hsign, hgauss']
    _ = ((1 + 4 / Real.sqrt (2 * Real.pi)) / 6 : ℝ) * M * |V| ^ (3 : Nat) := by
          ring

private lemma hybridQuadraticFormAvg_succ_eq_boundary_sign_avg
    (n m : ℕ) (lam : Fin (n + m + 1) → Fin (n + m + 1) → ℝ) (φ : ℝ → ℝ) :
    hybridQuadraticFormAvg (n + 1) m
      (fun i j : Fin ((n + 1) + m) =>
        lam (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
      =
    stdGaussianAvg m
      (fun x =>
        avgSigns n
          (fun σ =>
            (((∑ b : Fin 2,
                φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x))) / 2 : ℝ)))) := by
  unfold hybridQuadraticFormAvg hybridAvg
  congr 1 with x
  rw [avgSigns_split_last]
  congr 1 with σ
  have hQ (b : Fin 2) :
      Q2Gauss ((n + 1) + m)
          (fun i j : Fin ((n + 1) + m) =>
            lam (Fin.cast (by omega) i) (Fin.cast (by omega) j))
          (hybridPoint (n + 1) m (Fin.snoc σ b) x)
        =
      Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x) := by
        let e : Fin ((n + 1) + m) ≃ Fin (n + m + 1) := finCongr (by omega)
        let v : Fin ((n + 1) + m) → ℝ := hybridPoint (n + 1) m (Fin.snoc σ b) x
        have hv : ∀ i : Fin (n + m + 1), boundarySignHybridPoint n m σ b x i = v (e.symm i) := by
          intro i
          simp [boundarySignHybridPoint, v, e]
        unfold Q2Gauss
        change
          (∑ i : Fin ((n + 1) + m),
            ∑ j : Fin ((n + 1) + m), lam (e i) (e j) * v i * v j)
            =
          (∑ i : Fin (n + m + 1),
            ∑ j : Fin (n + m + 1),
              lam i j
                * boundarySignHybridPoint n m σ b x i
                * boundarySignHybridPoint n m σ b x j)
        calc
          ∑ i : Fin ((n + 1) + m),
              ∑ j : Fin ((n + 1) + m), lam (e i) (e j) * v i * v j
              =
              ∑ i : Fin (n + m + 1),
                ∑ j : Fin ((n + 1) + m), lam i (e j) * v (e.symm i) * v j := by
                  exact Fintype.sum_equiv e
                    (fun i : Fin ((n + 1) + m) =>
                      ∑ j : Fin ((n + 1) + m), lam (e i) (e j) * v i * v j)
                    (fun i : Fin (n + m + 1) =>
                      ∑ j : Fin ((n + 1) + m), lam i (e j) * v (e.symm i) * v j)
                    (by intro i; simp [e, v])
          _ =
              ∑ i : Fin (n + m + 1),
                ∑ j : Fin (n + m + 1), lam i j * v (e.symm i) * v (e.symm j) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  exact Fintype.sum_equiv e
                    (fun j : Fin ((n + 1) + m) => lam i (e j) * v (e.symm i) * v j)
                    (fun j : Fin (n + m + 1) => lam i j * v (e.symm i) * v (e.symm j))
                    (by intro j; simp [e, v])
          _ =
              ∑ i : Fin (n + m + 1),
                ∑ j : Fin (n + m + 1),
                  lam i j
                    * boundarySignHybridPoint n m σ b x i
                    * boundarySignHybridPoint n m σ b x j := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  rw [hv i, hv j]
  rw [Fin.sum_univ_two]
  simp [hQ]

private lemma integrable_boundary_sign_avgSigns_gaussianWeight_C3
    (n m : ℕ) (lam : Fin (n + m + 1) → Fin (n + m + 1) → ℝ)
    (hsymm : ∀ i j, lam i j = lam j i) (hdiag : ∀ i, lam i i = 0)
    (φ : ℝ → ℝ) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ =>
        avgSigns n
          (fun σ =>
            (((∑ b : Fin 2,
                φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x))) / 2 : ℝ)))
          * gaussianWeight m x) := by
  obtain ⟨C, hC_nonneg, hC⟩ := abs_phi_le_const_one_add_abs_cube φ M hM_nonneg hφ hφ3
  let A : (Fin m → ℝ) → ℝ :=
    fun x =>
      avgSigns n
        (fun σ =>
          (((∑ b : Fin 2,
              φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x))) / 2 : ℝ)))
  let S : (Fin m → ℝ) → ℝ :=
    fun x =>
      avgSigns n
        (fun σ =>
          (((∑ b : Fin 2,
              |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)) / 2 : ℝ)))
  have hterm_cont (σ : Fin n → Fin 2) (b : Fin 2) :
      Continuous
        (fun x : Fin m → ℝ =>
          φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x))) := by
    have hQ_cont :
        Continuous
          (fun x : Fin m → ℝ =>
            Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)) := by
      have hcontBS :
          Continuous (fun x : Fin m → ℝ => boundarySignHybridPoint n m σ b x) := by
        have hcast :
            Continuous
              (fun y : Fin ((n + 1) + m) → ℝ =>
                fun j : Fin (n + m + 1) => y (Fin.cast (by omega) j)) := by
          rw [continuous_pi_iff]
          intro j
          exact continuous_apply (Fin.cast (by omega) j)
        simpa [boundarySignHybridPoint] using
          hcast.comp (continuous_hybridPoint (n + 1) m (Fin.snoc σ b))
      exact (continuous_Q2Gauss (n + m + 1) lam).comp hcontBS
    exact hφ.continuous.comp hQ_cont
  have hA_cont : Continuous A := by
    have hsum_cont (σ : Fin n → Fin 2) :
        Continuous
          (fun x : Fin m → ℝ =>
            ∑ b : Fin 2, φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x))) := by
      exact continuous_finset_sum _ (fun b _ => hterm_cont σ b)
    have hterm_cont' (σ : Fin n → Fin 2) :
        Continuous
          (fun x : Fin m → ℝ =>
            (((∑ b : Fin 2,
                φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x))) / 2 : ℝ))) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (continuous_const.mul (hsum_cont σ))
    have hsum :
        Continuous
          (fun x : Fin m → ℝ =>
            ∑ σ : Fin n → Fin 2,
              (((∑ b : Fin 2,
                  φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x))) / 2 : ℝ))) := by
      exact continuous_finset_sum _ (fun σ _ => hterm_cont' σ)
    unfold A avgSigns
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (continuous_const.mul hsum)
  have hcube_int :
      MeasureTheory.Integrable (fun x : Fin m → ℝ => S x * gaussianWeight m x) := by
    simpa [S] using
      integrable_boundary_sign_q2_cube_avgSigns_gaussianWeight n m lam hsymm hdiag
  have hconst_int :
      MeasureTheory.Integrable (fun x : Fin m → ℝ => C * gaussianWeight m x) := by
    simpa [mul_assoc] using (integrable_stdGaussianDensity m).const_mul C
  have hcube_scaled :
      MeasureTheory.Integrable (fun x : Fin m → ℝ => (C * S x) * gaussianWeight m x) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcube_int.const_mul C
  have hdom_int :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ => (C * (1 + S x)) * gaussianWeight m x) := by
    have hadd := hconst_int.add hcube_scaled
    have hdom_int' :
        MeasureTheory.Integrable (fun x : Fin m → ℝ => (C + C * S x) * gaussianWeight m x) := by
      refine hadd.congr ?_
      exact Filter.Eventually.of_forall (fun x => by
        change C * gaussianWeight m x + C * S x * gaussianWeight m x = (C + C * S x) * gaussianWeight m x
        ring)
    refine hdom_int'.congr ?_
    exact Filter.Eventually.of_forall (fun x => by ring)
  refine hdom_int.mono' ?_ ?_
  · change MeasureTheory.AEStronglyMeasurable (fun x : Fin m → ℝ => A x * gaussianWeight m x)
    simpa [A] using (hA_cont.mul (continuous_gaussianWeight m)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun x => by
      have hAx :
          |A x| ≤ C * (1 + S x) := by
        calc
          |A x|
              ≤
            avgSigns n
              (fun σ =>
                |(((∑ b : Fin 2,
                    φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x))) / 2 : ℝ))|) := by
                  exact abs_avgSigns_le_avgSigns_abs n _
          _ ≤ avgSigns n (fun σ => C * (1 + (((∑ b : Fin 2,
                  |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)) / 2 : ℝ)))) := by
                refine avgSigns_mono n ?_
                intro σ
                rw [Fin.sum_univ_two, abs_div]
                rw [Fin.sum_univ_two]
                have h0 := hC (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 0 x))
                have h1 := hC (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 1 x))
                have habs :
                    |φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 0 x))
                        + φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 1 x))|
                      ≤
                    |φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 0 x))|
                      + |φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 1 x))| := by
                  simpa using
                    (norm_add_le
                      (φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 0 x)))
                      (φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 1 x))))
                have hsum :
                    |φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 0 x))|
                      + |φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 1 x))|
                      ≤
                    C * (1 + |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 0 x)| ^ (3 : Nat))
                      + C * (1 + |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 1 x)| ^ (3 : Nat)) := by
                  exact add_le_add h0 h1
                have hdiv :
                    |φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 0 x))
                        + φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 1 x))| / 2
                      ≤
                    (C * (1 + |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 0 x)| ^ (3 : Nat))
                      + C * (1 + |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 1 x)| ^ (3 : Nat))) / 2 := by
                  exact div_le_div_of_nonneg_right (le_trans habs hsum) (by norm_num)
                calc
                  |φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 0 x))
                      + φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 1 x))| / |(2 : ℝ)|
                      =
                    |φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 0 x))
                        + φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 1 x))| / 2 := by
                        norm_num
                  _ 
                      ≤
                    (C * (1 + |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 0 x)| ^ (3 : Nat))
                      + C * (1 + |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 1 x)| ^ (3 : Nat))) / 2 := hdiv
                  _ = C * (1 + ((|Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 0 x)| ^ (3 : Nat)
                      + |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ 1 x)| ^ (3 : Nat)) / 2 : ℝ)) := by
                      ring
          _ = C * (1 + S x) := by
                have hfun :
                    (fun σ : Fin n → Fin 2 =>
                      C * (1 + (((∑ b : Fin 2,
                          |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)) / 2 : ℝ))))
                      =
                    (fun σ : Fin n → Fin 2 =>
                      C + C * (((∑ b : Fin 2,
                          |Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x)| ^ (3 : Nat)) / 2 : ℝ))) := by
                  funext σ
                  ring
                rw [hfun, avgSigns_add, avgSigns_const, avgSigns_mul_const_left]
                unfold S
                ring_nf
      have hgw_nonneg : 0 ≤ gaussianWeight m x := gaussianWeight_nonneg m x
      calc
        |A x * gaussianWeight m x|
            = |A x| * gaussianWeight m x := by
                rw [abs_mul, abs_of_nonneg hgw_nonneg]
        _ ≤ (C * (1 + S x)) * gaussianWeight m x := by
              exact mul_le_mul_of_nonneg_right hAx hgw_nonneg)

private lemma integrable_boundary_gaussian_avgSigns_gaussianWeight_C3
    (n m : ℕ) (lam : Fin (n + m + 1) → Fin (n + m + 1) → ℝ)
    (hsymm : ∀ i j, lam i j = lam j i) (hdiag : ∀ i, lam i i = 0)
    (φ : ℝ → ℝ) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    MeasureTheory.Integrable
      (fun x : Fin m → ℝ =>
        avgSigns n
          (fun σ =>
            stdGaussianAvg1
              (fun z : ℝ =>
                φ (Q2Gauss (n + m + 1) lam (hybridPoint n (m + 1) σ (Fin.cons z x)))))
          * gaussianWeight m x) := by
  obtain ⟨C, hC_nonneg, hC⟩ := abs_phi_le_const_one_add_abs_cube φ M hM_nonneg hφ hφ3
  let fCast : Fin (n + (m + 1)) → Fin (n + (m + 1)) → ℝ :=
    fun i j => lam (Fin.cast (by omega) i) (Fin.cast (by omega) j)
  let F : (Fin (m + 1) → ℝ) → ℝ :=
    fun y =>
      avgSigns n (fun σ => φ (Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y)))
  let S : (Fin (m + 1) → ℝ) → ℝ :=
    fun y =>
      avgSigns n (fun σ => |Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y)| ^ (3 : Nat))
  have hfCast_symm : ∀ i j, fCast i j = fCast j i := by
    intro i j
    exact hsymm _ _
  have hfCast_diag : ∀ i, fCast i i = 0 := by
    intro i
    exact hdiag _
  have hterm_cont (σ : Fin n → Fin 2) :
      Continuous
        (fun y : Fin (m + 1) → ℝ =>
          φ (Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y))) := by
    exact hφ.continuous.comp
      ((continuous_Q2Gauss (n + (m + 1)) fCast).comp (continuous_hybridPoint n (m + 1) σ))
  have hF_cont : Continuous F := by
    have hsum_cont :
        Continuous
          (fun y : Fin (m + 1) → ℝ =>
            ∑ σ : Fin n → Fin 2, φ (Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y))) := by
      exact continuous_finset_sum _ (fun σ _ => hterm_cont σ)
    unfold F avgSigns
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (continuous_const.mul hsum_cont)
  have hcube_int :
      MeasureTheory.Integrable (fun y : Fin (m + 1) → ℝ => S y * gaussianWeight (m + 1) y) := by
    simpa [S] using
      integrable_hybrid_q2_cube_avgSigns_gaussianWeight n (m + 1) fCast hfCast_symm hfCast_diag
  have hconst_int :
      MeasureTheory.Integrable (fun y : Fin (m + 1) → ℝ => C * gaussianWeight (m + 1) y) := by
    simpa [mul_assoc] using (integrable_stdGaussianDensity (m + 1)).const_mul C
  have hcube_scaled :
      MeasureTheory.Integrable (fun y : Fin (m + 1) → ℝ => (C * S y) * gaussianWeight (m + 1) y) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcube_int.const_mul C
  have hF_int :
      MeasureTheory.Integrable (fun y : Fin (m + 1) → ℝ => F y * gaussianWeight (m + 1) y) := by
    have hdom_int := hconst_int.add hcube_scaled
    have hdom_int' :
        MeasureTheory.Integrable (fun y : Fin (m + 1) → ℝ => (C + C * S y) * gaussianWeight (m + 1) y) := by
      refine hdom_int.congr ?_
      exact Filter.Eventually.of_forall (fun y => by
        change C * gaussianWeight (m + 1) y + C * S y * gaussianWeight (m + 1) y =
          (C + C * S y) * gaussianWeight (m + 1) y
        ring)
    have hdom_int'' :
        MeasureTheory.Integrable (fun y : Fin (m + 1) → ℝ => (C * (1 + S y)) * gaussianWeight (m + 1) y) := by
      refine hdom_int'.congr ?_
      exact Filter.Eventually.of_forall (fun y => by ring)
    refine hdom_int''.mono' ?_ ?_
    · simpa using (hF_cont.mul (continuous_gaussianWeight (m + 1))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y => by
        have hFy :
            |F y| ≤ C * (1 + S y) := by
          calc
            |F y|
                ≤
              avgSigns n
                (fun σ =>
                  |φ
                    (Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y))|) := by
                    exact abs_avgSigns_le_avgSigns_abs n _
            _ ≤ avgSigns n (fun σ => C * (1 + |Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y)| ^ (3 : Nat))) := by
                  refine avgSigns_mono n ?_
                  intro σ
                  exact hC _
            _ = C * (1 + S y) := by
                  have hfun :
                      (fun σ : Fin n → Fin 2 =>
                        C * (1 + |Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y)| ^ (3 : Nat)))
                        =
                      (fun σ : Fin n → Fin 2 =>
                        C + C * |Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y)| ^ (3 : Nat)) := by
                    funext σ
                    ring
                  rw [hfun, avgSigns_add, avgSigns_const, avgSigns_mul_const_left]
                  unfold S
                  ring_nf
        have hweight_nonneg : 0 ≤ gaussianWeight (m + 1) y := gaussianWeight_nonneg (m + 1) y
        calc
          |F y * gaussianWeight (m + 1) y|
              = |F y| * gaussianWeight (m + 1) y := by
                  rw [abs_mul, abs_of_nonneg hweight_nonneg]
          _ ≤ C * (1 + S y) * gaussianWeight (m + 1) y := by
                exact mul_le_mul_of_nonneg_right hFy hweight_nonneg)
  let e : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  let Gprod : ℝ × (Fin m → ℝ) → ℝ :=
    fun p => F (Fin.cons p.1 p.2) * Real.exp (-(p.1 ^ (2 : Nat)) / 2) * gaussianWeight m p.2
  have hGprod_int : MeasureTheory.Integrable Gprod := by
    let hpres := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have hcomp :
        MeasureTheory.Integrable
          ((fun y : Fin (m + 1) → ℝ => F y * gaussianWeight (m + 1) y) ∘ e.symm) := by
      exact (MeasurePreserving.symm e hpres).integrable_comp_of_integrable hF_int
    refine hcomp.congr ?_
    exact Filter.Eventually.of_forall (fun p => by
      rcases p with ⟨z, x⟩
      have he : e.symm (z, x) = Fin.cons z x := by
        ext i <;> simp [e, MeasurableEquiv.piFinSuccAbove]
      calc
        ((fun y : Fin (m + 1) → ℝ => F y * gaussianWeight (m + 1) y) ∘ e.symm) (z, x)
            = F (Fin.cons z x) * gaussianWeight (m + 1) (Fin.cons z x) := by
              simpa [Function.comp] using congrArg (fun y => F y * gaussianWeight (m + 1) y) he
        _ = F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) * gaussianWeight m x := by
              rw [gaussianWeight_cons]
              ring
        _ = Gprod (z, x) := by
              simp [Gprod])
  have houter_raw :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ => ∫ z : ℝ, Gprod (z, x)) := by
    simpa [Gprod] using hGprod_int.integral_prod_right
  have houter :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ =>
          (∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume)
            * gaussianWeight m x) := by
    refine houter_raw.congr ?_
    exact Filter.Eventually.of_forall (fun x => by
      have hinner :
          ∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) * gaussianWeight m x
            =
          (∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume)
            * gaussianWeight m x := by
          rw [show
              (fun z : ℝ =>
                F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) * gaussianWeight m x)
                =
              (fun z : ℝ =>
                gaussianWeight m x
                  * (F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2))) by
                funext z
                ring]
          rw [MeasureTheory.integral_const_mul]
          ring
      simpa [Gprod] using hinner)
  have hQ (σ : Fin n → Fin 2) (x : Fin m → ℝ) (z : ℝ) :
      Q2Gauss (n + (m + 1))
        (fun i j : Fin (n + (m + 1)) =>
          lam (Fin.cast (by omega) i) (Fin.cast (by omega) j))
        (hybridPoint n (m + 1) σ (Fin.cons z x))
        =
      Q2Gauss (n + m + 1) lam (hybridPoint n (m + 1) σ (Fin.cons z x)) := by
    let y : Fin (n + (m + 1)) → ℝ := hybridPoint n (m + 1) σ (Fin.cons z x)
    have hvec :
        (fun i : Fin (n + m + 1) => y (Fin.cast (by omega) i))
          = hybridPoint n (m + 1) σ (Fin.cons z x) := by
      funext i
      simp [y]
    simpa [y, hvec] using
      (Q2Gauss_castKernel_eq (h := by omega) lam (hybridPoint n (m + 1) σ (Fin.cons z x)))
  have hHz_int (x : Fin m → ℝ) (σ : Fin n → Fin 2) :
      MeasureTheory.Integrable
        (fun z : ℝ =>
          φ (Q2Gauss (n + m + 1) lam (hybridPoint n (m + 1) σ (Fin.cons z x)))
            * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    let U : ℝ :=
      Q2Gauss (n + m) (minorKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)
    let V : ℝ :=
      linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)
    have hrew :
        (fun z : ℝ =>
          φ (Q2Gauss (n + m + 1) lam (hybridPoint n (m + 1) σ (Fin.cons z x)))
            * Real.exp (-(z ^ (2 : Nat)) / 2))
          =
        (fun z : ℝ => φ (U + z * V) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
      funext z
      simp [U, V, Q2Gauss_boundary_gaussian, hsymm, hdiag]
    rw [hrew]
    exact integrable_one_dim_phi_affine_gaussianWeight_C3 φ M hM_nonneg hφ hφ3 U V
  let c0 : ℝ := ((2 * Real.pi) ^ ((1 : ℝ) / 2))⁻¹
  have hfun :
      (fun x : Fin m → ℝ =>
        avgSigns n
          (fun σ =>
            stdGaussianAvg1
              (fun z : ℝ =>
                φ (Q2Gauss (n + m + 1) lam (hybridPoint n (m + 1) σ (Fin.cons z x)))))
          * gaussianWeight m x)
        =
      (fun x : Fin m → ℝ =>
        c0
          * ((∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume)
              * gaussianWeight m x)) := by
    funext x
    let H : (Fin n → Fin 2) → ℝ → ℝ :=
      fun σ z =>
        φ (Q2Gauss (n + m + 1) lam (hybridPoint n (m + 1) σ (Fin.cons z x)))
    have hcomm :
        stdGaussianAvg1 (fun z : ℝ => avgSigns n (fun σ => H σ z))
          = avgSigns n (fun σ => stdGaussianAvg1 (fun z : ℝ => H σ z)) :=
      stdGaussianAvg1_avgSigns_commute n H (hHz_int x)
    calc
      avgSigns n
        (fun σ =>
          stdGaussianAvg1
            (fun z : ℝ =>
              φ (Q2Gauss (n + m + 1) lam (hybridPoint n (m + 1) σ (Fin.cons z x)))))
          * gaussianWeight m x
          =
      stdGaussianAvg1 (fun z : ℝ => avgSigns n (fun σ => H σ z)) * gaussianWeight m x := by
            rw [hcomm]
      _ =
      c0 * ((∫ z : ℝ, avgSigns n (fun σ => H σ z) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume)
            * gaussianWeight m x) := by
            unfold stdGaussianAvg1 c0
            ring
      _ =
      c0 * ((∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume)
            * gaussianWeight m x) := by
            have hInt :
                ∫ z : ℝ, avgSigns n (fun σ => H σ z) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume
                  =
                ∫ z : ℝ, F (Fin.cons z x) * Real.exp (-(z ^ (2 : Nat)) / 2) ∂volume := by
                  refine MeasureTheory.integral_congr_ae ?_
                  exact Filter.Eventually.of_forall (fun z => by
                    have hEq :
                        avgSigns n (fun σ => H σ z) = F (Fin.cons z x) := by
                      refine avgSigns_congr n ?_
                      intro σ
                      exact congrArg φ (hQ σ x z).symm
                    simpa using congrArg (fun t : ℝ => t * Real.exp (-(z ^ (2 : Nat)) / 2)) hEq)
            rw [hInt]
  rw [hfun]
  simpa [c0, mul_assoc] using houter.const_mul c0

private lemma hybridQuadraticFormAvg_eq_boundary_gaussian_avg_C3
    (n m : ℕ) (lam : Fin (n + m + 1) → Fin (n + m + 1) → ℝ)
    (hsymm : ∀ i j, lam i j = lam j i) (hdiag : ∀ i, lam i i = 0)
    (φ : ℝ → ℝ) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    hybridQuadraticFormAvg n (m + 1)
      (fun i j : Fin (n + (m + 1)) =>
        lam (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
      =
    stdGaussianAvg m
      (fun x =>
        avgSigns n
          (fun σ =>
            stdGaussianAvg1
              (fun z : ℝ =>
                φ (Q2Gauss (n + m + 1) lam (hybridPoint n (m + 1) σ (Fin.cons z x)))))) := by
  let fCast : Fin (n + (m + 1)) → Fin (n + (m + 1)) → ℝ :=
    fun i j => lam (Fin.cast (by omega) i) (Fin.cast (by omega) j)
  let F : (Fin (m + 1) → ℝ) → ℝ :=
    fun y =>
      avgSigns n (fun σ => φ (Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y)))
  let S : (Fin (m + 1) → ℝ) → ℝ :=
    fun y =>
      avgSigns n (fun σ => |Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y)| ^ (3 : Nat))
  have hfCast_symm : ∀ i j, fCast i j = fCast j i := by
    intro i j
    exact hsymm _ _
  have hfCast_diag : ∀ i, fCast i i = 0 := by
    intro i
    exact hdiag _
  have hterm_cont (σ : Fin n → Fin 2) :
      Continuous
        (fun y : Fin (m + 1) → ℝ =>
          φ (Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y))) := by
    exact hφ.continuous.comp
      ((continuous_Q2Gauss (n + (m + 1)) fCast).comp (continuous_hybridPoint n (m + 1) σ))
  have hF_cont : Continuous F := by
    have hsum_cont :
        Continuous
          (fun y : Fin (m + 1) → ℝ =>
            ∑ σ : Fin n → Fin 2, φ (Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y))) := by
      exact continuous_finset_sum _ (fun σ _ => hterm_cont σ)
    unfold F avgSigns
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (continuous_const.mul hsum_cont)
  have hF_int :
      MeasureTheory.Integrable (fun y : Fin (m + 1) → ℝ => F y * gaussianWeight (m + 1) y) := by
    obtain ⟨C, hC_nonneg, hC⟩ := abs_phi_le_const_one_add_abs_cube φ M hM_nonneg hφ hφ3
    have hcube_int :
        MeasureTheory.Integrable (fun y : Fin (m + 1) → ℝ => S y * gaussianWeight (m + 1) y) := by
      simpa [S] using
        integrable_hybrid_q2_cube_avgSigns_gaussianWeight n (m + 1) fCast hfCast_symm hfCast_diag
    have hconst_int :
        MeasureTheory.Integrable (fun y : Fin (m + 1) → ℝ => C * gaussianWeight (m + 1) y) := by
      simpa [mul_assoc] using (integrable_stdGaussianDensity (m + 1)).const_mul C
    have hcube_scaled :
        MeasureTheory.Integrable (fun y : Fin (m + 1) → ℝ => (C * S y) * gaussianWeight (m + 1) y) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hcube_int.const_mul C
    have hdom_int := hconst_int.add hcube_scaled
    have hdom_int' :
        MeasureTheory.Integrable (fun y : Fin (m + 1) → ℝ => (C + C * S y) * gaussianWeight (m + 1) y) := by
      refine hdom_int.congr ?_
      exact Filter.Eventually.of_forall (fun y => by
        change C * gaussianWeight (m + 1) y + C * S y * gaussianWeight (m + 1) y =
          (C + C * S y) * gaussianWeight (m + 1) y
        ring)
    have hdom_int'' :
        MeasureTheory.Integrable (fun y : Fin (m + 1) → ℝ => (C * (1 + S y)) * gaussianWeight (m + 1) y) := by
      refine hdom_int'.congr ?_
      exact Filter.Eventually.of_forall (fun y => by ring)
    refine hdom_int''.mono' ?_ ?_
    · change MeasureTheory.AEStronglyMeasurable (fun y : Fin (m + 1) → ℝ => F y * gaussianWeight (m + 1) y)
      simpa [F] using (hF_cont.mul (continuous_gaussianWeight (m + 1))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun y => by
        have hFy :
            |F y| ≤ C * (1 + S y) := by
          calc
            |F y|
                ≤
              avgSigns n
                (fun σ =>
                  |φ
                    (Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y))|) := by
                    exact abs_avgSigns_le_avgSigns_abs n _
            _ ≤ avgSigns n (fun σ => C * (1 + |Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y)| ^ (3 : Nat))) := by
                  refine avgSigns_mono n ?_
                  intro σ
                  exact hC _
            _ = C * (1 + S y) := by
                  have hfun :
                      (fun σ : Fin n → Fin 2 =>
                        C * (1 + |Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y)| ^ (3 : Nat)))
                        =
                      (fun σ : Fin n → Fin 2 =>
                        C + C * |Q2Gauss (n + (m + 1)) fCast (hybridPoint n (m + 1) σ y)| ^ (3 : Nat)) := by
                    funext σ
                    ring
                  rw [hfun, avgSigns_add, avgSigns_const, avgSigns_mul_const_left]
                  unfold S
                  ring_nf
        have hweight_nonneg : 0 ≤ gaussianWeight (m + 1) y := gaussianWeight_nonneg (m + 1) y
        calc
          |F y * gaussianWeight (m + 1) y|
              = |F y| * gaussianWeight (m + 1) y := by
                  rw [abs_mul, abs_of_nonneg hweight_nonneg]
          _ ≤ C * (1 + S y) * gaussianWeight (m + 1) y := by
                exact mul_le_mul_of_nonneg_right hFy hweight_nonneg)
  have hQ (σ : Fin n → Fin 2) (x : Fin m → ℝ) (z : ℝ) :
      Q2Gauss (n + (m + 1))
        (fun i j : Fin (n + (m + 1)) =>
          lam (Fin.cast (by omega) i) (Fin.cast (by omega) j))
        (hybridPoint n (m + 1) σ (Fin.cons z x))
        =
      Q2Gauss (n + m + 1) lam (hybridPoint n (m + 1) σ (Fin.cons z x)) := by
    let y : Fin (n + (m + 1)) → ℝ := hybridPoint n (m + 1) σ (Fin.cons z x)
    have hvec :
        (fun i : Fin (n + m + 1) => y (Fin.cast (by omega) i))
          = hybridPoint n (m + 1) σ (Fin.cons z x) := by
      funext i
      simp [y]
    simpa [y, hvec] using
      (Q2Gauss_castKernel_eq (h := by omega) lam (hybridPoint n (m + 1) σ (Fin.cons z x)))
  have hHz_int (x : Fin m → ℝ) (σ : Fin n → Fin 2) :
      MeasureTheory.Integrable
        (fun z : ℝ =>
          φ (Q2Gauss (n + m + 1) lam (hybridPoint n (m + 1) σ (Fin.cons z x)))
            * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
    let U : ℝ :=
      Q2Gauss (n + m) (minorKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)
    let V : ℝ :=
      linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)
    have hrew :
        (fun z : ℝ =>
          φ (Q2Gauss (n + m + 1) lam (hybridPoint n (m + 1) σ (Fin.cons z x)))
            * Real.exp (-(z ^ (2 : Nat)) / 2))
          =
        (fun z : ℝ => φ (U + z * V) * Real.exp (-(z ^ (2 : Nat)) / 2)) := by
      funext z
      simp [U, V, Q2Gauss_boundary_gaussian, hsymm, hdiag]
    rw [hrew]
    exact integrable_one_dim_phi_affine_gaussianWeight_C3 φ M hM_nonneg hφ hφ3 U V
  unfold hybridQuadraticFormAvg hybridAvg
  rw [stdGaussianAvg_split_first m F hF_int]
  refine congrArg (stdGaussianAvg m) ?_
  funext x
  dsimp [F]
  let H : (Fin n → Fin 2) → ℝ → ℝ :=
    fun σ z =>
      φ
        (Q2Gauss (n + (m + 1))
          (fun i j : Fin (n + (m + 1)) =>
            lam (Fin.cast (by omega) i) (Fin.cast (by omega) j))
          (hybridPoint n (m + 1) σ (Fin.cons z x)))
  have hcomm :
      stdGaussianAvg1 (fun z : ℝ => avgSigns n (fun σ => H σ z))
        = avgSigns n (fun σ => stdGaussianAvg1 (fun z : ℝ => H σ z)) :=
    stdGaussianAvg1_avgSigns_commute n H (hHz_int x)
  rw [hcomm]
  refine avgSigns_congr n ?_
  intro σ
  refine congrArg stdGaussianAvg1 ?_
  funext z
  exact congrArg φ (hQ σ x z).symm

private def boundaryOneStepDiffReal
    (n m : ℕ)
    (lam : Fin (n + m + 1) → Fin (n + m + 1) → ℝ)
    (φ : ℝ → ℝ)
    (x : Fin m → ℝ) (σ : Fin n → Fin 2) : ℝ :=
  (((∑ b : Fin 2, φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x))) / 2 : ℝ)
    -
    stdGaussianAvg1
      (fun z : ℝ =>
        φ (Q2Gauss (n + m + 1) lam (hybridPoint n (m + 1) σ (Fin.cons z x)))))

private lemma boundaryOneStepDiffReal_abs_le
    (n m : ℕ)
    (lam : Fin (n + m + 1) → Fin (n + m + 1) → ℝ)
    (hsymm : ∀ i j, lam i j = lam j i) (hdiag : ∀ i, lam i i = 0)
    (φ : ℝ → ℝ) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M)
    (σ : Fin n → Fin 2) (x : Fin m → ℝ) :
    |boundaryOneStepDiffReal n m lam φ x σ|
      ≤ (((1 + 4 / Real.sqrt (2 * Real.pi)) / 6 : ℝ) * M)
          * |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)| ^ (3 : Nat) := by
  let U : ℝ :=
    Q2Gauss (n + m) (minorKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)
  let V : ℝ :=
    linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)
  have hrew :
      boundaryOneStepDiffReal n m lam φ x σ
        =
      (((φ (U - V) + φ (U + V)) / 2 : ℝ)
        - stdGaussianAvg1 (fun z : ℝ => φ (U + z * V))) := by
    unfold boundaryOneStepDiffReal
    rw [Fin.sum_univ_two]
    simp [signOf, U, V, Q2Gauss_boundary_sign, Q2Gauss_boundary_gaussian, hsymm, hdiag,
      sub_eq_add_neg]
  rw [hrew]
  simpa [U, V, mul_assoc, mul_left_comm, mul_comm] using
    (boundary_one_step_taylor_pointwise φ U V M hM_nonneg hφ hφ3)

private lemma boundary_one_step_average_raw_C3
    (n m : ℕ)
    (lam : Fin (n + m + 1) → Fin (n + m + 1) → ℝ)
    (hsymm : ∀ i j, lam i j = lam j i) (hdiag : ∀ i, lam i i = 0)
    (φ : ℝ → ℝ) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    |stdGaussianAvg m (fun x => avgSigns n (fun σ => boundaryOneStepDiffReal n m lam φ x σ))|
      ≤ (((1 + 4 / Real.sqrt (2 * Real.pi)) / 6 : ℝ) * M) *
          hybridAvg n m
            (fun y =>
              |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) y| ^ (3 : Nat)) := by
  let c0 : ℝ := (((1 + 4 / Real.sqrt (2 * Real.pi)) / 6 : ℝ) * M)
  have hcube_int :
      MeasureTheory.Integrable
        (fun x : Fin m → ℝ =>
          avgSigns n
            (fun σ =>
              c0
                * |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)| ^
                    (3 : Nat)) * gaussianWeight m x) := by
    let g : (Fin m → ℝ) → ℝ :=
      fun x =>
        avgSigns n
          (fun σ =>
            |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)| ^
              (3 : Nat)) * gaussianWeight m x
    have hbase :
        MeasureTheory.Integrable g :=
      integrable_boundary_cube_avgSigns_gaussianWeight n m
        (rowKernelAt (boundaryIndex n m) lam)
    have hscaled : MeasureTheory.Integrable (fun x : Fin m → ℝ => c0 * g x) :=
      hbase.const_mul c0
    have hrew :
        (fun x : Fin m → ℝ => c0 * g x)
          =
        (fun x : Fin m → ℝ =>
          avgSigns n
            (fun σ =>
              c0
                * |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)| ^
                    (3 : Nat)) * gaussianWeight m x) := by
      funext x
      rw [avgSigns_mul_const_left]
      simp [g, c0]
      ring
    rw [← hrew]
    exact hscaled
  have hstep1 :
      |stdGaussianAvg m (fun x => avgSigns n (fun σ => boundaryOneStepDiffReal n m lam φ x σ))|
        ≤ stdGaussianAvg m (fun x => |avgSigns n (fun σ => boundaryOneStepDiffReal n m lam φ x σ)|) := by
    exact abs_stdGaussianAvg_le_stdGaussianAvg_abs m _
  have hstep2 :
      stdGaussianAvg m (fun x => |avgSigns n (fun σ => boundaryOneStepDiffReal n m lam φ x σ)|)
        ≤
      stdGaussianAvg m
        (fun x =>
          avgSigns n
            (fun σ =>
              c0
                * |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)| ^
                    (3 : Nat))) := by
    refine stdGaussianAvg_mono_of_nonneg m ?_ hcube_int ?_
    · intro x
      positivity [hM_nonneg]
    · intro x
      refine le_trans (abs_avgSigns_le_avgSigns_abs n _) ?_
      refine avgSigns_mono n ?_
      intro σ
      simpa [c0] using
        (boundaryOneStepDiffReal_abs_le n m lam hsymm hdiag φ M hM_nonneg hφ hφ3 σ x)
  have hstep3 :
      stdGaussianAvg m
        (fun x =>
          avgSigns n
            (fun σ =>
              c0
                * |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)| ^
                    (3 : Nat)))
        =
      c0 *
        hybridAvg n m
          (fun y =>
            |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) y| ^ (3 : Nat)) := by
    have hfun :
        (fun x : Fin m → ℝ =>
          avgSigns n
            (fun σ =>
              c0
                * |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)| ^
                    (3 : Nat)))
          =
        (fun x : Fin m → ℝ =>
          c0
            * avgSigns n
                (fun σ =>
                  |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)| ^
                    (3 : Nat))) := by
      funext x
      rw [avgSigns_mul_const_left]
    have hconst :
        stdGaussianAvg m
          (fun x : Fin m → ℝ =>
            c0
              * avgSigns n
                  (fun σ =>
                    |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)| ^
                      (3 : Nat)))
          =
        c0 *
          stdGaussianAvg m
            (fun x : Fin m → ℝ =>
              avgSigns n
                (fun σ =>
                  |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)| ^
                    (3 : Nat))) := by
      simpa using
        (stdGaussianAvg_mul_const m c0
          (fun x : Fin m → ℝ =>
            avgSigns n
              (fun σ =>
                |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)| ^
                  (3 : Nat))))
    rw [hfun]
    simpa [hybridAvg] using hconst
  calc
    |stdGaussianAvg m (fun x => avgSigns n (fun σ => boundaryOneStepDiffReal n m lam φ x σ))|
      ≤ stdGaussianAvg m (fun x => |avgSigns n (fun σ => boundaryOneStepDiffReal n m lam φ x σ)|) := hstep1
    _ ≤
      stdGaussianAvg m
        (fun x =>
          avgSigns n
            (fun σ =>
              c0
                * |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) (hybridPoint n m σ x)| ^
                    (3 : Nat))) := hstep2
    _ = c0 *
        hybridAvg n m
          (fun y =>
            |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) y| ^ (3 : Nat)) := hstep3

private lemma hybridQuadraticFormAvg_adjacent_step_raw_C3
    (n m : ℕ)
    (lam : Fin (n + m + 1) → Fin (n + m + 1) → ℝ)
    (hsymm : ∀ i j, lam i j = lam j i) (hdiag : ∀ i, lam i i = 0)
    (φ : ℝ → ℝ) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    |hybridQuadraticFormAvg (n + 1) m
        (fun i j : Fin ((n + 1) + m) =>
          lam (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
      - hybridQuadraticFormAvg n (m + 1)
          (fun i j : Fin (n + (m + 1)) =>
            lam (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ|
      ≤ (((1 + 4 / Real.sqrt (2 * Real.pi)) / 6 : ℝ) * M) *
          hybridAvg n m
            (fun y =>
              |linForm (n + m) (rowKernelAt (boundaryIndex n m) lam) y| ^ (3 : Nat)) := by
  let A : (Fin m → ℝ) → ℝ :=
    fun x =>
      avgSigns n
        (fun σ =>
          (((∑ b : Fin 2, φ (Q2Gauss (n + m + 1) lam (boundarySignHybridPoint n m σ b x))) / 2 : ℝ)))
  let G : (Fin m → ℝ) → ℝ :=
    fun x =>
      avgSigns n
        (fun σ =>
          stdGaussianAvg1
            (fun z : ℝ =>
              φ (Q2Gauss (n + m + 1) lam (hybridPoint n (m + 1) σ (Fin.cons z x)))))
  have hA_int :
      MeasureTheory.Integrable (fun x : Fin m → ℝ => A x * gaussianWeight m x) := by
    simpa [A] using
      (integrable_boundary_sign_avgSigns_gaussianWeight_C3 n m lam hsymm hdiag φ M hM_nonneg hφ hφ3)
  have hG_int :
      MeasureTheory.Integrable (fun x : Fin m → ℝ => G x * gaussianWeight m x) := by
    simpa [G] using
      (integrable_boundary_gaussian_avgSigns_gaussianWeight_C3 n m lam hsymm hdiag φ M hM_nonneg hφ hφ3)
  rw [hybridQuadraticFormAvg_succ_eq_boundary_sign_avg]
  rw [hybridQuadraticFormAvg_eq_boundary_gaussian_avg_C3 n m lam hsymm hdiag φ M hM_nonneg hφ hφ3]
  rw [← stdGaussianAvg_sub m A G hA_int hG_int]
  have hdiff :
      (fun x : Fin m → ℝ => A x - G x)
        =
      (fun x : Fin m → ℝ => avgSigns n (fun σ => boundaryOneStepDiffReal n m lam φ x σ)) := by
    funext x
    unfold A G boundaryOneStepDiffReal
    rw [avgSigns_sub]
  rw [hdiff] at *
  simpa using
    (boundary_one_step_average_raw_C3 n m lam hsymm hdiag φ M hM_nonneg hφ hφ3)

private lemma quadraticForm_lindeberg_adjacent_step_C3
    (n m : ℕ)
    (f : Fin (n + m + 1) → Fin (n + m + 1) → ℝ)
    (hsymm : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0)
    (φ : ℝ → ℝ) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    |hybridQuadraticFormAvg (n + 1) m
        (fun i j : Fin ((n + 1) + m) =>
          f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
      - hybridQuadraticFormAvg n (m + 1)
          (fun i j : Fin (n + (m + 1)) =>
            f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ|
      ≤ (6 : ℝ) * M *
          (kernelInfluence (n + m + 1) f (boundaryIndex n m)
            * Real.sqrt (kernelInfluence (n + m + 1) f (boundaryIndex n m))) := by
  have hraw :=
    hybridQuadraticFormAvg_adjacent_step_raw_C3 n m f hsymm hdiag φ M hM_nonneg hφ hφ3
  let S : ℝ :=
    ∑ i : Fin (n + m), rowKernelAt (boundaryIndex n m) f i ^ (2 : Nat)
  have hs :
      S = 4 * kernelInfluence (n + m + 1) f (boundaryIndex n m) := by
    dsimp [S]
    simpa using sum_sq_rowKernelAt_eq_four_kernelInfluence (boundaryIndex n m) f hdiag
  have hk_nonneg : 0 ≤ kernelInfluence (n + m + 1) f (boundaryIndex n m) :=
    kernelInfluence_nonneg (n + m + 1) f (boundaryIndex n m)
  have hcube :=
    hybridAvg_abs_linForm_cube_le_sqrt_three_mul_sum_sq_mul_sqrt_sum_sq n m
      (rowKernelAt (boundaryIndex n m) f)
  calc
    |hybridQuadraticFormAvg (n + 1) m
        (fun i j : Fin ((n + 1) + m) =>
          f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
      - hybridQuadraticFormAvg n (m + 1)
          (fun i j : Fin (n + (m + 1)) =>
            f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ|
        ≤ (((1 + 4 / Real.sqrt (2 * Real.pi)) / 6 : ℝ) * M) *
            hybridAvg n m
              (fun y =>
                |linForm (n + m) (rowKernelAt (boundaryIndex n m) f) y| ^ (3 : Nat)) := hraw
    _ ≤ (((1 + 4 / Real.sqrt (2 * Real.pi)) / 6 : ℝ) * M) * (Real.sqrt 3 * S * Real.sqrt S) := by
      gcongr
    _ ≤ (3 / 4 : ℝ) * M * (S * Real.sqrt S) := by
      have hconst := lindeberg_scalar_constant_le_three_quarters
      calc
        (((1 + 4 / Real.sqrt (2 * Real.pi)) / 6 : ℝ) * M) * (Real.sqrt 3 * S * Real.sqrt S)
            = ((((1 + 4 / Real.sqrt (2 * Real.pi)) * Real.sqrt 3) / 6 : ℝ) * M)
                * (S * Real.sqrt S) := by ring
        _ ≤ ((3 / 4 : ℝ) * M) * (S * Real.sqrt S) := by
              gcongr
    _ = (6 : ℝ) * M *
          (kernelInfluence (n + m + 1) f (boundaryIndex n m)
            * Real.sqrt (kernelInfluence (n + m + 1) f (boundaryIndex n m))) := by
          rw [hs]
          have hsqrt :
              Real.sqrt (4 * kernelInfluence (n + m + 1) f (boundaryIndex n m))
                = 2 * Real.sqrt (kernelInfluence (n + m + 1) f (boundaryIndex n m)) := by
            rw [Real.sqrt_mul (show 0 ≤ (4 : ℝ) by positivity),
              show Real.sqrt (4 : ℝ) = 2 by norm_num]
          rw [hsqrt]
          ring

/-- Paper-facing `C^3` Lindeberg comparison for degree-`2` quadratic forms.

This compares the sign and Gaussian quadratic-form averages for a symmetric
kernel with zero diagonal.
The conclusion is the standard `C^3` Lindeberg bound:

`|E[φ(Q_f(X))) - E[φ(Q_f(G))]| ≤ 6 M * Σ Inf_k(f)^(3/2)`.
-/
theorem quadraticForm_lindeberg_comparison_C3
    (N : ℕ)
    (f : Fin N → Fin N → ℝ)
    (hsymm : ∀ i j, f i j = f j i)
    (hdiag : ∀ i, f i i = 0)
    (φ : ℝ → ℝ) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    |avgSigns N (fun σ => φ (Q2Signs N f σ))
      - stdGaussianAvg N (fun x => φ (Q2Gauss N f x))|
      ≤ (6 : ℝ) * M * ∑ k : Fin N,
          kernelInfluence N f k * Real.sqrt (kernelInfluence N f k) := by
  let H : ℕ → ℝ := fun k =>
    if hk : k ≤ N then
      hybridQuadraticFormAvg k (N - k)
        (fun i j : Fin (k + (N - k)) =>
          f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
    else 0
  have hstep :
      ∀ k : Fin N,
        |H (k + 1) - H k|
          ≤ (6 : ℝ) * M * (kernelInfluence N f k * Real.sqrt (kernelInfluence N f k)) := by
    intro k
    let f' : Fin (((k : ℕ) + (N - (k + 1))) + 1) → Fin (((k : ℕ) + (N - (k + 1))) + 1) → ℝ :=
      fun i j => f (Fin.cast (by omega) i) (Fin.cast (by omega) j)
    have hk0 : (k : ℕ) ≤ N := Nat.le_of_lt k.is_lt
    have hk1 : k + 1 ≤ N := Nat.succ_le_of_lt k.is_lt
    have hf'_symm : ∀ i j, f' i j = f' j i := by
      intro i j
      exact hsymm _ _
    have hf'_diag : ∀ i, f' i i = 0 := by
      intro i
      exact hdiag _
    have hraw :
        |hybridQuadraticFormAvg ((k : ℕ) + 1) (N - (k + 1))
            (fun i j : Fin (((k : ℕ) + 1) + (N - (k + 1))) =>
              f' (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
          - hybridQuadraticFormAvg (k : ℕ) ((N - (k + 1)) + 1)
              (fun i j : Fin ((k : ℕ) + ((N - (k + 1)) + 1)) =>
                f' (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ|
          ≤ (6 : ℝ) * M *
              (kernelInfluence (((k : ℕ) + (N - (k + 1))) + 1) f'
                (boundaryIndex (k : ℕ) (N - (k + 1)))
                * Real.sqrt
                    (kernelInfluence (((k : ℕ) + (N - (k + 1))) + 1) f'
                      (boundaryIndex (k : ℕ) (N - (k + 1))))) := by
      simpa [f'] using
        (quadraticForm_lindeberg_adjacent_step_C3
          (n := (k : ℕ)) (m := N - (k + 1)) (f := f')
          hf'_symm hf'_diag (φ := φ) (M := M) hM_nonneg hφ hφ3)
    have hker :
        kernelInfluence (((k : ℕ) + (N - (k + 1))) + 1) f'
            (boundaryIndex (k : ℕ) (N - (k + 1)))
          = kernelInfluence N f k := by
      simpa [f', boundaryIndex_eq_fin, k.is_lt] using
        (kernelInfluence_cast_eq (h := by omega) f (boundaryIndex (k : ℕ) (N - (k + 1))))
    have hsecond :
        hybridQuadraticFormAvg (k : ℕ) (N - k)
            (fun i j : Fin ((k : ℕ) + (N - k)) =>
              f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
          =
        hybridQuadraticFormAvg (k : ℕ) ((N - (k + 1)) + 1)
            (fun i j : Fin ((k : ℕ) + ((N - (k + 1)) + 1)) =>
              f' (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ := by
      have hkshape : N - (k : ℕ) = (N - (k + 1)) + 1 := by
        omega
      have hkshape_sum : (k : ℕ) + (N - k) = (k : ℕ) + ((N - (k + 1)) + 1) := by
        omega
      have hkernel :
          (fun i j : Fin ((k : ℕ) + ((N - (k + 1)) + 1)) =>
              f' (Fin.cast (by omega) i) (Fin.cast (by omega) j))
            =
          (fun i j : Fin ((k : ℕ) + ((N - (k + 1)) + 1)) =>
              f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) := by
        funext i j
        simp [f']
      calc
        hybridQuadraticFormAvg (k : ℕ) (N - k)
            (fun i j : Fin ((k : ℕ) + (N - k)) =>
              f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
            =
        hybridQuadraticFormAvg (k : ℕ) ((N - (k + 1)) + 1)
            (fun i j : Fin ((k : ℕ) + ((N - (k + 1)) + 1)) =>
              f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ := by
                convert
                  (rfl :
                    hybridQuadraticFormAvg (k : ℕ) ((N - (k + 1)) + 1)
                      (fun i j : Fin ((k : ℕ) + ((N - (k + 1)) + 1)) =>
                        f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
                      =
                    hybridQuadraticFormAvg (k : ℕ) ((N - (k + 1)) + 1)
                      (fun i j : Fin ((k : ℕ) + ((N - (k + 1)) + 1)) =>
                        f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ)
        _ =
        hybridQuadraticFormAvg (k : ℕ) ((N - (k + 1)) + 1)
            (fun i j : Fin ((k : ℕ) + ((N - (k + 1)) + 1)) =>
              f' (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ := by
                rw [hkernel]
    calc
      |H (k + 1) - H k|
          = |hybridQuadraticFormAvg ((k : ℕ) + 1) (N - (k + 1))
                (fun i j : Fin (((k : ℕ) + 1) + (N - (k + 1))) =>
                  f' (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
              - hybridQuadraticFormAvg (k : ℕ) (N - k)
                  (fun i j : Fin ((k : ℕ) + (N - k)) =>
                    f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ| := by
              simp [H, hk0, hk1, f']
      _ = |hybridQuadraticFormAvg ((k : ℕ) + 1) (N - (k + 1))
                (fun i j : Fin (((k : ℕ) + 1) + (N - (k + 1))) =>
                  f' (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
              - hybridQuadraticFormAvg (k : ℕ) ((N - (k + 1)) + 1)
                  (fun i j : Fin ((k : ℕ) + ((N - (k + 1)) + 1)) =>
                    f' (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ| := by
              congr 1
              rw [hsecond]
      _ ≤ (6 : ℝ) * M *
            (kernelInfluence (((k : ℕ) + (N - (k + 1))) + 1) f'
              (boundaryIndex (k : ℕ) (N - (k + 1)))
              * Real.sqrt
                  (kernelInfluence (((k : ℕ) + (N - (k + 1))) + 1) f'
                    (boundaryIndex (k : ℕ) (N - (k + 1))))) := hraw
      _ = (6 : ℝ) * M * (kernelInfluence N f k * Real.sqrt (kernelInfluence N f k)) := by
              rw [hker]
  have hsum :
      Finset.sum (Finset.range N) (fun i => |H (i + 1) - H i|)
        ≤ (6 : ℝ) * M * ∑ k : Fin N,
            kernelInfluence N f k * Real.sqrt (kernelInfluence N f k) := by
    calc
      Finset.sum (Finset.range N) (fun i => |H (i + 1) - H i|)
          = ∑ k : Fin N, |H (k + 1) - H k| := by
              rw [← Fin.sum_univ_eq_sum_range]
      _ ≤ ∑ k : Fin N,
            (6 : ℝ) * M * (kernelInfluence N f k * Real.sqrt (kernelInfluence N f k)) := by
              exact Finset.sum_le_sum (fun k hk => hstep k)
      _ = (6 : ℝ) * M * ∑ k : Fin N,
            kernelInfluence N f k * Real.sqrt (kernelInfluence N f k) := by
              rw [← Finset.mul_sum]
  have htel := abs_sub_zero_le_sum_range_abs_sub H N
  have hHN : H N = avgSigns N (fun σ => φ (Q2Signs N f σ)) := by
    calc
      H N
          = hybridQuadraticFormAvg N (N - N)
              (fun i j : Fin (N + (N - N)) => f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ := by
                simp [H]
      _ = hybridQuadraticFormAvg N 0
            (fun i j : Fin (N + 0) => f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ := by
                convert
                  (rfl :
                    hybridQuadraticFormAvg N 0
                      (fun i j : Fin (N + 0) => f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ
                      =
                    hybridQuadraticFormAvg N 0
                      (fun i j : Fin (N + 0) => f (Fin.cast (by omega) i) (Fin.cast (by omega) j)) φ)
                omega
      _ = hybridQuadraticFormAvg N 0 f φ := by
                have hkernel0 :
                    (fun i j : Fin (N + 0) => f (Fin.cast (by omega) i) (Fin.cast (by omega) j))
                      = f := by
                  funext i j
                  simp
                rw [hkernel0]
      _ = avgSigns N (fun σ => φ (Q2Signs N f σ)) :=
            hybridQuadraticFormAvg_all_sign N f φ
  have hH0 : H 0 = stdGaussianAvg N (fun x => φ (Q2Gauss N f x)) := by
    simp [H]
    simpa using (hybridQuadraticFormAvg_all_gaussian N f φ)
  calc
    |avgSigns N (fun σ => φ (Q2Signs N f σ))
      - stdGaussianAvg N (fun x => φ (Q2Gauss N f x))|
        = |H N - H 0| := by rw [hHN, hH0]
    _ ≤ Finset.sum (Finset.range N) (fun i => |H (i + 1) - H i|) := htel
    _ ≤ (6 : ℝ) * M * ∑ k : Fin N,
          kernelInfluence N f k * Real.sqrt (kernelInfluence N f k) := hsum

/- Project-kernel specialization of `quadraticForm_lindeberg_comparison_C3`.

This is an internal specialization used only to derive the `cos` and `sin`
comparisons appearing in the final `psi` theorem. -/
private theorem quadraticForm_lindeberg_comparison_mooKernel
    (N : ℕ) (lam : Fin N → Fin N → ℝ)
    (φ : ℝ → ℝ) (M : ℝ)
    (hM_nonneg : 0 ≤ M)
    (hφ : ContDiff ℝ 3 φ)
    (hφ3 : ∀ x : ℝ, |iteratedDeriv 3 φ x| ≤ M) :
    |avgSigns N (fun σ => φ (Q2Signs N (mooKernel N lam) σ))
      - stdGaussianAvg N (fun x => φ (Q2Gauss N (mooKernel N lam) x))|
      ≤ (3 / 4 : ℝ) * M * threeHalfInfluenceSum N lam := by
  have hraw :=
    quadraticForm_lindeberg_comparison_C3
      (N := N) (f := mooKernel N lam)
      (mooKernel_symm N lam) (mooKernel_diag N lam)
      (φ := φ) (M := M) hM_nonneg hφ hφ3
  calc
    |avgSigns N (fun σ => φ (Q2Signs N (mooKernel N lam) σ))
      - stdGaussianAvg N (fun x => φ (Q2Gauss N (mooKernel N lam) x))|
        ≤ (6 : ℝ) * M * ∑ k : Fin N,
            kernelInfluence N (mooKernel N lam) k
              * Real.sqrt (kernelInfluence N (mooKernel N lam) k) := hraw
    _ = (3 / 4 : ℝ) * M * threeHalfInfluenceSum N lam := by
        unfold threeHalfInfluenceSum
        calc
          (6 : ℝ) * M * ∑ k : Fin N,
              kernelInfluence N (mooKernel N lam) k
                * Real.sqrt (kernelInfluence N (mooKernel N lam) k)
              =
          ∑ k : Fin N,
            ((6 : ℝ) * M)
              * (kernelInfluence N (mooKernel N lam) k
                  * Real.sqrt (kernelInfluence N (mooKernel N lam) k)) := by
                rw [Finset.mul_sum]
          _ =
          ∑ k : Fin N,
            (3 / 4 : ℝ) * M * (rowInfluence N lam k * Real.sqrt (rowInfluence N lam k)) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                rw [kernelInfluence_mooKernel]
                have hrow_nonneg : 0 ≤ rowInfluence N lam k := rowInfluence_nonneg N lam k
                rw [rowInfluence]
                have hsqrt :
                    Real.sqrt ((1 / 4 : ℝ) * ∑ i : Fin N,
                        if i ≠ k then lam (min i k) (max i k) ^ (2 : Nat) else 0)
                      =
                    (1 / 2 : ℝ) * Real.sqrt (∑ i : Fin N,
                        if i ≠ k then lam (min i k) (max i k) ^ (2 : Nat) else 0) := by
                  rw [Real.sqrt_mul (show 0 ≤ (1 / 4 : ℝ) by positivity),
                    show Real.sqrt (1 / 4 : ℝ) = (1 / 2 : ℝ) by norm_num]
                rw [hsqrt]
                ring
          _ = (3 / 4 : ℝ) * M * ∑ k : Fin N, rowInfluence N lam k * Real.sqrt (rowInfluence N lam k) := by
                rw [← Finset.mul_sum]
          _ = (3 / 4 : ℝ) * M * threeHalfInfluenceSum N lam := by
                rfl

private lemma quadraticForm_lindeberg_comparison_cos_mooKernel
    (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    |avgSigns n (fun σ => Real.cos (Q2Signs n (mooKernel n lam) σ))
      - stdGaussianAvg n (fun x => Real.cos (Q2Gauss n (mooKernel n lam) x))|
      ≤ (3 / 4 : ℝ) * threeHalfInfluenceSum n lam := by
  simpa [q2Signs_mooKernel_eq_innerX, q2Gauss_mooKernel_eq_gaussianInnerX] using
    (quadraticForm_lindeberg_comparison_mooKernel
      (N := n) (lam := lam) (φ := Real.cos) (M := 1)
      (by positivity)
      Real.contDiff_cos
      (fun x => Real.abs_iteratedDeriv_cos_le_one 3 x))

private lemma quadraticForm_lindeberg_comparison_sin_mooKernel
    (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    |avgSigns n (fun σ => Real.sin (Q2Signs n (mooKernel n lam) σ))
      - stdGaussianAvg n (fun x => Real.sin (Q2Gauss n (mooKernel n lam) x))|
      ≤ (3 / 4 : ℝ) * threeHalfInfluenceSum n lam := by
  simpa [q2Signs_mooKernel_eq_innerX, q2Gauss_mooKernel_eq_gaussianInnerX] using
    (quadraticForm_lindeberg_comparison_mooKernel
      (N := n) (lam := lam) (φ := Real.sin) (M := 1)
      (by positivity)
      Real.contDiff_sin
      (fun x => Real.abs_iteratedDeriv_sin_le_one 3 x))

/-- Weak invariance bound in the project normalization.

This is the direct comparison theorem needed for the `J`-split far-shell
argument. It bounds the gap between `psi` and `gaussianPsi` by
`(3 / 2) * threeHalfInfluenceSum n lam`, where the latter encodes the sum of
row influences raised to the `3/2` power.
-/
theorem psi_sub_gaussianPsi_le_threeHalfInfluenceSum
    (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    ‖psi n lam - gaussianPsi n lam‖ ≤ (3 / 2 : ℝ) * threeHalfInfluenceSum n lam := by
  have hre :
      |(psi n lam - gaussianPsi n lam).re|
        ≤ (3 / 4 : ℝ) * threeHalfInfluenceSum n lam := by
    simpa [psi_re_eq_avgSigns_cos, gaussianPsi_re,
      q2Signs_mooKernel_eq_innerX, q2Gauss_mooKernel_eq_gaussianInnerX] using
      (quadraticForm_lindeberg_comparison_cos_mooKernel n lam)
  have him :
      |(psi n lam - gaussianPsi n lam).im|
        ≤ (3 / 4 : ℝ) * threeHalfInfluenceSum n lam := by
    simpa [psi_im_eq_avgSigns_sin, gaussianPsi_im,
      q2Signs_mooKernel_eq_innerX, q2Gauss_mooKernel_eq_gaussianInnerX] using
      (quadraticForm_lindeberg_comparison_sin_mooKernel n lam)
  have hnonneg : 0 ≤ threeHalfInfluenceSum n lam := by
    unfold threeHalfInfluenceSum
    refine Finset.sum_nonneg ?_
    intro k hk
    exact mul_nonneg (rowInfluence_nonneg n lam k) (Real.sqrt_nonneg _)
  calc
    ‖psi n lam - gaussianPsi n lam‖
      ≤ |(psi n lam - gaussianPsi n lam).re| + |(psi n lam - gaussianPsi n lam).im| := by
          exact Complex.norm_le_abs_re_add_abs_im (psi n lam - gaussianPsi n lam)
    _ ≤ (3 / 4 : ℝ) * threeHalfInfluenceSum n lam
          + (3 / 4 : ℝ) * threeHalfInfluenceSum n lam := by
            gcongr
    _ = (3 / 2 : ℝ) * threeHalfInfluenceSum n lam := by
          ring

private lemma edgePsi_norm_sq_le_half_one_add_exp_rowInfluence
    (n : ℕ) (hn : 2 ≤ n) (mu : Cn3Torus.Edge n → ℝ) (k : Fin n)
    (hbox : mu ∈ edgeBox n (π / 4)) :
    ‖Cn3Torus.psi n mu‖ ^ 2 ≤
      (1 + Real.exp (-(8 / Real.pi ^ (2 : Nat)) * rowInfluenceEdge n mu k)) / 2 := by
  have hbox' : matrixOfEdge n mu ∈ box n (π / 4) := hbox
  have hsq :=
    universal_magnitude_bound_full n hn (matrixOfEdge n mu) k
  have hfac :
      ∀ i : Fin n,
        (if i = k then 1
         else if i < k then Real.cos (2 * matrixOfEdge n mu i k)
         else Real.cos (2 * matrixOfEdge n mu k i))
          ≤
        Real.exp
          (-(8 / Real.pi ^ (2 : Nat)) *
            (if i ≠ k then matrixOfEdge n mu (min i k) (max i k) ^ (2 : Nat) else 0)) := by
    intro i
    by_cases hik : i = k
    · simp [hik]
    · rcases lt_or_gt_of_ne hik with hik_lt | hik_gt
      · have hcoord : |matrixOfEdge n mu i k| ≤ Real.pi / 4 := hbox' i k hik_lt
        have hcos :
            Real.cos (2 * matrixOfEdge n mu i k)
              ≤ Real.exp (-(8 / Real.pi ^ (2 : Nat)) * (matrixOfEdge n mu i k) ^ (2 : Nat)) :=
          cos_two_mul_le_exp_neg_eight_div_pi_sq_sq hcoord
        simpa [hik, hik_lt, not_lt_of_ge (le_of_lt hik_lt),
          min_eq_left (le_of_lt hik_lt), max_eq_right (le_of_lt hik_lt)] using hcos
      · have hcoord : |matrixOfEdge n mu k i| ≤ Real.pi / 4 := hbox' k i hik_gt
        have hcos :
            Real.cos (2 * matrixOfEdge n mu k i)
              ≤ Real.exp (-(8 / Real.pi ^ (2 : Nat)) * (matrixOfEdge n mu k i) ^ (2 : Nat)) :=
          cos_two_mul_le_exp_neg_eight_div_pi_sq_sq hcoord
        simpa [hik, not_lt_of_ge (le_of_lt hik_gt),
          min_eq_right (le_of_lt hik_gt), max_eq_left (le_of_lt hik_gt)] using hcos
  have hfac_nonneg :
      ∀ i : Fin n,
        0 ≤
          (if i = k then 1
           else if i < k then Real.cos (2 * matrixOfEdge n mu i k)
           else Real.cos (2 * matrixOfEdge n mu k i)) := by
    intro i
    by_cases hik : i = k
    · simp [hik]
    · rcases lt_or_gt_of_ne hik with hik_lt | hik_gt
      · have hcoord : |matrixOfEdge n mu i k| ≤ Real.pi / 4 := hbox' i k hik_lt
        have harg : |2 * matrixOfEdge n mu i k| ≤ Real.pi / 2 := by
          calc
            |2 * matrixOfEdge n mu i k| = (2 : ℝ) * |matrixOfEdge n mu i k| := by
              rw [abs_mul, abs_of_nonneg (by norm_num)]
            _ ≤ (2 : ℝ) * (Real.pi / 4) := by gcongr
            _ = Real.pi / 2 := by ring
        have hpair : -(Real.pi / 2) ≤ 2 * matrixOfEdge n mu i k ∧
            2 * matrixOfEdge n mu i k ≤ Real.pi / 2 := abs_le.mp harg
        have hcos_nonneg :
            0 ≤ Real.cos (2 * matrixOfEdge n mu i k) := by
          exact Real.cos_nonneg_of_mem_Icc hpair
        simpa [hik, hik_lt, not_lt_of_ge (le_of_lt hik_lt)] using hcos_nonneg
      · have hcoord : |matrixOfEdge n mu k i| ≤ Real.pi / 4 := hbox' k i hik_gt
        have harg : |2 * matrixOfEdge n mu k i| ≤ Real.pi / 2 := by
          calc
            |2 * matrixOfEdge n mu k i| = (2 : ℝ) * |matrixOfEdge n mu k i| := by
              rw [abs_mul, abs_of_nonneg (by norm_num)]
            _ ≤ (2 : ℝ) * (Real.pi / 4) := by gcongr
            _ = Real.pi / 2 := by ring
        have hpair : -(Real.pi / 2) ≤ 2 * matrixOfEdge n mu k i ∧
            2 * matrixOfEdge n mu k i ≤ Real.pi / 2 := abs_le.mp harg
        have hcos_nonneg :
            0 ≤ Real.cos (2 * matrixOfEdge n mu k i) := by
          exact Real.cos_nonneg_of_mem_Icc hpair
        simpa [hik, not_lt_of_ge (le_of_lt hik_gt)] using hcos_nonneg
  have hprod_le :
      ∏ i : Fin n,
          (if i = k then 1
           else if i < k then Real.cos (2 * matrixOfEdge n mu i k)
           else Real.cos (2 * matrixOfEdge n mu k i))
        ≤
      ∏ i : Fin n,
          Real.exp
            (-(8 / Real.pi ^ (2 : Nat)) *
              (if i ≠ k then matrixOfEdge n mu (min i k) (max i k) ^ (2 : Nat) else 0)) := by
    refine Finset.prod_le_prod (fun i hi => hfac_nonneg i) ?_
    intro i hi
    exact hfac i
  have hprod_exp :
      ∏ i : Fin n,
          Real.exp
            (-(8 / Real.pi ^ (2 : Nat)) *
              (if i ≠ k then matrixOfEdge n mu (min i k) (max i k) ^ (2 : Nat) else 0))
        =
      Real.exp (-(8 / Real.pi ^ (2 : Nat)) * rowInfluenceEdge n mu k) := by
    calc
      ∏ i : Fin n,
          Real.exp
            (-(8 / Real.pi ^ (2 : Nat)) *
              (if i ≠ k then matrixOfEdge n mu (min i k) (max i k) ^ (2 : Nat) else 0))
          =
        Real.exp
          (∑ i : Fin n,
            (-(8 / Real.pi ^ (2 : Nat)) *
              (if i ≠ k then matrixOfEdge n mu (min i k) (max i k) ^ (2 : Nat) else 0))) := by
            rw [← Real.exp_sum]
      _ = Real.exp (-(8 / Real.pi ^ (2 : Nat)) * rowInfluenceEdge n mu k) := by
            congr 1
            simp [rowInfluenceEdge_eq, rowInfluence, Finset.mul_sum]
  have hbound :
      ‖Cn3Torus.psi n mu‖ ^ 2
        ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) *
            Real.exp (-(8 / Real.pi ^ (2 : Nat)) * rowInfluenceEdge n mu k) := by
    have hsq' :
        ‖Cn3Torus.psi n mu‖ ^ 2
          ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) *
              ∏ i : Fin n,
                (if i = k then 1
                 else if i < k then Real.cos (2 * matrixOfEdge n mu i k)
                 else Real.cos (2 * matrixOfEdge n mu k i)) := by
      simpa [psi_matrixOfEdge_eq] using hsq
    have hmul :
        (1 / 2 : ℝ) *
            ∏ i : Fin n,
              (if i = k then 1
               else if i < k then Real.cos (2 * matrixOfEdge n mu i k)
               else Real.cos (2 * matrixOfEdge n mu k i))
          ≤
        (1 / 2 : ℝ) *
            Real.exp (-(8 / Real.pi ^ (2 : Nat)) * rowInfluenceEdge n mu k) := by
      have htmp := mul_le_mul_of_nonneg_left (hprod_le.trans_eq hprod_exp) (by positivity : 0 ≤ (1 / 2 : ℝ))
      simpa using htmp
    linarith
  ring_nf at hbound ⊢
  exact hbound

private lemma edgePsi_norm_sq_le_half_one_add_exp_rowInfluenceMax
    (n : ℕ) (hn : 2 ≤ n) (mu : Cn3Torus.Edge n → ℝ)
    (hbox : mu ∈ edgeBox n (π / 4)) :
    ‖Cn3Torus.psi n mu‖ ^ 2 ≤
      (1 + Real.exp (-(8 / Real.pi ^ (2 : Nat)) * rowInfluenceMaxEdge n mu)) / 2 := by
  have hn0 : 0 < n := by omega
  obtain ⟨k, hk⟩ := exists_rowInfluence_eq_maxInfluence n hn0 (matrixOfEdge n mu)
  have hrow := edgePsi_norm_sq_le_half_one_add_exp_rowInfluence n hn mu k hbox
  simpa [rowInfluenceMaxEdge_eq, rowInfluenceEdge_eq, hk] using hrow

private lemma rowInfluenceMaxEdge_ge_eta_div_n_two_thirds
    (n : ℕ) (hn : 0 < n) (mu : Cn3Torus.Edge n → ℝ) {η : ℝ}
    (hη : 0 < η) (hJ : η < threeHalfInfluenceSumEdge n mu) :
    (η / (n : ℝ)) ^ (2 / 3 : ℝ) ≤ rowInfluenceMaxEdge n mu := by
  have hnR_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hI_nonneg : 0 ≤ rowInfluenceMaxEdge n mu := by
    simpa [rowInfluenceMaxEdge] using maxInfluence_nonneg n (matrixOfEdge n mu)
  have hupper :=
    threeHalfInfluenceSumEdge_le_card_mul_maxInfluence n hn mu
  have hdiv :
      η / (n : ℝ) ≤ rowInfluenceMaxEdge n mu * Real.sqrt (rowInfluenceMaxEdge n mu) := by
    rw [_root_.div_le_iff₀ hnR_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using (lt_of_lt_of_le hJ hupper).le
  have hη_div_pos : 0 < η / (n : ℝ) := by positivity
  have hroot :
      ((η / (n : ℝ)) ^ (2 / 3 : ℝ)) * Real.sqrt ((η / (n : ℝ)) ^ (2 / 3 : ℝ))
        ≤ rowInfluenceMaxEdge n mu * Real.sqrt (rowInfluenceMaxEdge n mu) := by
    have hx :
        ((η / (n : ℝ)) ^ (2 / 3 : ℝ)) * Real.sqrt ((η / (n : ℝ)) ^ (2 / 3 : ℝ))
          = η / (n : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hη_div_pos.le, ← Real.rpow_add hη_div_pos]
      norm_num [Real.rpow_one]
    simpa [hx] using hdiv
  exact le_of_mul_sqrt_le_mul_sqrt (by positivity) hI_nonneg hroot

/-- The direct far-shell integral bound proved from the `J`-split argument.

This is the theorem surface consumed by the local-gap file:

the weighted even far-shell contribution is bounded by three terms:

- `qSm^(4t)`, a small-radius decay term
- `qBig^(4t)`, a uniform box-decay term
- `exp (-(a * t) / n^(2/3))`, the MOO/invariance contribution
-/
theorem edgeEvenFarShell_contribution_bound_Jsplit
    (r : ℝ) (hr : 0 < r) (_hr' : r < π / 4) :
    ∃ qSm qBig a : ℝ,
      0 < qSm ∧ qSm < 1 ∧
      0 < qBig ∧ qBig < 1 ∧
      0 < a ∧
      ∀ (n t : ℕ), 2 ≤ n → 1 ≤ t →
        Cn3Torus.texPrefactor n *
          ∫ mu in edgeEvenFarShell n r, ‖Cn3Torus.psi n mu‖ ^ (4 * t)
        ≤ qSm ^ (4 * t) + qBig ^ (4 * t)
            + Real.exp (-(a * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ)))) := by
  set qG : ℝ := (1 + 2 * r ^ (2 : Nat)) ^ (-(1 : ℝ) / 4)
  set η : ℝ := (1 - qG) / 3
  set qSm : ℝ := (1 + qG) / 2
  set qBig : ℝ := Real.sqrt ((1 + Real.exp (-(8 / Real.pi ^ (2 : Nat)))) / 2)
  set a : ℝ := (4 / Real.pi ^ (2 : Nat)) * η ^ (2 / 3 : ℝ)
  have hqG_lt_one : qG < 1 := by
    have hbase : 1 < 1 + 2 * r ^ (2 : Nat) := by
      nlinarith [sq_pos_of_pos hr]
    have hexp : (-(1 : ℝ) / 4) < 0 := by norm_num
    exact Real.rpow_lt_one_of_one_lt_of_neg hbase hexp
  have hη_pos : 0 < η := by
    dsimp [η]
    linarith
  have hqSm_pos : 0 < qSm := by
    dsimp [qSm, qG]
    positivity
  have hqSm_lt : qSm < 1 := by
    dsimp [qSm]
    linarith
  have hqBig_pos : 0 < qBig := by
    dsimp [qBig]
    apply Real.sqrt_pos.2
    have : 0 < (1 + Real.exp (-(8 / Real.pi ^ (2 : Nat)))) / 2 := by
      positivity
    exact this
  have hqBig_lt : qBig < 1 := by
    have hsq :
        qBig ^ (2 : Nat) = (1 + Real.exp (-(8 / Real.pi ^ (2 : Nat)))) / 2 := by
      dsimp [qBig]
      rw [sq_sqrt]
      positivity
    have hexp_lt : Real.exp (-(8 / Real.pi ^ (2 : Nat))) < 1 := by
      apply Real.exp_lt_one_iff.mpr
      have hcoeff_pos : 0 < 8 / Real.pi ^ (2 : Nat) := by positivity [Real.pi_pos]
      nlinarith
    have hinside_lt : (1 + Real.exp (-(8 / Real.pi ^ (2 : Nat)))) / 2 < 1 := by
      nlinarith
    by_contra hqBig_ge
    have hqBig_ge' : 1 ≤ qBig := by linarith
    have hsq_ge : 1 ≤ qBig ^ (2 : Nat) := by
      nlinarith [hqBig_ge']
    rw [hsq] at hsq_ge
    exact not_le_of_gt hinside_lt hsq_ge
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  refine ⟨qSm, qBig, a, hqSm_pos, hqSm_lt, hqBig_pos, hqBig_lt, ha_pos, ?_⟩
  intro n t hn ht
  let b : ℝ :=
    qSm ^ (4 * t) + qBig ^ (4 * t)
      + Real.exp (-(a * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ))))
  have htex_nonneg : 0 ≤ Cn3Torus.texPrefactor n := by
    unfold Cn3Torus.texPrefactor
    positivity [Real.pi_pos]
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    positivity
  have hf_box :
      MeasureTheory.IntegrableOn
        (fun mu : Cn3Torus.Edge n → ℝ => ‖Cn3Torus.psi n mu‖ ^ (4 * t))
        (edgeBox n (π / 4)) := by
    exact ((Cn3Torus.continuous_psi n).norm.pow (4 * t)).continuousOn.integrableOn_compact
      (edgeBox_isCompact n (π / 4))
  have hg_box :
      MeasureTheory.IntegrableOn
        (fun _ : Cn3Torus.Edge n → ℝ => b)
        (edgeBox n (π / 4)) := by
    exact continuous_const.continuousOn.integrableOn_compact
      (edgeBox_isCompact n (π / 4))
  have hf :
      MeasureTheory.IntegrableOn
        (fun mu : Cn3Torus.Edge n → ℝ => ‖Cn3Torus.psi n mu‖ ^ (4 * t))
        (edgeEvenFarShell n r) :=
    hf_box.mono_set (edgeEvenFarShell_subset_edgeBox n r)
  have hg :
      MeasureTheory.IntegrableOn
        (fun _ : Cn3Torus.Edge n → ℝ => b)
        (edgeEvenFarShell n r) :=
    hg_box.mono_set (edgeEvenFarShell_subset_edgeBox n r)
  have hmeas :
      MeasurableSet
        {mu : Cn3Torus.Edge n → ℝ |
          ‖Cn3Torus.psi n mu‖ ^ (4 * t) ≤ b} := by
    exact measurableSet_le
      (((Cn3Torus.continuous_psi n).norm.pow (4 * t)).measurable)
      measurable_const
  have hpoint :
      ∀ᵐ mu : Cn3Torus.Edge n → ℝ ∂(MeasureTheory.volume.restrict (edgeEvenFarShell n r)),
        ‖Cn3Torus.psi n mu‖ ^ (4 * t) ≤ b := by
    rw [MeasureTheory.ae_restrict_iff hmeas]
    exact Filter.Eventually.of_forall (fun mu hmu => by
      have hshell := (mem_edgeEvenFarShell_iff n r mu).1 hmu
      by_cases hsmallJ : threeHalfInfluenceSumEdge n mu ≤ η
      · have hsmall :
            ‖Cn3Torus.psi n mu‖ ≤ qSm := by
          let lam := matrixOfEdge n mu
          have hdiff := psi_sub_gaussianPsi_le_threeHalfInfluenceSum n lam
          have hgauss := gaussianPsi_norm_bound n lam
          have hsNorm_ge : r ^ (2 : Nat) ≤ sNorm n lam := by
            simpa [lam, sNorm_matrixOfEdge_eq] using hshell.2
          have hgauss' :
              ‖gaussianPsi n lam‖ ≤ qG := by
            calc
              ‖gaussianPsi n lam‖ ≤ (1 + 2 * sNorm n lam) ^ (-(1 : ℝ) / 4) := hgauss
              _ ≤ (1 + 2 * r ^ (2 : Nat)) ^ (-(1 : ℝ) / 4) := by
                    apply Real.rpow_le_rpow_of_nonpos
                    · positivity
                    · nlinarith
                    · norm_num
              _ = qG := by rfl
          calc
            ‖Cn3Torus.psi n mu‖ = ‖(psi n lam - gaussianPsi n lam) + gaussianPsi n lam‖ := by
              rw [← psi_matrixOfEdge_eq]
              congr 1
              ring
            _ ≤ ‖psi n lam - gaussianPsi n lam‖ + ‖gaussianPsi n lam‖ := norm_add_le _ _
            _ ≤ (3 / 2 : ℝ) * threeHalfInfluenceSum n lam + qG := by
                  exact add_le_add hdiff hgauss'
            _ ≤ (3 / 2 : ℝ) * η + qG := by
                  gcongr
                  simpa [lam, threeHalfInfluenceSumEdge_eq] using hsmallJ
            _ = qSm := by
                  dsimp [qSm, η]
                  ring
        have hpow : ‖Cn3Torus.psi n mu‖ ^ (4 * t) ≤ qSm ^ (4 * t) := by
          exact pow_le_pow_left₀ (norm_nonneg _) hsmall (4 * t)
        have hrest_nonneg :
            0 ≤ qBig ^ (4 * t)
                + Real.exp (-(a * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ)))) := by
          positivity
        nlinarith
      · by_cases hbigI : 1 ≤ rowInfluenceMaxEdge n mu
        · have hsq :
              ‖Cn3Torus.psi n mu‖ ^ 2 ≤ qBig ^ (2 : Nat) := by
            have hbase := edgePsi_norm_sq_le_half_one_add_exp_rowInfluenceMax n hn mu hshell.1
            have hexp_le :
                Real.exp (-(8 / Real.pi ^ (2 : Nat)) * rowInfluenceMaxEdge n mu)
                  ≤ Real.exp (-(8 / Real.pi ^ (2 : Nat))) := by
              have hcoeff_pos : 0 < 8 / Real.pi ^ (2 : Nat) := by
                positivity [Real.pi_pos]
              apply Real.exp_le_exp.mpr
              nlinarith
            have hhalf :
                (1 + Real.exp (-(8 / Real.pi ^ (2 : Nat)) * rowInfluenceMaxEdge n mu)) / 2
                  ≤ qBig ^ (2 : Nat) := by
              rw [show qBig ^ (2 : Nat) = (1 + Real.exp (-(8 / Real.pi ^ (2 : Nat)))) / 2 by
                dsimp [qBig]
                rw [sq_sqrt]
                positivity]
              nlinarith
            exact hbase.trans hhalf
          have hpow :
              ‖Cn3Torus.psi n mu‖ ^ (4 * t) ≤ qBig ^ (4 * t) := by
            have hpow' := pow_le_pow_left₀ (by positivity : 0 ≤ ‖Cn3Torus.psi n mu‖ ^ 2) hsq (2 * t)
            convert hpow' using 1 <;> ring_nf
          have hrest_nonneg :
              0 ≤ qSm ^ (4 * t)
                  + Real.exp (-(a * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ)))) := by
            positivity
          nlinarith
        · have hmidI : rowInfluenceMaxEdge n mu < 1 := lt_of_not_ge hbigI
          have hn0 : 0 < n := by omega
          have hI_lower :
              (η / (n : ℝ)) ^ (2 / 3 : ℝ) ≤ rowInfluenceMaxEdge n mu :=
            rowInfluenceMaxEdge_ge_eta_div_n_two_thirds n hn0 mu hη_pos
              (lt_of_not_ge hsmallJ)
          have hsq :
              ‖Cn3Torus.psi n mu‖ ^ 2
                ≤ Real.exp (-(2 / Real.pi ^ (2 : Nat)) * rowInfluenceMaxEdge n mu) := by
            calc
              ‖Cn3Torus.psi n mu‖ ^ 2
                  ≤ (1 + Real.exp (-(8 / Real.pi ^ (2 : Nat)) * rowInfluenceMaxEdge n mu)) / 2 :=
                    edgePsi_norm_sq_le_half_one_add_exp_rowInfluenceMax n hn mu hshell.1
              _ ≤ Real.exp (-(2 / Real.pi ^ (2 : Nat)) * rowInfluenceMaxEdge n mu) := by
                    apply avg_one_exp_neg_eight_div_pi_sq_le_exp_neg_two_div_pi_sq
                    · simpa [rowInfluenceMaxEdge] using
                        maxInfluence_nonneg n (matrixOfEdge n mu)
                    · linarith
          have hpow :
              ‖Cn3Torus.psi n mu‖ ^ (4 * t)
                ≤ Real.exp (-(a * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ)))) := by
            have hpow' :=
              pow_le_pow_left₀ (by positivity : 0 ≤ ‖Cn3Torus.psi n mu‖ ^ 2) hsq (2 * t)
            have hpow_exp :
                (Real.exp (-(2 / Real.pi ^ (2 : Nat)) * rowInfluenceMaxEdge n mu)) ^ (2 * t)
                  = Real.exp (-(4 / Real.pi ^ (2 : Nat)) * (t : ℝ) * rowInfluenceMaxEdge n mu) := by
              rw [← Real.exp_nat_mul]
              congr 1
              norm_num [Nat.cast_mul]
              ring
            have hcoeff :
                a * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ))
                  ≤ (4 / Real.pi ^ (2 : Nat)) * (t : ℝ) * rowInfluenceMaxEdge n mu := by
              have htmp :
                  (4 / Real.pi ^ (2 : Nat)) * (t : ℝ) * ((η / (n : ℝ)) ^ (2 / 3 : ℝ))
                    ≤ (4 / Real.pi ^ (2 : Nat)) * (t : ℝ) * rowInfluenceMaxEdge n mu := by
                gcongr
              have ha_eq :
                  a * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ))
                    = (4 / Real.pi ^ (2 : Nat)) * (t : ℝ) * ((η / (n : ℝ)) ^ (2 / 3 : ℝ)) := by
                calc
                  a * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ))
                      = (4 / Real.pi ^ (2 : Nat)) * (η ^ (2 / 3 : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ))) * (t : ℝ) := by
                          dsimp [a]
                          ring
                  _ = (4 / Real.pi ^ (2 : Nat)) * ((η / (n : ℝ)) ^ (2 / 3 : ℝ)) * (t : ℝ) := by
                          rw [← Real.div_rpow (le_of_lt hη_pos) (by positivity : 0 ≤ (n : ℝ))]
                  _ = (4 / Real.pi ^ (2 : Nat)) * (t : ℝ) * ((η / (n : ℝ)) ^ (2 / 3 : ℝ)) := by
                          ring
              simpa [ha_eq] using htmp
            have hexp_le :
                Real.exp (-(4 / Real.pi ^ (2 : Nat)) * (t : ℝ) * rowInfluenceMaxEdge n mu)
                  ≤ Real.exp (-(a * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ)))) := by
              apply Real.exp_le_exp.mpr
              nlinarith
            have hpow'' : ‖Cn3Torus.psi n mu‖ ^ (4 * t)
                ≤ Real.exp (-(4 / Real.pi ^ (2 : Nat)) * (t : ℝ) * rowInfluenceMaxEdge n mu) := by
              calc
                ‖Cn3Torus.psi n mu‖ ^ (4 * t)
                    = (‖Cn3Torus.psi n mu‖ ^ 2) ^ (2 * t) := by ring_nf
                _ ≤ Real.exp (-(2 / Real.pi ^ (2 : Nat)) * rowInfluenceMaxEdge n mu) ^ (2 * t) := hpow'
                _ = Real.exp (-(4 / Real.pi ^ (2 : Nat)) * (t : ℝ) * rowInfluenceMaxEdge n mu) := hpow_exp
            exact hpow''.trans hexp_le
          have hrest_nonneg : 0 ≤ qSm ^ (4 * t) + qBig ^ (4 * t) := by positivity
          have hbranch :
              ‖Cn3Torus.psi n mu‖ ^ (4 * t) ≤ b := by
            dsimp [b]
            nlinarith
          exact hbranch
      )
  have hint := integral_mono_ae hf hg hpoint
  have htop : MeasureTheory.volume (edgeBox n (π / 4)) ≠ ⊤ := by
    exact ne_of_lt (edgeBox_isCompact n (π / 4)).measure_lt_top
  have hvol_le :
      (MeasureTheory.volume (edgeEvenFarShell n r)).toReal
        ≤ (MeasureTheory.volume (edgeBox n (π / 4))).toReal := by
    exact ENNReal.toReal_mono htop (MeasureTheory.measure_mono (edgeEvenFarShell_subset_edgeBox n r))
  have hconst_eval :
      ∫ _mu in edgeEvenFarShell n r, b
        = MeasureTheory.volume.real (edgeEvenFarShell n r) * b := by
    simp [MeasureTheory.integral_const, mul_comm]
  have hreal_eq :
      MeasureTheory.volume.real (edgeEvenFarShell n r)
        = (MeasureTheory.volume (edgeEvenFarShell n r)).toReal := by
    simp [MeasureTheory.Measure.real_def]
  have hconst_bound :
      ∫ _mu in edgeEvenFarShell n r, b
        ≤ (MeasureTheory.volume (edgeBox n (π / 4))).toReal * b := by
    rw [hconst_eval, hreal_eq]
    exact mul_le_mul_of_nonneg_right hvol_le hb_nonneg
  calc
    Cn3Torus.texPrefactor n * ∫ mu in edgeEvenFarShell n r, ‖Cn3Torus.psi n mu‖ ^ (4 * t)
        ≤ Cn3Torus.texPrefactor n * ∫ _mu in edgeEvenFarShell n r, b := by
            exact mul_le_mul_of_nonneg_left hint htex_nonneg
    _ ≤ Cn3Torus.texPrefactor n * ((MeasureTheory.volume (edgeBox n (π / 4))).toReal * b) := by
          exact mul_le_mul_of_nonneg_left hconst_bound htex_nonneg
    _ = (Cn3Torus.texPrefactor n * (MeasureTheory.volume (edgeBox n (π / 4))).toReal) * b := by
          ring
    _ ≤ 1 * b := by
          exact mul_le_mul_of_nonneg_right
            (texPrefactor_mul_edgeBox_pi_div_four_volume_le_one n hn) hb_nonneg
    _ = qSm ^ (4 * t) + qBig ^ (4 * t)
          + Real.exp (-(a * (t : ℝ) / ((n : ℝ) ^ (2 / 3 : ℝ)))) := by
          simp [b]
