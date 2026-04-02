import RequestProject.HadamardCn3Defs

/-!
# Torus / Count Bridge For The Cn^3 Formalization

This module contains the torus-coordinate model, the Fourier inversion bridge,
and the normalized-count identification used throughout the formalization.

Readers primarily interested in the combinatorial-to-analytic translation should
start with:

- `Cn3Torus.lem_fourier_inversion_all`
- `torusIntegralC_eq_volume_mul_hadamardCount`
- `normalizedCount_eq_normalizedTargetIntegral`
-/

noncomputable section

open Real MeasureTheory Filter Finset Topology
open scoped Pointwise

set_option linter.unusedVariables false

namespace Cn3Torus

/-- Edge-coordinate dimension. -/
def d (n : ℕ) : ℕ := Nat.choose n 2

/-- Strict upper-triangular coordinates, viewed as edges of `K_n`. -/
def Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

instance instFintypeEdge (n : ℕ) : Fintype (Edge n) := by
  dsimp [Edge]
  infer_instance

instance instDecidableEqEdge (n : ℕ) : DecidableEq (Edge n) := by
  dsimp [Edge]
  infer_instance

/-- Identify an edge with the corresponding non-diagonal unordered pair. -/
noncomputable def edgeToSym2Subtype {n : ℕ} (e : Edge n) :
    {a : Sym2 (Fin n) // ¬ a.IsDiag} := by
  refine ⟨Sym2.mk (e.1.1, e.1.2), ?_⟩
  rcases e with ⟨⟨i, j⟩, hij⟩
  intro hdiag
  have hijEq : i = j := by
    simpa [Sym2.IsDiag] using hdiag
  exact (lt_irrefl i) (hijEq ▸ hij)

/-- The edge-coordinate space has dimension `n.choose 2`. -/
lemma card_Edge_eq_d (n : ℕ) : Fintype.card (Edge n) = d n := by
  have hinj : Function.Injective (@edgeToSym2Subtype n) := by
    intro e1 e2 h
    rcases e1 with ⟨⟨a, b⟩, hab⟩
    rcases e2 with ⟨⟨c, d⟩, hcd⟩
    change (⟨Sym2.mk (a, b), ?_⟩ : {a : Sym2 (Fin n) // ¬ a.IsDiag}) =
        (⟨Sym2.mk (c, d), ?_⟩ : {a : Sym2 (Fin n) // ¬ a.IsDiag}) at h
    have hmk : Sym2.mk (a, b) = Sym2.mk (c, d) := Subtype.ext_iff.mp h
    rcases Sym2.eq_iff.mp hmk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1
      subst h2
      rfl
    · exfalso
      have hba : b < a := by
        simpa [h1, h2] using hcd
      exact (lt_irrefl a) (lt_trans hab hba)
  have hsurj : Function.Surjective (@edgeToSym2Subtype n) := by
    intro z
    rcases z with ⟨z, hz⟩
    rcases Sym2.exists.mp (show ∃ x : Sym2 (Fin n), x = z from ⟨z, rfl⟩) with ⟨a, b, hab⟩
    have hneq : a ≠ b := by
      intro hEq
      apply hz
      rw [← hab]
      simpa [Sym2.IsDiag, hEq]
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · refine ⟨⟨(a, b), hlt⟩, ?_⟩
      apply Subtype.ext
      dsimp [edgeToSym2Subtype]
      exact hab
    · refine ⟨⟨(b, a), hgt⟩, ?_⟩
      apply Subtype.ext
      dsimp [edgeToSym2Subtype]
      rw [Sym2.eq_swap]
      exact hab
  calc
    Fintype.card (Edge n) = Fintype.card {a : Sym2 (Fin n) // ¬ a.IsDiag} := by
      exact Fintype.card_of_bijective (f := edgeToSym2Subtype (n := n))
        ⟨hinj, hsurj⟩
    _ = Nat.choose (Fintype.card (Fin n)) 2 := Sym2.card_subtype_not_diag
    _ = d n := by
      simp [d]

/-- Boolean spin encoding, matching the edge-model torus setup. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Edge monomials attached to a Boolean sign vector. -/
def Z {n : ℕ} (y : Fin n → Bool) : Edge n → ℝ :=
  fun e => spin (y e.1.1) * spin (y e.1.2)

/-- The edge-model phase. -/
def phase {n : ℕ} (lam : Edge n → ℝ) (y : Fin n → Bool) : ℝ :=
  ∑ e : Edge n, lam e * Z y e

/-- Edge-model characteristic function. -/
def psi (n : ℕ) (lam : Edge n → ℝ) : ℂ :=
  (∑ y : Fin n → Bool, Complex.exp (Complex.I * (phase lam y : ℂ))) / (2 ^ n : ℂ)

lemma continuous_psi (n : ℕ) : Continuous (psi n) := by
  unfold psi
  have hsum :
      Continuous
        (fun lam : Edge n → ℝ =>
          ∑ y : Fin n → Bool, Complex.exp (Complex.I * (phase lam y : ℂ))) := by
    refine continuous_finset_sum (s := (Finset.univ : Finset (Fin n → Bool))) ?_
    intro y hy
    have hphase : Continuous (fun lam : Edge n → ℝ => phase lam y) := by
      unfold phase
      fun_prop
    exact Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hphase))
  simpa [div_eq_mul_inv] using hsum.mul continuous_const

/-- Edge-model squared norm. -/
def sqNormEdge (n : ℕ) (lam : Edge n → ℝ) : ℝ :=
  ∑ e : Edge n, (lam e) ^ (2 : Nat)

lemma continuous_sqNormEdge (n : ℕ) : Continuous (sqNormEdge n) := by
  unfold sqNormEdge
  fun_prop

/-- The torus fundamental box of side length `2π` in edge coordinates. -/
def torusBox (n : ℕ) : Set (Edge n → ℝ) :=
  Set.pi Set.univ (fun _ : Edge n => Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4))

private lemma torusBox_isCompact (n : ℕ) : IsCompact (torusBox n) := by
  unfold torusBox
  simpa [Set.pi_univ_Icc] using
    (isCompact_Icc :
      IsCompact (Set.Icc (fun _ : Edge n => (-(Real.pi / 4))) (fun _ : Edge n => (7 * Real.pi / 4))))

/-- Complex torus integral before taking real parts. -/
def torusIntegralC (n m : ℕ) : ℂ :=
  ∫ lam in torusBox n, psi n lam ^ m

/-- Real quarter-scale torus integral. -/
def targetIntegral (n t : ℕ) : ℝ :=
  ∫ lam in torusBox n, Complex.re (psi n lam ^ (4 * t))

/-- Torus integral normalized by the torus volume `(2π)^d`. -/
def normalizedTargetIntegral (n t : ℕ) : ℝ :=
  (1 / ((2 * Real.pi) ^ (d n : Nat) : ℝ)) * targetIntegral n t

/-- Edge-count as a real number. -/
def edgeCount (n : ℕ) : ℝ := Fintype.card (Edge n)

/-- Fixed local radius used in the torus decomposition package. -/
def delta : ℝ := 3 * Real.pi / 16

lemma delta_pos : 0 < delta := by
  unfold delta
  positivity [Real.pi_pos]

private lemma delta_lt_pi_div_two : delta < Real.pi / 2 := by
  unfold delta
  linarith [Real.pi_pos]

/-- Local box around a lattice point in edge coordinates. -/
def localBox (n : ℕ) : Set (Edge n → ℝ) :=
  Set.pi Set.univ (fun _ : Edge n => Set.Icc (-delta) delta)

/-- A single coordinate square is bounded by the total edge squared norm. -/
lemma sqNormEdge_coord_sq_le (n : ℕ) (lam : Edge n → ℝ) (e : Edge n) :
    (lam e) ^ (2 : Nat) ≤ sqNormEdge n lam := by
  unfold sqNormEdge
  have hnonneg : ∀ e' ∈ (Finset.univ : Finset (Edge n)), 0 ≤ (lam e') ^ (2 : Nat) := by
    intro e' he'
    positivity
  simpa using
    (Finset.single_le_sum hnonneg (by simp : e ∈ (Finset.univ : Finset (Edge n))))

lemma localBox_isCompact (n : ℕ) : IsCompact (localBox n) := by
  unfold localBox
  simpa [Set.pi_univ_Icc] using
    (isCompact_Icc :
      IsCompact (Set.Icc (fun _ : Edge n => (-delta)) (fun _ : Edge n => delta)))

/-- Local integral over the core box. -/
def localIntegral (n t : ℕ) : ℝ :=
  ∫ lam in localBox n, Complex.re (psi n lam ^ (4 * t))

/-- Uniform remainder term from the torus decomposition package. -/
private def remainderTerm (t : ℕ) : ℝ :=
  (Real.cos delta) ^ (4 * t)

/-- The tex prefactor converting local integrals to normalized torus scale. -/
def texPrefactor (n : ℕ) : ℝ :=
  (2 ^ (2 * d n - n + 1) : ℝ) / ((2 * Real.pi) ^ (d n : Nat))

lemma n_le_two_mul_d (n : ℕ) (hn : 3 ≤ n) : n ≤ 2 * d n := by
  have htwo : 2 * d n = n * (n - 1) := by
    unfold d
    rw [Nat.choose_two_right]
    have hdvd : 2 ∣ n * (n - 1) := by
      rcases (Nat.even_mul_pred_self n) with ⟨k, hk⟩
      refine ⟨k, ?_⟩
      omega
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.mul_div_cancel' hdvd)
  rw [htwo]
  have h1 : 1 ≤ n - 1 := by omega
  have h2 : n * 1 ≤ n * (n - 1) := Nat.mul_le_mul_left _ h1
  simpa using h2

private lemma measurableSet_torusBox (n : ℕ) : MeasurableSet (torusBox n) := by
  unfold torusBox
  simp

private lemma volume_torusBox_eq (n : ℕ) :
    MeasureTheory.volume (torusBox n)
      = ENNReal.ofReal (((2 * Real.pi) ^ (d n : Nat) : ℝ)) := by
  unfold torusBox
  calc
    MeasureTheory.volume (Set.univ.pi (fun _ : Edge n => Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4)))
      = ∏ _ : Edge n, MeasureTheory.volume (Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4)) := by
          simpa using
            (MeasureTheory.volume_pi_pi
              (s := fun _ : Edge n => Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4)))
    _ = ∏ _ : Edge n, ENNReal.ofReal (2 * Real.pi) := by
          have hlen : (7 * Real.pi / 4) - (-(Real.pi / 4)) = 2 * Real.pi := by ring
          simp [Real.volume_Icc, hlen]
    _ = (ENNReal.ofReal (2 * Real.pi)) ^ Fintype.card (Edge n) := by
          simp [Finset.prod_const]
    _ = ENNReal.ofReal (((2 * Real.pi) ^ (Fintype.card (Edge n)) : ℝ)) := by
          symm
          exact ENNReal.ofReal_pow (by positivity [Real.pi_pos]) (Fintype.card (Edge n))
    _ = ENNReal.ofReal (((2 * Real.pi) ^ (d n : Nat) : ℝ)) := by
          simp [card_Edge_eq_d]

private lemma volume_torusBox_toReal (n : ℕ) :
    (MeasureTheory.volume (torusBox n)).toReal = ((2 * Real.pi) ^ (d n : Nat) : ℝ) := by
  rw [volume_torusBox_eq n]
  exact ENNReal.toReal_ofReal (by positivity [Real.pi_pos])

/-- Fourier inversion on the quarter-scale torus model.

This identifies the real-valued target integral used in the paper with the real
part of the complex torus integral `torusIntegralC`. -/
lemma lem_fourier_inversion_all (n m : ℕ) :
    Complex.re (torusIntegralC n m) =
      (∫ lam in torusBox n, Complex.re (psi n lam ^ m)) := by
  have hpow_cont : Continuous (fun lam : Edge n → ℝ => psi n lam ^ m) :=
    (continuous_psi n).pow m
  have hpow_int :
      MeasureTheory.IntegrableOn (fun lam : Edge n → ℝ => psi n lam ^ m) (torusBox n) :=
    hpow_cont.continuousOn.integrableOn_compact (torusBox_isCompact n)
  have hre :
      (∫ lam in torusBox n, Complex.re (psi n lam ^ m))
        = Complex.re (∫ lam in torusBox n, psi n lam ^ m) := by
    exact integral_re hpow_int
  simpa [torusIntegralC] using hre.symm

/-- One-dimensional torus character at integer frequency. -/
private def char1D (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((k : ℂ) * ((x : ℂ) * Complex.I))

private lemma char1D_periodic (k : ℤ) : Function.Periodic (char1D k) (2 * Real.pi) := by
  intro x
  unfold char1D
  calc
    Complex.exp ((k : ℂ) * (((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I))
        = Complex.exp ((k : ℂ) * ((x : ℂ) * Complex.I) + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
            congr 1
            calc
              (k : ℂ) * (((x + 2 * Real.pi : ℝ) : ℂ) * Complex.I)
                  = (k : ℂ) * ((((x : ℂ) + (2 * (Real.pi : ℂ))) * Complex.I)) := by norm_num
              _ = (k : ℂ) * (((x : ℂ) * Complex.I) + (2 * (Real.pi : ℂ) * Complex.I)) := by rw [add_mul]
              _ = (k : ℂ) * ((x : ℂ) * Complex.I) + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by rw [mul_add]
    _ = Complex.exp ((k : ℂ) * ((x : ℂ) * Complex.I)) *
          Complex.exp ((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
            rw [Complex.exp_add]
    _ = Complex.exp ((k : ℂ) * ((x : ℂ) * Complex.I)) * 1 := by
          rw [Complex.exp_int_mul_two_pi_mul_I]
    _ = Complex.exp ((k : ℂ) * ((x : ℂ) * Complex.I)) := by simp

private lemma char1D_shift_neg (k : ℤ) (hk : k ≠ 0) :
    ∀ x, char1D k (x + Real.pi / (k : ℝ)) = - char1D k x := by
  have hkC : (k : ℂ) ≠ 0 := by
    exact_mod_cast hk
  intro x
  unfold char1D
  calc
    Complex.exp ((k : ℂ) * ((((x + Real.pi / (k : ℝ) : ℝ) : ℂ) * Complex.I)))
        = Complex.exp ((k : ℂ) * ((x : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I) := by
            congr 1
            calc
              (k : ℂ) * (((x + Real.pi / (k : ℝ) : ℝ) : ℂ) * Complex.I)
                  = (k : ℂ) * ((((x : ℂ) + ((Real.pi / (k : ℝ) : ℝ) : ℂ)) * Complex.I)) := by norm_num
              _ = (k : ℂ) * (((x : ℂ) * Complex.I) + ((((Real.pi / (k : ℝ) : ℝ) : ℂ)) * Complex.I)) := by rw [add_mul]
              _ = (k : ℂ) * ((x : ℂ) * Complex.I) + (k : ℂ) * ((((Real.pi / (k : ℝ) : ℝ) : ℂ)) * Complex.I) := by rw [mul_add]
              _ = (k : ℂ) * ((x : ℂ) * Complex.I) + ((Real.pi : ℂ) * Complex.I) := by
                    congr 1
                    calc
                      (k : ℂ) * (((Real.pi / (k : ℝ) : ℝ) : ℂ) * Complex.I)
                          = ((k : ℂ) * (((Real.pi / (k : ℝ) : ℝ) : ℂ))) * Complex.I := by ring
                      _ = (((k : ℂ) * ((Real.pi : ℂ) / (k : ℂ)))) * Complex.I := by
                            rw [Complex.ofReal_div]
                            simp
                      _ = (Real.pi : ℂ) * Complex.I := by
                            field_simp [hkC]
    _ = Complex.exp ((k : ℂ) * ((x : ℂ) * Complex.I)) * Complex.exp ((Real.pi : ℂ) * Complex.I) := by
          rw [Complex.exp_add]
    _ = Complex.exp ((k : ℂ) * ((x : ℂ) * Complex.I)) * (-1) := by
          rw [Complex.exp_pi_mul_I]
    _ = - Complex.exp ((k : ℂ) * ((x : ℂ) * Complex.I)) := by ring

private lemma intervalIntegral_char1D_eq_zero (k : ℤ) (hk : k ≠ 0) :
    ∫ x in (-(Real.pi / 4))..(7 * Real.pi / 4), char1D k x = 0 := by
  let a : ℝ := -(Real.pi / 4)
  let s : ℝ := Real.pi / (k : ℝ)
  have hshift : ∀ x, char1D k (x + s) = - char1D k x := by
    simpa [s] using char1D_shift_neg k hk
  have hsame :
      ∫ x in a..a + 2 * Real.pi, char1D k (x + s)
        = ∫ x in a..a + 2 * Real.pi, char1D k x := by
    calc
      ∫ x in a..a + 2 * Real.pi, char1D k (x + s)
          = ∫ x in a + s..(a + 2 * Real.pi) + s, char1D k x := by
              simpa using (intervalIntegral.integral_comp_add_right (f := char1D k) (a := a) (b := a + 2 * Real.pi) s)
      _ = ∫ x in (a + s)..(a + s) + 2 * Real.pi, char1D k x := by ring_nf
      _ = ∫ x in a..a + 2 * Real.pi, char1D k x := by
            symm
            exact (char1D_periodic k).intervalIntegral_add_eq a (a + s)
  have hneg :
      ∫ x in a..a + 2 * Real.pi, char1D k (x + s)
        = - ∫ x in a..a + 2 * Real.pi, char1D k x := by
    rw [intervalIntegral.integral_congr (f := fun x => char1D k (x + s))
      (g := fun x => - char1D k x)]
    · simp [intervalIntegral.integral_neg]
    · intro x hx
      simp [hshift x]
  have heq :
      ∫ x in a..a + 2 * Real.pi, char1D k x
        = - ∫ x in a..a + 2 * Real.pi, char1D k x := by
    simpa [hsame] using hneg
  have hint : ∫ x in a..a + 2 * Real.pi, char1D k x = 0 := by
    simpa using congrArg (fun z => z + ∫ x in a..a + 2 * Real.pi, char1D k x) heq
  have hab : a + 2 * Real.pi = 7 * Real.pi / 4 := by
    unfold a
    ring
  simpa [a, hab] using hint

private lemma intervalIntegral_char1D (k : ℤ) :
    ∫ x in (-(Real.pi / 4))..(7 * Real.pi / 4), char1D k x
      = if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst hk
    have hab : (7 * Real.pi / 4) - (-(Real.pi / 4)) = 2 * Real.pi := by ring
    simp [char1D, intervalIntegral.integral_const, hab]
  · simp [hk, intervalIntegral_char1D_eq_zero]

private abbrev EdgeEq {n : ℕ} (e0 : Edge n) := {e : Edge n // e = e0}
abbrev EdgeNe {n : ℕ} (e0 : Edge n) := {e : Edge n // e ≠ e0}

private def edgeEqEquivUnit {n : ℕ} (e0 : Edge n) : EdgeEq e0 ≃ Unit where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => ⟨e0, rfl⟩
  left_inv := by
    intro a
    rcases a with ⟨a, rfl⟩
    rfl
  right_inv := by
    intro u
    cases u
    rfl

private def splitAtEdge {n : ℕ} (e0 : Edge n) : (Edge n → ℝ) ≃ᵐ ℝ × (EdgeNe e0 → ℝ) := by
  let e : Edge n ≃ EdgeEq e0 ⊕ EdgeNe e0 :=
    (Equiv.sumCompl (fun e : Edge n => e = e0)).symm
  let reindex1 : (Edge n → ℝ) ≃ᵐ (EdgeEq e0 ⊕ EdgeNe e0 → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : EdgeEq e0 ⊕ EdgeNe e0 => ℝ) e
  let reindex2 : (EdgeEq e0 ⊕ EdgeNe e0 → ℝ) ≃ᵐ (EdgeEq e0 → ℝ) × (EdgeNe e0 → ℝ) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : EdgeEq e0 ⊕ EdgeNe e0 => ℝ)
  let reindex3 : (EdgeEq e0 → ℝ) × (EdgeNe e0 → ℝ) ≃ᵐ (Unit → ℝ) × (EdgeNe e0 → ℝ) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ : Unit => ℝ) (edgeEqEquivUnit e0))
      (MeasurableEquiv.refl (EdgeNe e0 → ℝ))
  let reindex4 : (Unit → ℝ) × (EdgeNe e0 → ℝ) ≃ᵐ ℝ × (EdgeNe e0 → ℝ) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique Unit ℝ)
      (MeasurableEquiv.refl (EdgeNe e0 → ℝ))
  exact reindex1.trans (reindex2.trans (reindex3.trans reindex4))

private lemma splitAtEdge_fst {n : ℕ} (e0 : Edge n) (x : Edge n → ℝ) :
    (splitAtEdge e0 x).1 = x e0 := by
  unfold splitAtEdge
  let e : Edge n ≃ EdgeEq e0 ⊕ EdgeNe e0 :=
    (Equiv.sumCompl (fun e : Edge n => e = e0)).symm
  let reindex1 : (Edge n → ℝ) ≃ᵐ (EdgeEq e0 ⊕ EdgeNe e0 → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : EdgeEq e0 ⊕ EdgeNe e0 => ℝ) e
  let reindex2 : (EdgeEq e0 ⊕ EdgeNe e0 → ℝ) ≃ᵐ (EdgeEq e0 → ℝ) × (EdgeNe e0 → ℝ) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : EdgeEq e0 ⊕ EdgeNe e0 => ℝ)
  let reindex3 : (EdgeEq e0 → ℝ) × (EdgeNe e0 → ℝ) ≃ᵐ (Unit → ℝ) × (EdgeNe e0 → ℝ) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ : Unit => ℝ) (edgeEqEquivUnit e0))
      (MeasurableEquiv.refl (EdgeNe e0 → ℝ))
  let reindex4 : (Unit → ℝ) × (EdgeNe e0 → ℝ) ≃ᵐ ℝ × (EdgeNe e0 → ℝ) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique Unit ℝ)
      (MeasurableEquiv.refl (EdgeNe e0 → ℝ))
  have h1 : reindex1 x (Sum.inl ⟨e0, rfl⟩) = x e0 := by
    simpa [reindex1] using
      (Equiv.piCongrLeft_apply (P := fun _ : EdgeEq e0 ⊕ EdgeNe e0 => ℝ) e x (Sum.inl ⟨e0, rfl⟩))
  have h2 : (reindex2 (reindex1 x)).1 ⟨e0, rfl⟩ = reindex1 x (Sum.inl ⟨e0, rfl⟩) := by
    simp [reindex2, MeasurableEquiv.sumPiEquivProdPi]
  have h3 : (reindex3 (reindex2 (reindex1 x))).1 PUnit.unit = (reindex2 (reindex1 x)).1 ⟨e0, rfl⟩ := by
    simpa [reindex3] using
      (Equiv.piCongrLeft_apply (P := fun _ : Unit => ℝ) (edgeEqEquivUnit e0)
        ((reindex2 (reindex1 x)).1) PUnit.unit)
  have h4 : (reindex4 (reindex3 (reindex2 (reindex1 x)))).1 = (reindex3 (reindex2 (reindex1 x))).1 PUnit.unit := by
    change (MeasurableEquiv.funUnique Unit ℝ) ((reindex3 (reindex2 (reindex1 x))).1) = _
    rfl
  calc
    (reindex4 (reindex3 (reindex2 (reindex1 x)))).1
        = (reindex3 (reindex2 (reindex1 x))).1 PUnit.unit := h4
    _ = (reindex2 (reindex1 x)).1 ⟨e0, rfl⟩ := h3
    _ = reindex1 x (Sum.inl ⟨e0, rfl⟩) := h2
    _ = x e0 := h1

private lemma splitAtEdge_snd {n : ℕ} (e0 : Edge n) (x : Edge n → ℝ) (ee : EdgeNe e0) :
    (splitAtEdge e0 x).2 ee = x ee.1 := by
  unfold splitAtEdge
  let e : Edge n ≃ EdgeEq e0 ⊕ EdgeNe e0 :=
    (Equiv.sumCompl (fun e : Edge n => e = e0)).symm
  let reindex1 : (Edge n → ℝ) ≃ᵐ (EdgeEq e0 ⊕ EdgeNe e0 → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : EdgeEq e0 ⊕ EdgeNe e0 => ℝ) e
  let reindex2 : (EdgeEq e0 ⊕ EdgeNe e0 → ℝ) ≃ᵐ (EdgeEq e0 → ℝ) × (EdgeNe e0 → ℝ) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : EdgeEq e0 ⊕ EdgeNe e0 => ℝ)
  let reindex3 : (EdgeEq e0 → ℝ) × (EdgeNe e0 → ℝ) ≃ᵐ (Unit → ℝ) × (EdgeNe e0 → ℝ) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ : Unit => ℝ) (edgeEqEquivUnit e0))
      (MeasurableEquiv.refl (EdgeNe e0 → ℝ))
  let reindex4 : (Unit → ℝ) × (EdgeNe e0 → ℝ) ≃ᵐ ℝ × (EdgeNe e0 → ℝ) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique Unit ℝ)
      (MeasurableEquiv.refl (EdgeNe e0 → ℝ))
  have h1 : reindex1 x (Sum.inr ee) = x ee.1 := by
    simpa [reindex1] using
      (Equiv.piCongrLeft_apply (P := fun _ : EdgeEq e0 ⊕ EdgeNe e0 => ℝ) e x (Sum.inr ee))
  have h2 : (reindex2 (reindex1 x)).2 ee = reindex1 x (Sum.inr ee) := by
    simp [reindex2, MeasurableEquiv.sumPiEquivProdPi]
  have h3 : (reindex3 (reindex2 (reindex1 x))).2 ee = (reindex2 (reindex1 x)).2 ee := by
    rfl
  have h4 : (reindex4 (reindex3 (reindex2 (reindex1 x)))).2 ee = (reindex3 (reindex2 (reindex1 x))).2 ee := by
    rfl
  calc
    (reindex4 (reindex3 (reindex2 (reindex1 x)))).2 ee
        = (reindex3 (reindex2 (reindex1 x))).2 ee := h4
    _ = (reindex2 (reindex1 x)).2 ee := h3
    _ = reindex1 x (Sum.inr ee) := h2
    _ = x ee.1 := h1

/-- The singleton-coordinate collapse on `Unit → ℝ` preserves volume. -/
private lemma volume_measurePreserving_funUnique_real_aux :
    MeasureTheory.MeasurePreserving (MeasurableEquiv.funUnique Unit ℝ)
      MeasureTheory.volume MeasureTheory.volume := by
  refine MeasureTheory.MeasurePreserving.mk
    (MeasurableEquiv.funUnique Unit ℝ).measurable ?_
  ext s hs
  rw [MeasureTheory.Measure.map_apply
      (MeasurableEquiv.funUnique Unit ℝ).measurable hs]
  rw [MeasureTheory.volume_pi]
  change (MeasureTheory.Measure.pi (fun _ : Unit => MeasureTheory.volume))
      ((fun f : Unit → ℝ => f PUnit.unit) ⁻¹' s) = MeasureTheory.volume s
  have hpre :
      ((fun f : Unit → ℝ => f PUnit.unit) ⁻¹' s) = Set.univ.pi (fun _ : Unit => s) := by
    ext f
    constructor
    · intro hf
      simp [Set.mem_pi]
      intro i
      simpa using hf
    · intro hf
      have h := hf PUnit.unit
      simpa using h
  rw [hpre, MeasureTheory.Measure.pi_pi]
  simp

private lemma splitAtEdge_measurePreserving {n : ℕ} (e0 : Edge n) :
    MeasureTheory.MeasurePreserving (splitAtEdge e0) MeasureTheory.volume MeasureTheory.volume := by
  unfold splitAtEdge
  let e : Edge n ≃ EdgeEq e0 ⊕ EdgeNe e0 :=
    (Equiv.sumCompl (fun e : Edge n => e = e0)).symm
  let reindex1 : (Edge n → ℝ) ≃ᵐ (EdgeEq e0 ⊕ EdgeNe e0 → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : EdgeEq e0 ⊕ EdgeNe e0 => ℝ) e
  let reindex2 : (EdgeEq e0 ⊕ EdgeNe e0 → ℝ) ≃ᵐ (EdgeEq e0 → ℝ) × (EdgeNe e0 → ℝ) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ : EdgeEq e0 ⊕ EdgeNe e0 => ℝ)
  let reindex3 : (EdgeEq e0 → ℝ) × (EdgeNe e0 → ℝ) ≃ᵐ (Unit → ℝ) × (EdgeNe e0 → ℝ) :=
    MeasurableEquiv.prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ : Unit => ℝ) (edgeEqEquivUnit e0))
      (MeasurableEquiv.refl (EdgeNe e0 → ℝ))
  let reindex4 : (Unit → ℝ) × (EdgeNe e0 → ℝ) ≃ᵐ ℝ × (EdgeNe e0 → ℝ) :=
    MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique Unit ℝ)
      (MeasurableEquiv.refl (EdgeNe e0 → ℝ))
  have hpres1 :
      MeasureTheory.MeasurePreserving reindex1 MeasureTheory.volume MeasureTheory.volume := by
    simpa [reindex1] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : EdgeEq e0 ⊕ EdgeNe e0 => ℝ) e)
  have hpres2 :
      MeasureTheory.MeasurePreserving reindex2 MeasureTheory.volume MeasureTheory.volume := by
    simpa [reindex2] using
      (MeasureTheory.volume_measurePreserving_sumPiEquivProdPi
        (fun _ : EdgeEq e0 ⊕ EdgeNe e0 => ℝ))
  have hpres3 :
      MeasureTheory.MeasurePreserving reindex3 MeasureTheory.volume MeasureTheory.volume := by
    simpa [reindex3, MeasurableEquiv.prodCongr] using
      ((MeasureTheory.volume_measurePreserving_piCongrLeft
          (fun _ : Unit => ℝ) (edgeEqEquivUnit e0)).prod
        (MeasureTheory.MeasurePreserving.id
          (MeasureTheory.volume : MeasureTheory.Measure (EdgeNe e0 → ℝ))))
  have hpres4 :
      MeasureTheory.MeasurePreserving reindex4 MeasureTheory.volume MeasureTheory.volume := by
    simpa [reindex4, MeasurableEquiv.prodCongr] using
      (volume_measurePreserving_funUnique_real_aux.prod
        (MeasureTheory.MeasurePreserving.id
          (MeasureTheory.volume : MeasureTheory.Measure (EdgeNe e0 → ℝ))))
  exact hpres4.comp (hpres3.comp (hpres2.comp hpres1))

/-- Fourier character associated to an integer edge frequency. -/
private def torusCharacter {n : ℕ} (m : Edge n → ℤ) (lam : Edge n → ℝ) : ℂ :=
  Complex.exp (∑ e : Edge n, ((m e : ℂ) * ((lam e : ℂ) * Complex.I)))

private lemma torusCharacter_split {n : ℕ} (e0 : Edge n) (m : Edge n → ℤ) (x : Edge n → ℝ) :
    torusCharacter m x =
      char1D (m e0) ((splitAtEdge e0 x).1) *
        Complex.exp (∑ ee : EdgeNe e0, ((m ee.1 : ℂ) * (((splitAtEdge e0 x).2 ee : ℂ) * Complex.I))) := by
  let ecompl : Edge n ≃ EdgeEq e0 ⊕ EdgeNe e0 :=
    (Equiv.sumCompl (fun e : Edge n => e = e0)).symm
  have hsum :
      ∑ e : Edge n, ((m e : ℂ) * ((x e : ℂ) * Complex.I))
        = ((m e0 : ℂ) * ((x e0 : ℂ) * Complex.I))
            + ∑ ee : EdgeNe e0, ((m ee.1 : ℂ) * ((x ee.1 : ℂ) * Complex.I)) := by
    calc
      ∑ e : Edge n, ((m e : ℂ) * ((x e : ℂ) * Complex.I))
          = ∑ s : EdgeEq e0 ⊕ EdgeNe e0,
              match s with
              | Sum.inl a => ((m a.1 : ℂ) * ((x a.1 : ℂ) * Complex.I))
              | Sum.inr b => ((m b.1 : ℂ) * ((x b.1 : ℂ) * Complex.I)) := by
                exact Fintype.sum_equiv ecompl
                  (fun e : Edge n => ((m e : ℂ) * ((x e : ℂ) * Complex.I)))
                  (fun s : EdgeEq e0 ⊕ EdgeNe e0 =>
                    match s with
                    | Sum.inl a => ((m a.1 : ℂ) * ((x a.1 : ℂ) * Complex.I))
                    | Sum.inr b => ((m b.1 : ℂ) * ((x b.1 : ℂ) * Complex.I)))
                  (by
                    intro e
                    cases h : ecompl e with
                    | inl a =>
                        have he : e = a.1 := by
                          simpa [ecompl] using congrArg ecompl.symm h
                        simp [he]
                    | inr b =>
                        have he : e = b.1 := by
                          simpa [ecompl] using congrArg ecompl.symm h
                        simp [he])
      _ = (∑ a : EdgeEq e0, ((m a.1 : ℂ) * ((x a.1 : ℂ) * Complex.I)))
            + ∑ ee : EdgeNe e0, ((m ee.1 : ℂ) * ((x ee.1 : ℂ) * Complex.I)) := by
              rw [Fintype.sum_sum_type]
      _ = ((m e0 : ℂ) * ((x e0 : ℂ) * Complex.I))
            + ∑ ee : EdgeNe e0, ((m ee.1 : ℂ) * ((x ee.1 : ℂ) * Complex.I)) := by
              letI : Subsingleton (EdgeEq e0) := by
                refine ⟨?_⟩
                intro a b
                apply Subtype.ext
                simpa [a.2, b.2]
              rw [Fintype.sum_subsingleton
                (f := fun a : EdgeEq e0 => ((m a.1 : ℂ) * ((x a.1 : ℂ) * Complex.I)))
                ⟨e0, rfl⟩]
  unfold torusCharacter char1D
  rw [hsum, Complex.exp_add]
  have hrest :
      Complex.exp (∑ ee : EdgeNe e0, ((m ee.1 : ℂ) * ((x ee.1 : ℂ) * Complex.I)))
        = Complex.exp (∑ ee : EdgeNe e0, ((m ee.1 : ℂ) * (((splitAtEdge e0 x).2 ee : ℂ) * Complex.I))) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro ee hee
          simp [splitAtEdge_snd]
  rw [splitAtEdge_fst, hrest]

private def restTorusBox {n : ℕ} (e0 : Edge n) : Set (EdgeNe e0 → ℝ) :=
  Set.pi Set.univ (fun _ : EdgeNe e0 => Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4))

private lemma measurableSet_restTorusBox {n : ℕ} (e0 : Edge n) : MeasurableSet (restTorusBox e0) := by
  unfold restTorusBox
  simp

private lemma integral_char1D_Icc (k : ℤ) :
    ∫ x in Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4), char1D k x
      = if k = 0 then (2 * Real.pi : ℂ) else 0 := by
  have hle : -(Real.pi / 4) ≤ 7 * Real.pi / 4 := by
    linarith [Real.pi_pos]
  calc
    ∫ x in Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4), char1D k x
        = ∫ x in Set.Ioc (-(Real.pi / 4)) (7 * Real.pi / 4), char1D k x := by
            exact MeasureTheory.integral_Icc_eq_integral_Ioc
    _ = ∫ x in (-(Real.pi / 4))..(7 * Real.pi / 4), char1D k x := by
          symm
          exact intervalIntegral.integral_of_le hle
    _ = if k = 0 then (2 * Real.pi : ℂ) else 0 := intervalIntegral_char1D k

private lemma splitAtEdge_mem_torusBox_iff {n : ℕ} (e0 : Edge n) (x : Edge n → ℝ) :
    x ∈ torusBox n ↔
      (splitAtEdge e0 x).1 ∈ Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4)
        ∧ (splitAtEdge e0 x).2 ∈ restTorusBox e0 := by
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · simpa [splitAtEdge_fst] using hx e0 (by simp)
    · rw [restTorusBox, Set.mem_pi]
      intro ee hee
      simpa [splitAtEdge_snd] using hx ee.1 (by simp)
  · intro hx
    rw [torusBox, Set.mem_pi] at ⊢
    intro e he
    by_cases h : e = e0
    · subst h
      simpa [splitAtEdge_fst] using hx.1
    · have hmem := hx.2 ⟨e, h⟩ (by simp)
      simpa [restTorusBox, splitAtEdge_snd] using hmem

private lemma torusCharacter_integral_eq_zero_of_nonzero {n : ℕ} (m : Edge n → ℤ)
    (hfreq : ∃ e0 : Edge n, m e0 ≠ 0) :
    ∫ lam in torusBox n, torusCharacter m lam = 0 := by
  rcases hfreq with ⟨e0, he0⟩
  let g : (EdgeNe e0 → ℝ) → ℂ :=
    fun v => Complex.exp (∑ ee : EdgeNe e0, ((m ee.1 : ℂ) * ((v ee : ℂ) * Complex.I)))
  have hind :
      ∀ x : Edge n → ℝ,
        Set.indicator (torusBox n) (torusCharacter m) x
          = Set.indicator
              (Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4) ×ˢ restTorusBox e0)
              (fun p : ℝ × (EdgeNe e0 → ℝ) => char1D (m e0) p.1 * g p.2)
              (splitAtEdge e0 x) := by
    intro x
    by_cases hx : x ∈ torusBox n
    · have hs : splitAtEdge e0 x ∈ Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4) ×ˢ restTorusBox e0 :=
        (splitAtEdge_mem_torusBox_iff e0 x).1 hx
      simp [hx, hs, g, torusCharacter_split e0 m x]
    · have hs : splitAtEdge e0 x ∉ Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4) ×ˢ restTorusBox e0 := by
        intro hsplit
        exact hx ((splitAtEdge_mem_torusBox_iff e0 x).2 hsplit)
      simp [hx, hs]
  have htransport :=
    MeasureTheory.MeasurePreserving.integral_comp (splitAtEdge_measurePreserving e0)
      (splitAtEdge e0).measurableEmbedding
      (fun p : ℝ × (EdgeNe e0 → ℝ) =>
        Set.indicator
          (Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4) ×ˢ restTorusBox e0)
          (fun p : ℝ × (EdgeNe e0 → ℝ) => char1D (m e0) p.1 * g p.2)
          p)
  calc
    ∫ lam in torusBox n, torusCharacter m lam
        = ∫ x : Edge n → ℝ, Set.indicator (torusBox n) (torusCharacter m) x := by
            symm
            simpa using
              (MeasureTheory.integral_indicator (μ := MeasureTheory.volume)
                (f := torusCharacter m) (hs := measurableSet_torusBox n))
    _ = ∫ x : Edge n → ℝ,
          Set.indicator
            (Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4) ×ˢ restTorusBox e0)
            (fun p : ℝ × (EdgeNe e0 → ℝ) => char1D (m e0) p.1 * g p.2)
            (splitAtEdge e0 x) := by
              congr with x
              exact hind x
    _ = ∫ p : ℝ × (EdgeNe e0 → ℝ),
          Set.indicator
            (Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4) ×ˢ restTorusBox e0)
            (fun p : ℝ × (EdgeNe e0 → ℝ) => char1D (m e0) p.1 * g p.2)
            p := by
              simpa using htransport
    _ = ∫ p : ℝ × (EdgeNe e0 → ℝ) in
          Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4) ×ˢ restTorusBox e0,
          char1D (m e0) p.1 * g p.2 := by
            symm
            simpa using
              (MeasureTheory.integral_indicator (μ := MeasureTheory.volume)
                (f := fun p : ℝ × (EdgeNe e0 → ℝ) => char1D (m e0) p.1 * g p.2)
                (hs := measurableSet_Icc.prod (measurableSet_restTorusBox e0))).symm
    _ = (∫ z in Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4), char1D (m e0) z)
          * ∫ y in restTorusBox e0, g y := by
            change
              ∫ p : ℝ × (EdgeNe e0 → ℝ) in
                Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4) ×ˢ restTorusBox e0,
                char1D (m e0) p.1 * g p.2 ∂ (MeasureTheory.volume.prod MeasureTheory.volume)
                = _
            rw [MeasureTheory.setIntegral_prod_mul]
    _ = 0 := by
          rw [integral_char1D_Icc]
          simp [he0]

private lemma torusCharacter_integral {n : ℕ} (m : Edge n → ℤ) :
    ∫ lam in torusBox n, torusCharacter m lam
      = if ∀ e : Edge n, m e = 0 then (((2 * Real.pi) ^ (d n : Nat) : ℝ) : ℂ) else 0 := by
  by_cases hzero : ∀ e : Edge n, m e = 0
  · have hconst : ∀ lam : Edge n → ℝ, torusCharacter m lam = 1 := by
      intro lam
      unfold torusCharacter
      simp [hzero]
    have hreal_eq :
        MeasureTheory.volume.real (torusBox n) = ((2 * Real.pi) ^ (d n : Nat) : ℝ) := by
      rw [MeasureTheory.Measure.real_def, volume_torusBox_toReal n]
    have hvol :
        ∫ lam in torusBox n, (1 : ℂ) = (((2 * Real.pi) ^ (d n : Nat) : ℝ) : ℂ) := by
      simp [MeasureTheory.integral_const, hreal_eq, mul_comm]
    calc
      ∫ lam in torusBox n, torusCharacter m lam = ∫ lam in torusBox n, (1 : ℂ) := by
        congr with lam
        exact hconst lam
      _ = (((2 * Real.pi) ^ (d n : Nat) : ℝ) : ℂ) := hvol
      _ = if ∀ e : Edge n, m e = 0 then (((2 * Real.pi) ^ (d n : Nat) : ℝ) : ℂ) else 0 := by
        simp [hzero]
  · have hfreq : ∃ e : Edge n, m e ≠ 0 := by
      simpa [not_forall] using hzero
    rw [torusCharacter_integral_eq_zero_of_nonzero m hfreq]
    simp [hzero]

private lemma exp_taylor2 (x : ℝ) (hx : 0 ≤ x) : 1 + x + x ^ 2 / 2 ≤ Real.exp x := by
  simpa [add_assoc, add_comm, add_left_comm] using Real.quadratic_le_exp_of_nonneg hx

/-- A coarse but convenient domination of polynomial growth by a single exponential. -/
lemma pow_nat_le_nat_pow_mul_exp {u : ℝ} (m : ℕ) (hm : 0 < m) (hu : 0 ≤ u) :
    u ^ m ≤ (m : ℝ) ^ m * Real.exp u := by
  have hmR : (0 : ℝ) < m := by
    exact_mod_cast hm
  have hstep : u / (m : ℝ) ≤ Real.exp (u / (m : ℝ)) := by
    have hbase := Real.add_one_le_exp (u / (m : ℝ))
    linarith
  have hmul : u ≤ (m : ℝ) * Real.exp (u / (m : ℝ)) := by
    have hscaled := mul_le_mul_of_nonneg_left hstep hmR.le
    simpa [div_eq_mul_inv, hmR.ne', mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hpow := pow_le_pow_left₀ hu hmul m
  calc
    u ^ m ≤ ((m : ℝ) * Real.exp (u / (m : ℝ))) ^ m := hpow
    _ = (m : ℝ) ^ m * Real.exp u := by
          rw [mul_pow, ← Real.exp_nat_mul]
          congr 1
          field_simp [hmR.ne']

lemma log_two_lt_three_quarters : Real.log 2 < (3 / 4 : ℝ) := by
  have h65 : (65 / 32 : ℝ) > 2 := by norm_num
  have hexp : Real.exp (3 / 4 : ℝ) > 2 := by
    have hquad : 1 + (3 / 4 : ℝ) + (3 / 4 : ℝ) ^ 2 / 2 ≤ Real.exp (3 / 4 : ℝ) :=
      exp_taylor2 (3 / 4 : ℝ) (by positivity)
    have hval : 1 + (3 / 4 : ℝ) + (3 / 4 : ℝ) ^ 2 / 2 = (65 / 32 : ℝ) := by norm_num
    linarith
  have h2pos : (0 : ℝ) < 2 := by norm_num
  exact (Real.log_lt_iff_lt_exp h2pos).2 hexp

lemma log_nat_lt_half (n : ℕ) (hn : 3 ≤ n) : Real.log n < (n : ℝ) / 2 := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hexp : Real.exp ((n : ℝ) / 2) > (n : ℝ) := by
    have hquad :
        1 + ((n : ℝ) / 2) + (((n : ℝ) / 2) ^ 2) / 2 ≤
          Real.exp ((n : ℝ) / 2) :=
      exp_taylor2 ((n : ℝ) / 2) (by positivity)
    have hpoly : 1 + ((n : ℝ) / 2) + (((n : ℝ) / 2) ^ 2) / 2 > (n : ℝ) := by
      have haux : (n : ℝ) ^ 2 > 4 * (n : ℝ) - 8 := by
        nlinarith [hnR]
      nlinarith
    linarith
  exact (Real.log_lt_iff_lt_exp hnpos).2 hexp

/-- Averaging over all Boolean sign vectors. -/
def avgOver (n : ℕ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  (∑ y : Fin n → Bool, f y) / (2 ^ n : ℝ)

lemma avgOver_const (n : ℕ) (c : ℝ) : avgOver n (fun _ : Fin n → Bool => c) = c := by
  unfold avgOver
  simp

/-- The edge-model polynomial `W`, equal to `phase`. -/
def W {n : ℕ} (mu : Edge n → ℝ) (y : Fin n → Bool) : ℝ :=
  ∑ e : Edge n, mu e * Z y e

lemma phase_eq_W {n : ℕ} (mu : Edge n → ℝ) (y : Fin n → Bool) :
    phase mu y = W mu y := rfl

/-- The edges incident to a given vertex. -/
def edgesIncident (n : ℕ) (i : Fin n) : Finset (Edge n) :=
  (Finset.univ : Finset (Edge n)).filter (fun e => e.1.1 = i ∨ e.1.2 = i)

lemma mem_edgesIncident_iff {n : ℕ} {i : Fin n} {e : Edge n} :
    e ∈ edgesIncident n i ↔ e.1.1 = i ∨ e.1.2 = i := by
  unfold edgesIncident
  simp

lemma edge_mem_edgesIncident_left {n : ℕ} (e : Edge n) :
    e ∈ edgesIncident n e.1.1 := by
  exact (mem_edgesIncident_iff (i := e.1.1) (e := e)).2 (Or.inl rfl)

lemma edge_mem_edgesIncident_right {n : ℕ} (e : Edge n) :
    e ∈ edgesIncident n e.1.2 := by
  exact (mem_edgesIncident_iff (i := e.1.2) (e := e)).2 (Or.inr rfl)

/-- Flip the Boolean sign at a single vertex. -/
def flipBoolAt {n : ℕ} (i : Fin n) (y : Fin n → Bool) : Fin n → Bool :=
  fun j => if j = i then !(y j) else y j

private lemma spin_flip_at_eq_neg {n : ℕ} (i : Fin n) (y : Fin n → Bool) :
    spin (flipBoolAt i y i) = - spin (y i) := by
  unfold flipBoolAt
  by_cases hy : y i
  · simp [hy, spin]
  · simp [hy, spin]

private lemma spin_flip_at_eq {n : ℕ} (i j : Fin n) (y : Fin n → Bool) :
    spin (flipBoolAt i y j) = if j = i then - spin (y j) else spin (y j) := by
  by_cases hji : j = i
  · subst hji
    simp [spin_flip_at_eq_neg]
  · simp [flipBoolAt, hji]

private lemma Z_eq_one_or_neg_one {n : ℕ} (y : Fin n → Bool) (e : Edge n) :
    Z y e = 1 ∨ Z y e = -1 := by
  rcases e with ⟨⟨i, j⟩, hij⟩
  unfold Z
  cases y i <;> cases y j <;> simp [spin]

lemma Z_sq_eq_one {n : ℕ} (y : Fin n → Bool) (e : Edge n) :
    (Z y e) ^ (2 : Nat) = 1 := by
  rcases Z_eq_one_or_neg_one y e with h | h <;> simp [h]

lemma Z_flip_at {n : ℕ} (i : Fin n) (y : Fin n → Bool) (e : Edge n) :
    Z (flipBoolAt i y) e =
      if e ∈ edgesIncident n i then - Z y e else Z y e := by
  rcases e with ⟨⟨u, v⟩, huv⟩
  have huv_ne : u ≠ v := ne_of_lt huv
  have hmem : (⟨(u, v), huv⟩ : Edge n) ∈ edgesIncident n i ↔ u = i ∨ v = i := by
    simpa using (mem_edgesIncident_iff (n := n) (i := i) (e := ⟨(u, v), huv⟩))
  by_cases hu : u = i
  · have hv : v ≠ i := by
      intro hv
      exact huv_ne (hu.trans hv.symm)
    have h_in : (⟨(u, v), huv⟩ : Edge n) ∈ edgesIncident n i := (hmem).2 (Or.inl hu)
    have hsu : spin (flipBoolAt i y u) = - spin (y u) := by
      simpa [hu] using (spin_flip_at_eq (i := i) (j := u) (y := y))
    have hsv : spin (flipBoolAt i y v) = spin (y v) := by
      simpa [hv] using (spin_flip_at_eq (i := i) (j := v) (y := y))
    calc
      Z (flipBoolAt i y) ⟨(u, v), huv⟩
          = spin (flipBoolAt i y u) * spin (flipBoolAt i y v) := by rfl
      _ = (- spin (y u)) * spin (y v) := by simp [hsu, hsv]
      _ = - (spin (y u) * spin (y v)) := by ring
      _ = - Z y ⟨(u, v), huv⟩ := by rfl
      _ = if (⟨(u, v), huv⟩ : Edge n) ∈ edgesIncident n i then
            - Z y ⟨(u, v), huv⟩ else Z y ⟨(u, v), huv⟩ := by simp [h_in]
  · by_cases hv : v = i
    · have h_in : (⟨(u, v), huv⟩ : Edge n) ∈ edgesIncident n i := (hmem).2 (Or.inr hv)
      have hsu : spin (flipBoolAt i y u) = spin (y u) := by
        simpa [hu] using (spin_flip_at_eq (i := i) (j := u) (y := y))
      have hsv : spin (flipBoolAt i y v) = - spin (y v) := by
        simpa [hv] using (spin_flip_at_eq (i := i) (j := v) (y := y))
      calc
        Z (flipBoolAt i y) ⟨(u, v), huv⟩
            = spin (flipBoolAt i y u) * spin (flipBoolAt i y v) := by rfl
        _ = spin (y u) * (- spin (y v)) := by simp [hsu, hsv]
        _ = - (spin (y u) * spin (y v)) := by ring
        _ = - Z y ⟨(u, v), huv⟩ := by rfl
        _ = if (⟨(u, v), huv⟩ : Edge n) ∈ edgesIncident n i then
              - Z y ⟨(u, v), huv⟩ else Z y ⟨(u, v), huv⟩ := by simp [h_in]
    · have h_notin : (⟨(u, v), huv⟩ : Edge n) ∉ edgesIncident n i := by
        intro h
        rcases (hmem).1 h with hu' | hv'
        · exact hu hu'
        · exact hv hv'
      have hsu : spin (flipBoolAt i y u) = spin (y u) := by
        simpa [hu] using (spin_flip_at_eq (i := i) (j := u) (y := y))
      have hsv : spin (flipBoolAt i y v) = spin (y v) := by
        simpa [hv] using (spin_flip_at_eq (i := i) (j := v) (y := y))
      calc
        Z (flipBoolAt i y) ⟨(u, v), huv⟩
            = spin (flipBoolAt i y u) * spin (flipBoolAt i y v) := by rfl
        _ = spin (y u) * spin (y v) := by simp [hsu, hsv]
        _ = Z y ⟨(u, v), huv⟩ := by rfl
        _ = if (⟨(u, v), huv⟩ : Edge n) ∈ edgesIncident n i then
              - Z y ⟨(u, v), huv⟩ else Z y ⟨(u, v), huv⟩ := by simp [h_notin]

private lemma flipBoolAt_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (flipBoolAt i) := by
  intro y
  funext j
  by_cases hj : j = i
  · subst hj
    simp [flipBoolAt]
  · simp [flipBoolAt, hj]

lemma sum_flipBoolAt_eq {n : ℕ} {β : Type*} [AddCommMonoid β]
    (i : Fin n) (f : (Fin n → Bool) → β) :
    (∑ y : Fin n → Bool, f (flipBoolAt i y)) = ∑ y : Fin n → Bool, f y := by
  simpa using
    (Function.Bijective.sum_comp
      (e := flipBoolAt i)
      (he := (flipBoolAt_involutive i).bijective)
      (g := f))

/-- Row-degree of an edge monomial at vertex `i`. -/
def edgeNatRowSum {n : ℕ} (b : Edge n → Nat) (i : Fin n) : Nat :=
  (edgesIncident n i).sum (fun e => b e)

/-- Edge monomial in the sign variables. -/
def edgeZMonomial {n : ℕ} (b : Edge n → Nat) (y : Fin n → Bool) : ℝ :=
  ∏ e : Edge n, (Z y e) ^ (b e)

private lemma edgeZMonomial_flipAt {n : ℕ} (b : Edge n → Nat) (i : Fin n) (y : Fin n → Bool) :
    edgeZMonomial b (flipBoolAt i y)
      = (-1 : ℝ) ^ edgeNatRowSum b i * edgeZMonomial b y := by
  unfold edgeZMonomial edgeNatRowSum
  calc
    ∏ e : Edge n, (Z (flipBoolAt i y) e) ^ (b e)
        = ∏ e : Edge n, ((if e ∈ edgesIncident n i then - Z y e else Z y e) ^ (b e)) := by
            refine Finset.prod_congr rfl ?_
            intro e he
            rw [Z_flip_at]
    _ = ∏ e : Edge n, (((if e ∈ edgesIncident n i then (-1 : ℝ) else 1) ^ (b e))
          * (Z y e) ^ (b e)) := by
            refine Finset.prod_congr rfl ?_
            intro e he
            by_cases hmem : e ∈ edgesIncident n i
            · simpa [hmem, mul_assoc, mul_left_comm, mul_comm] using
                (mul_pow (-1 : ℝ) (Z y e) (b e))
            · simp [hmem]
    _ = (∏ e : Edge n, (if e ∈ edgesIncident n i then (-1 : ℝ) else 1) ^ (b e))
          * ∏ e : Edge n, (Z y e) ^ (b e) := by
            rw [Finset.prod_mul_distrib]
    _ = ((edgesIncident n i).prod (fun e => (-1 : ℝ) ^ (b e)))
          * ∏ e : Edge n, (Z y e) ^ (b e) := by
            have hprod_if :
                ((edgesIncident n i).prod (fun e => (-1 : ℝ) ^ (b e)))
                  = ∏ e : Edge n, (if e ∈ edgesIncident n i then (-1 : ℝ) else 1) ^ (b e) := by
              simpa using
                (Finset.prod_subset
                  (s₁ := edgesIncident n i)
                  (s₂ := (Finset.univ : Finset (Edge n)))
                  (f := fun e : Edge n =>
                    (if e ∈ edgesIncident n i then (-1 : ℝ) else 1) ^ (b e))
                  (by
                    intro e he
                    simp)
                  (by
                    intro e he_univ he_not
                    simp [he_not]))
            rw [← hprod_if]
    _ = (-1 : ℝ) ^ ((edgesIncident n i).sum (fun e => b e))
          * ∏ e : Edge n, (Z y e) ^ (b e) := by
            rw [Finset.prod_pow_eq_pow_sum]

private lemma sum_edgeZMonomial_eq_zero_of_odd_row {n : ℕ} (b : Edge n → Nat) (i : Fin n)
    (hodd : Odd (edgeNatRowSum b i)) :
    (∑ y : Fin n → Bool, edgeZMonomial b y) = 0 := by
  have hperm :
      (∑ y : Fin n → Bool, edgeZMonomial b (flipBoolAt i y))
        = ∑ y : Fin n → Bool, edgeZMonomial b y :=
    sum_flipBoolAt_eq i (fun y => edgeZMonomial b y)
  have hsign : (-1 : ℝ) ^ edgeNatRowSum b i = -1 := by
    rcases hodd with ⟨k, hk⟩
    rw [hk, pow_add, pow_mul]
    simp
  have hneg :
      (∑ y : Fin n → Bool, edgeZMonomial b (flipBoolAt i y))
        = -(∑ y : Fin n → Bool, edgeZMonomial b y) := by
    calc
      (∑ y : Fin n → Bool, edgeZMonomial b (flipBoolAt i y))
          = ∑ y : Fin n → Bool, ((-1 : ℝ) ^ edgeNatRowSum b i * edgeZMonomial b y) := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              rw [edgeZMonomial_flipAt]
      _ = (-1 : ℝ) ^ edgeNatRowSum b i * ∑ y : Fin n → Bool, edgeZMonomial b y := by
            rw [Finset.mul_sum]
      _ = -(∑ y : Fin n → Bool, edgeZMonomial b y) := by
            simp [hsign]
  linarith [hperm, hneg]

private lemma avg_edgeZMonomial_eq_zero_of_odd_row {n : ℕ} (b : Edge n → Nat) (i : Fin n)
    (hodd : Odd (edgeNatRowSum b i)) :
    avgOver n (fun y => edgeZMonomial b y) = 0 := by
  unfold avgOver
  rw [sum_edgeZMonomial_eq_zero_of_odd_row b i hodd]
  simp

/-- Boolean vector attached to a finite set of vertices. -/
private def yOfSet {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool :=
  fun i => i ∈ S

private lemma yOfSet_insert_eq_flip {n : ℕ} (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    yOfSet (insert i S) = flipBoolAt i (yOfSet S) := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [yOfSet, flipBoolAt, hi]
  · simp [yOfSet, flipBoolAt, hj]

private lemma y_eq_yOfSet_trueSupport {n : ℕ} (y : Fin n → Bool) :
    y = yOfSet ((Finset.univ : Finset (Fin n)).filter fun i => y i) := by
  funext i
  simp [yOfSet]

private lemma edgeZMonomial_yOfSet_eq_one_of_even_rows {n : ℕ} (b : Edge n → Nat)
    (hall : ∀ i : Fin n, Even (edgeNatRowSum b i)) :
    ∀ S : Finset (Fin n), edgeZMonomial b (yOfSet S) = 1 := by
  intro S
  refine Finset.induction_on S ?_ ?_
  · simp [edgeZMonomial, yOfSet, Z, spin]
  · intro i S hiS hS
    have hsign : (-1 : ℝ) ^ edgeNatRowSum b i = 1 := by
      rcases hall i with ⟨k, hk⟩
      have hk' : k + k = 2 * k := by omega
      rw [hk, hk', pow_mul]
      simp
    have hflip :
        edgeZMonomial b (flipBoolAt i (yOfSet S))
          = edgeZMonomial b (yOfSet S) := by
      calc
        edgeZMonomial b (flipBoolAt i (yOfSet S))
            = (-1 : ℝ) ^ edgeNatRowSum b i * edgeZMonomial b (yOfSet S) := by
                rw [edgeZMonomial_flipAt]
        _ = edgeZMonomial b (yOfSet S) := by simp [hsign]
    have hinsert : yOfSet (insert i S) = flipBoolAt i (yOfSet S) :=
      yOfSet_insert_eq_flip S i hiS
    rw [hinsert, hflip, hS]

lemma avg_edgeZMonomial_eq_ite_allEven {n : ℕ} (b : Edge n → Nat) :
    avgOver n (fun y => edgeZMonomial b y)
      = if ∀ i : Fin n, Even (edgeNatRowSum b i) then 1 else 0 := by
  by_cases hall : ∀ i : Fin n, Even (edgeNatRowSum b i)
  · unfold avgOver
    have hpoint : ∀ y : Fin n → Bool, edgeZMonomial b y = 1 := by
      intro y
      rw [y_eq_yOfSet_trueSupport y]
      exact edgeZMonomial_yOfSet_eq_one_of_even_rows b hall _
    have hsum :
        (∑ y : Fin n → Bool, edgeZMonomial b y) = ∑ y : Fin n → Bool, (1 : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro y hy
      simp [hpoint y]
    rw [if_pos hall, hsum]
    simp
  · push_neg at hall
    rcases hall with ⟨i, hi⟩
    have hodd : Odd (edgeNatRowSum b i) := Nat.not_even_iff_odd.mp hi
    rw [if_neg (by
      intro h
      exact hi (h i))]
    exact avg_edgeZMonomial_eq_zero_of_odd_row b i hodd

/-- Edge multiplicities attached to an ordered 4-tuple of edges. -/
def edgeMultiplicity4 {n : ℕ} (e₁ e₂ e₃ e₄ : Edge n) : Edge n → Nat :=
  fun e =>
    (if e = e₁ then 1 else 0) +
    (if e = e₂ then 1 else 0) +
    (if e = e₃ then 1 else 0) +
    (if e = e₄ then 1 else 0)

lemma edgeZMonomial_add {n : ℕ} (b₁ b₂ : Edge n → Nat) (y : Fin n → Bool) :
    edgeZMonomial (fun e => b₁ e + b₂ e) y
      = edgeZMonomial b₁ y * edgeZMonomial b₂ y := by
  unfold edgeZMonomial
  calc
    ∏ e : Edge n, (Z y e) ^ (b₁ e + b₂ e)
        = ∏ e : Edge n, ((Z y e) ^ (b₁ e) * (Z y e) ^ (b₂ e)) := by
            refine Finset.prod_congr rfl ?_
            intro e he
            rw [pow_add]
    _ = (∏ e : Edge n, (Z y e) ^ (b₁ e)) * ∏ e : Edge n, (Z y e) ^ (b₂ e) := by
          rw [Finset.prod_mul_distrib]

lemma edgeZMonomial_single {n : ℕ} (y : Fin n → Bool) (e₀ : Edge n) :
    edgeZMonomial (fun e : Edge n => if e = e₀ then 1 else 0) y = Z y e₀ := by
  unfold edgeZMonomial
  have hprod :
      (∏ e : Edge n, (Z y e) ^ (if e = e₀ then 1 else 0))
        = ∏ e : Edge n, (if e = e₀ then Z y e₀ else 1) := by
    refine Finset.prod_congr rfl ?_
    intro e he
    by_cases h : e = e₀
    · subst h
      simp
    · simp [h]
  rw [hprod]
  simpa using
    (Finset.prod_eq_single e₀ (by intro e he hne; simp [hne])
      (by simp))

lemma edgeZMonomial_edgeMultiplicity4 {n : ℕ} (y : Fin n → Bool)
    (e₁ e₂ e₃ e₄ : Edge n) :
    edgeZMonomial (edgeMultiplicity4 e₁ e₂ e₃ e₄) y
      = Z y e₁ * Z y e₂ * Z y e₃ * Z y e₄ := by
  let b₁ : Edge n → Nat := fun e => if e = e₁ then 1 else 0
  let b₂ : Edge n → Nat := fun e => if e = e₂ then 1 else 0
  let b₃ : Edge n → Nat := fun e => if e = e₃ then 1 else 0
  let b₄ : Edge n → Nat := fun e => if e = e₄ then 1 else 0
  have hmul12 :
      edgeZMonomial (fun e => b₁ e + b₂ e) y = edgeZMonomial b₁ y * edgeZMonomial b₂ y :=
    edgeZMonomial_add b₁ b₂ y
  have hmul34 :
      edgeZMonomial (fun e => b₃ e + b₄ e) y = edgeZMonomial b₃ y * edgeZMonomial b₄ y :=
    edgeZMonomial_add b₃ b₄ y
  have hmul1234 :
      edgeZMonomial (fun e => (b₁ e + b₂ e) + (b₃ e + b₄ e)) y
        = edgeZMonomial (fun e => b₁ e + b₂ e) y *
            edgeZMonomial (fun e => b₃ e + b₄ e) y :=
    edgeZMonomial_add (fun e => b₁ e + b₂ e) (fun e => b₃ e + b₄ e) y
  have hsum :
      edgeMultiplicity4 e₁ e₂ e₃ e₄ = fun e => (b₁ e + b₂ e) + (b₃ e + b₄ e) := by
    funext e
    simp [edgeMultiplicity4, b₁, b₂, b₃, b₄, add_assoc]
  rw [hsum, hmul1234, hmul12, hmul34]
  simp [b₁, b₂, b₃, b₄, edgeZMonomial_single, mul_assoc, mul_left_comm, mul_comm]

lemma exists_incident_xor_of_ne {n : ℕ} {e f : Edge n} (hef : e ≠ f) :
    ∃ i : Fin n, (e ∈ edgesIncident n i ∧ f ∉ edgesIncident n i) ∨
      (f ∈ edgesIncident n i ∧ e ∉ edgesIncident n i) := by
  rcases e with ⟨⟨a, b⟩, hab⟩
  rcases f with ⟨⟨c, d⟩, hcd⟩
  by_cases ha : a = c ∨ a = d
  · by_cases hb : b = c ∨ b = d
    · rcases ha with hac | had <;> rcases hb with hbc | hbd
      · exfalso
        subst hac
        exact (ne_of_lt hab) hbc.symm
      · exfalso
        subst hac
        subst hbd
        exact hef rfl
      · exfalso
        have hba : b < a := by simpa [had, hbc] using hcd
        exact (not_lt_of_gt hab) hba
      · exfalso
        have hab_eq : a = b := by
          exact had.trans hbd.symm
        exact (ne_of_lt hab) hab_eq
    · refine ⟨b, Or.inl ?_⟩
      constructor
      · exact edge_mem_edgesIncident_right ⟨(a, b), hab⟩
      · intro hf
        have hmem := (mem_edgesIncident_iff (i := b) (e := ⟨(c, d), hcd⟩)).1 hf
        cases hmem with
        | inl h =>
            exact hb (Or.inl h.symm)
        | inr h =>
            exact hb (Or.inr h.symm)
  · refine ⟨a, Or.inl ?_⟩
    constructor
    · exact edge_mem_edgesIncident_left ⟨(a, b), hab⟩
    · intro hf
      have hmem := (mem_edgesIncident_iff (i := a) (e := ⟨(c, d), hcd⟩)).1 hf
      cases hmem with
      | inl h =>
          exact ha (Or.inl h.symm)
      | inr h =>
          exact ha (Or.inr h.symm)

private lemma phase_add {n : ℕ} (lam₁ lam₂ : Edge n → ℝ) (y : Fin n → Bool) :
    phase (fun e => lam₁ e + lam₂ e) y = phase lam₁ y + phase lam₂ y := by
  have hfun :
      (fun e : Edge n => (lam₁ e + lam₂ e) * Z y e)
        = fun e => lam₁ e * Z y e + lam₂ e * Z y e := by
    funext e
    ring
  unfold phase
  rw [hfun, Finset.sum_add_distrib]

private def translateSet {n : ℕ} (a : Edge n → ℝ) (S : Set (Edge n → ℝ)) : Set (Edge n → ℝ) :=
  {x | x - a ∈ S}

private def LambdaCode (n : ℕ) : Type := Edge n → Fin 4

instance instFintypeLambdaCode (n : ℕ) : Fintype (LambdaCode n) := by
  dsimp [LambdaCode]
  infer_instance

instance instDecidableEqLambdaCode (n : ℕ) : DecidableEq (LambdaCode n) := by
  dsimp [LambdaCode]
  infer_instance

private def quarterReal (q : Fin 4) : ℝ := (q : ℕ) * (Real.pi / 2)

private def lambdaReal {n : ℕ} (b : LambdaCode n) : Edge n → ℝ := fun e => quarterReal (b e)

private def fin4ToBits (q : Fin 4) : Bool × Bool :=
  match q.1 with
  | 0 => (false, false)
  | 1 => (true, false)
  | 2 => (false, true)
  | _ => (true, true)

private def bitsToFin4 (b : Bool × Bool) : Fin 4 :=
  match b with
  | (false, false) => 0
  | (true, false) => 1
  | (false, true) => 2
  | (true, true) => 3

private lemma bitsToFin4_fin4ToBits (q : Fin 4) : bitsToFin4 (fin4ToBits q) = q := by
  fin_cases q <;> decide

private def parityBit {n : ℕ} (b : LambdaCode n) : Edge n → Bool :=
  fun e => (fin4ToBits (b e)).1

private def highBit {n : ℕ} (b : LambdaCode n) : Edge n → Bool :=
  fun e => (fin4ToBits (b e)).2

private def bitsToLambdaCode {n : ℕ} (p h : Edge n → Bool) : LambdaCode n :=
  fun e => bitsToFin4 (p e, h e)

private lemma bitsToLambdaCode_parity_high {n : ℕ} (b : LambdaCode n) :
    bitsToLambdaCode (parityBit b) (highBit b) = b := by
  funext e
  unfold bitsToLambdaCode parityBit highBit
  simpa using (bitsToFin4_fin4ToBits (b e))

private lemma parityBit_bitsToLambdaCode {n : ℕ} (p h : Edge n → Bool) :
    parityBit (bitsToLambdaCode p h) = p := by
  funext e
  unfold parityBit bitsToLambdaCode
  cases hp : p e <;> cases hh : h e <;> rfl

private lemma highBit_bitsToLambdaCode {n : ℕ} (p h : Edge n → Bool) :
    highBit (bitsToLambdaCode p h) = h := by
  funext e
  unfold highBit bitsToLambdaCode
  cases hp : p e <;> cases hh : h e <;> rfl

private lemma quarterReal_injective : Function.Injective quarterReal := by
  intro q1 q2 hq
  have hpi2_ne : (Real.pi / 2 : ℝ) ≠ 0 := by positivity [Real.pi_pos]
  have hnat_real : ((q1 : ℕ) : ℝ) = ((q2 : ℕ) : ℝ) := by
    exact mul_right_cancel₀ hpi2_ne (by simpa [quarterReal] using hq)
  have hnat : (q1 : ℕ) = (q2 : ℕ) := Nat.cast_inj.mp hnat_real
  exact Fin.ext hnat

private lemma lambdaReal_injective (n : ℕ) : Function.Injective (@lambdaReal n) := by
  intro b1 b2 h
  funext e
  apply quarterReal_injective
  exact congrArg (fun f => f e) h

private def rowParitySum {n : ℕ} (b : LambdaCode n) (i : Fin n) : ℕ :=
  edgeNatRowSum (fun e => (b e : ℕ)) i

private def rowParityEven {n : ℕ} (b : LambdaCode n) : Prop :=
  ∀ i : Fin n, Even (rowParitySum b i)

instance instDecidablePredRowParityEven (n : ℕ) : DecidablePred (@rowParityEven n) := by
  intro b
  unfold rowParityEven
  infer_instance

private def lambdaCodes (n : ℕ) : Finset (LambdaCode n) := by
  classical
  exact (Finset.univ : Finset (LambdaCode n)).filter rowParityEven

private lemma card_incident_vertices (n : ℕ) (e : Edge n) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => e.1.1 = i ∨ e.1.2 = i)).card = 2 := by
  have hneq : e.1.1 ≠ e.1.2 := ne_of_lt e.2
  have hset :
      ((Finset.univ : Finset (Fin n)).filter (fun i => e.1.1 = i ∨ e.1.2 = i))
        = ({e.1.1, e.1.2} : Finset (Fin n)) := by
    ext i
    by_cases hi1 : i = e.1.1
    · subst hi1
      simp
    · by_cases hi2 : i = e.1.2
      · subst hi2
        simp [hneq]
      · simp [hi1, hi2, eq_comm]
  rw [hset]
  simp [hneq]

private def paritySumBool {n : ℕ} (p : Edge n → Bool) (i : Fin n) : ℕ :=
  (edgesIncident n i).sum fun e => if p e then 1 else 0

private def parityEvenBool {n : ℕ} (p : Edge n → Bool) : Prop :=
  ∀ i : Fin n, Even (paritySumBool p i)

instance instDecidablePredParityEvenBool (n : ℕ) : DecidablePred (@parityEvenBool n) := by
  intro p
  unfold parityEvenBool
  infer_instance

private def parityCodes (n : ℕ) : Finset (Edge n → Bool) :=
  (Finset.univ : Finset (Edge n → Bool)).filter parityEvenBool

private abbrev F2 := ZMod 2

private def boolToF2 (b : Bool) : F2 := if b then 1 else 0

private def f2ToBool (z : F2) : Bool := if z = 0 then false else true

private lemma f2_eq_zero_or_one (z : F2) : z = 0 ∨ z = 1 := by
  fin_cases z
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma boolToF2_f2ToBool (z : F2) : boolToF2 (f2ToBool z) = z := by
  unfold f2ToBool boolToF2
  by_cases hz : z = 0
  · simp [hz]
  · have hz1 : z = 1 := by
      rcases f2_eq_zero_or_one z with hz0 | hz1
      · contradiction
      · exact hz1
    simp [hz, hz1]

private lemma f2ToBool_boolToF2 (b : Bool) : f2ToBool (boolToF2 b) = b := by
  cases b <;> simp [f2ToBool, boolToF2]

private def boolFuncEquivF2Func (n : ℕ) : (Edge n → Bool) ≃ (Edge n → F2) where
  toFun := fun p e => boolToF2 (p e)
  invFun := fun x e => f2ToBool (x e)
  left_inv := by
    intro p
    funext e
    exact f2ToBool_boolToF2 (p e)
  right_inv := by
    intro x
    funext e
    exact boolToF2_f2ToBool (x e)

private def incidenceF2 (n : ℕ) (x : Edge n → F2) (i : Fin n) : F2 :=
  Finset.sum (edgesIncident n i) fun e => x e

private def incidenceLin (n : ℕ) : (Edge n → F2) →ₗ[F2] (Fin n → F2) where
  toFun := fun x i => incidenceF2 n x i
  map_add' := by
    intro x y
    funext i
    unfold incidenceF2
    simpa [Pi.add_apply] using
      (Finset.sum_add_distrib :
        Finset.sum (edgesIncident n i) (fun e => x e + y e)
          = Finset.sum (edgesIncident n i) (fun e => x e)
              + Finset.sum (edgesIncident n i) (fun e => y e))
  map_smul' := by
    intro c x
    funext i
    unfold incidenceF2
    simp [Pi.smul_apply, Finset.mul_sum]

private lemma paritySumBool_cast_eq_incidenceF2 (n : ℕ) (p : Edge n → Bool) (i : Fin n) :
    ((paritySumBool p i : ℕ) : F2) = incidenceF2 n (boolFuncEquivF2Func n p) i := by
  unfold paritySumBool incidenceF2 boolFuncEquivF2Func
  calc
    ((Finset.sum (edgesIncident n i) (fun e => if p e then (1 : ℕ) else 0) : ℕ) : F2)
        = Finset.sum (edgesIncident n i) (fun e => ((if p e then (1 : ℕ) else 0 : ℕ) : F2)) := by
            simp [Nat.cast_sum]
    _ = Finset.sum (edgesIncident n i) (fun e => boolToF2 (p e)) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          cases hpe : p e <;> simp [boolToF2, hpe]

private lemma parityEvenBool_iff_incidence_zero (n : ℕ) (p : Edge n → Bool) :
    parityEvenBool p ↔ ∀ i : Fin n, incidenceF2 n (boolFuncEquivF2Func n p) i = 0 := by
  constructor
  · intro hp i
    have hcast0 : ((paritySumBool p i : ℕ) : F2) = 0 := by
      have hmod : paritySumBool p i % 2 = 0 := (Nat.even_iff).1 (hp i)
      have hdiv : 2 ∣ paritySumBool p i := Nat.dvd_of_mod_eq_zero hmod
      exact (ZMod.natCast_eq_zero_iff (paritySumBool p i) 2).2 hdiv
    simpa [paritySumBool_cast_eq_incidenceF2 n p i] using hcast0
  · intro hp i
    have hcast0 : ((paritySumBool p i : ℕ) : F2) = 0 := by
      simpa [paritySumBool_cast_eq_incidenceF2 n p i] using hp i
    have hdiv : 2 ∣ paritySumBool p i := (ZMod.natCast_eq_zero_iff (paritySumBool p i) 2).1 hcast0
    exact (Nat.even_iff).2 (Nat.mod_eq_zero_of_dvd hdiv)

private def sumVerticesLin (n : ℕ) : (Fin n → F2) →ₗ[F2] F2 where
  toFun := fun v => Finset.sum Finset.univ fun i => v i
  map_add' := by
    intro u v
    simp [Finset.sum_add_distrib]
  map_smul' := by
    intro c v
    simp [Finset.mul_sum]

private lemma incidence_total_sum_zero (n : ℕ) (x : Edge n → F2) :
    sumVerticesLin n (incidenceLin n x) = 0 := by
  unfold sumVerticesLin incidenceLin incidenceF2
  calc
    Finset.sum (Finset.univ : Finset (Fin n))
        (fun i => Finset.sum (edgesIncident n i) (fun e => x e))
        = Finset.sum (Finset.univ : Finset (Edge n))
            (fun e => Finset.sum (Finset.univ : Finset (Fin n))
              (fun i => if e.1.1 = i ∨ e.1.2 = i then x e else 0)) := by
            calc
              Finset.sum (Finset.univ : Finset (Fin n))
                  (fun i => Finset.sum (edgesIncident n i) (fun e => x e))
                    = Finset.sum (Finset.univ : Finset (Fin n))
                        (fun i => Finset.sum (Finset.univ : Finset (Edge n))
                          (fun e => if e.1.1 = i ∨ e.1.2 = i then x e else 0)) := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      simp [edgesIncident, Finset.sum_filter]
              _ = Finset.sum (Finset.univ : Finset (Edge n))
                    (fun e => Finset.sum (Finset.univ : Finset (Fin n))
                      (fun i => if e.1.1 = i ∨ e.1.2 = i then x e else 0)) := by
                    simpa using (Finset.sum_comm :
                      Finset.sum (Finset.univ : Finset (Fin n))
                        (fun i => Finset.sum (Finset.univ : Finset (Edge n))
                          (fun e => if e.1.1 = i ∨ e.1.2 = i then x e else 0))
                      = Finset.sum (Finset.univ : Finset (Edge n))
                          (fun e => Finset.sum (Finset.univ : Finset (Fin n))
                            (fun i => if e.1.1 = i ∨ e.1.2 = i then x e else 0)))
    _ = Finset.sum (Finset.univ : Finset (Edge n))
          (fun e => Finset.sum ((Finset.univ : Finset (Fin n)).filter
            (fun i => e.1.1 = i ∨ e.1.2 = i)) (fun _ => x e)) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          rw [← Finset.sum_filter]
    _ = Finset.sum (Finset.univ : Finset (Edge n))
          (fun e => (((Finset.univ : Finset (Fin n)).filter
            (fun i => e.1.1 = i ∨ e.1.2 = i)).card : F2) * x e) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = Finset.sum (Finset.univ : Finset (Edge n)) (fun e => (2 : F2) * x e) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          simp [card_incident_vertices]
    _ = Finset.sum (Finset.univ : Finset (Edge n)) (fun _ => 0) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          have h2 : (2 : F2) = 0 := by decide
          simp [h2]
    _ = 0 := by simp

private def edgeFromRoot (n : ℕ) (i : Fin n) : Edge (n + 1) :=
  ⟨(0, i.succ), Fin.succ_pos i⟩

private def starPreimage (n : ℕ) (v : Fin (n + 1) → F2) : Edge (n + 1) → F2 :=
  fun e => if e.1.1 = 0 then v e.1.2 else 0

private lemma edge_eq_edgeFromRoot_of_first_zero_second_succ (n : ℕ) (i : Fin n) (e : Edge (n + 1))
    (h1 : e.1.1 = 0) (h2 : e.1.2 = i.succ) :
    e = edgeFromRoot n i := by
  rcases e with ⟨⟨a, b⟩, hab⟩
  dsimp at h1 h2
  subst h1
  subst h2
  rfl

private lemma incidence_starPreimage_succ (n : ℕ) (v : Fin (n + 1) → F2) (i : Fin n) :
    incidenceF2 (n + 1) (starPreimage n v) i.succ = v i.succ := by
  unfold incidenceF2
  have hmem : edgeFromRoot n i ∈ edgesIncident (n + 1) i.succ :=
    (mem_edgesIncident_iff (i := i.succ) (e := edgeFromRoot n i)).2 (Or.inr rfl)
  have hsum :
      (edgesIncident (n + 1) i.succ).sum (fun e => starPreimage n v e)
        = starPreimage n v (edgeFromRoot n i) := by
    refine Finset.sum_eq_single_of_mem (edgeFromRoot n i) hmem ?_
    intro e he hne
    unfold starPreimage
    by_cases h0 : e.1.1 = 0
    · have hIncident : e.1.1 = i.succ ∨ e.1.2 = i.succ :=
        (mem_edgesIncident_iff (i := i.succ) (e := e)).1 he
      have hsucc_ne_zero : i.succ ≠ 0 := Fin.succ_ne_zero i
      have hright : e.1.2 = i.succ := by
        cases hIncident with
        | inl hleft =>
            exact (False.elim (hsucc_ne_zero (hleft.symm.trans h0)))
        | inr hright =>
            exact hright
      have heq : e = edgeFromRoot n i :=
        edge_eq_edgeFromRoot_of_first_zero_second_succ n i e h0 hright
      exact (hne heq).elim
    · simp [h0]
  calc
    incidenceF2 (n + 1) (starPreimage n v) i.succ
        = (edgesIncident (n + 1) i.succ).sum (fun e => starPreimage n v e) := by rfl
    _ = starPreimage n v (edgeFromRoot n i) := hsum
    _ = v i.succ := by
          simp [starPreimage, edgeFromRoot]

private lemma first_eq_sum_succ_of_sumVertices_zero (n : ℕ) (f : Fin (n + 1) → F2)
    (h : sumVerticesLin (n + 1) f = 0) :
    f 0 = ∑ i : Fin n, f i.succ := by
  have hsum : f 0 + ∑ i : Fin n, f i.succ = 0 := by
    have h' : (∑ i : Fin (n + 1), f i) = 0 := by
      simpa [sumVerticesLin] using h
    calc
      f 0 + ∑ i : Fin n, f i.succ = ∑ i : Fin (n + 1), f i := by
        simpa using (Fin.sum_univ_succ f).symm
      _ = 0 := h'
  have hneg : f 0 = -(∑ i : Fin n, f i.succ) := eq_neg_of_add_eq_zero_left hsum
  simpa using hneg

private lemma incidence_starPreimage_zero (n : ℕ) (v : Fin (n + 1) → F2)
    (hv : sumVerticesLin (n + 1) v = 0) :
    incidenceF2 (n + 1) (starPreimage n v) 0 = v 0 := by
  let w : Fin (n + 1) → F2 := incidenceLin (n + 1) (starPreimage n v)
  have hw0 : w 0 = ∑ i : Fin n, w i.succ := by
    apply first_eq_sum_succ_of_sumVertices_zero n w
    dsimp [w]
    simpa using incidence_total_sum_zero (n + 1) (starPreimage n v)
  have hv0 : v 0 = ∑ i : Fin n, v i.succ := first_eq_sum_succ_of_sumVertices_zero n v hv
  have hsucc :
      (∑ i : Fin n, w i.succ) = ∑ i : Fin n, v i.succ := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    dsimp [w]
    simpa [incidenceLin] using incidence_starPreimage_succ n v i
  calc
    incidenceF2 (n + 1) (starPreimage n v) 0 = w 0 := by
      simp [w, incidenceLin]
    _ = ∑ i : Fin n, w i.succ := hw0
    _ = ∑ i : Fin n, v i.succ := hsucc
    _ = v 0 := hv0.symm

private lemma incidence_starPreimage_eq (n : ℕ) (v : Fin (n + 1) → F2)
    (hv : sumVerticesLin (n + 1) v = 0) :
    incidenceLin (n + 1) (starPreimage n v) = v := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simpa [incidenceLin] using incidence_starPreimage_zero n v hv
  · intro j
    simpa [incidenceLin] using incidence_starPreimage_succ n v j

private lemma range_incidence_eq_ker_sumVertices_succ (n : ℕ) :
    (incidenceLin (n + 1)).range = (sumVerticesLin (n + 1)).ker := by
  apply le_antisymm
  · intro v hv
    rcases hv with ⟨x, rfl⟩
    exact incidence_total_sum_zero (n + 1) x
  · intro v hv
    refine ⟨starPreimage n v, ?_⟩
    exact incidence_starPreimage_eq n v hv

private lemma sumVertices_surjective_succ (n : ℕ) :
    Function.Surjective (sumVerticesLin (n + 1)) := by
  intro z
  refine ⟨fun i => if i = 0 then z else 0, ?_⟩
  unfold sumVerticesLin
  calc
    (∑ i : Fin (n + 1), if i = 0 then z else 0)
        = (if (0 : Fin (n + 1)) = 0 then z else 0)
            + ∑ i : Fin n, (if i.succ = 0 then z else 0) := by
              simpa using (Fin.sum_univ_succ (fun i : Fin (n + 1) => if i = 0 then z else 0))
    _ = z + ∑ i : Fin n, 0 := by simp [Fin.succ_ne_zero]
    _ = z := by simp

private lemma finrank_ker_sumVertices_succ (n : ℕ) :
    Module.finrank F2 ↥((sumVerticesLin (n + 1)).ker) = n := by
  have hsurj : Function.Surjective (sumVerticesLin (n + 1)) :=
    sumVertices_surjective_succ n
  have hrange_top : (sumVerticesLin (n + 1)).range = ⊤ :=
    (LinearMap.range_eq_top).2 hsurj
  have hrange_finrank :
      Module.finrank F2 ↥((sumVerticesLin (n + 1)).range) = 1 := by
    rw [hrange_top]
    simpa using (Module.finrank_self F2)
  have hdom_finrank :
      Module.finrank F2 (Fin (n + 1) → F2) = n + 1 := by
    simpa using (Module.finrank_fintype_fun_eq_card F2 (η := Fin (n + 1)))
  have hadd :
      Module.finrank F2 ↥((sumVerticesLin (n + 1)).range)
        + Module.finrank F2 ↥((sumVerticesLin (n + 1)).ker)
        = Module.finrank F2 (Fin (n + 1) → F2) :=
    LinearMap.finrank_range_add_finrank_ker (sumVerticesLin (n + 1))
  have hker_eq :
      1 + Module.finrank F2 ↥((sumVerticesLin (n + 1)).ker) = n + 1 := by
    simpa [hrange_finrank, hdom_finrank] using hadd
  omega

private lemma finrank_range_incidence_succ (n : ℕ) :
    Module.finrank F2 ↥((incidenceLin (n + 1)).range) = n := by
  have hEq : (incidenceLin (n + 1)).range = (sumVerticesLin (n + 1)).ker :=
    range_incidence_eq_ker_sumVertices_succ n
  rw [hEq]
  exact finrank_ker_sumVertices_succ n

private lemma finrank_ker_incidence_succ (n : ℕ) :
    Module.finrank F2 ↥((incidenceLin (n + 1)).ker) = d (n + 1) - n := by
  have hdom_finrank :
      Module.finrank F2 (Edge (n + 1) → F2) = d (n + 1) := by
    calc
      Module.finrank F2 (Edge (n + 1) → F2) = Fintype.card (Edge (n + 1)) := by
        simpa using (Module.finrank_fintype_fun_eq_card F2 (η := Edge (n + 1)))
      _ = d (n + 1) := card_Edge_eq_d (n + 1)
  have hrange_finrank :
      Module.finrank F2 ↥((incidenceLin (n + 1)).range) = n :=
    finrank_range_incidence_succ n
  have hadd :
      Module.finrank F2 ↥((incidenceLin (n + 1)).range)
        + Module.finrank F2 ↥((incidenceLin (n + 1)).ker)
        = Module.finrank F2 (Edge (n + 1) → F2) :=
    LinearMap.finrank_range_add_finrank_ker (incidenceLin (n + 1))
  have hker_eq :
      n + Module.finrank F2 ↥((incidenceLin (n + 1)).ker) = d (n + 1) := by
    simpa [hrange_finrank, hdom_finrank] using hadd
  omega

private def paritySubtypeEquivKer (n : ℕ) :
    {p : Edge n → Bool // parityEvenBool p} ≃ ↥((incidenceLin n).ker) where
  toFun := by
    intro p
    refine ⟨boolFuncEquivF2Func n p.1, ?_⟩
    change incidenceLin n (boolFuncEquivF2Func n p.1) = 0
    funext i
    exact (parityEvenBool_iff_incidence_zero n p.1).1 p.2 i
  invFun := by
    intro x
    let p : Edge n → Bool := (boolFuncEquivF2Func n).symm x.1
    refine ⟨p, ?_⟩
    apply (parityEvenBool_iff_incidence_zero n p).2
    intro i
    have hx0 : incidenceLin n x.1 = 0 := x.2
    have hi : incidenceLin n x.1 i = 0 := congrArg (fun f => f i) hx0
    have hi' : incidenceF2 n x.1 i = 0 := by
      change incidenceLin n x.1 i = 0
      exact hi
    have hp_eq : boolFuncEquivF2Func n p = x.1 := by
      simp [p]
    simpa [hp_eq] using hi'
  left_inv := by
    intro p
    apply Subtype.ext
    change (boolFuncEquivF2Func n).symm ((boolFuncEquivF2Func n) p.1) = p.1
    simpa using (Equiv.symm_apply_apply (boolFuncEquivF2Func n) p.1)
  right_inv := by
    intro x
    apply Subtype.ext
    change (boolFuncEquivF2Func n) ((boolFuncEquivF2Func n).symm x.1) = x.1
    simpa using (Equiv.apply_symm_apply (boolFuncEquivF2Func n) x.1)

set_option maxHeartbeats 1600000 in
private lemma card_parityCodes_succ (n : ℕ) :
    (parityCodes (n + 1)).card = 2 ^ (d (n + 1) - n) := by
  let V : Type := ↥((incidenceLin (n + 1)).ker)
  letI : Fintype V := by
    change Fintype ↥((incidenceLin (n + 1)).ker)
    exact Fintype.ofFinite _
  letI : AddCommGroup V := by
    change AddCommGroup ↥((incidenceLin (n + 1)).ker)
    infer_instance
  letI : Module F2 V := by
    change Module F2 ↥((incidenceLin (n + 1)).ker)
    infer_instance
  have hnat : Nat.card V = Nat.card F2 ^ Module.finrank F2 V := by
    exact @Module.natCard_eq_pow_finrank F2 V
      (by infer_instance) (by infer_instance)
      (show Module F2 V from by infer_instance)
      (by infer_instance)
  have hfin : Module.finrank F2 V = d (n + 1) - n := by
    simpa [V] using finrank_ker_incidence_succ n
  have hker :
      Fintype.card V = 2 ^ (d (n + 1) - n) := by
    calc
      Fintype.card V = Nat.card V := by simp [Nat.card_eq_fintype_card]
      _ = Nat.card F2 ^ Module.finrank F2 V := hnat
      _ = Fintype.card F2 ^ Module.finrank F2 V := by simp [Nat.card_eq_fintype_card]
      _ = 2 ^ Module.finrank F2 V := by simp [F2]
      _ = 2 ^ (d (n + 1) - n) := by simpa [hfin]
  calc
    (parityCodes (n + 1)).card
        = Fintype.card {p : Edge (n + 1) → Bool // parityEvenBool p} := by
            symm
            simpa [parityCodes] using
              (Fintype.card_subtype (fun p : Edge (n + 1) → Bool => parityEvenBool p))
    _ = Fintype.card V := by
          exact Fintype.card_congr (paritySubtypeEquivKer (n + 1))
    _ = 2 ^ (d (n + 1) - n) := hker

private lemma n_le_d_succ (n : ℕ) : n ≤ d (n + 1) := by
  unfold d
  calc
    n = Nat.choose n 1 := by simpa using (Nat.choose_one_right n).symm
    _ ≤ Nat.choose n 1 + Nat.choose n 2 := Nat.le_add_right _ _
    _ = Nat.choose (n + 1) 2 := by
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            (Nat.choose_succ_succ n 1).symm

private lemma bitsToFin4_nat_decomp (b0 b1 : Bool) :
    (bitsToFin4 (b0, b1) : ℕ) = (if b0 then 1 else 0) + 2 * (if b1 then 1 else 0) := by
  cases b0 <;> cases b1 <;> rfl

private lemma rowParitySum_bitsToLambdaCode (n : ℕ) (p h : Edge n → Bool) (i : Fin n) :
    rowParitySum (bitsToLambdaCode p h) i
      = paritySumBool p i + 2 * paritySumBool h i := by
  unfold rowParitySum edgeNatRowSum bitsToLambdaCode paritySumBool
  calc
    Finset.sum (edgesIncident n i) (fun e => (bitsToFin4 (p e, h e) : ℕ))
        = Finset.sum (edgesIncident n i)
            (fun e => (if p e then 1 else 0) + 2 * (if h e then 1 else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro e he
            simpa using bitsToFin4_nat_decomp (p e) (h e)
    _ = Finset.sum (edgesIncident n i) (fun e => if p e then 1 else 0)
          + Finset.sum (edgesIncident n i) (fun e => 2 * (if h e then 1 else 0)) := by
            simp [Finset.sum_add_distrib]
    _ = paritySumBool p i + 2 * paritySumBool h i := by
            rw [← Finset.mul_sum]
            simp [paritySumBool]

private lemma even_rowParitySum_bitsToLambdaCode_iff (n : ℕ) (p h : Edge n → Bool) (i : Fin n) :
    Even (rowParitySum (bitsToLambdaCode p h) i) ↔ Even (paritySumBool p i) := by
  rw [rowParitySum_bitsToLambdaCode]
  constructor
  · intro hs
    have htwo : Even (2 * paritySumBool h i) := even_two_mul _
    exact ((Nat.even_add).1 hs).2 htwo
  · intro hp
    have htwo : Even (2 * paritySumBool h i) := even_two_mul _
    have hiff : Even (paritySumBool p i) ↔ Even (2 * paritySumBool h i) :=
      ⟨fun _ => htwo, fun _ => hp⟩
    exact (Nat.even_add).2 hiff

private lemma rowParityEven_bitsToLambdaCode_iff (n : ℕ) (p h : Edge n → Bool) :
    rowParityEven (bitsToLambdaCode p h) ↔ parityEvenBool p := by
  unfold rowParityEven parityEvenBool
  constructor
  · intro hb i
    exact (even_rowParitySum_bitsToLambdaCode_iff n p h i).1 (hb i)
  · intro hp i
    exact (even_rowParitySum_bitsToLambdaCode_iff n p h i).2 (hp i)

private lemma card_boolFunctions_on_edges (n : ℕ) :
    Fintype.card (Edge n → Bool) = 2 ^ d n := by
  calc
    Fintype.card (Edge n → Bool) = Fintype.card Bool ^ Fintype.card (Edge n) := Fintype.card_fun
    _ = 2 ^ Fintype.card (Edge n) := by simp
    _ = 2 ^ d n := by simp [card_Edge_eq_d]

private def subtypeProdEquivSigma {A B : Type*} (P : A → Prop) :
    {ab : A × B // P ab.1} ≃ Σ a : {x : A // P x}, B where
  toFun := fun ab => ⟨⟨ab.1.1, ab.2⟩, ab.1.2⟩
  invFun := fun s => ⟨(s.1.1, s.2), s.1.2⟩
  left_inv := by intro ab; cases ab; rfl
  right_inv := by intro s; cases s; rfl

private def lambdaSubtypeEquivBits (n : ℕ) :
    {b : LambdaCode n // rowParityEven b}
      ≃ {ph : ((Edge n → Bool) × (Edge n → Bool)) // parityEvenBool ph.1} where
  toFun := by
    intro b
    refine ⟨(parityBit b.1, highBit b.1), ?_⟩
    have hb' :
        rowParityEven (bitsToLambdaCode (parityBit b.1) (highBit b.1)) := by
      simpa [bitsToLambdaCode_parity_high] using b.2
    exact (rowParityEven_bitsToLambdaCode_iff n (parityBit b.1) (highBit b.1)).1 hb'
  invFun := by
    intro ph
    refine ⟨bitsToLambdaCode ph.1.1 ph.1.2, ?_⟩
    exact (rowParityEven_bitsToLambdaCode_iff n ph.1.1 ph.1.2).2 ph.2
  left_inv := by
    intro b
    apply Subtype.ext
    simpa [bitsToLambdaCode_parity_high]
  right_inv := by
    intro ph
    rcases ph with ⟨ph, hph⟩
    cases ph with
    | mk p h =>
        apply Subtype.ext
        simp [parityBit_bitsToLambdaCode, highBit_bitsToLambdaCode]

private lemma card_lambdaCodes_eq_parityCodes_mul (n : ℕ) :
    (lambdaCodes n).card = (parityCodes n).card * 2 ^ d n := by
  have hsub :
      Fintype.card {b : LambdaCode n // rowParityEven b}
        = Fintype.card {ph : ((Edge n → Bool) × (Edge n → Bool)) // parityEvenBool ph.1} := by
    exact Fintype.card_congr (lambdaSubtypeEquivBits n)
  have hleft :
      Fintype.card {b : LambdaCode n // rowParityEven b} = (lambdaCodes n).card := by
    simpa [lambdaCodes] using
      (Fintype.card_subtype (fun b : LambdaCode n => rowParityEven b))
  have hright :
      Fintype.card {ph : ((Edge n → Bool) × (Edge n → Bool)) // parityEvenBool ph.1}
        = (parityCodes n).card * 2 ^ d n := by
    calc
      Fintype.card {ph : ((Edge n → Bool) × (Edge n → Bool)) // parityEvenBool ph.1}
          = Fintype.card (Sigma fun _ : {p : Edge n → Bool // parityEvenBool p} => (Edge n → Bool)) := by
              exact Fintype.card_congr (subtypeProdEquivSigma (fun p : Edge n → Bool => parityEvenBool p))
      _ = Fintype.card {p : Edge n → Bool // parityEvenBool p} * Fintype.card (Edge n → Bool) := by
              simp [Fintype.card_sigma]
      _ = (parityCodes n).card * Fintype.card (Edge n → Bool) := by
              simpa [parityCodes] using
                (Fintype.card_subtype (fun p : Edge n → Bool => parityEvenBool p))
      _ = (parityCodes n).card * 2 ^ d n := by
              rw [card_boolFunctions_on_edges]
  rw [← hleft, ← hright]
  exact hsub

def lambdaShifts (n : ℕ) : Finset (Edge n → ℝ) := by
  classical
  exact (lambdaCodes n).image (fun b => lambdaReal b)

private lemma card_lambdaShifts_eq_card_lambdaCodes (n : ℕ) :
    (lambdaShifts n).card = (lambdaCodes n).card := by
  classical
  unfold lambdaShifts
  exact Finset.card_image_of_injective (lambdaCodes n) (lambdaReal_injective n)

private lemma card_lambdaShifts_succ (n : ℕ) :
    (lambdaShifts (n + 1)).card = 2 ^ (2 * d (n + 1) - n) := by
  have hle : n ≤ d (n + 1) := n_le_d_succ n
  have hexp : (d (n + 1) - n) + d (n + 1) = 2 * d (n + 1) - n := by
    omega
  calc
    (lambdaShifts (n + 1)).card
        = (parityCodes (n + 1)).card * 2 ^ d (n + 1) := by
            rw [card_lambdaShifts_eq_card_lambdaCodes, card_lambdaCodes_eq_parityCodes_mul]
    _ = 2 ^ (d (n + 1) - n) * 2 ^ d (n + 1) := by
          rw [card_parityCodes_succ]
    _ = 2 ^ ((d (n + 1) - n) + d (n + 1)) := by
          rw [← Nat.pow_add]
    _ = 2 ^ (2 * d (n + 1) - n) := by
          simp [hexp]

lemma card_lambdaShifts_eq_pow_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    (lambdaShifts n).card = 2 ^ (2 * d n - n + 1) := by
  have hn' : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn')
  have hsucc : (lambdaShifts (m + 1)).card = 2 ^ (2 * d (m + 1) - m) :=
    card_lambdaShifts_succ m
  have hmle : m ≤ 2 * d (m + 1) := by
    calc
      m ≤ d (m + 1) := n_le_d_succ m
      _ ≤ 2 * d (m + 1) := by
            omega
  have hexp : 2 * d (m + 1) - m = 2 * d (m + 1) - (m + 1) + 1 := by
    by_cases hm0 : m = 0
    · omega
    · have hmpos : 1 ≤ m := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
      have hmle' : m + 1 ≤ 2 * d (m + 1) := by
        have hmd : m ≤ d (m + 1) := n_le_d_succ m
        calc
          m + 1 ≤ m + m := by omega
          _ ≤ d (m + 1) + d (m + 1) := by omega
          _ = 2 * d (m + 1) := by ring
      calc
        2 * d (m + 1) - m = (2 * d (m + 1) + 1) - (m + 1) := by
          simpa [Nat.succ_eq_add_one] using
            (Nat.succ_sub_succ_eq_sub (2 * d (m + 1)) m).symm
        _ = (2 * d (m + 1) - (m + 1)).succ := by
          simpa [Nat.succ_eq_add_one] using (Nat.succ_sub hmle')
        _ = 2 * d (m + 1) - (m + 1) + 1 := by
          rfl
  simpa [hexp] using hsucc

private lemma exp_nat_mul_pi_I (q : ℕ) :
    Complex.exp (((q : ℂ) * (Real.pi * Complex.I))) = (-1 : ℂ) ^ q := by
  calc
    Complex.exp (((q : ℂ) * (Real.pi * Complex.I)))
        = Complex.exp (q * (Real.pi * Complex.I)) := by simp
    _ = Complex.exp (Real.pi * Complex.I) ^ q := by
          simpa using (Complex.exp_nat_mul (Real.pi * Complex.I) q)
    _ = (-1 : ℂ) ^ q := by simp [Complex.exp_pi_mul_I]

private lemma exp_nat_mul_neg_pi_I (q : ℕ) :
    Complex.exp (((q : ℂ) * (-(Real.pi * Complex.I)))) = (-1 : ℂ) ^ q := by
  calc
    Complex.exp (((q : ℂ) * (-(Real.pi * Complex.I))))
        = Complex.exp (q * (-(Real.pi * Complex.I))) := by simp
    _ = Complex.exp (-(Real.pi * Complex.I)) ^ q := by
          simpa using (Complex.exp_nat_mul (-(Real.pi * Complex.I)) q)
    _ = (-1 : ℂ) ^ q := by
          simp [Complex.exp_neg, Complex.exp_pi_mul_I]

private lemma exp_neg_two_mul_lambdaReal_Z (n : ℕ) (b : LambdaCode n) (e : Edge n) (y : Fin n → Bool) :
    Complex.exp (Complex.I * (((-2 : ℝ) * lambdaReal b e * Z y e : ℝ) : ℂ))
      = (-1 : ℂ) ^ (b e : ℕ) := by
  rcases (Z_eq_one_or_neg_one y e) with hZ1 | hZm1
  · have hrew :
      Complex.I * (((-2 : ℝ) * lambdaReal b e * Z y e : ℝ) : ℂ)
        = ((b e : ℂ) * (-(Real.pi * Complex.I))) := by
      rw [hZ1]
      unfold lambdaReal quarterReal
      calc
        Complex.I * (((-2 : ℝ) * (((b e : ℕ) : ℝ) * (Real.pi / 2)) * (1 : ℝ) : ℝ) : ℂ)
            = Complex.I * ((-(((b e : ℕ) : ℝ) * Real.pi) : ℝ) : ℂ) := by ring
        _ = ((b e : ℂ) * (-(Real.pi * Complex.I))) := by
              calc
                Complex.I * ((-(((b e : ℕ) : ℝ) * Real.pi) : ℝ) : ℂ)
                    = Complex.I * (-((b e : ℂ) * (Real.pi : ℂ))) := by norm_num
                _ = ((b e : ℂ) * (-(Real.pi * Complex.I))) := by ring
    rw [hrew, exp_nat_mul_neg_pi_I]
  · have hrew :
      Complex.I * (((-2 : ℝ) * lambdaReal b e * Z y e : ℝ) : ℂ)
        = ((b e : ℂ) * (Real.pi * Complex.I)) := by
      rw [hZm1]
      unfold lambdaReal quarterReal
      calc
        Complex.I * (((-2 : ℝ) * (((b e : ℕ) : ℝ) * (Real.pi / 2)) * (-1 : ℝ) : ℝ) : ℂ)
            = Complex.I * (((2 : ℝ) * (((b e : ℕ) : ℝ) * (Real.pi / 2)) : ℝ) : ℂ) := by
                ring_nf
        _ = Complex.I * ((((b e : ℕ) : ℝ) * Real.pi : ℝ) : ℂ) := by
              have hreal :
                  (2 : ℝ) * (((b e : ℕ) : ℝ) * (Real.pi / 2))
                    = (((b e : ℕ) : ℝ) * Real.pi) := by ring
              rw [hreal]
        _ = ((b e : ℂ) * (Real.pi * Complex.I)) := by
              calc
                Complex.I * ((((b e : ℕ) : ℝ) * Real.pi : ℝ) : ℂ)
                    = Complex.I * ((b e : ℂ) * (Real.pi : ℂ)) := by norm_num
                _ = ((b e : ℂ) * (Real.pi * Complex.I)) := by ring
    rw [hrew, exp_nat_mul_pi_I]

private lemma exp_phase_eq_prod (n : ℕ) (lam : Edge n → ℝ) (y : Fin n → Bool) :
    Complex.exp (Complex.I * (phase lam y : ℂ))
      = ∏ e : Edge n, Complex.exp (Complex.I * ((lam e * Z y e : ℝ) : ℂ)) := by
  unfold phase
  calc
    Complex.exp (Complex.I * ((∑ e : Edge n, lam e * Z y e : ℝ) : ℂ))
        = Complex.exp (∑ e : Edge n, Complex.I * ((lam e * Z y e : ℝ) : ℂ)) := by
            simp [Finset.mul_sum]
    _ = ∏ e : Edge n, Complex.exp (Complex.I * ((lam e * Z y e : ℝ) : ℂ)) := by
          simpa using (Complex.exp_sum (Finset.univ : Finset (Edge n))
            (fun e : Edge n => Complex.I * ((lam e * Z y e : ℝ) : ℂ)))

private lemma rowParityEven_prod_neg_one_pow_incident (n : ℕ) (b : LambdaCode n)
    (hb : rowParityEven b) (i : Fin n) :
    ∏ e ∈ edgesIncident n i, (-1 : ℂ) ^ (b e : ℕ) = 1 := by
  have hpow :
      ∏ e ∈ edgesIncident n i, (-1 : ℂ) ^ (b e : ℕ)
        = (-1 : ℂ) ^ (rowParitySum b i) := by
    unfold rowParitySum edgeNatRowSum
    simpa using
      (Finset.prod_pow_eq_pow_sum (edgesIncident n i) (fun e => (b e : ℕ)) (-1 : ℂ))
  rcases hb i with ⟨k, hk⟩
  rw [hpow, hk, ← two_mul k, pow_mul, neg_one_sq, one_pow]

private lemma exp_phase_lambdaReal_flip_at (n : ℕ) (b : LambdaCode n)
    (hb : rowParityEven b) (i : Fin n) (y : Fin n → Bool) :
    Complex.exp (Complex.I * (phase (lambdaReal b) (flipBoolAt i y) : ℂ))
      = Complex.exp (Complex.I * (phase (lambdaReal b) y : ℂ)) := by
  rw [exp_phase_eq_prod n (lambdaReal b) (flipBoolAt i y), exp_phase_eq_prod n (lambdaReal b) y]
  have hterm : ∀ e : Edge n,
      Complex.exp (Complex.I * ((lambdaReal b e * Z (flipBoolAt i y) e : ℝ) : ℂ))
        = ((if e ∈ edgesIncident n i then (-1 : ℂ) ^ (b e : ℕ) else 1)
            * Complex.exp (Complex.I * ((lambdaReal b e * Z y e : ℝ) : ℂ))) := by
    intro e
    by_cases he : e ∈ edgesIncident n i
    · have hZ : Z (flipBoolAt i y) e = - Z y e := by
        simpa [he] using (Z_flip_at i y e)
      have hreal :
          lambdaReal b e * (- Z y e)
            = (-2 : ℝ) * lambdaReal b e * Z y e + lambdaReal b e * Z y e := by ring
      calc
        Complex.exp (Complex.I * ((lambdaReal b e * Z (flipBoolAt i y) e : ℝ) : ℂ))
            = Complex.exp (Complex.I * ((lambdaReal b e * (- Z y e) : ℝ) : ℂ)) := by simp [hZ]
        _ = Complex.exp (Complex.I * (((-2 : ℝ) * lambdaReal b e * Z y e +
                lambdaReal b e * Z y e : ℝ) : ℂ)) := by simp [hreal]
        _ = Complex.exp (Complex.I * (((-2 : ℝ) * lambdaReal b e * Z y e : ℝ) : ℂ)
                + Complex.I * ((lambdaReal b e * Z y e : ℝ) : ℂ)) := by
              simp [mul_add]
        _ = Complex.exp (Complex.I * (((-2 : ℝ) * lambdaReal b e * Z y e : ℝ) : ℂ))
                * Complex.exp (Complex.I * ((lambdaReal b e * Z y e : ℝ) : ℂ)) := by
              rw [Complex.exp_add]
        _ = ((-1 : ℂ) ^ (b e : ℕ))
              * Complex.exp (Complex.I * ((lambdaReal b e * Z y e : ℝ) : ℂ)) := by
              rw [exp_neg_two_mul_lambdaReal_Z]
        _ = ((if e ∈ edgesIncident n i then (-1 : ℂ) ^ (b e : ℕ) else 1)
              * Complex.exp (Complex.I * ((lambdaReal b e * Z y e : ℝ) : ℂ))) := by simp [he]
    · have hZ : Z (flipBoolAt i y) e = Z y e := by
        simpa [he] using (Z_flip_at i y e)
      simp [hZ, he]
  calc
    (∏ e : Edge n, Complex.exp (Complex.I * ((lambdaReal b e * Z (flipBoolAt i y) e : ℝ) : ℂ)))
        = ∏ e : Edge n, ((if e ∈ edgesIncident n i then (-1 : ℂ) ^ (b e : ℕ) else 1)
            * Complex.exp (Complex.I * ((lambdaReal b e * Z y e : ℝ) : ℂ))) := by
            refine Finset.prod_congr rfl ?_
            intro e he
            exact hterm e
    _ = (∏ e : Edge n, (if e ∈ edgesIncident n i then (-1 : ℂ) ^ (b e : ℕ) else 1))
          * (∏ e : Edge n, Complex.exp (Complex.I * ((lambdaReal b e * Z y e : ℝ) : ℂ))) := by
            simpa using (Finset.prod_mul_distrib
              (s := (Finset.univ : Finset (Edge n)))
              (f := fun e : Edge n => if e ∈ edgesIncident n i then (-1 : ℂ) ^ (b e : ℕ) else 1)
              (g := fun e : Edge n => Complex.exp (Complex.I * ((lambdaReal b e * Z y e : ℝ) : ℂ))))
    _ = (∏ e ∈ (Finset.univ : Finset (Edge n)) with e ∈ edgesIncident n i, (-1 : ℂ) ^ (b e : ℕ))
          * (∏ e : Edge n, Complex.exp (Complex.I * ((lambdaReal b e * Z y e : ℝ) : ℂ))) := by
            congr 1
            symm
            exact Finset.prod_filter (fun e : Edge n => e ∈ edgesIncident n i)
              (fun e : Edge n => (-1 : ℂ) ^ (b e : ℕ))
    _ = (∏ e ∈ edgesIncident n i, (-1 : ℂ) ^ (b e : ℕ))
          * (∏ e : Edge n, Complex.exp (Complex.I * ((lambdaReal b e * Z y e : ℝ) : ℂ))) := by
            congr 1
            have hfilter :
                ((Finset.univ : Finset (Edge n)).filter (fun e => e ∈ edgesIncident n i))
                  = edgesIncident n i := by
              ext e
              simp
            rw [hfilter]
    _ = (1 : ℂ)
          * (∏ e : Edge n, Complex.exp (Complex.I * ((lambdaReal b e * Z y e : ℝ) : ℂ))) := by
            rw [rowParityEven_prod_neg_one_pow_incident n b hb i]
    _ = ∏ e : Edge n, Complex.exp (Complex.I * ((lambdaReal b e * Z y e : ℝ) : ℂ)) := by simp

private lemma exp_phase_lambdaReal_const_on_yOfSet (n : ℕ) (b : LambdaCode n)
    (hb : rowParityEven b) :
    ∀ S : Finset (Fin n),
      Complex.exp (Complex.I * (phase (lambdaReal b) (yOfSet S) : ℂ))
        = Complex.exp (Complex.I * (phase (lambdaReal b) (yOfSet (∅ : Finset (Fin n))) : ℂ)) := by
  refine Finset.induction ?_ ?_
  · simp
  · intro i S hi hS
    have hflip := exp_phase_lambdaReal_flip_at n b hb i (yOfSet S)
    have hins : yOfSet (insert i S) = flipBoolAt i (yOfSet S) := yOfSet_insert_eq_flip S i hi
    calc
      Complex.exp (Complex.I * (phase (lambdaReal b) (yOfSet (insert i S)) : ℂ))
          = Complex.exp (Complex.I * (phase (lambdaReal b) (flipBoolAt i (yOfSet S)) : ℂ)) := by
              simp [hins]
      _ = Complex.exp (Complex.I * (phase (lambdaReal b) (yOfSet S) : ℂ)) := hflip
      _ = Complex.exp (Complex.I * (phase (lambdaReal b) (yOfSet (∅ : Finset (Fin n))) : ℂ)) := hS

private lemma exp_phase_lambdaReal_const (n : ℕ) (b : LambdaCode n)
    (hb : rowParityEven b) (y : Fin n → Bool) :
    Complex.exp (Complex.I * (phase (lambdaReal b) y : ℂ))
      = Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ)) := by
  have hS := exp_phase_lambdaReal_const_on_yOfSet n b hb
    ((Finset.univ : Finset (Fin n)).filter (fun i => y i))
  have hy : y = yOfSet ((Finset.univ : Finset (Fin n)).filter (fun i => y i)) :=
    y_eq_yOfSet_trueSupport y
  have hy' : yOfSet ((Finset.univ : Finset (Fin n)).filter (fun i => y i)) = y := hy.symm
  have h0 : yOfSet (∅ : Finset (Fin n)) = (fun _ : Fin n => false) := by
    funext i
    simp [yOfSet]
  calc
    Complex.exp (Complex.I * (phase (lambdaReal b) y : ℂ))
        = Complex.exp
            (Complex.I * (phase (lambdaReal b)
              (yOfSet ((Finset.univ : Finset (Fin n)).filter (fun i => y i))) : ℂ)) := by
              rw [hy']
    _ = Complex.exp (Complex.I * (phase (lambdaReal b) (yOfSet (∅ : Finset (Fin n))) : ℂ)) := hS
    _ = Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ)) := by
          rw [h0]

private lemma psi_translate_lambdaReal (n : ℕ) (b : LambdaCode n)
    (hb : rowParityEven b) (lam : Edge n → ℝ) :
    psi n (fun e => lambdaReal b e + lam e)
      = (Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ))) * psi n lam := by
  have hconst :
      ∀ y : Fin n → Bool,
      Complex.exp (Complex.I * (phase (lambdaReal b) y : ℂ))
        = Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ)) :=
    exp_phase_lambdaReal_const n b hb
  unfold psi
  have hsum :
      (∑ y : Fin n → Bool,
        Complex.exp (Complex.I * (phase (fun e => lambdaReal b e + lam e) y : ℂ)))
        = ∑ y : Fin n → Bool,
            (Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ)))
              * Complex.exp (Complex.I * (phase lam y : ℂ)) := by
    refine Finset.sum_congr rfl ?_
    intro y hy
    have hadd :
        phase (fun e => lambdaReal b e + lam e) y
          = phase (lambdaReal b) y + phase lam y := by
      simpa using phase_add (lam₁ := lambdaReal b) (lam₂ := lam) y
    calc
      Complex.exp (Complex.I * (phase (fun e => lambdaReal b e + lam e) y : ℂ))
          = Complex.exp (Complex.I * ((phase (lambdaReal b) y + phase lam y : ℝ) : ℂ)) := by simp [hadd]
      _ = Complex.exp ((Complex.I * (phase (lambdaReal b) y : ℂ))
              + (Complex.I * (phase lam y : ℂ))) := by
            simp [mul_add]
      _ = Complex.exp (Complex.I * (phase (lambdaReal b) y : ℂ))
              * Complex.exp (Complex.I * (phase lam y : ℂ)) := by rw [Complex.exp_add]
      _ = (Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ)))
              * Complex.exp (Complex.I * (phase lam y : ℂ)) := by simp [hconst y]
  have hfactor :
      (∑ y : Fin n → Bool,
        (Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ)))
          * Complex.exp (Complex.I * (phase lam y : ℂ)))
      = (Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ)))
          * (∑ y : Fin n → Bool, Complex.exp (Complex.I * (phase lam y : ℂ))) := by
    simpa [Finset.mul_sum]
  calc
    (∑ y : Fin n → Bool,
      Complex.exp (Complex.I * (phase (fun e => lambdaReal b e + lam e) y : ℂ))) / (2 ^ n : ℂ)
        = (∑ y : Fin n → Bool,
            (Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ)))
              * Complex.exp (Complex.I * (phase lam y : ℂ))) / (2 ^ n : ℂ) := by
            simp [hsum]
    _ = ((Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ)))
          * (∑ y : Fin n → Bool, Complex.exp (Complex.I * (phase lam y : ℂ)))) / (2 ^ n : ℂ) := by
            simp [hfactor]
    _ = (Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ)))
          * ((∑ y : Fin n → Bool, Complex.exp (Complex.I * (phase lam y : ℂ))) / (2 ^ n : ℂ)) := by
            simp [div_eq_mul_inv, mul_left_comm, mul_comm]

private lemma exp_nat_mul_pi_div_two_I (q : ℕ) :
    Complex.exp (((q : ℂ) * ((Real.pi / 2 : ℝ) * Complex.I))) = Complex.I ^ q := by
  calc
    Complex.exp (((q : ℂ) * ((Real.pi / 2 : ℝ) * Complex.I)))
        = Complex.exp (q * ((Real.pi / 2 : ℝ) * Complex.I)) := by simp
    _ = Complex.exp (((Real.pi / 2 : ℝ) * Complex.I) : ℂ) ^ q := by
          simpa using (Complex.exp_nat_mul (((Real.pi / 2 : ℝ) * Complex.I) : ℂ) q)
    _ = Complex.I ^ q := by simp [Complex.exp_pi_div_two_mul_I]

private lemma phase_lambdaReal_false (n : ℕ) (b : LambdaCode n) :
    phase (lambdaReal b) (fun _ : Fin n => false)
      = (Real.pi / 2) * (∑ e : Edge n, (b e : ℕ)) := by
  unfold phase lambdaReal quarterReal Z
  simp [spin, mul_left_comm, mul_comm, Finset.mul_sum]

private lemma exp_phase_lambdaReal_false_pow_four_mul (n : ℕ) (b : LambdaCode n) (t : ℕ) :
    (Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ))) ^ (4 * t) = 1 := by
  let s : ℕ := ∑ e : Edge n, (b e : ℕ)
  have hphase :
      phase (lambdaReal b) (fun _ : Fin n => false)
        = (Real.pi / 2) * s := by
    simp [s, phase_lambdaReal_false]
  have hrew :
      Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ))
        = Complex.exp (((s : ℂ) * ((Real.pi / 2 : ℝ) * Complex.I))) := by
    rw [hphase]
    norm_num [mul_assoc, mul_comm, mul_left_comm]
  rw [hrew, exp_nat_mul_pi_div_two_I]
  calc
    (Complex.I ^ s) ^ (4 * t)
        = ((Complex.I ^ s) ^ 4) ^ t := by rw [pow_mul]
    _ = (Complex.I ^ (s * 4)) ^ t := by rw [pow_mul]
    _ = (Complex.I ^ (4 * s)) ^ t := by rw [Nat.mul_comm]
    _ = ((Complex.I ^ 4) ^ s) ^ t := by rw [pow_mul]
    _ = 1 := by simp

private lemma psi_pow_translate_lambdaReal (n t : ℕ) (b : LambdaCode n)
    (hb : rowParityEven b) (lam : Edge n → ℝ) :
    psi n (fun e => lambdaReal b e + lam e) ^ (4 * t) = psi n lam ^ (4 * t) := by
  have hpsi := psi_translate_lambdaReal n b hb lam
  have hroot :
      (Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ))) ^ (4 * t) = 1 :=
    exp_phase_lambdaReal_false_pow_four_mul n b t
  calc
    psi n (fun e => lambdaReal b e + lam e) ^ (4 * t)
        = ((Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ))) * psi n lam) ^ (4 * t) := by
            simpa [hpsi]
    _ = (Complex.exp (Complex.I * (phase (lambdaReal b) (fun _ : Fin n => false) : ℂ))) ^ (4 * t)
          * (psi n lam) ^ (4 * t) := by
            rw [mul_pow]
    _ = (1 : ℂ) * (psi n lam) ^ (4 * t) := by rw [hroot]
    _ = psi n lam ^ (4 * t) := by simp

private lemma psi_pow_translate_lambdaShift (n t : ℕ) (a : Edge n → ℝ)
    (ha : a ∈ lambdaShifts n) (lam : Edge n → ℝ) :
    psi n (fun e => a e + lam e) ^ (4 * t) = psi n lam ^ (4 * t) := by
  classical
  unfold lambdaShifts at ha
  rcases Finset.mem_image.mp ha with ⟨b, hbmem, hba⟩
  have hb : rowParityEven b := by
    unfold lambdaCodes at hbmem
    exact (Finset.mem_filter.mp hbmem).2
  simpa [hba] using psi_pow_translate_lambdaReal n t b hb lam

private lemma measurableSet_localBox (n : ℕ) : MeasurableSet (localBox n) := by
  unfold localBox
  simp

private lemma integral_translateSet (n : ℕ) (a : Edge n → ℝ) (S : Set (Edge n → ℝ))
    (f : (Edge n → ℝ) → ℝ)
    (hS : MeasurableSet S) :
    (∫ x in translateSet a S, f x) = ∫ x in S, f (x + a) := by
  have hmeas_trans : MeasurableSet (translateSet a S) := by
    unfold translateSet
    exact (measurable_id.sub measurable_const) hS
  have hshift :
      ∫ x : Edge n → ℝ, Set.indicator (translateSet a S) f (x + a)
        = ∫ x : Edge n → ℝ, Set.indicator (translateSet a S) f x := by
    simpa using
      (MeasureTheory.integral_add_right_eq_self
        (μ := MeasureTheory.volume)
        (f := fun x : Edge n → ℝ => Set.indicator (translateSet a S) f x)
        a)
  have hleft :
      (fun x : Edge n → ℝ => Set.indicator (translateSet a S) f (x + a))
        = fun x => Set.indicator S (fun y => f (y + a)) x := by
    funext x
    by_cases hx : x ∈ S
    · have hmem : x + a ∈ translateSet a S := by
        change (x + a - a) ∈ S
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hx
      simp [hx, hmem]
    · have hnot : x + a ∉ translateSet a S := by
        intro hxmem
        exact hx (by
          change (x + a - a) ∈ S at hxmem
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxmem)
      simp [hx, hnot]
  have hshift2 :
      ∫ x : Edge n → ℝ, Set.indicator S (fun y => f (y + a)) x
        = ∫ x in translateSet a S, f x := by
    calc
      ∫ x : Edge n → ℝ, Set.indicator S (fun y => f (y + a)) x
          = ∫ x : Edge n → ℝ, Set.indicator (translateSet a S) f (x + a) := by
              simp [hleft]
      _ = ∫ x : Edge n → ℝ, Set.indicator (translateSet a S) f x := hshift
      _ = ∫ x in translateSet a S, f x := by
            simpa using (MeasureTheory.integral_indicator (μ := MeasureTheory.volume)
              (f := f) (hs := hmeas_trans))
  calc
    ∫ x in translateSet a S, f x
        = ∫ x : Edge n → ℝ, Set.indicator S (fun y => f (y + a)) x := by
            symm
            exact hshift2
    _ = ∫ x in S, f (x + a) := by
          simpa using (MeasureTheory.integral_indicator (μ := MeasureTheory.volume)
            (f := fun y => f (y + a)) (hs := hS))

private lemma mem_lambdaShifts_iff_exists (n : ℕ) (a : Edge n → ℝ) :
    a ∈ lambdaShifts n ↔ ∃ b : LambdaCode n, b ∈ lambdaCodes n ∧ lambdaReal b = a := by
  classical
  unfold lambdaShifts
  constructor
  · intro ha
    rcases Finset.mem_image.mp ha with ⟨b, hb, hba⟩
    exact ⟨b, hb, hba⟩
  · rintro ⟨b, hb, hba⟩
    exact Finset.mem_image.mpr ⟨b, hb, hba⟩

lemma delta_lt_pi_div_four : delta < Real.pi / 4 := by
  unfold delta
  nlinarith [Real.pi_pos]

private lemma two_delta_lt_pi_div_two : 2 * delta < Real.pi / 2 := by
  have h : delta < Real.pi / 4 := delta_lt_pi_div_four
  linarith

private lemma quarterReal_abs_sub_ge_pi_div_two {q1 q2 : Fin 4} (hneq : q1 ≠ q2) :
    Real.pi / 2 ≤ |quarterReal q1 - quarterReal q2| := by
  have hpi2_nonneg : (0 : ℝ) ≤ Real.pi / 2 := by positivity [Real.pi_pos]
  have hq_nat : (q1 : Nat) ≠ (q2 : Nat) := by
    intro h
    apply hneq
    exact Fin.ext h
  have hq_int : (q1 : ℤ) ≠ (q2 : ℤ) := by
    exact_mod_cast hq_nat
  have habs_int : (1 : ℤ) ≤ |(q1 : ℤ) - (q2 : ℤ)| := by
    exact Int.one_le_abs (sub_ne_zero.mpr hq_int)
  have habs_real : (1 : ℝ) ≤ |(((q1 : ℤ) - (q2 : ℤ) : ℤ) : ℝ)| := by
    exact_mod_cast habs_int
  have hrepr :
      quarterReal q1 - quarterReal q2
        = ((((q1 : ℤ) - (q2 : ℤ) : ℤ) : ℝ) * (Real.pi / 2)) := by
    calc
      quarterReal q1 - quarterReal q2
          = ((q1 : ℤ) : ℝ) * (Real.pi / 2) - ((q2 : ℤ) : ℝ) * (Real.pi / 2) := by
              simp [quarterReal]
      _ = ((((q1 : ℤ) - (q2 : ℤ) : ℤ) : ℝ) * (Real.pi / 2)) := by
            rw [Int.cast_sub]
            ring
  have habs_mul :
      |quarterReal q1 - quarterReal q2|
        = |(((q1 : ℤ) - (q2 : ℤ) : ℤ) : ℝ)| * (Real.pi / 2) := by
    rw [hrepr, abs_mul, abs_of_nonneg hpi2_nonneg]
  calc
    Real.pi / 2 = (1 : ℝ) * (Real.pi / 2) := by ring
    _ ≤ |(((q1 : ℤ) - (q2 : ℤ) : ℤ) : ℝ)| * (Real.pi / 2) :=
      mul_le_mul_of_nonneg_right habs_real hpi2_nonneg
    _ = |quarterReal q1 - quarterReal q2| := habs_mul.symm

private lemma exists_coord_sep_of_distinct_shifts (n : ℕ) {a b : Edge n → ℝ}
    (ha : a ∈ lambdaShifts n) (hb : b ∈ lambdaShifts n) (hneq : a ≠ b) :
    ∃ e : Edge n, Real.pi / 2 ≤ |a e - b e| := by
  classical
  rcases (mem_lambdaShifts_iff_exists n a).1 ha with ⟨ba, hba_mem, hba⟩
  rcases (mem_lambdaShifts_iff_exists n b).1 hb with ⟨bb, hbb_mem, hbb⟩
  have hnefun : ¬ ∀ e : Edge n, a e = b e := by
    intro hall
    apply hneq
    exact funext hall
  rcases not_forall.mp hnefun with ⟨e, he⟩
  refine ⟨e, ?_⟩
  have hae : a e = quarterReal (ba e) := by
    simpa [lambdaReal] using congrArg (fun f => f e) hba.symm
  have hbe : b e = quarterReal (bb e) := by
    simpa [lambdaReal] using congrArg (fun f => f e) hbb.symm
  have hqneq : ba e ≠ bb e := by
    intro hq
    apply he
    linarith [hae, hbe, congrArg quarterReal hq]
  calc
    Real.pi / 2 ≤ |quarterReal (ba e) - quarterReal (bb e)| :=
      quarterReal_abs_sub_ge_pi_div_two hqneq
    _ = |a e - b e| := by simpa [hae, hbe]

/-- Union of all local boxes centered at quarter-lattice shifts. -/
private def NdeltaCoreSet (n : ℕ) : Set (Edge n → ℝ) :=
  ⋃ a ∈ lambdaShifts n, translateSet a (localBox n)

/-- Near region of the torus decomposition. -/
private def NdeltaSet (n : ℕ) : Set (Edge n → ℝ) :=
  torusBox n ∩ NdeltaCoreSet n

/-- Residual region of the torus decomposition. -/
private def RdeltaSet (n : ℕ) : Set (Edge n → ℝ) :=
  torusBox n \ NdeltaSet n

private lemma measurableSet_translate_localBox (n : ℕ) (a : Edge n → ℝ) :
    MeasurableSet (translateSet a (localBox n)) := by
  unfold translateSet
  exact (measurableSet_localBox n).preimage (measurable_id.sub_const a)

private lemma measurableSet_NdeltaCoreSet (n : ℕ) : MeasurableSet (NdeltaCoreSet n) := by
  unfold NdeltaCoreSet
  classical
  simpa using Finset.measurableSet_biUnion (lambdaShifts n)
    (fun a ha => measurableSet_translate_localBox n a)

private lemma measurableSet_NdeltaSet (n : ℕ) : MeasurableSet (NdeltaSet n) := by
  unfold NdeltaSet
  exact (measurableSet_torusBox n).inter (measurableSet_NdeltaCoreSet n)

private lemma measurableSet_RdeltaSet (n : ℕ) : MeasurableSet (RdeltaSet n) := by
  unfold RdeltaSet
  exact (measurableSet_torusBox n).diff (measurableSet_NdeltaSet n)

private lemma RdeltaSet_subset_torusBox (n : ℕ) : RdeltaSet n ⊆ torusBox n := by
  intro x hx
  exact hx.1

private lemma psi_norm_le_one (n : ℕ) (lam : Edge n → ℝ) : ‖psi n lam‖ ≤ 1 := by
  classical
  have hsum :
      ‖∑ y : Fin n → Bool, Complex.exp (Complex.I * (phase lam y : ℂ))‖
        ≤ ∑ y : Fin n → Bool, ‖Complex.exp (Complex.I * (phase lam y : ℂ))‖ := by
    simpa using (norm_sum_le (Finset.univ : Finset (Fin n → Bool))
      (fun y => Complex.exp (Complex.I * (phase lam y : ℂ))))
  unfold psi
  calc
    ‖(∑ y : Fin n → Bool, Complex.exp (Complex.I * (phase lam y : ℂ))) / (2 ^ n : ℂ)‖
        = ‖∑ y : Fin n → Bool, Complex.exp (Complex.I * (phase lam y : ℂ))‖ / ‖(2 ^ n : ℂ)‖ := by
            simp
    _ ≤ (∑ y : Fin n → Bool, ‖Complex.exp (Complex.I * (phase lam y : ℂ))‖) / ‖(2 ^ n : ℂ)‖ := by
          exact div_le_div_of_nonneg_right hsum (by positivity)
    _ = (∑ y : Fin n → Bool, (1 : ℝ)) / ‖(2 ^ n : ℂ)‖ := by
          congr
          ext y
          simp [Complex.norm_exp]
    _ = (2 ^ n : ℝ) / (2 ^ n : ℝ) := by simp
    _ = 1 := by
          field_simp

private lemma integrand_abs_le_one (n t : ℕ) (lam : Edge n → ℝ) :
    |Complex.re (psi n lam ^ (4 * t))| ≤ 1 := by
  have hre : |Complex.re (psi n lam ^ (4 * t))| ≤ ‖psi n lam ^ (4 * t)‖ := Complex.abs_re_le_norm _
  have hpow : ‖psi n lam ^ (4 * t)‖ = ‖psi n lam‖ ^ (4 * t) := by
    simpa using (Complex.norm_pow (psi n lam) (4 * t))
  have hpsi : ‖psi n lam‖ ≤ 1 := psi_norm_le_one n lam
  have hpsi_nonneg : 0 ≤ ‖psi n lam‖ := by positivity
  have hpow_le : ‖psi n lam‖ ^ (4 * t) ≤ 1 := by
    exact pow_le_one₀ hpsi_nonneg hpsi
  calc
    |Complex.re (psi n lam ^ (4 * t))| ≤ ‖psi n lam ^ (4 * t)‖ := hre
    _ = ‖psi n lam‖ ^ (4 * t) := hpow
    _ ≤ 1 := hpow_le

private lemma integrableOn_integrand_of_subset_torus (n t : ℕ) {s : Set (Edge n → ℝ)}
    (hs : s ⊆ torusBox n) :
    MeasureTheory.IntegrableOn (fun lam => Complex.re (psi n lam ^ (4 * t))) s := by
  have hs_ne_top : MeasureTheory.volume s ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono hs) (torusBox_isCompact n).measure_lt_top)
  have hconst : MeasureTheory.IntegrableOn (fun _ : Edge n → ℝ => (1 : ℝ)) s := by
    exact MeasureTheory.integrableOn_const hs_ne_top
  have hfsm : MeasureTheory.AEStronglyMeasurable
      (fun lam : Edge n → ℝ => Complex.re (psi n lam ^ (4 * t)))
      (MeasureTheory.volume.restrict s) :=
    (Complex.continuous_re.comp ((continuous_psi n).pow (4 * t))).aestronglyMeasurable
  have hbound :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict s),
        ‖Complex.re (psi n x ^ (4 * t))‖ ≤ (1 : ℝ) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    simpa [Real.norm_eq_abs] using integrand_abs_le_one n t x
  exact MeasureTheory.Integrable.mono' hconst hfsm hbound

private lemma hpointR_abs_from_gap (n t : ℕ)
    (hgap : ∀ lam ∈ RdeltaSet n, ‖psi n lam‖ ≤ Real.cos delta) :
    ∀ lam ∈ RdeltaSet n,
      |Complex.re (psi n lam ^ (4 * t))| ≤ remainderTerm t := by
  intro lam hlam
  have hnorm_nonneg : 0 ≤ ‖psi n lam‖ := by positivity
  have hpow_le :
      ‖psi n lam‖ ^ (4 * t) ≤ (Real.cos delta) ^ (4 * t) := by
    exact pow_le_pow_left₀ hnorm_nonneg (hgap lam hlam) (4 * t)
  have hnormpow : ‖psi n lam ^ (4 * t)‖ = ‖psi n lam‖ ^ (4 * t) := by
    simpa using (Complex.norm_pow (psi n lam) (4 * t))
  calc
    |Complex.re (psi n lam ^ (4 * t))| ≤ ‖psi n lam ^ (4 * t)‖ := Complex.abs_re_le_norm _
    _ = ‖psi n lam‖ ^ (4 * t) := hnormpow
    _ ≤ (Real.cos delta) ^ (4 * t) := hpow_le
    _ = remainderTerm t := by rfl

private lemma hRabs_from_pointwise_bound (n t : ℕ) (R : Set (Edge n → ℝ)) (B : ℝ)
    (hB_nonneg : 0 ≤ B) (hRmeas : MeasurableSet R) (hRsubset : R ⊆ torusBox n)
    (hpoint : ∀ lam ∈ R, |Complex.re (psi n lam ^ (4 * t))| ≤ B) :
    |∫ lam in R, Complex.re (psi n lam ^ (4 * t))|
      ≤ ((2 * Real.pi) ^ (d n : Nat) : ℝ) * B := by
  let f : (Edge n → ℝ) → ℝ := fun lam => Complex.re (psi n lam ^ (4 * t))
  have htorus_int : MeasureTheory.IntegrableOn f (torusBox n) := by
    exact (Complex.continuous_re.comp ((continuous_psi n).pow (4 * t))).continuousOn.integrableOn_compact
      (torusBox_isCompact n)
  have hRint : MeasureTheory.IntegrableOn f R := htorus_int.mono_set hRsubset
  have hR_ne_top : MeasureTheory.volume R ≠ ⊤ := by
    exact ne_of_lt <| lt_of_le_of_lt (MeasureTheory.measure_mono hRsubset) <| by
      rw [volume_torusBox_eq n]
      exact ENNReal.ofReal_lt_top
  have hnorm_int :
      ‖∫ x in R, f x‖ ≤ ∫ x in R, ‖f x‖ := by
    simpa [f] using
      (MeasureTheory.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume.restrict R) (f := f))
  have hconst_int :
      MeasureTheory.IntegrableOn (fun _ : Edge n → ℝ => B) R := by
    exact MeasureTheory.integrableOn_const hR_ne_top
  have hmono_ae :
      ∀ᵐ x ∂(MeasureTheory.volume.restrict R),
        ‖f x‖ ≤ B := by
    rw [MeasureTheory.ae_restrict_iff' (μ := MeasureTheory.volume) hRmeas]
    exact Filter.Eventually.of_forall (fun x hx => by
      simpa [Real.norm_eq_abs, f] using hpoint x hx)
  have hint :
      (∫ x in R, ‖f x‖) ≤ ∫ x in R, B := by
    exact MeasureTheory.integral_mono_ae hRint.norm hconst_int hmono_ae
  have hconst_eval :
      (∫ x in R, B) = MeasureTheory.volume.real R * B := by
    simp [MeasureTheory.integral_const, mul_comm]
  have hreal_eq :
      MeasureTheory.volume.real R = (MeasureTheory.volume R).toReal := by
    simp [MeasureTheory.Measure.real_def]
  have hvol_mul :
      (MeasureTheory.volume R).toReal * B
        ≤ ((2 * Real.pi) ^ (d n : Nat) : ℝ) * B := by
    exact mul_le_mul_of_nonneg_right
      (by
        have hmono : MeasureTheory.volume R ≤ MeasureTheory.volume (torusBox n) :=
          MeasureTheory.measure_mono hRsubset
        have htop : MeasureTheory.volume (torusBox n) ≠ ⊤ := by
          rw [volume_torusBox_eq n]
          exact ENNReal.ofReal_ne_top
        have htoReal : (MeasureTheory.volume R).toReal ≤ (MeasureTheory.volume (torusBox n)).toReal :=
          ENNReal.toReal_mono htop hmono
        simpa [volume_torusBox_toReal n] using htoReal)
      hB_nonneg
  calc
    |∫ x in R, f x| = ‖∫ x in R, f x‖ := by simp
    _ ≤ ∫ x in R, ‖f x‖ := hnorm_int
    _ ≤ ∫ x in R, B := hint
    _ = MeasureTheory.volume.real R * B := hconst_eval
    _ = (MeasureTheory.volume R).toReal * B := by rw [hreal_eq]
    _ ≤ ((2 * Real.pi) ^ (d n : Nat) : ℝ) * B := hvol_mul

private lemma hRabs_from_pointwise_abs (n t : ℕ) (R : Set (Edge n → ℝ))
    (hRmeas : MeasurableSet R) (hRsubset : R ⊆ torusBox n)
    (hpoint : ∀ lam ∈ R, |Complex.re (psi n lam ^ (4 * t))| ≤ remainderTerm t) :
    |∫ lam in R, Complex.re (psi n lam ^ (4 * t))|
      ≤ ((2 * Real.pi) ^ (d n : Nat) : ℝ) * remainderTerm t := by
  have hrem_nonneg : 0 ≤ remainderTerm t := by
    unfold remainderTerm
    have hpi2 : 0 < Real.pi / 2 := by positivity [Real.pi_pos]
    have hcos_nonneg : 0 ≤ Real.cos delta := by
      exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [delta_pos, hpi2]) delta_lt_pi_div_two.le
    exact pow_nonneg hcos_nonneg _
  exact hRabs_from_pointwise_bound n t R (remainderTerm t) hrem_nonneg
    hRmeas hRsubset hpoint

private lemma normalized_RdeltaContribution_abs_le_remainderTerm (n t : ℕ)
    (hgap : ∀ lam ∈ RdeltaSet n, ‖psi n lam‖ ≤ Real.cos delta) :
    |(1 / ((2 * Real.pi) ^ (d n : Nat) : ℝ)) *
        ∫ lam in RdeltaSet n, Complex.re (psi n lam ^ (4 * t))|
      ≤ remainderTerm t := by
  let vol : ℝ := ((2 * Real.pi) ^ (d n : Nat) : ℝ)
  have hvol_pos : 0 < vol := by
    dsimp [vol]
    positivity [Real.pi_pos]
  have habs :=
    hRabs_from_pointwise_abs n t (RdeltaSet n)
      (measurableSet_RdeltaSet n)
      (RdeltaSet_subset_torusBox n)
      (hpointR_abs_from_gap n t hgap)
  calc
    |(1 / vol) * ∫ lam in RdeltaSet n, Complex.re (psi n lam ^ (4 * t))|
        = (1 / vol) * |∫ lam in RdeltaSet n, Complex.re (psi n lam ^ (4 * t))| := by
            rw [abs_mul, abs_of_pos (one_div_pos.mpr hvol_pos)]
    _ ≤ (1 / vol) * (vol * remainderTerm t) := by
          exact mul_le_mul_of_nonneg_left habs (by positivity)
    _ = remainderTerm t := by
          field_simp [hvol_pos.ne']

private lemma normalized_RdeltaContribution_abs_le_exp_neg_half_t (n t : ℕ)
    (hgap : ∀ lam ∈ RdeltaSet n, ‖psi n lam‖ ≤ Real.cos delta) :
    |(1 / ((2 * Real.pi) ^ (d n : Nat) : ℝ)) *
        ∫ lam in RdeltaSet n, Complex.re (psi n lam ^ (4 * t))|
      ≤ Real.exp (-(t : ℝ) / 2) := by
  have hremainder_le_exp : remainderTerm t ≤ Real.exp (-(t : ℝ) / 2) := by
    have hcos_delta_le_seven_eighth : Real.cos delta ≤ (7 / 8 : ℝ) := by
      have hpi_div_six_lt_delta : Real.pi / 6 < delta := by
        unfold delta
        have hpi : 0 < Real.pi := Real.pi_pos
        nlinarith
      have hdelta_le_pi : delta ≤ Real.pi := by
        have hpi2_lt_pi : Real.pi / 2 < Real.pi := by
          nlinarith [Real.pi_pos]
        exact le_trans delta_lt_pi_div_two.le hpi2_lt_pi.le
      have hcos : Real.cos delta ≤ Real.cos (Real.pi / 6) := by
        exact Real.cos_le_cos_of_nonneg_of_le_pi
          (by positivity [Real.pi_pos])
          hdelta_le_pi
          (le_of_lt hpi_div_six_lt_delta)
      have hsqrt :
          (Real.sqrt 3) / 2 ≤ (7 / 8 : ℝ) := by
        have hsq : ((Real.sqrt 3) / 2) ^ 2 ≤ ((7 / 8 : ℝ) ^ 2) := by
          have hsq3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
            simp [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
          nlinarith [hsq3]
        have habs : |(Real.sqrt 3) / 2| ≤ |(7 / 8 : ℝ)| := (sq_le_sq).1 hsq
        have hleft_nonneg : 0 ≤ (Real.sqrt 3) / 2 := by positivity
        have hright_nonneg : 0 ≤ (7 / 8 : ℝ) := by norm_num
        simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs
      have hcos_val : Real.cos (Real.pi / 6) = Real.sqrt 3 / 2 := Real.cos_pi_div_six
      linarith [hcos, hcos_val, hsqrt]
    have hremainder_le_pow : remainderTerm t ≤ (7 / 8 : ℝ) ^ (4 * t) := by
      unfold remainderTerm
      have hpi2 : 0 < Real.pi / 2 := by positivity [Real.pi_pos]
      have hcos_nonneg : 0 ≤ Real.cos delta := by
        exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le
          (by linarith [delta_pos, hpi2]) delta_lt_pi_div_two.le
      exact pow_le_pow_left₀ hcos_nonneg hcos_delta_le_seven_eighth (4 * t)
    have hpow_le_exp : (7 / 8 : ℝ) ^ (4 * t) ≤ Real.exp (-(t : ℝ) / 2) := by
      have hbase_pos : 0 < (7 / 8 : ℝ) := by norm_num
      have hpow :
          (7 / 8 : ℝ) ^ (4 * t)
            = Real.exp (((4 * t : ℕ) : ℝ) * Real.log (7 / 8 : ℝ)) := by
        rw [← Real.rpow_natCast (7 / 8 : ℝ) (4 * t), Real.rpow_def_of_pos hbase_pos]
        ring_nf
      have hlin : (((4 * t : ℕ) : ℝ) * Real.log (7 / 8 : ℝ)) ≤ (-(t : ℝ) / 2) := by
        have hlog : Real.log (7 / 8 : ℝ) ≤ (-1 / 8 : ℝ) := by
          have hx : 0 < 1 + (-1 / 8 : ℝ) := by norm_num
          have h :
              Real.log (1 + (-1 / 8 : ℝ)) ≤ (-1 / 8 : ℝ) := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              (Real.log_le_sub_one_of_pos (x := 1 + (-1 / 8 : ℝ)) hx)
          have h1 : (1 + (-1 / 8 : ℝ)) = (7 / 8 : ℝ) := by norm_num
          simpa [h1] using h
        have ht_nonneg : 0 ≤ (t : ℝ) := by positivity
        have hmul : (t : ℝ) * (4 * Real.log (7 / 8 : ℝ)) ≤ (t : ℝ) * (-1 / 2 : ℝ) := by
          have h4 : (4 : ℝ) * Real.log (7 / 8 : ℝ) ≤ (-1 / 2 : ℝ) := by
            nlinarith [hlog]
          exact mul_le_mul_of_nonneg_left h4 ht_nonneg
        simpa [neg_div, mul_assoc, mul_left_comm, mul_comm] using hmul
      have hexp_le :
          Real.exp (((4 * t : ℕ) : ℝ) * Real.log (7 / 8 : ℝ)) ≤
            Real.exp (-(t : ℝ) / 2) :=
        Real.exp_le_exp.mpr hlin
      simpa [hpow] using hexp_le
    exact hremainder_le_pow.trans hpow_le_exp
  exact (normalized_RdeltaContribution_abs_le_remainderTerm n t hgap).trans
    hremainder_le_exp

end Cn3Torus

/-!
## Edge Coordinate Transport
The public transport maps `edgeLam` and `matrixOfEdge` identify matrix and edge
coordinates. The Boolean-encoding conversions below are kept internal so the
reader sees the transport results rather than the implementation vocabulary.
-/

/-- Translate `Fin 2` signs to Booleans. -/
private def fin2ToBool (b : Fin 2) : Bool := b = 1

/-- Translate Booleans back to `Fin 2`. -/
private def boolToFin2 (b : Bool) : Fin 2 := if b then 1 else 0

private lemma boolToFin2_fin2ToBool (b : Fin 2) : boolToFin2 (fin2ToBool b) = b := by
  fin_cases b <;> simp [fin2ToBool, boolToFin2]

private lemma fin2ToBool_boolToFin2 (b : Bool) : fin2ToBool (boolToFin2 b) = b := by
  cases b <;> simp [fin2ToBool, boolToFin2]

/-- Pointwise transport of sign vectors to the `Bool`-valued edge model. -/
def signVecToBoolVec {n : ℕ} (σ : Fin n → Fin 2) : Fin n → Bool :=
  fun i => fin2ToBool (σ i)

/-- Pointwise transport of `Bool`-valued vectors back to `Fin 2`. -/
private def boolVecToSignVec {n : ℕ} (y : Fin n → Bool) : Fin n → Fin 2 :=
  fun i => boolToFin2 (y i)

/-- Equivalence between the two encodings of sign vectors. -/
def signVecEquivBoolVec (n : ℕ) : (Fin n → Fin 2) ≃ (Fin n → Bool) where
  toFun := signVecToBoolVec
  invFun := boolVecToSignVec
  left_inv := by
    intro σ
    funext i
    exact boolToFin2_fin2ToBool (σ i)
  right_inv := by
    intro y
    funext i
    exact fin2ToBool_boolToFin2 (y i)

/-- Read a strict upper-triangular matrix as an edge-indexed function. -/
def edgeLam (n : ℕ) (lam : Fin n → Fin n → ℝ) : Cn3Torus.Edge n → ℝ :=
  fun e => lam e.1.1 e.1.2

/-- Embed edge coordinates back into the strict upper-triangular matrix model. -/
def matrixOfEdge (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if hij : i < j then mu ⟨(i, j), hij⟩ else 0

/-- Edge-to-matrix transport is continuous coordinatewise. -/
lemma continuous_matrixOfEdge (n : ℕ) :
    Continuous (matrixOfEdge n) := by
  refine continuous_pi ?_
  intro i
  refine continuous_pi ?_
  intro j
  by_cases hij : i < j
  · let e : Cn3Torus.Edge n := ⟨(i, j), hij⟩
    have hcoord : Continuous (fun mu : Cn3Torus.Edge n → ℝ => mu e) :=
      continuous_apply e
    simpa [e, matrixOfEdge, hij] using hcoord
  · simpa [matrixOfEdge, hij] using continuous_const

lemma edgeLam_matrixOfEdge (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    edgeLam n (matrixOfEdge n mu) = mu := by
  funext e
  rcases e with ⟨⟨i, j⟩, hij⟩
  simp [edgeLam, matrixOfEdge, hij]

lemma spin_fin2ToBool_eq_signOf (b : Fin 2) :
    Cn3Torus.spin (fin2ToBool b) = (signOf b : ℝ) := by
  fin_cases b <;> norm_num [fin2ToBool, Cn3Torus.spin, signOf]

lemma dim_eq_edgeDim (n : ℕ) : dim n = Cn3Torus.d n := by
  simp [dim, Cn3Torus.d]

lemma card_Edge_eq_dim (n : ℕ) : Fintype.card (Cn3Torus.Edge n) = dim n := by
  rw [dim_eq_edgeDim]
  exact Cn3Torus.card_Edge_eq_d n

lemma sNorm_eq_sqNormEdge (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    sNorm n lam = Cn3Torus.sqNormEdge n (edgeLam n lam) := by
  classical
  let pairs : Finset (Fin n × Fin n) := Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2
  have hprod :
      sNorm n lam
        = ∑ p : Fin n × Fin n,
            if p.1 < p.2 then lam p.1 p.2 ^ (2 : Nat) else 0 := by
    unfold sNorm
    simpa using
      (Fintype.sum_prod_type
        (fun p : Fin n × Fin n =>
          if p.1 < p.2 then lam p.1 p.2 ^ (2 : Nat) else 0)).symm
  have hfilter :
      (∑ p : Fin n × Fin n,
          if p.1 < p.2 then lam p.1 p.2 ^ (2 : Nat) else 0)
        = pairs.sum (fun p => lam p.1 p.2 ^ (2 : Nat)) := by
    unfold pairs
    rw [Finset.sum_filter]
  have hsub :
      pairs.sum (fun p => lam p.1 p.2 ^ (2 : Nat))
        = ∑ e : {p : Fin n × Fin n // p.1 < p.2}, lam e.1.1 e.1.2 ^ (2 : Nat) := by
    exact Finset.sum_subtype
      (p := fun p : Fin n × Fin n => p.1 < p.2)
      (s := pairs)
      (h := by
        intro p
        simp [pairs])
      (f := fun p : Fin n × Fin n => lam p.1 p.2 ^ (2 : Nat))
  have hedge :
      (∑ e : {p : Fin n × Fin n // p.1 < p.2}, lam e.1.1 e.1.2 ^ (2 : Nat))
        = ∑ e : Cn3Torus.Edge n, lam e.1.1 e.1.2 ^ (2 : Nat) := by
    rfl
  unfold Cn3Torus.sqNormEdge edgeLam
  exact hprod.trans (hfilter.trans (hsub.trans hedge))

lemma innerX_eq_edgePhase (n : ℕ) (lam : Fin n → Fin n → ℝ) (σ : Fin n → Fin 2) :
    innerX n lam σ =
      Cn3Torus.phase (edgeLam n lam) (signVecToBoolVec σ) := by
  classical
  let pairs : Finset (Fin n × Fin n) := Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2
  have hprod :
      innerX n lam σ
        = ∑ p : Fin n × Fin n,
            if p.1 < p.2 then
              lam p.1 p.2 * (signOf (σ p.1)) * (signOf (σ p.2))
            else 0 := by
    unfold innerX
    simpa using
      (Fintype.sum_prod_type
        (fun p : Fin n × Fin n =>
          if p.1 < p.2 then
            lam p.1 p.2 * (signOf (σ p.1)) * (signOf (σ p.2))
          else 0)).symm
  have hfilter :
      (∑ p : Fin n × Fin n,
          if p.1 < p.2 then
            lam p.1 p.2 * (signOf (σ p.1)) * (signOf (σ p.2))
          else 0)
        = pairs.sum (fun p => lam p.1 p.2 * (signOf (σ p.1)) * (signOf (σ p.2))) := by
    unfold pairs
    rw [Finset.sum_filter]
  have hsub :
      pairs.sum (fun p => lam p.1 p.2 * (signOf (σ p.1)) * (signOf (σ p.2)))
        = ∑ e : {p : Fin n × Fin n // p.1 < p.2},
            lam e.1.1 e.1.2 * (signOf (σ e.1.1)) * (signOf (σ e.1.2)) := by
    exact Finset.sum_subtype
      (p := fun p : Fin n × Fin n => p.1 < p.2)
      (s := pairs)
      (h := by
        intro p
        simp [pairs])
      (f := fun p : Fin n × Fin n =>
        lam p.1 p.2 * (signOf (σ p.1)) * (signOf (σ p.2)))
  have hedge :
      (∑ e : {p : Fin n × Fin n // p.1 < p.2},
          lam e.1.1 e.1.2 * (signOf (σ e.1.1)) * (signOf (σ e.1.2)))
        = ∑ e : Cn3Torus.Edge n,
            lam e.1.1 e.1.2 * (signOf (σ e.1.1)) * (signOf (σ e.1.2)) := by
    rfl
  unfold Cn3Torus.phase edgeLam signVecToBoolVec Cn3Torus.Z
  calc
    innerX n lam σ
        = ∑ e : Cn3Torus.Edge n,
            lam e.1.1 e.1.2 * (signOf (σ e.1.1)) * (signOf (σ e.1.2)) :=
          hprod.trans (hfilter.trans (hsub.trans hedge))
    _ = ∑ e : Cn3Torus.Edge n,
          lam e.1.1 e.1.2 *
            Cn3Torus.spin (fin2ToBool (σ e.1.1)) *
            Cn3Torus.spin (fin2ToBool (σ e.1.2)) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          rw [spin_fin2ToBool_eq_signOf, spin_fin2ToBool_eq_signOf]
    _ = ∑ e : Cn3Torus.Edge n,
          lam e.1.1 e.1.2 *
            (Cn3Torus.spin (fin2ToBool (σ e.1.1)) *
              Cn3Torus.spin (fin2ToBool (σ e.1.2))) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          ring

private lemma psi_eq_edgePsi (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    psi n lam = Cn3Torus.psi n (edgeLam n lam) := by
  have hsum :
      ∑ σ : Fin n → Fin 2, Complex.exp (Complex.I * ↑(innerX n lam σ))
        =
      ∑ y : Fin n → Bool, Complex.exp (Complex.I * ↑(Cn3Torus.phase (edgeLam n lam) y)) := by
    exact Fintype.sum_equiv (signVecEquivBoolVec n)
      (fun σ : Fin n → Fin 2 => Complex.exp (Complex.I * ↑(innerX n lam σ)))
      (fun y : Fin n → Bool => Complex.exp (Complex.I * ↑(Cn3Torus.phase (edgeLam n lam) y)))
      (by
        intro σ
        simp [signVecEquivBoolVec, innerX_eq_edgePhase])
  unfold psi Cn3Torus.psi
  simp [div_eq_mul_inv, hsum, mul_comm]

lemma sNorm_matrixOfEdge_eq (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    sNorm n (matrixOfEdge n mu) = Cn3Torus.sqNormEdge n mu := by
  rw [sNorm_eq_sqNormEdge, edgeLam_matrixOfEdge]

lemma psi_matrixOfEdge_eq (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    psi n (matrixOfEdge n mu) = Cn3Torus.psi n mu := by
  rw [psi_eq_edgePsi, edgeLam_matrixOfEdge]

/-- Integer-valued Boolean spin. -/
private def signBool (b : Bool) : ℤ := if b then 1 else -1

private lemma signBool_eq_signOf_boolToFin2 (b : Bool) : signBool b = signOf (boolToFin2 b) := by
  cases b <;> norm_num [signBool, boolToFin2, signOf]

private lemma signBool_coe_eq_spin (b : Bool) : (signBool b : ℝ) = Cn3Torus.spin b := by
  cases b <;> norm_num [signBool, Cn3Torus.spin]

private def ZInt {n : ℕ} (y : Fin n → Bool) (e : Cn3Torus.Edge n) : ℤ :=
  signBool (y e.1.1) * signBool (y e.1.2)

private lemma ZInt_coe_eq_Z {n : ℕ} (y : Fin n → Bool) (e : Cn3Torus.Edge n) :
    (ZInt y e : ℝ) = Cn3Torus.Z y e := by
  rcases e with ⟨⟨i, j⟩, hij⟩
  simp [ZInt, Cn3Torus.Z, signBool_coe_eq_spin]

private def columnFrequency {n s : ℕ} (Y : Fin s → Fin n → Bool) : Cn3Torus.Edge n → ℤ :=
  fun e => ∑ k : Fin s, ZInt (Y k) e

private lemma sum_phase_eq_columnFrequency {n s : ℕ} (lam : Cn3Torus.Edge n → ℝ)
    (Y : Fin s → Fin n → Bool) :
    ∑ k : Fin s, Cn3Torus.phase lam (Y k)
      = ∑ e : Cn3Torus.Edge n, lam e * (columnFrequency Y e : ℝ) := by
  unfold Cn3Torus.phase columnFrequency
  calc
    ∑ k : Fin s, ∑ e : Cn3Torus.Edge n, lam e * Cn3Torus.Z (Y k) e
        = ∑ e : Cn3Torus.Edge n, ∑ k : Fin s, lam e * Cn3Torus.Z (Y k) e := by
            rw [Finset.sum_comm]
    _ = ∑ e : Cn3Torus.Edge n, lam e * ∑ k : Fin s, Cn3Torus.Z (Y k) e := by
          refine Finset.sum_congr rfl ?_
          intro e he
          rw [Finset.mul_sum]
    _ = ∑ e : Cn3Torus.Edge n, lam e * ∑ k : Fin s, (ZInt (Y k) e : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          congr 2
          ext k
          rw [ZInt_coe_eq_Z]
    _ = ∑ e : Cn3Torus.Edge n, lam e * (↑(∑ k : Fin s, ZInt (Y k) e) : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro e he
          simp [Int.cast_sum]

private lemma torusCharacter_eq_phaseSum {n s : ℕ} (lam : Cn3Torus.Edge n → ℝ)
    (Y : Fin s → Fin n → Bool) :
    Cn3Torus.torusCharacter (columnFrequency Y) lam
      = Complex.exp (Complex.I * ((∑ k : Fin s, Cn3Torus.phase lam (Y k)) : ℂ)) := by
  unfold Cn3Torus.torusCharacter
  have hphase := congrArg (fun r : ℝ => (r : ℂ)) (sum_phase_eq_columnFrequency lam Y)
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast] at hphase
  calc
    Complex.exp (∑ e : Cn3Torus.Edge n, (↑(columnFrequency Y e) : ℂ) * ((↑(lam e) : ℂ) * Complex.I))
      = Complex.exp (Complex.I * ∑ e : Cn3Torus.Edge n, (↑(lam e) : ℂ) * ↑(columnFrequency Y e)) := by
          congr 1
          symm
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro e he
          ring
    _ = Complex.exp (Complex.I * ((∑ k : Fin s, Cn3Torus.phase lam (Y k)) : ℂ)) := by
          congr 1
          exact congrArg (fun z : ℂ => Complex.I * z) hphase.symm

private def matrixToBoolColumns {n s : ℕ} (M : Fin n → Fin s → Fin 2) : Fin s → Fin n → Bool :=
  fun k i => fin2ToBool (M i k)

private def boolColumnsToMatrix {n s : ℕ} (Y : Fin s → Fin n → Bool) : Fin n → Fin s → Fin 2 :=
  fun i k => boolToFin2 (Y k i)

private lemma matrixToBoolColumns_boolColumnsToMatrix {n s : ℕ}
    (Y : Fin s → Fin n → Bool) :
    matrixToBoolColumns (boolColumnsToMatrix Y) = Y := by
  funext k i
  simp [matrixToBoolColumns, boolColumnsToMatrix, fin2ToBool_boolToFin2]

private lemma boolColumnsToMatrix_matrixToBoolColumns {n s : ℕ}
    (M : Fin n → Fin s → Fin 2) :
    boolColumnsToMatrix (matrixToBoolColumns M) = M := by
  funext i k
  simp [matrixToBoolColumns, boolColumnsToMatrix, boolToFin2_fin2ToBool]

private lemma columnFrequency_matrixToBoolColumns_eq {n s : ℕ}
    (M : Fin n → Fin s → Fin 2) (e : Cn3Torus.Edge n) :
    columnFrequency (matrixToBoolColumns M) e
      = ∑ k : Fin s, signOf (M e.1.1 k) * signOf (M e.1.2 k) := by
  rcases e with ⟨⟨i, j⟩, hij⟩
  unfold columnFrequency matrixToBoolColumns ZInt
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [signBool_eq_signOf_boolToFin2, boolToFin2_fin2ToBool]

private lemma matrixOrthogonal_iff_columnFrequency_zero {n s : ℕ}
    (M : Fin n → Fin s → Fin 2) :
    (∀ i j : Fin n, i ≠ j →
      (∑ k : Fin s, (signOf (M i k) : ℝ) * (signOf (M j k) : ℝ)) = 0)
    ↔ ∀ e : Cn3Torus.Edge n, columnFrequency (matrixToBoolColumns M) e = 0 := by
  constructor
  · intro h e
    have hreal :
        (columnFrequency (matrixToBoolColumns M) e : ℝ)
          = ∑ k : Fin s, (signOf (M e.1.1 k) : ℝ) * (signOf (M e.1.2 k) : ℝ) := by
      exact_mod_cast columnFrequency_matrixToBoolColumns_eq M e
    have hzero :
        (∑ k : Fin s, (signOf (M e.1.1 k) : ℝ) * (signOf (M e.1.2 k) : ℝ)) = 0 :=
      h e.1.1 e.1.2 (ne_of_lt e.2)
    have hcast_zero : (columnFrequency (matrixToBoolColumns M) e : ℝ) = 0 := by
      simpa [hreal] using hzero
    exact_mod_cast hcast_zero
  · intro h i j hij
    rcases lt_or_gt_of_ne hij with hij' | hij'
    · let e : Cn3Torus.Edge n := ⟨(i, j), hij'⟩
      have hreal :
          (columnFrequency (matrixToBoolColumns M) e : ℝ)
            = ∑ k : Fin s, (signOf (M i k) : ℝ) * (signOf (M j k) : ℝ) := by
        exact_mod_cast columnFrequency_matrixToBoolColumns_eq M e
      calc
        ∑ k : Fin s, (signOf (M i k) : ℝ) * (signOf (M j k) : ℝ)
            = (columnFrequency (matrixToBoolColumns M) e : ℝ) := by symm; exact hreal
        _ = 0 := by exact_mod_cast h e
    · let e : Cn3Torus.Edge n := ⟨(j, i), hij'⟩
      have hreal :
          (columnFrequency (matrixToBoolColumns M) e : ℝ)
            = ∑ k : Fin s, (signOf (M j k) : ℝ) * (signOf (M i k) : ℝ) := by
        exact_mod_cast columnFrequency_matrixToBoolColumns_eq M e
      calc
        ∑ k : Fin s, (signOf (M i k) : ℝ) * (signOf (M j k) : ℝ)
            = ∑ k : Fin s, (signOf (M j k) : ℝ) * (signOf (M i k) : ℝ) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                ring
        _ = (columnFrequency (matrixToBoolColumns M) e : ℝ) := by symm; exact hreal
        _ = 0 := by exact_mod_cast h e

private lemma sum_pow_eq_sum_fun_prod {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℂ) (s : ℕ) :
    (∑ a : α, f a) ^ s = ∑ Y : Fin s → α, ∏ k : Fin s, f (Y k) := by
  calc
    (∑ a : α, f a) ^ s = ∏ _ : Fin s, ∑ a : α, f a := by simp
    _ = ∑ Y : Fin s → α, ∏ k : Fin s, f (Y k) := by
      simpa using (Finset.prod_univ_sum (t := fun _ : Fin s => (Finset.univ : Finset α))
        (f := fun _ a => f a))

private lemma psi_pow_eq_sum_torusCharacter {n s : ℕ} (lam : Cn3Torus.Edge n → ℝ) :
    Cn3Torus.psi n lam ^ s
      = (((2 ^ n : ℂ) ^ s)⁻¹) *
          ∑ Y : Fin s → Fin n → Bool, Cn3Torus.torusCharacter (columnFrequency Y) lam := by
  unfold Cn3Torus.psi
  rw [div_pow]
  rw [sum_pow_eq_sum_fun_prod (f := fun y : Fin n → Bool => Complex.exp (Complex.I * (Cn3Torus.phase lam y : ℂ))) s]
  rw [div_eq_mul_inv]
  calc
    (∑ Y : Fin s → Fin n → Bool, ∏ k : Fin s, Complex.exp (Complex.I * ↑(Cn3Torus.phase lam (Y k)))) * (((2 ^ n : ℂ) ^ s)⁻¹)
      = (((2 ^ n : ℂ) ^ s)⁻¹) *
          ∑ Y : Fin s → Fin n → Bool, ∏ k : Fin s, Complex.exp (Complex.I * ↑(Cn3Torus.phase lam (Y k))) := by
            ring
    _ = (((2 ^ n : ℂ) ^ s)⁻¹) *
          ∑ Y : Fin s → Fin n → Bool, Cn3Torus.torusCharacter (columnFrequency Y) lam := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro Y hY
            rw [torusCharacter_eq_phaseSum]
            have hsum :
                Complex.I * ((∑ k : Fin s, Cn3Torus.phase lam (Y k)) : ℂ)
                  = ∑ k : Fin s, Complex.I * (Cn3Torus.phase lam (Y k) : ℂ) := by
                    rw [Finset.mul_sum]
            rw [hsum]
            symm
            exact Complex.exp_sum Finset.univ (fun k : Fin s => Complex.I * (Cn3Torus.phase lam (Y k) : ℂ))

private lemma integrable_torusCharacter_on_torusBox {n s : ℕ} (Y : Fin s → Fin n → Bool) :
    MeasureTheory.IntegrableOn (fun lam : Cn3Torus.Edge n → ℝ => Cn3Torus.torusCharacter (columnFrequency Y) lam)
      (Cn3Torus.torusBox n) := by
  have hcont : Continuous (fun lam : Cn3Torus.Edge n → ℝ => Cn3Torus.torusCharacter (columnFrequency Y) lam) := by
    unfold Cn3Torus.torusCharacter
    fun_prop
  exact hcont.continuousOn.integrableOn_compact (Cn3Torus.torusBox_isCompact n)

private lemma torusIntegralC_eq_sum_columnFrequency {n s : ℕ} :
    Cn3Torus.torusIntegralC n s
      = (((2 ^ n : ℂ) ^ s)⁻¹) *
          ∑ Y : Fin s → Fin n → Bool,
            ∫ lam in Cn3Torus.torusBox n, Cn3Torus.torusCharacter (columnFrequency Y) lam := by
  unfold Cn3Torus.torusIntegralC
  calc
    ∫ lam in Cn3Torus.torusBox n, Cn3Torus.psi n lam ^ s
        = ∫ lam in Cn3Torus.torusBox n,
            (((2 ^ n : ℂ) ^ s)⁻¹) *
              ∑ Y : Fin s → Fin n → Bool, Cn3Torus.torusCharacter (columnFrequency Y) lam := by
            congr with lam
            exact psi_pow_eq_sum_torusCharacter (n := n) (s := s) lam
    _ = (((2 ^ n : ℂ) ^ s)⁻¹) *
          ∫ lam in Cn3Torus.torusBox n,
            ∑ Y : Fin s → Fin n → Bool, Cn3Torus.torusCharacter (columnFrequency Y) lam := by
          rw [MeasureTheory.integral_const_mul]
    _ = (((2 ^ n : ℂ) ^ s)⁻¹) *
          ∑ Y : Fin s → Fin n → Bool,
            ∫ lam in Cn3Torus.torusBox n, Cn3Torus.torusCharacter (columnFrequency Y) lam := by
          congr 1
          simpa using MeasureTheory.integral_finset_sum
            (s := Finset.univ)
            (f := fun Y : Fin s → Fin n → Bool => fun lam : Cn3Torus.Edge n → ℝ =>
              Cn3Torus.torusCharacter (columnFrequency Y) lam)
            (hf := by
              intro Y hY
              exact integrable_torusCharacter_on_torusBox (n := n) (s := s) Y)

private lemma hadamardCount_eq_card_zeroColumnSubtype (n s : ℕ) :
    hadamardCount n s = Fintype.card {Y : Fin s → Fin n → Bool // ∀ e : Cn3Torus.Edge n, columnFrequency Y e = 0} := by
  classical
  let hEquiv :
      {M : Fin n → Fin s → Fin 2 // ∀ i j : Fin n, i ≠ j →
          (∑ k : Fin s, (signOf (M i k) : ℝ) * (signOf (M j k) : ℝ)) = 0}
        ≃ {Y : Fin s → Fin n → Bool // ∀ e : Cn3Torus.Edge n, columnFrequency Y e = 0} :=
    { toFun := fun M => ⟨matrixToBoolColumns M.1, (matrixOrthogonal_iff_columnFrequency_zero M.1).1 M.2⟩
      invFun := fun Y => ⟨boolColumnsToMatrix Y.1, by
        have hzero : ∀ e : Cn3Torus.Edge n,
            columnFrequency (matrixToBoolColumns (boolColumnsToMatrix Y.1)) e = 0 := by
          intro e
          simpa [matrixToBoolColumns_boolColumnsToMatrix] using Y.2 e
        exact (matrixOrthogonal_iff_columnFrequency_zero (boolColumnsToMatrix Y.1)).2 hzero⟩
      left_inv := by
        intro M
        apply Subtype.ext
        exact boolColumnsToMatrix_matrixToBoolColumns M.1
      right_inv := by
        intro Y
        apply Subtype.ext
        exact matrixToBoolColumns_boolColumnsToMatrix Y.1 }
  calc
    hadamardCount n s
      = Fintype.card {M : Fin n → Fin s → Fin 2 // ∀ i j : Fin n, i ≠ j →
          (∑ k : Fin s, (signOf (M i k) : ℝ) * (signOf (M j k) : ℝ)) = 0} := by
            symm
            exact Fintype.card_of_subtype
              (Finset.univ.filter (fun M : Fin n → Fin s → Fin 2 =>
                ∀ i j : Fin n, i ≠ j →
                  (∑ k : Fin s, (signOf (M i k) : ℝ) * (signOf (M j k) : ℝ)) = 0))
              (by
                intro M
                simp)
    _ = Fintype.card {Y : Fin s → Fin n → Bool // ∀ e : Cn3Torus.Edge n, columnFrequency Y e = 0} :=
          Fintype.card_congr hEquiv

/-- Exact count-to-integral bridge for the torus model.

The torus integral equals the torus volume times the number of `n × s` partial
Hadamard matrices, divided by the ambient sign count `2^(ns)`. This is the
formal Fourier-inversion step connecting the combinatorial count to the
analytic integral. -/
theorem torusIntegralC_eq_volume_mul_hadamardCount (n s : ℕ) :
    Cn3Torus.torusIntegralC n s
      = ((((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ) : ℂ) * (hadamardCount n s : ℂ)) /
          ((2 ^ n : ℂ) ^ s) := by
  classical
  have hsum :
      ∑ Y : Fin s → Fin n → Bool,
          ∫ lam in Cn3Torus.torusBox n, Cn3Torus.torusCharacter (columnFrequency Y) lam
        = ∑ Y : Fin s → Fin n → Bool,
            (if ∀ e : Cn3Torus.Edge n, columnFrequency Y e = 0
              then (((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ) : ℂ)
              else 0) := by
    refine Finset.sum_congr rfl ?_
    intro Y hY
    simpa using Cn3Torus.torusCharacter_integral (columnFrequency Y)
  calc
    Cn3Torus.torusIntegralC n s
      = (((2 ^ n : ℂ) ^ s)⁻¹) *
          ∑ Y : Fin s → Fin n → Bool,
            ∫ lam in Cn3Torus.torusBox n, Cn3Torus.torusCharacter (columnFrequency Y) lam :=
          torusIntegralC_eq_sum_columnFrequency (n := n) (s := s)
    _ = (((2 ^ n : ℂ) ^ s)⁻¹) *
          ∑ Y : Fin s → Fin n → Bool,
            (if ∀ e : Cn3Torus.Edge n, columnFrequency Y e = 0
              then (((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ) : ℂ)
              else 0) := by rw [hsum]
    _ = (((2 ^ n : ℂ) ^ s)⁻¹) * ((((Fintype.card {Y : Fin s → Fin n → Bool //
            ∀ e : Cn3Torus.Edge n, columnFrequency Y e = 0}) : ℕ) : ℂ) *
            ((((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ) : ℂ))) := by
          congr 1
          rw [← Finset.sum_filter]
          have hcard :
              (Finset.univ.filter (fun Y : Fin s → Fin n → Bool =>
                ∀ e : Cn3Torus.Edge n, columnFrequency Y e = 0)).card
                = Fintype.card {Y : Fin s → Fin n → Bool //
                    ∀ e : Cn3Torus.Edge n, columnFrequency Y e = 0} := by
                  symm
                  exact Fintype.card_of_subtype
                    (Finset.univ.filter (fun Y : Fin s → Fin n → Bool =>
                      ∀ e : Cn3Torus.Edge n, columnFrequency Y e = 0))
                    (by
                      intro Y
                      simp)
          simp [hcard]
    _ = (((2 ^ n : ℂ) ^ s)⁻¹) * (((hadamardCount n s : ℕ) : ℂ) *
            ((((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ) : ℂ))) := by
          rw [hadamardCount_eq_card_zeroColumnSubtype]
    _ = ((((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ) : ℂ) * (hadamardCount n s : ℂ)) /
          ((2 ^ n : ℂ) ^ s) := by
          field_simp

private lemma complex_pow_two_nat (n s : ℕ) : ((2 ^ n : ℂ) ^ s) = (2 ^ (n * s) : ℂ) := by
  calc
    ((2 ^ n : ℂ) ^ s) = (((2 : ℂ) ^ n) ^ s) := by norm_num
    _ = (2 : ℂ) ^ (n * s) := by rw [pow_mul]
    _ = (2 ^ (n * s) : ℂ) := by norm_num

private lemma complex_nat_div_re (a b : ℕ) : (((a : ℂ) / (b : ℂ)).re) = (a : ℝ) / (b : ℝ) := by
  have hquot : ((a : ℂ) / (b : ℂ)) = (((a : ℝ) / (b : ℝ) : ℝ) : ℂ) := by
    rw [show ((a : ℂ)) = (((a : ℝ) : ℝ) : ℂ) by norm_num,
      show ((b : ℂ)) = (((b : ℝ) : ℝ) : ℂ) by norm_num,
      Complex.ofReal_div]
  rw [hquot]
  simp

private lemma complex_two_pow_nat (m : ℕ) : ((2 : ℂ) ^ m) = ((2 ^ m : ℕ) : ℂ) := by
  norm_num

namespace Cn3Torus

def edgeFromOffdiag {n : ℕ} (i : Fin n) (j : {k : Fin n // k ≠ i}) : Edge n :=
  if hij : i < j.1 then
    ⟨(i, j.1), hij⟩
  else
    ⟨(j.1, i), by
      have hcmp : i < j.1 ∨ j.1 < i := lt_or_gt_of_ne j.2.symm
      exact hcmp.resolve_left hij⟩

private lemma edgeFromOffdiag_mem_edgesIncident {n : ℕ} (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    edgeFromOffdiag i j ∈ edgesIncident n i := by
  unfold edgeFromOffdiag
  by_cases hij : i < j.1
  · simp [hij, mem_edgesIncident_iff]
  · simp [hij, mem_edgesIncident_iff]

def offdiagOfIncident {n : ℕ} (i : Fin n) (e : Edge n)
    (he : e ∈ edgesIncident n i) : {k : Fin n // k ≠ i} := by
  by_cases hleft : e.1.1 = i
  · refine ⟨e.1.2, ?_⟩
    intro hEq
    exact (ne_of_lt e.2) (by simpa [hleft, hEq])
  · exact ⟨e.1.1, hleft⟩

lemma edgeFromOffdiag_offdiagOfIncident {n : ℕ} (i : Fin n) (e : Edge n)
    (he : e ∈ edgesIncident n i) :
    edgeFromOffdiag i (offdiagOfIncident i e he) = e := by
  rcases e with ⟨⟨a, b⟩, hab⟩
  unfold offdiagOfIncident
  by_cases hleft : a = i
  · have hlt : i < b := by simpa [hleft] using hab
    simp [hleft, edgeFromOffdiag, hlt]
  · have hright : b = i := by
      rcases (mem_edgesIncident_iff (i := i) (e := ⟨(a, b), hab⟩)).1 he with h1 | h2
      · exact (hleft h1).elim
      · exact h2
    have hfalse : ¬ i < a := by
      have hlt : a < i := by simpa [hright] using hab
      exact not_lt_of_ge hlt.le
    simp [hleft, hright, edgeFromOffdiag, hfalse]

private def incidentEdgeEquivOffdiag (n : ℕ) (i : Fin n) :
    {e : Edge n // e ∈ edgesIncident n i} ≃ {j : Fin n // j ≠ i} where
  toFun := fun e => offdiagOfIncident i e.1 e.2
  invFun := fun j => ⟨edgeFromOffdiag i j, edgeFromOffdiag_mem_edgesIncident (n := n) i j⟩
  left_inv := by
    intro e
    apply Subtype.ext
    simpa using edgeFromOffdiag_offdiagOfIncident (n := n) i e.1 e.2
  right_inv := by
    intro j
    apply Subtype.ext
    unfold offdiagOfIncident edgeFromOffdiag
    by_cases hij : i < j.1
    · simp [hij]
    · simp [hij, j.2]

private lemma rowParitySum_eq_sum_offdiag {n : ℕ} (b : LambdaCode n) (i : Fin n) :
    rowParitySum b i = ∑ j : {k : Fin n // k ≠ i}, (b (edgeFromOffdiag i j) : ℕ) := by
  classical
  unfold rowParitySum edgeNatRowSum
  rw [← (edgesIncident n i).sum_attach (f := fun e : Edge n => (b e : ℕ))]
  let eIso : {e : Edge n // e ∈ edgesIncident n i} ≃ {j : Fin n // j ≠ i} :=
    incidentEdgeEquivOffdiag n i
  have hsum :
      (∑ eSub : {e : Edge n // e ∈ edgesIncident n i}, (b eSub.1 : ℕ))
        = ∑ j : {k : Fin n // k ≠ i}, (b (edgeFromOffdiag i j) : ℕ) := by
    exact Fintype.sum_equiv eIso
      (fun eSub : {e : Edge n // e ∈ edgesIncident n i} => (b eSub.1 : ℕ))
      (fun j : {k : Fin n // k ≠ i} => (b (edgeFromOffdiag i j) : ℕ))
      (by
        intro eSub
        have hEq :
            edgeFromOffdiag i (offdiagOfIncident i eSub.1 eSub.2) = eSub.1 :=
          edgeFromOffdiag_offdiagOfIncident (n := n) i eSub.1 eSub.2
        simpa [eIso] using (congrArg (fun ee => (b ee : ℕ)) hEq).symm)
  simpa using hsum

private def rowCosProd (n : ℕ) (i : Fin n) (lam : Edge n → ℝ) : ℝ :=
  ∏ j : {k : Fin n // k ≠ i}, Real.cos (2 * lam (edgeFromOffdiag i j))

private lemma matrix_rowCosProd_eq_rowCosProd (n : ℕ) (i : Fin n) (lam : Edge n → ℝ) :
    (∏ k : Fin n,
      if k = i then 1
      else if k < i then Real.cos (2 * matrixOfEdge n lam k i)
      else Real.cos (2 * matrixOfEdge n lam i k))
      = rowCosProd n i lam := by
  classical
  let f : Fin n → ℝ := fun k =>
    if k = i then 1
    else if k < i then Real.cos (2 * matrixOfEdge n lam k i)
    else Real.cos (2 * matrixOfEdge n lam i k)
  have hsplit :
      (∏ k : Fin n, f k) = f i * Finset.prod (Finset.univ.erase i) f := by
    symm
    simpa [f] using
      (Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n))) (a := i) (f := f) (by simp))
  have hattach :
      Finset.prod (Finset.univ.erase i) f
        = ∏ k : {j : Fin n // j ∈ (Finset.univ.erase i)}, f k.1 := by
    symm
    simpa using (Finset.prod_attach (s := (Finset.univ.erase i)) (f := f))
  let eraseIso : {k : Fin n // k ∈ (Finset.univ.erase i)} ≃ {k : Fin n // k ≠ i} := {
    toFun := fun k => ⟨k.1, (Finset.mem_erase.mp k.2).1⟩
    invFun := fun k => ⟨k.1, Finset.mem_erase.mpr ⟨k.2, Finset.mem_univ _⟩⟩
    left_inv := by
      intro k
      apply Subtype.ext
      rfl
    right_inv := by
      intro k
      apply Subtype.ext
      rfl
  }
  have hreindex :
      (∏ k : {j : Fin n // j ∈ (Finset.univ.erase i)}, f k.1)
        = ∏ j : {k : Fin n // k ≠ i}, Real.cos (2 * lam (edgeFromOffdiag i j)) := by
    exact Fintype.prod_equiv eraseIso
      (fun k => f k.1)
      (fun j => Real.cos (2 * lam (edgeFromOffdiag i j)))
      (by
        intro k
        have hk : k.1 ≠ i := (Finset.mem_erase.mp k.2).1
        unfold f
        by_cases hlt : k.1 < i
        · have hnot : ¬ i < (eraseIso k).1 := by
            simpa using hlt.not_gt
          have hval : (eraseIso.toFun k).1 = k.1 := rfl
          have hedge : edgeFromOffdiag i (eraseIso k) = ⟨(k.1, i), hlt⟩ := by
            unfold edgeFromOffdiag
            apply Subtype.ext
            simpa [hnot] using hval
          simp [hk, hlt, matrixOfEdge, hedge]
        · have hgt : i < k.1 := lt_of_le_of_ne (le_of_not_gt hlt) hk.symm
          have hlt' : i < (eraseIso k).1 := by
            simpa using hgt
          have hval : (eraseIso.toFun k).1 = k.1 := rfl
          have hedge : edgeFromOffdiag i (eraseIso k) = ⟨(i, k.1), hlt'⟩ := by
            unfold edgeFromOffdiag
            apply Subtype.ext
            simpa [hlt'] using hval
          simp [hk, hlt, hgt, matrixOfEdge, hedge])
  calc
    (∏ k : Fin n, f k) = f i * Finset.prod (Finset.univ.erase i) f := hsplit
    _ = Finset.prod (Finset.univ.erase i) f := by simp [f]
    _ = ∏ k : {j : Fin n // j ∈ (Finset.univ.erase i)}, f k.1 := hattach
    _ = ∏ j : {k : Fin n // k ≠ i}, Real.cos (2 * lam (edgeFromOffdiag i j)) := hreindex
    _ = rowCosProd n i lam := by rfl

private lemma abs_rowCosProd_le_abs_factor (n : ℕ) (i : Fin n) (lam : Edge n → ℝ)
    (j0 : {k : Fin n // k ≠ i}) :
    |rowCosProd n i lam| ≤ |Real.cos (2 * lam (edgeFromOffdiag i j0))| := by
  let α : Type := {k : Fin n // k ≠ i}
  let f : α → ℝ := fun j => Real.cos (2 * lam (edgeFromOffdiag i j))
  have hsplit :
      (∏ j : α, f j) = f j0 * Finset.prod (Finset.univ.erase j0) f := by
    symm
    simpa using (Finset.mul_prod_erase (s := (Finset.univ : Finset α)) (a := j0) (f := f) (by simp))
  have hprod_abs_le_one : |Finset.prod (Finset.univ.erase j0) f| ≤ 1 := by
    have habs_prod :
        |Finset.prod (Finset.univ.erase j0) f|
          = Finset.prod (Finset.univ.erase j0) (fun j => |f j|) := by
      convert (norm_prod (s := (Finset.univ.erase j0)) (f := f)) using 1 <;>
        simp [Real.norm_eq_abs]
    calc
      |Finset.prod (Finset.univ.erase j0) f|
          = Finset.prod (Finset.univ.erase j0) (fun j => |f j|) := by
            exact habs_prod
      _ ≤ Finset.prod (Finset.univ.erase j0) (fun _ => (1 : ℝ)) := by
            refine Finset.prod_le_prod ?_ ?_
            · intro j hj
              exact abs_nonneg (f j)
            · intro j hj
              exact Real.abs_cos_le_one (2 * lam (edgeFromOffdiag i j))
      _ = (1 : ℝ) := by simp
  have hf_nonneg : 0 ≤ |f j0| := abs_nonneg (f j0)
  have hmul_le : |f j0| * |Finset.prod (Finset.univ.erase j0) f| ≤ |f j0| := by
    have hm := mul_le_mul_of_nonneg_left hprod_abs_le_one hf_nonneg
    simpa using hm
  calc
    |rowCosProd n i lam|
        = |∏ j : α, f j| := by simp [rowCosProd, α, f]
    _ = |f j0 * Finset.prod (Finset.univ.erase j0) f| := by rw [hsplit]
    _ = |f j0| * |Finset.prod (Finset.univ.erase j0) f| := by rw [abs_mul]
    _ ≤ |f j0| := hmul_le
    _ = |Real.cos (2 * lam (edgeFromOffdiag i j0))| := by rfl

private lemma rowCosProd_nonpos_of_odd_row_and_close (n : ℕ) (lam : Edge n → ℝ)
    (b : LambdaCode n) (i : Fin n)
    (hodd : Odd (rowParitySum b i))
    (hclose : ∀ e : Edge n, |lam e - quarterReal (b e)| < delta) :
    rowCosProd n i lam ≤ 0 := by
  let α : Type := {k : Fin n // k ≠ i}
  let r : Edge n → ℝ := fun e => lam e - quarterReal (b e)
  have hfactor :
      ∀ j : α,
        Real.cos (2 * lam (edgeFromOffdiag i j))
          = ((-1 : ℝ) ^ (b (edgeFromOffdiag i j) : ℕ))
              * Real.cos (2 * r (edgeFromOffdiag i j)) := by
    intro j
    have hrew :
        2 * lam (edgeFromOffdiag i j)
          = 2 * r (edgeFromOffdiag i j) + (b (edgeFromOffdiag i j) : ℕ) * Real.pi := by
      unfold r quarterReal
      ring
    rw [hrew, Real.cos_add_nat_mul_pi]
  have hcos_nonneg :
      ∀ j : α, 0 ≤ Real.cos (2 * r (edgeFromOffdiag i j)) := by
    intro j
    have hclose_j : |r (edgeFromOffdiag i j)| < delta := by
      simpa [r] using hclose (edgeFromOffdiag i j)
    have habs2 : |2 * r (edgeFromOffdiag i j)| = 2 * |r (edgeFromOffdiag i j)| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have harg_lt : |2 * r (edgeFromOffdiag i j)| < Real.pi / 2 := by
      have htmp : 2 * |r (edgeFromOffdiag i j)| < Real.pi / 2 := by
        have h2delta : 2 * |r (edgeFromOffdiag i j)| < 2 * delta := by
          nlinarith [hclose_j]
        exact lt_trans h2delta two_delta_lt_pi_div_two
      simpa [habs2] using htmp
    have harg_pair :
        -(Real.pi / 2) < 2 * r (edgeFromOffdiag i j) ∧
          2 * r (edgeFromOffdiag i j) < Real.pi / 2 := abs_lt.mp harg_lt
    have hlow : -(Real.pi / 2) ≤ 2 * r (edgeFromOffdiag i j) := le_of_lt harg_pair.1
    have hupp : 2 * r (edgeFromOffdiag i j) ≤ Real.pi / 2 := le_of_lt harg_pair.2
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le hlow hupp
  have hprod_nonneg : 0 ≤ ∏ j : α, Real.cos (2 * r (edgeFromOffdiag i j)) := by
    exact Finset.prod_nonneg (fun j hj => hcos_nonneg j)
  have hsum_eq :
      (∑ j : α, (b (edgeFromOffdiag i j) : ℕ)) = rowParitySum b i := by
    simpa [α] using (rowParitySum_eq_sum_offdiag b i).symm
  have hodd_sum : Odd (∑ j : α, (b (edgeFromOffdiag i j) : ℕ)) := by
    simpa [hsum_eq] using hodd
  have hsign :
      (∏ j : α, (-1 : ℝ) ^ (b (edgeFromOffdiag i j) : ℕ)) = -1 := by
    have hpow :
        (∏ j : α, (-1 : ℝ) ^ (b (edgeFromOffdiag i j) : ℕ))
          = (-1 : ℝ) ^ (∑ j : α, (b (edgeFromOffdiag i j) : ℕ)) := by
      simpa using
        (Finset.prod_pow_eq_pow_sum
          (s := (Finset.univ : Finset α))
          (f := fun j : α => (b (edgeFromOffdiag i j) : ℕ))
          (-1 : ℝ))
    rw [hpow]
    exact hodd_sum.neg_one_pow
  have hrow :
      rowCosProd n i lam
        = (∏ j : α, (-1 : ℝ) ^ (b (edgeFromOffdiag i j) : ℕ))
            * (∏ j : α, Real.cos (2 * r (edgeFromOffdiag i j))) := by
    unfold rowCosProd
    calc
      (∏ j : α, Real.cos (2 * lam (edgeFromOffdiag i j)))
          = ∏ j : α,
              (((-1 : ℝ) ^ (b (edgeFromOffdiag i j) : ℕ))
                * Real.cos (2 * r (edgeFromOffdiag i j))) := by
                refine Finset.prod_congr rfl ?_
                intro j hj
                exact hfactor j
      _ = (∏ j : α, (-1 : ℝ) ^ (b (edgeFromOffdiag i j) : ℕ))
            * (∏ j : α, Real.cos (2 * r (edgeFromOffdiag i j))) := by
            simpa using
              (Finset.prod_mul_distrib
                (s := (Finset.univ : Finset α))
                (f := fun j : α => (-1 : ℝ) ^ (b (edgeFromOffdiag i j) : ℕ))
                (g := fun j : α => Real.cos (2 * r (edgeFromOffdiag i j))))
  calc
    rowCosProd n i lam
        = (-1 : ℝ) * (∏ j : α, Real.cos (2 * r (edgeFromOffdiag i j))) := by
            rw [hrow, hsign]
    _ ≤ 0 := by
          nlinarith [hprod_nonneg]

private lemma rowCosProd_nonpos_of_odd_row_and_close_of_lt_pi_div_four
    (n : ℕ) (lam : Edge n → ℝ) (deltaBox : ℝ)
    (hdelta_pos : 0 < deltaBox) (hdelta_lt : deltaBox < Real.pi / 4)
    (b : LambdaCode n) (i : Fin n)
    (hodd : Odd (rowParitySum b i))
    (hclose : ∀ e : Edge n, |lam e - quarterReal (b e)| < deltaBox) :
    rowCosProd n i lam ≤ 0 := by
  let α : Type := {k : Fin n // k ≠ i}
  let r : Edge n → ℝ := fun e => lam e - quarterReal (b e)
  have hfactor :
      ∀ j : α,
        Real.cos (2 * lam (edgeFromOffdiag i j))
          = ((-1 : ℝ) ^ (b (edgeFromOffdiag i j) : ℕ))
              * Real.cos (2 * r (edgeFromOffdiag i j)) := by
    intro j
    have hrew :
        2 * lam (edgeFromOffdiag i j)
          = 2 * r (edgeFromOffdiag i j) + (b (edgeFromOffdiag i j) : ℕ) * Real.pi := by
      unfold r quarterReal
      ring
    rw [hrew, Real.cos_add_nat_mul_pi]
  have hcos_nonneg :
      ∀ j : α, 0 ≤ Real.cos (2 * r (edgeFromOffdiag i j)) := by
    intro j
    have hclose_j : |r (edgeFromOffdiag i j)| < deltaBox := by
      simpa [r] using hclose (edgeFromOffdiag i j)
    have habs2 : |2 * r (edgeFromOffdiag i j)| = 2 * |r (edgeFromOffdiag i j)| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have harg_lt : |2 * r (edgeFromOffdiag i j)| < Real.pi / 2 := by
      have htmp : 2 * |r (edgeFromOffdiag i j)| < 2 * deltaBox := by
        nlinarith [hclose_j]
      have h2delta : 2 * deltaBox < Real.pi / 2 := by
        linarith
      exact lt_of_eq_of_lt habs2 (lt_trans htmp h2delta)
    have harg_pair :
        -(Real.pi / 2) < 2 * r (edgeFromOffdiag i j) ∧
          2 * r (edgeFromOffdiag i j) < Real.pi / 2 := abs_lt.mp harg_lt
    have hlow : -(Real.pi / 2) ≤ 2 * r (edgeFromOffdiag i j) := le_of_lt harg_pair.1
    have hupp : 2 * r (edgeFromOffdiag i j) ≤ Real.pi / 2 := le_of_lt harg_pair.2
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le hlow hupp
  have hprod_nonneg : 0 ≤ ∏ j : α, Real.cos (2 * r (edgeFromOffdiag i j)) := by
    exact Finset.prod_nonneg (fun j hj => hcos_nonneg j)
  have hsum_eq :
      (∑ j : α, (b (edgeFromOffdiag i j) : ℕ)) = rowParitySum b i := by
    simpa [α] using (rowParitySum_eq_sum_offdiag b i).symm
  have hodd_sum : Odd (∑ j : α, (b (edgeFromOffdiag i j) : ℕ)) := by
    simpa [hsum_eq] using hodd
  have hsign :
      (∏ j : α, (-1 : ℝ) ^ (b (edgeFromOffdiag i j) : ℕ)) = -1 := by
    have hpow :
        (∏ j : α, (-1 : ℝ) ^ (b (edgeFromOffdiag i j) : ℕ))
          = (-1 : ℝ) ^ (∑ j : α, (b (edgeFromOffdiag i j) : ℕ)) := by
      simpa using
        (Finset.prod_pow_eq_pow_sum
          (s := (Finset.univ : Finset α))
          (f := fun j : α => (b (edgeFromOffdiag i j) : ℕ))
          (-1 : ℝ))
    rw [hpow]
    exact hodd_sum.neg_one_pow
  have hrow :
      rowCosProd n i lam
        = (∏ j : α, (-1 : ℝ) ^ (b (edgeFromOffdiag i j) : ℕ))
            * (∏ j : α, Real.cos (2 * r (edgeFromOffdiag i j))) := by
    unfold rowCosProd
    calc
      (∏ j : α, Real.cos (2 * lam (edgeFromOffdiag i j)))
          = ∏ j : α,
              (((-1 : ℝ) ^ (b (edgeFromOffdiag i j) : ℕ))
                * Real.cos (2 * r (edgeFromOffdiag i j))) := by
                refine Finset.prod_congr rfl ?_
                intro j hj
                exact hfactor j
      _ = (∏ j : α, (-1 : ℝ) ^ (b (edgeFromOffdiag i j) : ℕ))
            * (∏ j : α, Real.cos (2 * r (edgeFromOffdiag i j))) := by
            simpa using
              (Finset.prod_mul_distrib
                (s := (Finset.univ : Finset α))
                (f := fun j : α => (-1 : ℝ) ^ (b (edgeFromOffdiag i j) : ℕ))
                (g := fun j : α => Real.cos (2 * r (edgeFromOffdiag i j))))
  calc
    rowCosProd n i lam
        = (-1 : ℝ) * (∏ j : α, Real.cos (2 * r (edgeFromOffdiag i j))) := by
            rw [hrow, hsign]
    _ ≤ 0 := by
          nlinarith [hprod_nonneg]

private lemma cos_two_nonneg_of_lt_pi_div_four (deltaBox : ℝ)
    (hdelta_pos : 0 < deltaBox) (hdelta_lt : deltaBox < Real.pi / 4) :
    0 ≤ Real.cos (2 * deltaBox) := by
  have hlow : -(Real.pi / 2) ≤ 2 * deltaBox := by
    have hpi2 : 0 < Real.pi / 2 := by positivity [Real.pi_pos]
    linarith [hdelta_pos, hpi2]
  have hupp : 2 * deltaBox ≤ Real.pi / 2 := by
    linarith
  exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le hlow hupp

private lemma exists_quarterReal_close_of_mem_torusInterval {x : ℝ}
    (hx : x ∈ Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4)) :
    ∃ q : Fin 4, |x - quarterReal q| ≤ Real.pi / 4 := by
  rcases hx with ⟨hxL, hxU⟩
  by_cases h0 : x ≤ Real.pi / 4
  · refine ⟨(0 : Fin 4), ?_⟩
    have habs : |x| ≤ Real.pi / 4 := by
      exact abs_le.mpr ⟨by linarith, h0⟩
    simpa [quarterReal] using habs
  · have h0' : Real.pi / 4 < x := lt_of_not_ge h0
    by_cases h1 : x ≤ 3 * Real.pi / 4
    · refine ⟨(1 : Fin 4), ?_⟩
      have habs : |x - Real.pi / 2| ≤ Real.pi / 4 := by
        exact abs_le.mpr ⟨by linarith [h0'], by linarith [h1]⟩
      simpa [quarterReal] using habs
    · have h1' : 3 * Real.pi / 4 < x := lt_of_not_ge h1
      by_cases h2 : x ≤ 5 * Real.pi / 4
      · refine ⟨(2 : Fin 4), ?_⟩
        have habs : |x - 2 * (Real.pi / 2)| ≤ Real.pi / 4 := by
          exact abs_le.mpr ⟨by linarith [h1'], by linarith [h2]⟩
        simpa [quarterReal] using habs
      · have h2' : 5 * Real.pi / 4 < x := lt_of_not_ge h2
        refine ⟨(3 : Fin 4), ?_⟩
        have habs : |x - 3 * (Real.pi / 2)| ≤ Real.pi / 4 := by
          exact abs_le.mpr ⟨by linarith [h2'], by linarith [hxU]⟩
        simpa [quarterReal] using habs

private lemma abs_cos_two_mul_le_cos_two_delta_of_mem_torusInterval {x : ℝ}
    (hx : x ∈ Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4))
    (hfar : ∀ q : Fin 4, delta ≤ |x - quarterReal q|) :
    |Real.cos (2 * x)| ≤ Real.cos (2 * delta) := by
  rcases exists_quarterReal_close_of_mem_torusInterval hx with ⟨q, hqclose⟩
  let r : ℝ := |x - quarterReal q|
  have hdelta_le : delta ≤ r := by
    simpa [r] using hfar q
  have hr_le : r ≤ Real.pi / 4 := by
    simpa [r] using hqclose
  have hcos_shift :
      |Real.cos (2 * x)| = |Real.cos (2 * (x - quarterReal q))| := by
    have hrew :
        2 * x = 2 * (x - quarterReal q) + (q : Nat) * Real.pi := by
      unfold quarterReal
      ring
    rw [hrew, Real.cos_add_nat_mul_pi]
    simp [abs_mul]
  have harg_le : |2 * (x - quarterReal q)| ≤ Real.pi / 2 := by
    have habs2 : |2 * (x - quarterReal q)| = 2 * |x - quarterReal q| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have : 2 * |x - quarterReal q| ≤ Real.pi / 2 := by
      nlinarith [hqclose]
    simpa [habs2] using this
  have hcos_nonneg : 0 ≤ Real.cos (2 * (x - quarterReal q)) := by
    have harg_pair : -(Real.pi / 2) ≤ 2 * (x - quarterReal q) ∧
        2 * (x - quarterReal q) ≤ Real.pi / 2 := abs_le.mp harg_le
    have hlow : -(Real.pi / 2) ≤ 2 * (x - quarterReal q) := harg_pair.1
    have hupp : 2 * (x - quarterReal q) ≤ Real.pi / 2 := harg_pair.2
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le hlow hupp
  have hcos_abs :
      |Real.cos (2 * (x - quarterReal q))| = Real.cos (2 * r) := by
    have hcos_abs' : Real.cos (|2 * (x - quarterReal q)|) = Real.cos (2 * (x - quarterReal q)) := by
      simpa using Real.cos_abs (2 * (x - quarterReal q))
    have harg_abs : |2 * (x - quarterReal q)| = 2 * r := by
      unfold r
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [abs_of_nonneg hcos_nonneg, ← hcos_abs', harg_abs]
  have hcos_le : Real.cos (2 * r) ≤ Real.cos (2 * delta) := by
    have hleft_nonneg : 0 ≤ 2 * delta := by positivity [delta_pos]
    have hright_le_pi : 2 * r ≤ Real.pi := by
      linarith [hr_le, Real.pi_pos]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hleft_nonneg hright_le_pi (by nlinarith [hdelta_le])
  calc
    |Real.cos (2 * x)| = |Real.cos (2 * (x - quarterReal q))| := hcos_shift
    _ = Real.cos (2 * r) := hcos_abs
    _ ≤ Real.cos (2 * delta) := hcos_le

private lemma abs_cos_two_mul_le_cos_two_delta_of_mem_torusInterval_of_lt_pi_div_four
    {x deltaBox : ℝ}
    (hdelta_pos : 0 < deltaBox) (hdelta_lt : deltaBox < Real.pi / 4)
    (hx : x ∈ Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4))
    (hfar : ∀ q : Fin 4, deltaBox ≤ |x - quarterReal q|) :
    |Real.cos (2 * x)| ≤ Real.cos (2 * deltaBox) := by
  rcases exists_quarterReal_close_of_mem_torusInterval hx with ⟨q, hqclose⟩
  let r : ℝ := |x - quarterReal q|
  have hdelta_le : deltaBox ≤ r := by
    simpa [r] using hfar q
  have hr_le : r ≤ Real.pi / 4 := by
    simpa [r] using hqclose
  have hcos_shift :
      |Real.cos (2 * x)| = |Real.cos (2 * (x - quarterReal q))| := by
    have hrew :
        2 * x = 2 * (x - quarterReal q) + (q : Nat) * Real.pi := by
      unfold quarterReal
      ring
    rw [hrew, Real.cos_add_nat_mul_pi]
    simp [abs_mul]
  have harg_le : |2 * (x - quarterReal q)| ≤ Real.pi / 2 := by
    have habs2 : |2 * (x - quarterReal q)| = 2 * |x - quarterReal q| := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have : 2 * |x - quarterReal q| ≤ Real.pi / 2 := by
      nlinarith [hqclose]
    simpa [habs2] using this
  have hcos_nonneg : 0 ≤ Real.cos (2 * (x - quarterReal q)) := by
    have harg_pair : -(Real.pi / 2) ≤ 2 * (x - quarterReal q) ∧
        2 * (x - quarterReal q) ≤ Real.pi / 2 := abs_le.mp harg_le
    have hlow : -(Real.pi / 2) ≤ 2 * (x - quarterReal q) := harg_pair.1
    have hupp : 2 * (x - quarterReal q) ≤ Real.pi / 2 := harg_pair.2
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le hlow hupp
  have hcos_abs :
      |Real.cos (2 * (x - quarterReal q))| = Real.cos (2 * r) := by
    have hcos_abs' : Real.cos (|2 * (x - quarterReal q)|) = Real.cos (2 * (x - quarterReal q)) := by
      simpa using Real.cos_abs (2 * (x - quarterReal q))
    have harg_abs : |2 * (x - quarterReal q)| = 2 * r := by
      unfold r
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [abs_of_nonneg hcos_nonneg, ← hcos_abs', harg_abs]
  have hcos_le : Real.cos (2 * r) ≤ Real.cos (2 * deltaBox) := by
    have hleft_nonneg : 0 ≤ 2 * deltaBox := by positivity [hdelta_pos]
    have hright_le_pi : 2 * r ≤ Real.pi := by
      linarith [hr_le, Real.pi_pos]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hleft_nonneg hright_le_pi (by nlinarith [hdelta_le])
  calc
    |Real.cos (2 * x)| = |Real.cos (2 * (x - quarterReal q))| := hcos_shift
    _ = Real.cos (2 * r) := hcos_abs
    _ ≤ Real.cos (2 * deltaBox) := hcos_le

end Cn3Torus

lemma momentX_eq_avgOver_W_pow (n : ℕ) (lam : Fin n → Fin n → ℝ) (k : ℕ) :
    momentX n lam k =
      Cn3Torus.avgOver n (fun y => (Cn3Torus.W (edgeLam n lam) y) ^ k) := by
  have hsum :
      ∑ σ : Fin n → Fin 2, (innerX n lam σ) ^ k
        =
      ∑ y : Fin n → Bool, (Cn3Torus.W (edgeLam n lam) y) ^ k := by
    exact Fintype.sum_equiv (signVecEquivBoolVec n)
      (fun σ : Fin n → Fin 2 => (innerX n lam σ) ^ k)
      (fun y : Fin n → Bool => (Cn3Torus.W (edgeLam n lam) y) ^ k)
      (by
        intro σ
        simp [signVecEquivBoolVec, innerX_eq_edgePhase, Cn3Torus.phase_eq_W])
  unfold momentX Cn3Torus.avgOver
  simp [div_eq_mul_inv, hsum, mul_comm]

lemma avgSigns_abs_innerX_pow_eq_avgOver_abs_W_pow
    (n : ℕ) (lam : Fin n → Fin n → ℝ) (k : ℕ) :
    avgSigns n (fun σ => |innerX n lam σ| ^ k) =
      Cn3Torus.avgOver n (fun y => |Cn3Torus.W (edgeLam n lam) y| ^ k) := by
  have hsum :
      ∑ σ : Fin n → Fin 2, |innerX n lam σ| ^ k
        =
      ∑ y : Fin n → Bool, |Cn3Torus.W (edgeLam n lam) y| ^ k := by
    exact Fintype.sum_equiv (signVecEquivBoolVec n)
      (fun σ : Fin n → Fin 2 => |innerX n lam σ| ^ k)
      (fun y : Fin n → Bool => |Cn3Torus.W (edgeLam n lam) y| ^ k)
      (by
        intro σ
        simp [signVecEquivBoolVec, innerX_eq_edgePhase, Cn3Torus.phase_eq_W])
  unfold avgSigns Cn3Torus.avgOver
  simp [div_eq_mul_inv, hsum, mul_comm]

private lemma avgSigns_eq_avgOver_signVecToBoolVec
    (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    avgSigns n (fun σ => f (signVecToBoolVec σ)) = Cn3Torus.avgOver n f := by
  have hsum :
      ∑ σ : Fin n → Fin 2, f (signVecToBoolVec σ)
        = ∑ y : Fin n → Bool, f y := by
    exact Fintype.sum_equiv (signVecEquivBoolVec n)
      (fun σ : Fin n → Fin 2 => f (signVecToBoolVec σ))
      (fun y : Fin n → Bool => f y)
      (by
        intro σ
        simp [signVecEquivBoolVec])
  unfold avgSigns Cn3Torus.avgOver
  simp [div_eq_mul_inv, hsum, mul_comm]

/-- The `k`th row coefficients of the strict upper-triangular matrix, padded by
`0` on the diagonal. -/
private def rowCoeff (n : ℕ) (gam : Fin n → Fin n → ℝ) (k : Fin n) : Fin n → ℝ :=
  fun i => if i = k then 0 else if i < k then gam i k else gam k i

private lemma rowCoeff_eq_edgeLam_offdiag (n : ℕ) (gam : Fin n → Fin n → ℝ) (k : Fin n)
    (j : {m : Fin n // m ≠ k}) :
    rowCoeff n gam k j.1 = edgeLam n gam (Cn3Torus.edgeFromOffdiag k j) := by
  unfold rowCoeff edgeLam
  by_cases hlt : j.1 < k
  · have hnot : ¬ k < j.1 := hlt.not_gt
    simp [Cn3Torus.edgeFromOffdiag, j.2, hlt, hnot]
  · have hgt : k < j.1 := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm j.2)
    simp [Cn3Torus.edgeFromOffdiag, j.2, hlt, hgt]

private lemma linearX_rowCoeff_eq_sum_offdiag (n : ℕ) (gam : Fin n → Fin n → ℝ) (k : Fin n)
    (σ : Fin n → Fin 2) :
    linearX n (rowCoeff n gam k) σ
      = ∑ j : {m : Fin n // m ≠ k},
          edgeLam n gam (Cn3Torus.edgeFromOffdiag k j) * (signOf (σ j.1) : ℝ) := by
  classical
  let f : Fin n → ℝ := fun i => rowCoeff n gam k i * (signOf (σ i) : ℝ)
  have hkzero : f k = 0 := by
    simp [f, rowCoeff]
  have hsum :
      ∑ i : Fin n, f i = Finset.sum (Finset.univ.erase k) f := by
    calc
      ∑ i : Fin n, f i = Finset.sum (Finset.univ.erase k) f + f k := by
        simpa [add_comm] using
          (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n))) (a := k) (f := f) (by simp))
      _ = Finset.sum (Finset.univ.erase k) f := by simp [hkzero]
  have hattach :
      Finset.sum (Finset.univ.erase k) f
        = ∑ i : {j : Fin n // j ∈ (Finset.univ.erase k)}, f i.1 := by
    symm
    simpa using (Finset.sum_attach (s := (Finset.univ.erase k)) (f := f))
  let eraseIso : {j : Fin n // j ∈ (Finset.univ.erase k)} ≃ {j : Fin n // j ≠ k} := {
    toFun := fun j => ⟨j.1, (Finset.mem_erase.mp j.2).1⟩
    invFun := fun j => ⟨j.1, Finset.mem_erase.mpr ⟨j.2, Finset.mem_univ _⟩⟩
    left_inv := by
      intro j
      apply Subtype.ext
      rfl
    right_inv := by
      intro j
      apply Subtype.ext
      rfl
  }
  have hreindex :
      (∑ j : {i : Fin n // i ∈ (Finset.univ.erase k)}, f j.1)
        = ∑ j : {m : Fin n // m ≠ k},
            edgeLam n gam (Cn3Torus.edgeFromOffdiag k j) * (signOf (σ j.1) : ℝ) := by
    exact Fintype.sum_equiv eraseIso
      (fun j => f j.1)
      (fun j => edgeLam n gam (Cn3Torus.edgeFromOffdiag k j) * (signOf (σ j.1) : ℝ))
      (by
        intro j
        change rowCoeff n gam k (eraseIso j).1 * (signOf (σ j.1) : ℝ)
          = edgeLam n gam (Cn3Torus.edgeFromOffdiag k (eraseIso j)) * (signOf (σ j.1) : ℝ)
        rw [rowCoeff_eq_edgeLam_offdiag n gam k (eraseIso j)])
  calc
    linearX n (rowCoeff n gam k) σ = ∑ i : Fin n, f i := by
      rfl
    _ = Finset.sum (Finset.univ.erase k) f := hsum
    _ = ∑ i : {j : Fin n // j ∈ (Finset.univ.erase k)}, f i.1 := hattach
    _ = ∑ j : {m : Fin n // m ≠ k},
          edgeLam n gam (Cn3Torus.edgeFromOffdiag k j) * (signOf (σ j.1) : ℝ) := hreindex

namespace Cn3Torus

private lemma sq_avgOver_abs_le_avgOver_sq (n : ℕ) (f : (Fin n → Bool) → ℝ) :
    (avgOver n (fun y => |f y|)) ^ 2 ≤ avgOver n (fun y => f y ^ (2 : Nat)) := by
  set N : ℝ := (2 ^ n : ℝ)
  have hNpos : 0 < N := by positivity
  have hN2pos : 0 < N ^ 2 := sq_pos_of_pos hNpos
  have hsum :
      (∑ y : Fin n → Bool, |f y|) ^ 2 ≤ N * ∑ y : Fin n → Bool, (f y) ^ (2 : Nat) := by
    simpa [sq_abs, Fintype.card_fun, Fintype.card_fin] using
      sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin n → Bool)))
        (f := fun y : Fin n → Bool => |f y|)
  have havg_eq :
      avgOver n (fun y => |f y|) = (∑ y : Fin n → Bool, |f y|) / N := by
    unfold avgOver
    simp [N]
  have hsq_eq :
      avgOver n (fun y => f y ^ (2 : Nat)) = (∑ y : Fin n → Bool, (f y) ^ (2 : Nat)) / N := by
    unfold avgOver
    simp [N]
  rw [havg_eq, hsq_eq]
  have hkey :
      (∑ y : Fin n → Bool, |f y|) ^ 2 * N
        ≤ (∑ y : Fin n → Bool, (f y) ^ (2 : Nat)) * N ^ 2 := by
    nlinarith [hsum, hNpos]
  have hdiv :
      (∑ y : Fin n → Bool, |f y|) ^ 2 / N ^ 2
        ≤ (∑ y : Fin n → Bool, (f y) ^ (2 : Nat)) / N :=
    (div_le_div_iff₀ hN2pos hNpos).mpr (by simpa [mul_comm] using hkey)
  rw [div_pow]
  exact hdiv

private lemma phase_flipBoolAt_eq_sub_two_incident (n : ℕ) (i : Fin n) (lam : Edge n → ℝ)
    (y : Fin n → Bool) :
    phase lam (flipBoolAt i y)
      = phase lam y - 2 * Finset.sum (edgesIncident n i) (fun e => lam e * Z y e) := by
  unfold phase
  calc
    ∑ e : Edge n, lam e * Z (flipBoolAt i y) e
        = ∑ e : Edge n,
            (lam e * Z y e - 2 * (if e ∈ edgesIncident n i then lam e * Z y e else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro e he
              rw [Z_flip_at]
              by_cases hmem : e ∈ edgesIncident n i
              · simp [hmem]
                ring
              · simp [hmem]
    _ = (∑ e : Edge n, lam e * Z y e) - 2 * (∑ e : Edge n,
          if e ∈ edgesIncident n i then lam e * Z y e else 0) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = phase lam y - 2 * Finset.sum (edgesIncident n i) (fun e => lam e * Z y e) := by
          simp [phase]

private lemma incident_sum_edgeLam_eq_sign_mul_linearX (n : ℕ) (gam : Fin n → Fin n → ℝ) (k : Fin n)
    (σ : Fin n → Fin 2) :
    Finset.sum (edgesIncident n k) (fun e => edgeLam n gam e * Z (signVecToBoolVec σ) e)
      = (signOf (σ k) : ℝ) * linearX n (rowCoeff n gam k) σ := by
  classical
  let eIso : {e : Edge n // e ∈ edgesIncident n k} ≃ {j : Fin n // j ≠ k} :=
    incidentEdgeEquivOffdiag n k
  have hsum :
      (∑ eSub : {e : Edge n // e ∈ edgesIncident n k},
          edgeLam n gam eSub.1 * Z (signVecToBoolVec σ) eSub.1)
        = ∑ j : {m : Fin n // m ≠ k},
            edgeLam n gam (edgeFromOffdiag k j)
              * Z (signVecToBoolVec σ) (edgeFromOffdiag k j) := by
    exact Fintype.sum_equiv eIso
      (fun eSub : {e : Edge n // e ∈ edgesIncident n k} =>
        edgeLam n gam eSub.1 * Z (signVecToBoolVec σ) eSub.1)
      (fun j : {m : Fin n // m ≠ k} =>
        edgeLam n gam (edgeFromOffdiag k j)
          * Z (signVecToBoolVec σ) (edgeFromOffdiag k j))
      (by
        intro eSub
        have hEq :
            edgeFromOffdiag k (offdiagOfIncident k eSub.1 eSub.2) = eSub.1 :=
          edgeFromOffdiag_offdiagOfIncident (n := n) k eSub.1 eSub.2
        simpa [eIso] using
          (congrArg (fun e : Edge n => edgeLam n gam e * Z (signVecToBoolVec σ) e) hEq).symm)
  calc
    Finset.sum (edgesIncident n k) (fun e => edgeLam n gam e * Z (signVecToBoolVec σ) e)
      = ∑ eSub : {e : Edge n // e ∈ edgesIncident n k},
          edgeLam n gam eSub.1 * Z (signVecToBoolVec σ) eSub.1 := by
            symm
            exact Finset.sum_attach (edgesIncident n k)
              (fun e : Edge n => edgeLam n gam e * Z (signVecToBoolVec σ) e)
    _ = ∑ j : {m : Fin n // m ≠ k},
        edgeLam n gam (edgeFromOffdiag k j)
          * Z (signVecToBoolVec σ) (edgeFromOffdiag k j)
        := hsum
    _ = ∑ j : {m : Fin n // m ≠ k},
          (signOf (σ k) : ℝ)
            * (edgeLam n gam (edgeFromOffdiag k j) * (signOf (σ j.1) : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              by_cases hlt : j.1 < k
              · have hnot : ¬ k < j.1 := hlt.not_gt
                simp [Z, edgeFromOffdiag, hlt, hnot, signVecToBoolVec,
                  spin_fin2ToBool_eq_signOf, mul_assoc, mul_left_comm, mul_comm]
              · have hgt : k < j.1 := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm j.2)
                simp [Z, edgeFromOffdiag, hlt, hgt, signVecToBoolVec,
                  spin_fin2ToBool_eq_signOf, mul_assoc, mul_left_comm, mul_comm]
    _ = (signOf (σ k) : ℝ)
          * ∑ j : {m : Fin n // m ≠ k},
              edgeLam n gam (edgeFromOffdiag k j) * (signOf (σ j.1) : ℝ) := by
            rw [Finset.mul_sum]
    _ = (signOf (σ k) : ℝ) * linearX n (rowCoeff n gam k) σ := by
          rw [linearX_rowCoeff_eq_sum_offdiag]

end Cn3Torus

/-- The box B_δ = {λ : |λ_{ij}| ≤ δ for all i < j}. -/
def box (n : ℕ) (delta : ℝ) : Set (Fin n → Fin n → ℝ) :=
  {lam | ∀ i j : Fin n, i < j → |lam i j| ≤ delta}

/-- The Euclidean ball D_r = {λ : s(λ) ≤ r²}. -/
private def euclidBall' (n : ℕ) (r : ℝ) : Set (Fin n → Fin n → ℝ) :=
  {lam | sNorm n lam ≤ r ^ 2}

/-- The inner-core region D_t = {λ : s(λ) ≤ d/t}. -/
def coreRegion (n : ℕ) (t : ℝ) : Set (Fin n → Fin n → ℝ) :=
  {lam | sNorm n lam ≤ (dim n : ℝ) / t}

/-- Rowwise cosine product appearing in the DL10 product bound. -/
private def rowCosProd (n : ℕ) (k : Fin n) (lam : Fin n → Fin n → ℝ) : ℝ :=
  ∏ i : Fin n,
    if i = k then 1 else
    if i < k then Real.cos (2 * lam i k)
    else Real.cos (2 * lam k i)

/-- The even far shell R_even^far. -/
private def evenFarShell (n : ℕ) (r : ℝ) : Set (Fin n → Fin n → ℝ) :=
  {lam | lam ∈ box n (π / 4) ∧ r ^ 2 ≤ sNorm n lam}

/-- Edge-coordinate transport of the prototype box `B_δ`. -/
def edgeBox (n : ℕ) (delta : ℝ) : Set (Cn3Torus.Edge n → ℝ) :=
  {mu | matrixOfEdge n mu ∈ box n delta}

/-- Edge-coordinate transport of the Euclidean ball `D_r`. -/
def edgeEuclidBall (n : ℕ) (r : ℝ) : Set (Cn3Torus.Edge n → ℝ) :=
  {mu | matrixOfEdge n mu ∈ euclidBall' n r}

/-- Edge-coordinate transport of the core region `D_t`. -/
def edgeCoreRegion (n : ℕ) (t : ℝ) : Set (Cn3Torus.Edge n → ℝ) :=
  {mu | matrixOfEdge n mu ∈ coreRegion n t}

/-- Edge-coordinate transport of the even far shell. -/
def edgeEvenFarShell (n : ℕ) (r : ℝ) : Set (Cn3Torus.Edge n → ℝ) :=
  {mu | matrixOfEdge n mu ∈ evenFarShell n r}

lemma edgeBox_eq_pi (n : ℕ) (delta : ℝ) :
    edgeBox n delta = Set.pi Set.univ (fun _ : Cn3Torus.Edge n => Set.Icc (-delta) delta) := by
  ext mu
  constructor
  · intro hmu
    rw [Set.mem_pi]
    intro e he
    have hcoord := hmu e.1.1 e.1.2 e.2
    simpa [Set.mem_Icc, abs_le, matrixOfEdge, e.2] using hcoord
  · intro hmu
    rw [Set.mem_pi] at hmu
    intro i j hij
    have hcoord := hmu ⟨(i, j), hij⟩ (by simp)
    simpa [Set.mem_Icc, abs_le, matrixOfEdge, hij] using hcoord

lemma edgeBox_isCompact (n : ℕ) (delta : ℝ) : IsCompact (edgeBox n delta) := by
  rw [edgeBox_eq_pi]
  simpa [Set.pi_univ_Icc] using
    (isCompact_Icc :
      IsCompact (Set.Icc (fun _ : Cn3Torus.Edge n => (-delta)) (fun _ : Cn3Torus.Edge n => delta)))

lemma edgeBox_volume_eq (n : ℕ) (delta : ℝ) (hdelta : 0 ≤ delta) :
    MeasureTheory.volume (edgeBox n delta)
      = ENNReal.ofReal (((2 * delta) ^ (dim n : Nat) : ℝ)) := by
  rw [edgeBox_eq_pi]
  calc
    MeasureTheory.volume (Set.univ.pi (fun _ : Cn3Torus.Edge n => Set.Icc (-delta) delta))
      = ∏ _ : Cn3Torus.Edge n, MeasureTheory.volume (Set.Icc (-delta) delta) := by
          simpa using
            (MeasureTheory.volume_pi_pi
              (s := fun _ : Cn3Torus.Edge n => Set.Icc (-delta) delta))
    _ = ∏ _ : Cn3Torus.Edge n, ENNReal.ofReal (2 * delta) := by
          have hlen : delta - (-delta) = 2 * delta := by ring
          simpa [Real.volume_Icc, hlen]
    _ = (ENNReal.ofReal (2 * delta)) ^ Fintype.card (Cn3Torus.Edge n) := by
          simp [Finset.prod_const]
    _ = ENNReal.ofReal (((2 * delta) ^ (Fintype.card (Cn3Torus.Edge n)) : ℝ)) := by
          symm
          exact ENNReal.ofReal_pow (by positivity) (Fintype.card (Cn3Torus.Edge n))
    _ = ENNReal.ofReal (((2 * delta) ^ (dim n : Nat) : ℝ)) := by
          simp [card_Edge_eq_dim]

namespace Cn3Torus

private lemma quarterReal_add_mem_torusInterval_of_mem_Icc (q : Fin 4) {deltaBox u : ℝ}
    (hdelta_lt : deltaBox < Real.pi / 4)
    (hu : u ∈ Set.Icc (-deltaBox) deltaBox) :
    quarterReal q + u ∈ Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4) := by
  rcases hu with ⟨hul, huu⟩
  constructor
  · have hdelta : -(Real.pi / 4) ≤ -deltaBox := by
      linarith
    have hu_low : -(Real.pi / 4) ≤ u := le_trans hdelta hul
    have hq_nonneg : 0 ≤ quarterReal q := by
      have hhalf_nonneg : (0 : ℝ) ≤ Real.pi / 2 := by positivity [Real.pi_pos]
      have hqnat_nonneg : (0 : ℝ) ≤ (q : ℕ) := Nat.cast_nonneg _
      simpa [quarterReal] using mul_nonneg hqnat_nonneg hhalf_nonneg
    linarith
  · have hdelta : deltaBox ≤ Real.pi / 4 := le_of_lt hdelta_lt
    have hupper_q : quarterReal q ≤ 3 * Real.pi / 2 := by
      fin_cases q <;> simp [quarterReal] <;> nlinarith [Real.pi_pos]
    have hupper_q' : quarterReal q + deltaBox ≤ 7 * Real.pi / 4 := by
      nlinarith [hupper_q, hdelta, Real.pi_pos]
    linarith

private lemma translated_edgeBox_subset_torusBox (n : ℕ) {deltaBox : ℝ}
    (hdelta_lt : deltaBox < Real.pi / 4) :
    ∀ a ∈ lambdaShifts n, translateSet a (edgeBox n deltaBox) ⊆ torusBox n := by
  intro a ha x hx
  rcases (mem_lambdaShifts_iff_exists n a).1 ha with ⟨b, hb, hba⟩
  change x - a ∈ edgeBox n deltaBox at hx
  rw [edgeBox_eq_pi] at hx
  intro e he
  have hu : (x - a) e ∈ Set.Icc (-deltaBox) deltaBox := hx e (by simp)
  have hxcoord : x e = quarterReal (b e) + (x - a) e := by
    have hae : a e = quarterReal (b e) := by
      simpa [lambdaReal] using congrArg (fun f => f e) hba.symm
    calc
      x e = a e + (x - a) e := by
        simp [Pi.sub_apply]
      _ = quarterReal (b e) + (x - a) e := by rw [hae]
  exact hxcoord ▸ quarterReal_add_mem_torusInterval_of_mem_Icc (q := b e) hdelta_lt hu

private lemma translated_edgeBoxes_disjoint (n : ℕ) {deltaBox : ℝ}
    (hdelta_lt : deltaBox < Real.pi / 4) :
    ∀ a ∈ lambdaShifts n, ∀ b ∈ lambdaShifts n, a ≠ b →
      Disjoint (translateSet a (edgeBox n deltaBox)) (translateSet b (edgeBox n deltaBox)) := by
  intro a ha b hb hab
  refine Set.disjoint_left.2 ?_
  intro x hxa hxb
  rcases exists_coord_sep_of_distinct_shifts n ha hb hab with ⟨e, hsep⟩
  change x - a ∈ edgeBox n deltaBox at hxa
  change x - b ∈ edgeBox n deltaBox at hxb
  rw [edgeBox_eq_pi] at hxa hxb
  have hxa_e : (x - a) e ∈ Set.Icc (-deltaBox) deltaBox := hxa e (by simp)
  have hxb_e : (x - b) e ∈ Set.Icc (-deltaBox) deltaBox := hxb e (by simp)
  have hxa_abs : |x e - a e| ≤ deltaBox := by
    have hmem : x e - a e ∈ Set.Icc (-deltaBox) deltaBox := by
      simpa using hxa_e
    exact abs_le.mpr (Set.mem_Icc.mp hmem)
  have hxb_abs : |x e - b e| ≤ deltaBox := by
    have hmem : x e - b e ∈ Set.Icc (-deltaBox) deltaBox := by
      simpa using hxb_e
    exact abs_le.mpr (Set.mem_Icc.mp hmem)
  have hab_le : |a e - b e| ≤ 2 * deltaBox := by
    have htri : |a e - b e| ≤ |a e - x e| + |x e - b e| := abs_sub_le (a e) (x e) (b e)
    have htri' : |a e - b e| ≤ |x e - a e| + |x e - b e| := by
      simpa [abs_sub_comm, add_comm, add_left_comm, add_assoc] using htri
    linarith
  have h2delta : 2 * deltaBox < Real.pi / 2 := by
    linarith
  have hstrict : |a e - b e| < Real.pi / 2 := lt_of_le_of_lt hab_le h2delta
  exact (not_lt_of_ge hsep) hstrict

private lemma measurableSet_translate_edgeBox (n : ℕ) (a : Edge n → ℝ) (delta : ℝ) :
    MeasurableSet (translateSet a (edgeBox n delta)) := by
  unfold translateSet
  exact (edgeBox_isCompact n delta).measurableSet.preimage (measurable_id.sub_const a)

/-- Union of the quarter-lattice translates of the variable primary box `B_δ`. -/
private def edgePrimaryBoxUnion (n : ℕ) (delta : ℝ) : Set (Edge n → ℝ) :=
  ⋃ a ∈ lambdaShifts n, translateSet a (edgeBox n delta)

/-- Residual torus region left after removing all translated primary boxes. -/
def edgeResidualTorusRegion (n : ℕ) (delta : ℝ) : Set (Edge n → ℝ) :=
  torusBox n \ edgePrimaryBoxUnion n delta

private lemma measurableSet_edgePrimaryBoxUnion (n : ℕ) (delta : ℝ) :
    MeasurableSet (edgePrimaryBoxUnion n delta) := by
  unfold edgePrimaryBoxUnion
  classical
  simpa using Finset.measurableSet_biUnion (lambdaShifts n)
    (fun a ha => measurableSet_translate_edgeBox n a delta)

private lemma measurableSet_edgeResidualTorusRegion (n : ℕ) (delta : ℝ) :
    MeasurableSet (edgeResidualTorusRegion n delta) := by
  unfold edgeResidualTorusRegion
  exact (measurableSet_torusBox n).diff (measurableSet_edgePrimaryBoxUnion n delta)

private lemma edgePrimaryBoxUnion_subset_torusBox (n : ℕ) {delta : ℝ}
    (hdelta_lt : delta < Real.pi / 4) :
    edgePrimaryBoxUnion n delta ⊆ torusBox n := by
  intro x hx
  unfold edgePrimaryBoxUnion at hx
  rcases Set.mem_iUnion.mp hx with ⟨a, hx⟩
  rcases Set.mem_iUnion.mp hx with ⟨ha, hxa⟩
  exact translated_edgeBox_subset_torusBox n hdelta_lt a ha hxa

private lemma edgePrimaryBoxUnion_disjoint_edgeResidualTorusRegion (n : ℕ) (delta : ℝ) :
    Disjoint (edgePrimaryBoxUnion n delta) (edgeResidualTorusRegion n delta) := by
  unfold edgeResidualTorusRegion
  exact Set.disjoint_sdiff_right

private lemma integral_translate_lambdaShift_edgeBox (n t : ℕ) (a : Edge n → ℝ)
    (ha : a ∈ lambdaShifts n) (delta : ℝ) :
    (∫ x in translateSet a (edgeBox n delta), Complex.re (psi n x ^ (4 * t)))
      = ∫ x in edgeBox n delta, Complex.re (psi n x ^ (4 * t)) := by
  have htrans := integral_translateSet n a (edgeBox n delta)
    (fun x => Complex.re (psi n x ^ (4 * t))) ((edgeBox_isCompact n delta).measurableSet)
  have hswap :
      (fun x : Edge n → ℝ => Complex.re (psi n (x + a) ^ (4 * t)))
        = (fun x : Edge n → ℝ => Complex.re (psi n (fun e => a e + x e) ^ (4 * t))) := by
    funext x
    have hadd : x + a = (fun e => a e + x e) := by
      funext e
      simp [Pi.add_apply, add_comm]
    simp [hadd]
  have hpow_shift :
      (fun x : Edge n → ℝ => Complex.re (psi n (fun e => a e + x e) ^ (4 * t)))
        = (fun x : Edge n → ℝ => Complex.re (psi n x ^ (4 * t))) := by
    funext x
    simpa [psi_pow_translate_lambdaShift n t a ha x]
  calc
    (∫ x in translateSet a (edgeBox n delta), Complex.re (psi n x ^ (4 * t)))
        = ∫ x in edgeBox n delta, Complex.re (psi n (x + a) ^ (4 * t)) := by
            simpa [htrans]
    _ = ∫ x in edgeBox n delta, Complex.re (psi n (fun e => a e + x e) ^ (4 * t)) := by
          simp [hswap]
    _ = ∫ x in edgeBox n delta, Complex.re (psi n x ^ (4 * t)) := by
          simp [hpow_shift]

private lemma pairwiseDisjoint_translateSet_edgeBox (n : ℕ) {deltaBox : ℝ}
    (hdelta_lt : deltaBox < Real.pi / 4) :
    Set.Pairwise (↑(lambdaShifts n))
      (fun a b => Disjoint (translateSet a (edgeBox n deltaBox)) (translateSet b (edgeBox n deltaBox))) := by
  intro a ha b hb hab
  exact translated_edgeBoxes_disjoint n hdelta_lt a ha b hb hab

private lemma integral_edgePrimaryBoxUnion_eq_shift_card_mul_edgeBox (n t : ℕ) {delta : ℝ}
    (hdelta_lt : delta < Real.pi / 4) :
    (∫ lam in edgePrimaryBoxUnion n delta, Complex.re (psi n lam ^ (4 * t)))
      = ((lambdaShifts n).card : ℝ) * ∫ lam in edgeBox n delta, Complex.re (psi n lam ^ (4 * t)) := by
  have hsum :
      (∫ lam in edgePrimaryBoxUnion n delta, Complex.re (psi n lam ^ (4 * t)))
        = ∑ a ∈ lambdaShifts n,
            ∫ lam in translateSet a (edgeBox n delta), Complex.re (psi n lam ^ (4 * t)) := by
    unfold edgePrimaryBoxUnion
    exact MeasureTheory.integral_biUnion_finset (μ := MeasureTheory.volume)
      (t := lambdaShifts n)
      (s := fun a => translateSet a (edgeBox n delta))
      (f := fun lam => Complex.re (psi n lam ^ (4 * t)))
      (fun a ha => measurableSet_translate_edgeBox n a delta)
      (pairwiseDisjoint_translateSet_edgeBox n hdelta_lt)
      (fun a ha => integrableOn_integrand_of_subset_torus n t
        (translated_edgeBox_subset_torusBox n hdelta_lt a ha))
  calc
    (∫ lam in edgePrimaryBoxUnion n delta, Complex.re (psi n lam ^ (4 * t)))
        = ∑ a ∈ lambdaShifts n,
            ∫ lam in translateSet a (edgeBox n delta), Complex.re (psi n lam ^ (4 * t)) := hsum
    _ = ∑ a ∈ lambdaShifts n, ∫ lam in edgeBox n delta, Complex.re (psi n lam ^ (4 * t)) := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          simp [integral_translate_lambdaShift_edgeBox n t a ha delta]
    _ = ((lambdaShifts n).card : ℝ) * ∫ lam in edgeBox n delta, Complex.re (psi n lam ^ (4 * t)) := by
          simpa [nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
            (Finset.sum_const (s := lambdaShifts n)
              (b := ∫ lam in edgeBox n delta, Complex.re (psi n lam ^ (4 * t))))

end Cn3Torus

lemma mem_edgeEuclidBall_iff (n : ℕ) (r : ℝ) (mu : Cn3Torus.Edge n → ℝ) :
    mu ∈ edgeEuclidBall n r ↔ Cn3Torus.sqNormEdge n mu ≤ r ^ 2 := by
  simp [edgeEuclidBall, euclidBall', sNorm_matrixOfEdge_eq]

lemma mem_edgeCoreRegion_iff (n : ℕ) (t : ℝ) (mu : Cn3Torus.Edge n → ℝ) :
    mu ∈ edgeCoreRegion n t ↔ Cn3Torus.sqNormEdge n mu ≤ (dim n : ℝ) / t := by
  simp [edgeCoreRegion, coreRegion, sNorm_matrixOfEdge_eq]

lemma measurableSet_edgeEuclidBall (n : ℕ) (r : ℝ) :
    MeasurableSet (edgeEuclidBall n r) := by
  have hsq :
      Measurable (fun mu : Cn3Torus.Edge n → ℝ => Cn3Torus.sqNormEdge n mu) :=
    (Cn3Torus.continuous_sqNormEdge n).measurable
  have hset :
      edgeEuclidBall n r
        = {mu : Cn3Torus.Edge n → ℝ | Cn3Torus.sqNormEdge n mu ≤ r ^ 2} := by
    ext mu
    exact mem_edgeEuclidBall_iff n r mu
  rw [hset]
  exact measurableSet_le hsq measurable_const

lemma measurableSet_edgeCoreRegion (n : ℕ) (t : ℝ) :
    MeasurableSet (edgeCoreRegion n t) := by
  have hsq :
      Measurable (fun mu : Cn3Torus.Edge n → ℝ => Cn3Torus.sqNormEdge n mu) :=
    (Cn3Torus.continuous_sqNormEdge n).measurable
  have hset :
      edgeCoreRegion n t
        = {mu : Cn3Torus.Edge n → ℝ | Cn3Torus.sqNormEdge n mu ≤ (dim n : ℝ) / t} := by
    ext mu
    exact mem_edgeCoreRegion_iff n t mu
  rw [hset]
  exact measurableSet_le hsq measurable_const

lemma mem_edgeEvenFarShell_iff (n : ℕ) (r : ℝ) (mu : Cn3Torus.Edge n → ℝ) :
    mu ∈ edgeEvenFarShell n r
      ↔ mu ∈ edgeBox n (π / 4) ∧ r ^ 2 ≤ Cn3Torus.sqNormEdge n mu := by
  simp [edgeEvenFarShell, edgeBox, evenFarShell, sNorm_matrixOfEdge_eq]

/-!
## Fourier Inversion and Count Bridge
This section packages the de Launey-Levin quarter-scale Fourier bridge in the
form used by the rest of the active development.
-/

/-- **Fact 2.3** [DL10]: quarter-scale Fourier inversion in the edge-coordinate
torus model. This is the exact bridge from the combinatorial normalized count
to the normalized torus integral. -/
theorem normalizedCount_eq_normalizedTargetIntegral (n t : ℕ) :
    normalizedCount n (4 * t) = Cn3Torus.normalizedTargetIntegral n t := by
  have hre :
      Cn3Torus.targetIntegral n t = Complex.re (Cn3Torus.torusIntegralC n (4 * t)) := by
    symm
    simpa [Cn3Torus.targetIntegral] using Cn3Torus.lem_fourier_inversion_all n (4 * t)
  have hcomplex_real :
      Cn3Torus.torusIntegralC n (4 * t)
        = ((((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ) : ℂ) *
            ((↑(hadamardCount n (4 * t)) : ℂ) / ((2 : ℂ) ^ (n * (4 * t))))) := by
          rw [torusIntegralC_eq_volume_mul_hadamardCount, complex_pow_two_nat]
          simp [div_eq_mul_inv, mul_comm, mul_left_comm]
  have htarget :
      Cn3Torus.targetIntegral n t =
        ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ) *
          ((hadamardCount n (4 * t) : ℝ) / (2 ^ (n * (4 * t)) : ℝ)) := by
    calc
      Cn3Torus.targetIntegral n t = Complex.re (Cn3Torus.torusIntegralC n (4 * t)) := hre
      _ = ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ) *
            ((hadamardCount n (4 * t) : ℝ) / (2 ^ (n * (4 * t)) : ℝ)) := by
              rw [hcomplex_real, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                complex_two_pow_nat]
              simpa using (complex_nat_div_re (hadamardCount n (4 * t)) (2 ^ (n * (4 * t))))
  unfold Cn3Torus.normalizedTargetIntegral normalizedCount
  rw [htarget]
  have hvol_nonzero : (((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ)) ≠ 0 := by
    positivity [Real.pi_pos]
  field_simp [hvol_nonzero]

/- The lattice facts are proved below from the representative-box
classification and the edge-side quarter-lattice translation lemmas. -/

/-- The midpoint of two unit phases separated by angle `2D` has norm `|cos D|`. -/
private lemma norm_phase_pair_half_le_abs_cos (A D : ℝ) :
    ‖(((Complex.exp (Complex.I * (A : ℂ)))
        + Complex.exp (Complex.I * ((A - 2 * D : ℝ) : ℂ))) / 2 : ℂ)‖
      ≤ |Real.cos D| := by
  let z : ℂ :=
    (((Complex.exp (Complex.I * (A : ℂ)))
      + Complex.exp (Complex.I * ((A - 2 * D : ℝ) : ℂ))) / 2 : ℂ)
  have hz_re : z.re = Real.cos (A - D) * Real.cos D := by
    have hcos :
        (Real.cos A + Real.cos (A - 2 * D)) / 2 = Real.cos (A - D) * Real.cos D := by
      calc
        (Real.cos A + Real.cos (A - 2 * D)) / 2
            = (2 * Real.cos ((A + (A - 2 * D)) / 2) * Real.cos ((A - (A - 2 * D)) / 2)) / 2 := by
                rw [Real.cos_add_cos]
        _ = Real.cos (A - D) * Real.cos D := by
              congr 1 <;> ring
    have hre1 : (Complex.exp (Complex.I * (A : ℂ))).re = Real.cos A := by
      simpa [mul_comm] using (Complex.exp_ofReal_mul_I_re A)
    have hre2 :
        (Complex.exp (Complex.I * ((A : ℂ) - 2 * (D : ℂ)))).re = Real.cos (A - 2 * D) := by
      have hcast : (((A - 2 * D : ℝ) : ℂ)) = (A : ℂ) - 2 * (D : ℂ) := by
        norm_num
      simpa [hcast, mul_comm] using (Complex.exp_ofReal_mul_I_re (A - 2 * D))
    unfold z
    simp [Complex.div_re, hre1, hre2, hcos]
  have hz_im : z.im = Real.sin (A - D) * Real.cos D := by
    have hsin :
        (Real.sin A + Real.sin (A - 2 * D)) / 2 = Real.sin (A - D) * Real.cos D := by
      calc
        (Real.sin A + Real.sin (A - 2 * D)) / 2
            = (2 * Real.sin ((A + (A - 2 * D)) / 2) * Real.cos ((A - (A - 2 * D)) / 2)) / 2 := by
                rw [Real.sin_add_sin]
        _ = Real.sin (A - D) * Real.cos D := by
              congr 1 <;> ring
    have him1 : (Complex.exp (Complex.I * (A : ℂ))).im = Real.sin A := by
      simpa [mul_comm] using (Complex.exp_ofReal_mul_I_im A)
    have him2 :
        (Complex.exp (Complex.I * ((A : ℂ) - 2 * (D : ℂ)))).im = Real.sin (A - 2 * D) := by
      have hcast : (((A - 2 * D : ℝ) : ℂ)) = (A : ℂ) - 2 * (D : ℂ) := by
        norm_num
      simpa [hcast, mul_comm] using (Complex.exp_ofReal_mul_I_im (A - 2 * D))
    unfold z
    simp [Complex.div_im, him1, him2, hsin]
  have hsq :
      ‖z‖ ^ (2 : Nat) = |Real.cos D| ^ (2 : Nat) := by
    rw [Complex.sq_norm, Complex.normSq_apply, hz_re, hz_im, sq_abs]
    have htrig : Real.sin (A - D) ^ (2 : Nat) + Real.cos (A - D) ^ (2 : Nat) = 1 := by
      simpa [pow_two, add_comm] using (Real.sin_sq_add_cos_sq (A - D))
    nlinarith [htrig]
  have hnonneg : 0 ≤ ‖z‖ := norm_nonneg z
  have habs : 0 ≤ |Real.cos D| := abs_nonneg _
  have hle : ‖z‖ ≤ |Real.cos D| := by
    nlinarith [hsq]
  simpa [z] using hle

/-- **Fact 3.3** [DL10]: Full magnitude bound with product. -/
theorem universal_magnitude_bound_full (n : ℕ) (hn : 2 ≤ n)
    (gam : Fin n → Fin n → ℝ) (k : Fin n) :
  ‖psi n gam‖ ^ 2 ≤ 1/2 + 1/2 * ∏ i : Fin n,
    if i = k then 1 else
    if i < k then Real.cos (2 * gam i k)
    else Real.cos (2 * gam k i) := by
  let μ : Cn3Torus.Edge n → ℝ := edgeLam n gam
  let inc : (Fin n → Bool) → ℝ :=
    fun y => Finset.sum (Cn3Torus.edgesIncident n k) (fun e => μ e * Cn3Torus.Z y e)
  let paired : (Fin n → Bool) → ℂ := fun y =>
    (((Complex.exp (Complex.I * (Cn3Torus.phase μ y : ℂ)))
      + Complex.exp (Complex.I * (Cn3Torus.phase μ (Cn3Torus.flipBoolAt k y) : ℂ))) / 2 : ℂ)
  have hpairsum :
      ∑ y : Fin n → Bool, Complex.exp (Complex.I * (Cn3Torus.phase μ y : ℂ))
        = ∑ y : Fin n → Bool, paired y := by
    have hflipSum :
        ∑ y : Fin n → Bool, Complex.exp (Complex.I * (Cn3Torus.phase μ (Cn3Torus.flipBoolAt k y) : ℂ))
          = ∑ y : Fin n → Bool, Complex.exp (Complex.I * (Cn3Torus.phase μ y : ℂ)) := by
      simpa using
        (Cn3Torus.sum_flipBoolAt_eq k
          (fun y : Fin n → Bool =>
            Complex.exp (Complex.I * (Cn3Torus.phase μ y : ℂ))))
    have hpairExpand :
        (∑ y : Fin n → Bool, paired y)
          = ((∑ y : Fin n → Bool, Complex.exp (Complex.I * (Cn3Torus.phase μ y : ℂ)))
              + ∑ y : Fin n → Bool,
                  Complex.exp (Complex.I * (Cn3Torus.phase μ (Cn3Torus.flipBoolAt k y) : ℂ))) / 2 := by
      calc
        (∑ y : Fin n → Bool, paired y)
            = ∑ y : Fin n → Bool,
                ((Complex.exp (Complex.I * (Cn3Torus.phase μ y : ℂ))
                  + Complex.exp (Complex.I * (Cn3Torus.phase μ (Cn3Torus.flipBoolAt k y) : ℂ))) / 2 : ℂ) := by
                    rfl
        _ = ∑ y : Fin n → Bool,
              ((Complex.exp (Complex.I * (Cn3Torus.phase μ y : ℂ))
                + Complex.exp (Complex.I * (Cn3Torus.phase μ (Cn3Torus.flipBoolAt k y) : ℂ))) * (2 : ℂ)⁻¹) := by
                  simp [div_eq_mul_inv]
        _ = ∑ y : Fin n → Bool,
              ((2 : ℂ)⁻¹ * (Complex.exp (Complex.I * (Cn3Torus.phase μ y : ℂ))
                + Complex.exp (Complex.I * (Cn3Torus.phase μ (Cn3Torus.flipBoolAt k y) : ℂ)))) := by
                  refine Finset.sum_congr rfl ?_
                  intro y hy
                  ring
        _ = (2 : ℂ)⁻¹ * ∑ y : Fin n → Bool,
              (Complex.exp (Complex.I * (Cn3Torus.phase μ y : ℂ))
                + Complex.exp (Complex.I * (Cn3Torus.phase μ (Cn3Torus.flipBoolAt k y) : ℂ))) := by
                  rw [Finset.mul_sum]
        _ = (2 : ℂ)⁻¹ *
              ((∑ y : Fin n → Bool, Complex.exp (Complex.I * (Cn3Torus.phase μ y : ℂ)))
                + ∑ y : Fin n → Bool,
                    Complex.exp (Complex.I * (Cn3Torus.phase μ (Cn3Torus.flipBoolAt k y) : ℂ))) := by
                  rw [Finset.sum_add_distrib]
        _ = ((∑ y : Fin n → Bool, Complex.exp (Complex.I * (Cn3Torus.phase μ y : ℂ)))
              + ∑ y : Fin n → Bool,
                  Complex.exp (Complex.I * (Cn3Torus.phase μ (Cn3Torus.flipBoolAt k y) : ℂ))) / 2 := by
                    simp [div_eq_mul_inv, mul_comm]
    calc
      ∑ y : Fin n → Bool, Complex.exp (Complex.I * (Cn3Torus.phase μ y : ℂ))
          = ((∑ y : Fin n → Bool, Complex.exp (Complex.I * (Cn3Torus.phase μ y : ℂ)))
              + ∑ y : Fin n → Bool,
                  Complex.exp (Complex.I * (Cn3Torus.phase μ (Cn3Torus.flipBoolAt k y) : ℂ))) / 2 := by
                    rw [hflipSum]
                    ring
      _ = ∑ y : Fin n → Bool, paired y := by
            exact hpairExpand.symm
  have hnorm :
      ‖psi n gam‖ ≤ Cn3Torus.avgOver n (fun y => |Real.cos (inc y)|) := by
    rw [psi_eq_edgePsi]
    unfold Cn3Torus.psi Cn3Torus.avgOver
    rw [hpairsum]
    have hnonneg_inv : 0 ≤ ‖((↑(2 ^ n : ℕ) : ℂ)⁻¹)‖ := norm_nonneg _
    calc
      ‖(∑ y : Fin n → Bool, paired y) / (2 ^ n : ℂ)‖
          = ‖((↑(2 ^ n : ℕ) : ℂ)⁻¹)‖ * ‖∑ y : Fin n → Bool, paired y‖ := by
              simpa [div_eq_mul_inv, mul_comm] using
                (norm_mul (∑ y : Fin n → Bool, paired y) (((↑(2 ^ n : ℕ) : ℂ)⁻¹)))
      _ ≤ ‖((↑(2 ^ n : ℕ) : ℂ)⁻¹)‖ * ∑ y : Fin n → Bool, ‖paired y‖ := by
            exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hnonneg_inv
      _ ≤ ‖((↑(2 ^ n : ℕ) : ℂ)⁻¹)‖ * ∑ y : Fin n → Bool, |Real.cos (inc y)| := by
            refine mul_le_mul_of_nonneg_left ?_ hnonneg_inv
            refine Finset.sum_le_sum ?_
            intro y hy
            have hflip :=
              Cn3Torus.phase_flipBoolAt_eq_sub_two_incident n k μ y
            simpa [paired, inc, hflip] using
              norm_phase_pair_half_le_abs_cos (Cn3Torus.phase μ y) (inc y)
      _ = Cn3Torus.avgOver n (fun y => |Real.cos (inc y)|) := by
            unfold Cn3Torus.avgOver
            simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hsq :
      ‖psi n gam‖ ^ 2 ≤ (Cn3Torus.avgOver n (fun y => |Real.cos (inc y)|)) ^ 2 := by
    have havg_nonneg : 0 ≤ Cn3Torus.avgOver n (fun y => |Real.cos (inc y)|) := by
      unfold Cn3Torus.avgOver
      positivity
    nlinarith [hnorm, norm_nonneg (psi n gam), havg_nonneg]
  have hcauchy :
      (Cn3Torus.avgOver n (fun y => |Real.cos (inc y)|)) ^ 2
        ≤ Cn3Torus.avgOver n (fun y => Real.cos (inc y) ^ (2 : Nat)) := by
    simpa using Cn3Torus.sq_avgOver_abs_le_avgOver_sq n (fun y => Real.cos (inc y))
  have hcossq :
      Cn3Torus.avgOver n (fun y => Real.cos (inc y) ^ (2 : Nat))
        = 1 / 2 + 1 / 2 * ∏ i : Fin n,
            if i = k then 1 else
            if i < k then Real.cos (2 * gam i k)
            else Real.cos (2 * gam k i) := by
    calc
      Cn3Torus.avgOver n (fun y => Real.cos (inc y) ^ (2 : Nat))
          = avgSigns n
              (fun σ => Real.cos (linearX n (rowCoeff n gam k) σ) ^ (2 : Nat)) := by
                rw [← avgSigns_eq_avgOver_signVecToBoolVec]
                apply avgSigns_congr
                intro σ
                have hinc :
                    inc (signVecToBoolVec σ)
                      = (signOf (σ k) : ℝ) * linearX n (rowCoeff n gam k) σ := by
                    simpa [inc, μ] using
                      Cn3Torus.incident_sum_edgeLam_eq_sign_mul_linearX n gam k σ
                rw [hinc]
                let b : Fin 2 := σ k
                have hb_nat : ((b : Fin 2) : ℕ) = 0 ∨ ((b : Fin 2) : ℕ) = 1 := by
                  have hlt : ((b : Fin 2) : ℕ) < 2 := b.2
                  omega
                rcases hb_nat with hb0 | hb1
                · have hb0' : b = 0 := Fin.ext hb0
                  simp [b, hb0', signOf, Real.cos_neg]
                · have hb1' : b = 1 := Fin.ext hb1
                  simp [b, hb1', signOf, Real.cos_neg]
      _ = 1 / 2 + 1 / 2 * ∏ i : Fin n, Real.cos (2 * rowCoeff n gam k i) := by
            rw [avgSigns_cos_sq_linearX_eq_half_one_add_half_prod]
      _ = 1 / 2 + 1 / 2 * ∏ i : Fin n,
            if i = k then 1 else
            if i < k then Real.cos (2 * gam i k)
            else Real.cos (2 * gam k i) := by
            congr 2
            refine Finset.prod_congr rfl ?_
            intro i hi
            by_cases hik : i = k
            · simp [rowCoeff, hik]
            · by_cases hlt : i < k
              · simp [rowCoeff, hik, hlt]
              · have hgt : k < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hik)
                simp [rowCoeff, hik, hlt, hgt]
  linarith [hsq, hcauchy, hcossq]

private lemma avgSigns_mul_const_left_prehc6 (n : ℕ) (c : ℝ) (f : (Fin n → Fin 2) → ℝ) :
    avgSigns n (fun σ => c * f σ) = c * avgSigns n f := by
  simpa [avgSigns, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

private lemma avgSigns_linearX_sq_prehc6 (n : ℕ) (x : Fin n → ℝ) :
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
      rw [hpoint, avgSigns_add_aux, avgSigns_const_aux, ih]
      symm
      simpa [x₀, a] using sum_sq_snoc n x₀ a

private lemma avgSigns_linearX_four_prehc6 (n : ℕ) (x : Fin n → ℝ) :
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
      rw [avgSigns_add_aux, avgSigns_add_aux, avgSigns_const_aux,
        avgSigns_mul_const_left_prehc6, avgSigns_linearX_sq_prehc6, ih]
      symm
      have hs2 : (∑ i : Fin (n + 1), (Fin.snoc (α := fun _ => ℝ) x₀ a i) ^ (2 : Nat))
            = (∑ i : Fin n, x₀ i ^ (2 : Nat)) + a ^ (2 : Nat) := sum_sq_snoc n x₀ a
      have hs4 : (∑ i : Fin (n + 1), (Fin.snoc (α := fun _ => ℝ) x₀ a i) ^ (4 : Nat))
            = (∑ i : Fin n, x₀ i ^ (4 : Nat)) + a ^ (4 : Nat) := sum_fourth_snoc n x₀ a
      rw [hs2, hs4]
      ring

private lemma avgSigns_linearX_six_le_prehc6 (n : ℕ) (x : Fin n → ℝ) :
    avgSigns n (fun σ => linearX n x σ ^ (6 : Nat))
      ≤ 15 * (∑ i : Fin n, x i ^ (2 : Nat)) ^ (3 : Nat) := by
  induction n with
  | zero =>
      simp [avgSigns, linearX]
  | succ n ih =>
      let x₀ : Fin n → ℝ := Fin.init (α := fun _ => ℝ) x
      let a : ℝ := x (Fin.last n)
      let S : ℝ := ∑ i : Fin n, x₀ i ^ (2 : Nat)
      have hx : Fin.snoc (α := fun _ => ℝ) x₀ a = x := by
        funext i
        refine Fin.lastCases ?_ ?_ i
        · simp [a, Fin.snoc]
        · intro j
          simp [x₀, Fin.snoc, Fin.init]
      have hS_nonneg : 0 ≤ S := by
        dsimp [S]
        exact Finset.sum_nonneg (fun _ _ => by positivity)
      have ha2_nonneg : 0 ≤ a ^ (2 : Nat) := by positivity
      have hlin4_le :
          avgSigns n (fun σ => linearX n x₀ σ ^ (4 : Nat)) ≤ 3 * S ^ (2 : Nat) := by
        have hsum4_nonneg : 0 ≤ ∑ i : Fin n, x₀ i ^ (4 : Nat) := by
          exact Finset.sum_nonneg (fun _ _ => by positivity)
        rw [avgSigns_linearX_four_prehc6]
        dsimp [S]
        nlinarith
      have hlin2_eq : avgSigns n (fun σ => linearX n x₀ σ ^ (2 : Nat)) = S := by
        simpa [S] using avgSigns_linearX_sq_prehc6 n x₀
      have hpoint :
          (fun σ : Fin n → Fin 2 =>
            ((∑ b : Fin 2,
                (linearX (n + 1) (Fin.snoc (α := fun _ => ℝ) x₀ a)
                  (Fin.snoc (α := fun _ => Fin 2) σ b)) ^ (6 : Nat)) / 2 : ℝ))
            =
          (fun σ : Fin n → Fin 2 =>
            linearX n x₀ σ ^ (6 : Nat)
              + 15 * a ^ (2 : Nat) * linearX n x₀ σ ^ (4 : Nat)
              + 15 * a ^ (4 : Nat) * linearX n x₀ σ ^ (2 : Nat)
              + a ^ (6 : Nat)) := by
        funext σ
        have hs :=
          congrArg (fun t : ℝ => t / 2) (sum_sixth_over_last_sign (linearX n x₀ σ) a)
        simpa [linearX_snoc_last, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hs
      calc
        avgSigns (n + 1) (fun σ => linearX (n + 1) x σ ^ (6 : Nat))
            = avgSigns n
                (fun σ : Fin n → Fin 2 =>
                  ((∑ b : Fin 2,
                      (linearX (n + 1) x (Fin.snoc (α := fun _ => Fin 2) σ b)) ^ (6 : Nat)) / 2 : ℝ)) := by
                  simpa [hx] using
                    (avgSigns_split_last n (fun σ => linearX (n + 1) x σ ^ (6 : Nat)))
        _ = avgSigns n (fun σ =>
                linearX n x₀ σ ^ (6 : Nat)
                  + 15 * a ^ (2 : Nat) * linearX n x₀ σ ^ (4 : Nat)
                  + 15 * a ^ (4 : Nat) * linearX n x₀ σ ^ (2 : Nat)
                  + a ^ (6 : Nat)) := by
                  simpa [hx] using congrArg (fun f : (Fin n → Fin 2) → ℝ => avgSigns n f) hpoint
        _ = avgSigns n (fun σ => linearX n x₀ σ ^ (6 : Nat))
              + 15 * a ^ (2 : Nat) * avgSigns n (fun σ => linearX n x₀ σ ^ (4 : Nat))
              + 15 * a ^ (4 : Nat) * avgSigns n (fun σ => linearX n x₀ σ ^ (2 : Nat))
              + a ^ (6 : Nat) := by
                rw [avgSigns_add_aux, avgSigns_add_aux, avgSigns_add_aux, avgSigns_const_aux,
                  avgSigns_mul_const_left_prehc6, avgSigns_mul_const_left_prehc6]
        _ ≤ 15 * S ^ (3 : Nat) + 15 * a ^ (2 : Nat) * (3 * S ^ (2 : Nat))
              + 15 * a ^ (4 : Nat) * S + a ^ (6 : Nat) := by
                have hμ_term :
                    avgSigns n (fun σ => linearX n x₀ σ ^ (6 : Nat)) ≤ 15 * S ^ (3 : Nat) := by
                  simpa [S, x₀] using ih x₀
                have hlin4_term :
                    15 * a ^ (2 : Nat) * avgSigns n (fun σ => linearX n x₀ σ ^ (4 : Nat))
                      ≤ 15 * a ^ (2 : Nat) * (3 * S ^ (2 : Nat)) := by
                  gcongr
                have hlin2_term :
                    15 * a ^ (4 : Nat) * avgSigns n (fun σ => linearX n x₀ σ ^ (2 : Nat))
                      ≤ 15 * a ^ (4 : Nat) * S := by
                  rw [hlin2_eq]
                nlinarith [hμ_term, hlin4_term, hlin2_term]
        _ ≤ 15 * (S + a ^ (2 : Nat)) ^ (3 : Nat) := by
              have hSa_nonneg : 0 ≤ S * a ^ (2 : Nat) := by positivity
              have hSa4_nonneg : 0 ≤ S * a ^ (4 : Nat) := by positivity
              have ha6_nonneg : 0 ≤ a ^ (6 : Nat) := by positivity
              nlinarith [hS_nonneg, ha2_nonneg, hSa_nonneg, hSa4_nonneg, ha6_nonneg]
        _ = 15 * (∑ i : Fin (n + 1), (Fin.snoc (α := fun _ => ℝ) x₀ a i) ^ (2 : Nat)) ^ (3 : Nat) := by
              simpa [S] using congrArg (fun t : ℝ => 15 * t ^ (3 : Nat)) (sum_sq_snoc n x₀ a).symm
        _ = 15 * (∑ i : Fin (n + 1), x i ^ (2 : Nat)) ^ (3 : Nat) := by
              rw [← hx]

private lemma avgSigns_linearX_eight_le_prehc8 (n : ℕ) (x : Fin n → ℝ) :
    avgSigns n (fun σ => linearX n x σ ^ (8 : Nat))
      ≤ 105 * (∑ i : Fin n, x i ^ (2 : Nat)) ^ (4 : Nat) := by
  induction n with
  | zero =>
      simp [avgSigns, linearX]
  | succ n ih =>
      let x₀ : Fin n → ℝ := Fin.init (α := fun _ => ℝ) x
      let a : ℝ := x (Fin.last n)
      let S : ℝ := ∑ i : Fin n, x₀ i ^ (2 : Nat)
      have hx : Fin.snoc (α := fun _ => ℝ) x₀ a = x := by
        funext i
        refine Fin.lastCases ?_ ?_ i
        · simp [a, Fin.snoc]
        · intro j
          simp [x₀, Fin.snoc, Fin.init]
      have hS_nonneg : 0 ≤ S := by
        dsimp [S]
        exact Finset.sum_nonneg (fun _ _ => by positivity)
      have ha2_nonneg : 0 ≤ a ^ (2 : Nat) := by positivity
      have hlin6_le :
          avgSigns n (fun σ => linearX n x₀ σ ^ (6 : Nat)) ≤ 15 * S ^ (3 : Nat) := by
        simpa [x₀, S] using avgSigns_linearX_six_le_prehc6 n x₀
      have hlin4_le :
          avgSigns n (fun σ => linearX n x₀ σ ^ (4 : Nat)) ≤ 3 * S ^ (2 : Nat) := by
        have hsum4_nonneg : 0 ≤ ∑ i : Fin n, x₀ i ^ (4 : Nat) := by
          exact Finset.sum_nonneg (fun _ _ => by positivity)
        rw [avgSigns_linearX_four_prehc6]
        dsimp [S]
        nlinarith
      have hlin2_eq : avgSigns n (fun σ => linearX n x₀ σ ^ (2 : Nat)) = S := by
        simpa [S] using avgSigns_linearX_sq_prehc6 n x₀
      have hpoint :
          (fun σ : Fin n → Fin 2 =>
            ((∑ b : Fin 2,
                (linearX (n + 1) (Fin.snoc (α := fun _ => ℝ) x₀ a)
                  (Fin.snoc (α := fun _ => Fin 2) σ b)) ^ (8 : Nat)) / 2 : ℝ))
            =
          (fun σ : Fin n → Fin 2 =>
            linearX n x₀ σ ^ (8 : Nat)
              + 28 * a ^ (2 : Nat) * linearX n x₀ σ ^ (6 : Nat)
              + 70 * a ^ (4 : Nat) * linearX n x₀ σ ^ (4 : Nat)
              + 28 * a ^ (6 : Nat) * linearX n x₀ σ ^ (2 : Nat)
              + a ^ (8 : Nat)) := by
        funext σ
        have hs :=
          congrArg (fun t : ℝ => t / 2) (sum_eighth_over_last_sign (linearX n x₀ σ) a)
        simpa [linearX_snoc_last, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hs
      calc
        avgSigns (n + 1) (fun σ => linearX (n + 1) x σ ^ (8 : Nat))
            = avgSigns n
                (fun σ : Fin n → Fin 2 =>
                  ((∑ b : Fin 2,
                      (linearX (n + 1) x (Fin.snoc (α := fun _ => Fin 2) σ b)) ^ (8 : Nat)) / 2 : ℝ)) := by
                  simpa [hx] using
                    (avgSigns_split_last n (fun σ => linearX (n + 1) x σ ^ (8 : Nat)))
        _ = avgSigns n (fun σ =>
                linearX n x₀ σ ^ (8 : Nat)
                  + 28 * a ^ (2 : Nat) * linearX n x₀ σ ^ (6 : Nat)
                  + 70 * a ^ (4 : Nat) * linearX n x₀ σ ^ (4 : Nat)
                  + 28 * a ^ (6 : Nat) * linearX n x₀ σ ^ (2 : Nat)
                  + a ^ (8 : Nat)) := by
                  simpa [hx] using congrArg (fun f : (Fin n → Fin 2) → ℝ => avgSigns n f) hpoint
        _ = avgSigns n (fun σ => linearX n x₀ σ ^ (8 : Nat))
              + 28 * a ^ (2 : Nat) * avgSigns n (fun σ => linearX n x₀ σ ^ (6 : Nat))
              + 70 * a ^ (4 : Nat) * avgSigns n (fun σ => linearX n x₀ σ ^ (4 : Nat))
              + 28 * a ^ (6 : Nat) * avgSigns n (fun σ => linearX n x₀ σ ^ (2 : Nat))
              + a ^ (8 : Nat) := by
                rw [avgSigns_add_aux, avgSigns_add_aux, avgSigns_add_aux, avgSigns_add_aux,
                  avgSigns_const_aux, avgSigns_mul_const_left_prehc6, avgSigns_mul_const_left_prehc6,
                  avgSigns_mul_const_left_prehc6]
        _ ≤ 105 * S ^ (4 : Nat) + 28 * a ^ (2 : Nat) * (15 * S ^ (3 : Nat))
              + 70 * a ^ (4 : Nat) * (3 * S ^ (2 : Nat))
              + 28 * a ^ (6 : Nat) * S + a ^ (8 : Nat) := by
                have hμ_term :
                    avgSigns n (fun σ => linearX n x₀ σ ^ (8 : Nat)) ≤ 105 * S ^ (4 : Nat) := by
                  simpa [S, x₀] using ih x₀
                have hlin6_term :
                    28 * a ^ (2 : Nat) * avgSigns n (fun σ => linearX n x₀ σ ^ (6 : Nat))
                      ≤ 28 * a ^ (2 : Nat) * (15 * S ^ (3 : Nat)) := by
                  gcongr
                have hlin4_term :
                    70 * a ^ (4 : Nat) * avgSigns n (fun σ => linearX n x₀ σ ^ (4 : Nat))
                      ≤ 70 * a ^ (4 : Nat) * (3 * S ^ (2 : Nat)) := by
                  gcongr
                have hlin2_term :
                    28 * a ^ (6 : Nat) * avgSigns n (fun σ => linearX n x₀ σ ^ (2 : Nat))
                      ≤ 28 * a ^ (6 : Nat) * S := by
                  rw [hlin2_eq]
                nlinarith [hμ_term, hlin6_term, hlin4_term, hlin2_term]
        _ ≤ 105 * (S + a ^ (2 : Nat)) ^ (4 : Nat) := by
              have hpoly :
                  105 * (S + a ^ (2 : Nat)) ^ (4 : Nat)
                    - (105 * S ^ (4 : Nat) + 28 * a ^ (2 : Nat) * (15 * S ^ (3 : Nat))
                        + 70 * a ^ (4 : Nat) * (3 * S ^ (2 : Nat))
                        + 28 * a ^ (6 : Nat) * S + a ^ (8 : Nat))
                    = 420 * S ^ (2 : Nat) * a ^ (4 : Nat)
                        + 392 * S * a ^ (6 : Nat) + 104 * a ^ (8 : Nat) := by
                ring
              have hpoly_nonneg :
                  0 ≤ 420 * S ^ (2 : Nat) * a ^ (4 : Nat)
                        + 392 * S * a ^ (6 : Nat) + 104 * a ^ (8 : Nat) := by
                positivity
              nlinarith [hpoly, hpoly_nonneg]
        _ = 105 * (∑ i : Fin (n + 1), (Fin.snoc (α := fun _ => ℝ) x₀ a i) ^ (2 : Nat)) ^ (4 : Nat) := by
              simpa [S] using congrArg (fun t : ℝ => 105 * t ^ (4 : Nat)) (sum_sq_snoc n x₀ a).symm
        _ = 105 * (∑ i : Fin (n + 1), x i ^ (2 : Nat)) ^ (4 : Nat) := by
              rw [← hx]

private lemma momentX_six_peel_last_raw_prehc6 (n : ℕ) (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    momentX (n + 1) lam 6
      = avgSigns n (fun σ =>
          innerX n (minorLamLast lam) σ ^ (6 : Nat)
            + 15 * innerX n (minorLamLast lam) σ ^ (4 : Nat)
                * linearX n (lastColLam lam) σ ^ (2 : Nat)
            + 15 * innerX n (minorLamLast lam) σ ^ (2 : Nat)
                * linearX n (lastColLam lam) σ ^ (4 : Nat)
            + linearX n (lastColLam lam) σ ^ (6 : Nat)) := by
  let B : Fin n → Fin n → ℝ := minorLamLast lam
  let x : Fin n → ℝ := lastColLam lam
  have hsplit :
      (∑ τ : Fin (n + 1) → Fin 2, (innerX (n + 1) lam τ) ^ (6 : Nat))
        =
      ∑ σ : Fin n → Fin 2, ∑ b : Fin 2,
        (innerX (n + 1) lam (Fin.snoc (α := fun _ => Fin 2) σ b)) ^ (6 : Nat) := by
    simpa using
      (sum_signVec_split_last n (fun τ : Fin (n + 1) → Fin 2 => (innerX (n + 1) lam τ) ^ (6 : Nat)))
  unfold momentX avgSigns
  rw [hsplit]
  calc
    (↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹
        * ∑ σ : Fin n → Fin 2, ∑ b : Fin 2,
            (innerX (n + 1) lam (Fin.snoc (α := fun _ => Fin 2) σ b)) ^ (6 : Nat)
      =
    (↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹
        * ∑ σ : Fin n → Fin 2, ∑ b : Fin 2,
            (innerX n B σ + (signOf b : ℝ) * linearX n x σ) ^ (6 : Nat) := by
              refine congrArg ((↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹ * ·) ?_
              refine Finset.sum_congr rfl ?_
              intro σ hσ
              refine Finset.sum_congr rfl ?_
              intro b hb
              rw [innerX_snoc_last]
    _ =
      (↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹
        * ∑ σ : Fin n → Fin 2,
            2 * (innerX n B σ ^ (6 : Nat)
              + 15 * innerX n B σ ^ (4 : Nat) * linearX n x σ ^ (2 : Nat)
              + 15 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (4 : Nat)
              + linearX n x σ ^ (6 : Nat)) := by
                refine congrArg ((↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹ * ·) ?_
                refine Finset.sum_congr rfl ?_
                intro σ hσ
                rw [sum_sixth_over_last_sign]
    _ =
      (↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹
        * (2 * ∑ σ : Fin n → Fin 2,
            (innerX n B σ ^ (6 : Nat)
              + 15 * innerX n B σ ^ (4 : Nat) * linearX n x σ ^ (2 : Nat)
              + 15 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (4 : Nat)
              + linearX n x σ ^ (6 : Nat))) := by
                congr 1
                rw [Finset.mul_sum]
    _ =
      ((↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹ * 2)
        * ∑ σ : Fin n → Fin 2,
            (innerX n B σ ^ (6 : Nat)
              + 15 * innerX n B σ ^ (4 : Nat) * linearX n x σ ^ (2 : Nat)
              + 15 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (4 : Nat)
              + linearX n x σ ^ (6 : Nat)) := by
                ring
    _ =
      (↑(2 ^ n : ℕ) : ℝ)⁻¹
        * ∑ σ : Fin n → Fin 2,
            (innerX n B σ ^ (6 : Nat)
              + 15 * innerX n B σ ^ (4 : Nat) * linearX n x σ ^ (2 : Nat)
              + 15 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (4 : Nat)
              + linearX n x σ ^ (6 : Nat)) := by
                have hpow : (↑(2 ^ (n + 1) : ℕ) : ℝ) = (↑(2 ^ n : ℕ) : ℝ) * 2 := by
                  norm_num [pow_succ]
                rw [hpow]
                field_simp
    _ =
      avgSigns n (fun σ =>
        innerX n B σ ^ (6 : Nat)
          + 15 * innerX n B σ ^ (4 : Nat) * linearX n x σ ^ (2 : Nat)
          + 15 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (4 : Nat)
          + linearX n x σ ^ (6 : Nat)) := by
            rfl

private lemma momentX_six_peel_last_prehc6 (n : ℕ) (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    momentX (n + 1) lam 6
      = momentX n (minorLamLast lam) 6
          + 15 * avgSigns n
              (fun σ =>
                innerX n (minorLamLast lam) σ ^ (4 : Nat)
                  * linearX n (lastColLam lam) σ ^ (2 : Nat))
          + 15 * avgSigns n
              (fun σ =>
                innerX n (minorLamLast lam) σ ^ (2 : Nat)
                  * linearX n (lastColLam lam) σ ^ (4 : Nat))
          + avgSigns n (fun σ => linearX n (lastColLam lam) σ ^ (6 : Nat)) := by
  have hfun :
      (fun σ =>
        innerX n (minorLamLast lam) σ ^ (6 : Nat)
          + 15 * innerX n (minorLamLast lam) σ ^ (4 : Nat) * linearX n (lastColLam lam) σ ^ (2 : Nat)
          + 15 * innerX n (minorLamLast lam) σ ^ (2 : Nat) * linearX n (lastColLam lam) σ ^ (4 : Nat)
          + linearX n (lastColLam lam) σ ^ (6 : Nat))
        =
      (fun σ =>
        innerX n (minorLamLast lam) σ ^ (6 : Nat)
          + (15 * innerX n (minorLamLast lam) σ ^ (4 : Nat) * linearX n (lastColLam lam) σ ^ (2 : Nat)
              + (15 * innerX n (minorLamLast lam) σ ^ (2 : Nat) * linearX n (lastColLam lam) σ ^ (4 : Nat)
                + linearX n (lastColLam lam) σ ^ (6 : Nat)))) := by
    funext σ
    ring
  have hmul1 :
      avgSigns n
          (fun σ =>
            15 * innerX n (minorLamLast lam) σ ^ (4 : Nat)
              * linearX n (lastColLam lam) σ ^ (2 : Nat))
        =
      15 * avgSigns n
          (fun σ =>
            innerX n (minorLamLast lam) σ ^ (4 : Nat)
              * linearX n (lastColLam lam) σ ^ (2 : Nat)) := by
    have hpoint :
        (fun σ =>
          15 * innerX n (minorLamLast lam) σ ^ (4 : Nat)
            * linearX n (lastColLam lam) σ ^ (2 : Nat))
          =
        (fun σ =>
          15 * (innerX n (minorLamLast lam) σ ^ (4 : Nat)
            * linearX n (lastColLam lam) σ ^ (2 : Nat))) := by
      funext σ
      ring
    rw [hpoint, avgSigns_mul_const_left_prehc6]
  have hmul2 :
      avgSigns n
          (fun σ =>
            15 * innerX n (minorLamLast lam) σ ^ (2 : Nat)
              * linearX n (lastColLam lam) σ ^ (4 : Nat))
        =
      15 * avgSigns n
          (fun σ =>
            innerX n (minorLamLast lam) σ ^ (2 : Nat)
              * linearX n (lastColLam lam) σ ^ (4 : Nat)) := by
    have hpoint :
        (fun σ =>
          15 * innerX n (minorLamLast lam) σ ^ (2 : Nat)
            * linearX n (lastColLam lam) σ ^ (4 : Nat))
          =
        (fun σ =>
          15 * (innerX n (minorLamLast lam) σ ^ (2 : Nat)
            * linearX n (lastColLam lam) σ ^ (4 : Nat))) := by
      funext σ
      ring
    rw [hpoint, avgSigns_mul_const_left_prehc6]
  rw [momentX_six_peel_last_raw_prehc6, hfun, avgSigns_add_aux, avgSigns_add_aux, avgSigns_add_aux,
    hmul1, hmul2]
  simp [momentX, avgSigns]
  ring

private lemma sum_mul_sq_le_sum_sq_mul_sum_sq_prehc6 {α : Type} [Fintype α] [DecidableEq α]
    (f g : α → ℝ) :
    (∑ i : α, f i * g i) ^ (2 : Nat)
      ≤ (∑ i : α, f i ^ (2 : Nat)) * ∑ i : α, g i ^ (2 : Nat) := by
  let x : EuclideanSpace ℝ α := WithLp.toLp 2 f
  let y : EuclideanSpace ℝ α := WithLp.toLp 2 g
  have hinner : inner ℝ x y = ∑ i : α, f i * g i := by
    simp [x, y, PiLp.inner_apply, mul_comm]
  have hx_sq : ‖x‖ ^ (2 : Nat) = ∑ i : α, f i ^ (2 : Nat) := by
    rw [← real_inner_self_eq_norm_sq x, PiLp.inner_apply]
    simp [x, mul_comm]
  have hy_sq : ‖y‖ ^ (2 : Nat) = ∑ i : α, g i ^ (2 : Nat) := by
    rw [← real_inner_self_eq_norm_sq y, PiLp.inner_apply]
    simp [y, mul_comm]
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

private lemma avgSigns_four_two_sq_le_six_mul_two_four_prehc6 (n : ℕ)
    (f g : (Fin n → Fin 2) → ℝ) :
    (avgSigns n (fun σ => f σ ^ (4 : Nat) * g σ ^ (2 : Nat))) ^ (2 : Nat)
      ≤ avgSigns n (fun σ => f σ ^ (6 : Nat))
          * avgSigns n (fun σ => f σ ^ (2 : Nat) * g σ ^ (4 : Nat)) := by
  let A : ℝ := ∑ σ : Fin n → Fin 2, f σ ^ (4 : Nat) * g σ ^ (2 : Nat)
  let B : ℝ := ∑ σ : Fin n → Fin 2, f σ ^ (6 : Nat)
  let C : ℝ := ∑ σ : Fin n → Fin 2, f σ ^ (2 : Nat) * g σ ^ (4 : Nat)
  let M : ℝ := ((↑(2 ^ n : ℕ) : ℝ)⁻¹)
  have hA :
      (∑ σ : Fin n → Fin 2, (f σ ^ (3 : Nat)) * (f σ * g σ ^ (2 : Nat))) = A := by
    dsimp [A]
    refine Finset.sum_congr rfl ?_
    intro σ hσ
    ring_nf
  have hB :
      (∑ σ : Fin n → Fin 2, (f σ ^ (3 : Nat)) ^ (2 : Nat)) = B := by
    dsimp [B]
    refine Finset.sum_congr rfl ?_
    intro σ hσ
    ring_nf
  have hC :
      (∑ σ : Fin n → Fin 2, (f σ * g σ ^ (2 : Nat)) ^ (2 : Nat)) = C := by
    dsimp [C]
    refine Finset.sum_congr rfl ?_
    intro σ hσ
    ring_nf
  have hsum :
      A ^ (2 : Nat) ≤ B * C := by
    have hraw :=
      (sum_mul_sq_le_sum_sq_mul_sum_sq_prehc6
        (fun σ : Fin n → Fin 2 => f σ ^ (3 : Nat))
        (fun σ : Fin n → Fin 2 => f σ * g σ ^ (2 : Nat)))
    calc
      A ^ (2 : Nat)
          = (∑ σ : Fin n → Fin 2, (f σ ^ (3 : Nat)) * (f σ * g σ ^ (2 : Nat))) ^ (2 : Nat) := by
              rw [hA]
      _ ≤ (∑ σ : Fin n → Fin 2, (f σ ^ (3 : Nat)) ^ (2 : Nat))
            * ∑ σ : Fin n → Fin 2, (f σ * g σ ^ (2 : Nat)) ^ (2 : Nat) := hraw
      _ = B * C := by rw [hB, hC]
  have hcoeff_nonneg : 0 ≤ M ^ (2 : Nat) := by
    dsimp [M]
    positivity
  have hmul :
      M ^ (2 : Nat) * A ^ (2 : Nat)
        ≤ M ^ (2 : Nat) * (B * C) := by
    exact mul_le_mul_of_nonneg_left hsum hcoeff_nonneg
  calc
    (avgSigns n (fun σ => f σ ^ (4 : Nat) * g σ ^ (2 : Nat))) ^ (2 : Nat)
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
    _ = avgSigns n (fun σ => f σ ^ (6 : Nat))
          * avgSigns n (fun σ => f σ ^ (2 : Nat) * g σ ^ (4 : Nat)) := by
            dsimp [M]
            dsimp [B, C]
            unfold avgSigns
            rfl

lemma avgSigns_mul_sq_le_avgSigns_sq_mul_avgSigns_sq (n : ℕ)
    (u v : (Fin n → Fin 2) → ℝ) :
    (avgSigns n (fun σ => u σ * v σ)) ^ (2 : Nat)
      ≤ avgSigns n (fun σ => u σ ^ (2 : Nat))
          * avgSigns n (fun σ => v σ ^ (2 : Nat)) := by
  let A : ℝ := ∑ σ : Fin n → Fin 2, u σ * v σ
  let B : ℝ := ∑ σ : Fin n → Fin 2, u σ ^ (2 : Nat)
  let C : ℝ := ∑ σ : Fin n → Fin 2, v σ ^ (2 : Nat)
  let M : ℝ := ((↑(2 ^ n : ℕ) : ℝ)⁻¹)
  have hsum : A ^ (2 : Nat) ≤ B * C := by
    simpa [A, B, C] using
      (sum_mul_sq_le_sum_sq_mul_sum_sq_prehc6
        (fun σ : Fin n → Fin 2 => u σ) (fun σ : Fin n → Fin 2 => v σ))
  have hcoeff_nonneg : 0 ≤ M ^ (2 : Nat) := by
    dsimp [M]
    positivity
  have hmul :
      M ^ (2 : Nat) * A ^ (2 : Nat)
        ≤ M ^ (2 : Nat) * (B * C) := by
    exact mul_le_mul_of_nonneg_left hsum hcoeff_nonneg
  calc
    (avgSigns n (fun σ => u σ * v σ)) ^ (2 : Nat)
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
    _ = avgSigns n (fun σ => u σ ^ (2 : Nat))
          * avgSigns n (fun σ => v σ ^ (2 : Nat)) := by
            dsimp [M]
            dsimp [B, C]
            unfold avgSigns
            rfl

/-- Manuscript Fact 4.5(i): the degree-2 chaos `W` satisfies the `L^6`
hypercontractive bound with constant `5^6`. -/
theorem fixedDegreeHC_degree2_W_sixth (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (6 : Nat))
      ≤ (5 : ℝ) ^ (6 : Nat) * Cn3Torus.sqNormEdge n mu ^ (3 : Nat) := by
  have hmoment :
      ∀ m : ℕ, ∀ lam : Fin m → Fin m → ℝ,
        momentX m lam 6 ≤ (5 : ℝ) ^ (6 : Nat) * sNorm m lam ^ (3 : Nat) := by
    intro m
    induction m with
    | zero =>
        intro lam
        simp [momentX, avgSigns, innerX, sNorm]
    | succ m ih =>
        intro lam
        let B : Fin m → Fin m → ℝ := minorLamLast lam
        let x : Fin m → ℝ := lastColLam lam
        let sB : ℝ := sNorm m B
        let X : ℝ := ∑ i : Fin m, x i ^ (2 : Nat)
        let mixed42 : ℝ :=
          avgSigns m (fun σ => innerX m B σ ^ (4 : Nat) * linearX m x σ ^ (2 : Nat))
        let mixed24 : ℝ :=
          avgSigns m (fun σ => innerX m B σ ^ (2 : Nat) * linearX m x σ ^ (4 : Nat))
        have hsB_nonneg : 0 ≤ sB := by
          dsimp [sB, B]
          unfold sNorm
          positivity
        have hX_nonneg : 0 ≤ X := by
          dsimp [X, x]
          exact Finset.sum_nonneg (fun _ _ => by positivity)
        have hμ6B :
            momentX m B 6 ≤ (5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat) := by
          simpa [B, sB] using ih B
        have hμ6B_avg :
            avgSigns m (fun σ => innerX m B σ ^ (6 : Nat))
              ≤ (5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat) := by
          simpa [momentX, avgSigns] using hμ6B
        have hlin6_le :
            avgSigns m (fun σ => linearX m x σ ^ (6 : Nat)) ≤ 15 * X ^ (3 : Nat) := by
          simpa [x, X] using avgSigns_linearX_six_le_prehc6 m x
        have hmixed42_nonneg : 0 ≤ mixed42 := by
          dsimp [mixed42]
          unfold avgSigns
          positivity
        have hmixed24_nonneg : 0 ≤ mixed24 := by
          dsimp [mixed24]
          unfold avgSigns
          positivity
        have hmixed42_sq :
            mixed42 ^ (2 : Nat)
              ≤ avgSigns m (fun σ => innerX m B σ ^ (6 : Nat)) * mixed24 := by
          dsimp [mixed42, mixed24]
          have hmain :=
            avgSigns_four_two_sq_le_six_mul_two_four_prehc6 m
              (fun σ => innerX m B σ) (fun σ => linearX m x σ)
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
        have hmixed24_sq :
            mixed24 ^ (2 : Nat)
              ≤ avgSigns m (fun σ => linearX m x σ ^ (6 : Nat)) * mixed42 := by
          dsimp [mixed42, mixed24]
          have hmain :=
            avgSigns_four_two_sq_le_six_mul_two_four_prehc6 m
              (fun σ => linearX m x σ) (fun σ => innerX m B σ)
          simpa [mul_comm, mul_left_comm, mul_assoc] using hmain
        have hmixed42_sq' :
            mixed42 ^ (2 : Nat)
              ≤ ((5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat)) * mixed24 := by
          calc
            mixed42 ^ (2 : Nat)
                ≤ avgSigns m (fun σ => innerX m B σ ^ (6 : Nat)) * mixed24 := hmixed42_sq
            _ ≤ ((5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat)) * mixed24 := by
                  exact mul_le_mul hμ6B_avg (le_rfl) hmixed24_nonneg
                    (by positivity : 0 ≤ (5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat))
        have hmixed24_sq' :
            mixed24 ^ (2 : Nat)
              ≤ (15 * X ^ (3 : Nat)) * mixed42 := by
          calc
            mixed24 ^ (2 : Nat)
                ≤ avgSigns m (fun σ => linearX m x σ ^ (6 : Nat)) * mixed42 := hmixed24_sq
            _ ≤ (15 * X ^ (3 : Nat)) * mixed42 := by
                  exact mul_le_mul hlin6_le (le_rfl) hmixed42_nonneg
                    (by positivity : 0 ≤ 15 * X ^ (3 : Nat))
        have huv_bound :
            mixed42 * mixed24
              ≤ ((5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat)) * (15 * X ^ (3 : Nat)) := by
          let U : ℝ := mixed42 * mixed24
          let R : ℝ := ((5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat)) * (15 * X ^ (3 : Nat))
          have hright_nonneg :
              0 ≤ R := by
            positivity
          have hsq :
              U ^ (2 : Nat) ≤ R * U := by
            calc
              U ^ (2 : Nat)
                  = mixed42 ^ (2 : Nat) * mixed24 ^ (2 : Nat) := by ring
              _ ≤ (((5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat)) * mixed24)
                    * ((15 * X ^ (3 : Nat)) * mixed42) := by
                      gcongr
              _ = R * U := by
                      ring
          have huv_nonneg : 0 ≤ U := by positivity
          by_contra hU
          have hgt : R < U := lt_of_not_ge hU
          have hmul_lt : R * U < U ^ (2 : Nat) := by
            nlinarith [hgt, huv_nonneg, hright_nonneg]
          linarith
        have hmixed42_le :
            mixed42 ≤ 1600 * sB ^ (2 : Nat) * X := by
          have hleft_nonneg : 0 ≤ mixed42 := by positivity
          let R : ℝ := 1600 * sB ^ (2 : Nat) * X
          have hcube :
              mixed42 ^ (3 : Nat) ≤ R ^ (3 : Nat) := by
            calc
              mixed42 ^ (3 : Nat)
                  = mixed42 ^ (2 : Nat) * mixed42 := by ring
              _ ≤ (((5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat)) * mixed24) * mixed42 := by
                    gcongr
              _ = ((5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat)) * (mixed42 * mixed24) := by
                    ring
              _ ≤ ((5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat))
                    * (((5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat)) * (15 * X ^ (3 : Nat))) := by
                      gcongr
              _ ≤ ((1600 : ℝ) ^ (3 : Nat)) * (sB ^ (6 : Nat) * X ^ (3 : Nat)) := by
                    have hconst :
                        ((5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat))
                          * (((5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat)) * (15 * X ^ (3 : Nat)))
                          = ((((5 : ℝ) ^ (6 : Nat)) ^ (2 : Nat)) * 15)
                              * (sB ^ (6 : Nat) * X ^ (3 : Nat)) := by
                                ring_nf
                    rw [hconst]
                    have hnum : ((((5 : ℝ) ^ (6 : Nat)) ^ (2 : Nat)) * 15) ≤ (1600 : ℝ) ^ (3 : Nat) := by
                      norm_num
                    have hnonneg : 0 ≤ sB ^ (6 : Nat) * X ^ (3 : Nat) := by positivity
                    exact mul_le_mul_of_nonneg_right hnum hnonneg
              _ = R ^ (3 : Nat) := by
                    ring
          have hright_nonneg : 0 ≤ R := by positivity
          by_contra hR
          have hgt : R < mixed42 := lt_of_not_ge hR
          have hcube_gt : R ^ (3 : Nat) < mixed42 ^ (3 : Nat) := by
            have hfac_pos :
                0 < (mixed42 - R) * (mixed42 ^ (2 : Nat) + mixed42 * R + R ^ (2 : Nat)) := by
              have h1 : 0 < mixed42 - R := sub_pos.mpr hgt
              have hmixed42_pos : 0 < mixed42 := lt_of_le_of_lt hright_nonneg hgt
              have h2 : 0 < mixed42 ^ (2 : Nat) + mixed42 * R + R ^ (2 : Nat) := by
                have hsq_pos : 0 < mixed42 ^ (2 : Nat) := by positivity
                nlinarith
              exact mul_pos h1 h2
            have hfac :
                mixed42 ^ (3 : Nat) - R ^ (3 : Nat)
                  = (mixed42 - R) * (mixed42 ^ (2 : Nat) + mixed42 * R + R ^ (2 : Nat)) := by
                    ring
            have : 0 < mixed42 ^ (3 : Nat) - R ^ (3 : Nat) := by
              simpa [hfac] using hfac_pos
            linarith
          linarith
        have hmixed24_le :
            mixed24 ≤ 1600 * sB * X ^ (2 : Nat) := by
          have hleft_nonneg : 0 ≤ mixed24 := by positivity
          let R : ℝ := 1600 * sB * X ^ (2 : Nat)
          have hcube :
              mixed24 ^ (3 : Nat) ≤ R ^ (3 : Nat) := by
            calc
              mixed24 ^ (3 : Nat)
                  = mixed24 ^ (2 : Nat) * mixed24 := by ring
              _ ≤ ((15 * X ^ (3 : Nat)) * mixed42) * mixed24 := by
                    gcongr
              _ = (15 * X ^ (3 : Nat)) * (mixed42 * mixed24) := by
                    ring
              _ ≤ (15 * X ^ (3 : Nat))
                    * (((5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat)) * (15 * X ^ (3 : Nat))) := by
                      gcongr
              _ ≤ ((1600 : ℝ) ^ (3 : Nat)) * (sB ^ (3 : Nat) * X ^ (6 : Nat)) := by
                    have hconst :
                        (15 * X ^ (3 : Nat))
                          * (((5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat)) * (15 * X ^ (3 : Nat)))
                          = (((5 : ℝ) ^ (6 : Nat)) * 225)
                              * (sB ^ (3 : Nat) * X ^ (6 : Nat)) := by
                                ring_nf
                    rw [hconst]
                    have hnum : (((5 : ℝ) ^ (6 : Nat)) * 225) ≤ (1600 : ℝ) ^ (3 : Nat) := by
                      norm_num
                    have hnonneg : 0 ≤ sB ^ (3 : Nat) * X ^ (6 : Nat) := by positivity
                    exact mul_le_mul_of_nonneg_right hnum hnonneg
              _ = R ^ (3 : Nat) := by
                    ring
          have hright_nonneg : 0 ≤ R := by positivity
          by_contra hR
          have hgt : R < mixed24 := lt_of_not_ge hR
          have hcube_gt : R ^ (3 : Nat) < mixed24 ^ (3 : Nat) := by
            have hfac_pos :
                0 < (mixed24 - R) * (mixed24 ^ (2 : Nat) + mixed24 * R + R ^ (2 : Nat)) := by
              have h1 : 0 < mixed24 - R := sub_pos.mpr hgt
              have hmixed24_pos : 0 < mixed24 := lt_of_le_of_lt hright_nonneg hgt
              have h2 : 0 < mixed24 ^ (2 : Nat) + mixed24 * R + R ^ (2 : Nat) := by
                have hsq_pos : 0 < mixed24 ^ (2 : Nat) := by positivity
                nlinarith
              exact mul_pos h1 h2
            have hfac :
                mixed24 ^ (3 : Nat) - R ^ (3 : Nat)
                  = (mixed24 - R) * (mixed24 ^ (2 : Nat) + mixed24 * R + R ^ (2 : Nat)) := by
                    ring
            have : 0 < mixed24 ^ (3 : Nat) - R ^ (3 : Nat) := by
              simpa [hfac] using hfac_pos
            linarith
          linarith
        calc
          momentX (m + 1) lam 6
              = momentX m B 6 + 15 * mixed42 + 15 * mixed24
                  + avgSigns m (fun σ => linearX m x σ ^ (6 : Nat)) := by
                    simpa [B, x, mixed42, mixed24] using momentX_six_peel_last_prehc6 m lam
          _ ≤ (5 : ℝ) ^ (6 : Nat) * sB ^ (3 : Nat)
                + 15 * (1600 * sB ^ (2 : Nat) * X)
                + 15 * (1600 * sB * X ^ (2 : Nat))
                + 15 * X ^ (3 : Nat) := by
                  nlinarith [hμ6B, hmixed42_le, hmixed24_le, hlin6_le]
          _ ≤ (5 : ℝ) ^ (6 : Nat) * (sB + X) ^ (3 : Nat) := by
                nlinarith [hsB_nonneg, hX_nonneg]
          _ = (5 : ℝ) ^ (6 : Nat) * sNorm (m + 1) lam ^ (3 : Nat) := by
                have hs :
                    sB + X = sNorm (m + 1) lam := by
                  simpa [sB, B, X, x] using (sNorm_peel_last m lam).symm
                rw [hs]
  have habs :
      (fun y => |Cn3Torus.W mu y| ^ (6 : Nat))
        = (fun y => (Cn3Torus.W mu y) ^ (6 : Nat)) := by
    funext y
    simpa using (abs_pow_even (Cn3Torus.W mu y) 3)
  rw [habs]
  have hmoment_mu :
      momentX n (matrixOfEdge n mu) 6
        ≤ (5 : ℝ) ^ (6 : Nat) * sNorm n (matrixOfEdge n mu) ^ (3 : Nat) := by
    exact hmoment n (matrixOfEdge n mu)
  rw [momentX_eq_avgOver_W_pow, edgeLam_matrixOfEdge, sNorm_matrixOfEdge_eq] at hmoment_mu
  norm_num at hmoment_mu ⊢
  exact hmoment_mu

private lemma momentX_eight_peel_last_raw_prehc8 (n : ℕ) (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    momentX (n + 1) lam 8
      = avgSigns n (fun σ =>
          innerX n (minorLamLast lam) σ ^ (8 : Nat)
            + 28 * innerX n (minorLamLast lam) σ ^ (6 : Nat)
                * linearX n (lastColLam lam) σ ^ (2 : Nat)
            + 70 * innerX n (minorLamLast lam) σ ^ (4 : Nat)
                * linearX n (lastColLam lam) σ ^ (4 : Nat)
            + 28 * innerX n (minorLamLast lam) σ ^ (2 : Nat)
                * linearX n (lastColLam lam) σ ^ (6 : Nat)
            + linearX n (lastColLam lam) σ ^ (8 : Nat)) := by
  let B : Fin n → Fin n → ℝ := minorLamLast lam
  let x : Fin n → ℝ := lastColLam lam
  have hsplit :
      (∑ τ : Fin (n + 1) → Fin 2, (innerX (n + 1) lam τ) ^ (8 : Nat))
        =
      ∑ σ : Fin n → Fin 2, ∑ b : Fin 2,
        (innerX (n + 1) lam (Fin.snoc (α := fun _ => Fin 2) σ b)) ^ (8 : Nat) := by
    simpa using
      (sum_signVec_split_last n (fun τ : Fin (n + 1) → Fin 2 => (innerX (n + 1) lam τ) ^ (8 : Nat)))
  unfold momentX avgSigns
  rw [hsplit]
  calc
    (↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹
        * ∑ σ : Fin n → Fin 2, ∑ b : Fin 2,
            (innerX (n + 1) lam (Fin.snoc (α := fun _ => Fin 2) σ b)) ^ (8 : Nat)
      =
    (↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹
        * ∑ σ : Fin n → Fin 2, ∑ b : Fin 2,
            (innerX n B σ + (signOf b : ℝ) * linearX n x σ) ^ (8 : Nat) := by
              refine congrArg ((↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹ * ·) ?_
              refine Finset.sum_congr rfl ?_
              intro σ hσ
              refine Finset.sum_congr rfl ?_
              intro b hb
              rw [innerX_snoc_last]
    _ =
      (↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹
        * ∑ σ : Fin n → Fin 2,
            2 * (innerX n B σ ^ (8 : Nat)
              + 28 * innerX n B σ ^ (6 : Nat) * linearX n x σ ^ (2 : Nat)
              + 70 * innerX n B σ ^ (4 : Nat) * linearX n x σ ^ (4 : Nat)
              + 28 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (6 : Nat)
              + linearX n x σ ^ (8 : Nat)) := by
                refine congrArg ((↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹ * ·) ?_
                refine Finset.sum_congr rfl ?_
                intro σ hσ
                rw [sum_eighth_over_last_sign]
    _ =
      (↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹
        * (2 * ∑ σ : Fin n → Fin 2,
            (innerX n B σ ^ (8 : Nat)
              + 28 * innerX n B σ ^ (6 : Nat) * linearX n x σ ^ (2 : Nat)
              + 70 * innerX n B σ ^ (4 : Nat) * linearX n x σ ^ (4 : Nat)
              + 28 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (6 : Nat)
              + linearX n x σ ^ (8 : Nat))) := by
                congr 1
                rw [Finset.mul_sum]
    _ =
      ((↑(2 ^ (n + 1) : ℕ) : ℝ)⁻¹ * 2)
        * ∑ σ : Fin n → Fin 2,
            (innerX n B σ ^ (8 : Nat)
              + 28 * innerX n B σ ^ (6 : Nat) * linearX n x σ ^ (2 : Nat)
              + 70 * innerX n B σ ^ (4 : Nat) * linearX n x σ ^ (4 : Nat)
              + 28 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (6 : Nat)
              + linearX n x σ ^ (8 : Nat)) := by
                ring
    _ =
      (↑(2 ^ n : ℕ) : ℝ)⁻¹
        * ∑ σ : Fin n → Fin 2,
            (innerX n B σ ^ (8 : Nat)
              + 28 * innerX n B σ ^ (6 : Nat) * linearX n x σ ^ (2 : Nat)
              + 70 * innerX n B σ ^ (4 : Nat) * linearX n x σ ^ (4 : Nat)
              + 28 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (6 : Nat)
              + linearX n x σ ^ (8 : Nat)) := by
                have hpow : (↑(2 ^ (n + 1) : ℕ) : ℝ) = (↑(2 ^ n : ℕ) : ℝ) * 2 := by
                  norm_num [pow_succ]
                rw [hpow]
                have htwo : ((↑(2 ^ n : ℕ) : ℝ) * 2) ≠ 0 := by positivity
                field_simp [htwo]
                ring
    _ =
      avgSigns n (fun σ =>
        innerX n B σ ^ (8 : Nat)
          + 28 * innerX n B σ ^ (6 : Nat) * linearX n x σ ^ (2 : Nat)
          + 70 * innerX n B σ ^ (4 : Nat) * linearX n x σ ^ (4 : Nat)
          + 28 * innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (6 : Nat)
          + linearX n x σ ^ (8 : Nat)) := by
            rfl

private lemma momentX_eight_peel_last_prehc8 (n : ℕ) (lam : Fin (n + 1) → Fin (n + 1) → ℝ) :
    momentX (n + 1) lam 8
      = momentX n (minorLamLast lam) 8
          + 28 * avgSigns n
              (fun σ =>
                innerX n (minorLamLast lam) σ ^ (6 : Nat)
                  * linearX n (lastColLam lam) σ ^ (2 : Nat))
          + 70 * avgSigns n
              (fun σ =>
                innerX n (minorLamLast lam) σ ^ (4 : Nat)
                  * linearX n (lastColLam lam) σ ^ (4 : Nat))
          + 28 * avgSigns n
              (fun σ =>
                innerX n (minorLamLast lam) σ ^ (2 : Nat)
                  * linearX n (lastColLam lam) σ ^ (6 : Nat))
          + avgSigns n (fun σ => linearX n (lastColLam lam) σ ^ (8 : Nat)) := by
  have hfun :
      (fun σ =>
        innerX n (minorLamLast lam) σ ^ (8 : Nat)
          + 28 * innerX n (minorLamLast lam) σ ^ (6 : Nat)
              * linearX n (lastColLam lam) σ ^ (2 : Nat)
          + 70 * innerX n (minorLamLast lam) σ ^ (4 : Nat)
              * linearX n (lastColLam lam) σ ^ (4 : Nat)
          + 28 * innerX n (minorLamLast lam) σ ^ (2 : Nat)
              * linearX n (lastColLam lam) σ ^ (6 : Nat)
          + linearX n (lastColLam lam) σ ^ (8 : Nat))
        =
      (fun σ =>
        innerX n (minorLamLast lam) σ ^ (8 : Nat)
          + (28 * innerX n (minorLamLast lam) σ ^ (6 : Nat)
              * linearX n (lastColLam lam) σ ^ (2 : Nat)
            + (70 * innerX n (minorLamLast lam) σ ^ (4 : Nat)
                * linearX n (lastColLam lam) σ ^ (4 : Nat)
              + (28 * innerX n (minorLamLast lam) σ ^ (2 : Nat)
                  * linearX n (lastColLam lam) σ ^ (6 : Nat)
                + linearX n (lastColLam lam) σ ^ (8 : Nat))))) := by
    funext σ
    ring
  have hmul1 :
      avgSigns n
          (fun σ =>
            28 * innerX n (minorLamLast lam) σ ^ (6 : Nat)
              * linearX n (lastColLam lam) σ ^ (2 : Nat))
        =
      28 * avgSigns n
          (fun σ =>
            innerX n (minorLamLast lam) σ ^ (6 : Nat)
              * linearX n (lastColLam lam) σ ^ (2 : Nat)) := by
    have hpoint :
        (fun σ =>
          28 * innerX n (minorLamLast lam) σ ^ (6 : Nat)
            * linearX n (lastColLam lam) σ ^ (2 : Nat))
          =
        (fun σ =>
          28 * (innerX n (minorLamLast lam) σ ^ (6 : Nat)
            * linearX n (lastColLam lam) σ ^ (2 : Nat))) := by
      funext σ
      ring
    rw [hpoint, avgSigns_mul_const_left_prehc6]
  have hmul2 :
      avgSigns n
          (fun σ =>
            70 * innerX n (minorLamLast lam) σ ^ (4 : Nat)
              * linearX n (lastColLam lam) σ ^ (4 : Nat))
        =
      70 * avgSigns n
          (fun σ =>
            innerX n (minorLamLast lam) σ ^ (4 : Nat)
              * linearX n (lastColLam lam) σ ^ (4 : Nat)) := by
    have hpoint :
        (fun σ =>
          70 * innerX n (minorLamLast lam) σ ^ (4 : Nat)
            * linearX n (lastColLam lam) σ ^ (4 : Nat))
          =
        (fun σ =>
          70 * (innerX n (minorLamLast lam) σ ^ (4 : Nat)
            * linearX n (lastColLam lam) σ ^ (4 : Nat))) := by
      funext σ
      ring
    rw [hpoint, avgSigns_mul_const_left_prehc6]
  have hmul3 :
      avgSigns n
          (fun σ =>
            28 * innerX n (minorLamLast lam) σ ^ (2 : Nat)
              * linearX n (lastColLam lam) σ ^ (6 : Nat))
        =
      28 * avgSigns n
          (fun σ =>
            innerX n (minorLamLast lam) σ ^ (2 : Nat)
              * linearX n (lastColLam lam) σ ^ (6 : Nat)) := by
    have hpoint :
        (fun σ =>
          28 * innerX n (minorLamLast lam) σ ^ (2 : Nat)
            * linearX n (lastColLam lam) σ ^ (6 : Nat))
          =
        (fun σ =>
          28 * (innerX n (minorLamLast lam) σ ^ (2 : Nat)
            * linearX n (lastColLam lam) σ ^ (6 : Nat))) := by
      funext σ
      ring
    rw [hpoint, avgSigns_mul_const_left_prehc6]
  rw [momentX_eight_peel_last_raw_prehc8, hfun, avgSigns_add_aux, avgSigns_add_aux, avgSigns_add_aux,
    avgSigns_add_aux, hmul1, hmul2, hmul3]
  simp [momentX, avgSigns]
  ring

set_option maxHeartbeats 1600000

/-- A fixed explicit `L^8` bound for degree-2 Rademacher chaos. This is used
to derive the dimension-free seventh moment by Cauchy from the proved sixth
moment. -/
private theorem fact_fixedDegreeHC_degree2_W_eighth (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (8 : Nat))
      ≤ (280000 : ℝ) * Cn3Torus.sqNormEdge n mu ^ (4 : Nat) := by
  let K : ℝ := 280000
  have hmoment :
      ∀ m : ℕ, ∀ lam : Fin m → Fin m → ℝ,
        momentX m lam 8 ≤ K * sNorm m lam ^ (4 : Nat) := by
    intro m
    induction m with
    | zero =>
        intro lam
        simp [momentX, avgSigns, innerX, sNorm, K]
    | succ m ih =>
        intro lam
        let B : Fin m → Fin m → ℝ := minorLamLast lam
        let x : Fin m → ℝ := lastColLam lam
        let sB : ℝ := sNorm m B
        let X : ℝ := ∑ i : Fin m, x i ^ (2 : Nat)
        let mixed62 : ℝ :=
          avgSigns m (fun σ => innerX m B σ ^ (6 : Nat) * linearX m x σ ^ (2 : Nat))
        let mixed44 : ℝ :=
          avgSigns m (fun σ => innerX m B σ ^ (4 : Nat) * linearX m x σ ^ (4 : Nat))
        let mixed26 : ℝ :=
          avgSigns m (fun σ => innerX m B σ ^ (2 : Nat) * linearX m x σ ^ (6 : Nat))
        let A8 : ℝ := avgSigns m (fun σ => innerX m B σ ^ (8 : Nat))
        let X8 : ℝ := avgSigns m (fun σ => linearX m x σ ^ (8 : Nat))
        have hsB_nonneg : 0 ≤ sB := by
          dsimp [sB, B, sNorm]
          positivity
        have hX_nonneg : 0 ≤ X := by
          dsimp [X, x]
          exact Finset.sum_nonneg (fun _ _ => by positivity)
        have hμ8B :
            momentX m B 8 ≤ K * sB ^ (4 : Nat) := by
          simpa [B, sB] using ih B
        have hμ8B_avg : A8 ≤ K * sB ^ (4 : Nat) := by
          simpa [A8, momentX, avgSigns] using hμ8B
        have hlin8_le : X8 ≤ 105 * X ^ (4 : Nat) := by
          simpa [X8, x, X] using avgSigns_linearX_eight_le_prehc8 m x
        have hmixed62_nonneg : 0 ≤ mixed62 := by
          dsimp [mixed62]
          unfold avgSigns
          positivity
        have hmixed44_nonneg : 0 ≤ mixed44 := by
          dsimp [mixed44]
          unfold avgSigns
          positivity
        have hmixed26_nonneg : 0 ≤ mixed26 := by
          dsimp [mixed26]
          unfold avgSigns
          positivity
        have hA8_nonneg : 0 ≤ A8 := by
          dsimp [A8]
          unfold avgSigns
          positivity
        have hX8_nonneg : 0 ≤ X8 := by
          dsimp [X8]
          unfold avgSigns
          positivity
        have hmixed44_sq :
            mixed44 ^ (2 : Nat) ≤ A8 * X8 := by
          have hmain :=
            avgSigns_mul_sq_le_avgSigns_sq_mul_avgSigns_sq m
              (fun σ => linearX m x σ ^ (4 : Nat))
              (fun σ => innerX m B σ ^ (4 : Nat))
          have hX8_eq :
              avgSigns m (fun σ => (linearX m x σ ^ (4 : Nat)) ^ (2 : Nat)) = X8 := by
            dsimp [X8]
            refine avgSigns_congr m ?_
            intro σ
            rw [← pow_mul]
          have hA8_eq :
              avgSigns m (fun σ => (innerX m B σ ^ (4 : Nat)) ^ (2 : Nat)) = A8 := by
            dsimp [A8]
            refine avgSigns_congr m ?_
            intro σ
            rw [← pow_mul]
          calc
            mixed44 ^ (2 : Nat)
                = (avgSigns m (fun σ => linearX m x σ ^ (4 : Nat) * innerX m B σ ^ (4 : Nat))) ^ (2 : Nat) := by
                    congr 1
                    refine avgSigns_congr m ?_
                    intro σ
                    ring
            _ ≤ avgSigns m (fun σ => (linearX m x σ ^ (4 : Nat)) ^ (2 : Nat))
                  * avgSigns m (fun σ => (innerX m B σ ^ (4 : Nat)) ^ (2 : Nat)) := hmain
            _ = X8 * A8 := by rw [hX8_eq, hA8_eq]
            _ = A8 * X8 := by ring
        have hmixed62_sq :
            mixed62 ^ (2 : Nat) ≤ A8 * mixed44 := by
          have hmain :=
            avgSigns_mul_sq_le_avgSigns_sq_mul_avgSigns_sq m
              (fun σ => innerX m B σ ^ (2 : Nat) * linearX m x σ ^ (2 : Nat))
              (fun σ => innerX m B σ ^ (4 : Nat))
          have hmid_eq :
              avgSigns m
                  (fun σ =>
                    (innerX m B σ ^ (2 : Nat) * linearX m x σ ^ (2 : Nat)) ^ (2 : Nat))
                = mixed44 := by
            dsimp [mixed44]
            refine avgSigns_congr m ?_
            intro σ
            ring_nf
          have hA8_eq :
              avgSigns m (fun σ => (innerX m B σ ^ (4 : Nat)) ^ (2 : Nat)) = A8 := by
            dsimp [A8]
            refine avgSigns_congr m ?_
            intro σ
            rw [← pow_mul]
          calc
            mixed62 ^ (2 : Nat)
                = (avgSigns m
                    (fun σ =>
                      (innerX m B σ ^ (2 : Nat) * linearX m x σ ^ (2 : Nat))
                        * innerX m B σ ^ (4 : Nat))) ^ (2 : Nat) := by
                    congr 1
                    refine avgSigns_congr m ?_
                    intro σ
                    ring
            _ ≤ avgSigns m
                    (fun σ =>
                      (innerX m B σ ^ (2 : Nat) * linearX m x σ ^ (2 : Nat)) ^ (2 : Nat))
                  * avgSigns m (fun σ => (innerX m B σ ^ (4 : Nat)) ^ (2 : Nat)) := hmain
            _ = mixed44 * A8 := by rw [hmid_eq, hA8_eq]
            _ = A8 * mixed44 := by ring
        have hmixed26_sq :
            mixed26 ^ (2 : Nat) ≤ mixed44 * X8 := by
          have hmain :=
            avgSigns_mul_sq_le_avgSigns_sq_mul_avgSigns_sq m
              (fun σ => linearX m x σ ^ (4 : Nat))
              (fun σ => innerX m B σ ^ (2 : Nat) * linearX m x σ ^ (2 : Nat))
          have hX8_eq :
              avgSigns m (fun σ => (linearX m x σ ^ (4 : Nat)) ^ (2 : Nat)) = X8 := by
            dsimp [X8]
            refine avgSigns_congr m ?_
            intro σ
            rw [← pow_mul]
          have hmid_eq :
              avgSigns m
                  (fun σ =>
                    (innerX m B σ ^ (2 : Nat) * linearX m x σ ^ (2 : Nat)) ^ (2 : Nat))
                = mixed44 := by
            dsimp [mixed44]
            refine avgSigns_congr m ?_
            intro σ
            ring_nf
          calc
            mixed26 ^ (2 : Nat)
                = (avgSigns m
                    (fun σ =>
                      linearX m x σ ^ (4 : Nat)
                        * (innerX m B σ ^ (2 : Nat) * linearX m x σ ^ (2 : Nat)))) ^ (2 : Nat) := by
                    congr 1
                    refine avgSigns_congr m ?_
                    intro σ
                    ring
            _ ≤ avgSigns m (fun σ => (linearX m x σ ^ (4 : Nat)) ^ (2 : Nat))
                  * avgSigns m
                      (fun σ =>
                        (innerX m B σ ^ (2 : Nat) * linearX m x σ ^ (2 : Nat)) ^ (2 : Nat)) := hmain
            _ = X8 * mixed44 := by rw [hX8_eq, hmid_eq]
            _ = mixed44 * X8 := by ring
        have hmixed44_sq' :
            mixed44 ^ (2 : Nat) ≤ (K * sB ^ (4 : Nat)) * (105 * X ^ (4 : Nat)) := by
          calc
            mixed44 ^ (2 : Nat) ≤ A8 * X8 := hmixed44_sq
            _ ≤ (K * sB ^ (4 : Nat)) * X8 := by
                  gcongr
            _ ≤ (K * sB ^ (4 : Nat)) * (105 * X ^ (4 : Nat)) := by
                  gcongr
        have hmixed44_le :
            mixed44 ≤ 24000 * sB ^ (2 : Nat) * X ^ (2 : Nat) := by
          let R : ℝ := 24000 * sB ^ (2 : Nat) * X ^ (2 : Nat)
          have hR_nonneg : 0 ≤ R := by positivity
          have hsq : mixed44 ^ (2 : Nat) ≤ R ^ (2 : Nat) := by
            calc
              mixed44 ^ (2 : Nat) ≤ (K * sB ^ (4 : Nat)) * (105 * X ^ (4 : Nat)) := hmixed44_sq'
              _ = (K * 105) * (sB ^ (4 : Nat) * X ^ (4 : Nat)) := by ring
              _ ≤ (24000 : ℝ) ^ (2 : Nat) * (sB ^ (4 : Nat) * X ^ (4 : Nat)) := by
                    have hnum : K * 105 ≤ (24000 : ℝ) ^ (2 : Nat) := by
                      norm_num [K]
                    exact mul_le_mul_of_nonneg_right hnum (by positivity)
              _ = R ^ (2 : Nat) := by
                    dsimp [R]
                    ring
          exact le_of_not_gt (fun hgt =>
            let hpow_gt := pow_lt_pow_left₀ hgt hR_nonneg (by norm_num : (2 : ℕ) ≠ 0)
            by exact (not_lt_of_ge hsq) hpow_gt)
        have hmixed62_fourth :
            mixed62 ^ (4 : Nat) ≤ A8 ^ (3 : Nat) * X8 := by
          calc
            mixed62 ^ (4 : Nat) = (mixed62 ^ (2 : Nat)) ^ (2 : Nat) := by ring
            _ ≤ (A8 * mixed44) ^ (2 : Nat) := by
                  gcongr
            _ = A8 ^ (2 : Nat) * mixed44 ^ (2 : Nat) := by ring
            _ ≤ A8 ^ (2 : Nat) * (A8 * X8) := by
                  gcongr
            _ = A8 ^ (3 : Nat) * X8 := by ring
        have hmixed62_fourth' :
            mixed62 ^ (4 : Nat) ≤ (K * sB ^ (4 : Nat)) ^ (3 : Nat) * (105 * X ^ (4 : Nat)) := by
          calc
            mixed62 ^ (4 : Nat) ≤ A8 ^ (3 : Nat) * X8 := hmixed62_fourth
            _ ≤ (K * sB ^ (4 : Nat)) ^ (3 : Nat) * X8 := by
                  gcongr
            _ ≤ (K * sB ^ (4 : Nat)) ^ (3 : Nat) * (105 * X ^ (4 : Nat)) := by
                  gcongr
        have hmixed62_le :
            mixed62 ≤ 40000 * sB ^ (3 : Nat) * X := by
          let R : ℝ := 40000 * sB ^ (3 : Nat) * X
          have hR_nonneg : 0 ≤ R := by positivity
          have hpow : mixed62 ^ (4 : Nat) ≤ R ^ (4 : Nat) := by
            calc
              mixed62 ^ (4 : Nat) ≤ (K * sB ^ (4 : Nat)) ^ (3 : Nat) * (105 * X ^ (4 : Nat)) := hmixed62_fourth'
              _ = (K ^ (3 : Nat) * 105) * (sB ^ (12 : Nat) * X ^ (4 : Nat)) := by ring
              _ ≤ (40000 : ℝ) ^ (4 : Nat) * (sB ^ (12 : Nat) * X ^ (4 : Nat)) := by
                    have hnum : K ^ (3 : Nat) * 105 ≤ (40000 : ℝ) ^ (4 : Nat) := by
                      norm_num [K]
                    exact mul_le_mul_of_nonneg_right hnum (by positivity)
              _ = R ^ (4 : Nat) := by
                    dsimp [R]
                    ring
          exact le_of_not_gt (fun hgt =>
            let hpow_gt := pow_lt_pow_left₀ hgt hR_nonneg (by norm_num : (4 : ℕ) ≠ 0)
            by exact (not_lt_of_ge hpow) hpow_gt)
        have hmixed26_fourth :
            mixed26 ^ (4 : Nat) ≤ A8 * X8 ^ (3 : Nat) := by
          calc
            mixed26 ^ (4 : Nat) = (mixed26 ^ (2 : Nat)) ^ (2 : Nat) := by ring
            _ ≤ (mixed44 * X8) ^ (2 : Nat) := by
                  gcongr
            _ = mixed44 ^ (2 : Nat) * X8 ^ (2 : Nat) := by ring
            _ ≤ (A8 * X8) * X8 ^ (2 : Nat) := by
                  gcongr
            _ = A8 * X8 ^ (3 : Nat) := by ring
        have hmixed26_fourth' :
            mixed26 ^ (4 : Nat) ≤ (K * sB ^ (4 : Nat)) * (105 * X ^ (4 : Nat)) ^ (3 : Nat) := by
          calc
            mixed26 ^ (4 : Nat) ≤ A8 * X8 ^ (3 : Nat) := hmixed26_fourth
            _ ≤ (K * sB ^ (4 : Nat)) * X8 ^ (3 : Nat) := by
                  gcongr
            _ ≤ (K * sB ^ (4 : Nat)) * (105 * X ^ (4 : Nat)) ^ (3 : Nat) := by
                  gcongr
        have hmixed26_le :
            mixed26 ≤ 40000 * sB * X ^ (3 : Nat) := by
          let R : ℝ := 40000 * sB * X ^ (3 : Nat)
          have hR_nonneg : 0 ≤ R := by positivity
          have hpow : mixed26 ^ (4 : Nat) ≤ R ^ (4 : Nat) := by
            calc
              mixed26 ^ (4 : Nat) ≤ (K * sB ^ (4 : Nat)) * (105 * X ^ (4 : Nat)) ^ (3 : Nat) := hmixed26_fourth'
              _ = (K * 105 ^ (3 : Nat)) * (sB ^ (4 : Nat) * X ^ (12 : Nat)) := by ring
              _ ≤ (40000 : ℝ) ^ (4 : Nat) * (sB ^ (4 : Nat) * X ^ (12 : Nat)) := by
                    have hnum : K * 105 ^ (3 : Nat) ≤ (40000 : ℝ) ^ (4 : Nat) := by
                      norm_num [K]
                    exact mul_le_mul_of_nonneg_right hnum (by positivity)
              _ = R ^ (4 : Nat) := by
                    dsimp [R]
                    ring
          exact le_of_not_gt (fun hgt =>
            let hpow_gt := pow_lt_pow_left₀ hgt hR_nonneg (by norm_num : (4 : ℕ) ≠ 0)
            by exact (not_lt_of_ge hpow) hpow_gt)
        calc
          momentX (m + 1) lam 8
              = momentX m B 8 + 28 * mixed62 + 70 * mixed44 + 28 * mixed26
                  + avgSigns m (fun σ => linearX m x σ ^ (8 : Nat)) := by
                    simpa [B, x, mixed62, mixed44, mixed26] using momentX_eight_peel_last_prehc8 m lam
          _ ≤ K * sB ^ (4 : Nat)
                + 28 * (40000 * sB ^ (3 : Nat) * X)
                + 70 * (24000 * sB ^ (2 : Nat) * X ^ (2 : Nat))
                + 28 * (40000 * sB * X ^ (3 : Nat))
                + 105 * X ^ (4 : Nat) := by
                  nlinarith [hμ8B, hmixed62_le, hmixed44_le, hmixed26_le, hlin8_le]
          _ ≤ K * (sB + X) ^ (4 : Nat) := by
                dsimp [K]
                nlinarith [hsB_nonneg, hX_nonneg]
          _ = K * sNorm (m + 1) lam ^ (4 : Nat) := by
                have hs : sB + X = sNorm (m + 1) lam := by
                  simpa [sB, B, X, x] using (sNorm_peel_last m lam).symm
                rw [hs]
  have habs :
      (fun y => |Cn3Torus.W mu y| ^ (8 : Nat))
        = (fun y => (Cn3Torus.W mu y) ^ (8 : Nat)) := by
    funext y
    simpa using (abs_pow_even (Cn3Torus.W mu y) 4)
  rw [habs]
  have hmoment_mu :
      momentX n (matrixOfEdge n mu) 8
        ≤ K * sNorm n (matrixOfEdge n mu) ^ (4 : Nat) := by
    exact hmoment n (matrixOfEdge n mu)
  rw [momentX_eq_avgOver_W_pow, edgeLam_matrixOfEdge, sNorm_matrixOfEdge_eq] at hmoment_mu
  norm_num [K] at hmoment_mu ⊢
  exact hmoment_mu

/- A dimension-free seventh-moment consequence from the proved sixth and
eighth moment bounds. -/
theorem fixedDegreeHC_degree2_W_seventh_uniform
    (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (7 : Nat))
      ≤ (6 : ℝ) ^ (7 : Nat) * Cn3Torus.sqNormEdge n mu ^ (7 / 2 : ℝ) := by
  let M7 : ℝ := Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (7 : Nat))
  let M6 : ℝ := Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (6 : Nat))
  let M8 : ℝ := Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (8 : Nat))
  have hM7_nonneg : 0 ≤ M7 := by
    dsimp [M7]
    unfold Cn3Torus.avgOver
    positivity
  have hM8_nonneg : 0 ≤ M8 := by
    dsimp [M8]
    unfold Cn3Torus.avgOver
    positivity
  have hs_nonneg : 0 ≤ Cn3Torus.sqNormEdge n mu := by
    unfold Cn3Torus.sqNormEdge
    positivity
  have hM7_sq : M7 ^ (2 : Nat) ≤ M6 * M8 := by
    dsimp [M7, M6, M8]
    have hmain :=
      avgSigns_mul_sq_le_avgSigns_sq_mul_avgSigns_sq n
        (fun σ => |innerX n (matrixOfEdge n mu) σ| ^ (3 : Nat))
        (fun σ => |innerX n (matrixOfEdge n mu) σ| ^ (4 : Nat))
    have hconv7 :
        avgSigns n
            (fun σ =>
              |innerX n (matrixOfEdge n mu) σ| ^ (3 : Nat)
                * |innerX n (matrixOfEdge n mu) σ| ^ (4 : Nat))
          = avgSigns n (fun σ => |innerX n (matrixOfEdge n mu) σ| ^ (7 : Nat)) := by
      refine avgSigns_congr n ?_
      intro σ
      rw [← pow_add]
    have hconv6 :
        avgSigns n
            (fun σ => (|innerX n (matrixOfEdge n mu) σ| ^ (3 : Nat)) ^ (2 : Nat))
          = avgSigns n (fun σ => |innerX n (matrixOfEdge n mu) σ| ^ (6 : Nat)) := by
      refine avgSigns_congr n ?_
      intro σ
      rw [← pow_mul]
    have hconv8 :
        avgSigns n
            (fun σ => (|innerX n (matrixOfEdge n mu) σ| ^ (4 : Nat)) ^ (2 : Nat))
          = avgSigns n (fun σ => |innerX n (matrixOfEdge n mu) σ| ^ (8 : Nat)) := by
      refine avgSigns_congr n ?_
      intro σ
      rw [← pow_mul]
    rw [hconv7, hconv6, hconv8] at hmain
    rw [avgSigns_abs_innerX_pow_eq_avgOver_abs_W_pow n (matrixOfEdge n mu) 7,
      avgSigns_abs_innerX_pow_eq_avgOver_abs_W_pow n (matrixOfEdge n mu) 6,
      avgSigns_abs_innerX_pow_eq_avgOver_abs_W_pow n (matrixOfEdge n mu) 8] at hmain
    simpa [M7, M6, M8, edgeLam_matrixOfEdge] using hmain
  have hM6_bound : M6 ≤ (5 : ℝ) ^ (6 : Nat) * Cn3Torus.sqNormEdge n mu ^ (3 : Nat) := by
    dsimp [M6]
    exact fixedDegreeHC_degree2_W_sixth n mu
  have hM8_bound : M8 ≤ (280000 : ℝ) * Cn3Torus.sqNormEdge n mu ^ (4 : Nat) := by
    dsimp [M8]
    exact fact_fixedDegreeHC_degree2_W_eighth n mu
  have hsq_bound :
      M7 ^ (2 : Nat)
        ≤ ((6 : ℝ) ^ (7 : Nat) * Cn3Torus.sqNormEdge n mu ^ (7 / 2 : ℝ)) ^ (2 : Nat) := by
    calc
      M7 ^ (2 : Nat) ≤ M6 * M8 := hM7_sq
      _ ≤ ((5 : ℝ) ^ (6 : Nat) * Cn3Torus.sqNormEdge n mu ^ (3 : Nat))
            * ((280000 : ℝ) * Cn3Torus.sqNormEdge n mu ^ (4 : Nat)) := by
              exact mul_le_mul hM6_bound hM8_bound hM8_nonneg
                (by positivity : 0 ≤ (5 : ℝ) ^ (6 : Nat) * Cn3Torus.sqNormEdge n mu ^ (3 : Nat))
      _ = (((5 : ℝ) ^ (6 : Nat)) * (280000 : ℝ))
            * (Cn3Torus.sqNormEdge n mu ^ (3 : Nat) * Cn3Torus.sqNormEdge n mu ^ (4 : Nat)) := by
              ring
      _ = (((5 : ℝ) ^ (6 : Nat)) * (280000 : ℝ))
            * Cn3Torus.sqNormEdge n mu ^ (7 : Nat) := by
              have hpow :
                  Cn3Torus.sqNormEdge n mu ^ (3 : Nat) * Cn3Torus.sqNormEdge n mu ^ (4 : Nat)
                    = Cn3Torus.sqNormEdge n mu ^ (7 : Nat) := by
                rw [← pow_add]
              rw [hpow]
      _ ≤ ((6 : ℝ) ^ (7 : Nat)) ^ (2 : Nat) * Cn3Torus.sqNormEdge n mu ^ (7 : Nat) := by
            have hnum : (((5 : ℝ) ^ (6 : Nat)) * (280000 : ℝ)) ≤ ((6 : ℝ) ^ (7 : Nat)) ^ (2 : Nat) := by
              norm_num
            exact mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = ((6 : ℝ) ^ (7 : Nat) * Cn3Torus.sqNormEdge n mu ^ (7 / 2 : ℝ)) ^ (2 : Nat) := by
            have hs_pow :
                (Cn3Torus.sqNormEdge n mu ^ (7 / 2 : ℝ)) ^ (2 : Nat)
                  = Cn3Torus.sqNormEdge n mu ^ (7 : Nat) := by
              rw [pow_two, ← Real.rpow_add_of_nonneg hs_nonneg (by positivity) (by positivity)]
              norm_num
            rw [mul_pow, hs_pow]
  have htarget_nonneg :
      0 ≤ (6 : ℝ) ^ (7 : Nat) * Cn3Torus.sqNormEdge n mu ^ (7 / 2 : ℝ) := by
    positivity
  have habs :
      |M7| ≤ |(6 : ℝ) ^ (7 : Nat) * Cn3Torus.sqNormEdge n mu ^ (7 / 2 : ℝ)| := by
    exact (sq_le_sq).1 hsq_bound
  have hle :
      M7 ≤ (6 : ℝ) ^ (7 : Nat) * Cn3Torus.sqNormEdge n mu ^ (7 / 2 : ℝ) := by
    simpa [abs_of_nonneg hM7_nonneg, abs_of_nonneg htarget_nonneg] using habs
  simpa [M7] using hle

set_option maxHeartbeats 200000

namespace Cn3Torus

private lemma psi_norm_sq_le_half_one_add_rowCosProd (n : ℕ) (hn2 : 2 ≤ n) (i : Fin n) (lam : Edge n → ℝ) :
    ‖psi n lam‖ ^ 2 ≤ (1 + rowCosProd n i lam) / 2 := by
  have hbound := universal_magnitude_bound_full n hn2 (matrixOfEdge n lam) i
  have hbound' :
      ‖psi n lam‖ ^ 2 ≤ (1 / 2 : ℝ) + (1 / 2 : ℝ) * rowCosProd n i lam := by
    simpa [psi_matrixOfEdge_eq n lam, matrix_rowCosProd_eq_rowCosProd n i lam]
      using hbound
  have hrewrite : (1 / 2 : ℝ) + (1 / 2 : ℝ) * rowCosProd n i lam = (1 + rowCosProd n i lam) / 2 := by
    ring
  exact hbound'.trans_eq hrewrite

private theorem gap_torus_input (n : ℕ) (hn : 2 ≤ n) :
    ∀ lam ∈ RdeltaSet n, ‖psi n lam‖ ≤ Real.cos delta := by
  intro lam hlamR
  have hR : lam ∈ torusBox n ∧ lam ∉ NdeltaSet n := by
    simpa [RdeltaSet] using hlamR
  have htorus : lam ∈ torusBox n := hR.1
  have hnotN : lam ∉ NdeltaSet n := hR.2
  have hnotCore : lam ∉ NdeltaCoreSet n := by
    intro hcore
    exact hnotN (by simpa [NdeltaSet] using And.intro htorus hcore)
  have hrow_exists : ∃ i : Fin n, rowCosProd n i lam ≤ Real.cos (2 * delta) := by
    by_cases hcloseAll : ∀ e : Edge n, ∃ q : Fin 4, |lam e - quarterReal q| < delta
    · classical
      choose b hb using hcloseAll
      have hb_not_code : b ∉ lambdaCodes n := by
        intro hbcode
        have hshift : lambdaReal b ∈ lambdaShifts n := by
          unfold lambdaShifts
          exact Finset.mem_image.mpr ⟨b, hbcode, rfl⟩
        have htrans : lam ∈ translateSet (lambdaReal b) (localBox n) := by
          show lam - lambdaReal b ∈ localBox n
          intro e he
          have hclosee : |lam e - quarterReal (b e)| < delta := hb e
          have hcoord :
              -delta < (lam - lambdaReal b) e ∧
                (lam - lambdaReal b) e < delta := by
            simpa [Pi.sub_apply, lambdaReal] using (abs_lt.mp hclosee)
          exact ⟨le_of_lt hcoord.1, le_of_lt hcoord.2⟩
        have hcore : lam ∈ NdeltaCoreSet n := by
          refine Set.mem_iUnion.mpr ?_
          refine ⟨lambdaReal b, Set.mem_iUnion.mpr ?_⟩
          exact ⟨hshift, htrans⟩
        exact hnotCore hcore
      have hnot_even : ¬ rowParityEven b := by
        intro hrow
        apply hb_not_code
        unfold lambdaCodes
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, hrow⟩
      have hodd_exists : ∃ i : Fin n, Odd (rowParitySum b i) := by
        have hnotall : ¬ ∀ i : Fin n, Even (rowParitySum b i) := by
          simpa [rowParityEven] using hnot_even
        push_neg at hnotall
        rcases hnotall with ⟨i, hi⟩
        exact ⟨i, Nat.not_even_iff_odd.mp hi⟩
      rcases hodd_exists with ⟨i, hodd⟩
      have hnonpos : rowCosProd n i lam ≤ 0 :=
        rowCosProd_nonpos_of_odd_row_and_close n lam b i hodd hb
      have hcos_nonneg : 0 ≤ Real.cos (2 * delta) := by
        have hlow : -(Real.pi / 2) ≤ 2 * delta := by
          have hpi2 : 0 < Real.pi / 2 := by positivity [Real.pi_pos]
          linarith [delta_pos, hpi2]
        have hupp : 2 * delta ≤ Real.pi / 2 := by
          linarith [delta_lt_pi_div_four]
        exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le hlow hupp
      exact ⟨i, hnonpos.trans hcos_nonneg⟩
    · have hfar_edge : ∃ e : Edge n, ∀ q : Fin 4, delta ≤ |lam e - quarterReal q| := by
        push_neg at hcloseAll
        exact hcloseAll
      rcases hfar_edge with ⟨e, hfar_e⟩
      let i : Fin n := e.1.1
      have he_inc : e ∈ edgesIncident n i := by
        simpa [i] using edge_mem_edgesIncident_left e
      let j0 : {k : Fin n // k ≠ i} := offdiagOfIncident i e he_inc
      have hedge : edgeFromOffdiag i j0 = e := edgeFromOffdiag_offdiagOfIncident i e he_inc
      have hx : lam e ∈ Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4) := by
        exact htorus e (by simp)
      have hfac0 : |Real.cos (2 * lam e)| ≤ Real.cos (2 * delta) :=
        abs_cos_two_mul_le_cos_two_delta_of_mem_torusInterval hx hfar_e
      have hfac : |Real.cos (2 * lam (edgeFromOffdiag i j0))| ≤ Real.cos (2 * delta) := by
        simpa [hedge] using hfac0
      have hrow : rowCosProd n i lam ≤ Real.cos (2 * delta) := by
        exact (le_abs_self (rowCosProd n i lam)).trans
          ((abs_rowCosProd_le_abs_factor n i lam j0).trans hfac)
      exact ⟨i, hrow⟩
  rcases hrow_exists with ⟨i, hrow⟩
  have hsq1 : ‖psi n lam‖ ^ 2 ≤ (1 + rowCosProd n i lam) / 2 :=
    psi_norm_sq_le_half_one_add_rowCosProd n hn i lam
  have hsq2 : (1 + rowCosProd n i lam) / 2 ≤ (Real.cos delta) ^ 2 := by
    have hlin : (1 + rowCosProd n i lam) / 2 ≤ (1 + Real.cos (2 * delta)) / 2 := by
      nlinarith [hrow]
    have hcos : (1 + Real.cos (2 * delta)) / 2 = (Real.cos delta) ^ 2 := by
      have h := Real.cos_two_mul delta
      nlinarith [h]
    exact hlin.trans (le_of_eq hcos)
  have hsq : ‖psi n lam‖ ^ 2 ≤ (Real.cos delta) ^ 2 := hsq1.trans hsq2
  have hcos_nonneg : 0 ≤ Real.cos delta := by
    have hpi2 : 0 < Real.pi / 2 := by positivity [Real.pi_pos]
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [delta_pos, hpi2]) delta_lt_pi_div_two.le
  have hnorm_nonneg : 0 ≤ ‖psi n lam‖ := norm_nonneg _
  nlinarith [hsq, hcos_nonneg, hnorm_nonneg]

private theorem gap_edgeResidualTorusRegion_input (n : ℕ) (hn : 2 ≤ n)
    {deltaBox : ℝ} (hdelta_pos : 0 < deltaBox) (hdelta_lt : deltaBox < Real.pi / 4) :
    ∀ lam ∈ edgeResidualTorusRegion n deltaBox, ‖psi n lam‖ ≤ Real.cos deltaBox := by
  intro lam hlamR
  have hR : lam ∈ torusBox n ∧ lam ∉ edgePrimaryBoxUnion n deltaBox := by
    simpa [edgeResidualTorusRegion] using hlamR
  have htorus : lam ∈ torusBox n := hR.1
  have hnotPrimary : lam ∉ edgePrimaryBoxUnion n deltaBox := hR.2
  have hrow_exists : ∃ i : Fin n, rowCosProd n i lam ≤ Real.cos (2 * deltaBox) := by
    by_cases hcloseAll : ∀ e : Edge n, ∃ q : Fin 4, |lam e - quarterReal q| < deltaBox
    · classical
      choose b hb using hcloseAll
      have hb_not_code : b ∉ lambdaCodes n := by
        intro hbcode
        have hshift : lambdaReal b ∈ lambdaShifts n := by
          unfold lambdaShifts
          exact Finset.mem_image.mpr ⟨b, hbcode, rfl⟩
        have htrans : lam ∈ translateSet (lambdaReal b) (edgeBox n deltaBox) := by
          show lam - lambdaReal b ∈ edgeBox n deltaBox
          rw [edgeBox_eq_pi]
          rw [Set.mem_pi]
          intro e he
          have hclosee : |lam e - quarterReal (b e)| < deltaBox := hb e
          have hcoord :
              -deltaBox < (lam - lambdaReal b) e ∧
                (lam - lambdaReal b) e < deltaBox := by
            simpa [Pi.sub_apply, lambdaReal] using (abs_lt.mp hclosee)
          exact ⟨le_of_lt hcoord.1, le_of_lt hcoord.2⟩
        have hprimary : lam ∈ edgePrimaryBoxUnion n deltaBox := by
          refine Set.mem_iUnion.mpr ?_
          refine ⟨lambdaReal b, Set.mem_iUnion.mpr ?_⟩
          exact ⟨hshift, htrans⟩
        exact hnotPrimary hprimary
      have hnot_even : ¬ rowParityEven b := by
        intro hrow
        apply hb_not_code
        unfold lambdaCodes
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ b, hrow⟩
      have hodd_exists : ∃ i : Fin n, Odd (rowParitySum b i) := by
        have hnotall : ¬ ∀ i : Fin n, Even (rowParitySum b i) := by
          simpa [rowParityEven] using hnot_even
        push_neg at hnotall
        rcases hnotall with ⟨i, hi⟩
        exact ⟨i, Nat.not_even_iff_odd.mp hi⟩
      rcases hodd_exists with ⟨i, hodd⟩
      have hnonpos : rowCosProd n i lam ≤ 0 :=
        rowCosProd_nonpos_of_odd_row_and_close_of_lt_pi_div_four
          n lam deltaBox hdelta_pos hdelta_lt b i hodd hb
      exact ⟨i, hnonpos.trans (cos_two_nonneg_of_lt_pi_div_four deltaBox hdelta_pos hdelta_lt)⟩
    · have hfar_edge : ∃ e : Edge n, ∀ q : Fin 4, deltaBox ≤ |lam e - quarterReal q| := by
        push_neg at hcloseAll
        exact hcloseAll
      rcases hfar_edge with ⟨e, hfar_e⟩
      let i : Fin n := e.1.1
      have he_inc : e ∈ edgesIncident n i := by
        simpa [i] using edge_mem_edgesIncident_left e
      let j0 : {k : Fin n // k ≠ i} := offdiagOfIncident i e he_inc
      have hedge : edgeFromOffdiag i j0 = e := edgeFromOffdiag_offdiagOfIncident i e he_inc
      have hx : lam e ∈ Set.Icc (-(Real.pi / 4)) (7 * Real.pi / 4) := by
        exact htorus e (by simp)
      have hfac0 : |Real.cos (2 * lam e)| ≤ Real.cos (2 * deltaBox) :=
        abs_cos_two_mul_le_cos_two_delta_of_mem_torusInterval_of_lt_pi_div_four
          hdelta_pos hdelta_lt hx hfar_e
      have hfac : |Real.cos (2 * lam (edgeFromOffdiag i j0))| ≤ Real.cos (2 * deltaBox) := by
        simpa [hedge] using hfac0
      have hrow : rowCosProd n i lam ≤ Real.cos (2 * deltaBox) := by
        exact (le_abs_self (rowCosProd n i lam)).trans
          ((abs_rowCosProd_le_abs_factor n i lam j0).trans hfac)
      exact ⟨i, hrow⟩
  rcases hrow_exists with ⟨i, hrow⟩
  have hsq1 : ‖psi n lam‖ ^ 2 ≤ (1 + rowCosProd n i lam) / 2 :=
    psi_norm_sq_le_half_one_add_rowCosProd n hn i lam
  have hsq2 : (1 + rowCosProd n i lam) / 2 ≤ (Real.cos deltaBox) ^ 2 := by
    have hlin : (1 + rowCosProd n i lam) / 2 ≤ (1 + Real.cos (2 * deltaBox)) / 2 := by
      nlinarith [hrow]
    have hcos : (1 + Real.cos (2 * deltaBox)) / 2 = (Real.cos deltaBox) ^ 2 := by
      have h := Real.cos_two_mul deltaBox
      nlinarith [h]
    exact hlin.trans (le_of_eq hcos)
  have hsq : ‖psi n lam‖ ^ 2 ≤ (Real.cos deltaBox) ^ 2 := hsq1.trans hsq2
  have hcos_nonneg : 0 ≤ Real.cos deltaBox := by
    have hpi2 : 0 < Real.pi / 2 := by positivity [Real.pi_pos]
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith [hdelta_pos, hpi2])
      (by linarith [hdelta_lt])
  have hnorm_nonneg : 0 ≤ ‖psi n lam‖ := norm_nonneg _
  nlinarith [hsq, hcos_nonneg, hnorm_nonneg]

end Cn3Torus

lemma normalized_edgeResidualTorusRegion_abs_le_cos_pow
    (n t : ℕ) (hn : 2 ≤ n) {deltaBox : ℝ}
    (hdelta_pos : 0 < deltaBox) (hdelta_lt : deltaBox < Real.pi / 4) :
    |(1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ)) *
        ∫ lam in Cn3Torus.edgeResidualTorusRegion n deltaBox,
            Complex.re (Cn3Torus.psi n lam ^ (4 * t))|
      ≤ (Real.cos deltaBox) ^ (4 * t) := by
  let vol : ℝ := ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ)
  have hvol_pos : 0 < vol := by
    dsimp [vol]
    positivity [Real.pi_pos]
  have hgap := Cn3Torus.gap_edgeResidualTorusRegion_input n hn hdelta_pos hdelta_lt
  have habs :
      |∫ lam in Cn3Torus.edgeResidualTorusRegion n deltaBox,
          Complex.re (Cn3Torus.psi n lam ^ (4 * t))|
        ≤ ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ) * (Real.cos deltaBox) ^ (4 * t) := by
    have hcos_nonneg : 0 ≤ Real.cos deltaBox := by
      have hpi2 : 0 < Real.pi / 2 := by positivity [Real.pi_pos]
      exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [hdelta_pos, hpi2])
        (by linarith [hdelta_lt])
    refine Cn3Torus.hRabs_from_pointwise_bound n t
      (Cn3Torus.edgeResidualTorusRegion n deltaBox) ((Real.cos deltaBox) ^ (4 * t)) ?_
      (Cn3Torus.measurableSet_edgeResidualTorusRegion n deltaBox) ?_ ?_
    · exact pow_nonneg hcos_nonneg _
    · intro lam hlam
      exact hlam.1
    · intro lam hlam
      have hnorm_nonneg : 0 ≤ ‖Cn3Torus.psi n lam‖ := by positivity
      have hpow_le :
          ‖Cn3Torus.psi n lam‖ ^ (4 * t) ≤ (Real.cos deltaBox) ^ (4 * t) := by
        exact pow_le_pow_left₀ hnorm_nonneg (hgap lam hlam) (4 * t)
      have hnormpow : ‖Cn3Torus.psi n lam ^ (4 * t)‖ = ‖Cn3Torus.psi n lam‖ ^ (4 * t) := by
        simpa using (Complex.norm_pow (Cn3Torus.psi n lam) (4 * t))
      calc
        |Complex.re (Cn3Torus.psi n lam ^ (4 * t))| ≤ ‖Cn3Torus.psi n lam ^ (4 * t)‖ := Complex.abs_re_le_norm _
        _ = ‖Cn3Torus.psi n lam‖ ^ (4 * t) := hnormpow
        _ ≤ (Real.cos deltaBox) ^ (4 * t) := hpow_le
  calc
    |(1 / vol) *
        ∫ lam in Cn3Torus.edgeResidualTorusRegion n deltaBox,
          Complex.re (Cn3Torus.psi n lam ^ (4 * t))|
      = (1 / vol) *
          |∫ lam in Cn3Torus.edgeResidualTorusRegion n deltaBox,
              Complex.re (Cn3Torus.psi n lam ^ (4 * t))| := by
          rw [abs_mul, abs_of_pos (one_div_pos.mpr hvol_pos)]
    _ ≤ (1 / vol) * (vol * (Real.cos deltaBox) ^ (4 * t)) := by
          exact mul_le_mul_of_nonneg_left habs (by positivity)
    _ = (Real.cos deltaBox) ^ (4 * t) := by
          field_simp [hvol_pos.ne']

/-- The actual primary-secondary torus decomposition from the manuscript, written in
edge coordinates and normalized directly at the normalized-count scale. -/
theorem normalizedCount_primary_secondary_decomposition (n t : ℕ) {delta : ℝ}
    (hdelta_lt : delta < π / 4) :
    normalizedCount n (4 * t)
      = (((Cn3Torus.lambdaShifts n).card : ℝ) / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
          * (∫ mu in edgeBox n delta, Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
        + (1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
          * (∫ mu in Cn3Torus.edgeResidualTorusRegion n delta,
              Complex.re (Cn3Torus.psi n mu ^ (4 * t))) := by
  let f : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu => Complex.re (Cn3Torus.psi n mu ^ (4 * t))
  let vol : ℝ := ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ)
  let I : ℝ := ∫ mu in edgeBox n delta, f mu
  let J : ℝ := ∫ mu in Cn3Torus.edgeResidualTorusRegion n delta, f mu
  have hprimary_int :
      (∫ mu in Cn3Torus.edgePrimaryBoxUnion n delta, f mu)
        = ((Cn3Torus.lambdaShifts n).card : ℝ) * I := by
    simpa [f, I] using
      Cn3Torus.integral_edgePrimaryBoxUnion_eq_shift_card_mul_edgeBox n t hdelta_lt
  have hprimary_subset : Cn3Torus.edgePrimaryBoxUnion n delta ⊆ Cn3Torus.torusBox n :=
    Cn3Torus.edgePrimaryBoxUnion_subset_torusBox n hdelta_lt
  have hprimary_int_on :
      MeasureTheory.IntegrableOn f (Cn3Torus.edgePrimaryBoxUnion n delta) :=
    Cn3Torus.integrableOn_integrand_of_subset_torus n t hprimary_subset
  have hresid_int_on :
      MeasureTheory.IntegrableOn f (Cn3Torus.edgeResidualTorusRegion n delta) :=
    Cn3Torus.integrableOn_integrand_of_subset_torus n t (by
      intro x hx
      exact hx.1)
  have hsum :
      (∫ mu in Cn3Torus.torusBox n, f mu)
        = (∫ mu in Cn3Torus.edgePrimaryBoxUnion n delta, f mu)
            + (∫ mu in Cn3Torus.edgeResidualTorusRegion n delta, f mu) := by
    have hsum' :
        (∫ mu in Cn3Torus.edgePrimaryBoxUnion n delta ∪ Cn3Torus.edgeResidualTorusRegion n delta, f mu)
          = (∫ mu in Cn3Torus.edgePrimaryBoxUnion n delta, f mu)
              + (∫ mu in Cn3Torus.edgeResidualTorusRegion n delta, f mu) := by
      exact MeasureTheory.integral_union_ae
        (Cn3Torus.edgePrimaryBoxUnion_disjoint_edgeResidualTorusRegion n delta).aedisjoint
        (Cn3Torus.measurableSet_edgeResidualTorusRegion n delta).nullMeasurableSet
        hprimary_int_on hresid_int_on
    have hunion :
        Cn3Torus.edgePrimaryBoxUnion n delta ∪ Cn3Torus.edgeResidualTorusRegion n delta
          = Cn3Torus.torusBox n := by
      unfold Cn3Torus.edgeResidualTorusRegion
      exact Set.union_diff_cancel hprimary_subset
    simpa [hunion] using hsum'
  calc
    normalizedCount n (4 * t) = Cn3Torus.normalizedTargetIntegral n t := by
      exact normalizedCount_eq_normalizedTargetIntegral n t
    _ = (1 / vol) * (∫ mu in Cn3Torus.torusBox n, f mu) := by
          simp [Cn3Torus.normalizedTargetIntegral, Cn3Torus.targetIntegral, f, vol]
    _ = (1 / vol) * ((∫ mu in Cn3Torus.edgePrimaryBoxUnion n delta, f mu)
          + (∫ mu in Cn3Torus.edgeResidualTorusRegion n delta, f mu)) := by
            rw [hsum]
    _ = (1 / vol) * ((((Cn3Torus.lambdaShifts n).card : ℝ) * I) + J) := by
          rw [hprimary_int]
    _ = (((Cn3Torus.lambdaShifts n).card : ℝ) / vol) * I + (1 / vol) * J := by
          rw [div_eq_mul_inv]
          ring
    _ = (((Cn3Torus.lambdaShifts n).card : ℝ) / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
          * (∫ mu in edgeBox n delta, f mu)
        + (1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
          * J := by
            simp [vol, I]
    _ = (((Cn3Torus.lambdaShifts n).card : ℝ) / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
          * (∫ mu in edgeBox n delta, Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
        + (1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
          * (∫ mu in Cn3Torus.edgeResidualTorusRegion n delta,
              Complex.re (Cn3Torus.psi n mu ^ (4 * t))) := by
            simp [f, J]

/-- The global normalized count is within the exponentially small `Rdelta` error
of the transported local-box contribution. -/
theorem normalizedCount_sub_texPrefactor_mul_localIntegral_abs_le_exp_neg_half_t
    (n t : ℕ) (hn : 2 ≤ n) :
    |normalizedCount n (4 * t) - Cn3Torus.texPrefactor n * Cn3Torus.localIntegral n t|
      ≤ Real.exp (-(t : ℝ) / 2) := by
  let R : ℝ :=
    (1 / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
      * (∫ mu in Cn3Torus.RdeltaSet n, Complex.re (Cn3Torus.psi n mu ^ (4 * t)))
  have hdecomp :
      normalizedCount n (4 * t) = Cn3Torus.texPrefactor n * Cn3Torus.localIntegral n t + R := by
    have hdelta_lt : Cn3Torus.delta < π / 4 := by
      unfold Cn3Torus.delta
      linarith [Real.pi_pos]
    have hbox :
        edgeBox n Cn3Torus.delta = Cn3Torus.localBox n := by
      simpa [Cn3Torus.localBox, Cn3Torus.delta] using (edgeBox_eq_pi n Cn3Torus.delta)
    have hmain :=
      normalizedCount_primary_secondary_decomposition n t (delta := Cn3Torus.delta) hdelta_lt
    have hcoeff :
        (((Cn3Torus.lambdaShifts n).card : ℝ) / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
          = Cn3Torus.texPrefactor n := by
      rw [Cn3Torus.texPrefactor, Cn3Torus.card_lambdaShifts_eq_pow_of_two_le n hn, Nat.cast_pow]
      norm_num
    have hresid :
        Cn3Torus.edgeResidualTorusRegion n Cn3Torus.delta = Cn3Torus.RdeltaSet n := by
      unfold Cn3Torus.edgeResidualTorusRegion Cn3Torus.RdeltaSet
        Cn3Torus.edgePrimaryBoxUnion Cn3Torus.NdeltaSet Cn3Torus.NdeltaCoreSet
      simp [hbox]
    unfold R
    rw [hcoeff] at hmain
    simpa [Cn3Torus.localIntegral, hbox, hresid] using hmain
  have hR : |R| ≤ Real.exp (-(t : ℝ) / 2) := by
    unfold R
    exact Cn3Torus.normalized_RdeltaContribution_abs_le_exp_neg_half_t n t
      (Cn3Torus.gap_torus_input n hn)
  have hcancel :
      Cn3Torus.texPrefactor n * Cn3Torus.localIntegral n t + R
        - Cn3Torus.texPrefactor n * Cn3Torus.localIntegral n t = R := by
    ring
  calc
    |normalizedCount n (4 * t) - Cn3Torus.texPrefactor n * Cn3Torus.localIntegral n t|
      = |R| := by
          rw [hdecomp, hcancel]
    _ ≤ Real.exp (-(t : ℝ) / 2) := hR
