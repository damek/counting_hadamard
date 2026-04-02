import RequestProject.HadamardCn3TorusCount

/-!
# Moment Layer For The Cn^3 Formalization

This module packages the reusable discrete and Gaussian moment estimates that
sit between the torus/count bridge and the weak invariance layer.

Its declarations are meant to support later modules rather than to provide the
main reader-facing theorem surface.
-/

noncomputable section

open Real MeasureTheory Filter Finset Topology
open scoped Pointwise

set_option linter.unusedVariables false

/-!
### DL10 Local Expansion Facts
These are from the proof of DL10 Lemma 3.1 and standard Rademacher moment computations.
-/

/-- Linearity of the Boolean-edge average in a scalar factor. -/
lemma Cn3Torus.avgOver_mul_const_left (n : ℕ) (c : ℝ) (f : (Fin n → Bool) → ℝ) :
    Cn3Torus.avgOver n (fun y => c * f y) = c * Cn3Torus.avgOver n f := by
  unfold Cn3Torus.avgOver
  calc
    (∑ y : Fin n → Bool, c * f y) / (2 ^ n : ℝ)
        = (c * ∑ y : Fin n → Bool, f y) / (2 ^ n : ℝ) := by
            simp [Finset.mul_sum]
    _ = c * ((∑ y : Fin n → Bool, f y) / (2 ^ n : ℝ)) := by
          ring

lemma Cn3Torus.sqNormEdge_nonneg (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    0 ≤ Cn3Torus.sqNormEdge n mu := by
  unfold Cn3Torus.sqNormEdge
  exact Finset.sum_nonneg (fun _ _ => by positivity)

private lemma Cn3Torus.avgOver_abs_cube_sq_le_avgOver_abs_sixth (n : ℕ)
    (mu : Cn3Torus.Edge n → ℝ) :
    (Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (3 : Nat))) ^ (2 : Nat)
      ≤ Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (6 : Nat)) := by
  let f : (Fin n → Bool) → ℝ := fun y => |Cn3Torus.W mu y| ^ (3 : Nat)
  have hsq_sum :
      (∑ y : Fin n → Bool, f y) ^ (2 : Nat)
        ≤ (Fintype.card (Fin n → Bool) : ℝ) * ∑ y : Fin n → Bool, (f y) ^ (2 : Nat) := by
    simpa [f] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin n → Bool)))
        (f := fun y : Fin n → Bool => |Cn3Torus.W mu y| ^ (3 : Nat)))
  have hcardR : (Fintype.card (Fin n → Bool) : ℝ) = (2 ^ n : ℝ) := by
    exact_mod_cast (by simp : Fintype.card (Fin n → Bool) = 2 ^ n)
  have hden_pos : (0 : ℝ) < (2 ^ n : ℝ) := by positivity
  have hdiv :
      (∑ y : Fin n → Bool, f y) ^ (2 : Nat) / (2 ^ n : ℝ) ^ (2 : Nat)
        ≤ ((Fintype.card (Fin n → Bool) : ℝ) * ∑ y : Fin n → Bool, (f y) ^ (2 : Nat))
            / (2 ^ n : ℝ) ^ (2 : Nat) := by
    exact div_le_div_of_nonneg_right hsq_sum (by positivity)
  calc
    (Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (3 : Nat))) ^ (2 : Nat)
        = (∑ y : Fin n → Bool, f y) ^ (2 : Nat) / (2 ^ n : ℝ) ^ (2 : Nat) := by
            unfold Cn3Torus.avgOver f
            field_simp [hden_pos.ne']
    _ ≤ ((Fintype.card (Fin n → Bool) : ℝ) * ∑ y : Fin n → Bool, (f y) ^ (2 : Nat))
          / (2 ^ n : ℝ) ^ (2 : Nat) := hdiv
    _ = (∑ y : Fin n → Bool, (f y) ^ (2 : Nat)) / (2 ^ n : ℝ) := by
          rw [hcardR]
          field_simp [hden_pos.ne']
    _ = Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (6 : Nat)) := by
          unfold Cn3Torus.avgOver f
          congr 1
          refine Finset.sum_congr rfl ?_
          intro y hy
          change (|Cn3Torus.W mu y| ^ (3 : Nat)) ^ (2 : Nat) = |Cn3Torus.W mu y| ^ (6 : Nat)
          rw [← pow_mul]

lemma Cn3Torus.avgOver_abs_cube_le_125_mul_sqNormEdge_threeHalves (n : ℕ)
    (mu : Cn3Torus.Edge n → ℝ) :
    Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (3 : Nat))
      ≤ (125 : ℝ) * (Cn3Torus.sqNormEdge n mu) ^ (3 / 2 : ℝ) := by
  have havg_sq :
      (Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (3 : Nat))) ^ (2 : Nat)
        ≤ Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (6 : Nat)) :=
    Cn3Torus.avgOver_abs_cube_sq_le_avgOver_abs_sixth n mu
  have hhc :
      Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (6 : Nat))
        ≤ (5 : ℝ) ^ (6 : Nat) * Cn3Torus.sqNormEdge n mu ^ (3 : Nat) :=
    fixedDegreeHC_degree2_W_sixth n mu
  have hs_nonneg : 0 ≤ Cn3Torus.sqNormEdge n mu := Cn3Torus.sqNormEdge_nonneg n mu
  have havg_nonneg : 0 ≤ Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (3 : Nat)) := by
    unfold Cn3Torus.avgOver
    exact div_nonneg
      (Finset.sum_nonneg (fun _ _ => by positivity))
      (by positivity)
  have hs32_sq :
      ((Cn3Torus.sqNormEdge n mu) ^ (3 / 2 : ℝ)) ^ (2 : Nat)
        = Cn3Torus.sqNormEdge n mu ^ (3 : Nat) := by
    calc
      ((Cn3Torus.sqNormEdge n mu) ^ (3 / 2 : ℝ)) ^ (2 : Nat)
          = (Cn3Torus.sqNormEdge n mu) ^ (3 / 2 : ℝ)
              * (Cn3Torus.sqNormEdge n mu) ^ (3 / 2 : ℝ) := by
                rw [pow_two]
      _ = (Cn3Torus.sqNormEdge n mu) ^ (3 / 2 + 3 / 2 : ℝ) := by
            rw [← Real.rpow_add_of_nonneg hs_nonneg (by positivity) (by positivity)]
      _ = (Cn3Torus.sqNormEdge n mu) ^ (3 : ℝ) := by
            have hexp : (3 / 2 + 3 / 2 : ℝ) = 3 := by norm_num
            rw [hexp]
      _ = Cn3Torus.sqNormEdge n mu ^ (3 : Nat) := by
            simp
  have hbound_sq :
      (Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (3 : Nat))) ^ (2 : Nat)
        ≤ ((125 : ℝ) * (Cn3Torus.sqNormEdge n mu) ^ (3 / 2 : ℝ)) ^ (2 : Nat) := by
    calc
      (Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (3 : Nat))) ^ (2 : Nat)
          ≤ Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (6 : Nat)) := havg_sq
      _ ≤ (5 : ℝ) ^ (6 : Nat) * Cn3Torus.sqNormEdge n mu ^ (3 : Nat) := hhc
      _ = ((125 : ℝ) * (Cn3Torus.sqNormEdge n mu) ^ (3 / 2 : ℝ)) ^ (2 : Nat) := by
            have h125 : (5 : ℝ) ^ (6 : Nat) = (125 : ℝ) ^ (2 : Nat) := by norm_num
            rw [h125, hs32_sq.symm]
            ring
  have hright_nonneg : 0 ≤ (125 : ℝ) * (Cn3Torus.sqNormEdge n mu) ^ (3 / 2 : ℝ) := by
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hs_nonneg _)
  nlinarith [hbound_sq, havg_nonneg, hright_nonneg]

lemma Cn3Torus.avgOver_abs_five_sq_le_avgOver_abs_four_mul_avgOver_abs_sixth
    (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    (Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (5 : Nat))) ^ (2 : Nat)
      ≤
        Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (4 : Nat))
          * Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (6 : Nat)) := by
  let f : (Fin n → Bool) → ℝ := fun y => |Cn3Torus.W mu y| ^ (2 : Nat)
  let g : (Fin n → Bool) → ℝ := fun y => |Cn3Torus.W mu y| ^ (3 : Nat)
  let N : ℝ := (2 ^ n : ℝ)
  let A : ℝ := ∑ y : Fin n → Bool, |Cn3Torus.W mu y| ^ (5 : Nat)
  let B : ℝ := ∑ y : Fin n → Bool, |Cn3Torus.W mu y| ^ (4 : Nat)
  let C : ℝ := ∑ y : Fin n → Bool, |Cn3Torus.W mu y| ^ (6 : Nat)
  have hcs0 :
      (∑ y : Fin n → Bool, f y * g y) ^ (2 : Nat)
        ≤ (∑ y : Fin n → Bool, f y ^ (2 : Nat)) * ∑ y : Fin n → Bool, g y ^ (2 : Nat) := by
    let x : EuclideanSpace ℝ (Fin n → Bool) := WithLp.toLp 2 f
    let yv : EuclideanSpace ℝ (Fin n → Bool) := WithLp.toLp 2 g
    have hinner : inner ℝ x yv = ∑ i : Fin n → Bool, f i * g i := by
      simp [x, yv, PiLp.inner_apply, mul_comm]
    have hx_sq : ‖x‖ ^ (2 : Nat) = ∑ i : Fin n → Bool, f i ^ (2 : Nat) := by
      rw [← real_inner_self_eq_norm_sq x, PiLp.inner_apply]
      simp [x, mul_comm]
    have hy_sq : ‖yv‖ ^ (2 : Nat) = ∑ i : Fin n → Bool, g i ^ (2 : Nat) := by
      rw [← real_inner_self_eq_norm_sq yv, PiLp.inner_apply]
      simp [yv, mul_comm]
    have habs : |∑ i : Fin n → Bool, f i * g i| ≤ ‖x‖ * ‖yv‖ := by
      calc
        |∑ i : Fin n → Bool, f i * g i| = ‖inner ℝ x yv‖ := by
          rw [← hinner]
          simp
        _ ≤ ‖x‖ * ‖yv‖ := norm_inner_le_norm x yv
    have hxy_nonneg : 0 ≤ ‖x‖ * ‖yv‖ := by positivity
    have hsq :
        (∑ i : Fin n → Bool, f i * g i) ^ (2 : Nat) ≤ (‖x‖ * ‖yv‖) ^ (2 : Nat) := by
      have hmul :
          |∑ i : Fin n → Bool, f i * g i| * |∑ i : Fin n → Bool, f i * g i|
            ≤ (‖x‖ * ‖yv‖) * (‖x‖ * ‖yv‖) := by
        exact mul_le_mul habs habs (abs_nonneg _) hxy_nonneg
      simpa [sq_abs, pow_two, abs_of_nonneg hxy_nonneg] using hmul
    calc
      (∑ i : Fin n → Bool, f i * g i) ^ (2 : Nat) ≤ (‖x‖ * ‖yv‖) ^ (2 : Nat) := hsq
      _ = (‖x‖ ^ (2 : Nat)) * (‖yv‖ ^ (2 : Nat)) := by rw [mul_pow]
      _ = (∑ i : Fin n → Bool, f i ^ (2 : Nat)) * ∑ i : Fin n → Bool, g i ^ (2 : Nat) := by
            rw [hx_sq, hy_sq]
  have hfg : ∑ y : Fin n → Bool, f y * g y = A := by
    dsimp [A, f, g]
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [← pow_add]
  have hf2 : ∑ y : Fin n → Bool, f y ^ (2 : Nat) = B := by
    dsimp [B, f]
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [← pow_mul]
  have hg2 : ∑ y : Fin n → Bool, g y ^ (2 : Nat) = C := by
    dsimp [C, g]
    refine Finset.sum_congr rfl ?_
    intro y hy
    rw [← pow_mul]
  have hcs : A ^ (2 : Nat) ≤ B * C := by
    simpa [hfg, hf2, hg2] using hcs0
  have hN_pos : 0 < N := by
    dsimp [N]
    positivity
  have hdiv : A ^ (2 : Nat) / N ^ (2 : Nat) ≤ (B * C) / N ^ (2 : Nat) := by
    exact div_le_div_of_nonneg_right hcs (by positivity)
  calc
    (Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (5 : Nat))) ^ (2 : Nat)
        = A ^ (2 : Nat) / N ^ (2 : Nat) := by
            dsimp [A, N]
            unfold Cn3Torus.avgOver
            rw [div_pow]
    _ ≤ (B * C) / N ^ (2 : Nat) := hdiv
    _ = (B / N) * (C / N) := by
          field_simp [hN_pos.ne']
    _ =
        Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (4 : Nat))
          * Cn3Torus.avgOver n (fun y => |Cn3Torus.W mu y| ^ (6 : Nat)) := by
            dsimp [B, C, N]
            unfold Cn3Torus.avgOver
            rfl

/-- Pull a finite outer sum through the Boolean-edge average. -/
lemma Cn3Torus.avgOver_sum {α : Type*} [Fintype α] (n : ℕ)
    (f : α → (Fin n → Bool) → ℝ) :
    Cn3Torus.avgOver n (fun y => ∑ a : α, f a y)
      = ∑ a : α, Cn3Torus.avgOver n (fun y => f a y) := by
  have hswap :
      ∑ y : Fin n → Bool, ∑ a : α, f a y
        = ∑ a : α, ∑ y : Fin n → Bool, f a y := by
    calc
      ∑ y : Fin n → Bool, ∑ a : α, f a y
          = ∑ z : (Fin n → Bool) × α, f z.2 z.1 := by
              symm
              simpa using
                (Fintype.sum_prod_type (f := fun z : (Fin n → Bool) × α => f z.2 z.1))
      _ = ∑ z : α × (Fin n → Bool), f z.1 z.2 := by
            exact Fintype.sum_equiv (Equiv.prodComm (Fin n → Bool) α)
              (fun z : (Fin n → Bool) × α => f z.2 z.1)
              (fun z : α × (Fin n → Bool) => f z.1 z.2)
              (by intro z; rfl)
      _ = ∑ a : α, ∑ y : Fin n → Bool, f a y := by
            simpa using
              (Fintype.sum_prod_type (f := fun z : α × (Fin n → Bool) => f z.1 z.2))
  unfold Cn3Torus.avgOver
  calc
    (∑ y : Fin n → Bool, ∑ a : α, f a y) / (2 ^ n : ℝ)
        = (∑ a : α, ∑ y : Fin n → Bool, f a y) / (2 ^ n : ℝ) := by rw [hswap]
    _ = (∑ a : α, ∑ y : Fin n → Bool, f a y) * (2 ^ n : ℝ)⁻¹ := by
          rw [div_eq_mul_inv]
    _ = ∑ a : α, (∑ y : Fin n → Bool, f a y) * (2 ^ n : ℝ)⁻¹ := by
          rw [Finset.sum_mul]
    _ = ∑ a : α, ((∑ y : Fin n → Bool, f a y) / (2 ^ n : ℝ)) := by
          simp [div_eq_mul_inv]

private lemma Cn3Torus.avg_Z_product_two_eq_ite {n : ℕ} (e f : Cn3Torus.Edge n) :
    Cn3Torus.avgOver n (fun y => Cn3Torus.Z y e * Cn3Torus.Z y f)
      = if e = f then 1 else 0 := by
  by_cases hef : e = f
  · subst hef
    rw [show
      (fun y => Cn3Torus.Z y e * Cn3Torus.Z y e) = (fun _ : Fin n → Bool => 1) by
        funext y
        have hsq := Cn3Torus.Z_sq_eq_one y e
        simpa [pow_two] using hsq]
    simpa using Cn3Torus.avgOver_const n 1
  · unfold Cn3Torus.avgOver
    rcases Cn3Torus.exists_incident_xor_of_ne hef with ⟨i, hxor | hxor⟩
    · have hperm :
          (∑ y : Fin n → Bool,
              Cn3Torus.Z (Cn3Torus.flipBoolAt i y) e * Cn3Torus.Z (Cn3Torus.flipBoolAt i y) f)
            = ∑ y : Fin n → Bool, Cn3Torus.Z y e * Cn3Torus.Z y f := by
        simpa using Cn3Torus.sum_flipBoolAt_eq i (fun y => Cn3Torus.Z y e * Cn3Torus.Z y f)
      have hneg :
          (∑ y : Fin n → Bool,
              Cn3Torus.Z (Cn3Torus.flipBoolAt i y) e * Cn3Torus.Z (Cn3Torus.flipBoolAt i y) f)
            = -(∑ y : Fin n → Bool, Cn3Torus.Z y e * Cn3Torus.Z y f) := by
        calc
          (∑ y : Fin n → Bool,
              Cn3Torus.Z (Cn3Torus.flipBoolAt i y) e * Cn3Torus.Z (Cn3Torus.flipBoolAt i y) f)
              =
            ∑ y : Fin n → Bool,
              ((if e ∈ Cn3Torus.edgesIncident n i then -Cn3Torus.Z y e else Cn3Torus.Z y e)
                * (if f ∈ Cn3Torus.edgesIncident n i then -Cn3Torus.Z y f else Cn3Torus.Z y f)) := by
                  refine Finset.sum_congr rfl ?_
                  intro y hy
                  rw [Cn3Torus.Z_flip_at, Cn3Torus.Z_flip_at]
          _ = ∑ y : Fin n → Bool, -(Cn3Torus.Z y e * Cn3Torus.Z y f) := by
                refine Finset.sum_congr rfl ?_
                intro y hy
                simp [hxor.1, hxor.2]
          _ = -(∑ y : Fin n → Bool, Cn3Torus.Z y e * Cn3Torus.Z y f) := by
                rw [Finset.sum_neg_distrib]
      have hsum : (∑ y : Fin n → Bool, Cn3Torus.Z y e * Cn3Torus.Z y f) = 0 := by
        linarith
      rw [hsum, if_neg hef]
      simp
    · have hperm :
          (∑ y : Fin n → Bool,
              Cn3Torus.Z (Cn3Torus.flipBoolAt i y) e * Cn3Torus.Z (Cn3Torus.flipBoolAt i y) f)
            = ∑ y : Fin n → Bool, Cn3Torus.Z y e * Cn3Torus.Z y f := by
        simpa using Cn3Torus.sum_flipBoolAt_eq i (fun y => Cn3Torus.Z y e * Cn3Torus.Z y f)
      have hneg :
          (∑ y : Fin n → Bool,
              Cn3Torus.Z (Cn3Torus.flipBoolAt i y) e * Cn3Torus.Z (Cn3Torus.flipBoolAt i y) f)
            = -(∑ y : Fin n → Bool, Cn3Torus.Z y e * Cn3Torus.Z y f) := by
        calc
          (∑ y : Fin n → Bool,
              Cn3Torus.Z (Cn3Torus.flipBoolAt i y) e * Cn3Torus.Z (Cn3Torus.flipBoolAt i y) f)
              =
            ∑ y : Fin n → Bool,
              ((if e ∈ Cn3Torus.edgesIncident n i then -Cn3Torus.Z y e else Cn3Torus.Z y e)
                * (if f ∈ Cn3Torus.edgesIncident n i then -Cn3Torus.Z y f else Cn3Torus.Z y f)) := by
                  refine Finset.sum_congr rfl ?_
                  intro y hy
                  rw [Cn3Torus.Z_flip_at, Cn3Torus.Z_flip_at]
          _ = ∑ y : Fin n → Bool, -(Cn3Torus.Z y e * Cn3Torus.Z y f) := by
                refine Finset.sum_congr rfl ?_
                intro y hy
                simp [hxor.1, hxor.2]
          _ = -(∑ y : Fin n → Bool, Cn3Torus.Z y e * Cn3Torus.Z y f) := by
                rw [Finset.sum_neg_distrib]
      have hsum : (∑ y : Fin n → Bool, Cn3Torus.Z y e * Cn3Torus.Z y f) = 0 := by
        linarith
      rw [hsum, if_neg hef]
      simp

lemma Cn3Torus.avgOver_weighted_prod_Z_two (n : ℕ) (mu : Cn3Torus.Edge n → ℝ)
    (e : Cn3Torus.Edge n) :
    Cn3Torus.avgOver n (fun y => Cn3Torus.W mu y * Cn3Torus.Z y e) = mu e := by
  have hpoint :
      (fun y => Cn3Torus.W mu y * Cn3Torus.Z y e)
        = (fun y => ∑ f : Cn3Torus.Edge n, mu f * (Cn3Torus.Z y f * Cn3Torus.Z y e)) := by
    funext y
    unfold Cn3Torus.W
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro f hf
    ring
  rw [hpoint]
  calc
    Cn3Torus.avgOver n
        (fun y => ∑ f : Cn3Torus.Edge n, mu f * (Cn3Torus.Z y f * Cn3Torus.Z y e))
        = ∑ f : Cn3Torus.Edge n,
            Cn3Torus.avgOver n (fun y => mu f * (Cn3Torus.Z y f * Cn3Torus.Z y e)) := by
              simpa using Cn3Torus.avgOver_sum n
                (fun f : Cn3Torus.Edge n => fun y => mu f * (Cn3Torus.Z y f * Cn3Torus.Z y e))
    _ = ∑ f : Cn3Torus.Edge n, mu f * (if f = e then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro f hf
          rw [Cn3Torus.avgOver_mul_const_left, Cn3Torus.avg_Z_product_two_eq_ite]
    _ = mu e := by
          classical
          rw [Finset.sum_eq_single e]
          · simp
          · intro f hf hfe
            simp [hfe]
          · simp

/-- The singleton-coordinate collapse on `Unit → ℝ` preserves volume. -/
lemma volume_measurePreserving_funUnique_real :
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

/-- **Gaussian integral**: ∫_{ℝ^d} e^{-a‖x‖²} dx = (π/a)^{d/2} for a > 0. -/
theorem gaussian_integral_formula (d : ℕ) (a : ℝ) (ha : 0 < a) :
  ∫ x : Fin d → ℝ, Real.exp (-a * ∑ i, x i ^ 2) = (π / a) ^ ((d : ℝ) / 2) := by
  induction d with
  | zero =>
      rw [MeasureTheory.integral_unique]
      have hvol : (MeasureTheory.volume : MeasureTheory.Measure (Fin 0 → ℝ)) Set.univ = 1 := by
        rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
        simp
      rw [MeasureTheory.Measure.real_def, hvol]
      norm_num
  | succ n ih =>
      let e : Fin (n + 1) ≃ Unit ⊕ Fin n :=
        Fintype.equivOfCardEq (by simp [Nat.add_comm])
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
      have hsq :
          ∀ x : Fin (n + 1) → ℝ,
            ∑ i : Fin (n + 1), x i ^ (2 : Nat)
              = (split x).1 ^ (2 : Nat) + ∑ i : Fin n, (split x).2 i ^ (2 : Nat) := by
        intro x
        have hsum1 :
            ∑ i : Fin (n + 1), x i ^ (2 : Nat)
              = ∑ s : Unit ⊕ Fin n, (reindex1 x s) ^ (2 : Nat) := by
          exact Fintype.sum_equiv e
            (fun i : Fin (n + 1) => x i ^ (2 : Nat))
            (fun s : Unit ⊕ Fin n => (reindex1 x s) ^ (2 : Nat))
            (by
              intro i
              have happly : reindex1 x (e i) = x i := by
                change (MeasurableEquiv.piCongrLeft (fun _ : Unit ⊕ Fin n => ℝ) e x) (e i) = x i
                simp [MeasurableEquiv.piCongrLeft]
              simp [happly])
        calc
          ∑ i : Fin (n + 1), x i ^ (2 : Nat)
              = ∑ s : Unit ⊕ Fin n, (reindex1 x s) ^ (2 : Nat) := hsum1
          _ = (reindex2 (reindex1 x)).1 PUnit.unit ^ (2 : Nat)
                + ∑ i : Fin n, (reindex2 (reindex1 x)).2 i ^ (2 : Nat) := by
                  rw [Fintype.sum_sum_type]
                  simp [reindex2, MeasurableEquiv.sumPiEquivProdPi]
          _ = (split x).1 ^ (2 : Nat) + ∑ i : Fin n, (split x).2 i ^ (2 : Nat) := by
                rfl
      have htransport :=
        MeasureTheory.MeasurePreserving.integral_comp hpres hsplit_meas
          (fun p : ℝ × (Fin n → ℝ) =>
            Real.exp (-a * (p.1 ^ 2 + ∑ i : Fin n, p.2 i ^ 2)))
      calc
        ∫ x : Fin (n + 1) → ℝ, Real.exp (-a * ∑ i : Fin (n + 1), x i ^ 2)
            = ∫ x : Fin (n + 1) → ℝ,
                Real.exp (-a * ((split x).1 ^ 2 + ∑ i : Fin n, (split x).2 i ^ 2)) := by
                  congr with x
                  rw [hsq x]
        _ = ∫ p : ℝ × (Fin n → ℝ),
              Real.exp (-a * (p.1 ^ 2 + ∑ i : Fin n, p.2 i ^ 2)) := by
                simpa [split] using htransport
        _ = ∫ p : ℝ × (Fin n → ℝ),
              Real.exp (-a * p.1 ^ 2) * Real.exp (-a * ∑ i : Fin n, p.2 i ^ 2) := by
                congr with p
                rw [← Real.exp_add]
                congr 1
                ring
        _ = (∫ z : ℝ, Real.exp (-a * z ^ 2))
              * ∫ y : Fin n → ℝ, Real.exp (-a * ∑ i : Fin n, y i ^ 2) := by
                change
                  ∫ p : ℝ × (Fin n → ℝ),
                    Real.exp (-a * p.1 ^ 2) * Real.exp (-a * ∑ i : Fin n, p.2 i ^ 2)
                      ∂ (MeasureTheory.volume.prod MeasureTheory.volume)
                    = _
                rw [← MeasureTheory.integral_prod_mul]
        _ = Real.sqrt (π / a) * (π / a) ^ ((n : ℝ) / 2) := by
              rw [integral_gaussian, ih]
        _ = (π / a) ^ (((n + 1 : ℕ) : ℝ) / 2) := by
              have hpa : 0 < π / a := by exact div_pos pi_pos ha
              rw [Real.sqrt_eq_rpow]
              rw [← Real.rpow_add hpa]
              congr 1
              norm_num [Nat.cast_add]
              linarith

/-- Edge-coordinate transport of `gaussian_integral_formula`. -/
theorem gaussian_integral_formula_edge (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫ mu : Cn3Torus.Edge n → ℝ, Real.exp (-a * Cn3Torus.sqNormEdge n mu) =
      (π / a) ^ ((dim n : ℝ) / 2) := by
  let e : Fin (dim n) ≃ Cn3Torus.Edge n :=
    Fintype.equivOfCardEq
      (by rw [Fintype.card_fin, dim_eq_edgeDim]; exact (Cn3Torus.card_Edge_eq_d n).symm)
  let reindex : (Fin (dim n) → ℝ) ≃ᵐ (Cn3Torus.Edge n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Cn3Torus.Edge n => ℝ) e
  have hpres :
      MeasureTheory.MeasurePreserving reindex MeasureTheory.volume MeasureTheory.volume := by
    simpa [reindex] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Cn3Torus.Edge n => ℝ) e)
  have hsq :
      ∀ x : Fin (dim n) → ℝ,
        Cn3Torus.sqNormEdge n (reindex x) = ∑ i : Fin (dim n), x i ^ (2 : Nat) := by
    intro x
    unfold Cn3Torus.sqNormEdge
    calc
      ∑ ee : Cn3Torus.Edge n, (reindex x ee) ^ (2 : Nat)
          = ∑ ee : Cn3Torus.Edge n, (x (e.symm ee)) ^ (2 : Nat) := by
              refine Finset.sum_congr rfl ?_
              intro ee hee
              have happly : reindex x ee = x (e.symm ee) := by
                simpa [reindex] using
                  (Equiv.piCongrLeft_apply (P := fun _ : Cn3Torus.Edge n => ℝ) e x ee)
              rw [happly]
      _ = ∑ i : Fin (dim n), x i ^ (2 : Nat) := by
            symm
            exact Fintype.sum_equiv e
              (fun i : Fin (dim n) => x i ^ (2 : Nat))
              (fun ee : Cn3Torus.Edge n => x (e.symm ee) ^ (2 : Nat))
              (by intro i; simp)
  have htransport :=
    MeasureTheory.MeasurePreserving.integral_comp hpres reindex.measurableEmbedding
      (fun mu : Cn3Torus.Edge n → ℝ => Real.exp (-a * Cn3Torus.sqNormEdge n mu))
  calc
    ∫ mu : Cn3Torus.Edge n → ℝ, Real.exp (-a * Cn3Torus.sqNormEdge n mu)
        = ∫ x : Fin (dim n) → ℝ,
            Real.exp (-a * Cn3Torus.sqNormEdge n (reindex x)) := by
              symm
              simpa [reindex] using htransport
    _ = ∫ x : Fin (dim n) → ℝ, Real.exp (-a * ∑ i : Fin (dim n), x i ^ (2 : Nat)) := by
          congr with x
          rw [hsq x]
    _ = (π / a) ^ ((dim n : ℝ) / 2) := gaussian_integral_formula (dim n) a ha

/-! **Gaussian monomial moments** (reusable for Section 5 / `gaussianF` comparisons). -/

/-- **1D even Gaussian moments** (exact): \(\int_{\mathbb R} x^{2k} e^{-a x^2}\,dx
  = \frac{(2k-1)!!}{2^k a^k}\sqrt{\pi/a}\) for \(a>0\). -/
theorem gaussian_one_dim_even_moment (k : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ, x ^ (2 * k) * Real.exp (-a * x ^ 2) =
      (((Nat.doubleFactorial (2 * k - 1) : ℕ) : ℝ) / (2 ^ k * a ^ k))
        * Real.sqrt (Real.pi / a) := by
  have hq : -1 < (2 * k : ℝ) := by
    have hk_nonneg : 0 ≤ (2 * k : ℝ) := by positivity
    linarith
  have hpow (x : ℝ) : x ^ (2 * k) = |x| ^ (2 * k) := by
    rw [pow_mul, pow_mul]
    simpa [pow_two] using congrArg (fun t : ℝ => t ^ k) (sq_abs x)
  let f : ℝ → ℝ := fun t => t ^ (2 * k) * Real.exp (-a * t ^ 2)
  have hfabs :
      ∫ x : ℝ, x ^ (2 * k) * Real.exp (-a * x ^ 2) = ∫ x : ℝ, f |x| := by
    refine MeasureTheory.integral_congr_ae ?_
    exact Filter.Eventually.of_forall (fun x => by simp [f, hpow x])
  have hIoi :=
    (integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0 : ℝ) < 2) hq ha :
      ∫ x in Set.Ioi (0 : ℝ), x ^ (2 * k : ℝ) * Real.exp (-a * x ^ (2 : ℝ)) = _)
  have hpowIoi :
      ∫ x in Set.Ioi (0 : ℝ), x ^ (2 * k) * Real.exp (-a * x ^ 2) =
        ∫ x in Set.Ioi (0 : ℝ), x ^ (2 * k : ℝ) * Real.exp (-a * x ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [Set.mem_Ioi] at hx
    simpa using (Real.rpow_natCast x (2 * k)).symm
  have hGam : Real.Gamma (((2 * k : ℝ) + 1) / 2) = Real.Gamma (k + 1 / 2) := by congr 1; field
  calc
    ∫ x : ℝ, x ^ (2 * k) * Real.exp (-a * x ^ 2)
        = ∫ x : ℝ, f |x| := hfabs
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := by
          rw [integral_comp_abs]
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), x ^ (2 * k) * Real.exp (-a * x ^ 2) := by
          simp [f]
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), x ^ (2 * k : ℝ) * Real.exp (-a * x ^ 2) := by
          simpa using congrArg (fun z : ℝ => 2 * z) hpowIoi
    _ = 2 * (a ^ (-((2 * k : ℝ) + 1) / 2) * (1 / 2) * Real.Gamma (((2 * k : ℝ) + 1) / 2)) := by
          simpa using congrArg (fun z : ℝ => 2 * z) hIoi
    _ = a ^ (-((2 * k : ℝ) + 1) / 2) * Real.Gamma (k + 1 / 2) := by
          rw [hGam]
          ring
    _ = (((Nat.doubleFactorial (2 * k - 1) : ℕ) : ℝ) / (2 ^ k * a ^ k))
          * Real.sqrt (Real.pi / a) := by
          rw [Real.Gamma_nat_add_half k]
          have ha₀ : 0 < a := ha
          have hexp : -((2 * k : ℝ) + 1) / 2 = (-(k : ℝ)) + (-(1 / 2 : ℝ)) := by ring
          have hsqrt :
              Real.sqrt (Real.pi / a) = Real.pi ^ (1 / 2 : ℝ) * a ^ (-(1 / 2 : ℝ)) := by
            rw [Real.sqrt_eq_rpow, Real.div_rpow (show 0 ≤ Real.pi by positivity) ha₀.le,
              Real.rpow_neg ha₀.le]
            simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
          rw [hexp, Real.rpow_add ha₀, Real.rpow_neg ha₀.le, Real.rpow_natCast,
            Real.sqrt_eq_rpow, hsqrt]
          simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Normalized radial kernel \(\int |y|^{2m} e^{-y^2}\,dy\) (shorthand for scaling identities). -/
noncomputable def gaussianRadialMomentK (m : ℕ) : ℝ :=
  ∫ y : ℝ, y ^ (2 * m) * Real.exp (-1 * y ^ 2)

/-- Exact 1D moment formula specialized to the kernel `exp(-2 t x^2)`. -/
lemma gaussian_one_dim_scaled_moment (m : ℕ) (t : ℝ) (ht : 0 < t) :
    ∫ x : ℝ, x ^ (2 * m) * Real.exp (-2 * t * x ^ 2) =
      (((Nat.doubleFactorial (2 * m - 1) : ℕ) : ℝ) / (2 ^ m * (2 * t) ^ m))
        * Real.sqrt (Real.pi / (2 * t)) := by
  have h2t : 0 < (2 * t : ℝ) := by positivity
  simpa [mul_assoc] using gaussian_one_dim_even_moment m (2 * t) h2t

/-- Explicit coefficient \((2m-1)!!/4^m\) in \(\mathbb R^d\) radial moment bounds
    (matches \(d^m/t^m\) after absorbing powers of \(2\) from the kernel \(\exp(-2t\|x\|^2)\)). -/
noncomputable def gaussianRadialMomentCoeff (m : ℕ) : ℝ :=
  (Nat.doubleFactorial (2 * m - 1) : ℝ) / (4 : ℝ) ^ m

/-- Manuscript `lem:gaussian-radial-moments` in a form strong enough for the local
core error estimates: the radial Gaussian moments cost a factor `t^{-m}` relative to
`gaussianF`. -/
theorem gaussian_radial_moments (d m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ∫ x : Fin d → ℝ,
        (∑ i : Fin d, x i ^ (2 : Nat)) ^ m * Real.exp (-2 * t * ∑ i : Fin d, x i ^ (2 : Nat))
          ≤ (C / t ^ m) * gaussianF d t := by
  let S : (Fin d → ℝ) → ℝ := fun x => ∑ i : Fin d, x i ^ (2 : Nat)
  let K : ℝ := ∫ x : Fin d → ℝ, (S x) ^ m * Real.exp (-S x)
  let C0 : ℝ := K / ((2 : ℝ) ^ m * π ^ ((d : ℝ) / 2))
  refine ⟨C0 + 1, by positivity, ?_⟩
  intro t ht
  have ht_pos : 0 < t := by linarith
  have h2t_pos : 0 < 2 * t := by positivity
  let R : ℝ := Real.sqrt (2 * t)
  let f : (Fin d → ℝ) → ℝ := fun x => (S x) ^ m * Real.exp (-S x)
  let g : (Fin d → ℝ) → ℝ := fun x => (S x) ^ m * Real.exp (-2 * t * S x)
  have hS_scale (x : Fin d → ℝ) : S (R • x) = (2 * t) * S x := by
    unfold S R
    calc
      ∑ i : Fin d, ((Real.sqrt (2 * t)) • x i) ^ (2 : Nat)
          = ∑ i : Fin d, (Real.sqrt (2 * t)) ^ (2 : Nat) * x i ^ (2 : Nat) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [smul_eq_mul, pow_two, mul_assoc, mul_left_comm, mul_comm]
      _ = (Real.sqrt (2 * t)) ^ (2 : Nat) * ∑ i : Fin d, x i ^ (2 : Nat) := by
            rw [Finset.mul_sum]
      _ = (2 * t) * S x := by
            rw [Real.sq_sqrt h2t_pos.le]
  have hcomp (x : Fin d → ℝ) : f (R • x) = (2 * t) ^ m * g x := by
    unfold f g
    calc
      f (R • x) = (S (R • x)) ^ m * Real.exp (-S (R • x)) := by rfl
      _ = ((2 * t) * S x) ^ m * Real.exp (-((2 * t) * S x)) := by
            rw [hS_scale x]
      _ = ((2 * t) ^ m * S x ^ m) * Real.exp (-(2 * t * S x)) := by
            rw [mul_pow]
      _ = (2 * t) ^ m * (S x ^ m * Real.exp (-(2 * t * S x))) := by
            ring
      _ = (2 * t) ^ m * g x := by
            simp [g]
  have hleft :
      ∫ x : Fin d → ℝ, f (R • x) = (2 * t) ^ m * ∫ x : Fin d → ℝ, g x := by
    calc
      ∫ x : Fin d → ℝ, f (R • x) = ∫ x : Fin d → ℝ, (2 * t) ^ m * g x := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall hcomp
      _ = (2 * t) ^ m * ∫ x : Fin d → ℝ, g x := by
            rw [MeasureTheory.integral_const_mul]
  have hscale :=
    MeasureTheory.Measure.integral_comp_smul
      (μ := MeasureTheory.volume) (f := f) R
  have hRpow : (R ^ d : ℝ) = (2 * t) ^ ((d : ℝ) / 2) := by
    unfold R
    rw [Real.sqrt_eq_rpow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul h2t_pos.le]
    congr 1
    ring
  have habs_inv : |((R ^ d)⁻¹ : ℝ)| = (2 * t) ^ (-((d : ℝ) / 2)) := by
    have hRpow_pos : 0 < (R ^ d : ℝ) := by
      rw [hRpow]
      positivity
    rw [abs_of_nonneg (inv_nonneg.mpr hRpow_pos.le), hRpow]
    symm
    exact Real.rpow_neg h2t_pos.le ((d : ℝ) / 2)
  have hmain :
      (2 * t) ^ m * ∫ x : Fin d → ℝ, g x = (2 * t) ^ (-((d : ℝ) / 2)) * K := by
    calc
      (2 * t) ^ m * ∫ x : Fin d → ℝ, g x = ∫ x : Fin d → ℝ, f (R • x) := by
            symm
            exact hleft
      _ = |((R ^ d)⁻¹ : ℝ)| * ∫ x : Fin d → ℝ, f x := by
            simpa [smul_eq_mul] using hscale
      _ = (2 * t) ^ (-((d : ℝ) / 2)) * K := by
            rw [habs_inv]
  have hm_nonzero : ((2 * t : ℝ) ^ m) ≠ 0 := by positivity
  have hformula :
      ∫ x : Fin d → ℝ, g x = ((C0 / t ^ m) * gaussianF d t) := by
    have hgauss :
        gaussianF d t = π ^ ((d : ℝ) / 2) * (2 * t) ^ (-((d : ℝ) / 2)) := by
      unfold gaussianF
      rw [Real.div_rpow (by positivity : 0 ≤ π) h2t_pos.le, Real.rpow_neg h2t_pos.le]
      simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    calc
      ∫ x : Fin d → ℝ, g x
          = ((2 * t) ^ (-((d : ℝ) / 2)) * K) / (2 * t) ^ m := by
              exact (eq_div_iff hm_nonzero).2 (by simpa [mul_comm] using hmain)
      _ = ((C0 / t ^ m) * gaussianF d t) := by
            unfold C0
            rw [hgauss, mul_pow]
            field_simp [hm_nonzero, ht_pos.ne', Real.pi_ne_zero]
  have hC0_le : C0 ≤ C0 + 1 := by linarith
  have hnonneg : 0 ≤ (t ^ m)⁻¹ * gaussianF d t := by
    have hgauss_nonneg : 0 ≤ gaussianF d t := by
      unfold gaussianF
      positivity
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg ht_pos.le _)) hgauss_nonneg
  calc
    ∫ x : Fin d → ℝ,
      (∑ i : Fin d, x i ^ (2 : Nat)) ^ m * Real.exp (-2 * t * ∑ i : Fin d, x i ^ (2 : Nat))
        = ((C0 / t ^ m) * gaussianF d t) := by
            simpa [g, S] using hformula
    _ ≤ (((C0 + 1) / t ^ m) * gaussianF d t) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (mul_le_mul_of_nonneg_right hC0_le hnonneg)
    _ = ((C0 + 1) / t ^ m) * gaussianF d t := by rfl

/-- Edge-coordinate transport of `gaussian_radial_moments`. -/
theorem gaussian_radial_moments_edge (n m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ∫ mu : Cn3Torus.Edge n → ℝ,
        Cn3Torus.sqNormEdge n mu ^ m * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
          ≤ (C / t ^ m) * gaussianF (dim n) t := by
  obtain ⟨C, hC_pos, hbound⟩ := gaussian_radial_moments (dim n) m
  refine ⟨C, hC_pos, ?_⟩
  intro t ht
  let e : Fin (dim n) ≃ Cn3Torus.Edge n :=
    Fintype.equivOfCardEq
      (by rw [Fintype.card_fin, dim_eq_edgeDim]; exact (Cn3Torus.card_Edge_eq_d n).symm)
  let reindex : (Fin (dim n) → ℝ) ≃ᵐ (Cn3Torus.Edge n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Cn3Torus.Edge n => ℝ) e
  have hpres :
      MeasureTheory.MeasurePreserving reindex MeasureTheory.volume MeasureTheory.volume := by
    simpa [reindex] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Cn3Torus.Edge n => ℝ) e)
  have hsq :
      ∀ x : Fin (dim n) → ℝ,
        Cn3Torus.sqNormEdge n (reindex x) = ∑ i : Fin (dim n), x i ^ (2 : Nat) := by
    intro x
    unfold Cn3Torus.sqNormEdge
    calc
      ∑ ee : Cn3Torus.Edge n, (reindex x ee) ^ (2 : Nat)
          = ∑ ee : Cn3Torus.Edge n, (x (e.symm ee)) ^ (2 : Nat) := by
              refine Finset.sum_congr rfl ?_
              intro ee hee
              have happly : reindex x ee = x (e.symm ee) := by
                simpa [reindex] using
                  (Equiv.piCongrLeft_apply (P := fun _ : Cn3Torus.Edge n => ℝ) e x ee)
              rw [happly]
      _ = ∑ i : Fin (dim n), x i ^ (2 : Nat) := by
            symm
            exact Fintype.sum_equiv e
              (fun i : Fin (dim n) => x i ^ (2 : Nat))
              (fun ee : Cn3Torus.Edge n => x (e.symm ee) ^ (2 : Nat))
              (by intro i; simp)
  let g : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu =>
    Cn3Torus.sqNormEdge n mu ^ m * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
  let h : (Fin (dim n) → ℝ) → ℝ := fun x =>
    (∑ i : Fin (dim n), x i ^ (2 : Nat)) ^ m
      * Real.exp (-2 * t * ∑ i : Fin (dim n), x i ^ (2 : Nat))
  have hcomp : ∀ x : Fin (dim n) → ℝ, g (reindex x) = h x := by
    intro x
    simp [g, h, hsq x]
  have htransport :=
    MeasureTheory.MeasurePreserving.integral_comp hpres reindex.measurableEmbedding g
  calc
    ∫ mu : Cn3Torus.Edge n → ℝ,
      Cn3Torus.sqNormEdge n mu ^ m * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
        = ∫ mu : Cn3Torus.Edge n → ℝ, g mu := by
            rfl
    _ = ∫ x : Fin (dim n) → ℝ, g (reindex x) := by
          symm
          simpa [reindex, g] using htransport
    _ = ∫ x : Fin (dim n) → ℝ, h x := by
          refine MeasureTheory.integral_congr_ae ?_
          exact Filter.Eventually.of_forall hcomp
    _ = ∫ x : Fin (dim n) → ℝ,
          (∑ i : Fin (dim n), x i ^ (2 : Nat)) ^ m
            * Real.exp (-2 * t * ∑ i : Fin (dim n), x i ^ (2 : Nat)) := by
          rfl
    _ ≤ (C / t ^ m) * gaussianF (dim n) t := hbound t ht

/-- The edge-core Gaussian mass is exactly `coreMass` after transport from
`Fin (dim n)` coordinates. -/
theorem coreMass_eq_edgeCoreRegion_gaussian_integral (n : ℕ) (t : ℝ) :
    coreMass (dim n) t =
      ∫ mu in edgeCoreRegion n t, Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu) := by
  let e : Fin (dim n) ≃ Cn3Torus.Edge n :=
    Fintype.equivOfCardEq
      (by rw [Fintype.card_fin, dim_eq_edgeDim]; exact (Cn3Torus.card_Edge_eq_d n).symm)
  let reindex : (Fin (dim n) → ℝ) ≃ᵐ (Cn3Torus.Edge n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Cn3Torus.Edge n => ℝ) e
  have hpres :
      MeasureTheory.MeasurePreserving reindex MeasureTheory.volume MeasureTheory.volume := by
    simpa [reindex] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft
        (fun _ : Cn3Torus.Edge n => ℝ) e)
  have hsq :
      ∀ x : Fin (dim n) → ℝ,
        Cn3Torus.sqNormEdge n (reindex x) = ∑ i : Fin (dim n), x i ^ (2 : Nat) := by
    intro x
    unfold Cn3Torus.sqNormEdge
    calc
      ∑ ee : Cn3Torus.Edge n, (reindex x ee) ^ (2 : Nat)
          = ∑ ee : Cn3Torus.Edge n, (x (e.symm ee)) ^ (2 : Nat) := by
              refine Finset.sum_congr rfl ?_
              intro ee hee
              have happly : reindex x ee = x (e.symm ee) := by
                simpa [reindex] using
                  (Equiv.piCongrLeft_apply (P := fun _ : Cn3Torus.Edge n => ℝ) e x ee)
              rw [happly]
      _ = ∑ i : Fin (dim n), x i ^ (2 : Nat) := by
            symm
            exact Fintype.sum_equiv e
              (fun i : Fin (dim n) => x i ^ (2 : Nat))
              (fun ee : Cn3Torus.Edge n => x (e.symm ee) ^ (2 : Nat))
              (by intro i; simp)
  let g : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu =>
    Set.indicator (edgeCoreRegion n t)
      (fun mu => Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)) mu
  let h : (Fin (dim n) → ℝ) → ℝ := fun x =>
    Set.indicator {x : Fin (dim n) → ℝ | ∑ i : Fin (dim n), x i ^ (2 : Nat) ≤ (dim n : ℝ) / t}
      (fun x => Real.exp (-2 * t * ∑ i : Fin (dim n), x i ^ (2 : Nat))) x
  have hcomp : ∀ x : Fin (dim n) → ℝ, g (reindex x) = h x := by
    intro x
    by_cases hx : Cn3Torus.sqNormEdge n (reindex x) ≤ (dim n : ℝ) / t
    · have hsum : ∑ i : Fin (dim n), x i ^ (2 : Nat) ≤ (dim n : ℝ) / t := by
        simpa [hsq x] using hx
      have hmem : reindex x ∈ edgeCoreRegion n t := by
        exact (mem_edgeCoreRegion_iff n t (reindex x)).2 hx
      simp [g, h, hsum, hmem, hsq x]
    · have hsum : ¬ ∑ i : Fin (dim n), x i ^ (2 : Nat) ≤ (dim n : ℝ) / t := by
        simpa [hsq x] using hx
      have hmem : reindex x ∉ edgeCoreRegion n t := by
        intro hmem
        exact hx ((mem_edgeCoreRegion_iff n t (reindex x)).1 hmem)
      simp [g, h, hsum, hmem, hsq x]
  have htransport :=
    MeasureTheory.MeasurePreserving.integral_comp hpres reindex.measurableEmbedding g
  calc
    coreMass (dim n) t = ∫ x : Fin (dim n) → ℝ, h x := by
          rfl
    _ = ∫ x : Fin (dim n) → ℝ, g (reindex x) := by
          refine MeasureTheory.integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun x => (hcomp x).symm)
    _ = ∫ mu : Cn3Torus.Edge n → ℝ, g mu := by
          simpa [reindex, g] using htransport
    _ = ∫ mu in edgeCoreRegion n t, Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu) := by
          simp [g, measurableSet_edgeCoreRegion, MeasureTheory.integral_indicator]

/-- **Gaussian tail**: On {‖x‖² > d/t}, e^{-2t‖x‖²} ≤ e^{-d}·e^{-t‖x‖²}. -/
theorem gaussian_tail_factoring (d : ℕ) (t : ℝ) (ht : 0 < t) :
  ∫ x : Fin d → ℝ,
    Set.indicator {x : Fin d → ℝ | ∑ i, x i ^ 2 > (d : ℝ) / t}
      (fun x => Real.exp (-2 * t * ∑ i, x i ^ 2)) x ≤
  Real.exp (-(d : ℝ)) * (π / t) ^ ((d : ℝ) / 2) := by
  let g : (Fin d → ℝ) → ℝ := fun x =>
    Real.exp (-(d : ℝ)) * Real.exp (-t * ∑ i, x i ^ 2)
  have hbase_int :
      ∫ x : Fin d → ℝ, Real.exp (-t * ∑ i, x i ^ 2) = (π / t) ^ ((d : ℝ) / 2) :=
    gaussian_integral_formula d t ht
  have hbase_integrable :
      MeasureTheory.Integrable (fun x : Fin d → ℝ => Real.exp (-t * ∑ i, x i ^ 2)) := by
    by_contra hnot
    rw [MeasureTheory.integral_undef hnot] at hbase_int
    have hpos : 0 < (π / t) ^ ((d : ℝ) / 2) := by positivity
    linarith
  have hg_integrable : MeasureTheory.Integrable g := by
    exact hbase_integrable.const_mul _
  refine le_trans (MeasureTheory.integral_mono_of_nonneg ?_ hg_integrable ?_) ?_
  · exact Filter.Eventually.of_forall (fun x => by
      rw [Set.indicator_apply]
      split_ifs <;> positivity)
  · filter_upwards with x
    by_cases hx : ∑ i, x i ^ 2 > (d : ℝ) / t
    · simp [hx, g]
      have hle : Real.exp (-(t * ∑ i, x i ^ 2)) ≤ Real.exp (-(d : ℝ)) := by
        have hx' : (d : ℝ) < (∑ i, x i ^ 2) * t := by
          exact (div_lt_iff₀ ht).mp (by simpa using hx)
        apply Real.exp_le_exp.mpr
        linarith
      have hnonneg : 0 ≤ Real.exp (-(t * ∑ i, x i ^ 2)) := by positivity
      have hmul := mul_le_mul_of_nonneg_right hle hnonneg
      have hexp :
          Real.exp (-(2 * t * ∑ i, x i ^ 2))
            = Real.exp (-(t * ∑ i, x i ^ 2)) * Real.exp (-(t * ∑ i, x i ^ 2)) := by
              rw [← Real.exp_add]
              congr 1
              ring
      rw [hexp]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    · simp [hx, g]
      positivity
  · rw [show ∫ x : Fin d → ℝ, g x
            = Real.exp (-(d : ℝ)) * ∫ x : Fin d → ℝ, Real.exp (-t * ∑ i, x i ^ 2) by
            rw [MeasureTheory.integral_const_mul]]
    rw [hbase_int]
