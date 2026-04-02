import RequestProject.HadamardCn3DiscreteMoments

/-!
# Residual Analytic Support For The Cn^3 Formalization

This module contains the triangle/quartic/cubic support estimates that feed the
local-gap residual analysis. It is the last foundational layer before the
higher-level bridge and residual modules.
-/

noncomputable section

open Real MeasureTheory Filter Finset Topology
open scoped Pointwise

set_option linter.unusedVariables false

/-!
## Triangle Expansion
-/

/-- Expands the cubic statistic as an explicit sum over ordered triangles. -/
theorem triangle_formula (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    cubicT n lam = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      if i < j ∧ j < k then lam i j * lam i k * lam j k else 0 := rfl

private lemma edgeLam_singleEdgeLam {n : ℕ} {u v : Fin n} (huv : u < v) :
    edgeLam n (singleEdgeLam u v)
      = fun e : Cn3Torus.Edge n => if e = ⟨(u, v), huv⟩ then 1 else 0 := by
  funext e
  rcases e with ⟨⟨i, j⟩, hij⟩
  by_cases he : (⟨(i, j), hij⟩ : Cn3Torus.Edge n) = ⟨(u, v), huv⟩
  · cases he
    simp [edgeLam, singleEdgeLam]
  · have hneq : ¬ (i = u ∧ j = v) := by
      intro hp
      apply he
      rcases hp with ⟨rfl, rfl⟩
      rfl
    simp [edgeLam, singleEdgeLam, hneq, he]

private lemma innerX_add (n : ℕ) (lam gam : Fin n → Fin n → ℝ) (σ : Fin n → Fin 2) :
    innerX n (fun i j => lam i j + gam i j) σ = innerX n lam σ + innerX n gam σ := by
  unfold innerX
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        if i < j then (lam i j + gam i j) * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0)
        =
      ∑ i : Fin n, ∑ j : Fin n,
        ((if i < j then lam i j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0)
          + (if i < j then gam i j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases hij : i < j
            · simp [hij, add_mul]
            · simp [hij]
    _ = (∑ i : Fin n, ∑ j : Fin n,
          if i < j then lam i j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0)
        + (∑ i : Fin n, ∑ j : Fin n,
            if i < j then gam i j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0) := by
              calc
                (∑ i : Fin n, ∑ j : Fin n,
                    ((if i < j then lam i j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0)
                      + (if i < j then gam i j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0)))
                    =
                  ∑ i : Fin n,
                    ((∑ j : Fin n,
                        if i < j then lam i j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0)
                      + (∑ j : Fin n,
                          if i < j then gam i j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0)) := by
                            refine Finset.sum_congr rfl ?_
                            intro i hi
                            rw [Finset.sum_add_distrib]
                _ = (∑ i : Fin n, ∑ j : Fin n,
                      if i < j then lam i j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0)
                    + (∑ i : Fin n, ∑ j : Fin n,
                        if i < j then gam i j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0) := by
                          rw [Finset.sum_add_distrib]

private lemma innerX_singleEdgeLam {n : ℕ} {u v : Fin n} (huv : u < v) (σ : Fin n → Fin 2) :
    innerX n (singleEdgeLam u v) σ = (signOf (σ u) : ℝ) * (signOf (σ v) : ℝ) := by
  rw [innerX_eq_edgePhase, edgeLam_singleEdgeLam huv]
  unfold Cn3Torus.phase
  simp [signVecToBoolVec, Cn3Torus.Z, spin_fin2ToBool_eq_signOf]

private lemma momentX_three_add_singleEdge (n : ℕ) (B : Fin n → Fin n → ℝ) {u v : Fin n}
    (huv : u < v) :
    momentX n (fun i j => B i j + singleEdgeLam u v i j) 3
      = momentX n B 3
          + 3 * avgSigns n
              (fun σ =>
                innerX n B σ ^ (2 : Nat)
                  * (signOf (σ u) : ℝ) * (signOf (σ v) : ℝ)) := by
  have hpoint :
      (fun σ => innerX n (fun i j => B i j + singleEdgeLam u v i j) σ ^ (3 : Nat))
        =
      (fun σ =>
        innerX n B σ ^ (3 : Nat)
          + 3 * (innerX n B σ ^ (2 : Nat)
              * ((signOf (σ u) : ℝ) * (signOf (σ v) : ℝ)))
          + 3 * innerX n B σ
          + ((signOf (σ u) : ℝ) * (signOf (σ v) : ℝ))) := by
    funext σ
    let z : ℝ := (signOf (σ u) : ℝ) * (signOf (σ v) : ℝ)
    have hz2 : z ^ (2 : Nat) = 1 := by
      calc
        z ^ (2 : Nat)
            = (signOf (σ u) : ℝ) ^ (2 : Nat) * (signOf (σ v) : ℝ) ^ (2 : Nat) := by
                unfold z
                ring
        _ = 1 := by simp [signOf_sq]
    have hz3 : z ^ (3 : Nat) = z := by
      calc
        z ^ (3 : Nat) = z * z ^ (2 : Nat) := by ring
        _ = z := by rw [hz2]; ring
    rw [innerX_add, innerX_singleEdgeLam huv]
    calc
      (innerX n B σ + z) ^ (3 : Nat)
          = innerX n B σ ^ (3 : Nat)
              + 3 * innerX n B σ ^ (2 : Nat) * z
              + 3 * innerX n B σ * z ^ (2 : Nat)
              + z ^ (3 : Nat) := by ring
      _ =
          innerX n B σ ^ (3 : Nat)
            + 3 * (innerX n B σ ^ (2 : Nat) * z)
            + 3 * innerX n B σ
            + z := by rw [hz2, hz3]; ring
  have hm1 : avgSigns n (fun σ => innerX n B σ) = 0 := by
    unfold avgSigns
    simpa [momentX] using momentX_one_eq_zero n B
  have hpair_zero : avgSigns n (fun σ => (signOf (σ u) : ℝ) * (signOf (σ v) : ℝ)) = 0 := by
    unfold avgSigns
    simpa [momentX, innerX_singleEdgeLam huv] using
      momentX_one_eq_zero n (singleEdgeLam u v)
  change avgSigns n (fun σ => innerX n (fun i j => B i j + singleEdgeLam u v i j) σ ^ (3 : Nat))
      = momentX n B 3
          + 3 * avgSigns n
              (fun σ =>
                innerX n B σ ^ (2 : Nat)
                  * (signOf (σ u) : ℝ) * (signOf (σ v) : ℝ))
  rw [hpoint, avgSigns_add, avgSigns_add, avgSigns_add, avgSigns_mul_const_left,
    avgSigns_mul_const_left, hm1, hpair_zero]
  unfold momentX avgSigns
  ring_nf

private lemma cubicT_singleEdgeDiff_eq_triangleThroughPair (n : ℕ) (B : Fin n → Fin n → ℝ)
    {u v : Fin n} (huv : u < v) :
    cubicT n (fun i j => B i j + singleEdgeLam u v i j) - cubicT n B
      = triangleThroughPair n B u v := by
  rw [triangle_formula, triangle_formula]
  let bump : Fin n → Fin n → Fin n → ℝ :=
    fun i j k =>
      if i < j ∧ j < k then
        (B i j + singleEdgeLam u v i j) * (B i k + singleEdgeLam u v i k) *
          (B j k + singleEdgeLam u v j k)
      else 0
  let base : Fin n → Fin n → Fin n → ℝ :=
    fun i j k => if i < j ∧ j < k then B i j * B i k * B j k else 0
  have hterm :
      ∀ i j k : Fin n,
        bump i j k - base i j k
          =
        (if i = u ∧ j = v ∧ v < k then B u k * B v k else 0)
          + (if i = u ∧ k = v ∧ u < j ∧ j < v then B u j * B j v else 0)
          + (if j = u ∧ k = v ∧ i < u then B i u * B i v else 0) := by
    intro i j k
    by_cases hijk : i < j ∧ j < k
    · by_cases hijuv : i = u ∧ j = v
      · have hikuv : ¬ (i = u ∧ k = v) := by
          intro hikuv
          rcases hijuv with ⟨hi, hj⟩
          rcases hikuv with ⟨_, hk⟩
          have hEq : j = k := by rw [hj, hk]
          exact (ne_of_lt hijk.2) hEq
        have hjkuv : ¬ (j = u ∧ k = v) := by
          intro hjkuv
          rcases hijuv with ⟨_, hj⟩
          rcases hjkuv with ⟨hj', hk⟩
          have hEq : u = v := by rw [← hj', hj]
          exact (ne_of_lt huv) hEq
        rcases hijuv with ⟨hi, hj⟩
        subst i
        subst j
        have hvk : v < k := hijk.2
        have hkv : k ≠ v := ne_of_gt hvk
        simp [bump, base, singleEdgeLam, huv, hvk, hkv, hikuv, hjkuv]
        ring_nf
      · by_cases hikuv : i = u ∧ k = v
        · have hjkuv : ¬ (j = u ∧ k = v) := by
            intro hjkuv
            rcases hikuv with ⟨hi, _⟩
            rcases hjkuv with ⟨hj, _⟩
            have hEq : i = j := by rw [hi, hj]
            exact (ne_of_lt hijk.1) hEq
          rcases hikuv with ⟨hi, hk⟩
          subst i
          subst k
          have huj : u < j := hijk.1
          have hjv : j < v := hijk.2
          have hju : j ≠ u := ne_of_gt huj
          have hjv_ne : j ≠ v := ne_of_lt hjv
          simp [bump, base, singleEdgeLam, huv, huj, hjv, hju, hjv_ne, hijuv, hjkuv]
          ring_nf
        · by_cases hjkuv : j = u ∧ k = v
          · rcases hjkuv with ⟨hj, hk⟩
            subst j
            subst k
            have hiu : i < u := hijk.1
            have hiu_ne : i ≠ u := ne_of_lt hiu
            simp [bump, base, singleEdgeLam, huv, hiu, hiu_ne, hijuv, hikuv]
            ring_nf
          · have hcase1 : ¬ (i = u ∧ j = v ∧ v < k) := by
              intro hcase1
              exact hijuv ⟨hcase1.1, hcase1.2.1⟩
            have hcase2 : ¬ (i = u ∧ k = v ∧ u < j ∧ j < v) := by
              intro hcase2
              exact hikuv ⟨hcase2.1, hcase2.2.1⟩
            have hcase3 : ¬ (j = u ∧ k = v ∧ i < u) := by
              intro hcase3
              exact hjkuv ⟨hcase3.1, hcase3.2.1⟩
            simp [bump, base, hijk, hcase1, hcase2, hcase3, singleEdgeLam, hijuv, hikuv, hjkuv]
    · have hcase1 : ¬ (i = u ∧ j = v ∧ v < k) := by
        intro hcase1
        rcases hcase1 with ⟨hi, hj, hvk⟩
        subst hi hj
        exact hijk ⟨huv, hvk⟩
      have hcase2 : ¬ (i = u ∧ k = v ∧ u < j ∧ j < v) := by
        intro hcase2
        rcases hcase2 with ⟨hi, hk, huj, hjv⟩
        subst hi hk
        exact hijk ⟨huj, hjv⟩
      have hcase3 : ¬ (j = u ∧ k = v ∧ i < u) := by
        intro hcase3
        rcases hcase3 with ⟨hj, hk, hiu⟩
        subst hj hk
        exact hijk ⟨hiu, huv⟩
      simp [bump, base, hijk, hcase1, hcase2, hcase3]
  calc
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, bump i j k)
        - (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, base i j k)
      = ∑ i : Fin n, ((∑ j : Fin n, ∑ k : Fin n, bump i j k) - ∑ j : Fin n, ∑ k : Fin n, base i j k) := by
          rw [← Finset.sum_sub_distrib]
    _ = ∑ i : Fin n, ∑ j : Fin n, ((∑ k : Fin n, bump i j k) - ∑ k : Fin n, base i j k) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [← Finset.sum_sub_distrib]
    _ = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (bump i j k - base i j k) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [← Finset.sum_sub_distrib]
    _ =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        ((if i = u ∧ j = v ∧ v < k then B u k * B v k else 0)
          + (if i = u ∧ k = v ∧ u < j ∧ j < v then B u j * B j v else 0)
          + (if j = u ∧ k = v ∧ i < u then B i u * B i v else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact hterm i j k
    _ =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if i = u ∧ j = v ∧ v < k then B u k * B v k else 0)
        + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            if i = u ∧ k = v ∧ u < j ∧ j < v then B u j * B j v else 0)
        + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            if j = u ∧ k = v ∧ i < u then B i u * B i v else 0) := by
              calc
                (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                    (((if i = u ∧ j = v ∧ v < k then B u k * B v k else 0)
                        + (if i = u ∧ k = v ∧ u < j ∧ j < v then B u j * B j v else 0))
                      + (if j = u ∧ k = v ∧ i < u then B i u * B i v else 0)))
                    =
                  ∑ i : Fin n, ∑ j : Fin n,
                    (((∑ k : Fin n, if i = u ∧ j = v ∧ v < k then B u k * B v k else 0)
                        + (∑ k : Fin n, if i = u ∧ k = v ∧ u < j ∧ j < v then B u j * B j v else 0))
                      + (∑ k : Fin n, if j = u ∧ k = v ∧ i < u then B i u * B i v else 0)) := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        refine Finset.sum_congr rfl ?_
                        intro j hj
                        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                _ =
                  ∑ i : Fin n,
                    (((∑ j : Fin n, ∑ k : Fin n,
                          if i = u ∧ j = v ∧ v < k then B u k * B v k else 0)
                        + (∑ j : Fin n, ∑ k : Fin n,
                            if i = u ∧ k = v ∧ u < j ∧ j < v then B u j * B j v else 0))
                      + (∑ j : Fin n, ∑ k : Fin n,
                          if j = u ∧ k = v ∧ i < u then B i u * B i v else 0)) := by
                            refine Finset.sum_congr rfl ?_
                            intro i hi
                            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                _ =
                  (((∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                        if i = u ∧ j = v ∧ v < k then B u k * B v k else 0)
                      + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                          if i = u ∧ k = v ∧ u < j ∧ j < v then B u j * B j v else 0))
                    + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                        if j = u ∧ k = v ∧ i < u then B i u * B i v else 0)) := by
                          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                _ =
                  (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                      if i = u ∧ j = v ∧ v < k then B u k * B v k else 0)
                    + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                        if i = u ∧ k = v ∧ u < j ∧ j < v then B u j * B j v else 0)
                    + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                        if j = u ∧ k = v ∧ i < u then B i u * B i v else 0) := by
                          ring
    _ = triangleThroughPair n B u v := by
          classical
          have h1 :
              (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                  if i = u ∧ j = v ∧ v < k then B u k * B v k else 0)
                = ∑ k : Fin n, if v < k then B u k * B v k else 0 := by
            rw [Finset.sum_eq_single_of_mem u (by simp)]
            · rw [Finset.sum_eq_single_of_mem v (by simp)]
              · simp
              · intro j hj hjv
                simp [hjv]
            · intro i hi hiu
              simp [hiu]
          have h2 :
              (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                  if i = u ∧ k = v ∧ u < j ∧ j < v then B u j * B j v else 0)
                = ∑ j : Fin n, if u < j ∧ j < v then B u j * B j v else 0 := by
            rw [Finset.sum_eq_single_of_mem u (by simp)]
            · refine Finset.sum_congr rfl ?_
              intro j hj
              rw [Finset.sum_eq_single_of_mem v (by simp)]
              · simp
              · intro k hk hkv
                simp [hkv]
            · intro i hi hiu
              simp [hiu]
          have h3 :
              (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                  if j = u ∧ k = v ∧ i < u then B i u * B i v else 0)
                = ∑ i : Fin n, if i < u then B i u * B i v else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.sum_eq_single_of_mem u (by simp)]
            · rw [Finset.sum_eq_single_of_mem v (by simp)]
              · simp
              · intro k hk hkv
                simp [hkv]
            · intro j hj hju
              simp [hju]
          rw [h1, h2, h3]
          unfold triangleThroughPair
          ring

private lemma avgSigns_innerX_sq_mul_signPair (n : ℕ) (B : Fin n → Fin n → ℝ) {u v : Fin n}
    (huv : u < v) :
    avgSigns n
        (fun σ =>
          innerX n B σ ^ (2 : Nat) * (signOf (σ u) : ℝ) * (signOf (σ v) : ℝ))
      = 2 * triangleThroughPair n B u v := by
  let B' : Fin n → Fin n → ℝ := fun i j => B i j + singleEdgeLam u v i j
  have hmoment : momentX n B' 3
      = momentX n B 3
          + 3 * avgSigns n
              (fun σ =>
                innerX n B σ ^ (2 : Nat) * (signOf (σ u) : ℝ) * (signOf (σ v) : ℝ)) :=
    momentX_three_add_singleEdge n B huv
  have hcubic :
      momentX n B' 3 = momentX n B 3 + 6 * triangleThroughPair n B u v := by
    rw [momentX_three_eq_six_cubicT, momentX_three_eq_six_cubicT]
    have hdiff : cubicT n B' - cubicT n B = triangleThroughPair n B u v := by
      simpa [B'] using cubicT_singleEdgeDiff_eq_triangleThroughPair n B huv
    linarith
  linarith

lemma pair_triangleThroughPair_eq_simpleCycle4LastCross (n : ℕ) (B : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j * triangleThroughPair n B i j else 0)
      = simpleCycle4LastCross n B x := by
  have hpoint :
      ∀ i j : Fin n,
        (if i < j then x i * x j * triangleThroughPair n B i j else 0)
          =
        (∑ k : Fin n, if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
          + (∑ k : Fin n, if i < k ∧ k < j then B i k * B k j * x i * x j else 0)
          + (∑ k : Fin n, if i < j ∧ j < k then B i k * B j k * x i * x j else 0) := by
    intro i j
    by_cases hij : i < j
    · rw [if_pos hij]
      unfold triangleThroughPair
      have h1 :
          x i * x j * (∑ k : Fin n, if k < i then B k i * B k j else 0)
            = ∑ k : Fin n, if k < i then B k i * B k j * x i * x j else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        by_cases hki : k < i
        · simp [hki]
          ring
        · simp [hki]
      have h2 :
          x i * x j * (∑ k : Fin n, if i < k ∧ k < j then B i k * B k j else 0)
            = ∑ k : Fin n, if i < k ∧ k < j then B i k * B k j * x i * x j else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        by_cases hikj : i < k ∧ k < j
        · simp [hikj]
          ring
        · simp [hikj]
      have h3 :
          x i * x j * (∑ k : Fin n, if j < k then B i k * B j k else 0)
            = ∑ k : Fin n, if j < k then B i k * B j k * x i * x j else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        by_cases hjk : j < k
        · simp [hjk]
          ring
        · simp [hjk]
      calc
        x i * x j *
            ((∑ k : Fin n, if k < i then B k i * B k j else 0)
              + (∑ k : Fin n, if i < k ∧ k < j then B i k * B k j else 0)
              + (∑ k : Fin n, if j < k then B i k * B j k else 0))
            =
          (x i * x j * (∑ k : Fin n, if k < i then B k i * B k j else 0))
            + ((x i * x j * (∑ k : Fin n, if i < k ∧ k < j then B i k * B k j else 0))
              + (x i * x j * (∑ k : Fin n, if j < k then B i k * B j k else 0))) := by
              ring
        _ =
          (∑ k : Fin n, if k < i then B k i * B k j * x i * x j else 0)
            + ((∑ k : Fin n, if i < k ∧ k < j then B i k * B k j * x i * x j else 0)
              + (∑ k : Fin n, if j < k then B i k * B j k * x i * x j else 0)) := by
              rw [h1, h2, h3]
        _ =
          (∑ k : Fin n, if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
            + (∑ k : Fin n, if i < k ∧ k < j then B i k * B k j * x i * x j else 0)
            + (∑ k : Fin n, if i < j ∧ j < k then B i k * B j k * x i * x j else 0) := by
              simp [hij, and_assoc, add_assoc]
    · have h1 : ∀ k : Fin n, ¬ (k < i ∧ i < j) := by
        intro k hk
        exact hij hk.2
      have h2 : ∀ k : Fin n, ¬ (i < k ∧ k < j) := by
        intro k hk
        exact hij (lt_trans hk.1 hk.2)
      have h3 : ∀ k : Fin n, ¬ (i < j ∧ j < k) := by
        intro k hk
        exact hij hk.1
      simp [hij, h1, h2, h3]
  have hsplit :
      (∑ i : Fin n, ∑ j : Fin n,
          ((∑ k : Fin n, if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
            + (∑ k : Fin n, if i < k ∧ k < j then B i k * B k j * x i * x j else 0)
            + (∑ k : Fin n, if i < j ∧ j < k then B i k * B j k * x i * x j else 0)))
        =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
        + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            if i < k ∧ k < j then B i k * B k j * x i * x j else 0)
        + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            if i < j ∧ j < k then B i k * B j k * x i * x j else 0) := by
    calc
      (∑ i : Fin n, ∑ j : Fin n,
          ((∑ k : Fin n, if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
            + (∑ k : Fin n, if i < k ∧ k < j then B i k * B k j * x i * x j else 0)
            + (∑ k : Fin n, if i < j ∧ j < k then B i k * B j k * x i * x j else 0)))
          =
        ∑ i : Fin n, ∑ j : Fin n,
          (((∑ k : Fin n, if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
              + (∑ k : Fin n, if i < k ∧ k < j then B i k * B k j * x i * x j else 0))
            + (∑ k : Fin n, if i < j ∧ j < k then B i k * B j k * x i * x j else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ =
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
          + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
              if i < k ∧ k < j then B i k * B k j * x i * x j else 0)
          + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
              if i < j ∧ j < k then B i k * B j k * x i * x j else 0) := by
                calc
                  (∑ i : Fin n, ∑ j : Fin n,
                      (((∑ k : Fin n, if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
                          + (∑ k : Fin n, if i < k ∧ k < j then B i k * B k j * x i * x j else 0))
                        + (∑ k : Fin n, if i < j ∧ j < k then B i k * B j k * x i * x j else 0)))
                      =
                    ∑ i : Fin n,
                      (((∑ j : Fin n, ∑ k : Fin n,
                            if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
                          + (∑ j : Fin n, ∑ k : Fin n,
                              if i < k ∧ k < j then B i k * B k j * x i * x j else 0))
                        + (∑ j : Fin n, ∑ k : Fin n,
                            if i < j ∧ j < k then B i k * B j k * x i * x j else 0)) := by
                              refine Finset.sum_congr rfl ?_
                              intro i hi
                              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                  _ = ((∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                            if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
                        + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                            if i < k ∧ k < j then B i k * B k j * x i * x j else 0))
                      + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                          if i < j ∧ j < k then B i k * B j k * x i * x j else 0) := by
                            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                  _ =
                    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                        if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
                      + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                          if i < k ∧ k < j then B i k * B k j * x i * x j else 0)
                      + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                          if i < j ∧ j < k then B i k * B j k * x i * x j else 0) := by
                            ring
  have hA :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
        =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        if i < j ∧ j < k then B i j * x j * x k * B i k else 0 := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
          =
        ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
          if k < i ∧ i < j then B k i * B k j * x i * x j else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.sum_comm]
      _ =
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if i < j ∧ j < k then B i j * x j * x k * B i k else 0 := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            refine Finset.sum_congr rfl ?_
            intro k hk
            by_cases hijk : i < j ∧ j < k
            · simp [hijk, mul_comm, mul_left_comm, mul_assoc]
            · simp [hijk]
  have hB :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if i < k ∧ k < j then B i k * B k j * x i * x j else 0)
        =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        if i < j ∧ j < k then B i j * B j k * x k * x i else 0 := by
    calc
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if i < k ∧ k < j then B i k * B k j * x i * x j else 0)
          =
        ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
          if i < k ∧ k < j then B i k * B k j * x i * x j else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [Finset.sum_comm]
      _ =
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if i < j ∧ j < k then B i j * B j k * x k * x i else 0 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            refine Finset.sum_congr rfl ?_
            intro k hk
            by_cases hijk : i < j ∧ j < k
            · simp [hijk, mul_comm, mul_left_comm, mul_assoc]
            · simp [hijk]
  have hC :
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if i < j ∧ j < k then B i k * B j k * x i * x j else 0)
        =
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        if i < j ∧ j < k then B i k * B j k * x j * x i else 0 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine Finset.sum_congr rfl ?_
    intro j hj
    refine Finset.sum_congr rfl ?_
    intro k hk
    by_cases hijk : i < j ∧ j < k
    · simp [hijk, mul_comm, mul_left_comm, mul_assoc]
    · simp [hijk]
  have hcross :
      simpleCycle4LastCross n B x
        =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if i < j ∧ j < k then B i j * B j k * x k * x i else 0)
        + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            if i < j ∧ j < k then B i j * x j * x k * B i k else 0)
        + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            if i < j ∧ j < k then B i k * B j k * x j * x i else 0) := by
    unfold simpleCycle4LastCross
    calc
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if i < j ∧ j < k then
            B i j * B j k * x k * x i + B i j * x j * x k * B i k + B i k * B j k * x j * x i
          else 0)
          =
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (((if i < j ∧ j < k then B i j * B j k * x k * x i else 0)
              + (if i < j ∧ j < k then B i j * x j * x k * B i k else 0))
            + (if i < j ∧ j < k then B i k * B j k * x j * x i else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              refine Finset.sum_congr rfl ?_
              intro k hk
              by_cases hijk : i < j ∧ j < k
              · simp [hijk]
              · simp [hijk]
      _ =
        (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            if i < j ∧ j < k then B i j * B j k * x k * x i else 0)
          + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
              if i < j ∧ j < k then B i j * x j * x k * B i k else 0)
          + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
              if i < j ∧ j < k then B i k * B j k * x j * x i else 0) := by
                calc
                  (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                      (((if i < j ∧ j < k then B i j * B j k * x k * x i else 0)
                          + (if i < j ∧ j < k then B i j * x j * x k * B i k else 0))
                        + (if i < j ∧ j < k then B i k * B j k * x j * x i else 0)))
                      =
                    ∑ i : Fin n, ∑ j : Fin n,
                      (((∑ k : Fin n, if i < j ∧ j < k then B i j * B j k * x k * x i else 0)
                          + (∑ k : Fin n, if i < j ∧ j < k then B i j * x j * x k * B i k else 0))
                        + (∑ k : Fin n, if i < j ∧ j < k then B i k * B j k * x j * x i else 0)) := by
                              refine Finset.sum_congr rfl ?_
                              intro i hi
                              refine Finset.sum_congr rfl ?_
                              intro j hj
                              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                  _ =
                    ∑ i : Fin n,
                      (((∑ j : Fin n, ∑ k : Fin n,
                            if i < j ∧ j < k then B i j * B j k * x k * x i else 0)
                          + (∑ j : Fin n, ∑ k : Fin n,
                              if i < j ∧ j < k then B i j * x j * x k * B i k else 0))
                        + (∑ j : Fin n, ∑ k : Fin n,
                            if i < j ∧ j < k then B i k * B j k * x j * x i else 0)) := by
                              refine Finset.sum_congr rfl ?_
                              intro i hi
                              rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                  _ =
                    ((∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                        if i < j ∧ j < k then B i j * B j k * x k * x i else 0)
                      + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                          if i < j ∧ j < k then B i j * x j * x k * B i k else 0))
                      + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                          if i < j ∧ j < k then B i k * B j k * x j * x i else 0) := by
                            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
                  _ =
                    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                        if i < j ∧ j < k then B i j * B j k * x k * x i else 0)
                      + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                          if i < j ∧ j < k then B i j * x j * x k * B i k else 0)
                      + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
                          if i < j ∧ j < k then B i k * B j k * x j * x i else 0) := by
                            ring
  calc
    (∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j * triangleThroughPair n B i j else 0)
        =
      ∑ i : Fin n, ∑ j : Fin n,
        ((∑ k : Fin n, if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
          + (∑ k : Fin n, if i < k ∧ k < j then B i k * B k j * x i * x j else 0)
          + (∑ k : Fin n, if i < j ∧ j < k then B i k * B j k * x i * x j else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            exact hpoint i j
    _ =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if k < i ∧ i < j then B k i * B k j * x i * x j else 0)
        + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            if i < k ∧ k < j then B i k * B k j * x i * x j else 0)
        + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            if i < j ∧ j < k then B i k * B j k * x i * x j else 0) := hsplit
    _ =
      (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          if i < j ∧ j < k then B i j * B j k * x k * x i else 0)
        + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            if i < j ∧ j < k then B i j * x j * x k * B i k else 0)
        + (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
            if i < j ∧ j < k then B i k * B j k * x j * x i else 0) := by
              rw [hA, hB, hC]
              ring
    _ = simpleCycle4LastCross n B x := by
          simpa [add_assoc] using hcross.symm

private lemma avgSigns_innerX_sq_mul_linearX_sq (n : ℕ) (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    avgSigns n
        (fun σ => innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (2 : Nat))
      = sNorm n B * ∑ i : Fin n, x i ^ (2 : Nat) + 4 * simpleCycle4LastCross n B x := by
  let s : ℝ := ∑ i : Fin n, x i ^ (2 : Nat)
  let off : (Fin n → Fin 2) → ℝ :=
    fun σ =>
      ∑ i : Fin n, ∑ j : Fin n,
        if i < j then
          innerX n B σ ^ (2 : Nat) * x i * x j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ)
        else 0
  have hpoint :
      (fun σ => innerX n B σ ^ (2 : Nat) * linearX n x σ ^ (2 : Nat))
        =
      (fun σ => s * innerX n B σ ^ (2 : Nat) + 2 * off σ) := by
    funext σ
    rw [linearX_sq_eq_diag_add_offdiag]
    dsimp [s, off]
    have hmul :
        innerX n B σ ^ (2 : Nat)
            * (∑ i : Fin n, ∑ j : Fin n,
                if i < j then x i * x j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0)
          =
        ∑ i : Fin n, ∑ j : Fin n,
          if i < j then
            innerX n B σ ^ (2 : Nat) * x i * x j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ)
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
      innerX n B σ ^ (2 : Nat)
          * ((∑ i : Fin n, x i ^ (2 : Nat))
              + 2 * (∑ i : Fin n, ∑ j : Fin n,
                  if i < j then x i * x j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0))
          =
        s * innerX n B σ ^ (2 : Nat)
          + 2 * (innerX n B σ ^ (2 : Nat)
              * (∑ i : Fin n, ∑ j : Fin n,
                  if i < j then x i * x j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ) else 0)) := by
                    ring
      _ =
        s * innerX n B σ ^ (2 : Nat)
          + 2 * (∑ i : Fin n, ∑ j : Fin n,
              if i < j then
                innerX n B σ ^ (2 : Nat) * x i * x j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ)
              else 0) := by
                rw [hmul]
      _ = s * innerX n B σ ^ (2 : Nat) + 2 * off σ := by
            rfl
  have hsecond :
      avgSigns n (fun σ => innerX n B σ ^ (2 : Nat)) = sNorm n B := by
    unfold avgSigns
    simpa [momentX] using momentX_two_eq_sNorm n B
  have hoff_expand :
      avgSigns n off
        = ∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j * (2 * triangleThroughPair n B i j) else 0 := by
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
            innerX n B σ ^ (2 : Nat) * x i * x j * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ))
            =
          (fun σ =>
            (x i * x j)
              * (innerX n B σ ^ (2 : Nat) * (signOf (σ i) : ℝ) * (signOf (σ j) : ℝ))) := by
                funext σ
                ring
      rw [hfun, avgSigns_mul_const_left, avgSigns_innerX_sq_mul_signPair n B hij]
    · simp [hij, avgSigns_const]
  have hoff :
      avgSigns n off = 2 * simpleCycle4LastCross n B x := by
    calc
      avgSigns n off
          = ∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j * (2 * triangleThroughPair n B i j) else 0 := hoff_expand
      _ = ∑ i : Fin n, ∑ j : Fin n, 2 * (if i < j then x i * x j * triangleThroughPair n B i j else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            refine Finset.sum_congr rfl ?_
            intro j hj
            by_cases hij : i < j
            · simp [hij]
              ring
            · simp [hij]
      _ = ∑ i : Fin n, 2 * (∑ j : Fin n, if i < j then x i * x j * triangleThroughPair n B i j else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [← Finset.mul_sum]
      _ = 2 * (∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j * triangleThroughPair n B i j else 0) := by
            rw [← Finset.mul_sum]
      _ = 2 * simpleCycle4LastCross n B x := by
            rw [pair_triangleThroughPair_eq_simpleCycle4LastCross]
  rw [hpoint, avgSigns_add, avgSigns_mul_const_left, avgSigns_mul_const_left, hsecond, hoff]
  ring

/-- **Fourth cumulant identity**: κ₄/24 = Q₄^corr(λ).
    The fourth cumulant κ₄ = μ₄ - 3μ₂² = μ₄ - 3s², and
    κ₄/24 = (μ₄ - 3s²)/24 = Q₄^corr. -/
theorem fourth_cumulant_identity (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    ((momentX n lam 4 - 3 * sNorm n lam ^ (2 : Nat)) / 24 : ℝ) = quarticCorr n lam := by
  apply fourth_cumulant_identity_of_mixed_peel
  intro n lam
  simpa using avgSigns_innerX_sq_mul_linearX_sq n (minorLamLast lam) (lastColLam lam)

/-!
## Fourth-Moment and Gaussian Bounds
-/

/-
PROBLEM
Helper: Real logarithm near 1. For |u| ≤ 1/2: |log(1+u) - u| ≤ 2u².

PROVIDED SOLUTION
For |u| ≤ 1/2, we have 1+u ≥ 1/2 > 0, so log(1+u) is well-defined.

Use the fact that log(1+u) = u - u²/2 + u³/3 - ... (Taylor series).
The remainder after the linear term is bounded by:
|log(1+u) - u| ≤ u²/(2(1-|u|)) ≤ u²/(2·(1/2)) = u²

More precisely, for u ≥ 0: log(1+u) ≤ u (standard inequality), and
log(1+u) ≥ u - u²/2 (from log(1+u) ≥ u - u²/(2(1-u)) for 0 ≤ u < 1).

For u < 0 with |u| ≤ 1/2: similar but we use -log(1-|u|) ≤ |u| + |u|²/(1-|u|).

Actually, the simplest approach: use Real.abs_log_sub_add_one_le or a similar Mathlib lemma if it exists. Or use the inequality:
|log(1+u) - u| ≤ u²/(1-|u|) ≤ u²/(1/2) = 2u²

This follows from: log(1+u) = ∫₀ᵘ 1/(1+t) dt, so
log(1+u) - u = ∫₀ᵘ (1/(1+t) - 1) dt = -∫₀ᵘ t/(1+t) dt.
|log(1+u) - u| ≤ ∫₀^|u| |t|/(1-|t|) dt ≤ (1/(1-|u|)) ∫₀^|u| t dt = |u|²/(2(1-|u|)) ≤ |u|²/(2·1/2) = u².
-/
theorem complex_re_abs_le_norm (z : ℂ) : |z.re| ≤ ‖z‖ := by
  have hsq : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  have := (sq_le_sq).mp hsq
  simpa [abs_of_nonneg (norm_nonneg _)] using this

theorem complex_im_abs_le_norm (z : ℂ) : |z.im| ≤ ‖z‖ := by
  have hsq : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  have := (sq_le_sq).mp hsq
  simpa [abs_of_nonneg (norm_nonneg _)] using this

theorem complex_log_approx_quadratic (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 + z) - z + z ^ 2 / 2‖ ≤ ‖z‖ ^ 3 := by
  have hnorm : ‖z‖ < 1 := by
    exact lt_of_le_of_lt hz (by norm_num : (1 / 2 : ℝ) < 1)
  have h :=
    Complex.norm_log_sub_logTaylor_le 2 hnorm
  norm_num at h
  have htaylor : Complex.logTaylor 3 z = z - z ^ 2 / 2 := by
    rw [Complex.logTaylor_succ, Complex.logTaylor_succ, Complex.logTaylor_succ, Complex.logTaylor_zero]
    ring_nf
    norm_num
  have h' : ‖Complex.log (1 + z) - z + z ^ 2 / 2‖ ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 := by
    convert h using 2
    rw [htaylor]
    ring
  refine le_trans h' ?_
  have h_inv : (1 - ‖z‖)⁻¹ ≤ (2 : ℝ) := by
    have hpos : 0 < 1 - ‖z‖ := by
      nlinarith
    have : 1 / (1 - ‖z‖) ≤ (2 : ℝ) := by
      rw [div_le_iff₀]
      · nlinarith
      · exact hpos
    simpa [one_div] using this
  have hpow_nonneg : 0 ≤ ‖z‖ ^ 3 := by positivity
  have hmain : ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 ≤ ‖z‖ ^ 3 := by
    nlinarith
  exact hmain

/-
PROBLEM
**Lemma 4.5** (Inner-core Gaussian mass):
    G_core(d,t) ≥ (1 - e^{-c*d}) F(d,t) for c* = 1 - (log 2)/2.

    Proof: coreMass = F - tail. On {‖x‖² > d/t}: e^{-2t‖x‖²} ≤ e^{-d}·e^{-t‖x‖²}.
    So tail ≤ e^{-d}·∫e^{-t‖x‖²} = e^{-d}·(π/t)^{d/2} = e^{-d}·2^{d/2}·F.
    Hence coreMass ≥ F·(1 - e^{-d}·2^{d/2}) = F·(1 - e^{-d(1 - log2/2)}).

PROVIDED SOLUTION
Use c_star = 1/2.

The proof idea:
coreMass d t is the integral of e^{-2t‖x‖²} over {‖x‖² ≤ d/t}.
gaussianF d t = (π/(2t))^{d/2} is the full Gaussian integral.

We need coreMass ≥ (1 - e^{-d/2}) · gaussianF.

Step 1: The full integral: by gaussian_integral_formula with a = 2t:
∫ e^{-2t‖x‖²} dx = (π/(2t))^{d/2} = gaussianF d t.

Step 2: coreMass + tailMass = gaussianF, where tailMass is the tail integral.
This follows from: for any measurable function f ≥ 0,
∫ f·1_S + ∫ f·1_{S^c} = ∫ f.

So coreMass = gaussianF - tailMass ≥ gaussianF - tailBound.

Step 3: By gaussian_tail_factoring:
tailMass ≤ e^{-d} · (π/t)^{d/2}.

Step 4: (π/t)^{d/2} = (2·π/(2t))^{d/2} = 2^{d/2} · (π/(2t))^{d/2} = 2^{d/2} · gaussianF.
So tailMass ≤ e^{-d} · 2^{d/2} · gaussianF.

Step 5: e^{-d} · 2^{d/2} = e^{-d + (d/2)·ln2} = e^{-d(1 - ln2/2)}.
Since 1 - ln2/2 > 1/2 (because ln2 < 1), we have e^{-d(1-ln2/2)} ≤ e^{-d/2}.

Step 6: So coreMass ≥ gaussianF - e^{-d/2} · gaussianF = (1 - e^{-d/2}) · gaussianF.
This gives the result with c_star = 1/2.
-/
theorem inner_core_gaussian_mass :
    ∃ c_star : ℝ, 0 < c_star ∧ ∀ (d : ℕ) (t : ℝ),
      1 ≤ t → coreMass d t ≥ (1 - Real.exp (-(c_star * ↑d))) * gaussianF d t := by
        use 1 / 2, by norm_num, ?_;
        intro d t ht
        have h_coreMass_ge : coreMass d t ≥ gaussianF d t - Real.exp (-d) * (2 ^ (d / 2 : ℝ)) * gaussianF d t := by
          have h_coreMass_ge : coreMass d t ≥ gaussianF d t - Real.exp (-d) * (Real.pi / t) ^ ((d : ℝ) / 2) := by
            have h_coreMass_ge : coreMass d t = gaussianF d t - ∫ x : Fin d → ℝ,
              Set.indicator {x : Fin d → ℝ | ∑ i, x i ^ 2 > (d : ℝ) / t}
                (fun x => Real.exp (-2 * t * ∑ i, x i ^ 2)) x := by
                  unfold coreMass gaussianF;
                  rw [ eq_sub_iff_add_eq', ← MeasureTheory.integral_add ];
                  · convert gaussian_integral_formula d ( 2 * t ) ( by positivity ) using 1;
                    congr with x ; by_cases hx : ∑ i, x i ^ 2 > ( d : ℝ ) / t <;> simp +decide [ hx ];
                  · refine' MeasureTheory.Integrable.indicator _ _;
                    · have := @gaussian_integral_formula d ( 2 * t ) ( by positivity );
                      contrapose! this;
                      rw [ MeasureTheory.integral_undef ( by simpa only [ neg_mul ] using this ) ] ; positivity;
                    · exact measurableSet_lt measurable_const ( Finset.measurable_sum _ fun _ _ => measurable_pi_apply _ |> Measurable.pow_const <| 2 );
                  · refine' MeasureTheory.Integrable.indicator _ _;
                    · have := @gaussian_integral_formula d ( 2 * t ) ( by positivity );
                      exact ( by contrapose! this; rw [ MeasureTheory.integral_undef ( by aesop ) ] ; positivity );
                    · exact measurableSet_le ( by measurability ) ( by measurability )
            generalize_proofs at *; (
            exact h_coreMass_ge.symm ▸ sub_le_sub_left ( gaussian_tail_factoring d t ( by positivity ) ) _ |> le_trans ( by norm_num ) ;);
          convert h_coreMass_ge using 2 ; rw [ show ( Real.pi / t ) ^ ( ( d : ℝ ) / 2 ) = ( Real.pi / ( 2 * t ) ) ^ ( ( d : ℝ ) / 2 ) * ( 2 ^ ( ( d : ℝ ) / 2 ) ) by rw [ ← Real.mul_rpow ( by positivity ) ( by positivity ) ] ; ring ] ; ring!;
        -- We'll use that $e^{-d} \cdot 2^{d/2} \leq e^{-d/2}$ to conclude the proof.
        have h_exp_bound : Real.exp (-d) * (2 ^ (d / 2 : ℝ)) ≤ Real.exp (-(1 / 2 * d)) := by
          rw [ ← Real.log_le_log_iff ( by positivity ) ( by positivity ), Real.log_mul ( by positivity ) ( by positivity ), Real.log_exp, Real.log_rpow ] <;> norm_num ; ring_nf ; norm_num [ Real.exp_pos ] ; nlinarith [ Real.log_le_sub_one_of_pos zero_lt_two ] ;
        nlinarith [ show 0 ≤ gaussianF d t by exact Real.rpow_nonneg ( by positivity ) _ ]

/-- The Gaussian reference mass is controlled by a fixed multiple of `coreMass`. -/
lemma gaussianF_le_const_mul_coreMass :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ) (t : ℝ), 1 ≤ d → 1 ≤ t →
      gaussianF d t ≤ C * coreMass d t := by
  obtain ⟨c_star, hc_star_pos, hcore⟩ := inner_core_gaussian_mass
  refine ⟨(1 - Real.exp (-c_star))⁻¹, ?_, ?_⟩
  · have hexp_lt : Real.exp (-c_star) < 1 := by
      have hneg : -c_star < (0 : ℝ) := by linarith
      simpa using (Real.exp_lt_exp.mpr hneg)
    have hden_pos : 0 < 1 - Real.exp (-c_star) := by linarith
    simpa [one_div] using (one_div_pos.mpr hden_pos)
  · intro d t hd ht
    have hmain := hcore d t ht
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hexp_le : Real.exp (-(c_star * (d : ℝ))) ≤ Real.exp (-c_star) := by
      have hneg : -(c_star * (d : ℝ)) ≤ -c_star := by
        nlinarith [hc_star_pos, hdR]
      exact Real.exp_le_exp.mpr hneg
    have hcoef :
        1 - Real.exp (-c_star) ≤ 1 - Real.exp (-(c_star * (d : ℝ))) := by
      nlinarith
    have hcoef_pos : 0 < 1 - Real.exp (-c_star) := by
      have hexp_lt : Real.exp (-c_star) < 1 := by
        have hneg : -c_star < (0 : ℝ) := by linarith
        simpa using (Real.exp_lt_exp.mpr hneg)
      linarith
    have hscaled :
        (1 - Real.exp (-c_star)) * gaussianF d t ≤ coreMass d t := by
      have hstep :
          (1 - Real.exp (-c_star)) * gaussianF d t
            ≤ (1 - Real.exp (-(c_star * (d : ℝ)))) * gaussianF d t := by
        exact mul_le_mul_of_nonneg_right hcoef
          (show 0 ≤ gaussianF d t by exact Real.rpow_nonneg (by positivity) _)
      exact le_trans hstep hmain
    have hdiv : gaussianF d t ≤ coreMass d t / (1 - Real.exp (-c_star)) := by
      exact (le_div_iff₀ hcoef_pos).2 (by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled)
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv

set_option maxHeartbeats 1600000

/-!
## Far-Shell and Off-Core Estimates
-/

-- Historical note: an earlier far-shell argument used a dimension-uniform pointwise
-- modulus gap on `B_{π/4} \ D_r`. The present proof uses the J-split integral argument
-- from `HadamardCn3WeakInvariance`, so only the surviving local box/shell lemmas remain here.

lemma edgeEvenFarShell_subset_edgeBox (n : ℕ) (r : ℝ) :
    edgeEvenFarShell n r ⊆ edgeBox n (π / 4) := by
  intro mu hmu
  exact (mem_edgeEvenFarShell_iff n r mu).1 hmu |>.1

/-- The ambient Gaussian kernel on edge coordinates is integrable. -/
lemma gaussian_integrable_edge (n : ℕ) (a : ℝ) (ha : 0 < a) :
    MeasureTheory.Integrable
      (fun mu : Cn3Torus.Edge n → ℝ => Real.exp (-a * Cn3Torus.sqNormEdge n mu)) := by
  by_contra hnot
  have hformula := gaussian_integral_formula_edge n a ha
  rw [MeasureTheory.integral_undef hnot] at hformula
  have hpos : 0 < (π / a) ^ ((dim n : ℝ) / 2) := by positivity
  linarith

/-- Polynomial-Gaussian kernels on edge coordinates are integrable. -/
lemma sqNorm_moment_gaussian_integrable_edge
    (n m : ℕ) (hm : 0 < m) (t : ℝ) (ht : 0 < t) :
    MeasureTheory.Integrable
      (fun mu : Cn3Torus.Edge n → ℝ =>
        Cn3Torus.sqNormEdge n mu ^ m * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)) := by
  let f : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu =>
    Cn3Torus.sqNormEdge n mu ^ m * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
  let g : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu =>
    ((m : ℝ) ^ m / t ^ m) * Real.exp (-t * Cn3Torus.sqNormEdge n mu)
  have hg_int : MeasureTheory.Integrable g := by
    simpa [g] using
      (gaussian_integrable_edge n t ht).const_mul ((m : ℝ) ^ m / t ^ m)
  have hfsm : MeasureTheory.AEStronglyMeasurable f := by
    have hpoly :
        Continuous (fun mu : Cn3Torus.Edge n → ℝ => Cn3Torus.sqNormEdge n mu ^ m) :=
      (Cn3Torus.continuous_sqNormEdge n).pow m
    have hexp' :
        Continuous (fun mu : Cn3Torus.Edge n → ℝ =>
          Real.exp (-(2 * t * Cn3Torus.sqNormEdge n mu))) := by
      exact Real.continuous_exp.comp
        ((continuous_const.mul (Cn3Torus.continuous_sqNormEdge n)).neg)
    have hexp :
        Continuous (fun mu : Cn3Torus.Edge n → ℝ =>
          Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)) := by
      simpa [mul_assoc] using hexp'
    exact (hpoly.mul hexp).aestronglyMeasurable
  have hbound :
      ∀ᵐ mu : Cn3Torus.Edge n → ℝ ∂MeasureTheory.volume, ‖f mu‖ ≤ g mu := by
    exact Filter.Eventually.of_forall (fun mu => by
      have hs_nonneg : 0 ≤ Cn3Torus.sqNormEdge n mu := Cn3Torus.sqNormEdge_nonneg n mu
      have hts_nonneg : 0 ≤ t * Cn3Torus.sqNormEdge n mu := mul_nonneg ht.le hs_nonneg
      have hpow :
          (t * Cn3Torus.sqNormEdge n mu) ^ m
            ≤ (m : ℝ) ^ m * Real.exp (t * Cn3Torus.sqNormEdge n mu) :=
        Cn3Torus.pow_nat_le_nat_pow_mul_exp m hm hts_nonneg
      have hstep :
          (t * Cn3Torus.sqNormEdge n mu) ^ m
              * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
            ≤ (m : ℝ) ^ m * Real.exp (-t * Cn3Torus.sqNormEdge n mu) := by
        have hmul :=
          mul_le_mul_of_nonneg_right hpow
            (show 0 ≤ Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu) by positivity)
        calc
          (t * Cn3Torus.sqNormEdge n mu) ^ m
              * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
            ≤ ((m : ℝ) ^ m * Real.exp (t * Cn3Torus.sqNormEdge n mu))
                * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu) := hmul
          _ = (m : ℝ) ^ m * Real.exp (-t * Cn3Torus.sqNormEdge n mu) := by
                rw [mul_assoc, ← Real.exp_add]
                congr 1
                ring
      have ht_pow_pos : 0 < t ^ m := pow_pos ht m
      have hmain :
          f mu ≤ g mu := by
        have hdiv :
            f mu ≤ ((m : ℝ) ^ m * Real.exp (-t * Cn3Torus.sqNormEdge n mu)) / t ^ m := by
          refine (le_div_iff₀ ht_pow_pos).2 ?_
          calc
            f mu * t ^ m
                = (Cn3Torus.sqNormEdge n mu ^ m * t ^ m)
                    * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu) := by
                      unfold f
                      ring
            _ = (t * Cn3Torus.sqNormEdge n mu) ^ m
                    * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu) := by
                      rw [← mul_pow]
                      ring
            _ ≤ (m : ℝ) ^ m * Real.exp (-t * Cn3Torus.sqNormEdge n mu) := hstep
        simpa [g, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
      have hf_nonneg : 0 ≤ f mu := by
        unfold f
        positivity
      simpa [Real.norm_eq_abs, abs_of_nonneg hf_nonneg] using hmain)
  exact MeasureTheory.Integrable.mono' hg_int hfsm hbound

lemma texPrefactor_mul_edgeBox_pi_div_four_volume_le_one (n : ℕ) (hn : 2 ≤ n) :
    Cn3Torus.texPrefactor n * (MeasureTheory.volume (edgeBox n (π / 4))).toReal ≤ 1 := by
  have hpi4_nonneg : 0 ≤ (Real.pi / 4 : ℝ) := by positivity [Real.pi_pos]
  have hvol :
      (MeasureTheory.volume (edgeBox n (π / 4))).toReal
        = ((Real.pi / 2) ^ (Cn3Torus.d n : Nat) : ℝ) := by
    calc
      (MeasureTheory.volume (edgeBox n (π / 4))).toReal
          = (ENNReal.ofReal (((2 * (Real.pi / 4)) ^ (dim n : Nat) : ℝ))).toReal := by
              rw [edgeBox_volume_eq n (Real.pi / 4) hpi4_nonneg]
      _ = ((2 * (Real.pi / 4)) ^ (dim n : Nat) : ℝ) := by
            exact ENNReal.toReal_ofReal (pow_nonneg (by positivity) _)
      _ = ((2 * (Real.pi / 4)) ^ (Cn3Torus.d n : Nat) : ℝ) := by
            simp [dim, Cn3Torus.d]
      _ = ((Real.pi / 2) ^ (Cn3Torus.d n : Nat) : ℝ) := by
            congr 1
            ring
  have hden_ne : ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ) ≠ 0 := by positivity
  have hratio :
      (((Real.pi / 2) ^ (Cn3Torus.d n : Nat) : ℝ) / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
        = (1 / 4 : ℝ) ^ (Cn3Torus.d n : Nat) := by
    calc
      (((Real.pi / 2) ^ (Cn3Torus.d n : Nat) : ℝ) / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))
          = ((Real.pi / 2) / (2 * Real.pi)) ^ (Cn3Torus.d n : Nat) := by
              simpa using (div_pow (Real.pi / 2) (2 * Real.pi) (Cn3Torus.d n)).symm
      _ = (1 / 4 : ℝ) ^ (Cn3Torus.d n : Nat) := by
            congr 1
            have hbase : (Real.pi / 2) / (2 * Real.pi) = (1 / 4 : ℝ) := by
              field_simp [Real.pi_ne_zero]
              norm_num
            exact hbase
  have hpow_nat : (2 ^ (2 * Cn3Torus.d n - n + 1) : ℕ) ≤ 2 ^ (2 * Cn3Torus.d n) := by
    have hexp_le : 2 * Cn3Torus.d n - n + 1 ≤ 2 * Cn3Torus.d n := by
      by_cases hn3 : 3 ≤ n
      · have hnd : n ≤ 2 * Cn3Torus.d n := Cn3Torus.n_le_two_mul_d n hn3
        omega
      · have hn2_eq : n = 2 := by omega
        simp [hn2_eq, Cn3Torus.d]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hexp_le
  have hpow_real :
      (2 ^ (2 * Cn3Torus.d n - n + 1) : ℝ) ≤ (2 ^ (2 * Cn3Torus.d n) : ℝ) := by
    exact_mod_cast hpow_nat
  have hquarter :
      (1 / 4 : ℝ) ^ (Cn3Torus.d n : Nat) = 1 / (2 ^ (2 * Cn3Torus.d n) : ℝ) := by
    have hquarter_base : (1 / 4 : ℝ) = (1 / 2 : ℝ) * (1 / 2 : ℝ) := by norm_num
    calc
      (1 / 4 : ℝ) ^ (Cn3Torus.d n : Nat)
          = (((1 / 2 : ℝ) * (1 / 2 : ℝ)) ^ (Cn3Torus.d n : Nat)) := by rw [hquarter_base]
      _ = ((1 / 2 : ℝ) ^ (Cn3Torus.d n : Nat)) * ((1 / 2 : ℝ) ^ (Cn3Torus.d n : Nat)) := by
            rw [mul_pow]
      _ = (1 / 2 : ℝ) ^ (Cn3Torus.d n + Cn3Torus.d n : Nat) := by rw [← pow_add]
      _ = (1 / 2 : ℝ) ^ (2 * Cn3Torus.d n : Nat) := by
            congr 1
            omega
      _ = ((2 : ℝ)⁻¹) ^ (2 * Cn3Torus.d n : Nat) := by norm_num
      _ = ((2 : ℝ) ^ (2 * Cn3Torus.d n : Nat))⁻¹ := by rw [inv_pow]
      _ = 1 / (2 ^ (2 * Cn3Torus.d n) : ℝ) := by simp [one_div]
  have hmul_le :
      (2 ^ (2 * Cn3Torus.d n - n + 1) : ℝ) * (1 / 4 : ℝ) ^ (Cn3Torus.d n : Nat) ≤ 1 := by
    rw [hquarter]
    have hpow_pos : (0 : ℝ) < (2 ^ (2 * Cn3Torus.d n) : ℝ) := by positivity
    have hdiv_le :
        (2 ^ (2 * Cn3Torus.d n - n + 1) : ℝ) / (2 ^ (2 * Cn3Torus.d n) : ℝ) ≤ 1 :=
      (div_le_one hpow_pos).2 hpow_real
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv_le
  calc
    Cn3Torus.texPrefactor n * (MeasureTheory.volume (edgeBox n (π / 4))).toReal
        = (2 ^ (2 * Cn3Torus.d n - n + 1) : ℝ) * (1 / 4 : ℝ) ^ (Cn3Torus.d n : Nat) := by
            rw [Cn3Torus.texPrefactor, hvol]
            calc
              ((2 ^ (2 * Cn3Torus.d n - n + 1) : ℝ) / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat)))
                  * ((Real.pi / 2) ^ (Cn3Torus.d n : Nat) : ℝ)
                  =
                (2 ^ (2 * Cn3Torus.d n - n + 1) : ℝ)
                  * ((((Real.pi / 2) ^ (Cn3Torus.d n : Nat) : ℝ)
                      / ((2 * Real.pi) ^ (Cn3Torus.d n : Nat) : ℝ))) := by
                        field_simp [hden_ne]
              _ = (2 ^ (2 * Cn3Torus.d n - n + 1) : ℝ) * (1 / 4 : ℝ) ^ (Cn3Torus.d n : Nat) := by
                    rw [hratio]
    _ ≤ 1 := hmul_le

lemma cos_two_mul_le_exp_neg_eight_div_pi_sq_sq
    {x : ℝ} (hx : |x| ≤ Real.pi / 4) :
    Real.cos (2 * x) ≤ Real.exp (-(8 / Real.pi ^ (2 : Nat)) * x ^ (2 : Nat)) := by
  have hcos :
      Real.cos (2 * x) ≤ 1 - (2 / Real.pi ^ (2 : Nat)) * (2 * x) ^ (2 : Nat) := by
    apply Real.cos_le_one_sub_mul_cos_sq
    have hx2 : |2 * x| ≤ Real.pi := by
      calc
        |2 * x| = (2 : ℝ) * |x| := by rw [abs_mul, abs_of_nonneg (by norm_num)]
        _ ≤ (2 : ℝ) * (Real.pi / 4) := by gcongr
        _ = Real.pi / 2 := by ring
        _ ≤ Real.pi := by nlinarith [Real.pi_pos]
    exact le_trans hx2 (by linarith [Real.pi_pos])
  calc
    Real.cos (2 * x) ≤ 1 - (2 / Real.pi ^ (2 : Nat)) * (2 * x) ^ (2 : Nat) := hcos
    _ = 1 - (8 / Real.pi ^ (2 : Nat)) * x ^ (2 : Nat) := by ring
    _ ≤ Real.exp (-(8 / Real.pi ^ (2 : Nat)) * x ^ (2 : Nat)) := by
          simpa using Real.one_sub_le_exp_neg ((8 / Real.pi ^ (2 : Nat)) * x ^ (2 : Nat))

lemma avg_one_exp_neg_eight_div_pi_sq_le_exp_neg_two_div_pi_sq
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (1 + Real.exp (-(8 / Real.pi ^ (2 : Nat)) * u)) / 2
      ≤ Real.exp (-(2 / Real.pi ^ (2 : Nat)) * u) := by
  let v : ℝ := (4 / Real.pi ^ (2 : Nat)) * u
  have hv_nonneg : 0 ≤ v := by
    dsimp [v]
    positivity [Real.pi_pos]
  have hv_le_one : v ≤ 1 := by
    dsimp [v]
    have hpi : (4 : ℝ) ≤ Real.pi ^ (2 : Nat) := by
      nlinarith [Real.pi_gt_three]
    have hcoeff : 4 / Real.pi ^ (2 : Nat) ≤ (1 : ℝ) := by
      have hpi_pos : 0 < Real.pi ^ (2 : Nat) := by positivity [Real.pi_pos]
      exact (div_le_iff₀ hpi_pos).2 (by simpa using hpi)
    nlinarith
  have hcosh :
      (1 + Real.exp (-(8 / Real.pi ^ (2 : Nat)) * u)) / 2
        = Real.exp (-v) * Real.cosh v := by
    rw [Real.cosh_eq]
    have hexp_zero : (1 : ℝ) = Real.exp (-v) * Real.exp v := by
      rw [← Real.exp_add]
      have : -v + v = (0 : ℝ) := by ring
      rw [this, Real.exp_zero]
    have hexp_neg : Real.exp (-(8 / Real.pi ^ (2 : Nat)) * u) = Real.exp (-v) * Real.exp (-v) := by
      have hv_eq : -(8 / Real.pi ^ (2 : Nat)) * u = -v + -v := by
        dsimp [v]
        ring_nf
      rw [hv_eq, Real.exp_add]
    calc
      (1 + Real.exp (-(8 / Real.pi ^ (2 : Nat)) * u)) / 2
        = (Real.exp (-v) * Real.exp v + Real.exp (-v) * Real.exp (-v)) / 2 := by
            rw [← hexp_zero, hexp_neg]
      _ = (Real.exp (-v) * Real.exp v + Real.exp (-v) * Real.exp (-v)) / 2 := by
            rfl
      _ = Real.exp (-v) * ((Real.exp v + Real.exp (-v)) / 2) := by ring
  rw [hcosh]
  calc
    Real.exp (-v) * Real.cosh v ≤ Real.exp (-v) * Real.exp (v ^ (2 : Nat) / 2) := by
      exact mul_le_mul_of_nonneg_left (Real.cosh_le_exp_half_sq v) (by positivity)
    _ = Real.exp (-v + v ^ (2 : Nat) / 2) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp (-v / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hv_nonneg, hv_le_one]
    _ = Real.exp (-(2 / Real.pi ^ (2 : Nat)) * u) := by
      dsimp [v]
      ring_nf

/-- A uniform cubic bound with only linear-in-`n` loss. This is sharper than the
crude standalone `n^3` counting bound and is enough for the cubic core model
estimate. -/
private theorem cubicT_abs_le_two_mul_n_mul_sNorm_threeHalves
    (n : ℕ) (lam : Fin n → Fin n → ℝ) :
    |cubicT n lam| ≤ (2 * (n : ℝ)) * sNorm n lam ^ (3 / 2 : ℝ) := by
  let row : Fin n → ℝ := fun i => ∑ k : Fin n, if i < k then lam i k ^ (2 : Nat) else 0
  have hrow_le : ∀ i : Fin n, row i ≤ sNorm n lam := by
    intro i
    unfold row sNorm
    have hnonneg :
        ∀ a ∈ (Finset.univ : Finset (Fin n)),
          0 ≤ ∑ k : Fin n, if a < k then lam a k ^ (2 : Nat) else 0 := by
      intro a ha
      refine Finset.sum_nonneg ?_
      intro k hk
      split_ifs <;> positivity
    simpa using
      (Finset.single_le_sum hnonneg (Finset.mem_univ i))
  have hpair_le :
      ∀ i j : Fin n,
        |∑ k : Fin n, if i < j ∧ j < k then lam i k * lam j k else 0|
          ≤ 2 * sNorm n lam := by
    intro i j
    have habs :
        |∑ k : Fin n, if i < j ∧ j < k then lam i k * lam j k else 0|
        ≤ ∑ k : Fin n, if i < j ∧ j < k then |lam i k| * |lam j k| else 0 := by
      calc
        |∑ k : Fin n, if i < j ∧ j < k then lam i k * lam j k else 0|
            ≤ ∑ k : Fin n, |if i < j ∧ j < k then lam i k * lam j k else 0| := by
                simpa using
                  (Finset.abs_sum_le_sum_abs
                    (s := (Finset.univ : Finset (Fin n)))
                    (f := fun k : Fin n => if i < j ∧ j < k then lam i k * lam j k else 0))
        _ = ∑ k : Fin n, if i < j ∧ j < k then |lam i k| * |lam j k| else 0 := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              by_cases hijk : i < j ∧ j < k
              · simp [hijk, abs_mul]
              · simp [hijk]
    have hsq :
      (∑ k : Fin n, if i < j ∧ j < k then |lam i k| * |lam j k| else 0)
        ≤ (∑ k : Fin n, if i < j ∧ j < k then (lam i k ^ (2 : Nat) + lam j k ^ (2 : Nat)) else 0) := by
      refine Finset.sum_le_sum ?_
      intro k hk
      by_cases hijk : i < j ∧ j < k
      · have hterm : |lam i k| * |lam j k| ≤ lam i k ^ (2 : Nat) + lam j k ^ (2 : Nat) := by
          have hsq_nonneg : 0 ≤ (|lam i k| - |lam j k|) ^ (2 : Nat) := by positivity
          have hab_nonneg : 0 ≤ |lam i k| * |lam j k| := by positivity
          nlinarith [sq_abs (lam i k), sq_abs (lam j k)]
        simp [hijk, hterm]
      · simp [hijk]
    have hrows :
        (∑ k : Fin n, if i < j ∧ j < k then (lam i k ^ (2 : Nat) + lam j k ^ (2 : Nat)) else 0)
          ≤ row i + row j := by
      unfold row
      calc
      (∑ k : Fin n, if i < j ∧ j < k then (lam i k ^ (2 : Nat) + lam j k ^ (2 : Nat)) else 0)
          ≤ (∑ k : Fin n,
              ((if i < k then lam i k ^ (2 : Nat) else 0)
                + (if j < k then lam j k ^ (2 : Nat) else 0))) := by
                  refine Finset.sum_le_sum ?_
                  intro k hk
                  by_cases hijk : i < j ∧ j < k
                  · have hik : i < k := lt_trans hijk.1 hijk.2
                    simp [hijk, hik, hijk.2]
                  · have hnonneg :
                        0 ≤
                          ((if i < k then lam i k ^ (2 : Nat) else 0)
                            + (if j < k then lam j k ^ (2 : Nat) else 0)) := by
                        split_ifs <;> positivity
                    simp [hijk, hnonneg]
        _ = row i + row j := by
            simp [row, Finset.sum_add_distrib]
    have hrows_le : row i + row j ≤ 2 * sNorm n lam := by
      nlinarith [hrow_le i, hrow_le j]
    exact le_trans habs (le_trans hsq (le_trans hrows hrows_le))
  have hcubic :
      cubicT n lam =
        ∑ i : Fin n, ∑ j : Fin n,
          lam i j * ∑ k : Fin n, if i < j ∧ j < k then lam i k * lam j k else 0 := by
    unfold cubicT
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine Finset.sum_congr rfl ?_
    intro j hj
    by_cases hij : i < j
    · simp [hij, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    · simp [hij]
  have hinner :
      ∀ i : Fin n,
        |∑ j : Fin n, lam i j * ∑ k : Fin n, if i < j ∧ j < k then lam i k * lam j k else 0|
          ≤ ∑ j : Fin n, if i < j then |lam i j| * (2 * sNorm n lam) else 0 := by
    intro i
    have habs :
        |∑ j : Fin n, lam i j * ∑ k : Fin n, if i < j ∧ j < k then lam i k * lam j k else 0|
          ≤ ∑ j : Fin n,
              |lam i j * ∑ k : Fin n, if i < j ∧ j < k then lam i k * lam j k else 0| := by
      simpa using
        (Finset.abs_sum_le_sum_abs
          (s := (Finset.univ : Finset (Fin n)))
          (f := fun j : Fin n =>
            lam i j * ∑ k : Fin n, if i < j ∧ j < k then lam i k * lam j k else 0))
    refine le_trans habs ?_
    refine Finset.sum_le_sum ?_
    intro j hj
    by_cases hij : i < j
    · rw [if_pos hij]
      have hmul :=
        mul_le_mul_of_nonneg_left (hpair_le i j) (abs_nonneg (lam i j))
      simpa [abs_mul, hij, mul_assoc, mul_left_comm, mul_comm] using hmul
    · have hzero :
        (∑ k : Fin n, if i < j ∧ j < k then lam i k * lam j k else 0) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro k hk
          simp [hij]
      rw [if_neg hij]
      simp [hzero]
  let A : ℝ := ∑ i : Fin n, ∑ j : Fin n, if i < j then |lam i j| else 0
  have hmain :
      |cubicT n lam| ≤ ∑ i : Fin n, ∑ j : Fin n, if i < j then |lam i j| * (2 * sNorm n lam) else 0 := by
    calc
      |cubicT n lam|
          = |∑ i : Fin n, ∑ j : Fin n,
                lam i j * ∑ k : Fin n, if i < j ∧ j < k then lam i k * lam j k else 0| := by
                  rw [hcubic]
      _ ≤ ∑ i : Fin n,
            |∑ j : Fin n,
                lam i j * ∑ k : Fin n, if i < j ∧ j < k then lam i k * lam j k else 0| := by
              exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, if i < j then |lam i j| * (2 * sNorm n lam) else 0 := by
            exact Finset.sum_le_sum (fun i hi => hinner i)
  have hfactor :
      (∑ i : Fin n, ∑ j : Fin n, if i < j then |lam i j| * (2 * sNorm n lam) else 0)
        = (2 * sNorm n lam) * A := by
    unfold A
    calc
      (∑ i : Fin n, ∑ j : Fin n, if i < j then |lam i j| * (2 * sNorm n lam) else 0)
          = ∑ i : Fin n, ∑ j : Fin n, (2 * sNorm n lam) * (if i < j then |lam i j| else 0) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              by_cases hij : i < j <;> simp [hij, mul_assoc, mul_left_comm, mul_comm]
      _ = (2 * sNorm n lam) * ∑ i : Fin n, ∑ j : Fin n, if i < j then |lam i j| else 0 := by
            simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ = (2 * sNorm n lam) * A := by rfl
  let f : Fin n × Fin n → ℝ := fun p => if p.1 < p.2 then |lam p.1 p.2| else 0
  have hA_eq : A = ∑ p : Fin n × Fin n, f p := by
    unfold A f
    simpa using
      (Fintype.sum_prod_type
        (f := fun p : Fin n × Fin n => if p.1 < p.2 then |lam p.1 p.2| else 0)).symm
  have hA_nonneg : 0 ≤ A := by
    unfold A
    refine Finset.sum_nonneg ?_
    intro i hi
    refine Finset.sum_nonneg ?_
    intro j hj
    split_ifs <;> positivity
  have hA_sq :
      A ^ (2 : Nat) ≤ (n : ℝ) ^ (2 : Nat) * sNorm n lam := by
    rw [hA_eq]
    have hsq :=
      sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin n × Fin n)))
        (f := f)
    have hcard : (Fintype.card (Fin n × Fin n) : ℝ) = (n : ℝ) ^ (2 : Nat) := by
      have hcard_nat : Fintype.card (Fin n × Fin n) = n * n := by simp
      have hcard_real : (Fintype.card (Fin n × Fin n) : ℝ) = (n : ℝ) * (n : ℝ) := by
        exact_mod_cast hcard_nat
      simpa [pow_two] using hcard_real
    have hsum_sq : ∑ p : Fin n × Fin n, f p ^ (2 : Nat) = sNorm n lam := by
      rw [Fintype.sum_prod_type]
      unfold f sNorm
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      by_cases hij : i < j
      · simp [hij, abs_pow_even]
      · simp [hij]
    have hsq' :
        (∑ p : Fin n × Fin n, f p) ^ (2 : Nat) ≤ (n : ℝ) ^ (2 : Nat) * sNorm n lam := by
      calc
        (∑ p : Fin n × Fin n, f p) ^ (2 : Nat)
            ≤ (Fintype.card (Fin n × Fin n) : ℝ) * ∑ p : Fin n × Fin n, f p ^ (2 : Nat) := by
                simpa using hsq
        _ = (n : ℝ) ^ (2 : Nat) * sNorm n lam := by
              rw [hcard, hsum_sq]
    simpa [hA_eq] using hsq'
  have hs_nonneg : 0 ≤ sNorm n lam := sNorm_nonneg n lam
  have hA_bound : A ≤ (n : ℝ) * Real.sqrt (sNorm n lam) := by
    have hsq_bound : A ^ (2 : Nat) ≤ ((n : ℝ) * Real.sqrt (sNorm n lam)) ^ (2 : Nat) := by
      have hsqrt_sq :
          ((n : ℝ) * Real.sqrt (sNorm n lam)) ^ (2 : Nat) = (n : ℝ) ^ (2 : Nat) * sNorm n lam := by
        calc
          ((n : ℝ) * Real.sqrt (sNorm n lam)) ^ (2 : Nat)
              = (n : ℝ) ^ (2 : Nat) * (Real.sqrt (sNorm n lam)) ^ (2 : Nat) := by
                  rw [mul_pow]
          _ = (n : ℝ) ^ (2 : Nat) * sNorm n lam := by
                rw [Real.sq_sqrt hs_nonneg]
      calc
        A ^ (2 : Nat) ≤ (n : ℝ) ^ (2 : Nat) * sNorm n lam := hA_sq
        _ = ((n : ℝ) * Real.sqrt (sNorm n lam)) ^ (2 : Nat) := by
              rw [hsqrt_sq]
    have hright_nonneg : 0 ≤ (n : ℝ) * Real.sqrt (sNorm n lam) := by positivity
    nlinarith
  have hs_sqrt :
      sNorm n lam * Real.sqrt (sNorm n lam) = sNorm n lam ^ (3 / 2 : ℝ) := by
    by_cases hs_zero : sNorm n lam = 0
    · simp [hs_zero]
    · have hs_pos : 0 < sNorm n lam := by
          exact lt_of_le_of_ne hs_nonneg (by
            intro h
            exact hs_zero h.symm)
      calc
        sNorm n lam * Real.sqrt (sNorm n lam)
            = sNorm n lam ^ (1 : ℝ) * sNorm n lam ^ (1 / 2 : ℝ) := by
                rw [Real.sqrt_eq_rpow]
                simp [Real.rpow_one]
        _ = sNorm n lam ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by
              rw [← Real.rpow_add hs_pos]
        _ = sNorm n lam ^ (3 / 2 : ℝ) := by norm_num
  calc
    |cubicT n lam|
      ≤ (2 * sNorm n lam) * A := by
          rw [← hfactor]
          exact hmain
    _ ≤ (2 * sNorm n lam) * ((n : ℝ) * Real.sqrt (sNorm n lam)) := by
          exact mul_le_mul_of_nonneg_left hA_bound (by positivity)
    _ = (2 * (n : ℝ)) * (sNorm n lam * Real.sqrt (sNorm n lam)) := by
          ring
    _ = (2 * (n : ℝ)) * sNorm n lam ^ (3 / 2 : ℝ) := by
          rw [hs_sqrt]

/-- The squared cubic phase is dominated by the third Gaussian radial moment. -/
private lemma cubicT_sq_gaussian_le (n : ℕ) (t : ℝ) (mu : Cn3Torus.Edge n → ℝ) :
    (cubicT n (matrixOfEdge n mu)) ^ (2 : Nat)
      * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
    ≤ ((2 * (n : ℝ)) ^ (2 : Nat))
        * (Cn3Torus.sqNormEdge n mu ^ (3 : Nat)
            * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)) := by
  have hs_nonneg : 0 ≤ Cn3Torus.sqNormEdge n mu := Cn3Torus.sqNormEdge_nonneg n mu
  have hcubic :
      |cubicT n (matrixOfEdge n mu)|
        ≤ (2 * (n : ℝ)) * Cn3Torus.sqNormEdge n mu ^ (3 / 2 : ℝ) := by
    simpa [sNorm_matrixOfEdge_eq] using
      cubicT_abs_le_two_mul_n_mul_sNorm_threeHalves n (matrixOfEdge n mu)
  have hpow :=
    pow_le_pow_left₀ (abs_nonneg (cubicT n (matrixOfEdge n mu))) hcubic 2
  have hs_rpow :
      Cn3Torus.sqNormEdge n mu ^ (3 / 2 : ℝ)
        * Cn3Torus.sqNormEdge n mu ^ (3 / 2 : ℝ)
        = Cn3Torus.sqNormEdge n mu ^ (3 : Nat) := by
    by_cases hs_zero : Cn3Torus.sqNormEdge n mu = 0
    · simp [hs_zero]
    · have hs_pos : 0 < Cn3Torus.sqNormEdge n mu := by
        exact lt_of_le_of_ne hs_nonneg (by
          intro h
          exact hs_zero h.symm)
      calc
        Cn3Torus.sqNormEdge n mu ^ (3 / 2 : ℝ)
            * Cn3Torus.sqNormEdge n mu ^ (3 / 2 : ℝ)
          = Cn3Torus.sqNormEdge n mu ^ ((3 / 2 : ℝ) + (3 / 2 : ℝ)) := by
              rw [← Real.rpow_add hs_pos]
        _ = Cn3Torus.sqNormEdge n mu ^ (3 : ℝ) := by norm_num
        _ = Cn3Torus.sqNormEdge n mu ^ (3 : Nat) := by
              simpa using (Real.rpow_natCast (Cn3Torus.sqNormEdge n mu) 3)
  have hsq :
      (cubicT n (matrixOfEdge n mu)) ^ (2 : Nat)
        ≤ ((2 * (n : ℝ)) ^ (2 : Nat)) * Cn3Torus.sqNormEdge n mu ^ (3 : Nat) := by
    calc
      (cubicT n (matrixOfEdge n mu)) ^ (2 : Nat)
          = |cubicT n (matrixOfEdge n mu)| ^ (2 : Nat) := by
              symm
              simpa using (abs_pow_even (cubicT n (matrixOfEdge n mu)) 1)
      _ ≤ ((2 * (n : ℝ)) * Cn3Torus.sqNormEdge n mu ^ (3 / 2 : ℝ)) ^ (2 : Nat) := hpow
      _ = ((2 * (n : ℝ)) ^ (2 : Nat))
            * (Cn3Torus.sqNormEdge n mu ^ (3 / 2 : ℝ)
                * Cn3Torus.sqNormEdge n mu ^ (3 / 2 : ℝ)) := by
            rw [pow_two]
            ring
      _ = ((2 * (n : ℝ)) ^ (2 : Nat)) * Cn3Torus.sqNormEdge n mu ^ (3 : Nat) := by
            rw [hs_rpow]
  have hmul :=
    mul_le_mul_of_nonneg_right hsq
      (show 0 ≤ Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu) by positivity)
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

/-- The cubic-core `L²` kernel is globally integrable against the Gaussian weight. -/
lemma cubicT_sq_gaussian_integrable_edge (n : ℕ) (t : ℝ) (ht : 0 < t) :
    MeasureTheory.Integrable
      (fun mu : Cn3Torus.Edge n → ℝ =>
        (cubicT n (matrixOfEdge n mu)) ^ (2 : Nat)
          * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)) := by
  let f : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu =>
    (cubicT n (matrixOfEdge n mu)) ^ (2 : Nat)
      * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)
  let g : (Cn3Torus.Edge n → ℝ) → ℝ := fun mu =>
    ((2 * (n : ℝ)) ^ (2 : Nat))
      * (Cn3Torus.sqNormEdge n mu ^ (3 : Nat)
          * Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu))
  have hg_int : MeasureTheory.Integrable g := by
    simpa [g, mul_assoc, mul_left_comm, mul_comm] using
      (sqNorm_moment_gaussian_integrable_edge n 3 (by norm_num) t ht).const_mul
        ((2 * (n : ℝ)) ^ (2 : Nat))
  have hfsm : MeasureTheory.AEStronglyMeasurable f := by
    have hcubic :
        Continuous (fun mu : Cn3Torus.Edge n → ℝ =>
          cubicT n (matrixOfEdge n mu)) :=
      (continuous_cubicT n).comp (continuous_matrixOfEdge n)
    have hexp' :
        Continuous (fun mu : Cn3Torus.Edge n → ℝ =>
          Real.exp (-(2 * t * Cn3Torus.sqNormEdge n mu))) := by
      exact Real.continuous_exp.comp
        ((continuous_const.mul (Cn3Torus.continuous_sqNormEdge n)).neg)
    have hexp :
        Continuous (fun mu : Cn3Torus.Edge n → ℝ =>
          Real.exp (-2 * t * Cn3Torus.sqNormEdge n mu)) := by
      simpa [mul_assoc] using hexp'
    exact ((hcubic.pow 2).mul hexp).aestronglyMeasurable
  have hbound :
      ∀ᵐ mu : Cn3Torus.Edge n → ℝ ∂MeasureTheory.volume, ‖f mu‖ ≤ g mu := by
    exact Filter.Eventually.of_forall (fun mu => by
      have hf_nonneg : 0 ≤ f mu := by
        unfold f
        positivity
      have hpoint := cubicT_sq_gaussian_le n t mu
      simpa [f, g, Real.norm_eq_abs, abs_of_nonneg hf_nonneg] using hpoint)
  exact MeasureTheory.Integrable.mono' hg_int hfsm hbound

/-- The corrected logarithmic core exponent, written in edge coordinates. -/
def correctedCoreExponent (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) : ℂ :=
  ((-(Cn3Torus.sqNormEdge n mu / 2) : ℝ) : ℂ)
    - Complex.I * (cubicT n (matrixOfEdge n mu) : ℂ)
    + (quarticCorr n (matrixOfEdge n mu) : ℂ)
    + Complex.I * (quinticP5 n (matrixOfEdge n mu) : ℂ)

/-- The repaired step-1 core model with quartic and quintic phases included. -/
def correctedCoreIntegrand (n t : ℕ) (mu : Cn3Torus.Edge n → ℝ) : ℂ :=
  Complex.exp ((((4 * t : ℕ) : ℂ) * correctedCoreExponent n mu))

lemma correctedCoreExponent_re (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    (correctedCoreExponent n mu).re
      = -(Cn3Torus.sqNormEdge n mu / 2) + quarticCorr n (matrixOfEdge n mu) := by
  unfold correctedCoreExponent
  simp [sub_eq_add_neg]

lemma correctedCoreIntegrand_norm (n t : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    ‖correctedCoreIntegrand n t mu‖
      = Real.exp
          (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu
            + 4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)) := by
  unfold correctedCoreIntegrand
  rw [Complex.norm_exp]
  have hre :
      ((((4 * t : ℕ) : ℂ) * correctedCoreExponent n mu)).re
        = (4 * t : ℝ) * (correctedCoreExponent n mu).re := by
    simp
  rw [hre, correctedCoreExponent_re]
  ring

/-- The intermediate core exponent that keeps the quartic term but drops the quintic phase. -/
def quarticCoreExponent (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) : ℂ :=
  ((-(Cn3Torus.sqNormEdge n mu / 2) : ℝ) : ℂ)
    - Complex.I * (cubicT n (matrixOfEdge n mu) : ℂ)
    + (quarticCorr n (matrixOfEdge n mu) : ℂ)

/-- The quartic core model used between the repaired and cubic cores. -/
def quarticCoreIntegrand (n t : ℕ) (mu : Cn3Torus.Edge n → ℝ) : ℂ :=
  Complex.exp ((((4 * t : ℕ) : ℂ) * quarticCoreExponent n mu))

/-- The pure cubic-Gaussian core exponent. -/
def cubicCoreExponent (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) : ℂ :=
  ((-(Cn3Torus.sqNormEdge n mu / 2) : ℝ) : ℂ)
    - Complex.I * (cubicT n (matrixOfEdge n mu) : ℂ)

/-- The cubic-Gaussian core model. -/
def cubicCoreIntegrand (n t : ℕ) (mu : Cn3Torus.Edge n → ℝ) : ℂ :=
  Complex.exp ((((4 * t : ℕ) : ℂ) * cubicCoreExponent n mu))

lemma quarticCoreExponent_re (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    (quarticCoreExponent n mu).re
      = -(Cn3Torus.sqNormEdge n mu / 2) + quarticCorr n (matrixOfEdge n mu) := by
  unfold quarticCoreExponent
  simp [sub_eq_add_neg]

private lemma quarticCoreIntegrand_norm (n t : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    ‖quarticCoreIntegrand n t mu‖
      = Real.exp
          (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu
            + 4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)) := by
  unfold quarticCoreIntegrand
  rw [Complex.norm_exp]
  have hre :
      ((((4 * t : ℕ) : ℂ) * quarticCoreExponent n mu)).re
        = (4 * t : ℝ) * (quarticCoreExponent n mu).re := by
    simp
  rw [hre, quarticCoreExponent_re]
  ring

lemma cubicCoreExponent_re (n : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    (cubicCoreExponent n mu).re = -(Cn3Torus.sqNormEdge n mu / 2) := by
  unfold cubicCoreExponent
  simp [sub_eq_add_neg]

private lemma cubicCoreIntegrand_norm (n t : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    ‖cubicCoreIntegrand n t mu‖
      = Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu) := by
  unfold cubicCoreIntegrand
  rw [Complex.norm_exp]
  have hre :
      ((((4 * t : ℕ) : ℂ) * cubicCoreExponent n mu)).re
        = (4 * t : ℝ) * (cubicCoreExponent n mu).re := by
    simp
  rw [hre, cubicCoreExponent_re]
  ring

/-- Exact pointwise factorization of the repaired-to-quartic core difference. -/
lemma correctedCoreIntegrand_sub_quarticCoreIntegrand_norm_eq
    (n t : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    ‖correctedCoreIntegrand n t mu - quarticCoreIntegrand n t mu‖
      = Real.exp
          (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu
            + 4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu))
          * ‖Complex.exp
                ((((4 * t : ℕ) : ℂ)
                    * (Complex.I * (quinticP5 n (matrixOfEdge n mu) : ℂ))))
              - 1‖ := by
  have hsplit :
      correctedCoreIntegrand n t mu
        = quarticCoreIntegrand n t mu
            * Complex.exp
                ((((4 * t : ℕ) : ℂ)
                    * (Complex.I * (quinticP5 n (matrixOfEdge n mu) : ℂ)))) := by
    have hexp_split :
        (((4 * t : ℕ) : ℂ) * correctedCoreExponent n mu)
          = (((4 * t : ℕ) : ℂ) * quarticCoreExponent n mu)
              + (((4 * t : ℕ) : ℂ)
                  * (Complex.I * (quinticP5 n (matrixOfEdge n mu) : ℂ))) := by
      unfold correctedCoreExponent quarticCoreExponent
      ring_nf
    unfold correctedCoreIntegrand quarticCoreIntegrand
    rw [hexp_split, Complex.exp_add]
  have hsub :
      correctedCoreIntegrand n t mu - quarticCoreIntegrand n t mu
        = quarticCoreIntegrand n t mu
            * (Complex.exp
                ((((4 * t : ℕ) : ℂ)
                    * (Complex.I * (quinticP5 n (matrixOfEdge n mu) : ℂ))))
                - 1) := by
    rw [hsplit]
    ring
  calc
    ‖correctedCoreIntegrand n t mu - quarticCoreIntegrand n t mu‖
      = ‖quarticCoreIntegrand n t mu
          * (Complex.exp
              ((((4 * t : ℕ) : ℂ)
                  * (Complex.I * (quinticP5 n (matrixOfEdge n mu) : ℂ))))
              - 1)‖ := by
            rw [hsub]
    _ = ‖quarticCoreIntegrand n t mu‖
          * ‖Complex.exp
              ((((4 * t : ℕ) : ℂ)
                  * (Complex.I * (quinticP5 n (matrixOfEdge n mu) : ℂ))))
              - 1‖ := by
            rw [norm_mul]
    _ = Real.exp
          (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu
            + 4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu))
          * ‖Complex.exp
              ((((4 * t : ℕ) : ℂ)
                  * (Complex.I * (quinticP5 n (matrixOfEdge n mu) : ℂ))))
              - 1‖ := by
            rw [quarticCoreIntegrand_norm]

/-- Exact pointwise factorization of the quartic-to-cubic core difference. -/
lemma quarticCoreIntegrand_sub_cubicCoreIntegrand_norm_eq
    (n t : ℕ) (mu : Cn3Torus.Edge n → ℝ) :
    ‖quarticCoreIntegrand n t mu - cubicCoreIntegrand n t mu‖
      = Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
          * |Real.exp (4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)) - 1| := by
  have hsplit :
      quarticCoreIntegrand n t mu
        = cubicCoreIntegrand n t mu
            * Complex.exp
                ((((4 * t : ℕ) : ℂ) * (quarticCorr n (matrixOfEdge n mu) : ℂ))) := by
    have hexp_split :
        (((4 * t : ℕ) : ℂ) * quarticCoreExponent n mu)
          = (((4 * t : ℕ) : ℂ) * cubicCoreExponent n mu)
              + (((4 * t : ℕ) : ℂ) * (quarticCorr n (matrixOfEdge n mu) : ℂ)) := by
      unfold quarticCoreExponent cubicCoreExponent
      ring_nf
    unfold quarticCoreIntegrand cubicCoreIntegrand
    rw [hexp_split, Complex.exp_add]
  have hsub :
      quarticCoreIntegrand n t mu - cubicCoreIntegrand n t mu
        = cubicCoreIntegrand n t mu
            * (Complex.exp
                ((((4 * t : ℕ) : ℂ) * (quarticCorr n (matrixOfEdge n mu) : ℂ)))
                - 1) := by
    rw [hsplit]
    ring
  have hexp_real :
      Complex.exp ((((4 * t : ℕ) : ℂ) * (quarticCorr n (matrixOfEdge n mu) : ℂ)))
        = (Real.exp (4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)) : ℂ) := by
    simp
  calc
    ‖quarticCoreIntegrand n t mu - cubicCoreIntegrand n t mu‖
      = ‖cubicCoreIntegrand n t mu
          * (Complex.exp
              ((((4 * t : ℕ) : ℂ) * (quarticCorr n (matrixOfEdge n mu) : ℂ)))
              - 1)‖ := by
            rw [hsub]
    _ = ‖cubicCoreIntegrand n t mu‖
          * ‖Complex.exp
              ((((4 * t : ℕ) : ℂ) * (quarticCorr n (matrixOfEdge n mu) : ℂ)))
              - 1‖ := by
            rw [norm_mul]
    _ = ‖cubicCoreIntegrand n t mu‖
          * |Real.exp (4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)) - 1| := by
            rw [hexp_real]
            congr 1
            simpa using
              (Complex.norm_real
                (Real.exp (4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)) - 1))
    _ = Real.exp (-2 * (t : ℝ) * Cn3Torus.sqNormEdge n mu)
          * |Real.exp (4 * (t : ℝ) * quarticCorr n (matrixOfEdge n mu)) - 1| := by
            rw [cubicCoreIntegrand_norm]

/-- Real-phase Lipschitz bound: `|e^{iu} - 1| ≤ |u|`. -/
lemma complex_exp_mul_I_sub_one_norm_le_abs (u : ℝ) :
    ‖Complex.exp (((u : ℂ) * Complex.I)) - 1‖ ≤ |u| := by
  have hsq :
      ‖Complex.exp (((u : ℂ) * Complex.I)) - 1‖ ^ (2 : Nat) ≤ |u| ^ (2 : Nat) := by
    have hexp_re : (Complex.exp (((u : ℂ) * Complex.I))).re = Real.cos u := by
      simpa using congrArg Complex.re (Complex.exp_mul_I (u : ℂ))
    have hexp_im : (Complex.exp (((u : ℂ) * Complex.I))).im = Real.sin u := by
      simpa using congrArg Complex.im (Complex.exp_mul_I (u : ℂ))
    have hsin_cos : Real.sin u ^ (2 : Nat) + Real.cos u ^ (2 : Nat) = 1 := by
      simpa [pow_two, add_comm] using (Real.sin_sq_add_cos_sq u)
    have hcos_two : Real.cos u = 2 * Real.cos (u / 2) ^ (2 : Nat) - 1 := by
      simpa [pow_two, two_mul] using (Real.cos_two_mul (u / 2))
    have hsin_half :
        4 * Real.sin (u / 2) ^ (2 : Nat) ≤ u ^ (2 : Nat) := by
      have hsq_half : Real.sin (u / 2) ^ (2 : Nat) ≤ (u / 2) ^ (2 : Nat) := Real.sin_sq_le_sq
      nlinarith
    have hrewrite : 2 - 2 * Real.cos u = 4 * Real.sin (u / 2) ^ (2 : Nat) := by
      have hsum_half : Real.sin (u / 2) ^ (2 : Nat) + Real.cos (u / 2) ^ (2 : Nat) = 1 := by
        simpa [pow_two, add_comm] using (Real.sin_sq_add_cos_sq (u / 2))
      nlinarith
    have hnorm_sq :
        ((Real.cos u - 1) ^ (2 : Nat) + Real.sin u ^ (2 : Nat))
          = 2 - 2 * Real.cos u := by
      nlinarith [hsin_cos]
    have hcalc :
        (Real.cos u - 1) ^ (2 : Nat) + Real.sin u ^ (2 : Nat)
          ≤ |u| ^ (2 : Nat) := by
      rw [hnorm_sq, hrewrite]
      have habs_sq : u ^ (2 : Nat) = |u| ^ (2 : Nat) := by
        rw [sq_abs]
      rw [← habs_sq]
      exact hsin_half
    have hsub_re : (Complex.exp (((u : ℂ) * Complex.I)) - 1).re = Real.cos u - 1 := by
      simp [hexp_re]
    have hsub_im : (Complex.exp (((u : ℂ) * Complex.I)) - 1).im = Real.sin u := by
      simp [hexp_im]
    rw [Complex.sq_norm, Complex.normSq_apply]
    rw [hsub_re, hsub_im]
    simpa [pow_two] using hcalc
  have h := (sq_le_sq).mp hsq
  simpa [abs_of_nonneg (norm_nonneg _), abs_abs] using h

-- The remaining section-7 analytic input was reduced to the pure local-gap comparison.
-- The exponentially small transport error is now handled in `HadamardCn3LocalGap`.
--
-- This is not obtainable from `normalizedCount = texPrefactor * localIntegral + Rdelta` and a bound on
-- `normalizedCount - gaussianScale` without circularity, since that residual is exactly what the
-- downstream lemmas control. The proof now proceeds through the local-gap pipeline, so the older
-- placeholder theorem block that used to follow here has been removed.
