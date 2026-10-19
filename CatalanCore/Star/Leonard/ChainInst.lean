module

public import CatalanCore.Star.Leonard.ChainProd

/-!
# The three explicit chains (package H4): downward from `S`, downward from `0`, upward from `1`

With `Π`-projected start vectors; each `u(T~, ·)` is an explicit product times a Cauchy factor and is
nonzero (the cyclicity hypotheses of `ds_concrete`).
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

section Hc

variable [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)

include hm hθ in
lemma hc_down (y0 : ℤ)
    (H0 : 1 < n → ∃ d : F, ∃ w ∈ CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))),
      Ttil (m + n) m S θ *ᵥ wcol (m + n) θ y0 =
        (-tau (m + n) m S θ (-θ - (y0 : F))) • wcol (m + n) θ (y0 - 1) + d • wcol (m + n) θ y0 + w)
    (hy : ∀ j : ℕ, 1 ≤ j → j + 1 < n → y0 - (j : ℤ) + 1 ≤ (S : ℤ)) :
    ∀ j, j + 1 < n → ∃ a b : F, ∃ w ∈ CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))),
      Ttil (m + n) m S θ *ᵥ wcol (m + n) θ (y0 - (j : ℤ)) =
        (-tau (m + n) m S θ (-θ - ((y0 - (j : ℤ) : ℤ) : F))) • wcol (m + n) θ (y0 - ((j + 1 : ℕ) : ℤ))
          + a • wcol (m + n) θ (y0 - (j : ℤ)) + b • wcol (m + n) θ (y0 - ((j - 1 : ℕ) : ℤ)) + w := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · obtain ⟨d, w, hw, h⟩ := H0 (by omega)
    refine ⟨d, 0, w, hw, ?_⟩
    have e1 : y0 - (((0 : ℕ) + 1 : ℕ) : ℤ) = y0 - 1 := by push_cast; ring
    simp only [Nat.cast_zero, sub_zero, zero_smul, add_zero, e1]
    exact h
  · obtain ⟨d, w, hw, h⟩ := Ttil_rel m n S hm θ hθ (y0 - (j : ℤ)) (hy j hj0 hj)
    refine ⟨d, -sigma (m + n) m S θ (-θ - ((y0 - (j : ℤ) : ℤ) : F) - 1), w, hw, ?_⟩
    have e1 : y0 - ((j + 1 : ℕ) : ℤ) = y0 - (j : ℤ) - 1 := by push_cast; ring
    have e2 : y0 - ((j - 1 : ℕ) : ℤ) = y0 - (j : ℤ) + 1 := by
      rw [Nat.cast_sub hj0]; push_cast; ring
    rw [e1, e2]; exact h

include hm hθ in
lemma hc_up (y1 : ℤ)
    (H0 : 1 < n → ∃ d : F, ∃ w ∈ CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))),
      Ttil (m + n) m S θ *ᵥ wcol (m + n) θ y1 =
        (-sigma (m + n) m S θ (-θ - (y1 : F) - 1)) • wcol (m + n) θ (y1 + 1) + d • wcol (m + n) θ y1 + w)
    (hy : ∀ j : ℕ, 1 ≤ j → j + 1 < n → y1 + (j : ℤ) + 1 ≤ (S : ℤ)) :
    ∀ j, j + 1 < n → ∃ a b : F, ∃ w ∈ CatalanCore.Wsp (Wb (m + n) θ (bY m (S : ℤ))),
      Ttil (m + n) m S θ *ᵥ wcol (m + n) θ (y1 + (j : ℤ)) =
        (-sigma (m + n) m S θ (-θ - ((y1 + (j : ℤ) : ℤ) : F) - 1)) • wcol (m + n) θ (y1 + ((j + 1 : ℕ) : ℤ))
          + a • wcol (m + n) θ (y1 + (j : ℤ)) + b • wcol (m + n) θ (y1 + ((j - 1 : ℕ) : ℤ)) + w := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · obtain ⟨d, w, hw, h⟩ := H0 (by omega)
    refine ⟨d, 0, w, hw, ?_⟩
    have e1 : y1 + (((0 : ℕ) + 1 : ℕ) : ℤ) = y1 + 1 := by push_cast; ring
    simp only [Nat.cast_zero, add_zero, zero_smul, e1]
    exact h
  · obtain ⟨d, w, hw, h⟩ := Ttil_rel m n S hm θ hθ (y1 + (j : ℤ)) (hy j hj0 hj)
    refine ⟨d, -tau (m + n) m S θ (-θ - ((y1 + (j : ℤ) : ℤ) : F)), w, hw, ?_⟩
    have e1 : y1 + ((j + 1 : ℕ) : ℤ) = y1 + (j : ℤ) + 1 := by push_cast; ring
    have e2 : y1 + ((j - 1 : ℕ) : ℤ) = y1 + (j : ℤ) - 1 := by
      rw [Nat.cast_sub hj0]; push_cast; ring
    rw [e1, e2, h]; abel

end Hc

lemma cauFac_chain_ne_zero [CharZero F] {θ : F} (hθ : Gen θ) (m n S : ℕ) (y : ℕ → ℤ)
    (hy : ∀ i j : ℕ, i < n → j < n → y i = y j → i = j)
    (hd : ∀ (i : ℕ) (j : ℕ), i < m → j < n → (S : ℤ) + 1 + 2 * (i : ℤ) ≠ y j) :
    cauFac θ (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : F))
      (fun j : Fin n => ((y j : ℤ) : F))) ≠ 0 := by
  have hv : Function.Injective (Fin.addCases (m := m) (n := n) (motive := fun _ => ℤ)
      (bY m (S : ℤ)) (fun j => y j)) := by
    intro a b hab
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left i' =>
        simp only [Fin.addCases_left] at hab
        have : (i : ℕ) = i' := by simp [bY] at hab; omega
        exact congrArg _ (Fin.ext this)
      | right j' =>
        simp only [Fin.addCases_left, Fin.addCases_right] at hab
        exact absurd (by simpa [bY] using hab) (hd i j' i.2 j'.2)
    | right j =>
      induction b using Fin.addCases with
      | left i' =>
        simp only [Fin.addCases_left, Fin.addCases_right] at hab
        exact absurd (by simpa [bY] using hab.symm) (hd i' j i'.2 j.2)
      | right j' =>
        simp only [Fin.addCases_right] at hab
        exact congrArg _ (Fin.ext (hy j j' j.2 j'.2 hab))
  have := cauFac_ne_zero (F := F) hθ _ hv
  convert this using 2
  funext j
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j <;> simp

section Main


variable [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)
  (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)

include hm hθ hΔ

/-- `u(T~, Π c_S)`: the downward chain `c_S, c_{S-1}, …`. -/
theorem u_down_S (hS : n ≤ S) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) =
      (∏ k : Fin n, ∏ j ∈ Finset.range k,
          (-tau (m + n) m S θ (-θ - (((S : ℤ) - (j : ℤ) : ℤ) : F)))) *
        cauFac θ (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : F))
          (fun j : Fin n => ((((S : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : F))) := by
  have h := bkdet_Ttil_chain m n S hm θ hθ hΔ (fun j => (S : ℤ) - (j : ℤ))
    (fun j => -tau (m + n) m S θ (-θ - (((S : ℤ) - (j : ℤ) : ℤ) : F)))
    (hc_down m n S hm θ hθ (S : ℤ) (fun _ => Ttil_rel_top m n S hm θ hθ) (by intro j h1 h2; omega))
  beta_reduce at h
  rw [show (S : ℤ) - ((0 : ℕ) : ℤ) = S by simp] at h
  exact h

theorem u_down_S_ne (hS : n ≤ S) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ (S : ℤ)) ≠ 0 := by
  rw [u_down_S m n S hm θ hθ hΔ hS]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => Finset.prod_ne_zero_iff.2
    fun j hj => ?_) (cauFac_chain_ne_zero hθ m n S (fun j => (S : ℤ) - (j : ℤ))
      (by intro i j hi hj h; omega) (by intro i j hi hj; omega))
  have hjk := Finset.mem_range.1 hj
  have hk := k.2
  refine neg_ne_zero.2 (tau_ne_zero m n S θ hθ _ (by omega) ?_ ?_) <;> intro i hi <;> omega

end Main

lemma sigma_at_zero (K m S : ℕ) (θ : F) : sigma K m S θ (-θ - ((0 : ℤ) : F) - 1) = 0 := by
  have : pp K θ (-θ - ((0 : ℤ) : F) - 1) = 0 := by unfold pp; push_cast; ring
  unfold sigma; rw [this]; simp

lemma tau_at_one (K m S : ℕ) (θ : F) : tau K m S θ (-θ - ((1 : ℤ) : F)) = 0 := by
  have : pp K θ (-θ - ((1 : ℤ) : F)) = 0 := by unfold pp; push_cast; ring
  unfold tau; rw [this]; simp

section Main2

variable [CharZero F] (m n S : ℕ) (hm : 1 ≤ m) (θ : F) (hθ : Gen θ)
  (hΔ : IsUnit ((Wb (m + n) θ (bX m (S : ℤ)))ᵀ * Wb (m + n) θ (bY m (S : ℤ))).det)

include hm hθ hΔ

/-- `u(T~, Π c_0)`: the downward chain `c_0, c_{-1}, …`. -/
theorem u_down_0 (hS : n ≤ S) (hn : 1 ≤ n) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 0) =
      (∏ k : Fin n, ∏ j ∈ Finset.range k,
          (-tau (m + n) m S θ (-θ - (((0 : ℤ) - (j : ℤ) : ℤ) : F)))) *
        cauFac θ (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : F))
          (fun j : Fin n => ((((0 : ℤ) - ((j : ℕ) : ℤ) : ℤ)) : F))) := by
  have h := bkdet_Ttil_chain m n S hm θ hθ hΔ (fun j => (0 : ℤ) - (j : ℤ))
    (fun j => -tau (m + n) m S θ (-θ - (((0 : ℤ) - (j : ℤ) : ℤ) : F)))
    (hc_down m n S hm θ hθ (0 : ℤ) (fun h1 => by
      obtain ⟨d, w, hw, h⟩ := Ttil_rel m n S hm θ hθ 0 (by omega)
      rw [sigma_at_zero] at h
      exact ⟨d, w, hw, by simpa using h⟩) (by intro j h1 h2; omega))
  beta_reduce at h
  rw [show (0 : ℤ) - ((0 : ℕ) : ℤ) = 0 by simp] at h
  exact h

theorem u_down_0_ne (hS : n ≤ S) (hn : 1 ≤ n) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 0) ≠ 0 := by
  rw [u_down_0 m n S hm θ hθ hΔ hS hn]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => Finset.prod_ne_zero_iff.2
    fun j hj => ?_) (cauFac_chain_ne_zero hθ m n S (fun j => (0 : ℤ) - (j : ℤ))
      (by intro i j hi hj h; omega) (by intro i j hi hj; omega))
  refine neg_ne_zero.2 (tau_ne_zero m n S θ hθ _ (by omega) ?_ ?_) <;> intro i hi <;> omega

/-- `u(T~, Π c_1)`: the upward chain `c_1, c_2, …` (leading coefficient `r(y) = -σ(-θ-y-1)`). -/
theorem u_up_1 (hS : n ≤ S) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 1) =
      (∏ k : Fin n, ∏ j ∈ Finset.range k,
          (-sigma (m + n) m S θ (-θ - (((1 : ℤ) + (j : ℤ) : ℤ) : F) - 1))) *
        cauFac θ (Fin.addCases (fun i : Fin m => ((bY m (S : ℤ) i : ℤ) : F))
          (fun j : Fin n => ((((1 : ℤ) + ((j : ℕ) : ℤ) : ℤ)) : F))) := by
  have h := bkdet_Ttil_chain m n S hm θ hθ hΔ (fun j => (1 : ℤ) + (j : ℤ))
    (fun j => -sigma (m + n) m S θ (-θ - (((1 : ℤ) + (j : ℤ) : ℤ) : F) - 1))
    (hc_up m n S hm θ hθ (1 : ℤ) (fun h1 => by
      obtain ⟨d, w, hw, h⟩ := Ttil_rel m n S hm θ hθ 1 (by omega)
      rw [tau_at_one] at h
      exact ⟨d, w, hw, by rw [h]; simp [add_comm, add_left_comm]⟩) (by intro j h1 h2; omega))
  beta_reduce at h
  rw [show (1 : ℤ) + ((0 : ℕ) : ℤ) = 1 by simp] at h
  exact h

theorem u_up_1_ne (hS : n ≤ S) :
    CatalanCore.bkdet (Wb (m + n) θ (bY m (S : ℤ))) (Ttil (m + n) m S θ)
        (projB (m + n) θ (bX m (S : ℤ)) (bY m (S : ℤ)) *ᵥ wcol (m + n) θ 1) ≠ 0 := by
  rw [u_up_1 m n S hm θ hθ hΔ hS]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => Finset.prod_ne_zero_iff.2
    fun j hj => ?_) (cauFac_chain_ne_zero hθ m n S (fun j => (1 : ℤ) + (j : ℤ))
      (by intro i j hi hj h; omega) (by intro i j hi hj; omega))
  have hjk := Finset.mem_range.1 hj
  have hk := k.2
  refine neg_ne_zero.2 (sigma_ne_zero m n S θ hθ _ (by omega) ?_ ?_) <;> intro i hi <;> omega

end Main2

end CatalanCore.Star.Leonard
