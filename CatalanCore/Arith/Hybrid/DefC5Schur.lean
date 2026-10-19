module

public import CatalanCore.Arith.Hybrid.DefC5Zero

@[expose] public section

/-!
# Theorem C5: elimination of the block `𝒫`

`UpMW`: `Up5 · Minv5 · Wp5` is the sum over the block `B1 = [k, p)` only (the `P0` columns of
`Up5` and the `P0` rows of `Wp5` vanish, and `Minv5` is `1` on the diagonal of `B1` and `0` on
`B2`).
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section Elim

variable {p : ℕ} [Fact p.Prime] {r m k : ℕ} (S : CSetup p r m k)
include S

lemma TcF_UU {u w : ℕ} (hu1 : r - p ≤ u) (hu2 : u < k) (hw1 : r - p ≤ w) (hw2 : w < k) :
    TcF p r k u w = Tfull p 1 k u w := by
  rcases lt_trichotomy u w with h | h | h
  · rw [TcF_lt h, wC_U S hu1 hu2, wC_U S hw1 hw2]
    simp [TCgen, Tfull, TB, regE, h, hw2]
  · subst h
    rw [TcF_diag, wC_U S hu1 hu2]
    simp [TCDgen, Tfull, TD, regD, hu2]
  · rw [TcF_symm, Tfull_symm, TcF_lt h, wC_U S hu1 hu2, wC_U S hw1 hw2]
    simp [TCgen, Tfull, TB, regE, h, hu2]

lemma TcF_UB1 {u c : ℕ} (hu1 : r - p ≤ u) (hu2 : u < k) (hc1 : k ≤ c) (hc2 : c < p) :
    TcF p r k u c = Tfull p 1 k u c := by
  have hkp := S.kp; have hrp := S.hrp
  have huc : u < c := by omega
  rw [TcF_lt huc, wC_U S hu1 hu2, wC_P S (by omega) (by omega), Tfull_lh hu2 hc1 hc2]
  have hs : sing p k u c = -4 := by
    unfold sing; split_ifs <;> first | (exfalso; omega) | ring
  unfold TCgen
  rw [if_neg (by omega), if_pos (by omega), hs]
  simp

omit S in
lemma Ival_col_B1 {α β : ℕ} (hS : CSetup p r m k) (hα : α < r) (hb1 : k ≤ β) (hb2 : β < p) :
    Ival p r α β = if β = α then 1 else 0 := by
  have := hS.kp; have := hS.hLlo; have := hS.hrp; have := hS.hN
  unfold Ival; split_ifs <;> first | rfl | (exfalso; omega)

lemma Ival_col_B2 {α β : ℕ} (hα : r - p ≤ α) (hb : p ≤ β) (hβr : β < r) (hαr : α < r) :
    Ival p r α β = 0 := by
  have := S.kp; have := S.hLlo; have := S.hrp; have := S.hN
  unfold Ival; split_ifs <;> first | rfl | (exfalso; omega)


lemma Up5_P0 (a : BU p r k ⊕ Fin m) (α : BP p r k) (h : (α.1 : ℕ) < r - p) :
    Up5 p r k m a α = 0 := by
  simp only [Up5, Matrix.of_apply]
  rcases a with u | x
  · rw [rowlab, Sum.elim_inl, TcF_symm, TcF_P0 S h (Or.inl u.2), rfC_zero]
  · have hx := x.2
    rw [rowlab, Sum.elim_inr, TcF_symm, TcF_P0 S h (Or.inr ⟨by omega, by omega⟩), rfC_zero]

lemma Wp5_P0 (b : BU p r k ⊕ Fin m) (α : BP p r k) (h : (α.1 : ℕ) < r - p) :
    Wp5 p r k m α b = 0 := by
  simp only [Wp5, Matrix.of_apply]
  rcases b with u | y
  · rw [collab, Sum.elim_inl, TcF_P0 S h (Or.inl u.2), rfC_zero]
  · have hy := y.2
    rw [collab, Sum.elim_inr, TcF_P0 S h (Or.inr ⟨by omega, by omega⟩), rfC_zero]

lemma UpMinv_Wp_term (a b : BU p r k ⊕ Fin m) (β : BP p r k) :
    (∑ α : BP p r k, Up5 p r k m a α * Minv5 p r k α β) * Wp5 p r k m β b =
      if k ≤ (β.1 : ℕ) ∧ (β.1 : ℕ) < p then
        rfC p (TcF p r k (rowlab p r k m a) (β.1 : ℕ)) *
          rfC p (TcF p r k (β.1 : ℕ) (collab p r k m b)) else 0 := by
  have hkp := S.kp; have hrp := S.hrp; have hLlo := S.hLlo; have hN := S.hN
  have hβ := β.2
  have hβr := β.1.2
  rcases (by omega : (β.1 : ℕ) < r - p ∨ ((k ≤ (β.1 : ℕ)) ∧ (β.1 : ℕ) < p) ∨ p ≤ (β.1 : ℕ)) with
    h | h | h
  · rw [Wp5_P0 S b β h, mul_zero, if_neg (by omega)]
  · rw [if_pos h]
    have hsum : ∑ α : BP p r k, Up5 p r k m a α * Minv5 p r k α β = Up5 p r k m a β := by
      rw [Finset.sum_eq_single β]
      · simp only [Minv5, Matrix.of_apply]
        rw [Ival_col_B1 S β.1.2 h.1 h.2, if_pos rfl, rfC_one, mul_one]
      · intro α _ hα
        have : (β.1 : ℕ) ≠ (α.1 : ℕ) := fun h' => hα (Subtype.ext (Fin.ext h'.symm))
        simp only [Minv5, Matrix.of_apply]
        rw [Ival_col_B1 S α.1.2 h.1 h.2, if_neg this, rfC_zero, mul_zero]
      · intro h'; exact absurd (Finset.mem_univ _) h'
    rw [hsum]
    simp only [Up5, Wp5, Matrix.of_apply]
  · rw [if_neg (by omega)]
    have hsum : ∑ α : BP p r k, Up5 p r k m a α * Minv5 p r k α β = 0 := by
      refine Finset.sum_eq_zero fun α _ => ?_
      by_cases hα : (α.1 : ℕ) < r - p
      · rw [Up5_P0 S a α hα, zero_mul]
      · simp only [Minv5, Matrix.of_apply]
        rw [Ival_col_B2 S (by omega) h β.1.2 α.1.2, rfC_zero, mul_zero]
    rw [hsum, zero_mul]

lemma sum_BP_B1 {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ β : BP p r k, (if k ≤ (β.1 : ℕ) ∧ (β.1 : ℕ) < p then F β.1 else 0) =
      ∑ c ∈ Ico k p, F c := by
  have hrp := S.hrp
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun β _ => (β.1 : ℕ)) ?_ ?_ ?_ ?_
  · intro β hβ
    have := Finset.mem_filter.1 hβ
    simp only [Finset.mem_Ico]; exact this.2
  · intro a _ b _ h; exact Subtype.ext (Fin.ext h)
  · intro c hc
    have := Finset.mem_Ico.1 hc
    exact ⟨⟨⟨c, by omega⟩, by simp only; omega⟩, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact this, rfl⟩
  · intro β _; rfl

/-- **`Up5 · Minv5 · Wp5` is the `B1`-sum.** -/
lemma UpMW (a b : BU p r k ⊕ Fin m) :
    (Up5 p r k m * Minv5 p r k * Wp5 p r k m) a b =
      ∑ c ∈ Ico k p, rfC p (TcF p r k (rowlab p r k m a) c) *
        rfC p (TcF p r k c (collab p r k m b)) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_congr rfl (fun β _ => UpMinv_Wp_term S a b β)]
  exact sum_BP_B1 S (fun c => rfC p (TcF p r k (rowlab p r k m a) c) *
    rfC p (TcF p r k c (collab p r k m b)))

end Elim

end CatalanCore.Arith.Hybrid
