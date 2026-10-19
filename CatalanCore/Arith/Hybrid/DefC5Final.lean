module

public import CatalanCore.Arith.Hybrid.DefC5Schur

@[expose] public section

/-!
# Theorem C5 for a λ-like frame, at a prime `p < r`

`gleAt_C5_lam` (dual form): with `τ' = ∑u + ∑v` the value of the D2 potentials `wC`,
`p^{τ' - (p + k - r - m)} · det Full(X)` is `ℤ_(p)`-integral, where `L = p + k - r ∈ [m, 2m)`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section Final

variable {o p : ℕ} [Fact p.Prime] {r m k : ℕ} (S : CSetup o p r m k)
include S

lemma CSetup.m0 : 0 < m := by have := S.hLlo; have := S.hLhi; omega

lemma hk4_C : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p) := S.hk4

/-- The scalar Schur complement on `U`. -/
lemma ScUU [Invertible (Mp5 p r k)] (u w : BU p r k) :
    (T5 p r k m - Up5 p r k m * ⅟(Mp5 p r k) * Wp5 p r k m) (Sum.inl u) (Sum.inl w) =
      if u = w then s0L p k else 0 := by
  have hkp := S.kp; have hrp := S.hrp
  rw [invOf_Mp5 S, Matrix.sub_apply, UpMW S]
  have hZ := schur_Z_C5 (j := 1) S.p5 (hk4_C S) (by simp) hkp.le (u := (u.1 : ℕ)) (w := (w.1 : ℕ))
    u.2.2 w.2.2
  simp only [Nat.cast_one, inv_one, one_pow] at hZ
  have hZ' := congrArg (rfCH p) hZ
  have e1 : ∀ c ∈ Ico k p, rfC p (TcF p r k (rowlab p r k m (Sum.inl u)) c) *
      rfC p (TcF p r k c (collab p r k m (Sum.inl w))) =
      rfC p (Tfull p 1 k (u.1 : ℕ) c) * rfC p (Tfull p 1 k (w.1 : ℕ) c) := by
    intro c hc
    have hc' := Finset.mem_Ico.1 hc
    simp only [rowlab, collab, Sum.elim_inl]
    rw [TcF_UB1 S u.2.1 u.2.2 hc'.1 hc'.2, TcF_symm, TcF_UB1 S w.2.1 w.2.2 hc'.1 hc'.2]
  rw [Finset.sum_congr rfl e1]
  simp only [T5, Matrix.of_apply, rowlab, collab, Sum.elim_inl]
  rw [TcF_UU S u.2.1 u.2.2 w.2.1 w.2.2]
  simp only [rfC_eq, map_sub, map_mul, map_sum, map_div₀, map_one, map_ofNat, apply_ite (rfCH p),
    map_zero, inv_one, one_mul] at hZ' ⊢
  have hu : u = w ↔ (u.1 : ℕ) = (w.1 : ℕ) := ⟨fun h => by rw [h], fun h => Subtype.ext (Fin.ext h)⟩
  by_cases huw : u = w
  · simp only [huw, if_true, hu.1 huw] at hZ' ⊢
    simp only [s0L, rfC_eq, map_div₀, map_ofNat, map_add]
    linear_combination hZ'
  · simp only [if_neg huw, if_neg (fun h => huw (hu.2 h))] at hZ' ⊢
    linear_combination hZ'

lemma ScXY [Invertible (Mp5 p r k)] (x y : Fin m) :
    (T5 p r k m - Up5 p r k m * ⅟(Mp5 p r k) * Wp5 p r k m) (Sum.inr x) (Sum.inr y) = 0 := by
  have hkp := S.kp; have hrp := S.hrp
  have hx := x.2; have hy := y.2
  rw [invOf_Mp5 S, Matrix.sub_apply, UpMW S]
  have hT : T5 p r k m (Sum.inr x) (Sum.inr y) = 0 := by
    simp only [T5, Matrix.of_apply, rowlab, collab, Sum.elim_inr]
    rw [TcF_zone_zone S (by omega) (by omega) (by omega) (by omega) (by omega), rfC_zero, zero_add]
  rw [hT, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun c hc => ?_
  have hc' := Finset.mem_Ico.1 hc
  simp only [rowlab, collab, Sum.elim_inr]
  by_cases h1 : r + 2 * (x : ℕ) - c = p
  · have h2 : r + 2 * (y : ℕ) + 1 - c ≠ p := by omega
    rw [TcF_zone_B1 S hc'.1 hc'.2 (by omega) (by omega) h2, rfC_zero, mul_zero]
  · rw [TcF_symm, TcF_zone_B1 S hc'.1 hc'.2 (by omega) (by omega) h1, rfC_zero, zero_mul]

lemma ScGx [Invertible (Mp5 p r k)] (w : BU p r k) (x : Fin m) (hx : r + 2 * (x : ℕ) < p + k) :
    (T5 p r k m - Up5 p r k m * ⅟(Mp5 p r k) * Wp5 p r k m) (Sum.inr x) (Sum.inl w) =
      if (w.1 : ℕ) + p = r + 2 * (x : ℕ) then rfC p (eC p) else 0 := by
  have hkp := S.kp; have hrp := S.hrp
  have hx' := x.2
  have hw := w.2
  rw [invOf_Mp5 S, Matrix.sub_apply, UpMW S]
  have hsum : ∑ c ∈ Ico k p, rfC p (TcF p r k (rowlab p r k m (Sum.inr x)) c) *
      rfC p (TcF p r k c (collab p r k m (Sum.inl w))) = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := Finset.mem_Ico.1 hc
    simp only [rowlab, Sum.elim_inr]
    rw [TcF_symm, TcF_zone_B1 S hc'.1 hc'.2 (by omega) (by omega) (by omega), rfC_zero, zero_mul]
  rw [hsum, sub_zero]
  simp only [T5, Matrix.of_apply, rowlab, collab, Sum.elim_inr, Sum.elim_inl]
  rw [TcF_symm, TcF_U_low S hw.1 hw.2 (by omega) hx]
  by_cases h : (w.1 : ℕ) + p = r + 2 * (x : ℕ)
  · rw [if_pos (by omega), if_pos h, add_zero]
  · rw [if_neg (by omega), if_neg h, rfC_zero, add_zero]

lemma ScGy [Invertible (Mp5 p r k)] (w : BU p r k) (y : Fin m)
    (hy : r + 2 * (y : ℕ) + 1 < p + k) :
    (T5 p r k m - Up5 p r k m * ⅟(Mp5 p r k) * Wp5 p r k m) (Sum.inl w) (Sum.inr y) =
      if (w.1 : ℕ) + p = r + 2 * (y : ℕ) + 1 then rfC p (eC p) else 0 := by
  have hkp := S.kp; have hrp := S.hrp
  have hy' := y.2
  have hw := w.2
  rw [invOf_Mp5 S, Matrix.sub_apply, UpMW S]
  have hsum : ∑ c ∈ Ico k p, rfC p (TcF p r k (rowlab p r k m (Sum.inl w)) c) *
      rfC p (TcF p r k c (collab p r k m (Sum.inr y))) = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := Finset.mem_Ico.1 hc
    simp only [collab, Sum.elim_inr]
    rw [TcF_zone_B1 S hc'.1 hc'.2 (by omega) (by omega) (by omega), rfC_zero, mul_zero]
  rw [hsum, sub_zero]
  simp only [T5, Matrix.of_apply, rowlab, collab, Sum.elim_inr, Sum.elim_inl]
  rw [TcF_U_low S hw.1 hw.2 (by omega) hy]
  by_cases h : (w.1 : ℕ) + p = r + 2 * (y : ℕ) + 1
  · rw [if_pos (by omega), if_pos h, add_zero]
  · rw [if_neg (by omega), if_neg h, rfC_zero, add_zero]

end Final

end CatalanCore.Arith.Hybrid
