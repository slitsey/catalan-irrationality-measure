module

public import CatalanCore.Arith.Hybrid.DefC7Schur

@[expose] public section

/-!
# Theorem C7 (j = 3, p ≡ 1 mod 4) for a λ-like frame, at a prime `p < r`

`gleAt_C7_lam` (dual form): with `τ' = ∑u + ∑v` the value of the D2 potentials `wC7`,
`p^{τ' - (p + k - r - m)} · det Full(X)` is `ℤ_(p)`-integral, where `L = p + k - r ∈ [m, 2m)`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

section Final7

variable {o p : ℕ} [Fact p.Prime] {r m k : ℕ} (S : CSetup7 o p r m k)
include S

lemma CSetup7.m0 : 0 < m := by have := S.hLlo; have := S.hLhi; omega

lemma hk4_C7 : (4 : ZMod p) * (k : ZMod p) = (o : ZMod p) := S.hk4

/-- The scalar Schur complement on `U`. -/
lemma ScUU7 [Invertible (Mp57 p r k)] (u w : BU7 p r k) :
    (T57 p r k m - Up57 p r k m * ⅟(Mp57 p r k) * Wp57 p r k m) (Sum.inl u) (Sum.inl w) =
      if u = w then s0L p k else 0 := by
  have hkp := S.kp; have hrp := S.hrp
  rw [invOf_Mp57 S, Matrix.sub_apply, UpMW7 S]
  have hZ := schur_Z_C5 (j := 3) S.p5 (hk4_C7 S) (by simpa using three_ne S.p5) hkp.le (u := (u.1 : ℕ)) (w := (w.1 : ℕ))
    u.2.2 w.2.2
  simp only [Nat.cast_ofNat] at hZ
  have hZ' := congrArg (rfCH p) hZ
  have e1 : ∀ c ∈ Ico k p, rfC p (TcF7 p r k (rowlab7 p r k m (Sum.inl u)) c) *
      rfC p (TcF7 p r k c (collab7 p r k m (Sum.inl w))) =
      rfC p (Tfull p 3 k (u.1 : ℕ) c) * rfC p (Tfull p 3 k (w.1 : ℕ) c) := by
    intro c hc
    have hc' := Finset.mem_Ico.1 hc
    simp only [rowlab7, collab7, Sum.elim_inl]
    rw [TcF7_UB1 S u.2.1 u.2.2 hc'.1 hc'.2, TcF7_symm, TcF7_UB1 S w.2.1 w.2.2 hc'.1 hc'.2]
  rw [← Finset.mul_sum, Finset.sum_congr rfl e1]
  simp only [T57, Matrix.of_apply, rowlab7, collab7, Sum.elim_inl]
  rw [TcF7_UU S u.2.1 u.2.2 w.2.1 w.2.2]
  simp only [rfC_eq, map_sub, map_mul, map_sum, map_div₀, map_one, map_ofNat, apply_ite (rfCH p),
    map_zero, inv_one, one_mul] at hZ' ⊢
  have hu : u = w ↔ (u.1 : ℕ) = (w.1 : ℕ) := ⟨fun h => by rw [h], fun h => Subtype.ext (Fin.ext h)⟩
  unfold b1C7
  by_cases huw : u = w
  · simp only [huw, if_true, hu.1 huw] at hZ' ⊢
    simp only [s0L, rfC_eq, map_div₀, map_ofNat, map_add]
    linear_combination hZ'
  · simp only [if_neg huw, if_neg (fun h => huw (hu.2 h))] at hZ' ⊢
    linear_combination hZ'

lemma ScXY7 [Invertible (Mp57 p r k)] (x y : Fin m) :
    (T57 p r k m - Up57 p r k m * ⅟(Mp57 p r k) * Wp57 p r k m) (Sum.inr x) (Sum.inr y) = 0 := by
  have hkp := S.kp; have hrp := S.hrp
  have hx := x.2; have hy := y.2
  rw [invOf_Mp57 S, Matrix.sub_apply, UpMW7 S]
  have hT : T57 p r k m (Sum.inr x) (Sum.inr y) = 0 := by
    simp only [T57, Matrix.of_apply, rowlab7, collab7, Sum.elim_inr]
    rw [TcF7_zone_zone S (by omega) (by omega) (by omega) (by omega) (by omega), rfC_zero, zero_add]
  rw [hT, zero_sub, neg_eq_zero]
  refine Finset.sum_eq_zero fun c hc => ?_
  have hc' := Finset.mem_Ico.1 hc
  simp only [rowlab7, collab7, Sum.elim_inr]
  by_cases h1 : r + 2 * (x : ℕ) - c = p
  · have h2 : r + 2 * (y : ℕ) + 1 - c ≠ p := by omega
    rw [TcF7_zone_B1 S hc'.1 hc'.2 (by omega) (by omega) h2, rfC_zero, mul_zero, mul_zero]
  · rw [TcF7_symm, TcF7_zone_B1 S hc'.1 hc'.2 (by omega) (by omega) h1, rfC_zero, zero_mul, mul_zero]

lemma ScGx7 [Invertible (Mp57 p r k)] (w : BU7 p r k) (x : Fin m) (hx : r + 2 * (x : ℕ) < p + k) :
    (T57 p r k m - Up57 p r k m * ⅟(Mp57 p r k) * Wp57 p r k m) (Sum.inr x) (Sum.inl w) =
      if (w.1 : ℕ) + p = r + 2 * (x : ℕ) then rfC p (eC7 p) else 0 := by
  have hkp := S.kp; have hrp := S.hrp
  have hx' := x.2
  have hw := w.2
  rw [invOf_Mp57 S, Matrix.sub_apply, UpMW7 S]
  have hsum : ∑ c ∈ Ico k p, rfC p (b1C7 p)⁻¹ * (rfC p (TcF7 p r k (rowlab7 p r k m (Sum.inr x)) c) *
      rfC p (TcF7 p r k c (collab7 p r k m (Sum.inl w)))) = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := Finset.mem_Ico.1 hc
    simp only [rowlab7, Sum.elim_inr]
    rw [TcF7_symm, TcF7_zone_B1 S hc'.1 hc'.2 (by omega) (by omega) (by omega), rfC_zero, zero_mul, mul_zero]
  rw [hsum, sub_zero]
  simp only [T57, Matrix.of_apply, rowlab7, collab7, Sum.elim_inr, Sum.elim_inl]
  rw [TcF7_symm, TcF7_U_low S hw.1 hw.2 (by omega) hx]
  by_cases h : (w.1 : ℕ) + p = r + 2 * (x : ℕ)
  · rw [if_pos (by omega), if_pos h, add_zero]
  · rw [if_neg (by omega), if_neg h, rfC_zero, add_zero]

lemma ScGy7 [Invertible (Mp57 p r k)] (w : BU7 p r k) (y : Fin m)
    (hy : r + 2 * (y : ℕ) + 1 < p + k) :
    (T57 p r k m - Up57 p r k m * ⅟(Mp57 p r k) * Wp57 p r k m) (Sum.inl w) (Sum.inr y) =
      if (w.1 : ℕ) + p = r + 2 * (y : ℕ) + 1 then rfC p (eC7 p) else 0 := by
  have hkp := S.kp; have hrp := S.hrp
  have hy' := y.2
  have hw := w.2
  rw [invOf_Mp57 S, Matrix.sub_apply, UpMW7 S]
  have hsum : ∑ c ∈ Ico k p, rfC p (b1C7 p)⁻¹ * (rfC p (TcF7 p r k (rowlab7 p r k m (Sum.inl w)) c) *
      rfC p (TcF7 p r k c (collab7 p r k m (Sum.inr y)))) = 0 := by
    refine Finset.sum_eq_zero fun c hc => ?_
    have hc' := Finset.mem_Ico.1 hc
    simp only [collab7, Sum.elim_inr]
    rw [TcF7_zone_B1 S hc'.1 hc'.2 (by omega) (by omega) (by omega), rfC_zero, mul_zero, mul_zero]
  rw [hsum, sub_zero]
  simp only [T57, Matrix.of_apply, rowlab7, collab7, Sum.elim_inr, Sum.elim_inl]
  rw [TcF7_U_low S hw.1 hw.2 (by omega) hy]
  by_cases h : (w.1 : ℕ) + p = r + 2 * (y : ℕ) + 1
  · rw [if_pos (by omega), if_pos h, add_zero]
  · rw [if_neg (by omega), if_neg h, rfC_zero, add_zero]

end Final7

end CatalanCore.Arith.Hybrid
