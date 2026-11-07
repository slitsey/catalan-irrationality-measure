module

public import CatalanCore.Arith.Hybrid.DefC7Inv

@[expose] public section

/-!
# Theorem C7 (j = 3, p ≡ 1 mod 4): vanishing and shape of the entries of `TcF7` used by the Schur complement
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

section Zero7

variable {o p : ℕ} [Fact p.Prime] {r m k : ℕ} (S : CSetup7 o p r m k)
include S

omit S in
lemma TCgen_zero7 {w A B : ℕ} (hw : 2 ≤ w) (hp : w = 2 → B - A ≠ p) : TCgen7 p k w A B = 0 := by
  unfold TCgen7; split_ifs <;> first | rfl | (exfalso; omega) | (exfalso; exact hp ‹_› ‹_›.2)

lemma TcF7_lt_zero {A B : ℕ} (hAB : A < B)
    (hw : 2 ≤ wC7 p r k A + wC7 p r k B) (hp : wC7 p r k A + wC7 p r k B = 2 → B - A ≠ p) :
    TcF7 p r k A B = 0 := by
  rw [TcF7_lt hAB]; exact TCgen_zero7 hw hp

/-- The columns `P0` of `Up57`: a `P0` label against `U` or a zone label. -/
lemma TcF7_P0 {c L : ℕ} (hc : c < r - p) (hL : (r - p ≤ L ∧ L < k) ∨ (r ≤ L ∧ L < r + 2 * m)) :
    TcF7 p r k c L = 0 := by
  have hkp := S.kp; have hrp := S.hrp; have hLlo := S.hLlo; have hLhi := S.hLhi
  have hcl : c < L := by omega
  have wc : wC7 p r k c = 1 := wC7_P S (by omega) (by omega)
  rcases hL with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have wl : wC7 p r k L = 0 := wC7_U S h1 h2
    rw [TcF7_lt hcl, wc, wl]
    have hs : sing7 p k c L = 0 := by
      unfold sing7; split_ifs <;> first | (exfalso; omega) | ring
    unfold TCgen7
    rw [if_neg (by omega), if_pos (by omega), hs, mul_zero]
  · by_cases hlow : L < p + k
    · apply TcF7_lt_zero S hcl
      · have := wC7_low S h1 hlow; omega
      · intro _; omega
    · apply TcF7_lt_zero S hcl
      · have := wC7_high S (A := L) (by omega); omega
      · intro _; omega

/-- A zone label against `B1`: zero unless `z - c = p`. -/
lemma TcF7_zone_B1 {c z : ℕ} (hc1 : k ≤ c) (hc2 : c < p) (hz1 : r ≤ z) (hz2 : z < r + 2 * m)
    (hzc : z - c ≠ p) : TcF7 p r k c z = 0 := by
  have hkp := S.kp; have hrp := S.hrp; have hLlo := S.hLlo
  have hcl : c < z := by omega
  have wc : wC7 p r k c = 1 := wC7_P S (by omega) (by omega)
  apply TcF7_lt_zero S hcl
  · by_cases hlow : z < p + k
    · have := wC7_low S hz1 hlow; omega
    · have := wC7_high S (A := z) (by omega); omega
  · intro _; exact hzc

/-- Zone × zone vanishes. -/
lemma TcF7_zone_zone {z y : ℕ} (hz1 : r ≤ z) (hz2 : z < r + 2 * m) (hy1 : r ≤ y)
    (hy2 : y < r + 2 * m) (hzy : z ≠ y) : TcF7 p r k z y = 0 := by
  have hkp := S.kp; have hrp := S.hrp; have hLlo := S.hLlo; have hN := S.hN
  have wz : 1 ≤ wC7 p r k z := by
    by_cases h : z < p + k
    · rw [wC7_low S hz1 h]; omega
    · rw [wC7_high S (by omega)]
  have wy : 1 ≤ wC7 p r k y := by
    by_cases h : y < p + k
    · rw [wC7_low S hy1 h]; omega
    · rw [wC7_high S (by omega)]
  rcases lt_or_gt_of_ne hzy with h | h
  · apply TcF7_lt_zero S h
    · omega
    · intro _; omega
  · rw [TcF7_symm]
    apply TcF7_lt_zero S h
    · omega
    · intro _; omega

/-- A low zone label against `U`. -/
lemma TcF7_U_low {w z : ℕ} (hw1 : r - p ≤ w) (hw2 : w < k) (hz1 : r ≤ z) (hz2 : z < p + k) :
    TcF7 p r k w z = if z - w = p then eC7 p else 0 := by
  have hkp := S.kp; have hrp := S.hrp; have hLlo := S.hLlo
  have hwz : w < z := by omega
  rw [TcF7_lt hwz, wC7_U S hw1 hw2, wC7_low S hz1 hz2]
  unfold TCgen7
  rw [if_neg (by omega), if_neg (by omega)]
  by_cases hd : z - w = p
  · have hs : sing7 p k w z = -(3 : ZMod p)⁻¹ := by
      have h3 := three_ne S.p5
      unfold sing7; split_ifs <;> first | (exfalso; omega) | (field_simp; try ring)
    rw [if_pos ⟨by omega, hd⟩, if_pos hd, hs]; rfl
  · rw [if_neg (fun h => hd h.2), if_neg hd]

end Zero7

end CatalanCore.Arith.Hybrid
