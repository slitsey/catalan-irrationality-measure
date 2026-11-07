module

public import CatalanCore.Arith.Hybrid.DefC5Inv

@[expose] public section

/-!
# Theorem C5: vanishing and shape of the entries of `TcF` used by the Schur complement
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

section Zero

variable {o p : ℕ} [Fact p.Prime] {r m k : ℕ} (S : CSetup o p r m k)
include S

omit S in
lemma TCgen_zero {w A B : ℕ} (hw : 2 ≤ w) (hp : w = 2 → B - A ≠ p) : TCgen p k w A B = 0 := by
  unfold TCgen; split_ifs <;> first | rfl | (exfalso; omega) | (exfalso; exact hp ‹_› ‹_›.2)

lemma TcF_lt_zero {A B : ℕ} (hAB : A < B)
    (hw : 2 ≤ wC p r k A + wC p r k B) (hp : wC p r k A + wC p r k B = 2 → B - A ≠ p) :
    TcF p r k A B = 0 := by
  rw [TcF_lt hAB]; exact TCgen_zero hw hp

/-- The columns `P0` of `Up5`: a `P0` label against `U` or a zone label. -/
lemma TcF_P0 {c L : ℕ} (hc : c < r - p) (hL : (r - p ≤ L ∧ L < k) ∨ (r ≤ L ∧ L < r + 2 * m)) :
    TcF p r k c L = 0 := by
  have hkp := S.kp; have hrp := S.hrp; have hLlo := S.hLlo; have hLhi := S.hLhi
  have hcl : c < L := by omega
  have wc : wC p r k c = 1 := wC_P S (by omega) (by omega)
  rcases hL with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have wl : wC p r k L = 0 := wC_U S h1 h2
    rw [TcF_lt hcl, wc, wl]
    have hs : sing p k c L = 0 := by
      unfold sing; split_ifs <;> first | (exfalso; omega) | ring
    unfold TCgen
    rw [if_neg (by omega), if_pos (by omega), hs, mul_zero]
  · by_cases hlow : L < p + k
    · apply TcF_lt_zero S hcl
      · have := wC_low S h1 hlow; omega
      · intro _; omega
    · apply TcF_lt_zero S hcl
      · have := wC_high S (A := L) (by omega); omega
      · intro _; omega

/-- A zone label against `B1`: zero unless `z - c = p`. -/
lemma TcF_zone_B1 {c z : ℕ} (hc1 : k ≤ c) (hc2 : c < p) (hz1 : r ≤ z) (hz2 : z < r + 2 * m)
    (hzc : z - c ≠ p) : TcF p r k c z = 0 := by
  have hkp := S.kp; have hrp := S.hrp; have hLlo := S.hLlo
  have hcl : c < z := by omega
  have wc : wC p r k c = 1 := wC_P S (by omega) (by omega)
  apply TcF_lt_zero S hcl
  · by_cases hlow : z < p + k
    · have := wC_low S hz1 hlow; omega
    · have := wC_high S (A := z) (by omega); omega
  · intro _; exact hzc

/-- Zone × zone vanishes. -/
lemma TcF_zone_zone {z y : ℕ} (hz1 : r ≤ z) (hz2 : z < r + 2 * m) (hy1 : r ≤ y)
    (hy2 : y < r + 2 * m) (hzy : z ≠ y) : TcF p r k z y = 0 := by
  have hkp := S.kp; have hrp := S.hrp; have hLlo := S.hLlo; have hN := S.hN
  have wz : 1 ≤ wC p r k z := by
    by_cases h : z < p + k
    · rw [wC_low S hz1 h]; omega
    · rw [wC_high S (by omega)]
  have wy : 1 ≤ wC p r k y := by
    by_cases h : y < p + k
    · rw [wC_low S hy1 h]; omega
    · rw [wC_high S (by omega)]
  rcases lt_or_gt_of_ne hzy with h | h
  · apply TcF_lt_zero S h
    · omega
    · intro _; omega
  · rw [TcF_symm]
    apply TcF_lt_zero S h
    · omega
    · intro _; omega

/-- A low zone label against `U`. -/
lemma TcF_U_low {w z : ℕ} (hw1 : r - p ≤ w) (hw2 : w < k) (hz1 : r ≤ z) (hz2 : z < p + k) :
    TcF p r k w z = if z - w = p then eC p else 0 := by
  have hkp := S.kp; have hrp := S.hrp; have hLlo := S.hLlo
  have hwz : w < z := by omega
  rw [TcF_lt hwz, wC_U S hw1 hw2, wC_low S hz1 hz2]
  unfold TCgen
  rw [if_neg (by omega), if_neg (by omega)]
  by_cases hd : z - w = p
  · have hs : sing p k w z = -3 := by
      unfold sing; split_ifs <;> first | (exfalso; omega) | ring
    rw [if_pos ⟨by omega, hd⟩, if_pos hd, hs]; rfl
  · rw [if_neg (fun h => hd h.2), if_neg hd]

end Zero

end CatalanCore.Arith.Hybrid
