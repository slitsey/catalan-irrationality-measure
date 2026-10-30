import CatalanCore.Uniform.Bank.FifthsContent.M3
import CatalanCore.Uniform.Bank.Fifths.Frame
import CatalanFrames.Fifths.ContentHyb
import CatalanCore.Uniform.Content.BankShared.Reindex
import CatalanCore.Rect.MinorContent
set_option Elab.async false

/-! # Tropical (table T) bridge for the fifths family (lane B, B5c)

For a prime `p ≥ 7` with `5 (r + 2m) < p²` (one level only) and even `r ≥ 1`, every member of the
fifths family at scale `r` is `p ^ XGm`-integral, where `XGm = tropVal (HW lev p r m)` is the
level-one tropical value of the old-route instance `fifthsInst`.  The closed forms `XGm_D1x`
(sawtooth), `XGm_D2_good`, `XGm_D45_good`, `XGm_D6_good` (table T) bound it. -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.HybGen CatalanFrames.Fifths CatalanCore.Rect

/-- `ShiftData` for the new-bank fifths frames. -/
theorem shift_thirdsFrame (u : ℕ) (hu0 : 1 ≤ u) (hu1 : u < 5) (s xs δ0 : ℚ) (n0 : ℕ)
    (hs : s = ((5 : ℚ) - u) / 5) (h0 : 0 < s) (h1 : s < 1) :
    ShiftData (CatalanFrames.Thirds.thirdsFrame s 25 xs δ0 n0 h0 h1 (by norm_num)) 5 u := by
  simpa only [Nat.cast_ofNat, show ((5 : ℚ)) ^ 2 = 25 by norm_num] using
    (ShiftData.of_frame (M := 5) (u := u) (by norm_num) hu0 hu1 s xs δ0 n0 (by simpa using hs) h0 h1)

theorem fifths1_shift : ShiftData CatalanCore.Uniform.Bank.Fifths.fifths1 5 4 :=
  shift_thirdsFrame 4 (by norm_num) (by norm_num) (1/5) (3/5) (1/4) 1
    (by norm_num) (by norm_num) (by norm_num)

theorem fifths2_shift : ShiftData CatalanCore.Uniform.Bank.Fifths.fifths2 5 3 :=
  shift_thirdsFrame 3 (by norm_num) (by norm_num) (2/5) (7/10) (1/4) 1
    (by norm_num) (by norm_num) (by norm_num)

theorem fifths3_shift : ShiftData CatalanCore.Uniform.Bank.Fifths.fifths3 5 2 :=
  shift_thirdsFrame 2 (by norm_num) (by norm_num) (3/5) (3/10) (1/4) 0
    (by norm_num) (by norm_num) (by norm_num)

theorem fifths4_shift : ShiftData CatalanCore.Uniform.Bank.Fifths.fifths4 5 1 :=
  shift_thirdsFrame 1 (by norm_num) (by norm_num) (4/5) (2/5) (1/4) 0
    (by norm_num) (by norm_num) (by norm_num)

theorem fifths_T_gle {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ)
    (i : (AltE (2 / 9) two_ninths_pos Fr depth).ι) (hr : i.1 % 2 = 0) (hr1 : 1 ≤ i.1)
    (p : ℕ) [Fact p.Prime] (hp7 : 7 ≤ p) (hsq : 5 * (i.1 + 2 * F5.borderSize i.1) < p * p) :
    GLE p (XGm (fifthsInst T) i.1 (F5.borderSize i.1) p)
      ((AltE (2 / 9) two_ninths_pos Fr depth).Q i) := by
  obtain ⟨r, S⟩ := i
  have hQ := altGeom_member_commonMinor (2 / 9) two_ninths_pos Fr depth hr S
  haveI := fifthsInst_diagOK T r (F5.borderSize r)
  have hG := commonMinorPoly_gle (fifthsInst T) p r (F5.borderSize r)
    (retainedFin (F5_hyb hr) S)
  have hB := fifths_arithmetic T
  have hpp : p.Prime := Fact.out
  have hnb : p ∉ (fifthsInst T).cd.bad := by
    intro h
    simp [fifthsInst, HybInst.ofSing, fifthsCD, badPrimes] at h
    omega
  have hcnt : cntG (fifthsInst T) r (F5.borderSize r) p = 0 := by
    apply cntG_zero _ _ _ _ hpp
    rw [hB.L_eq]
    nlinarith
  have hle := tropExp_le_arithmetic hB r (F5.borderSize r) p hr1 hpp
  rw [if_neg hnb, hcnt] at hle
  simp only [if_neg hnb, Nat.cast_zero, mul_zero, add_zero, zero_add] at hle
  have hle' : tropExp (fifthsInst T) r (F5.borderSize r) p ≤ XGm (fifthsInst T) r (F5.borderSize r) p := by
    unfold XGm
    exact_mod_cast hle
  have : GLE p (XGm (fifthsInst T) r (F5.borderSize r) p)
      (commonMinorPoly Fr r (F5.borderSize r) (retainedFin (F5_hyb hr) S)) :=
    hG.mono hle'
  exact hQ ▸ this

#print axioms fifths_T_gle
end CatalanCore.Uniform.Bank.FifthsContent
