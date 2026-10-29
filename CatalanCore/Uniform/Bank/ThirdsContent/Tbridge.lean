import CatalanCore.Uniform.Bank.ThirdsContent.OfBounds
import CatalanCore.Uniform.Bank.ThirdsContent.TwoTerm
import CatalanFrames.Thirds.Instance
import CatalanFrames.Thirds.ContourInstances
import CatalanCore.Uniform.Content.BankShared.Reindex
import CatalanCore.Rect.MinorContent
set_option Elab.async false

/-! # Tropical (table T) bridge for the thirds family (lane B, B4b)

For a prime `p ≥ 5` with `3 (r + 2k) < p²` (one level only) and even `r ≥ 1`, every member of the
thirds family at scale `r` is `p ^ XGm`-integral, where `XGm = tropVal (HW lev p r k)` is the
level-one tropical value.  `XGm` is bounded by the closed forms `XGm_D1x` (sawtooth), `XGm_D2`,
`XGm_D45`, `XGm_D6` (table T, any `2 k ≤ r`). -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.HybGen CatalanFrames.Thirds CatalanCore.Rect

theorem thirds_T_gle {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (depth : ℕ)
    (i : (FamE Fr depth).ι) (hr : i.1 % 2 = 0) (hr1 : 1 ≤ i.1) (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hsq : 3 * (i.1 + 2 * G310.borderSize i.1) < p * p) :
    GLE p (XGm (thirdsInst T) i.1 (G310.borderSize i.1) p) ((FamE Fr depth).Q i) := by
  obtain ⟨r, S⟩ := i
  have hQ := altGeom_member_commonMinor (3 / 10) c310_pos Fr depth hr S
  have hG := commonMinorPoly_gle (thirdsInst T) p r (G310.borderSize r)
    (retainedFin (altGeom_hybShape (3 / 10) c310_pos hr) S)
  have hB := thirds_badInfo T
  have hpp : p.Prime := Fact.out
  have hnb : p ∉ (thirdsInst T).cd.bad := by
    intro h
    have := hB.bad_le p h
    omega
  have hcnt : cntG (thirdsInst T) r (G310.borderSize r) p = 0 := by
    apply cntG_zero _ _ _ _ hpp
    rw [hB.L_eq]
    nlinarith
  have hle := tropExp_leG hB r (G310.borderSize r) p hr1 hpp
  rw [if_neg hnb, hcnt] at hle
  simp only [if_neg hnb, Nat.cast_zero, mul_zero, add_zero, zero_add] at hle
  have hle' : tropExp (thirdsInst T) r (G310.borderSize r) p ≤ XGm (thirdsInst T) r (G310.borderSize r) p := by
    unfold XGm
    exact_mod_cast hle
  have : GLE p (XGm (thirdsInst T) r (G310.borderSize r) p)
      (commonMinorPoly Fr r (G310.borderSize r) (retainedFin (altGeom_hybShape (3 / 10) c310_pos hr) S)) :=
    hG.mono hle'
  exact hQ ▸ this


/-- Every member is `p ^ tropExp`-integral (any prime `p`, even `r ≥ 1`). -/
theorem thirds_trop_gle {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (depth : ℕ)
    (i : (FamE Fr depth).ι) (hr : i.1 % 2 = 0) (p : ℕ) [Fact p.Prime] :
    GLE p (tropExp (thirdsInst T) i.1 (G310.borderSize i.1) p) ((FamE Fr depth).Q i) := by
  obtain ⟨r, S⟩ := i
  have hQ := altGeom_member_commonMinor (3 / 10) c310_pos Fr depth hr S
  have hG := commonMinorPoly_gle (thirdsInst T) p r (G310.borderSize r)
    (retainedFin (altGeom_hybShape (3 / 10) c310_pos hr) S)
  exact hQ ▸ hG

end CatalanCore.Uniform.Bank.ThirdsContent
