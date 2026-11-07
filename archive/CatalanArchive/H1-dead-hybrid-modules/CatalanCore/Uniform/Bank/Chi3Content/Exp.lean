module

public import CatalanCore.Uniform.Bank.Chi3Content.M3
public import CatalanFrames.P6Hybrid.QuarterPeriodicContent

@[expose] public section

/-!
# The refined exponent and denominator (lane B, B3c)

`eExp r m p = min (tropExp) (inf of the M3D prices of all valid witnesses)`.  It is a valid
`p`-integrality budget for every common-node minor, and it is dominated by the tropical exponent, so
the numerology of the old route (`sum_Bnd_le_gen`) applies unchanged.
-/

open Polynomial Finset Filter CatalanCore CatalanCore.Rect CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.P6 CatalanFrames.P6Hybrid

namespace CatalanCore.Uniform.Bank.Chi3Content

/-- The M3D prices of all valid witnesses. -/
def m3set (r m p : ℕ) : Set ℕ := {x | ∃ a b, M3Hyp r m p a b ∧ x = m3price r m p a b}

open Classical in
noncomputable def eExp (r m p : ℕ) : ℕ :=
  if (m3set r m p).Nonempty then min (tropExp (p6Inst r m) r m p) (sInf (m3set r m p))
  else tropExp (p6Inst r m) r m p

theorem eExp_le_trop (r m p : ℕ) : eExp r m p ≤ tropExp (p6Inst r m) r m p := by
  unfold eExp
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem eExp_le_m3 {r m p a b : ℕ} (h : M3Hyp r m p a b) : eExp r m p ≤ m3price r m p a b := by
  have hne : (m3set r m p).Nonempty := ⟨_, a, b, h, rfl⟩
  unfold eExp
  rw [if_pos hne]
  exact (min_le_right _ _).trans (Nat.sInf_le ⟨a, b, h, rfl⟩)

theorem eExp_gle (p : ℕ) [Fact p.Prime] (r m : ℕ) (s : Finset (Fin r)) :
    GLE p (eExp r m p) (commonMinorPoly p6Frame r m s) := by
  have ht : GLE p (tropExp (p6Inst r m) r m p) (commonMinorPoly p6Frame r m s) :=
    commonMinorPoly_gle (p6Inst r m) p r m s
  unfold eExp
  split_ifs with hne
  · rcases le_total (tropExp (p6Inst r m) r m p) (sInf (m3set r m p)) with h | h
    · rw [min_eq_left h]; exact ht
    · rw [min_eq_right h]
      obtain ⟨a, b, hM, hv⟩ := Nat.sInf_mem hne
      rw [hv]
      exact m3_gle_minor hM s
  · exact ht

theorem eExp_zero (r m p : ℕ) (hp : p.Prime) (hbig : Bnd (p6Inst r m) r m ≤ p) :
    eExp r m p = 0 := by
  have := eExp_le_trop r m p
  rw [tropExp_eq_zero (p6Inst r m) r m p hp hbig] at this
  omega

/-- The refined common denominator. -/
noncomputable def Dnew (r m : ℕ) : ℕ := primeDenominator (Bnd (p6Inst r m) r m) (eExp r m)

theorem Dnew_pos (r m : ℕ) : 0 < Dnew r m := primeDenominator_pos _ _

theorem Dnew_integral (r m : ℕ) (s : Finset (Fin r)) (j : ℕ) :
    ∃ z : ℤ, (Dnew r m : ℚ) * (commonMinorPoly p6Frame r m s).coeff j = z := by
  apply primeDenominator_integral
  intro p hp
  by_cases hb : p < Bnd (p6Inst r m) r m
  · simpa only [if_pos hb] using eExp_gle p r m s
  · simpa only [if_neg hb, eExp_zero r m p hp.out (by omega)] using eExp_gle p r m s

end CatalanCore.Uniform.Bank.Chi3Content
