import CatalanCore.Uniform.Bank.Chi3Rank.RankExp
import CatalanCore.Uniform.Bank.Chi3Content.Final
set_option Elab.async false

/-! # The rank-refined exponent and denominator (lane H, H16)

`eExp2 r m p = rankExp (eExp r m p) r m p`: B3c's M3D/tropical exponent with the rank layer
`min`'d in per prime.  It is a valid `p`-integrality budget of every common-node minor, it is
dominated by `eExp`, and so by the tropical exponent, hence the numerology of the old route applies
unchanged to `Dnew2`. -/

open Polynomial Finset Filter CatalanCore CatalanCore.Rect CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.P6 CatalanFrames.P6Hybrid
  CatalanCore.Uniform.Bank.Chi3Content

namespace CatalanCore.Uniform.Bank.Chi3Rank

/-- The rank-refined exponent. -/
noncomputable def eExp2 (r m p : ℕ) : ℕ := rankExp (eExp r m p) r m p

theorem eExp2_le (r m p : ℕ) : eExp2 r m p ≤ eExp r m p := rankExp_le _ _ _ _

theorem eExp2_le_trop (r m p : ℕ) : eExp2 r m p ≤ tropExp (p6Inst r m) r m p :=
  (eExp2_le r m p).trans (eExp_le_trop r m p)

theorem eExp2_gle (p : ℕ) [Fact p.Prime] (r m : ℕ) (s : Finset (Fin r)) :
    GLE p (eExp2 r m p) (commonMinorPoly p6Frame r m s) :=
  rankExp_gle p r m _ s (eExp_gle p r m s)

theorem eExp2_zero (r m p : ℕ) (hp : p.Prime) (hbig : Bnd (p6Inst r m) r m ≤ p) :
    eExp2 r m p = 0 := by
  have := eExp2_le r m p
  rw [eExp_zero r m p hp hbig] at this
  omega

/-- The rank-refined common denominator. -/
noncomputable def Dnew2 (r m : ℕ) : ℕ := primeDenominator (Bnd (p6Inst r m) r m) (eExp2 r m)

theorem Dnew2_pos (r m : ℕ) : 0 < Dnew2 r m := primeDenominator_pos _ _

theorem Dnew2_integral (r m : ℕ) (s : Finset (Fin r)) (j : ℕ) :
    ∃ z : ℤ, (Dnew2 r m : ℚ) * (commonMinorPoly p6Frame r m s).coeff j = z := by
  apply primeDenominator_integral
  intro p hp
  by_cases hb : p < Bnd (p6Inst r m) r m
  · simpa only [if_pos hb] using eExp2_gle p r m s
  · simpa only [if_neg hb, eExp2_zero r m p hp.out (by omega)] using eExp2_gle p r m s

/-- `log Dnew2` against the class sums of `min (wa, eExp2)`. -/
theorem log_Dnew2_le (R : ZMod 6 → ℕ) (r m : ℕ) (hr : 1 ≤ r) (wa : ℕ → ℝ)
    (hwa0 : ∀ p, 0 ≤ wa p)
    (hwa : ∀ p, p.Prime → (tropVal (HW (p6Inst r m).lev p r m) : ℝ) ≤ wa p)
    (ht : ∀ c ∈ ({1, 5} : Finset (ZMod 6)), ∀ p, p.Prime → p ∉ (p6Inst r m).cd.bad →
      (p : ZMod 6) = c → R c < p → wa p = 0) :
    Real.log (Dnew2 r m) ≤
      extraG 3 Ecub 2 (badLog (p6Inst r m)) r m +
        ∑ c ∈ ({1, 5} : Finset (ZMod 6)),
          clsSum 6 c (fun p => min (wa p) (eExp2 r m p : ℝ)) 0 (R c) := by
  unfold Dnew2
  rw [log_primeDenominator]
  have B := p6_badInfo r m
  refine sum_Bnd_le_gen B (M := 6) ({1, 5} : Finset (ZMod 6)) R r m (eExp2 r m)
    (fun p => min (wa p) (eExp2 r m p : ℝ)) (fun p => le_min (hwa0 p) (Nat.cast_nonneg _))
    (cntG (p6Inst r m) r m)
    (fun p hp => (cntG_le (p6Inst r m) r m p hp).trans (by rw [B.L_eq]))
    (fun p hp h => cntG_zero (p6Inst r m) r m p hp (by rw [B.L_eq]; exact h)) ?_
    (fun p hp hb => p6_cls r m p hp hb) ?_ ?_
  · intro p hp
    have h := tropExp_leG B r m p hr hp
    have hle : (eExp2 r m p : ℝ) ≤ (tropExp (p6Inst r m) r m p : ℝ) := by
      exact_mod_cast eExp2_le_trop r m p
    have hc : (0 : ℝ) ≤ ((2 * (r + m) * cntG (p6Inst r m) r m p : ℕ) : ℝ) := Nat.cast_nonneg _
    by_cases hb : p ∈ (p6Inst r m).cd.bad
    · rw [if_pos hb, if_pos hb] at h ⊢
      linarith
    · rw [if_neg hb, if_neg hb] at h ⊢
      have hw := hwa p hp
      rcases le_total (wa p) (eExp2 r m p : ℝ) with h1 | h1
      · rw [min_eq_left h1]; linarith
      · rw [min_eq_right h1]; linarith
  · intro c hc b hb hbc
    have hb' : b ∈ ({2, 3} : Finset ℕ) := hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb' hc
    rcases hb' with rfl | rfl <;> rcases hc with rfl | rfl <;> exact absurd hbc (by decide)
  · intro c hc p hp hb hpc hRp
    have h0 := ht c hc p hp hb hpc hRp
    show min (wa p) (eExp2 r m p : ℝ) = 0
    rw [h0]
    exact min_eq_left (Nat.cast_nonneg _)

end CatalanCore.Uniform.Bank.Chi3Rank
