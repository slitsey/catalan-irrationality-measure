module

public import CatalanCore.Uniform.Bank.Chi3Content.Exp

@[expose] public section

/-!
# `log Dnew` against the class sums of `min (wa, eExp)` (lane B, B3c)

The old route's `p6_log_Dhyb_le` with the exponent `tropExp` replaced by the smaller `eExp`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.P6 CatalanFrames.P6Hybrid

namespace CatalanCore.Uniform.Bank.Chi3Content

theorem log_Dnew_le (R : ZMod 6 → ℕ) (r m : ℕ) (hr : 1 ≤ r) (wa : ℕ → ℝ)
    (hwa0 : ∀ p, 0 ≤ wa p)
    (hwa : ∀ p, p.Prime → (tropVal (HW (p6Inst r m).lev p r m) : ℝ) ≤ wa p)
    (ht : ∀ c ∈ ({1, 5} : Finset (ZMod 6)), ∀ p, p.Prime → p ∉ (p6Inst r m).cd.bad →
      (p : ZMod 6) = c → R c < p → wa p = 0) :
    Real.log (Dnew r m) ≤
      extraG 3 Ecub 2 (badLog (p6Inst r m)) r m +
        ∑ c ∈ ({1, 5} : Finset (ZMod 6)),
          clsSum 6 c (fun p => min (wa p) (eExp r m p : ℝ)) 0 (R c) := by
  unfold Dnew
  rw [log_primeDenominator]
  have B := p6_badInfo r m
  refine sum_Bnd_le_gen B (M := 6) ({1, 5} : Finset (ZMod 6)) R r m (eExp r m)
    (fun p => min (wa p) (eExp r m p : ℝ)) (fun p => le_min (hwa0 p) (Nat.cast_nonneg _))
    (cntG (p6Inst r m) r m)
    (fun p hp => (cntG_le (p6Inst r m) r m p hp).trans (by rw [B.L_eq]))
    (fun p hp h => cntG_zero (p6Inst r m) r m p hp (by rw [B.L_eq]; exact h)) ?_
    (fun p hp hb => p6_cls r m p hp hb) ?_ ?_
  · intro p hp
    have h := tropExp_leG B r m p hr hp
    have hle : (eExp r m p : ℝ) ≤ (tropExp (p6Inst r m) r m p : ℝ) := by
      exact_mod_cast eExp_le_trop r m p
    have hc : (0 : ℝ) ≤ ((2 * (r + m) * cntG (p6Inst r m) r m p : ℕ) : ℝ) := Nat.cast_nonneg _
    by_cases hb : p ∈ (p6Inst r m).cd.bad
    · rw [if_pos hb, if_pos hb] at h ⊢
      linarith
    · rw [if_neg hb, if_neg hb] at h ⊢
      have hw := hwa p hp
      rcases le_total (wa p) (eExp r m p : ℝ) with h1 | h1
      · rw [min_eq_left h1]; linarith
      · rw [min_eq_right h1]; linarith
  · intro c hc b hb hbc
    have hb' : b ∈ ({2, 3} : Finset ℕ) := hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb' hc
    rcases hb' with rfl | rfl <;> rcases hc with rfl | rfl <;> exact absurd hbc (by decide)
  · intro c hc p hp hb hpc hRp
    have h0 := ht c hc p hp hb hpc hRp
    show min (wa p) (eExp r m p : ℝ) = 0
    rw [h0]
    exact min_eq_left (Nat.cast_nonneg _)

end CatalanCore.Uniform.Bank.Chi3Content
