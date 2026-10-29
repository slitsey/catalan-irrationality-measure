import CatalanCore.Uniform.Bank.ThirdsContent.Pre
import CatalanFrames.HybGen.TableSum
import CatalanCore.Uniform.Content.BankShared.BudgetAdd
set_option Elab.async false
set_option maxHeartbeats 3200000

/-! # The two ends of the thirds template (lane B, B4b)

* `thirds_tail_gle`: for `p > 4 r` every member is `p`-integral (exponent `0`): table T, branch D6.
* `thirdsBudget` and `thirds_pre_gle`: for `p ≤ 3 r/1000` the exponent is at most
  `(23/10) r + X r p` where `X` is the sum of the data-free hybrid budget (higher levels at the
  primes with `p² ≤ 5 r`) and the constant `1` on `p ≤ 3 r/1000` (rounding of `2(r+k)`). -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.SmallPrimes
  CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon CatalanFrames.HybGen
  CatalanFrames.Thirds

theorem thirds_tail_gle {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (depth : ℕ)
    (i : (FamE Fr depth).ι) (hi : (FamE Fr depth).Adm i) (p : ℕ) [hp : Fact p.Prime]
    (h : 4 * i.1 < p) : GLE p 0 ((FamE Fr depth).Q i) := by
  have hr2 : i.1 % 2 = 0 := hi.2
  rcases Nat.eq_zero_or_pos i.1 with h0 | h0
  · have := altGeom_gle_Ecrude (3 / 10) c310_pos (by norm_num) Fr depth i hr2 p
    have h00 : Ecrude (cFr Fr) i.1 p = 0 := by simp [Ecrude, h0]
    rw [h00] at this
    exact this
  · obtain ⟨hk1, hk2⟩ := border_bounds hr2
    have hp5 : 5 ≤ p := by omega
    have hsq : 3 * (i.1 + 2 * G310.borderSize i.1) < p * p := by nlinarith
    have hG := thirds_T_gle T depth i hr2 (by omega) p hp5 hsq
    have hq := thirds_kq_formula T hp5 (by
      intro h3
      have := hp.out
      have h3' : 3 ∣ p := Nat.dvd_of_mod_eq_zero h3
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp h3'
      omega)
    have hb := XGm_D6 (thirds_levels T) i.1 (G310.borderSize i.1) p hp.out hp5 (by omega) (by omega)
    have : XGm (thirdsInst T) i.1 (G310.borderSize i.1) p = 0 := by omega
    rwa [this] at hG


/-- The small-prime budget of the thirds template. -/
noncomputable def thirdsBudget : SmallBudget := SmallBudget.add (SmallBudget.sqrtLog 5 5) SmallBudget.unit

theorem thirdsBudget_X (r p : ℕ) :
    thirdsBudget.X r p = (SmallBudget.sqrtLog 5 5).X r p + (if p ≤ r then 1 else 0) := rfl

theorem thirds_pre_gle {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (depth : ℕ)
    (i : (FamE Fr depth).ι) (hi : (FamE Fr depth).Adm i) (p : ℕ) [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hpr : p ≤ 3 * i.1 / 1000) :
    ∃ n : ℕ, GLE p n ((FamE Fr depth).Q i) ∧
      (n : ℝ) ≤ 23 / 10 * (i.1 : ℝ) + thirdsBudget.X i.1 p := by
  have hr2 : i.1 % 2 = 0 := hi.2
  have hr : 600 ≤ i.1 := by omega
  obtain ⟨hk1, hk2⟩ := border_bounds hr2
  have hG := thirds_trop_gle T depth i hr2 p
  refine ⟨_, hG, ?_⟩
  set r := i.1 with hrdef
  set k := G310.borderSize r with hkdef
  have hB := thirds_badInfo T
  have hX := thirdsBudget_X r p
  rw [if_pos (by omega : p ≤ r)] at hX
  have hX0 := (SmallBudget.sqrtLog 5 5).nonneg r p
  have hle := tropExp_leG hB r k p (by omega) hp.out
  have hnb : p ∉ (thirdsInst T).cd.bad := by
    intro h; have := hB.bad_le p h; omega
  rw [if_neg hnb] at hle
  simp only [if_neg hnb, zero_add] at hle
  have hD1 : XGm (thirdsInst T) r k p ≤ 2 * (r + k) := XGm_D1 _ _ _ _
  have hXG : (tropVal (HW (thirdsInst T).lev p r k) : ℝ) ≤ 2 * ((r : ℝ) + k) := by
    have : tropVal (HW (thirdsInst T).lev p r k) ≤ 2 * (r + k) := hD1
    exact_mod_cast this
  have hkR : 20 * (k : ℝ) < 3 * r + 10 := by exact_mod_cast hk2
  have hrR : (600 : ℝ) ≤ r := by exact_mod_cast hr
  by_cases hsq : p * p ≤ 5 * r
  · rw [SmallBudget.sqrtLog_X_of 5 5 r p (by omega)] at hX
    have hcnt := cntG_le (thirdsInst T) r k p hp.out
    rw [hB.L_eq] at hcnt
    have hlog : Nat.log 2 (3 * (r + 2 * k)) ≤ Nat.log 2 r + 2 := by
      have h1 : Nat.log 2 (3 * (r + 2 * k)) ≤ Nat.log 2 (r * 2 * 2) :=
        Nat.log_mono_right (by omega)
      rw [Nat.log_mul_base (by norm_num) (by omega), Nat.log_mul_base (by norm_num) (by omega)] at h1
      omega
    have hc : (cntG (thirdsInst T) r k p : ℝ) ≤ (Nat.log 2 r : ℝ) + 2 := by
      have : cntG (thirdsInst T) r k p ≤ Nat.log 2 r + 2 := hcnt.trans hlog
      exact_mod_cast this
    have hc0 : (0 : ℝ) ≤ (cntG (thirdsInst T) r k p : ℝ) := Nat.cast_nonneg _
    have hL0 : (0 : ℝ) ≤ (Nat.log 2 r : ℝ) := Nat.cast_nonneg _
    have hcast : ((2 * (r + k) * cntG (thirdsInst T) r k p : ℕ) : ℝ) =
        2 * ((r : ℝ) + k) * cntG (thirdsInst T) r k p := by push_cast; ring
    rw [hcast] at hle
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hm : 2 * ((r : ℝ) + k) ≤ 12 / 5 * r := by nlinarith
    have h1 : 2 * ((r : ℝ) + k) * cntG (thirdsInst T) r k p ≤
        12 / 5 * r * ((Nat.log 2 r : ℝ) + 2) := by
      calc 2 * ((r : ℝ) + k) * cntG (thirdsInst T) r k p
          ≤ 12 / 5 * r * (cntG (thirdsInst T) r k p) := mul_le_mul_of_nonneg_right hm hc0
        _ ≤ 12 / 5 * r * ((Nat.log 2 r : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left hc (by positivity)
    have hr0 : (0 : ℝ) ≤ r := by linarith
    push_cast at hX
    nlinarith
  · have hz : cntG (thirdsInst T) r k p = 0 := by
      apply cntG_zero _ _ _ _ hp.out
      rw [hB.L_eq]; nlinarith
    rw [hz] at hle
    simp only [mul_zero, Nat.cast_zero, zero_add] at hle
    push_cast at hX
    nlinarith

end CatalanCore.Uniform.Bank.ThirdsContent
