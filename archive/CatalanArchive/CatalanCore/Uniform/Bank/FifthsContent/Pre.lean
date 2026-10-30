import CatalanCore.Uniform.Bank.FifthsContent.Cov
import CatalanCore.Uniform.Content.BankShared.BudgetAdd
import CatalanFrames.HybGen.TableSum
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # Prefix and tail bounds of the fifths template (lane B, B5c)

`B5`: the small-prime budget (higher levels at `p^2 <= 7 r`, rounding `1` at `p <= r`, and the early
scales `r < R0`).  `pre5`: for `p <= r/900` some `n` clearing the member satisfies
`n <= (20/9) r + B5.X r p`.  `tail5`: beyond `(63/10) r` the member is cleared with exponent `0`. -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Fifths CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.SmallPrimes
  CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon CatalanFrames.HybGen
  CatalanFrames.Fifths

/-- The small-prime budget of the fifths template. -/
noncomputable def B5 : SmallBudget :=
  (SmallBudget.sqrtLog 7 122).add (SmallBudget.unit.add (SmallBudget.early R0 2600000000))

theorem B5_X (r p : ℕ) : B5.X r p = (SmallBudget.sqrtLog 7 122).X r p +
    (SmallBudget.unit.X r p + (SmallBudget.early R0 2600000000).X r p) := rfl

theorem unit_X_of {r p : ℕ} (h : p ≤ r) : SmallBudget.unit.X r p = 1 := by
  simp [SmallBudget.unit, SmallBudget.ofCutoff, h]

theorem early_X_of {r p : ℕ} (h : p ≤ r) (hr : r < R0) :
    (SmallBudget.early R0 2600000000).X r p = 2600000000 := by
  simp [SmallBudget.early, SmallBudget.ofCutoff, h, hr]

theorem Ecrude_log (cE : ℕ) (hcE : cE ≤ 49) (r p : ℕ) (hp : 2 ≤ p) :
    Ecrude cE r p ≤ 122 * r * (Nat.log 2 r + 1) := by
  rcases Nat.eq_zero_or_pos r with h0 | hr
  · subst h0; simp [Ecrude]
  unfold Ecrude
  have h1 : Nat.log p (14 * r) ≤ Nat.log 2 r + 4 := by
    refine (Nat.log_anti_left (by omega) hp).trans ?_
    have hL : r < 2 ^ (Nat.log 2 r + 1) := Nat.lt_pow_succ_log_self (by omega) r
    have : Nat.log 2 (14 * r) < Nat.log 2 r + 5 := by
      refine Nat.log_lt_of_lt_pow (by omega) ?_
      have h16 : 14 * r < 2 ^ (Nat.log 2 r + 5) := by
        have : 2 ^ (Nat.log 2 r + 5) = 16 * 2 ^ (Nat.log 2 r + 1) := by ring
        rw [this]; omega
      exact h16
    omega
  have h2 : 3 * Nat.log p (14 * r) + cE ≤ 61 * (Nat.log 2 r + 1) := by omega
  calc 2 * r * (3 * Nat.log p (14 * r) + cE) ≤ 2 * r * (61 * (Nat.log 2 r + 1)) :=
        Nat.mul_le_mul_left _ h2
    _ = 122 * r * (Nat.log 2 r + 1) := by ring

theorem pre5 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth : ℕ) (hcF : cFr Fr ≤ 49)
    (i : (AltE (2 / 9) two_ninths_pos Fr depth).ι)
    (hi : (AltE (2 / 9) two_ninths_pos Fr depth).Adm i) (p : ℕ) (hp : p.Prime)
    (h : p ≤ ⌊(1 / 900 : ℝ) * (F5.scale i : ℝ)⌋₊) [Fact p.Prime] :
    ∃ n : ℕ, GLE p n ((AltE (2 / 9) two_ninths_pos Fr depth).Q i) ∧
      (n : ℝ) ≤ (20 / 9 : ℝ) * (F5.scale i : ℝ) + B5.X (F5.scale i) p := by
  have hsc : F5.scale i = i.1 := rfl
  rw [hsc]
  have h900 : 900 * p ≤ i.1 := by
    have h' := (Nat.le_floor_iff (by positivity)).1 h
    rw [hsc] at h'
    have : (900 * p : ℝ) ≤ i.1 := by linarith
    exact_mod_cast this
  have hgl := altGeom_gle_Ecrude (2 / 9) two_ninths_pos (by norm_num) Fr depth i hi.2 p
  have hB0 := (SmallBudget.sqrtLog 7 122).nonneg i.1 p
  have hB1 := SmallBudget.unit.nonneg i.1 p
  have hB2 := (SmallBudget.early R0 2600000000).nonneg i.1 p
  by_cases hR : R0 ≤ i.1
  · by_cases hs : p * p ≤ 7 * i.1
    · refine ⟨_, hgl, ?_⟩
      have hX := SmallBudget.sqrtLog_X_of 7 122 i.1 p hs
      have hE := Ecrude_log (cFr Fr) hcF i.1 p hp.two_le
      have hE' : ((Ecrude (cFr Fr) i.1 p : ℕ) : ℝ) ≤ 122 * (i.1 : ℝ) * ((Nat.log 2 i.1 : ℝ) + 1) := by
        exact_mod_cast hE
      rw [B5_X, hX]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) i.1]
    · push Not at hs
      have hp7 : 7 ≤ p := by
        by_contra hc
        push Not at hc
        have : p * p ≤ 6 * 6 := Nat.mul_le_mul (by omega) (by omega)
        unfold R0 at hR
        omega
      obtain ⟨hr, hb1, hb2⟩ := member_dom depth hi
      have hsq : 5 * (i.1 + 2 * F5.borderSize i.1) < p * p := by unfold R0 at hR; omega
      have hr1 : 1 ≤ i.1 := by unfold R0 at hR; omega
      have hg := fifths_T_gle T depth i hr hr1 p hp7 hsq
      refine ⟨_, hg, ?_⟩
      have hD1 := XGm_D1 (fifthsInst T) i.1 (F5.borderSize i.1) p
      have hn : 9 * XGm (fifthsInst T) i.1 (F5.borderSize i.1) p ≤ 20 * i.1 + 8 := by omega
      have hn' : (9 : ℝ) * (XGm (fifthsInst T) i.1 (F5.borderSize i.1) p : ℝ) ≤ 20 * i.1 + 8 := by
        exact_mod_cast hn
      have hpr : p ≤ i.1 := by omega
      have hu := unit_X_of hpr
      rw [B5_X]
      rw [hu] at *
      nlinarith
  · push Not at hR
    refine ⟨_, hgl, ?_⟩
    have hpr : p ≤ i.1 := by omega
    have he := early_X_of hpr hR
    have hE := Ecrude_small5 (cFr Fr) hcF i.1 p hR hp.two_le
    have hE' : ((Ecrude (cFr Fr) i.1 p : ℕ) : ℝ) ≤ 2600000000 := by exact_mod_cast hE
    rw [B5_X, he]
    nlinarith [Nat.cast_nonneg (α := ℝ) i.1]

theorem tail5 {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u) (depth j : ℕ) (hj : 1 ≤ j)
    (i : (AltE (2 / 9) two_ninths_pos Fr depth).ι)
    (hi : (AltE (2 / 9) two_ninths_pos Fr depth).Adm i) (p : ℕ) (hp : p.Prime)
    (hk : 1 ≤ i.1 → 5 * (fifthsInst T).cd.kq p = j * p + u) (h : 63 * i.1 / 10 < p) [Fact p.Prime] :
    GLE p 0 ((AltE (2 / 9) two_ninths_pos Fr depth).Q i) := by
  rcases Nat.eq_zero_or_pos i.1 with h0 | hr1
  · have := altGeom_gle_Ecrude (2 / 9) two_ninths_pos (by norm_num) Fr depth i hi.2 p
    rw [h0] at this
    simpa [Ecrude] using this
  obtain ⟨hr, hb1, hb2⟩ := member_dom depth hi
  have hk := hk hr1
  have hu0 := T.hu0
  have hjp : p ≤ j * p := Nat.le_mul_of_pos_left p hj
  generalize j * p = t at hk hjp
  have hp7 : 7 ≤ p := by omega
  have hpp : 13 * p ≤ p * p := Nat.mul_le_mul_right p (by omega)
  have hsq : 5 * (i.1 + 2 * F5.borderSize i.1) < p * p := by omega
  have hg := fifths_T_gle T depth i hr hr1 p hp7 hsq
  have hD6 := XGm_D6_good (fifths_levels T) i.1 (F5.borderSize i.1) p hp hp7 (by omega) (by omega)
  have hz : XGm (fifthsInst T) i.1 (F5.borderSize i.1) p = 0 := by omega
  rwa [hz] at hg

#print axioms pre5
#print axioms tail5
end CatalanCore.Uniform.Bank.FifthsContent
