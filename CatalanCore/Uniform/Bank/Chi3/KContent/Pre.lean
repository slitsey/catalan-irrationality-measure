module

public import CatalanCore.Uniform.Bank.Chi3.KContent.Trop
public import CatalanCore.Arith.Hybrid.PieceTools

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # The small-prime prefix bound of chi_{-3} (`PreValid`) on the k-shift route (lane K)

`p6_pre_gle` is `TwoTerm.pre_gle` for the P6 instance at the scale (`p6Inst r m`), whose diagonal set depends on `(r, m)`
so that the generic lemma (`[∀ r m, I.DiagOK r m]`) does not apply; the body is the same: the tropical bridge, `D1`, and the
counting of the levels.  `p6_preValid`: for every prime `p ∤ 6` with `p ≤ r / 68`, some clearing exponent is at most
`(5/2) r + X r p`, `X` the budget `sqrtLog 5 10 + unit`. -/

namespace CatalanCore.Uniform.Bank.Chi3.KContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.TwoTerm CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.HybGen CatalanFrames.P6 CatalanFrames.P6Hybrid CatalanCore.Rect

/-- **The tropical exponent bridge at `p6Inst r m`.** -/
theorem p6_gle_tropExp (c : ℚ) (hc : 0 < c) (depth : ℕ) (i : ((altGeom c hc).family p6Frame depth).ι)
    (hr : i.1 % 2 = 0) (p : ℕ) [Fact p.Prime] :
    GLE p (tropExp (p6Inst i.1 ((altGeom c hc).borderSize i.1)) i.1 ((altGeom c hc).borderSize i.1) p)
      (((altGeom c hc).family p6Frame depth).Q i) := by
  obtain ⟨r, S⟩ := i
  haveI := p6Inst_diagOK r ((altGeom c hc).borderSize r)
  have hQ := altGeom_member_commonMinor c hc p6Frame depth hr S
  have hG0 := commonMinorPoly_gle (p6Inst r ((altGeom c hc).borderSize r)) p r ((altGeom c hc).borderSize r)
    (retainedFin (altGeom_hybShape c hc hr) S)
  exact hQ ▸ hG0

/-- **`pre_gle` for P6.** -/
theorem p6_pre_gle (c : ℚ) (hc : 0 < c) (depth : ℕ) (i : ((altGeom c hc).family p6Frame depth).ι)
    (hr : i.1 % 2 = 0) (hr1 : 1 ≤ i.1) (p : ℕ) [hp : Fact p.Prime] (h5 : 5 ≤ p)
    (A C e : ℕ) (α0 : ℝ)
    (hA : 3 * (i.1 + 2 * (altGeom c hc).borderSize i.1) ≤ A * i.1)
    (he : 3 * (i.1 + 2 * (altGeom c hc).borderSize i.1) ≤ i.1 * 2 ^ e)
    (hC1 : 2 * (i.1 + (altGeom c hc).borderSize i.1) * e ≤ C * i.1)
    (hC2 : 2 * (i.1 + (altGeom c hc).borderSize i.1) ≤ C * i.1)
    (h0 : 2 * ((i.1 : ℝ) + (altGeom c hc).borderSize i.1) ≤ α0 * i.1 + 1) (hpr : p ≤ i.1) :
    ∃ n : ℕ, GLE p n (((altGeom c hc).family p6Frame depth).Q i) ∧
      (n : ℝ) ≤ α0 * i.1 + (SmallBudget.add (SmallBudget.sqrtLog A C) SmallBudget.unit).X i.1 p := by
  have hG0 := p6_gle_tropExp c hc depth i hr p
  set r := i.1 with hrdef
  set m := (altGeom c hc).borderSize r with hmdef
  have hG : GLE p (tropExp (p6Inst r m) r m p) (((altGeom c hc).family p6Frame depth).Q i) := hG0
  refine ⟨_, hG, ?_⟩
  have hL : (p6Inst r m).cd.L = 3 := (p6_badInfo r m).L_eq
  have hnb : p ∉ (p6Inst r m).cd.bad := by
    intro hb
    have := (p6_badInfo r m).bad_le p hb
    omega
  have hX : (SmallBudget.add (SmallBudget.sqrtLog A C) SmallBudget.unit).X r p =
      (SmallBudget.sqrtLog A C).X r p + 1 := by
    show (SmallBudget.sqrtLog A C).X r p + SmallBudget.unit.X r p = _
    congr 1
    simp [SmallBudget.unit, SmallBudget.ofCutoff, hpr]
  have hX0 := (SmallBudget.sqrtLog A C).nonneg r p
  have hle := tropExp_le_good (p6Inst r m) r m p hr1 hp.out hnb
  have hD1 : XGm (p6Inst r m) r m p ≤ 2 * (r + m) := XGm_D1 _ _ _ _
  have hXG : (tropVal (HW (p6Inst r m).lev p r m) : ℝ) ≤ 2 * ((r : ℝ) + m) := by
    have : tropVal (HW (p6Inst r m).lev p r m) ≤ 2 * (r + m) := hD1
    exact_mod_cast this
  rw [hX]
  by_cases hsq : p * p ≤ A * r
  · rw [SmallBudget.sqrtLog_X_of A C r p hsq]
    have hcnt := cntG_le (p6Inst r m) r m p hp.out
    rw [hL] at hcnt
    have hlog : Nat.log 2 (3 * (r + 2 * m)) ≤ Nat.log 2 r + e := by
      rw [← log2_mul_pow r e (by omega)]
      exact Nat.log_mono_right he
    have hcn : 2 * (r + m) * cntG (p6Inst r m) r m p ≤ C * r * (Nat.log 2 r + 1) := by
      have h1 : 2 * (r + m) * cntG (p6Inst r m) r m p ≤ 2 * (r + m) * (Nat.log 2 r + e) :=
        Nat.mul_le_mul_left _ (hcnt.trans hlog)
      have h2 : 2 * (r + m) * Nat.log 2 r ≤ C * r * Nat.log 2 r := Nat.mul_le_mul_right _ hC2
      calc 2 * (r + m) * cntG (p6Inst r m) r m p ≤ 2 * (r + m) * (Nat.log 2 r + e) := h1
        _ = 2 * (r + m) * Nat.log 2 r + 2 * (r + m) * e := by ring
        _ ≤ C * r * Nat.log 2 r + C * r := Nat.add_le_add h2 hC1
        _ = C * r * (Nat.log 2 r + 1) := by ring
    have hcn' : ((2 * (r + m) * cntG (p6Inst r m) r m p : ℕ) : ℝ) ≤ (C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1) := by
      have h := (Nat.cast_le (α := ℝ)).2 hcn
      have e : ((C * r * (Nat.log 2 r + 1) : ℕ) : ℝ) = (C : ℝ) * r * ((Nat.log 2 r : ℝ) + 1) := by
        push_cast; ring
      rw [e] at h
      exact h
    linarith
  · push Not at hsq
    have hz : cntG (p6Inst r m) r m p = 0 := by
      apply cntG_zero _ _ _ _ hp.out
      rw [hL, pow_two]
      omega
    rw [hz] at hle
    simp only [mul_zero, Nat.cast_zero, zero_add] at hle
    linarith

/-- **The prefix bound of chi_{-3}**: `p ∤ 6`, `p ≤ r / 68`. -/
theorem p6_preValid (depth : ℕ) :
    PreValid (1 / 2) c12_pos p6Frame depth 6
      (SmallBudget.add (SmallBudget.sqrtLog 5 10) SmallBudget.unit) (qq 1 68) (qq 5 2) := by
  intro i hi p _ hpM h
  have hp : p.Prime := Fact.out
  have e1 : ((qq 1 68 : ℚ) : ℝ) = ((1 : ℕ) : ℝ) / ((68 : ℕ) : ℝ) := by norm_num [qq]
  rw [e1, floor_frac 1 68 i.1] at h
  have h68 : 68 * p ≤ i.1 := by omega
  have h5 : 5 ≤ p := by
    have h2 : p ≠ 2 := fun h => hpM (by rw [h]; norm_num)
    have h3 : p ≠ 3 := fun h => hpM (by rw [h]; norm_num)
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
    have := hp.two_le
    omega
  have hr2 : i.1 % 2 = 0 := hi.2
  obtain ⟨hb1, hb2⟩ := altGeom_border_nat (1 / 2) c12_pos 1 2 (by norm_num) (by norm_num) hr2
  have hR : (4 * (altGeom (1 / 2) c12_pos).borderSize i.1 : ℝ) < i.1 + 2 := by
    have : 4 * (altGeom (1 / 2) c12_pos).borderSize i.1 < i.1 + 2 := by omega
    exact_mod_cast this
  obtain ⟨n, hn, hle⟩ := p6_pre_gle (1 / 2) c12_pos depth i hr2 (by omega) p h5 5 10 3 (5 / 2)
    (by omega) (by norm_num; omega) (by omega) (by omega) (by linarith) (by omega)
  refine ⟨n, hn, ?_⟩
  have e2 : ((qq 5 2 : ℚ) : ℝ) = 5 / 2 := by norm_num [qq]
  rw [e2]
  exact hle

end CatalanCore.Uniform.Bank.Chi3.KContent
