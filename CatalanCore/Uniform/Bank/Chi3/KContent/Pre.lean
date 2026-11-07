module

public import CatalanCore.Uniform.Bank.Chi3.KContent.Trop
public import CatalanCore.Uniform.Content.BankShared.KTerm.Pre
public import CatalanCore.Arith.Hybrid.PieceTools

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # The small-prime prefix bound of chi_{-3} (`PreValid`) on the k-shift route (lane K)

`KBundle.pre_gle` (instance `chi3Bundle`) is `TwoTerm.pre_gle` for the instance at the scale (`p6Inst r m`).  `p6_preValid`: for every prime `p ∤ 6` with `p ≤ r / 68`, some clearing exponent is at most
`(5/2) r + X r p`, `X` the budget `sqrtLog 5 10 + unit`. -/

namespace CatalanCore.Uniform.Bank.Chi3.KContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.TwoTerm CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.HybGen CatalanFrames.P6 CatalanFrames.P6Hybrid CatalanCore.Rect

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
  obtain ⟨n, hn, hle⟩ := chi3Bundle.pre_gle (1 / 2) c12_pos depth i hr2 (by omega) p h5 5 10 3 (5 / 2)
    (by omega) (by norm_num; omega) (by omega) (by omega) (by linarith) (by omega)
  refine ⟨n, hn, ?_⟩
  have e2 : ((qq 5 2 : ℚ) : ℝ) = 5 / 2 := by norm_num [qq]
  rw [e2]
  exact hle

end CatalanCore.Uniform.Bank.Chi3.KContent
