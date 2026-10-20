module

public import CatalanArchive.CatalanLambda.Growth
public import CatalanArchive.CatalanLambda.PNTAP

@[expose] public section

/-!
# (2a-ii): `log D_h ≤ (313/105 + ε) h²` eventually, using the PNT in progressions mod 4.
-/

open Filter

namespace CatalanLambda

lemma th_eq_thetaAP (j N : ℕ) (hj : j < 4) : th j N = thetaAP 4 (j : ZMod 4) N := by
  unfold th thetaAP
  refine Finset.sum_congr (Finset.filter_congr fun n _ => ?_) fun _ _ => rfl
  rw [ZMod.natCast_eq_natCast_iff']
  rw [Nat.mod_eq_of_lt hj]

theorem th_upper (j : ℕ) (hj : j = 1 ∨ j = 3) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, th j N ≤ (1 / 2 + ε) * N := by
  have ha : ((j : ℕ) : ZMod 4) = 1 ∨ ((j : ℕ) : ZMod 4) = 3 := by
    rcases hj with rfl | rfl
    · left; rfl
    · right; rfl
  filter_upwards [theta_mod4_upper ha hε, eventually_gt_atTop 0] with N hN hN0
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN0
  rw [th_eq_thetaAP j N (by rcases hj with rfl | rfl <;> norm_num)]
  rwa [div_le_iff₀ hNp] at hN

/-- **(2a-ii)** The growth bound: for every `ε > 0`, eventually
`log D_h ≤ (313/105 + ε) h²`. -/
theorem log_Dden_le_eventually {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℕ in atTop, Real.log (Dden h) ≤ (313 / 105 + ε) * (h : ℝ) ^ 2 :=
  growth_of_theta th_upper hε

end CatalanLambda
