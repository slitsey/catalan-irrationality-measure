module
public import CatalanMeasure.GenD.Uniform.W.ZoneZ.Groups
@[expose] public section
set_option Elab.async false

/-!
# The count identities `N_H = Law_H`, `N_L = Law_L` (arithmetic, `omega`)

zone2 sec. 5.  Not needed for the ledger (the condition-count form suffices), but it
verifies the paper's closed forms exactly.  `p = 2 hp + 1`, `s = 4`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
noncomputable section

set_option maxHeartbeats 4000000 in
/-- `N_H(4) = min(hp, η - hp) - max(g, rtop)` in the regime of zone2 sec. 5. -/
theorem zNH_eq_law (n b q g h hp : ℤ) (hp0 : 0 ≤ hp) (hg0 : 0 ≤ g) (hh0 : 0 ≤ h) (hq0 : 0 ≤ q)
    (hg : 2 * g + 1 < 2 * hp + 1) (hqh : q + h ≤ hp) (hhp : h + hp ≤ 2 * hp)
    (hb0 : 0 ≤ b) (hb : b < 2 * hp + 1)
    (hL1 : 4 * (2 * hp + 1) ≤ n + b + q) (hL2 : n + b + q < 6 * (2 * hp + 1))
    (heta1 : h + hp - 1 ≤ n + b + q + g + h - 1 - 4 * (2 * hp + 1))
    (heta2 : n + b + q + g + h - 1 - 4 * (2 * hp + 1) < 2 * (2 * hp + 1))
    (hM1 : 3 * (2 * hp + 1) ≤ n - 1 - g) (hM2 : n - 1 - g < 4 * (2 * hp + 1))
    (hr : n - 1 - g - 3 * (2 * hp + 1) ≤ hp) (hbe : b ≤ n + b + q + g + h - 1 - 4 * (2 * hp + 1) + 1)
    (ht : n + b + q + g + h - 1 - 4 * (2 * hp + 1) - (2 * hp + 1) ≤ h + hp - 1)
    (ht2 : n + b + q + g + h - 1 - 4 * (2 * hp + 1) - (2 * hp + 1) + 1 ≤
      h + max g (n - 1 - g - 3 * (2 * hp + 1))) :
    zNH n b q g h (2 * hp + 1) 4 =
      min hp (n + b + q + g + h - 1 - 4 * (2 * hp + 1) - hp) -
        max g (n - 1 - g - 3 * (2 * hp + 1)) := by
  unfold zNH pos
  simp only []
  have e : (2 * hp + 1 - 1) / 2 = hp := by omega
  rw [e]
  omega

set_option maxHeartbeats 4000000 in
/-- `N_L(4) = min(hp, L-1-4p-hp) - (b-h) - (t-b+1)_+` in the regime of zone2 sec. 5. -/
theorem zNL_eq_law (n b q g h hp : ℤ) (hp0 : 0 ≤ hp) (hg0 : 0 ≤ g) (hh0 : 0 ≤ h) (hq0 : 0 ≤ q)
    (hg : 2 * g + 1 < 2 * hp + 1) (hqh : q + h ≤ hp) (hhp : h + hp ≤ 2 * hp)
    (hb0 : 0 ≤ b) (hb : b < 2 * hp + 1)
    (hL1 : 4 * (2 * hp + 1) ≤ n + b + q) (hL2 : n + b + q < 6 * (2 * hp + 1))
    (heta1 : h + hp - 1 ≤ n + b + q + g + h - 1 - 4 * (2 * hp + 1))
    (heta2 : n + b + q + g + h - 1 - 4 * (2 * hp + 1) < 2 * (2 * hp + 1))
    (hd1 : 1 ≤ 4 * (2 * hp + 1) - (n - 1 - g)) (hd2 : 4 * (2 * hp + 1) - (n - 1 - g) ≤ hp)
    (ht : n + b + q + g + h - 1 - 4 * (2 * hp + 1) - (2 * hp + 1) ≤ h + hp - 1)
    (hpe : 2 * hp + 1 - 1 ≤ n + b + q + g + h - 1 - 4 * (2 * hp + 1)) :
    zNL n b q g h (2 * hp + 1) 4 =
      min hp (n + b + q - 1 - 4 * (2 * hp + 1) - hp) - (b - h) -
        pos (n + b + q + g + h - 1 - 4 * (2 * hp + 1) - (2 * hp + 1) - b + 1) := by
  unfold zNL pos
  simp only []
  have e : (2 * hp + 1 - 1) / 2 = hp := by omega
  rw [e]
  omega

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
