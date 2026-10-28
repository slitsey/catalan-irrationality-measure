module
public import CatalanMeasure.GenD.Uniform.W.ZoneZ2.ZLB
public import CatalanMeasure.GenD.Uniform.W.ZoneZ2.ZLBcap5
public import CatalanMeasure.GenD.Uniform.W.ZoneZ2.ZWinH
@[expose] public section
set_option Elab.async false

/-!
# `zLB5`: Theorem Z at `s = 4` with the digit-`5` columns of Law_H (G2h)

`zHLBcap5` (cap, any `L`) dominates `zHLBcap` (cap, `L ≤ 5p`); `zLB5 = sup (zHLB5, zLLB)`.
The direct count `(L - 5p)` of the digit-`5` group equals the count of zone2 sec. 5
(`(r' - g)_+ + (t + 1 - h - max(g, rtop))_+` together with the part of the digit-`s` group that
lies in the window-`(s+1)` zone), so no Shift-Lemma reduction is needed for the count.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open CatalanMeasure.Parametric CatalanMeasure.GenD
noncomputable section

theorem zHLB_kap_cap5_eq {P : Parameters} (hP : Admissible P) {N p : ℕ} (hA : zHAppCap5 P N p) :
    (zHLBcap5 P hP).kap N p = zHvalCap5 P N p := by
  unfold zHLBcap5
  simp only [CatalanMeasure.GenD.NullityLB.ofWindow]
  simp [hA]

theorem zHLB_kap_cap_zero {P : Parameters} (hP : Admissible P) {N p : ℕ} (hA : ¬ zHAppCap P N p) :
    (zHLBcap P hP).kap N p = 0 := by
  unfold zHLBcap
  simp only [CatalanMeasure.GenD.NullityLB.ofWindow]
  simp [hA]

theorem zHvalCap5_eq {P : Parameters} {N p : ℕ} (hA : zHAppCap P N p) :
    zHvalCap5 P N p = zHvalCap P N p := by
  obtain ⟨a, b, c, d, e, f, hL, g, h, i⟩ := hA
  unfold zHvalCap5 zHvalCap
  have : P.L N - 5 * p = 0 := by omega
  simp only [this, Nat.add_zero]

theorem zHAppCap5_of {P : Parameters} {N p : ℕ} (hA : zHAppCap P N p) : zHAppCap5 P N p := by
  obtain ⟨a, b, c, d, e, f, hL, g, h, i⟩ := hA
  exact ⟨a, b, c, d, e, f, g, h, i⟩

theorem zHLBcap_le_cap5 {P : Parameters} (hP : Admissible P) (N p : ℕ) :
    (zHLBcap P hP).kap N p ≤ (zHLBcap5 P hP).kap N p := by
  by_cases hA : zHAppCap P N p
  · rw [zHLB_kap_cap_eq hP hA, zHLB_kap_cap5_eq hP (zHAppCap5_of hA), zHvalCap5_eq hA]
  · rw [zHLB_kap_cap_zero hP hA]; exact Nat.zero_le _

theorem zHLB_le_zHLB5 {P : Parameters} (hP : Admissible P) (N p : ℕ) :
    (zHLB P hP).kap N p ≤ (zHLB5 P hP).kap N p := by
  show max _ _ ≤ max _ _
  exact max_le_max le_rfl (zHLBcap_le_cap5 hP N p)

/-- **Theorem Z at `s = 4`, strongest form**: Law_H(4) (any `L` in the cap window) and Law_L(4). -/
def zLB5 (P : Parameters) (hP : Admissible P) : CatalanMeasure.GenD.NullityLB P :=
  CatalanMeasure.GenD.NullityLB.sup (zHLB5 P hP) (zLLB P hP)

theorem zLB_le_zLB5 {P : Parameters} (hP : Admissible P) (N p : ℕ) :
    (zLB P hP).kap N p ≤ (zLB5 P hP).kap N p := by
  show max _ _ ≤ max _ _
  exact max_le_max (zHLB_le_zHLB5 hP N p) le_rfl

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
