module
public import CatalanMeasure.GenD.Uniform.W.ZoneZ2.ZLB
public import CatalanMeasure.GenD.Uniform.W.ZoneZ2.ZWin
public import CatalanMeasure.GenD.Uniform.Bank540.Ledger3.Fam
@[expose] public section
set_option Elab.async false

/-!
# Law_H(4): piecewise-linear closed forms (G2h)

Design-generic closed forms of `zHval` (no cap) and `zHvalCap` (cap) on their windows, as integer
inequalities with `min`, and the family-level statements `zHLB_kap_ge_nc`, `zHLB_kap_ge_cap`.

No cap (`η = H - 1 - 4p < p`), with `rt = min (n - 1 - g - 3p) ((p-1)/2)`:
`2 zHval ≥ -3p + 1 + 2 (2g + h + q + b) + 2 (min 0 (rt - g) + min 0 (η + 1 - b))`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial OAI.InternalCatalan CatalanMeasure.Parametric
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

theorem zHval_closed {P : Parameters} {N p : ℕ} (hodd : p % 2 = 1) (hA : zHApp P N p) :
    -3 * (p : ℤ) + 1 + 2 * (2 * (P.g N : ℤ) + P.h N + P.q N + P.b N) +
      2 * (min 0 ((min ((P.n N : ℤ) - 1 - P.g N - 3 * p) (((p - 1) / 2 : ℕ) : ℤ)) - P.g N) +
        min 0 (((P.H N : ℤ) - 1 - 4 * p) + 1 - P.b N)) ≤ 2 * (zHval P N p : ℤ) := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hA
  unfold zHval
  simp only
  have hp2 : 2 * ((p - 1) / 2) + 1 = p := by omega
  generalize (p - 1) / 2 = hp at *
  omega

theorem zHLB_kap_nc_eq {P : Parameters} (hP : Admissible P) {N p : ℕ} (hA : zHApp P N p) :
    (zHLBnc P hP).kap N p = zHval P N p := by
  unfold zHLBnc
  simp only [CatalanMeasure.GenD.NullityLB.ofWindow]
  simp [hA]

theorem zHLB_kap_cap_eq {P : Parameters} (hP : Admissible P) {N p : ℕ} (hA : zHAppCap P N p) :
    (zHLBcap P hP).kap N p = zHvalCap P N p := by
  unfold zHLBcap
  simp only [CatalanMeasure.GenD.NullityLB.ofWindow]
  simp [hA]

/-- Family-level bound, no cap. -/
theorem zHLB_kap_ge_nc {P : Parameters} (hP : Admissible P) {N p : ℕ} (hodd : p % 2 = 1)
    (hA : zHApp P N p) :
    -3 * (p : ℤ) + 1 + 2 * (2 * (P.g N : ℤ) + P.h N + P.q N + P.b N) +
      2 * (min 0 ((min ((P.n N : ℤ) - 1 - P.g N - 3 * p) (((p - 1) / 2 : ℕ) : ℤ)) - P.g N) +
        min 0 (((P.H N : ℤ) - 1 - 4 * p) + 1 - P.b N)) ≤ 2 * ((zHLB P hP).kap N p : ℤ) := by
  have h1 := zHval_closed hodd hA
  have h2 : (zHLBnc P hP).kap N p ≤ (zHLB P hP).kap N p := le_max_left _ _
  rw [zHLB_kap_nc_eq hP hA] at h2
  have h3 : (zHval P N p : ℤ) ≤ ((zHLB P hP).kap N p : ℤ) := by exact_mod_cast h2
  omega

/-- Family-level bound, cap window (`zHvalCap` as the `kap`). -/
theorem zHLB_kap_ge_cap {P : Parameters} (hP : Admissible P) {N p : ℕ}
    (hA : zHAppCap P N p) : zHvalCap P N p ≤ (zHLB P hP).kap N p := by
  have h2 : (zHLBcap P hP).kap N p ≤ (zHLB P hP).kap N p := le_max_right _ _
  rwa [zHLB_kap_cap_eq hP hA] at h2

/-- Family-level bound, Law_L: `zLval5 ≤ kap`. -/
theorem zLLB_kap_ge_val {P : Parameters} (hP : Admissible P) {N p : ℕ}
    (hA : zLApp5 P N p) : zLval5 P N p ≤ (zLB P hP).kap N p := by
  have h2 : (zLLB P hP).kap N p ≤ (zLB P hP).kap N p := le_max_right _ _
  rwa [zLLB_kap_eq hP hA] at h2

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
