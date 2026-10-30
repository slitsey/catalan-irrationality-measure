import CatalanCore.Uniform.Bank.Sevenths.Frame
import Mathlib.Data.ZMod.Basic
set_option Elab.async false

namespace CatalanCore.Uniform.Bank.Sevenths

def seventhOffset (a : Fin 6) : ℕ := 7 - seventhNumerator a

theorem seventhOffset_bounds (a : Fin 6) :
    1 ≤ seventhOffset a ∧ seventhOffset a ≤ 6 := by
  dsimp [seventhOffset, seventhNumerator]
  have := a.isLt
  omega

/-- The actual increment-pole residue: 7 rho = 7-a modulo p. -/
noncomputable def seventhRho (a : Fin 6) (p : ℕ) : ℕ :=
  ((seventhOffset a : ZMod p) * (7 : ZMod p)⁻¹).val

theorem seventhRho_mul (a : Fin 6) (p : ℕ) [hp : Fact p.Prime] (hp8 : 8 ≤ p) :
    (7 : ZMod p) * (seventhRho a p : ZMod p) = (seventhOffset a : ZMod p) := by
  have h7 : (7 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 7 := (ZMod.natCast_eq_zero_iff 7 p).1 hz
    have := Nat.le_of_dvd (by norm_num : 0 < 7) hd
    omega
  have hv : (seventhRho a p : ZMod p) = (seventhOffset a : ZMod p) * (7 : ZMod p)⁻¹ :=
    ZMod.natCast_zmod_val _
  rw [hv]
  field_simp [h7]

theorem seventhRho_bounds (a : Fin 6) (p : ℕ) [hp : Fact p.Prime] (hp8 : 8 ≤ p) :
    1 ≤ seventhRho a p ∧ seventhRho a p < p := by
  have hlt : seventhRho a p < p := ZMod.val_lt _
  have hne : seventhRho a p ≠ 0 := by
    intro hz
    have h := seventhRho_mul a p hp8
    rw [hz, Nat.cast_zero, mul_zero] at h
    have hd : p ∣ seventhOffset a := by
      simpa only [ZMod.natCast_eq_zero_iff] using h.symm
    have := Nat.le_of_dvd (seventhOffset_bounds a).1 hd
    have := (seventhOffset_bounds a).2
    omega
  exact ⟨by omega, hlt⟩

theorem seventhRho_dvd (a : Fin 6) (p : ℕ) [Fact p.Prime] (hp8 : 8 ≤ p) :
    p ∣ 7 * seventhRho a p - seventhOffset a := by
  have hb := seventhRho_bounds a p hp8
  have ho := seventhOffset_bounds a
  have hle : seventhOffset a ≤ 7 * seventhRho a p := by omega
  have hz : ((7 * seventhRho a p - seventhOffset a : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_sub hle, Nat.cast_mul]
    exact sub_eq_zero.mpr (seventhRho_mul a p hp8)
  simpa only [ZMod.natCast_eq_zero_iff] using hz

/-- Every valid prime has one of the six exact q7 root indices. -/
theorem seventhRho_root (a : Fin 6) (p : ℕ) [hp : Fact p.Prime] (hp8 : 8 ≤ p) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 6 ∧
      7 * seventhRho a p = j * p + seventhOffset a := by
  have hb := seventhRho_bounds a p hp8
  have ho := seventhOffset_bounds a
  have hle : seventhOffset a ≤ 7 * seventhRho a p := by omega
  obtain ⟨j, hj⟩ := seventhRho_dvd a p hp8
  have he : 7 * seventhRho a p = j * p + seventhOffset a := by
    have h := Nat.sub_add_cancel hle
    rw [hj] at h
    nlinarith
  have hj0 : 1 ≤ j := by
    by_contra h
    have hz : j = 0 := by omega
    rw [hz, zero_mul] at he
    omega
  have hj6 : j ≤ 6 := by
    by_contra h
    have hh := Nat.mul_le_mul_left p (show 7 ≤ j by omega)
    nlinarith
  exact ⟨j, hj0, hj6, he⟩

theorem seventh_palette_root (a : Fin 6) (p : ℕ) [Fact p.Prime] (hp8 : 8 ≤ p) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ 6 ∧
      7 * (seventhRho a p - 1) + seventhNumerator a = j * p := by
  obtain ⟨j, hj0, hj6, he⟩ := seventhRho_root a p hp8
  have hb := seventhRho_bounds a p hp8
  have ha : seventhNumerator a ≤ 7 := by dsimp [seventhNumerator]; have := a.isLt; omega
  have ho : seventhOffset a + seventhNumerator a = 7 := Nat.sub_add_cancel ha
  exact ⟨j, hj0, hj6, by omega⟩

#print axioms seventhRho_dvd
#print axioms seventh_palette_root
end CatalanCore.Uniform.Bank.Sevenths
