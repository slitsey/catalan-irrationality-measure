module

public import CatalanCore.Zeta5.CostOut.ExtGamma
public import CatalanCore.Zeta5.CostIn.Gamma

@[expose] public section

/-!
# ZC19: the bridge `p Γ(K/p) = GZ2/2`

`Apery.CostIn.Gam` is the paper's `Γ` (a `z`-integral plus `u(2T-q-5) + (u-v)₊`). For `K = 40 n`
and `K/3 < p ≤ K` (`1 ≤ x = K/p < 3`) its four-region closed form is the integer `pGam2 n p / 2`.
-/

open Finset

namespace CatalanCore.Zeta5.CostOut

open Apery Apery.CostIn

lemma floorR_div (a p : ℕ) : ⌊(a : ℝ) / p⌋ = ((a / p : ℕ) : ℤ) := by
  have h : (a : ℝ) / p = (((a : ℚ) / p : ℚ) : ℝ) := by push_cast; rfl
  rw [h, Rat.floor_cast, Rat.floor_natCast_div_natCast]
  push_cast; rfl

lemma fractR_div (a p : ℕ) (hp : 0 < p) : Int.fract ((a : ℝ) / p) = ((a % p : ℕ) : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Int.fract, floorR_div]
  have hd := Nat.div_add_mod a p
  have hd' : (p : ℝ) * ((a / p : ℕ) : ℝ) + ((a % p : ℕ) : ℝ) = a := by exact_mod_cast hd
  simp only [Int.cast_natCast]
  field_simp
  linarith


theorem p_Gam_eq {n p : ℕ} (hn : 1 ≤ n) (h1 : 40 * n < 3 * p) (hpK : p ≤ 40 * n)
    (hodd : p % 2 = 1) :
    (p : ℝ) * Gam ((40 * n : ℝ) / p) = (pGam2 n p : ℝ) / 2 := by
  have hp0n : 0 < p := by omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp0n
  have hxe : (40 * n : ℝ) / p = ((40 * n : ℕ) : ℝ) / p := by push_cast; ring
  have hfl := floorR_div (40 * n) p
  have hfr := fractR_div (40 * n) p hp0n
  have e3 : (3 / 40 : ℝ) * ((40 * n : ℝ) / p) = ((3 * n : ℕ) : ℝ) / p := by
    push_cast; field_simp
  have hN : 3 * n < p := by omega
  have hfl3 : ⌊(3 / 40 : ℝ) * ((40 * n : ℝ) / p)⌋ = 0 := by
    rw [e3, floorR_div, Nat.div_eq_of_lt hN]; rfl
  have hfr3 : Int.fract ((3 / 40 : ℝ) * ((40 * n : ℝ) / p)) = ((3 * n : ℕ) : ℝ) / p := by
    rw [e3, fractR_div _ _ hp0n, Nat.mod_eq_of_lt hN]
  have e92 : 2 * (23 / 20 : ℝ) * ((40 * n : ℝ) / p) = ((92 * n : ℕ) : ℝ) / p := by
    push_cast; field_simp; ring
  have e80 : 2 * ((40 * n : ℝ) / p) = ((80 * n : ℕ) : ℝ) / p := by
    push_cast; field_simp; ring
  have hT : Tf ((40 * n : ℝ) / p) = ((92 * n / p : ℕ) : ℤ) := by
    unfold Tf; rw [e92, floorR_div]
  have hq2 : qf ((40 * n : ℝ) / p) = ((80 * n / p : ℕ) : ℤ) := by
    unfold qf; rw [e80, floorR_div]
  have hf0 : 0 ≤ Int.fract ((40 * n : ℝ) / p) := Int.fract_nonneg _
  have hf1 := Int.fract_lt_one ((40 * n : ℝ) / p)
  have hg0 := Int.fract_nonneg ((3 / 40 : ℝ) * ((40 * n : ℝ) / p))
  have hg1 := Int.fract_lt_one ((3 / 40 : ℝ) * ((40 * n : ℝ) / p))
  have hfl' : ⌊(40 * n : ℝ) / p⌋ = ((40 * n / p : ℕ) : ℤ) := by rw [hxe]; exact hfl
  have hfr' : Int.fract ((40 * n : ℝ) / p) = ((40 * n % p : ℕ) : ℝ) / p := by rw [hxe]; exact hfr
  have hvlt := Nat.mod_lt (40 * n) hp0n
  unfold Gam
  rw [integral_GamInt, Cint_eval _ hf0 hf1 hg0 hg1]
  unfold uf vf
  rw [hT, hq2, hfl3, hfr3, hfr', hfl']
  unfold pGam2 GZ2 hwt Hq
  generalize 40 * n % p = v at hvlt ⊢
  generalize 92 * n / p = T0
  generalize 40 * n / p = q
  generalize 80 * n / p = q2
  push_cast
  have hvR : (v : ℝ) < p := by exact_mod_cast hvlt
  have hv0 : (0 : ℝ) ≤ v := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have h3n : (2 * (3 * n : ℝ)) < p := by exact_mod_cast (by omega : 2 * (3 * n) < p)
  have hg : 3 * (n : ℝ) / p < 1 / 2 := by rw [div_lt_iff₀ hp0]; linarith
  have hgm : min (3 * (n : ℝ) / p) (1 - 3 * (n : ℝ) / p) = 3 * (n : ℝ) / p :=
    min_eq_left (by linarith)
  have hpx : (p : ℝ) * (40 * n / p) = 40 * n := by field_simp
  have hmx : ∀ A : ℝ, (p : ℝ) * max A 0 = max ((p : ℝ) * A) 0 := fun A => by
    rw [mul_max_of_nonneg _ _ hp0.le, mul_zero]
  simp only [hg, hgm, ite_true]
  have hmax2 : ∀ Y : ℝ, max (Y / 2) 0 = max 0 Y / 2 := fun Y => by
    rcases le_total 0 Y with h | h
    · rw [max_eq_left (by linarith), max_eq_right h]
    · rw [max_eq_right (by linarith), max_eq_left h]; simp
  have hlast : (p : ℝ) * max (23 / 20 * (40 * (n : ℝ) / p) - (T0 : ℝ) / 2
      - (40 * (n : ℝ) / p - (q2 : ℝ) / 2)) 0 = max 0 (12 * n + p * ((q2 : ℝ) - T0)) / 2 := by
    rw [hmx, ← hmax2]
    congr 1
    field_simp
    ring
  rw [mul_add, hlast]
  by_cases hh : 2 * v < p
  · have hhR : 2 * (v : ℝ) < p := by exact_mod_cast hh
    have hf : (v : ℝ) / p < 1 / 2 := by rw [div_lt_iff₀ hp0]; linarith
    have hm1 : min ((v : ℝ) / p) (1 - (v : ℝ) / p) = (v : ℝ) / p := min_eq_left (by linarith)
    have hm2 : min (v : ℝ) ((p : ℝ) - v) = v := min_eq_left (by linarith)
    have hhZ : 2 * (v : ℤ) < (p : ℤ) := by exact_mod_cast hh
    simp only [hf, hhR, hhZ, hm1, hm2, ite_true]
    rcases le_total (v : ℝ) (3 * n) with hl | hl
    · have e1 : max ((v : ℝ) / p) (3 * (n : ℝ) / p) = 3 * (n : ℝ) / p :=
        max_eq_right (by gcongr)
      rw [e1, max_eq_right hl]
      field_simp
      ring
    · have e1 : max ((v : ℝ) / p) (3 * (n : ℝ) / p) = (v : ℝ) / p :=
        max_eq_left (by gcongr)
      rw [e1, max_eq_left hl]
      field_simp
      ring
  · have hhR : ¬ (2 * (v : ℝ) < p) := by exact_mod_cast hh
    have hf : ¬ ((v : ℝ) / p < 1 / 2) := by
      rw [not_lt, le_div_iff₀ hp0]; push Not at hhR; linarith
    have hm1 : min ((v : ℝ) / p) (1 - (v : ℝ) / p) = 1 - (v : ℝ) / p :=
      min_eq_right (by push Not at hf; linarith)
    have hm2 : min (v : ℝ) ((p : ℝ) - v) = (p : ℝ) - v := min_eq_right (by push Not at hhR; linarith)
    have hhZ : ¬ (2 * (v : ℤ) < (p : ℤ)) := by exact_mod_cast hh
    simp only [hf, hhR, hhZ, hm1, hm2, ite_false]
    rcases le_total ((p : ℝ) - v) (3 * n) with hl | hl
    · have e1 : max (1 - (v : ℝ) / p) (3 * (n : ℝ) / p) = 3 * (n : ℝ) / p := by
        refine max_eq_right ?_
        rw [show 1 - (v : ℝ) / p = ((p : ℝ) - v) / p by field_simp]
        gcongr
      rw [e1, max_eq_right hl]
      field_simp
      ring
    · have e1 : max (1 - (v : ℝ) / p) (3 * (n : ℝ) / p) = 1 - (v : ℝ) / p := by
        refine max_eq_left ?_
        rw [show 1 - (v : ℝ) / p = ((p : ℝ) - v) / p by field_simp]
        gcongr
      rw [e1, max_eq_left hl]
      field_simp
      ring

end CatalanCore.Zeta5.CostOut
