module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
@[expose] public section

/-!
# Arithmetic of the `O(r log r)` error of the block energy step

`err_arith`: if `E1 ≤ C1 u`, `E3 ≤ C3 u`, `E4 ≤ C4 r u` (`u = 1 + log (1+r) ≥ 1`) and `N ≤ Nb r`,
then the explicit error of `energy_block` is at most `A r u`.
-/

namespace CatalanCore.Uniform.Decay.Nodes

set_option maxHeartbeats 4000000 in
theorem err_arith {r u N k M Kc e Cl mp Ibd Cdef Af Ab E1 E3 E4 lρ Nb C1 C3 C4 : ℝ}
    (hr : 1 ≤ r) (hu : 1 ≤ u) (hk0 : 0 ≤ k) (hkN : k ≤ N) (hNb : N ≤ Nb * r) (hNb0 : 0 ≤ Nb)
    (hM : 0 ≤ M) (hKc : 0 ≤ Kc) (hCl : 0 ≤ Cl) (hAf : 0 ≤ Af) (hAb : 0 ≤ Ab)
    (hE1 : 0 ≤ E1) (hE1u : E1 ≤ C1 * u) (hE3 : 0 ≤ E3) (hE3u : E3 ≤ C3 * u)
    (hE4 : E4 ≤ C4 * r * u) (hC4 : 0 ≤ C4) :
    2 * r * Cdef + 2 * r * Kc * |mp| + (2 * M * r * Kc + Kc ^ 2) * |Ibd|
        + (1 - e) * k * Cl + 2 * Kc * k * Af + 2 * Kc * (N - k) * Ab + (N - k) * E3
        + k * E1 + E4 / 2 + N * |lρ| ≤
      (2 * |Cdef| + 2 * Kc * |mp| + (2 * M * Kc + Kc ^ 2) * |Ibd|
        + (|1 - e| * Cl + 2 * Kc * Af + 2 * Kc * Ab + C3 + C1 + |lρ|) * Nb + C4 / 2) * r * u := by
  have hr0 : 0 ≤ r := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hN0 : 0 ≤ N := le_trans hk0 hkN
  have hru : 1 ≤ r * u := by nlinarith
  have hru0 : 0 ≤ r * u := by linarith
  have hC1 : 0 ≤ C1 := (mul_nonneg_iff_of_pos_right (by linarith : 0 < u)).mp (le_trans hE1 hE1u)
  have hC3 : 0 ≤ C3 := (mul_nonneg_iff_of_pos_right (by linarith : 0 < u)).mp (le_trans hE3 hE3u)
  -- individual bounds
  have t1 : 2 * r * Cdef ≤ 2 * |Cdef| * r * u := by
    have := le_abs_self Cdef
    nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 2 * |Cdef| * r), abs_nonneg Cdef]
  have t2 : 2 * r * Kc * |mp| ≤ 2 * Kc * |mp| * r * u := by
    nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 2 * Kc * |mp| * r)]
  have t3 : (2 * M * r * Kc + Kc ^ 2) * |Ibd| ≤ (2 * M * Kc + Kc ^ 2) * |Ibd| * r * u := by
    have a1 := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 2 * M * Kc * |Ibd| * r)
    have a2 := mul_le_mul_of_nonneg_left hru (by positivity : 0 ≤ Kc ^ 2 * |Ibd|)
    nlinarith [a1, a2]
  have hNru : N ≤ Nb * (r * u) := by nlinarith
  have t4 : (1 - e) * k * Cl ≤ |1 - e| * Cl * Nb * r * u := by
    have : (1 - e) * k * Cl ≤ |1 - e| * k * Cl := by
      have := le_abs_self (1 - e)
      nlinarith [mul_nonneg hk0 hCl]
    have h2 : |1 - e| * k * Cl ≤ |1 - e| * N * Cl := by
      nlinarith [mul_nonneg (abs_nonneg (1 - e)) hCl]
    have h3 : |1 - e| * N * Cl ≤ |1 - e| * (Nb * (r * u)) * Cl := by
      nlinarith [mul_nonneg (abs_nonneg (1 - e)) hCl]
    nlinarith
  have t5 : 2 * Kc * k * Af ≤ 2 * Kc * Af * Nb * r * u := by
    nlinarith [mul_nonneg hKc hAf]
  have t6 : 2 * Kc * (N - k) * Ab ≤ 2 * Kc * Ab * Nb * r * u := by
    nlinarith [mul_nonneg hKc hAb]
  have t7 : (N - k) * E3 ≤ C3 * Nb * r * u := by
    have h1 : (N - k) * E3 ≤ N * E3 := by nlinarith
    have h2 : N * E3 ≤ (Nb * (r * u)) * E3 := by nlinarith
    have h3 : (Nb * (r * u)) * E3 ≤ (Nb * (r * u)) * (C3 * u) := by
      apply mul_le_mul_of_nonneg_left hE3u; positivity
    nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ C3 * Nb * (r * u))]
  have t8 : k * E1 ≤ C1 * Nb * r * u := by
    have h1 : k * E1 ≤ N * E1 := by nlinarith
    have h2 : N * E1 ≤ (Nb * (r * u)) * E1 := by nlinarith
    have h3 : (Nb * (r * u)) * E1 ≤ (Nb * (r * u)) * (C1 * u) := by
      apply mul_le_mul_of_nonneg_left hE1u; positivity
    nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ C1 * Nb * (r * u))]
  have t9 : E4 / 2 ≤ C4 / 2 * r * u := by nlinarith
  have t10 : N * |lρ| ≤ |lρ| * Nb * r * u := by
    nlinarith [abs_nonneg lρ]
  nlinarith [t1, t2, t3, t4, t5, t6, t7, t8, t9, t10]

end CatalanCore.Uniform.Decay.Nodes
