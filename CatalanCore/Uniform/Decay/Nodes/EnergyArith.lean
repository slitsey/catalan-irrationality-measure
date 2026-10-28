module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
@[expose] public section

/-!
# The arithmetic core of the block-node energy step (Part 1, Lemma `general-energy`)

Pure real arithmetic, no analysis: all aggregated inequalities of the proof (CPD lower bound for
the restored-node energy, the three node-sum discrepancies, the free-point and removed-node
`g`-bounds with the mass-rounding `N = M r + O(1)`, the cap sum, the log-weights) are hypotheses;
the conclusion is the quadratic bound
`LHS ≤ -(2 M m' + 2 S - M² I + J) r² + c r (N - k) + Err`.
-/

namespace CatalanCore.Uniform.Decay.Nodes

set_option maxHeartbeats 4000000 in
theorem block_arith
    {r N k M Kc e ε Cl mp ℓ cB Ibd Irho Scap Cdef J E1 E2 E3 E4 Af Ab lρ P : ℝ}
    {SI SIr Slq SY SYb SU SUb Sg Bexp ASs PSs RSs LHS : ℝ}
    (hr : 0 < r) (hk0 : 0 ≤ k) (hkN : k ≤ N) (hNM : |N - M * r| ≤ Kc) (hM : 0 ≤ M)
    (hKc : 0 ≤ Kc) (hCl : 0 ≤ Cl) (hP : 0 ≤ P) (he : e ≤ ε) (hSI0 : 0 ≤ SI) (hSI : SI = r * SIr)
    (hAf : 0 ≤ Af) (hAb : 0 ≤ Ab)
    -- identity layer
    (hLHS : LHS ≤ Slq - Bexp - ASs / 2 + PSs + RSs)
    -- CPD
    (hBX : 2 * N * (SY + SYb) - N ^ 2 * Irho + N * lρ ≤ Bexp)
    -- node-sum discrepancies
    (hPS : PSs ≤ 2 * r * SU + k * E1 + E2 * SIr)
    (hRS : RSs ≤ 2 * r * SUb + (N - k) * E3)
    (hAS : 2 * r ^ 2 * J - E4 ≤ ASs)
    -- pointwise g-bounds, summed
    (hfree : 2 * r * Sg - 2 * (1 - ε) * P * SI - 2 * Kc * (k * Af + 2 * SIr) ≤ 2 * N * SY - 2 * r * SU)
    (hline : (N - k) * (2 * r * ℓ - 2 * Kc * Ab) ≤ 2 * N * SYb - 2 * r * SUb)
    (hcap : k * mp + r * Scap - Cdef ≤ Sg)
    (hq : Slq ≤ (1 - e) * k * Cl - 2 * (1 - e) * P * SI)
    (hIb : Irho ≤ Ibd) (hcB : 2 * (mp - ℓ) ≤ cB)
    (hmargin : 4 * Kc + E2 ≤ 2 * P * (ε - e) * r) :
    LHS ≤ -(r ^ 2 * (2 * M * mp + 2 * Scap - M ^ 2 * Ibd + J)) + cB * r * (N - k)
      + (2 * r * Cdef + 2 * r * Kc * |mp| + (2 * M * r * Kc + Kc ^ 2) * |Ibd|
        + (1 - e) * k * Cl + 2 * Kc * k * Af + 2 * Kc * (N - k) * Ab + (N - k) * E3
        + k * E1 + E4 / 2 + N * |lρ|) := by
  have hN0 : 0 ≤ N := le_trans hk0 hkN
  have hNk : 0 ≤ N - k := sub_nonneg.mpr hkN
  have hSIr : 0 ≤ SIr := by
    have : 0 ≤ r * SIr := hSI ▸ hSI0
    exact nonneg_of_mul_nonneg_right this hr
  -- step: eliminate Bexp, PSs, RSs, ASs
  have h1 : LHS ≤ Slq - (2 * N * (SY + SYb) - N ^ 2 * Irho + N * lρ) - (r ^ 2 * J - E4 / 2)
      + (2 * r * SU + k * E1 + E2 * SIr) + (2 * r * SUb + (N - k) * E3) := by
    linarith
  -- free and removed bounds
  have h2 : -(2 * N * SY) + 2 * r * SU ≤ -(2 * r * Sg) + 2 * (1 - ε) * P * SI
      + 2 * Kc * (k * Af + 2 * SIr) := by linarith
  have h3 : -(2 * N * SYb) + 2 * r * SUb ≤ -((N - k) * (2 * r * ℓ - 2 * Kc * Ab)) := by linarith
  have hcap' : -(2 * r * Sg) ≤ -(2 * r * (k * mp + r * Scap - Cdef)) := by
    have := mul_le_mul_of_nonneg_left hcap hr.le
    linarith
  -- the imaginary-part terms have a negative coefficient
  have hSIterm : (-2 * (1 - e) * P + 2 * (1 - ε) * P) * SI + 4 * Kc * SIr + E2 * SIr ≤ 0 := by
    have e1 : (-2 * (1 - e) * P + 2 * (1 - ε) * P) * SI = -(2 * P * (ε - e) * r) * SIr := by
      rw [hSI]; ring
    rw [e1]
    have := mul_le_mul_of_nonneg_right hmargin hSIr
    linarith
  -- 2 r ℓ ≥ 2 r mp - r cB
  have hl : (N - k) * (2 * r * mp - r * cB) ≤ (N - k) * (2 * r * ℓ) := by
    have : 2 * r * mp - r * cB ≤ 2 * r * ℓ := by
      have := mul_le_mul_of_nonneg_left hcB hr.le
      linarith
    exact mul_le_mul_of_nonneg_left this hNk
  -- N = M r + delta
  obtain ⟨hd1, hd2⟩ := abs_le.mp hNM
  have hN1 : -(2 * r * N * mp) ≤ -(2 * M * r ^ 2 * mp) + 2 * r * Kc * |mp| := by
    have : -(2 * r * N * mp) = -(2 * M * r ^ 2 * mp) - 2 * r * (N - M * r) * mp := by ring
    rw [this]
    have h : -(2 * r * (N - M * r) * mp) ≤ 2 * r * Kc * |mp| := by
      have h0 : |(N - M * r) * mp| ≤ Kc * |mp| := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_right hNM (abs_nonneg _)
      have h00 := (abs_le.mp h0).1
      nlinarith [mul_le_mul_of_nonneg_left h00 (by positivity : (0 : ℝ) ≤ 2 * r)]
    linarith
  have hN2 : N ^ 2 * Irho ≤ M ^ 2 * r ^ 2 * Ibd + (2 * M * r * Kc + Kc ^ 2) * |Ibd| := by
    have hsq : N ^ 2 = M ^ 2 * r ^ 2 + 2 * M * r * (N - M * r) + (N - M * r) ^ 2 := by ring
    have hb1 : N ^ 2 * Irho ≤ N ^ 2 * Ibd := mul_le_mul_of_nonneg_left hIb (sq_nonneg N)
    have hb2 : N ^ 2 * Ibd ≤ M ^ 2 * r ^ 2 * Ibd + (2 * M * r * Kc + Kc ^ 2) * |Ibd| := by
      rw [hsq]
      have hd : |N - M * r| ≤ Kc := hNM
      have hdd : (N - M * r) ^ 2 ≤ Kc ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
      have e1 : 2 * M * r * (N - M * r) * Ibd ≤ 2 * M * r * Kc * |Ibd| := by
        have : |(N - M * r) * Ibd| ≤ Kc * |Ibd| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right hNM (abs_nonneg _)
        have := (abs_le.mp this).2
        nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * M * r)]
      have e2 : (N - M * r) ^ 2 * Ibd ≤ Kc ^ 2 * |Ibd| := by
        calc (N - M * r) ^ 2 * Ibd ≤ (N - M * r) ^ 2 * |Ibd| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
          _ ≤ Kc ^ 2 * |Ibd| := mul_le_mul_of_nonneg_right hdd (abs_nonneg _)
      nlinarith [e1, e2]
    linarith
  have hlr : -(N * lρ) ≤ N * |lρ| := by
    nlinarith [mul_le_mul_of_nonneg_left (neg_le_abs lρ) hN0]
  linarith [h1, h2, h3, hcap', hSIterm, hl, hN1, hN2, hlr, hq, hmargin]

end CatalanCore.Uniform.Decay.Nodes
