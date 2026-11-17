module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The plain measure form under integer Möbius maps

`plain_measure_mobius`: if `q ^ (-μ') < |x - p/q|` for all `p` and all large `q`, with `1 ≤ μ'`, then for
every integer matrix `(a, b; c, d)` with `a d - b c ≠ 0` and every `μ > μ'`,
`q ^ (-μ) < |(a x + b)/(c x + d) - p/q|` for all `p` and all large `q`.

The proof writes `P = d p - b q`, `Q = a q - c p`, so that
`(a x + b)/(c x + d) - p/q = (Q x - P) / ((c x + d) q)`, and uses the hypothesis at denominator
`K |Q|` for a fixed `K`, which covers small `|Q|` as well.

Say μ, never B, for the irrationality measure.
-/

open Filter Topology

namespace CatalanCore.Measure

/-- The hypothesis at every nonzero integer denominator, with a fixed factor `K ≥ 1`. -/
theorem plain_measure_all_den {x μ' : ℝ}
    (h : ∀ᶠ q : ℕ in atTop, ∀ p : ℤ, (q : ℝ) ^ (-μ') < |x - (p : ℝ) / q|) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ Q : ℤ, Q ≠ 0 → ∀ P : ℤ,
      ((K : ℝ) * |(Q : ℝ)|) ^ (-μ') < |(Q : ℝ) * x - P| / |(Q : ℝ)| := by
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨q₀ + 1, by omega, fun Q hQ P => ?_⟩
  set n : ℕ := (q₀ + 1) * Q.natAbs with hn
  have hQn : 1 ≤ Q.natAbs := Int.natAbs_pos.mpr hQ
  have hnq : q₀ ≤ n := by
    rw [hn]; nlinarith
  have hn0 : (0 : ℝ) < n := by
    have : 0 < n := by rw [hn]; positivity
    exact_mod_cast this
  have key := hq₀ n hnq (P * Q.sign * (q₀ + 1 : ℕ))
  have hnR : (n : ℝ) = ((q₀ + 1 : ℕ) : ℝ) * |(Q : ℝ)| := by
    rw [hn, Nat.cast_mul, Nat.cast_natAbs, Int.cast_abs]
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ
  have hsgn : (Q.sign : ℝ) * |(Q : ℝ)| = Q := by
    rcases lt_trichotomy Q 0 with h' | h' | h'
    · rw [Int.sign_eq_neg_one_of_neg h', abs_of_neg (by exact_mod_cast h')]; push_cast; ring
    · exact absurd h' hQ
    · rw [Int.sign_eq_one_of_pos h', abs_of_pos (by exact_mod_cast h')]; push_cast; ring
  have hsq : (Q.sign : ℝ) * (Q.sign : ℝ) = 1 := by
    rcases lt_trichotomy Q 0 with h' | h' | h'
    · rw [Int.sign_eq_neg_one_of_neg h']; norm_num
    · exact absurd h' hQ
    · rw [Int.sign_eq_one_of_pos h']; norm_num
  have hK0 : (0 : ℝ) < ((q₀ + 1 : ℕ) : ℝ) := by positivity
  have habsQ : (0 : ℝ) < |(Q : ℝ)| := abs_pos.mpr hQR
  have hs2 : |(Q : ℝ)| = (Q.sign : ℝ) * Q := by
    rcases lt_trichotomy Q 0 with h' | h' | h'
    · rw [Int.sign_eq_neg_one_of_neg h', abs_of_neg (by exact_mod_cast h')]; push_cast; ring
    · exact absurd h' hQ
    · rw [Int.sign_eq_one_of_pos h', abs_of_pos (by exact_mod_cast h')]; push_cast; ring
  have e1 : ((P * Q.sign * (q₀ + 1 : ℕ) : ℤ) : ℝ) / (n : ℝ) = (P : ℝ) / Q := by
    rw [hnR, div_eq_div_iff (by positivity) hQR, hs2]; push_cast; ring
  have e : x - ((P * Q.sign * (q₀ + 1 : ℕ) : ℤ) : ℝ) / (n : ℝ) = ((Q : ℝ) * x - P) / (Q : ℝ) := by
    rw [e1]; field_simp
  rw [e, abs_div, hnR] at key
  exact key

/-- **Möbius invariance of the plain measure form.** -/
theorem plain_measure_mobius {x μ' μ : ℝ} (h1 : 1 ≤ μ') (hμ : μ' < μ) (a b c d : ℤ)
    (hdet : a * d - b * c ≠ 0)
    (h : ∀ᶠ q : ℕ in atTop, ∀ p : ℤ, (q : ℝ) ^ (-μ') < |x - (p : ℝ) / q|) :
    ∀ᶠ q : ℕ in atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-μ) < |((a : ℝ) * x + b) / ((c : ℝ) * x + d) - (p : ℝ) / q| := by
  obtain ⟨K, hK1, hK⟩ := plain_measure_all_den h
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  -- `c x + d ≠ 0`
  have hden : (c : ℝ) * x + d ≠ 0 := by
    intro h0
    by_cases hc : c = 0
    · subst hc
      have hd : d ≠ 0 := by intro hd; apply hdet; subst hd; ring
      have : (d : ℝ) = 0 := by simpa using h0
      exact hd (by exact_mod_cast this)
    · have := hK c hc (-d)
      have e0 : (c : ℝ) * x - ((-d : ℤ) : ℝ) = 0 := by push_cast; linarith
      rw [e0, abs_zero, zero_div] at this
      exact absurd this (not_lt.mpr (by positivity))
  set y : ℝ := ((a : ℝ) * x + b) / ((c : ℝ) * x + d) with hy
  set A : ℝ := |(c : ℝ) * x + d| with hA
  have hA0 : 0 < A := abs_pos.mpr hden
  set C : ℝ := |(a : ℝ)| + |(c : ℝ)| * (|y| + 1) + 1 with hC
  have hC1 : 1 ≤ C := by
    rw [hC]; have := abs_nonneg (a : ℝ); have := abs_nonneg (c : ℝ); have := abs_nonneg y; nlinarith
  -- the constant in the main case
  set M : ℝ := (K : ℝ) ^ (-μ') * C ^ (1 - μ') / A with hM
  have hM0 : 0 < M := by rw [hM]; positivity
  -- the constant in the case `Q = 0`
  set E : ℝ := if c = 0 then 1 else |y - (a : ℝ) / c| with hE
  have hE0 : 0 < E := by
    rw [hE]; split_ifs with hc
    · norm_num
    · apply abs_pos.mpr
      intro h0
      have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
      have h0' : ((a : ℝ) * x + b) / ((c : ℝ) * x + d) = (a : ℝ) / c := by
        rw [← hy]; linarith
      rw [div_eq_div_iff hden hcR] at h0'
      apply hdet
      have : ((a * d - b * c : ℤ) : ℝ) = 0 := by
        push_cast; linear_combination (-1 : ℝ) * h0'
      exact_mod_cast this
  have hlim : Tendsto (fun q : ℕ => (q : ℝ) ^ (-(μ - μ'))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hμ)).comp tendsto_natCast_atTop_atTop
  have hlimE : Tendsto (fun q : ℕ => (q : ℝ) ^ (-μ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
  have ev1 := hlim.eventually (gt_mem_nhds hM0)
  have ev2 := hlimE.eventually (gt_mem_nhds (lt_min hE0 one_pos))
  filter_upwards [ev1, ev2, eventually_ge_atTop 1] with q hq1 hq2 hq0 p
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hq2' : (q : ℝ) ^ (-μ) < E := lt_of_lt_of_le hq2 (min_le_left _ _)
  have hq2'' : (q : ℝ) ^ (-μ) < 1 := lt_of_lt_of_le hq2 (min_le_right _ _)
  by_cases hfar : 1 ≤ |y - (p : ℝ) / q|
  · exact lt_of_lt_of_le hq2'' hfar
  push Not at hfar
  set Q : ℤ := a * q - c * p with hQdef
  set P : ℤ := d * p - b * q with hPdef
  have hident : y - (p : ℝ) / q = ((Q : ℝ) * x - P) / (((c : ℝ) * x + d) * q) := by
    rw [hy, div_sub_div _ _ hden (ne_of_gt hqR), hQdef, hPdef]; push_cast; ring
  by_cases hQ0 : Q = 0
  · -- `p/q = a/c`
    have hc : c ≠ 0 := by
      intro hc; apply hdet
      have : a * (q : ℤ) = 0 := by rw [hQdef, hc] at hQ0; simpa using hQ0
      have ha : a = 0 := by
        rcases mul_eq_zero.mp this with h' | h'
        · exact h'
        · exfalso; have : (q : ℤ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
          exact this h'
      rw [ha, hc]; ring
    have hpq : (p : ℝ) / q = (a : ℝ) / c := by
      have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc
      have : (a : ℝ) * q = c * p := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hQ0; rw [hQdef] at this; push_cast at this; linarith
      field_simp; linarith
    rw [hpq]
    have : E = |y - (a : ℝ) / c| := by rw [hE]; simp [hc]
    rw [← this]; exact hq2'
  · -- main case
    have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ0
    have habsQ : (0 : ℝ) < |(Q : ℝ)| := abs_pos.mpr hQR
    have hQ1 : (1 : ℝ) ≤ |(Q : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hQ0
    -- `|p| ≤ (|y| + 1) q`
    have hp : |(p : ℝ)| ≤ (|y| + 1) * q := by
      have h' : |(p : ℝ) / q| ≤ |y| + 1 := by
        have := abs_sub_abs_le_abs_sub ((p : ℝ) / q) y
        rw [abs_sub_comm] at this; linarith
      rw [abs_div, abs_of_pos hqR, div_le_iff₀ hqR] at h'; exact h'
    have hQC : |(Q : ℝ)| ≤ C * q := by
      have : (Q : ℝ) = a * q - c * p := by rw [hQdef]; push_cast; ring
      rw [this]
      calc |(a : ℝ) * q - c * p| ≤ |(a : ℝ)| * q + |(c : ℝ)| * |(p : ℝ)| := by
            have := abs_sub ((a : ℝ) * q) (c * p)
            rw [abs_mul, abs_mul, abs_of_pos hqR] at this; exact this
        _ ≤ |(a : ℝ)| * q + |(c : ℝ)| * ((|y| + 1) * q) := by gcongr
        _ ≤ C * q := by rw [hC]; nlinarith [abs_nonneg (a : ℝ), abs_nonneg (c : ℝ)]
    have hkey := hK Q hQ0 P
    -- `|y - p/q| = |Q x - P| / (A q)`
    have habs : |y - (p : ℝ) / q| = |(Q : ℝ) * x - P| / |(Q : ℝ)| * (|(Q : ℝ)| / (A * q)) := by
      rw [hident, abs_div, abs_mul, abs_of_pos hqR, hA]; field_simp
    -- lower bound for `|Q|^(1 - μ')`
    have hpow : (C * q) ^ (1 - μ') ≤ |(Q : ℝ)| ^ (1 - μ') :=
      Real.rpow_le_rpow_of_nonpos habsQ hQC (by linarith)
    have hsplit : ((K : ℝ) * |(Q : ℝ)|) ^ (-μ') * (|(Q : ℝ)| / (A * q))
        = (K : ℝ) ^ (-μ') * |(Q : ℝ)| ^ (1 - μ') / (A * q) := by
      rw [Real.mul_rpow (by positivity) habsQ.le]
      have : |(Q : ℝ)| ^ (1 - μ') = |(Q : ℝ)| ^ (-μ') * |(Q : ℝ)| := by
        rw [show (1 - μ') = -μ' + 1 by ring, Real.rpow_add habsQ, Real.rpow_one]
      rw [this]; field_simp
    have hqpow : (C * q) ^ (1 - μ') / q = C ^ (1 - μ') * (q : ℝ) ^ (-μ') := by
      rw [Real.mul_rpow (by linarith) hqR.le]
      have : (q : ℝ) ^ (1 - μ') = (q : ℝ) ^ (-μ') * q := by
        rw [show (1 - μ') = -μ' + 1 by ring, Real.rpow_add hqR, Real.rpow_one]
      rw [this]; field_simp
    have hsplitμ : (q : ℝ) ^ (-μ) = (q : ℝ) ^ (-(μ - μ')) * (q : ℝ) ^ (-μ') := by
      rw [← Real.rpow_add hqR]; ring_nf
    have hqμ' : (0 : ℝ) < (q : ℝ) ^ (-μ') := by positivity
    calc (q : ℝ) ^ (-μ) = (q : ℝ) ^ (-(μ - μ')) * (q : ℝ) ^ (-μ') := hsplitμ
      _ < M * (q : ℝ) ^ (-μ') := by gcongr
      _ = (K : ℝ) ^ (-μ') * ((C * q) ^ (1 - μ') / q) / A := by rw [hqpow, hM]; ring
      _ ≤ (K : ℝ) ^ (-μ') * (|(Q : ℝ)| ^ (1 - μ') / q) / A := by
            gcongr
      _ = ((K : ℝ) * |(Q : ℝ)|) ^ (-μ') * (|(Q : ℝ)| / (A * q)) := by
            rw [hsplit]; field_simp
      _ < |(Q : ℝ) * x - P| / |(Q : ℝ)| * (|(Q : ℝ)| / (A * q)) := by
            gcongr
      _ = |y - (p : ℝ) / q| := habs.symm

end CatalanCore.Measure
