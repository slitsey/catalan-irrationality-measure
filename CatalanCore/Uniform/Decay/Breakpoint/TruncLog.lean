module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.MeanInequalities

@[expose] public section
set_option Elab.async false

/-!
# The truncated-logarithm breakpoint term (ledger B05a; sevenths avoidance, 7 Nov 2026)

For `0 < t ≤ 1`: `-log t = T_K(t) + R`, `T_K(t) = ∑_{k<K} (1-t)^(k+1)/(k+1)`,
`0 ≤ R ≤ (1-t)^(K+1) / ((K+1) t)`.  With `s = S t` and `ρ(1,K) = 1/(K+1)`,
`ρ(m,K) = (m-1)^(m-1) (K+1)^(K+1) / ((m+K)^(m+K) (K+1))` (`m ≥ 2`; sharp weighted AM-GM `tpow_le`):

`b s^m (λ - T_K(s/S)) - |b| S^m ε - max b 0 · S^m ρ(m,K) ≤ b s^m log s`  for `0 < s ≤ S`, `|log S - λ| ≤ ε`
(`term_lower`).  So the logarithmic terms `b_m s^m log s` of a breakpoint expansion are bounded below by
a polynomial (degree `m + K`) minus a constant.
-/

namespace CatalanCore.Uniform.Decay.Breakpoint.TL

open Finset

/-- `T_K(t)`. -/
noncomputable def TK (K : ℕ) (t : ℝ) : ℝ := ∑ k ∈ range K, (1 - t) ^ (k + 1) / ((k : ℝ) + 1)

theorem log_trunc {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (K : ℕ) :
    0 ≤ -Real.log t - TK K t ∧
      -Real.log t - TK K t ≤ (1 - t) ^ (K + 1) / (((K : ℝ) + 1) * t) := by
  set x : ℝ := 1 - t with hx
  have hx0 : 0 ≤ x := by simp only [hx]; linarith
  have hx1 : x < 1 := by simp only [hx]; linarith
  have habs : |x| < 1 := by rw [abs_of_nonneg hx0]; exact hx1
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have hlog : Real.log (1 - x) = Real.log t := by simp only [hx]; ring_nf
  rw [hlog] at hs
  have hs2 : HasSum (fun n : ℕ => x ^ (n + K + 1) / (((n + K : ℕ) : ℝ) + 1))
      (-Real.log t - TK K t) := by
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => x ^ (n + 1) / ((n : ℝ) + 1)) K).2 hs
    simpa [TK, hx] using this
  constructor
  · exact hs2.nonneg fun n => by positivity
  · have hgeo : HasSum (fun n : ℕ => x ^ (K + 1) / ((K : ℝ) + 1) * x ^ n)
        (x ^ (K + 1) / ((K : ℝ) + 1) * (1 - x)⁻¹) :=
      (hasSum_geometric_of_lt_one hx0 hx1).mul_left _
    have hle := hasSum_le (fun n => ?_) hs2 hgeo
    · have e : x ^ (K + 1) / ((K : ℝ) + 1) * (1 - x)⁻¹ = x ^ (K + 1) / (((K : ℝ) + 1) * t) := by
        have : 1 - x = t := by simp only [hx]; ring
        rw [this]; field_simp
      rwa [e] at hle
    · have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
      have hnK : (K : ℝ) + 1 ≤ ((n + K : ℕ) : ℝ) + 1 := by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have e : x ^ (K + 1) / ((K : ℝ) + 1) * x ^ n = x ^ (n + K + 1) / ((K : ℝ) + 1) := by
        rw [show n + K + 1 = (K + 1) + n by ring, pow_add]; ring
      rw [e]
      exact div_le_div_of_nonneg_left (by positivity) hK hnK

/-- Bernoulli: `t (1-t)^n ≤ 1/n`-type bound, `(1-t)^n (1 + n t) ≤ 1`. -/
theorem pow_one_sub_mul_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (n : ℕ) :
    (1 - t) ^ n * (1 + (n : ℝ) * t) ≤ 1 := by
  have hb : 1 + (n : ℝ) * t ≤ (1 + t) ^ n := one_add_mul_le_pow (by linarith) n
  have h2 : (1 - t) ^ n * (1 + t) ^ n ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg (by linarith) n)).trans h2


/-- Sharp weighted AM-GM: `t^a (1-t)^b (a+b)^(a+b) <= a^a b^b` on `[0,1]` (gives `rhoMK`). -/
theorem tpow_le (a b : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    t ^ a * (1 - t) ^ b * ((a : ℝ) + b) ^ (a + b) ≤ (a : ℝ) ^ a * (b : ℝ) ^ b := by
  have haR : (0:ℝ) < a := by exact_mod_cast ha
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  set N : ℝ := (a : ℝ) + b with hN
  have hNpos : 0 < N := by linarith
  set p1 : ℝ := t * N / a with hp1d
  set p2 : ℝ := (1 - t) * N / b with hp2d
  have hp1 : 0 ≤ p1 := div_nonneg (mul_nonneg ht0 hNpos.le) haR.le
  have hp2 : 0 ≤ p2 := div_nonneg (mul_nonneg (by linarith) hNpos.le) hbR.le
  have hw : (a:ℝ) / N + b / N = 1 := by rw [← add_div]; exact div_self hNpos.ne'
  have hg := Real.geom_mean_le_arith_mean2_weighted (div_nonneg haR.le hNpos.le)
    (div_nonneg hbR.le hNpos.le) hp1 hp2 hw
  have hr : (a:ℝ) / N * p1 + b / N * p2 = 1 := by
    rw [hp1d, hp2d]; field_simp; ring
  rw [hr] at hg
  have hpow : (p1 ^ ((a:ℝ) / N) * p2 ^ ((b:ℝ) / N)) ^ (a + b) ≤ 1 := by
    calc _ ≤ (1:ℝ) ^ (a + b) := pow_le_pow_left₀ (by positivity) hg _
      _ = 1 := one_pow _
  have e1 : (p1 ^ ((a:ℝ) / N)) ^ (a + b) = p1 ^ a := by
    rw [← Real.rpow_natCast (p1 ^ ((a:ℝ) / N)) (a + b), ← Real.rpow_mul hp1]
    have : (a:ℝ) / N * ((a + b : ℕ) : ℝ) = ((a : ℕ) : ℝ) := by
      push_cast; rw [← hN]; field_simp
    rw [this, Real.rpow_natCast]
  have e2 : (p2 ^ ((b:ℝ) / N)) ^ (a + b) = p2 ^ b := by
    rw [← Real.rpow_natCast (p2 ^ ((b:ℝ) / N)) (a + b), ← Real.rpow_mul hp2]
    have : (b:ℝ) / N * ((a + b : ℕ) : ℝ) = ((b : ℕ) : ℝ) := by
      push_cast; rw [← hN]; field_simp
    rw [this, Real.rpow_natCast]
  rw [mul_pow, e1, e2] at hpow
  have hab : (0:ℝ) < (a:ℝ) ^ a * (b:ℝ) ^ b := by positivity
  have hid : p1 ^ a * p2 ^ b = t ^ a * (1 - t) ^ b * N ^ (a + b) / ((a:ℝ) ^ a * (b:ℝ) ^ b) := by
    rw [hp1d, hp2d, div_pow, div_pow, mul_pow, mul_pow, pow_add]; field_simp
  rw [hid, div_le_one hab] at hpow
  exact hpow


/-- `ρ(m,K)` as a rational (exact; the cell checker evaluates it). -/
def rhoMK (m K : ℕ) : ℚ :=
  if m ≤ 1 then 1 / ((K + 1 : ℕ) : ℚ) else
  (((m - 1 : ℕ) : ℚ) ^ (m - 1) * ((K + 1 : ℕ) : ℚ) ^ (K + 1) / ((m + K : ℕ) : ℚ) ^ (m + K)) / ((K + 1 : ℕ) : ℚ)

/-- For `m ≥ 1`, `t ∈ (0,1]`: `t^m (-log t - T_K t) ≤ ρ(m,K)`. -/
theorem pow_mul_rem_le {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (K : ℕ) :
    t ^ m * (-Real.log t - TK K t) ≤ (rhoMK m K : ℝ) := by
  have hK : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hR := (log_trunc h0 h1 K).2
  have hx0 : 0 ≤ 1 - t := by linarith
  have ht1 : t ^ m * ((1 - t) ^ (K + 1) / (((K : ℝ) + 1) * t))
      = t ^ (m - 1) * (1 - t) ^ (K + 1) / ((K : ℝ) + 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  have hstep : t ^ m * (-Real.log t - TK K t) ≤ t ^ (m - 1) * (1 - t) ^ (K + 1) / ((K : ℝ) + 1) := by
    rw [← ht1]; exact mul_le_mul_of_nonneg_left hR (by positivity)
  refine hstep.trans ?_
  unfold rhoMK
  by_cases h : m ≤ 1
  · have : m = 1 := by omega
    subst this
    simp only [le_refl, ite_true, Nat.sub_self, pow_zero, one_mul]
    push_cast
    exact div_le_div_of_nonneg_right (pow_le_one₀ hx0 (by linarith)) hK.le
  · rw [if_neg h]
    have ha : 0 < m - 1 := by omega
    have hb : 0 < K + 1 := by omega
    have hT := tpow_le (m - 1) (K + 1) t h0.le h1 ha hb
    have hsum : (((m - 1 : ℕ) : ℝ) + ((K + 1 : ℕ) : ℝ)) = ((m + K : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ m)]; ring
    have hsum' : (m - 1) + (K + 1) = m + K := by omega
    rw [hsum, hsum'] at hT
    have hpos : (0 : ℝ) < ((m : ℝ) + K) ^ (m + K) := by
      have : (0 : ℝ) < (m : ℝ) + K := by
        have : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
        have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        linarith
      positivity
    have hK1 : (((K + 1 : ℕ) : ℝ)) = (K : ℝ) + 1 := by push_cast; ring
    rw [hK1] at hT
    push_cast at hT ⊢
    rw [div_le_div_iff_of_pos_right hK, le_div_iff₀ hpos]
    nlinarith [hT]

/-- **The one-term lower bound.**  For `0 < s ≤ S`, `m ≥ 1`, `|log S - λ| ≤ ε`. -/
theorem term_lower {b lam ε S s : ℝ} {m : ℕ} (hm : 1 ≤ m) (K : ℕ) (hs0 : 0 < s) (hs : s ≤ S)
    (hl : b ≠ 0 → |Real.log S - lam| ≤ ε) :
    b * s ^ m * (lam - TK K (s / S)) - |b| * S ^ m * ε - max b 0 * S ^ m * (rhoMK m K : ℝ)
      ≤ b * s ^ m * Real.log s := by
  have hS0 : 0 < S := lt_of_lt_of_le hs0 hs
  set t := s / S with ht
  have ht0 : 0 < t := div_pos hs0 hS0
  have ht1 : t ≤ 1 := (div_le_one hS0).2 hs
  have hst : s = S * t := by rw [ht]; field_simp
  have hlog : Real.log s = Real.log S + Real.log t := by
    rw [hst, Real.log_mul hS0.ne' ht0.ne']
  set R := -Real.log t - TK K t with hR
  have hR0 : 0 ≤ R := (log_trunc ht0 ht1 K).1
  have hRm := pow_mul_rem_le hm ht0 ht1 K
  have hpow : s ^ m = S ^ m * t ^ m := by rw [hst, mul_pow]
  have hSm : 0 < S ^ m := pow_pos hS0 m
  have hsm : 0 < s ^ m := pow_pos hs0 m
  have hle : s ^ m ≤ S ^ m := pow_le_pow_left₀ hs0.le hs m
  have hd : b * s ^ m * Real.log s - b * s ^ m * (lam - TK K t)
      = b * s ^ m * (Real.log S - lam) - b * s ^ m * R := by
    rw [hlog, hR]; ring
  have h1 : -(|b| * S ^ m * ε) ≤ b * s ^ m * (Real.log S - lam) := by
    by_cases hb : b = 0
    · subst hb; simp
    have hl' := hl hb
    have : |b * s ^ m * (Real.log S - lam)| ≤ |b| * S ^ m * ε := by
      rw [abs_mul, abs_mul, abs_of_pos hsm]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hle (abs_nonneg _)) hl' (abs_nonneg _)
        (by positivity)
    exact (abs_le.1 this).1
  have h2 : -(max b 0 * S ^ m * (rhoMK m K : ℝ)) ≤ -(b * s ^ m * R) := by
    have hmx : 0 ≤ max b 0 := le_max_right _ _
    have hbm : b ≤ max b 0 := le_max_left _ _
    have hsR : 0 ≤ s ^ m * R := by positivity
    have hA : b * (s ^ m * R) ≤ max b 0 * (s ^ m * R) := mul_le_mul_of_nonneg_right hbm hsR
    have hB : s ^ m * R ≤ S ^ m * (rhoMK m K : ℝ) := by
      rw [hpow, mul_assoc]; exact mul_le_mul_of_nonneg_left hRm hSm.le
    have hC : max b 0 * (s ^ m * R) ≤ max b 0 * (S ^ m * (rhoMK m K : ℝ)) :=
      mul_le_mul_of_nonneg_left hB hmx
    nlinarith
  linarith

end CatalanCore.Uniform.Decay.Breakpoint.TL
