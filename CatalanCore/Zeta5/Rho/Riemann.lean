module

public import CatalanCore.Zeta5.Rho.Steps
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-!
# Riemann sums of `log (t + v²)` and the field exponent `V` (ledger ZR02, first half)

`J_A(t) = A log(t + A²) - 2A + 2√t arctan(A/√t) = ∫_0^A log(t + v²) dv`, and
`V(t) = 2π√t + J_1(t) - 6 J_α(t)`, `α = 3/40`.

For `K, N` with `v_l = l/K`, the increasing function `log(t + v²)` gives
  `K J_{N/K}(t) ≤ Σ_{l ≤ N} log(t + v_l²)`  and
  `Σ_{k ≤ K} log(t + v_k²) ≤ K J_1(t) + log(1+t) - log t`,
and hence the product bound `∏_{l≤N}(t+v_l²)^6 / ∏_{k≤K}(t+v_k²) ≥ t/(1+t) · exp(-K (J_1 - 6 J_α))`.
-/

namespace CatalanCore.Zeta5.Rho

open Set Finset Real

/-- `J_A(t) = ∫_0^A log(t + v²) dv`. -/
noncomputable def Jf (t A : ℝ) : ℝ :=
  A * Real.log (t + A ^ 2) - 2 * A + 2 * √t * Real.arctan (A / √t)

/-- The field exponent `V(t) = 2π√t + J_1(t) - 6 J_α(t)`, `α = 3/40`. -/
noncomputable def Vf (t : ℝ) : ℝ := 2 * Real.pi * √t + Jf t 1 - 6 * Jf t (3 / 40)

theorem hasDerivAt_Jf {t : ℝ} (ht : 0 < t) (A : ℝ) :
    HasDerivAt (Jf t) (Real.log (t + A ^ 2)) A := by
  have hs : 0 < √t := Real.sqrt_pos.mpr ht
  have hpos : t + A ^ 2 ≠ 0 := by positivity
  have h1 := (hasDerivAt_id' A).mul (((hasDerivAt_pow 2 A).const_add t).log hpos)
  have h3 := (((hasDerivAt_id' A).div_const (√t)).arctan).const_mul (2 * √t)
  have h4 := (hasDerivAt_id' A).const_mul (2 : ℝ)
  have := (h1.sub h4).add h3
  convert this using 1
  · funext B; simp [Jf]
  · have e : √t ^ 2 = t := Real.sq_sqrt ht.le
    field_simp
    rw [e]
    ring

theorem continuous_Jf {t : ℝ} (ht : 0 < t) : Continuous (Jf t) :=
  continuous_iff_continuousAt.2 fun A => (hasDerivAt_Jf ht A).continuousAt

theorem Jf_zero (t : ℝ) : Jf t 0 = 0 := by simp [Jf]

theorem monotoneOn_logsq {t : ℝ} (ht : 0 < t) :
    MonotoneOn (fun v : ℝ => Real.log (t + v ^ 2)) (Ici 0) := by
  intro v hv w hw hvw
  have hv' : (0 : ℝ) ≤ v := hv
  exact Real.log_le_log (by positivity) (by nlinarith)

/-- Lower Riemann sum: `K J_{N/K}(t) ≤ Σ_{l ≤ N} log(t + (l/K)²)`. -/
theorem sumlog_lower {t : ℝ} (ht : 0 < t) (K N : ℕ) (hK : 0 < K) :
    (K : ℝ) * Jf t ((N : ℝ) / K) ≤ ∑ l ∈ Icc 1 N, Real.log (t + ((l : ℝ) / K) ^ 2) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have := telescope_le_sum_Icc (fun l : ℕ => Real.log (t + ((l : ℝ) / K) ^ 2))
    (fun l : ℕ => (K : ℝ) * Jf t ((l : ℝ) / K)) N ?_
  · simpa [Jf_zero] using this
  intro l hl1 _
  have hxy : (((l - 1 : ℕ) : ℝ) / K) < (l : ℝ) / K := by
    rw [div_lt_div_iff_of_pos_right hKr]
    have : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by push_cast [Nat.cast_sub hl1]; ring
    rw [this]; linarith
  have hstep := step_le_right (φ := Jf t) (f := fun v => Real.log (t + v ^ 2)) hxy
    (continuous_Jf ht).continuousOn (fun s _ => hasDerivAt_Jf ht s)
    (fun a ha b hb hab => monotoneOn_logsq ht
      (show 0 ≤ a from le_trans (by positivity) ha.1.le) (show 0 ≤ b from le_trans (by positivity) hb.1.le) hab)
  have hdiff : (l : ℝ) / K - ((l - 1 : ℕ) : ℝ) / K = 1 / K := by
    have : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by push_cast [Nat.cast_sub hl1]; ring
    rw [this]; field_simp; ring
  rw [hdiff] at hstep
  have := mul_le_mul_of_nonneg_left hstep hKr.le
  calc (K : ℝ) * Jf t ((l : ℝ) / K) - (K : ℝ) * Jf t (((l - 1 : ℕ) : ℝ) / K)
      = (K : ℝ) * (Jf t ((l : ℝ) / K) - Jf t (((l - 1 : ℕ) : ℝ) / K)) := by ring
    _ ≤ (K : ℝ) * (1 / K * Real.log (t + ((l : ℝ) / K) ^ 2)) := this
    _ = _ := by field_simp

/-- Upper Riemann sum: `Σ_{k ≤ K} log(t + (k/K)²) ≤ K J_1(t) + log(1+t) - log t`. -/
theorem sumlog_upper {t : ℝ} (ht : 0 < t) (K : ℕ) (hK : 0 < K) :
    ∑ k ∈ Icc 1 K, Real.log (t + ((k : ℝ) / K) ^ 2) ≤
      (K : ℝ) * Jf t 1 + Real.log (1 + t) - Real.log t := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hleft : ∑ k ∈ Ico 0 K, Real.log (t + ((k : ℝ) / K) ^ 2) ≤ (K : ℝ) * Jf t 1 := by
    have := sum_Ico_le_telescope (fun k : ℕ => (K : ℝ) * (1 / K * Real.log (t + ((k : ℝ) / K) ^ 2)))
      (fun k : ℕ => (K : ℝ) * Jf t ((k : ℝ) / K)) (Nat.zero_le K) ?_
    · simp only [Nat.cast_zero, zero_div, Jf_zero, mul_zero, sub_zero] at this
      have e : (K : ℝ) / K = 1 := div_self hKr.ne'
      rw [e] at this
      convert this using 1
      refine sum_congr rfl fun k _ => ?_
      field_simp
    intro k _ hk
    have hxy : (k : ℝ) / K < ((k + 1 : ℕ) : ℝ) / K := by
      rw [div_lt_div_iff_of_pos_right hKr]; push_cast; linarith
    have hstep := step_left_le (φ := Jf t) (f := fun v => Real.log (t + v ^ 2)) hxy
      (continuous_Jf ht).continuousOn (fun s _ => hasDerivAt_Jf ht s)
      (fun a ha b hb hab => monotoneOn_logsq ht
        (show 0 ≤ a from le_trans (by positivity) ha.1) (show 0 ≤ b from le_trans (by positivity) hb.1) hab)
    have hdiff : ((k + 1 : ℕ) : ℝ) / K - (k : ℝ) / K = 1 / K := by
      push_cast; field_simp; ring
    rw [hdiff] at hstep
    have := mul_le_mul_of_nonneg_left hstep hKr.le
    calc (K : ℝ) * (1 / K * Real.log (t + ((k : ℝ) / K) ^ 2))
        ≤ (K : ℝ) * (Jf t (((k + 1 : ℕ) : ℝ) / K) - Jf t ((k : ℝ) / K)) := this
      _ = _ := by ring
  have hK1 : ∑ k ∈ Icc 1 K, Real.log (t + ((k : ℝ) / K) ^ 2) =
      ∑ k ∈ Ico 0 K, Real.log (t + ((k : ℝ) / K) ^ 2) + Real.log (t + 1) - Real.log t := by
    rw [Finset.sum_eq_sum_Ico_succ_bot hK]
    have h2 : ∑ k ∈ Icc 1 K, Real.log (t + ((k : ℝ) / K) ^ 2) =
        ∑ k ∈ Ico 1 K, Real.log (t + ((k : ℝ) / K) ^ 2) + Real.log (t + ((K : ℝ) / K) ^ 2) := by
      rw [← Finset.sum_Ico_succ_top (Nat.succ_le_of_lt hK)]; rfl
    rw [h2, div_self hKr.ne']
    simp
    ring
  rw [hK1, add_comm 1 t]
  linarith


theorem prod_shift {t : ℝ} (ht : 0 < t) (K N : ℕ) (hK : 0 < K) :
    ∏ l ∈ Icc 1 N, ((K : ℝ) ^ 2 * t + (l : ℝ) ^ 2) =
      (K : ℝ) ^ (2 * N) * Real.exp (∑ l ∈ Icc 1 N, Real.log (t + ((l : ℝ) / K) ^ 2)) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have e1 : ∀ l : ℕ, (K : ℝ) ^ 2 * t + (l : ℝ) ^ 2 = (K : ℝ) ^ 2 * (t + ((l : ℝ) / K) ^ 2) :=
    fun l => by field_simp
  rw [Finset.prod_congr rfl (fun l _ => e1 l), Finset.prod_mul_distrib, Finset.prod_const,
    Nat.card_Icc, Nat.add_sub_cancel, ← pow_mul, Real.exp_sum]
  congr 1
  refine prod_congr rfl fun l _ => ?_
  rw [Real.exp_log (by positivity)]

/-- The product bound: `∏_{l≤N}(K²t+l²)^6 / ∏_{k≤K}(K²t+k²) ≥ K^{12N-2K} · t/(1+t) ·
exp(-K(J_1(t) - 6 J_{N/K}(t)))`. -/
theorem prod_ratio_lower {t : ℝ} (ht : 0 < t) (K N : ℕ) (hK : 0 < K) :
    (K : ℝ) ^ (12 * N) / (K : ℝ) ^ (2 * K) * (t / (1 + t)) *
        Real.exp (-((K : ℝ) * (Jf t 1 - 6 * Jf t ((N : ℝ) / K)))) ≤
      (∏ l ∈ Icc 1 N, ((K : ℝ) ^ 2 * t + (l : ℝ) ^ 2)) ^ 6 /
        ∏ k ∈ Icc 1 K, ((K : ℝ) ^ 2 * t + (k : ℝ) ^ 2) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  rw [prod_shift ht K N hK, prod_shift ht K K hK, mul_pow, ← Real.exp_nat_mul, ← pow_mul]
  set SN := ∑ l ∈ Icc 1 N, Real.log (t + ((l : ℝ) / K) ^ 2) with hSN
  set SK := ∑ k ∈ Icc 1 K, Real.log (t + ((k : ℝ) / K) ^ 2) with hSK
  have h1 := sumlog_lower ht K N hK
  have h2 := sumlog_upper ht K hK
  have hexp : Real.exp (-((K : ℝ) * (Jf t 1 - 6 * Jf t ((N : ℝ) / K)))) * (t / (1 + t)) ≤
      Real.exp ((6 : ℕ) * SN) / Real.exp SK := by
    rw [← Real.exp_sub]
    have hlog : t / (1 + t) = Real.exp (Real.log t - Real.log (1 + t)) := by
      rw [Real.exp_sub, Real.exp_log ht, Real.exp_log (by linarith)]
    rw [hlog, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    push_cast
    nlinarith
  have hA : 0 < (K : ℝ) ^ (2 * N * 6) := by positivity
  have hB : 0 < (K : ℝ) ^ (2 * K) := by positivity
  have hrhs : ((K : ℝ) ^ (2 * N * 6) * Real.exp ((6 : ℕ) * SN)) /
      ((K : ℝ) ^ (2 * K) * Real.exp SK) =
      (K : ℝ) ^ (12 * N) / (K : ℝ) ^ (2 * K) * (Real.exp ((6 : ℕ) * SN) / Real.exp SK) := by
    rw [show 2 * N * 6 = 12 * N by ring]
    field_simp
  rw [hrhs]
  calc _ = (K : ℝ) ^ (12 * N) / (K : ℝ) ^ (2 * K) *
        (Real.exp (-((K : ℝ) * (Jf t 1 - 6 * Jf t ((N : ℝ) / K)))) * (t / (1 + t))) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left hexp (by positivity)

end CatalanCore.Zeta5.Rho
