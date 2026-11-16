module

public import CatalanCore.Zeta5.Rho.Residue
public import CatalanCore.Zeta5.Rho.Steps
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-!
# The node estimate for the residues (ledger ZR04)

`|r_j| ≤ exp(K · L(u_j))`, `L(u) = 6[g(α-u) + g(α+u)] - g(1-u) - g(1+u)`, `g(x) = x(log|x| - 1)`,
`g(0) = 0`, for `N < j ≤ K`, `u = j/K`, `α = N/K`.

Riemann sums of the monotone functions `log(u² - v²)` and `log(v² - u²)` are compared with the
integrals through the antiderivatives `φ_u(v) = g(u+v) - g(u-v)` and `ψ_u(v) = g(v+u) + g(v-u)`
and the mean value theorem (`Steps`), with no integrals.
-/

namespace CatalanCore.Zeta5.Rho

open Set Finset Real

/-- `g(x) = x (log |x| - 1)` (Lean's `Real.log` is `log |·|`), `g(0) = 0`. -/
noncomputable def gfun (x : ℝ) : ℝ := x * (Real.log x - 1)

theorem gfun_zero : gfun 0 = 0 := by simp [gfun]

theorem continuous_gfun : Continuous gfun := by
  have h : gfun = fun x => x * Real.log x - x := by funext x; unfold gfun; ring
  rw [h]
  exact Real.continuous_mul_log.sub continuous_id

theorem hasDerivAt_gfun {x : ℝ} (hx : 0 < x) : HasDerivAt gfun (Real.log x) x := by
  have h := (Real.hasDerivAt_mul_log hx.ne').sub (hasDerivAt_id' x)
  convert h using 1
  · funext y; simp only [Pi.sub_apply, gfun]; ring
  · ring

/-- `φ_u(v) = ∫_0^v log(u² - w²) dw = g(u+v) - g(u-v)`. -/
noncomputable def phiF (u v : ℝ) : ℝ := gfun (u + v) - gfun (u - v)

/-- `ψ_u(v) = ∫_u^v log(w² - u²) dw = g(v+u) + g(v-u)`. -/
noncomputable def psiF (u v : ℝ) : ℝ := gfun (v + u) + gfun (v - u)

theorem continuous_phiF (u : ℝ) : Continuous (phiF u) := by
  unfold phiF
  exact (continuous_gfun.comp (continuous_const.add continuous_id)).sub
    (continuous_gfun.comp (continuous_const.sub continuous_id))

theorem continuous_psiF (u : ℝ) : Continuous (psiF u) := by
  unfold psiF
  exact (continuous_gfun.comp (continuous_id.add continuous_const)).add
    (continuous_gfun.comp (continuous_id.sub continuous_const))

theorem hasDerivAt_phiF {u v : ℝ} (h1 : 0 < u + v) (h2 : 0 < u - v) :
    HasDerivAt (phiF u) (Real.log (u ^ 2 - v ^ 2)) v := by
  have a1 := (hasDerivAt_gfun h1).comp v ((hasDerivAt_id' v).const_add u)
  have a2 := (hasDerivAt_gfun h2).comp v ((hasDerivAt_id' v).const_sub u)
  have := a1.sub a2
  convert this using 1
  · funext y; simp [phiF, Function.comp]
  · rw [show u ^ 2 - v ^ 2 = (u + v) * (u - v) by ring, Real.log_mul h1.ne' h2.ne']; ring

theorem hasDerivAt_psiF {u v : ℝ} (h1 : 0 < v + u) (h2 : 0 < v - u) :
    HasDerivAt (psiF u) (Real.log (v ^ 2 - u ^ 2)) v := by
  have a1 := (hasDerivAt_gfun h1).comp v ((hasDerivAt_id' v).add_const u)
  have a2 := (hasDerivAt_gfun h2).comp v ((hasDerivAt_id' v).sub_const u)
  have := a1.add a2
  convert this using 1
  · funext y; simp [psiF, Function.comp]
  · rw [show v ^ 2 - u ^ 2 = (v + u) * (v - u) by ring, Real.log_mul h1.ne' h2.ne']; ring

theorem phiF_zero (u : ℝ) : phiF u 0 = 0 := by simp [phiF]


theorem cast_pred {l : ℕ} (hl : 1 ≤ l) : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
  push_cast [Nat.cast_sub hl]; ring

/-- Numerator sum: `Σ_{l ≤ N} log(u² - (l/K)²) ≤ K φ_u(N/K)`. -/
theorem sumN {K N j : ℕ} (hK : 0 < K) (hNj : N < j) :
    ∑ l ∈ Icc 1 N, Real.log (((j : ℝ) / K) ^ 2 - ((l : ℝ) / K) ^ 2) ≤
      (K : ℝ) * phiF ((j : ℝ) / K) ((N : ℝ) / K) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  set u : ℝ := (j : ℝ) / K with hu
  have := sum_Icc_le_telescope (fun l : ℕ => Real.log (u ^ 2 - ((l : ℝ) / K) ^ 2))
    (fun l : ℕ => (K : ℝ) * phiF u ((l : ℝ) / K)) N ?_
  · simpa [phiF_zero] using this
  intro l hl1 hlN
  have hlr : (l : ℝ) ≤ N := by exact_mod_cast hlN
  have hNj' : (N : ℝ) < j := by exact_mod_cast hNj
  have hyu : (l : ℝ) / K < u := by
    rw [hu, div_lt_div_iff_of_pos_right hKr]; linarith
  have hx0 : (0 : ℝ) ≤ ((l - 1 : ℕ) : ℝ) / K := by positivity
  have hxy : ((l - 1 : ℕ) : ℝ) / K < (l : ℝ) / K := by
    rw [div_lt_div_iff_of_pos_right hKr, cast_pred hl1]; linarith
  have hstep := step_right_le_anti (φ := phiF u) (f := fun s => Real.log (u ^ 2 - s ^ 2)) hxy
    (continuous_phiF u).continuousOn
    (fun s hs => hasDerivAt_phiF (by linarith [hs.1]) (by linarith [hs.2]))
    (fun a ha b hb hab => by
      have ha0 : 0 ≤ a := le_trans hx0 ha.1.le
      have hb1 : b < u := lt_of_le_of_lt hb.2 hyu
      exact Real.log_le_log (by nlinarith) (by nlinarith))
  have hdiff : (l : ℝ) / K - ((l - 1 : ℕ) : ℝ) / K = 1 / K := by
    rw [cast_pred hl1]; field_simp; ring
  rw [hdiff] at hstep
  have := mul_le_mul_of_nonneg_left hstep hKr.le
  calc Real.log (u ^ 2 - ((l : ℝ) / K) ^ 2)
      = (K : ℝ) * (1 / K * Real.log (u ^ 2 - ((l : ℝ) / K) ^ 2)) := by field_simp
    _ ≤ (K : ℝ) * (phiF u ((l : ℝ) / K) - phiF u (((l - 1 : ℕ) : ℝ) / K)) := this
    _ = _ := by ring

/-- Denominator, below `u`: `K (φ_u(u) - φ_u((N+1)/K)) ≤ Σ_{N<k<j} log(u² - (k/K)²)`. -/
theorem sumD1 {K N j : ℕ} (hK : 0 < K) (hNj : N < j) :
    (K : ℝ) * (phiF ((j : ℝ) / K) ((j : ℝ) / K) - phiF ((j : ℝ) / K) (((N + 1 : ℕ) : ℝ) / K)) ≤
      ∑ k ∈ Ico (N + 1) j, Real.log (((j : ℝ) / K) ^ 2 - ((k : ℝ) / K) ^ 2) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  set u : ℝ := (j : ℝ) / K with hu
  have := telescope_le_sum_Ico (fun k : ℕ => Real.log (u ^ 2 - ((k : ℝ) / K) ^ 2))
    (fun k : ℕ => (K : ℝ) * phiF u ((k : ℝ) / K)) (Nat.succ_le_of_lt hNj) ?_
  · push_cast at this ⊢
    linarith
  intro i hi1 hij
  have hij' : ((i + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hij
  have hyu : ((i + 1 : ℕ) : ℝ) / K ≤ u := by
    rw [hu]; exact div_le_div_of_nonneg_right hij' hKr.le
  have hx0 : (0 : ℝ) ≤ (i : ℝ) / K := by positivity
  have hxy : (i : ℝ) / K < ((i + 1 : ℕ) : ℝ) / K := by
    rw [div_lt_div_iff_of_pos_right hKr]; push_cast; linarith
  have hstep := step_le_left_anti (φ := phiF u) (f := fun s => Real.log (u ^ 2 - s ^ 2)) hxy
    (continuous_phiF u).continuousOn
    (fun s hs => hasDerivAt_phiF (by linarith [hs.1]) (by linarith [hs.2]))
    (fun a ha b hb hab => by
      have ha0 : 0 ≤ a := le_trans hx0 ha.1
      have hb1 : b < u := lt_of_lt_of_le hb.2 hyu
      exact Real.log_le_log (by nlinarith) (by nlinarith))
  have hdiff : ((i + 1 : ℕ) : ℝ) / K - (i : ℝ) / K = 1 / K := by
    push_cast; field_simp; ring
  rw [hdiff] at hstep
  have := mul_le_mul_of_nonneg_left hstep hKr.le
  calc (K : ℝ) * phiF u (((i + 1 : ℕ) : ℝ) / K) - (K : ℝ) * phiF u ((i : ℝ) / K)
      = (K : ℝ) * (phiF u (((i + 1 : ℕ) : ℝ) / K) - phiF u ((i : ℝ) / K)) := by ring
    _ ≤ (K : ℝ) * (1 / K * Real.log (u ^ 2 - ((i : ℝ) / K) ^ 2)) := this
    _ = _ := by field_simp

/-- Denominator, above `u`: `K (ψ_u(1) - ψ_u(u)) ≤ Σ_{j<k≤K} log((k/K)² - u²)`. -/
theorem sumD2 {K j : ℕ} (hK : 0 < K) (hjK : j ≤ K) :
    (K : ℝ) * (psiF ((j : ℝ) / K) ((K : ℝ) / K) - psiF ((j : ℝ) / K) ((j : ℝ) / K)) ≤
      ∑ k ∈ Ioc j K, Real.log (((k : ℝ) / K) ^ 2 - ((j : ℝ) / K) ^ 2) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  set u : ℝ := (j : ℝ) / K with hu
  have := telescope_le_sum_Ioc (fun k : ℕ => Real.log (((k : ℝ) / K) ^ 2 - u ^ 2))
    (fun k : ℕ => (K : ℝ) * psiF u ((k : ℝ) / K)) j K hjK ?_
  · push_cast at this ⊢
    linarith
  intro l hjl hlK
  have hl1 : 1 ≤ l := by omega
  have hjl' : (j : ℝ) ≤ ((l - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : j ≤ l - 1)
  have hxu : u ≤ ((l - 1 : ℕ) : ℝ) / K := by
    rw [hu]; exact div_le_div_of_nonneg_right hjl' hKr.le
  have hxy : ((l - 1 : ℕ) : ℝ) / K < (l : ℝ) / K := by
    rw [div_lt_div_iff_of_pos_right hKr, cast_pred hl1]; linarith
  have hu0 : 0 ≤ u := by positivity
  have hstep := step_le_right (φ := psiF u) (f := fun s => Real.log (s ^ 2 - u ^ 2)) hxy
    (continuous_psiF u).continuousOn
    (fun s hs => hasDerivAt_psiF (by linarith [hs.1]) (by linarith [hs.1]))
    (fun a ha b hb hab => by
      have ha1 : u < a := lt_of_le_of_lt hxu ha.1
      exact Real.log_le_log (by nlinarith) (by nlinarith))
  have hdiff : (l : ℝ) / K - ((l - 1 : ℕ) : ℝ) / K = 1 / K := by
    rw [cast_pred hl1]; field_simp; ring
  rw [hdiff] at hstep
  have := mul_le_mul_of_nonneg_left hstep hKr.le
  calc (K : ℝ) * psiF u ((l : ℝ) / K) - (K : ℝ) * psiF u (((l - 1 : ℕ) : ℝ) / K)
      = (K : ℝ) * (psiF u ((l : ℝ) / K) - psiF u (((l - 1 : ℕ) : ℝ) / K)) := by ring
    _ ≤ (K : ℝ) * (1 / K * Real.log (((l : ℝ) / K) ^ 2 - u ^ 2)) := this
    _ = _ := by field_simp

/-- `φ_u((N+1)/K) ≤ φ_u(N/K)` for `N/K < u ≤ 1`, `(N+1)/K ≤ u`. -/
theorem phi_step_le {K N j : ℕ} (hK : 0 < K) (hNj : N < j) (hjK : j ≤ K) :
    phiF ((j : ℝ) / K) (((N + 1 : ℕ) : ℝ) / K) ≤ phiF ((j : ℝ) / K) ((N : ℝ) / K) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  set u : ℝ := (j : ℝ) / K with hu
  have hNj' : ((N + 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast hNj
  have hyu : ((N + 1 : ℕ) : ℝ) / K ≤ u := by
    rw [hu]; exact div_le_div_of_nonneg_right hNj' hKr.le
  have hx0 : (0 : ℝ) ≤ (N : ℝ) / K := by positivity
  have hxy : (N : ℝ) / K < ((N + 1 : ℕ) : ℝ) / K := by
    rw [div_lt_div_iff_of_pos_right hKr]; push_cast; linarith
  have hu1 : u ≤ 1 := by
    rw [hu, div_le_one hKr]; exact_mod_cast hjK
  have hstep := step_le_left_anti (φ := phiF u) (f := fun s => Real.log (u ^ 2 - s ^ 2)) hxy
    (continuous_phiF u).continuousOn
    (fun s hs => hasDerivAt_phiF (by linarith [hs.1]) (by linarith [hs.2]))
    (fun a ha b hb hab => by
      have ha0 : 0 ≤ a := le_trans hx0 ha.1
      have hb1 : b < u := lt_of_lt_of_le hb.2 hyu
      exact Real.log_le_log (by nlinarith) (by nlinarith))
  have hxu : (N : ℝ) / K < u := lt_of_lt_of_le hxy hyu
  have hlog : Real.log (u ^ 2 - ((N : ℝ) / K) ^ 2) ≤ 0 := by
    apply Real.log_nonpos (by nlinarith)
    nlinarith
  have hpos : 0 < ((N + 1 : ℕ) : ℝ) / K - (N : ℝ) / K := sub_pos.mpr hxy
  have := mul_nonpos_of_nonneg_of_nonpos hpos.le hlog
  linarith


theorem gfun_neg (x : ℝ) : gfun (-x) = - gfun x := by
  unfold gfun; rw [Real.log_neg_eq_log]; ring

/-- `L_α(u) = 6 [g(α-u) + g(α+u)] - g(1-u) - g(1+u)`. -/
noncomputable def Lg (α u : ℝ) : ℝ := 6 * (gfun (α - u) + gfun (α + u)) - gfun (1 - u) - gfun (1 + u)

theorem erase_Ioc_split {K N j : ℕ} (hNj : N < j) (hjK : j ≤ K) :
    (Finset.Ioc N K).erase j = Finset.Ico (N + 1) j ∪ Finset.Ioc j K := by
  ext i
  simp only [Finset.mem_erase, Finset.mem_Ioc, Finset.mem_union, Finset.mem_Ico]
  omega

/-- The logarithm of `|r_j|`, for general `K, N, j`. -/
theorem log_rj_le {K N j : ℕ} (hK : 0 < K) (hNj : N < j) (hjK : j ≤ K) :
    Real.log |((j : ℝ) / K) ^ 4 *
        (∏ l ∈ Finset.Icc 1 N, (((l : ℝ) / K) ^ 2 - ((j : ℝ) / K) ^ 2) ^ 5) /
        ∏ k ∈ (Finset.Ioc N K).erase j, (((k : ℝ) / K) ^ 2 - ((j : ℝ) / K) ^ 2)| ≤
      (K : ℝ) * Lg ((N : ℝ) / K) ((j : ℝ) / K) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  set u : ℝ := (j : ℝ) / K with hu
  have hjpos : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [hu, div_le_one hKr]; exact_mod_cast hjK
  have hNr : (N : ℝ) < j := by exact_mod_cast hNj
  -- nonvanishing
  have hnz1 : ∀ l ∈ Finset.Icc 1 N, ((l : ℝ) / K) ^ 2 - u ^ 2 ≠ 0 := by
    intro l hl h
    have hl' := Finset.mem_Icc.mp hl
    have hlr : (l : ℝ) < j := by exact_mod_cast (by omega : l < j)
    have h1 : (l : ℝ) / K < u := by rw [hu]; exact (div_lt_div_iff_of_pos_right hKr).2 hlr
    have h0 : (0 : ℝ) ≤ (l : ℝ) / K := by positivity
    nlinarith
  have hnz2 : ∀ k ∈ (Finset.Ioc N K).erase j, ((k : ℝ) / K) ^ 2 - u ^ 2 ≠ 0 := by
    intro k hk h
    have hk' := Finset.mem_erase.mp hk
    have hkj : (k : ℝ) ≠ j := by exact_mod_cast hk'.1
    have h0 : (0 : ℝ) ≤ (k : ℝ) / K := by positivity
    have h2 : ((k : ℝ) / K) ^ 2 = u ^ 2 := by linarith
    have h3 : (k : ℝ) / K = u := (sq_eq_sq₀ h0 hu0.le).mp h2
    apply hkj
    rw [hu] at h3
    exact (div_left_inj' hKr.ne').mp h3
  have hP1 : (∏ l ∈ Finset.Icc 1 N, (((l : ℝ) / K) ^ 2 - u ^ 2) ^ 5) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun l hl => pow_ne_zero _ (hnz1 l hl)
  have hP2 : (∏ k ∈ (Finset.Ioc N K).erase j, (((k : ℝ) / K) ^ 2 - u ^ 2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hnz2
  have hP0 : u ^ 4 ≠ 0 := pow_ne_zero _ hu0.ne'
  rw [Real.log_abs, Real.log_div (mul_ne_zero hP0 hP1) hP2, Real.log_mul hP0 hP1,
    Real.log_prod hnz2, Real.log_prod (fun l hl => pow_ne_zero _ (hnz1 l hl)), Real.log_pow]
  simp only [Real.log_pow]
  rw [← Finset.mul_sum]
  -- the three Riemann-sum bounds
  have hN := sumN hK hNj
  have hD1 := sumD1 hK hNj
  have hD2 := sumD2 hK hjK
  have hphi := phi_step_le hK hNj hjK
  rw [erase_Ioc_split hNj hjK, Finset.sum_union (by
    rw [Finset.disjoint_left]; intro i h1 h2
    simp only [Finset.mem_Ico, Finset.mem_Ioc] at h1 h2; omega)]
  have e1 : ∑ k ∈ Finset.Ico (N + 1) j, Real.log (((k : ℝ) / K) ^ 2 - u ^ 2) =
      ∑ k ∈ Finset.Ico (N + 1) j, Real.log (u ^ 2 - ((k : ℝ) / K) ^ 2) :=
    sum_congr rfl fun k _ => by rw [← Real.log_neg_eq_log]; ring_nf
  have e2 : ∑ l ∈ Finset.Icc 1 N, Real.log (((l : ℝ) / K) ^ 2 - u ^ 2) =
      ∑ l ∈ Finset.Icc 1 N, Real.log (u ^ 2 - ((l : ℝ) / K) ^ 2) :=
    sum_congr rfl fun l _ => by rw [← Real.log_neg_eq_log]; ring_nf
  rw [e1, e2]
  have hlogu : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1
  have hKK : (K : ℝ) / K = 1 := div_self hKr.ne'
  have hv1 : phiF u u = gfun (2 * u) := by unfold phiF; rw [sub_self, gfun_zero]; ring_nf
  have hv2 : psiF u u = gfun (2 * u) := by unfold psiF; rw [sub_self, gfun_zero]; ring_nf
  have hv3 : psiF u 1 = gfun (1 + u) + gfun (1 - u) := by unfold psiF; ring_nf
  have hv4 : phiF u ((N : ℝ) / K) = gfun (u + (N : ℝ) / K) + gfun ((N : ℝ) / K - u) := by
    unfold phiF
    have : u - (N : ℝ) / K = -((N : ℝ) / K - u) := by ring
    rw [this, gfun_neg]; ring
  rw [hKK, hv3] at hD2
  rw [hv1] at hD1
  rw [hv2] at hD2
  unfold Lg
  have hphi' : (K : ℝ) * phiF u (((N + 1 : ℕ) : ℝ) / K) ≤ (K : ℝ) * phiF u ((N : ℝ) / K) :=
    mul_le_mul_of_nonneg_left hphi hKr.le
  have hlogu4 : 4 * Real.log u ≤ 0 := by linarith
  have key : (K : ℝ) * (6 * (gfun ((N : ℝ) / K - u) + gfun ((N : ℝ) / K + u)) - gfun (1 - u) - gfun (1 + u)) =
      6 * ((K : ℝ) * phiF u ((N : ℝ) / K)) - (K : ℝ) * (gfun (1 + u) + gfun (1 - u)) := by
    rw [hv4]; ring
  rw [key]
  nlinarith [hN, hD1, hD2, hphi', hlogu4, hv4]


/-- **ZR04.**  `|r_j| ≤ exp(K · L(u_j))`, `u_j = j/K`, `L = L_{3/40}`, for `N < j ≤ K`. -/
theorem rj_abs_le (n : ℕ) (hn : 0 < n) {j : ℕ} (hj : j ∈ Finset.Ioc (3 * n) (40 * n)) :
    |rj n j| ≤ Real.exp ((40 * n : ℝ) * Lg (3 / 40) ((j : ℝ) / (40 * n : ℝ))) := by
  have hj' := Finset.mem_Ioc.mp hj
  have hK : 0 < 40 * n := by omega
  have h := log_rj_le hK hj'.1 hj'.2
  have hα : ((3 * n : ℕ) : ℝ) / ((40 * n : ℕ) : ℝ) = 3 / 40 := by
    push_cast; have : (n : ℝ) ≠ 0 := by positivity
    field_simp
  have hrj : rj n j = ((j : ℝ) / ((40 * n : ℕ) : ℝ)) ^ 4 *
        (∏ l ∈ Finset.Icc 1 (3 * n), (((l : ℝ) / ((40 * n : ℕ) : ℝ)) ^ 2 -
          ((j : ℝ) / ((40 * n : ℕ) : ℝ)) ^ 2) ^ 5) /
        ∏ k ∈ (Finset.Ioc (3 * n) (40 * n)).erase j, (((k : ℝ) / ((40 * n : ℕ) : ℝ)) ^ 2 -
          ((j : ℝ) / ((40 * n : ℕ) : ℝ)) ^ 2) := by
    unfold rj uu
    push_cast
    rfl
  rw [hα] at h
  have hc : ((40 * n : ℕ) : ℝ) = 40 * n := by push_cast; ring
  rw [hc] at h
  rw [hrj, hc]
  generalize (((j : ℝ) / (40 * n : ℝ)) ^ 4 *
        (∏ l ∈ Finset.Icc 1 (3 * n), (((l : ℝ) / (40 * n : ℝ)) ^ 2 - ((j : ℝ) / (40 * n : ℝ)) ^ 2) ^ 5) /
        ∏ k ∈ (Finset.Ioc (3 * n) (40 * n)).erase j, (((k : ℝ) / (40 * n : ℝ)) ^ 2 -
          ((j : ℝ) / (40 * n : ℝ)) ^ 2)) = R at h ⊢
  rcases eq_or_ne R 0 with h0 | h0
  · rw [h0]; simp; exact (Real.exp_pos _).le
  · calc |R| = Real.exp (Real.log |R|) := (Real.exp_log (abs_pos.mpr h0)).symm
      _ ≤ _ := Real.exp_le_exp.mpr h

end CatalanCore.Zeta5.Rho
