module

public import CatalanCore.Zeta5.Criterion.Family
public import CatalanCore.Measure.Scaling
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# The terminal assembly: `μ(ζ(5)) < 87` from content, decay and the ρ bound
(ledger ZA10, ZA16, ZA17, ZA18)

Three named hypotheses, each the interface of another agent's deliverable:

* `hΛ : HasScaledContent zeta5Family zeta5Scale Λ` (ZA06/ZA07/ZA17, content side): an integer
  `den n` (the normaliser `m_{K,M}`) with `q^{37 n} · den n · F_{40n}(p/q) ∈ ℤ` and
  `log (den n) ≤ (Λ + ε) (40 n)²` for large `n`.
* `hD : DecayAtConst D` (ZD34, decay side): `F_{40n}(ζ(5)) ≤ exp(-(D - δ)(40 n)²)` for large `n`.
* `hρ : RhoBound ρ` (ZR10, ρ side): `|vᵀ M_n v| ≤ exp(ρ · 40 n) vᵀ G_n v` for large `n`.

`zeta5_hasScaledDecay` (ZA16): decay at the constant plus `ρ` give the window decay
`HasScaledDecay zeta5Family zeta5Scale D ρ` (relative-norm bound `F_n(x) ≤ 2 F_n(ζ)`).
`za10_threshold` (ZA10): the exact rational inequality at `D = 1.38500086`, `Λ = 1.288519`.
`zeta5_measure` (ZA18): `MeasureLBAt ζ(5) 87`, and the exact-exponent forms.
-/

open Polynomial Matrix Apery CatalanCore CatalanCore.Uniform CatalanCore.Measure

namespace CatalanCore.Zeta5

/-- **Decay at the constant** (interface of ZD34): for every `δ > 0` and all large `n`,
`F_{40n}(ζ(5)) ≤ exp(-(D - δ) (40 n)²)`. -/
def DecayAtConst (D : ℝ) : Prop :=
  ∀ δ > 0, ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
    aeval Apery.zeta5 (Apery.F n) ≤ Real.exp (-(D - δ) * ((40 * n : ℕ) : ℝ) ^ 2)

/-- **ZA16.**  Decay at `ζ(5)` and the ρ bound give the window decay. -/
theorem zeta5_hasScaledDecay {D ρ : ℝ} (hρ : RhoBound ρ) (hD : DecayAtConst D) :
    HasScaledDecay zeta5Family zeta5Scale D ρ := by
  obtain ⟨N0, hN0⟩ := hρ
  intro ε hε
  obtain ⟨N1, hN1⟩ := hD (ε / 2) (by positivity)
  let M : ℕ := max (max N0 N1) (max (winN ε) (⌈2 / ε⌉₊ + 1))
  refine ⟨40 * M, fun (n : ℕ) _ hr t ht => ?_⟩
  have hnM : M ≤ n := by unfold zeta5Scale at hr; omega
  have hnN0 : N0 ≤ n := (((le_max_left _ _).trans (le_max_left _ _)).trans hnM)
  have hnN1 : N1 ≤ n := (((le_max_right _ _).trans (le_max_left _ _)).trans hnM)
  have hnw : winN ε ≤ n := (((le_max_left _ _).trans (le_max_right _ _)).trans hnM)
  have hn2 : 2 / ε ≤ (n : ℝ) := by
    have h1 : ⌈2 / ε⌉₊ + 1 ≤ n := (((le_max_right _ _).trans (le_max_right _ _)).trans hnM)
    have h2 : ⌈2 / ε⌉₊ ≤ n := by omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast h2)
  have ht' : |t| ≤ Real.exp (-(ρ + ε) * ((40 * n : ℕ) : ℝ)) := ht
  have hprod := window_bound ρ ε hε n hnw t ht'
  have hb := F_pencil_bounds n ρ (hN0 n hnN0) (Apery.zeta5 + t)
    (by rwa [add_sub_cancel_left])
  have hF := hN1 n hnN1
  -- 2 ≤ exp (ε K² / 2)
  have hεn : 2 ≤ ε * n := by
    have := (div_le_iff₀ hε).mp hn2
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnpos : 0 < n := by
    by_contra h0
    have : n = 0 := by omega
    subst this
    simp at hεn
    linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hy : 1 ≤ ε * ((40 * n : ℕ) : ℝ) ^ 2 / 2 := by
    have h3 : 2 * (n : ℝ) ≤ ε * n * n := mul_le_mul_of_nonneg_right hεn hn0
    have h4 : ε * ((40 * n : ℕ) : ℝ) ^ 2 / 2 = 800 * (ε * n * n) := by push_cast; ring
    rw [h4]
    linarith
  have h2 : (2 : ℝ) ≤ Real.exp (ε * ((40 * n : ℕ) : ℝ) ^ 2 / 2) := by
    have := Real.add_one_le_exp (ε * ((40 * n : ℕ) : ℝ) ^ 2 / 2)
    linarith
  have hev : zeta5Family.evalR n (zeta5Family.const + t) = aeval (Apery.zeta5 + t) (Apery.F n) := rfl
  rw [hev, abs_of_pos hb.1]
  calc aeval (Apery.zeta5 + t) (Apery.F n)
      ≤ 2 * aeval Apery.zeta5 (Apery.F n) := hb.2
    _ ≤ 2 * Real.exp (-(D - ε / 2) * ((40 * n : ℕ) : ℝ) ^ 2) := by linarith
    _ ≤ Real.exp (ε * ((40 * n : ℕ) : ℝ) ^ 2 / 2) *
          Real.exp (-(D - ε / 2) * ((40 * n : ℕ) : ℝ) ^ 2) := by
        nlinarith [Real.exp_pos (-(D - ε / 2) * ((40 * n : ℕ) : ℝ) ^ 2)]
    _ = Real.exp (-(D - ε) * ((zeta5Scale n : ℕ) : ℝ) ^ 2) := by
        rw [← Real.exp_add]; unfold zeta5Scale; congr 1; ring

/-- A common denominator of the coefficients clears the denominators of `q^d P(p/q)`. -/
lemma exists_den_int (P : ℚ[X]) (d : ℕ) (hd : P.natDegree ≤ d) :
    ∃ L : ℕ, 0 < L ∧ ∀ p q : ℤ, 0 < q →
      ∃ z : ℤ, (q : ℚ) ^ d * L * P.eval ((p : ℚ) / q) = z := by
  classical
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = ∏ i ∈ Finset.range (d + 1), (P.coeff i).den := ⟨_, rfl⟩
  refine ⟨L, ?_, ?_⟩
  · rw [hL]; exact Finset.prod_pos fun i _ => (P.coeff i).den_pos
  · intro p q hq
    have hw : ∀ i ∈ Finset.range (d + 1), ∃ w : ℤ, (L : ℚ) * P.coeff i = w := by
      intro i hi
      have hdvd : (P.coeff i).den ∣ L := by
        rw [hL]; exact Finset.dvd_prod_of_mem _ hi
      obtain ⟨k, hk⟩ := hdvd
      refine ⟨(k : ℤ) * (P.coeff i).num, ?_⟩
      have h1 := Rat.mul_den_eq_num (P.coeff i)
      rw [hk]; push_cast
      calc ((P.coeff i).den : ℚ) * k * P.coeff i
          = k * (P.coeff i * (P.coeff i).den) := by ring
        _ = k * ((P.coeff i).num : ℚ) := by rw [h1]
    choose! w hw using hw
    refine ⟨∑ i ∈ Finset.range (d + 1), w i * p ^ i * q ^ (d - i), ?_⟩
    rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < d + 1), Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun i hi => ?_
    have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hqne : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    have hqd : (q : ℚ) ^ d = q ^ i * q ^ (d - i) := by rw [← pow_add]; congr 1; omega
    rw [← hw i hi, hqd, div_pow]
    field_simp

/-- **Content interface, eventual form.**  The content side may state integrality and the
log bound only for `n ≥ N0`; for the finitely many `n < N0` the normaliser is replaced by a
common denominator of the coefficients of `F_n` (no loss: `HasScaledContent` bounds `log den`
only at large scale). -/
theorem hasScaledContent_of_eventually {Λ : ℝ} (N0 : ℕ) (den : ℕ → ℕ)
    (hpos : ∀ n, N0 ≤ n → 0 < den n)
    (hint : ∀ n, N0 ≤ n → ∀ p q : ℤ, 0 < q →
      ∃ z : ℤ, (q : ℚ) ^ (37 * n) * den n * (Apery.F n).eval ((p : ℚ) / q) = z)
    (hlog : ∀ ε > 0, ∃ R0 : ℕ, ∀ n, N0 ≤ n → R0 ≤ 40 * n →
      Real.log (den n) ≤ (Λ + ε) * ((40 * n : ℕ) : ℝ) ^ 2) :
    HasScaledContent zeta5Family zeta5Scale Λ := by
  classical
  have hsmall : ∀ n : ℕ, ∃ L : ℕ, 0 < L ∧ ∀ p q : ℤ, 0 < q →
      ∃ z : ℤ, (q : ℚ) ^ (37 * n) * L * (Apery.F n).eval ((p : ℚ) / q) = z :=
    fun n => exists_den_int (Apery.F n) (37 * n) (natDegree_F n).le
  choose Ls hLpos hLint using hsmall
  refine ⟨fun n => if N0 ≤ n then den n else Ls n, ?_, ?_, ?_⟩
  · intro n
    by_cases h : N0 ≤ n
    · simp only [h, ite_true]; exact hpos n h
    · simp only [h, ite_false]; exact hLpos n
  · intro (n : ℕ) _ p q hq
    by_cases h : N0 ≤ n
    · simp only [h, ite_true]; exact hint n h p q hq
    · simp only [h, ite_false]; exact hLint n p q hq
  · intro ε hε
    obtain ⟨R0, hR⟩ := hlog ε hε
    refine ⟨max R0 (40 * N0), fun (n : ℕ) _ hr => ?_⟩
    have hn : N0 ≤ n := by unfold zeta5Scale at hr; have := le_max_right R0 (40 * N0); omega
    have hR0 : R0 ≤ 40 * n := by
      unfold zeta5Scale at hr; have := le_max_left R0 (40 * N0); omega
    simp only [hn, ite_true]
    exact hR n hn hR0

/-- **ZA17/ZA18, generic form.**  Content `Λ`, decay `D`, window constant `ρ`:
`MeasureLB (37/40 · ρ / (D - Λ))` for Fauzan's family. -/
theorem zeta5_measureLB_of {Λ D ρ : ℝ}
    (hΛ : HasScaledContent zeta5Family zeta5Scale Λ) (hD : DecayAtConst D)
    (hρ : RhoBound ρ) (hρ0 : 0 < ρ) (hΛD : Λ < D) :
    zeta5Family.MeasureLB (37 / 40 * ρ / (D - Λ)) := by
  refine measure_of_family_nnv_period zeta5Family zeta5Scale 40 (by norm_num)
    (γ := 37 / 40) (K := 0) hΛ (zeta5_hasScaledDecay hρ hD) hΛD hρ0 (by norm_num) le_rfl
    ?_ (fun n _ => ⟨n, rfl⟩) ⟨0, fun s _ => ⟨s, trivial, rfl⟩⟩ (zeta5_nearbyNV hρ)
  intro (n : ℕ) _
  show ((37 * n : ℕ) : ℝ) ≤ 37 / 40 * ((40 * n : ℕ) : ℝ) + 0
  push_cast; linarith

/-- **ZA10.**  The exact rational inequality `(37/40)(907427/10⁵)/(D − Λ) < 87` at the lower
end `D = 138500086/10⁸` of the certified decay and `Λ = 1288519/10⁶` (kernel cost: a handful of
rational operations in `norm_num`; no `decide +kernel`). -/
theorem za10_threshold :
    (37 / 40 : ℚ) * (907427 / 10 ^ 5) / (138500086 / 10 ^ 8 - 1288519 / 10 ^ 6) < 87 := by
  norm_num

/-- Real version of `za10_threshold`. -/
theorem za10_threshold_real :
    (37 / 40 : ℝ) * (907427 / 10 ^ 5) / (138500086 / 10 ^ 8 - 1288519 / 10 ^ 6) < 87 := by
  norm_num

/-- The exponent of the final bound is below 87 whenever `Λ ≤ 1288519/10⁶` and
`D ≥ 138500086/10⁸` (monotonicity in `D - Λ` plus `za10_threshold`). -/
lemma exponent_lt_87 {Λ D : ℝ} (hΛ0 : Λ ≤ 1288519 / 10 ^ 6) (hD0 : 138500086 / 10 ^ 8 ≤ D) :
    37 / 40 * (907427 / 10 ^ 5) / (D - Λ) < 87 := by
  have hpos : (0 : ℝ) < 138500086 / 10 ^ 8 - 1288519 / 10 ^ 6 := by norm_num
  have hle : (138500086 / 10 ^ 8 - 1288519 / 10 ^ 6 : ℝ) ≤ D - Λ := by linarith
  calc 37 / 40 * (907427 / 10 ^ 5) / (D - Λ)
      ≤ 37 / 40 * (907427 / 10 ^ 5) / (138500086 / 10 ^ 8 - 1288519 / 10 ^ 6) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hle
    _ < 87 := za10_threshold_real

/-- **ZA18 (`MeasureLB` form).**  `μ(ζ(5)) ≤ 87` for the family, from content `Λ ≤ 1.288519`,
decay `D ≥ 1.38500086` and `ρ = 9.07427`. -/
theorem zeta5_measureLB {Λ D : ℝ}
    (hΛ : HasScaledContent zeta5Family zeta5Scale Λ) (hΛ0 : Λ ≤ 1288519 / 10 ^ 6)
    (hD : DecayAtConst D) (hD0 : 138500086 / 10 ^ 8 ≤ D)
    (hρ : RhoBound (907427 / 10 ^ 5)) :
    zeta5Family.MeasureLB 87 := by
  have hΛD : Λ < D := by
    have : (1288519 / 10 ^ 6 : ℝ) < 138500086 / 10 ^ 8 := by norm_num
    linarith
  have h := zeta5_measureLB_of hΛ hD hρ (by norm_num) hΛD
  rw [MeasureLB_iff] at h ⊢
  exact MeasureLBAt.mono (exponent_lt_87 hΛ0 hD0).le h

/-- **ZA18 (`MeasureLBAt` form).** -/
theorem zeta5_measure {Λ D : ℝ}
    (hΛ : HasScaledContent zeta5Family zeta5Scale Λ) (hΛ0 : Λ ≤ 1288519 / 10 ^ 6)
    (hD : DecayAtConst D) (hD0 : 138500086 / 10 ^ 8 ≤ D)
    (hρ : RhoBound (907427 / 10 ^ 5)) :
    MeasureLBAt Apery.zeta5 87 :=
  zeta5_measureLB hΛ hΛ0 hD hD0 hρ

/-- **ZA18, exact exponent (`μ < 87`).**  For all large `q` and all `p` coprime to `q`:
`q^{-87} < |ζ(5) - p/q|`. -/
theorem zeta5_measure_exact {Λ D : ℝ}
    (hΛ : HasScaledContent zeta5Family zeta5Scale Λ) (hΛ0 : Λ ≤ 1288519 / 10 ^ 6)
    (hD : DecayAtConst D) (hD0 : 138500086 / 10 ^ 8 ≤ D)
    (hρ : RhoBound (907427 / 10 ^ 5)) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(87 : ℝ)) < |Apery.zeta5 - (p : ℝ) / q| := by
  have hΛD : Λ < D := by
    have : (1288519 / 10 ^ 6 : ℝ) < 138500086 / 10 ^ 8 := by norm_num
    linarith
  have h := zeta5_measureLB_of hΛ hD hρ (by norm_num) hΛD
  rw [MeasureLB_iff] at h
  have hlt := exponent_lt_87 hΛ0 hD0
  obtain ⟨q₀, hq⟩ := h (87 - 37 / 40 * (907427 / 10 ^ 5) / (D - Λ)) (by linarith)
  refine ⟨q₀, fun p q hq0 hc => ?_⟩
  have := hq p q hq0 hc
  have e : (37 / 40 * (907427 / 10 ^ 5) / (D - Λ) +
      (87 - 37 / 40 * (907427 / 10 ^ 5) / (D - Λ)) : ℝ) = 87 := by ring
  rw [e] at this
  exact this

/-- The same with `riemannZeta 5` in place of `Apery.zeta5`. -/
theorem zeta5_measure_riemann {Λ D : ℝ}
    (hΛ : HasScaledContent zeta5Family zeta5Scale Λ) (hΛ0 : Λ ≤ 1288519 / 10 ^ 6)
    (hD : DecayAtConst D) (hD0 : 138500086 / 10 ^ 8 ≤ D)
    (hρ : RhoBound (907427 / 10 ^ 5)) :
    ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
      (q : ℝ) ^ (-(87 : ℝ)) < ‖riemannZeta 5 - (p : ℂ) / (q : ℂ)‖ := by
  obtain ⟨q₀, hq⟩ := zeta5_measure_exact hΛ hΛ0 hD hD0 hρ
  refine ⟨q₀, fun p q hq0 hc => ?_⟩
  have h := hq p q hq0 hc
  have e : riemannZeta 5 - (p : ℂ) / (q : ℂ) = ((Apery.zeta5 - (p : ℝ) / q : ℝ) : ℂ) := by
    rw [riemannZeta_five]; push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  exact h

end CatalanCore.Zeta5

#print axioms CatalanCore.Uniform.measure_of_family_nnv
#print axioms CatalanCore.Uniform.measure_of_family_nnv_period
#print axioms Apery.det_pencil_bounds
#print axioms CatalanCore.Zeta5.F_pencil_bounds
#print axioms CatalanCore.Zeta5.zeta5_nearbyNV
#print axioms CatalanCore.Zeta5.zeta5_hasScaledDecay
#print axioms CatalanCore.Zeta5.hasScaledContent_of_eventually
#print axioms CatalanCore.Zeta5.zeta5_measureLB_of
#print axioms CatalanCore.Zeta5.za10_threshold
#print axioms CatalanCore.Zeta5.zeta5_measureLB
#print axioms CatalanCore.Zeta5.zeta5_measure
#print axioms CatalanCore.Zeta5.zeta5_measure_exact
#print axioms CatalanCore.Zeta5.zeta5_measure_riemann
