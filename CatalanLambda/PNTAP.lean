import Mathlib.NumberTheory.LSeries.PrimesInAP
import PrimeNumberTheoremAnd.Catalan.Wiener

/-!
# Prime number theorem in arithmetic progressions (Wiener-Ikehara)

For `a : ZMod q` a unit, `(∑_{n < N, n ≡ a mod q} Λ n) / N → 1 / φ(q)`.
-/

open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt CatalanPNT

namespace CatalanLambda

/-- PNT for the von Mangoldt function restricted to a unit residue class. -/
theorem pnt_residueClass {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun N : ℕ ↦ cumsum (residueClass a) N / N) atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  have l1 : 0 ≤ residueClass a := fun n ↦ residueClass_nonneg a n
  have l5 (σ' : ℝ) (hσ' : 1 < σ') : Summable (nterm (fun n ↦ (residueClass a n : ℂ)) σ') := by
    have h := @ArithmeticFunction.LSeriesSummable_vonMangoldt σ' hσ'
    have h2 : Summable (nterm (fun n ↦ ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)) σ') := by
      simpa only [← nterm_eq_norm_term] using h.norm
    refine Summable.of_nonneg_of_le (fun n ↦ ?_) (fun n ↦ ?_) h2
    · unfold nterm; split_ifs <;> positivity
    · unfold nterm; split_ifs
      · exact le_rfl
      · simp only [Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_nonneg (residueClass_nonneg a n), abs_of_nonneg vonMangoldt_nonneg]
        gcongr
        exact residueClass_le a n
  have l4 : ∃ C : ℝ, ∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖((residueClass a k : ℝ) : ℂ)‖) n ≤ C * n := by
    obtain ⟨C, hC⟩ := vonMangoldt_cheby
    refine ⟨C, fun n ↦ le_trans ?_ (hC n)⟩
    unfold cumsum
    refine Finset.sum_le_sum fun k _ ↦ ?_
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (residueClass_nonneg a k), abs_of_nonneg vonMangoldt_nonneg]
    exact residueClass_le a k
  have l3 := continuousOn_LFunctionResidueClassAux a
  have l2 : Set.EqOn (LFunctionResidueClassAux a)
      (fun s ↦ LSeries (fun n ↦ (residueClass a n : ℂ)) s - (((q.totient : ℝ)⁻¹ : ℝ) : ℂ) / (s - 1))
      {s | 1 < s.re} := by
    intro s hs
    have := eqOn_LFunctionResidueClassAux ha hs
    simpa using this
  exact WienerIkeharaTheorem' (f := residueClass a) (A := (q.totient : ℝ)⁻¹)
    l1 l5 l4 l3 l2

/-- Sum form: `cumsum (residueClass a) N = ∑_{n < N, n ≡ a} Λ n`. -/
theorem cumsum_residueClass_eq {q : ℕ} (a : ZMod q) (N : ℕ) :
    cumsum (residueClass a) N =
      ∑ n ∈ (Finset.range N).filter (fun n : ℕ ↦ (n : ZMod q) = a),
        ArithmeticFunction.vonMangoldt n := by
  unfold cumsum
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp [residueClass, Set.indicator_apply]

/-- PNT in the residue class `a` mod `q`, sum form. -/
theorem pnt_AP {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ (Finset.range N).filter (fun n : ℕ ↦ (n : ZMod q) = a),
        ArithmeticFunction.vonMangoldt n) / N) atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  simpa only [cumsum_residueClass_eq] using pnt_residueClass ha

/-- PNT mod 4: `(∑_{n < N, n ≡ 1 mod 4} Λ n) / N → 1/2`. -/
theorem pnt_mod4_one :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ (Finset.range N).filter (fun n : ℕ ↦ n % 4 = 1),
        ArithmeticFunction.vonMangoldt n) / N) atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := pnt_AP (q := 4) (a := 1) (by decide)
  have e : (Nat.totient 4 : ℝ)⁻¹ = 1 / 2 := by
    rw [show Nat.totient 4 = 2 by decide]; norm_num
  rw [e] at h
  refine h.congr fun N ↦ ?_
  congr 2

/-- PNT mod 4: `(∑_{n < N, n ≡ 3 mod 4} Λ n) / N → 1/2`. -/
theorem pnt_mod4_three :
    Tendsto (fun N : ℕ ↦ (∑ n ∈ (Finset.range N).filter (fun n : ℕ ↦ n % 4 = 3),
        ArithmeticFunction.vonMangoldt n) / N) atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := pnt_AP (q := 4) (a := 3) (by decide)
  have e : (Nat.totient 4 : ℝ)⁻¹ = 1 / 2 := by
    rw [show Nat.totient 4 = 2 by decide]; norm_num
  rw [e] at h
  refine h.congr fun N ↦ ?_
  congr 2

/-- Chebyshev theta function of a residue class: `∑_{p ≤ N, p prime, p ≡ a} log p`. -/
noncomputable def thetaAP (q : ℕ) (a : ZMod q) (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ ↦ n.Prime ∧ (n : ZMod q) = a), Real.log n

theorem thetaAP_le_cumsum {q : ℕ} (a : ZMod q) (N : ℕ) :
    thetaAP q a N ≤ cumsum (residueClass a) (N + 1) := by
  unfold thetaAP cumsum
  calc _ ≤ ∑ n ∈ (Finset.range (N + 1)).filter (fun n : ℕ ↦ n.Prime ∧ (n : ZMod q) = a),
        residueClass a n := by
        refine Finset.sum_le_sum fun n hn ↦ ?_
        obtain ⟨-, hp, hna⟩ := by simpa using hn
        simp [residueClass, hna, ArithmeticFunction.vonMangoldt_apply_prime hp]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun n _ _ ↦ residueClass_nonneg a n)

/-- `θ(N; q, a) / N` has limsup at most `1/φ(q)`: for every `ε > 0` eventually
`θ(N; q, a) ≤ (1/φ(q) + ε) N`. -/
theorem thetaAP_upper {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, thetaAP q a N / N ≤ (q.totient : ℝ)⁻¹ + ε := by
  have h1 := (pnt_residueClass ha).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun N : ℕ ↦ ((N : ℝ) + 1) / N) atTop (𝓝 1) := by
    have : Tendsto (fun N : ℕ ↦ 1 + 1 / (N : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    simp only [add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    field_simp
  have h3 := h1.mul h2
  rw [mul_one] at h3
  filter_upwards [h3.eventually (gt_mem_nhds (lt_add_of_pos_right ((q.totient : ℝ)⁻¹) hε)),
    eventually_gt_atTop 0] with N hN hN0
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN0
  refine le_trans ?_ hN.le
  simp only [Function.comp, Nat.cast_add, Nat.cast_one]
  have : cumsum (residueClass a) (N + 1) / ((N : ℝ) + 1) * (((N : ℝ) + 1) / N)
      = cumsum (residueClass a) (N + 1) / N := by field_simp
  rw [this]
  gcongr
  exact thetaAP_le_cumsum a N

/-- `θ(N; 4, a) ≤ (1/2 + ε) N` eventually, for `a = 1` and `a = 3`. -/
theorem theta_mod4_upper {a : ZMod 4} (ha : a = 1 ∨ a = 3) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, thetaAP 4 a N / N ≤ 1 / 2 + ε := by
  have hu : IsUnit a := by rcases ha with rfl | rfl <;> decide
  have e : (Nat.totient 4 : ℝ)⁻¹ = 1 / 2 := by
    rw [show Nat.totient 4 = 2 by decide]; norm_num
  simpa [e] using thetaAP_upper hu hε


end CatalanLambda
