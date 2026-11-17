module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

/-!
# Partial fractions with double poles at distinct nodes (generic, any field)

Let `s` be a finite set of nodes `z j` (injective), `W = ∏ (X - z j)` and `f` a polynomial of degree
`< 2 |s|`.  Then `f / W²` is the sum of its principal parts at the nodes:

`f = ∑ k ∈ s, A2 k * u_k² + A1 k * (X - z k) * u_k²`,  `u_k = ∏_{j ≠ k} (X - z j)`,

with `A2 k = f(z k) / u_k(z k)²` and `A1 k = (f'(z k) - (u_k²)'(z k) * A2 k) / u_k(z k)²`.  If moreover
`deg f ≤ 2 |s| - 2` then `∑ A1 k = 0`.  This is the algebraic core of Lai's Lemma 2.2 (ledger LA01, LA02) and
of every double-pole moment functional (design `(K, 2)` with jets `{1, 2}`); nothing here is specific to the
nodes `0, -1, ..., -6n` or the numerator of Lai's `R_n`.
-/

open Polynomial Finset

namespace CatalanCore.Lai.DoublePole

variable {𝕜 : Type*} [Field 𝕜] {ι : Type*} [DecidableEq ι]

/-- `(X - r)² ∣ E` as soon as `E` and `E'` vanish at `r`. -/
theorem sq_dvd_of_eval_derivative {E : 𝕜[X]} {r : 𝕜} (h0 : E.eval r = 0)
    (h1 : (derivative E).eval r = 0) : (X - C r) ^ 2 ∣ E := by
  obtain ⟨F, hF⟩ := dvd_iff_isRoot.2 (show E.IsRoot r from h0)
  have hF0 : F.eval r = 0 := by
    have h2 := congrArg (fun p => (derivative p).eval r) hF
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, eval_add, eval_mul,
      eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, sub_zero, one_mul] at h2
    rw [h1] at h2
    exact h2.symm
  obtain ⟨G, hG⟩ := dvd_iff_isRoot.2 (show F.IsRoot r from hF0)
  exact ⟨G, by rw [hF, hG]; ring⟩

/-- The product over all nodes. -/
noncomputable def nodeProd (s : Finset ι) (z : ι → 𝕜) : 𝕜[X] := ∏ j ∈ s, (X - C (z j))

/-- The product over the other nodes. -/
noncomputable def cofac (s : Finset ι) (z : ι → 𝕜) (k : ι) : 𝕜[X] := ∏ j ∈ s.erase k, (X - C (z j))

/-- Coefficient of the double pole at `z k`. -/
noncomputable def A2 (s : Finset ι) (z : ι → 𝕜) (f : 𝕜[X]) (k : ι) : 𝕜 :=
  f.eval (z k) / ((cofac s z k).eval (z k)) ^ 2

/-- Coefficient of the simple pole at `z k`. -/
noncomputable def A1 (s : Finset ι) (z : ι → 𝕜) (f : 𝕜[X]) (k : ι) : 𝕜 :=
  ((derivative f).eval (z k) -
      2 * (cofac s z k).eval (z k) * (derivative (cofac s z k)).eval (z k) * A2 s z f k) /
    ((cofac s z k).eval (z k)) ^ 2

/-- The principal part at `z k`, as a polynomial over the common denominator. -/
noncomputable def term (s : Finset ι) (z : ι → 𝕜) (f : 𝕜[X]) (k : ι) : 𝕜[X] :=
  C (A2 s z f k) * cofac s z k ^ 2 + C (A1 s z f k) * ((X - C (z k)) * cofac s z k ^ 2)

variable {s : Finset ι} {z : ι → 𝕜}

theorem cofac_eval_ne (hz : Function.Injective z) {k : ι} (hk : k ∈ s) :
    (cofac s z k).eval (z k) ≠ 0 := by
  unfold cofac
  rw [eval_prod, Finset.prod_ne_zero_iff]
  intro j hj
  have hjk : j ≠ k := (Finset.mem_erase.1 hj).1
  simp only [eval_sub, eval_X, eval_C]
  exact sub_ne_zero.2 (fun h => hjk (hz h.symm))

theorem nodeProd_eq (k : ι) (hk : k ∈ s) :
    nodeProd s z = (X - C (z k)) * cofac s z k := by
  unfold nodeProd cofac
  rw [Finset.mul_prod_erase s (fun j => X - C (z j)) hk]

theorem monic_cofac (k : ι) : (cofac s z k).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem natDegree_cofac (k : ι) (hk : k ∈ s) : (cofac s z k).natDegree = s.card - 1 := by
  unfold cofac
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp [Finset.card_erase_of_mem hk]

/-- The sq-divisibility at each node. -/
theorem sq_dvd_diff (hz : Function.Injective z) (f : 𝕜[X]) {k : ι} (hk : k ∈ s) :
    (X - C (z k)) ^ 2 ∣ f - ∑ j ∈ s, term s z f j := by
  rw [← Finset.add_sum_erase s _ hk]
  have h1 : (X - C (z k)) ^ 2 ∣ f - term s z f k := by
    apply sq_dvd_of_eval_derivative
    · have hne := cofac_eval_ne hz hk
      simp only [term, A1, A2, eval_sub, eval_add, eval_mul, eval_C, eval_pow, eval_X, sub_self,
        mul_zero, add_zero]
      field_simp
      ring
    · have hne := cofac_eval_ne hz hk
      simp only [term, A1, A2, derivative_sub, derivative_add, derivative_mul, derivative_C,
        derivative_pow, derivative_X, derivative_sub, eval_sub, eval_add, eval_mul, eval_C,
        eval_pow, eval_X, eval_natCast, sub_self, zero_mul, zero_add, mul_zero, add_zero,
        eval_one, mul_one, one_mul, eval_zero]
      field_simp
      ring
  have h2 : (X - C (z k)) ^ 2 ∣ ∑ j ∈ s.erase k, term s z f j := by
    refine Finset.dvd_sum fun j hj => ?_
    have hjk : j ≠ k := (Finset.mem_erase.1 hj).1
    have hjs : j ∈ s := (Finset.mem_erase.1 hj).2
    have hd : (X - C (z k)) ^ 2 ∣ cofac s z j ^ 2 :=
      pow_dvd_pow_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_erase.2 ⟨hjk.symm, hk⟩)) 2
    unfold term
    exact dvd_add (hd.mul_left _) ((hd.mul_left _).mul_left _)
  have := dvd_sub h1 h2
  convert this using 1
  ring

theorem natDegree_term_le {k : ι} (hk : k ∈ s) (f : 𝕜[X]) : (term s z f k).natDegree ≤ 2 * s.card - 1 := by
  have hu : (cofac s z k ^ 2).natDegree = 2 * (s.card - 1) := by
    rw [natDegree_pow, natDegree_cofac k hk]
  have hpos : 0 < s.card := Finset.card_pos.2 ⟨k, hk⟩
  unfold term
  refine natDegree_add_le_of_degree_le ?_ ?_
  · refine (natDegree_C_mul_le _ _).trans ?_
    rw [hu]; omega
  · refine (natDegree_C_mul_le _ _).trans ?_
    refine (natDegree_mul_le).trans ?_
    rw [hu, natDegree_X_sub_C]; omega

/-- **Partial fractions with double poles.** -/
theorem eq_sum_term (hz : Function.Injective z) {f : 𝕜[X]} (hf : f.degree < ((2 * s.card : ℕ) : WithBot ℕ)) :
    f = ∑ j ∈ s, term s z f j := by
  have hdvd : (∏ j ∈ s, (X - C (z j)) ^ 2) ∣ f - ∑ j ∈ s, term s z f j := by
    refine Finset.prod_dvd_of_coprime (fun a _ b _ hab => ?_) fun k hk => sq_dvd_diff hz f hk
    exact (isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.2
      (sub_ne_zero.2 (fun h => hab (hz h))))).pow
  have hmonic : (∏ j ∈ s, (X - C (z j)) ^ 2).Monic :=
    monic_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow 2
  have hdeg : (∏ j ∈ s, (X - C (z j)) ^ 2).natDegree = 2 * s.card := by
    rw [natDegree_prod_of_monic _ _ fun _ _ => (monic_X_sub_C _).pow 2]
    simp [natDegree_pow, Finset.sum_const, mul_comm]
  have hsum : (∑ j ∈ s, term s z f j).degree < ((2 * s.card : ℕ) : WithBot ℕ) := by
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simpa using hf
    · refine lt_of_le_of_lt (degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro j hj
      refine lt_of_le_of_lt (degree_le_natDegree) ?_
      have := natDegree_term_le (z := z) hj f
      have hpos : 0 < s.card := Finset.card_pos.2 hne
      exact_mod_cast (by omega : (term s z f j).natDegree < 2 * s.card)
  have hlt : (f - ∑ j ∈ s, term s z f j).degree < (∏ j ∈ s, (X - C (z j)) ^ 2).degree := by
    rw [degree_eq_natDegree hmonic.ne_zero, hdeg]
    exact lt_of_le_of_lt (degree_sub_le _ _) (max_lt hf hsum)
  exact sub_eq_zero.1 (eq_zero_of_dvd_of_degree_lt hdvd hlt)

/-- The simple-pole coefficients of a numerator of degree `≤ 2 |s| - 2` sum to zero. -/
theorem sum_A1_eq_zero (hz : Function.Injective z) {f : 𝕜[X]}
    (hf : f.degree < ((2 * s.card - 1 : ℕ) : WithBot ℕ)) : ∑ k ∈ s, A1 s z f k = 0 := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  have hpos : 0 < s.card := Finset.card_pos.2 hne
  have hf' : f.degree < ((2 * s.card : ℕ) : WithBot ℕ) := by
    refine lt_of_lt_of_le hf ?_
    exact_mod_cast (by omega : 2 * s.card - 1 ≤ 2 * s.card)
  have h := congrArg (fun p => p.coeff (2 * s.card - 1)) (eq_sum_term hz hf')
  simp only [finsetSum_coeff] at h
  have hf0 : f.coeff (2 * s.card - 1) = 0 := by
    apply coeff_eq_zero_of_degree_lt
    exact hf
  have hterm : ∀ k ∈ s, (term s z f k).coeff (2 * s.card - 1) = A1 s z f k := by
    intro k hk
    have hu : (cofac s z k ^ 2).natDegree = 2 * (s.card - 1) := by
      rw [natDegree_pow, natDegree_cofac k hk]
    have hm : (cofac s z k ^ 2).Monic := (monic_cofac k).pow 2
    have hlead : (cofac s z k ^ 2).coeff (2 * (s.card - 1)) = 1 := by
      rw [← hu]; exact hm.coeff_natDegree
    have e1 : (C (A2 s z f k) * cofac s z k ^ 2).coeff (2 * s.card - 1) = 0 := by
      rw [coeff_C_mul]
      rw [coeff_eq_zero_of_natDegree_lt (by rw [hu]; omega), mul_zero]
    have e2 : (C (A1 s z f k) * ((X - C (z k)) * cofac s z k ^ 2)).coeff (2 * s.card - 1)
        = A1 s z f k := by
      have e : 2 * s.card - 1 = 2 * (s.card - 1) + 1 := by omega
      rw [e, coeff_C_mul, sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul, hlead,
        coeff_eq_zero_of_natDegree_lt (by rw [hu]; omega)]
      simp
    unfold term
    rw [coeff_add, e1, e2, zero_add]
  rw [Finset.sum_congr rfl hterm, hf0] at h
  exact h.symm

/-- Pointwise form: for `t` not a node, `f(t) / W(t)² = ∑ A1 k / (t - z k) + A2 k / (t - z k)²`. -/
theorem eval_div_eq (hz : Function.Injective z) {f : 𝕜[X]}
    (hf : f.degree < ((2 * s.card : ℕ) : WithBot ℕ)) {t : 𝕜} (ht : ∀ k ∈ s, t ≠ z k) :
    f.eval t / (nodeProd s z).eval t ^ 2 =
      ∑ k ∈ s, (A1 s z f k / (t - z k) + A2 s z f k / (t - z k) ^ 2) := by
  have h := congrArg (Polynomial.eval t) (eq_sum_term hz hf)
  rw [eval_finsetSum] at h
  have hW : (nodeProd s z).eval t ≠ 0 := by
    unfold nodeProd
    rw [eval_prod, Finset.prod_ne_zero_iff]
    intro j hj
    simpa [sub_ne_zero] using ht j hj
  rw [h, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hW2 : (nodeProd s z).eval t = (t - z k) * (cofac s z k).eval t := by
    rw [nodeProd_eq k hk]; simp
  have htk : t - z k ≠ 0 := sub_ne_zero.2 (ht k hk)
  have hu : (cofac s z k).eval t ≠ 0 := by
    rintro h0
    apply hW
    rw [hW2, h0, mul_zero]
  rw [hW2]
  simp only [term, eval_add, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
  field_simp
  ring

/-- Logarithmic derivative of a product of linear factors. -/
theorem eval_derivative_prod_X_sub (s : Finset ι) (ρ : ι → 𝕜) {x : 𝕜} (hx : ∀ i ∈ s, x ≠ ρ i) :
    (derivative (∏ i ∈ s, (X - C (ρ i)))).eval x =
      (∏ i ∈ s, (x - ρ i)) * ∑ i ∈ s, 1 / (x - ρ i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hxa : x - ρ a ≠ 0 := sub_ne_zero.2 (hx a (Finset.mem_insert_self _ _))
    have ih' := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, derivative_mul]
    simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, derivative_sub, derivative_X,
      derivative_C, sub_zero, eval_one, eval_prod]
    rw [ih']
    field_simp


/-! ### The moment functional on the half line

For real coefficients `a1 a2` the function `pfFun K a1 a2` is the sum of principal parts at the nodes
`0, -1, ..., -K`.  The functional `g ↦ c1 ∑_{m ≥ 1} g'(m) + c2 ∑_{m ≥ 1} g''(m)` evaluates to harmonic
numbers plus `ζ(3)`, `ζ(4)` once `∑ a1 = 0`. -/

section Moment

/-- `∑_{i < k} 1/(i+1)^s`. -/
noncomputable def harm (s k : ℕ) : ℝ := ∑ i ∈ range k, 1 / ((i : ℝ) + 1) ^ s

/-- `∑_{i ≥ 0} 1/(i+1)^s`. -/
noncomputable def zetaSum (s : ℕ) : ℝ := ∑' i : ℕ, 1 / ((i : ℝ) + 1) ^ s

/-- The sum of principal parts at the nodes `-k`, `k ≤ K`. -/
noncomputable def pfFun (K : ℕ) (a1 a2 : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ range (K + 1), (a1 k / (t + k) + a2 k / (t + k) ^ 2)

/-- Its first derivative (closed form). -/
noncomputable def pfD1 (K : ℕ) (a1 a2 : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ range (K + 1), (-a1 k / (t + k) ^ 2 + -(2 * a2 k) / (t + k) ^ 3)

/-- Its second derivative (closed form). -/
noncomputable def pfD2 (K : ℕ) (a1 a2 : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ range (K + 1), (2 * a1 k / (t + k) ^ 3 + 6 * a2 k / (t + k) ^ 4)

theorem hasDerivAt_inv_pow' (n : ℕ) {x : ℝ} (hx : x ≠ 0) (c : ℝ) :
    HasDerivAt (fun y : ℝ => c / y ^ (n + 1)) (-((n + 1 : ℝ) * c) / x ^ (n + 2)) x := by
  have h := ((hasDerivAt_pow (n + 1) x).inv (pow_ne_zero _ hx)).const_mul c
  convert h using 1
  · funext y; simp [div_eq_mul_inv]
  · simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

theorem hasDerivAt_shift (n : ℕ) {t : ℝ} (k : ℕ) (ht : 0 < t) (c : ℝ) :
    HasDerivAt (fun y : ℝ => c / (y + k) ^ (n + 1)) (-((n + 1 : ℝ) * c) / (t + k) ^ (n + 2)) t := by
  have hx : t + (k : ℝ) ≠ 0 := by positivity
  exact HasDerivAt.comp_add_const t (k : ℝ) (hasDerivAt_inv_pow' n hx c)

theorem hasDerivAt_pfFun (K : ℕ) (a1 a2 : ℕ → ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (pfFun K a1 a2) (pfD1 K a1 a2 t) t := by
  unfold pfFun pfD1
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h1 := hasDerivAt_shift 0 k ht (a1 k)
  have h2 := hasDerivAt_shift 1 k ht (a2 k)
  simp only [zero_add, pow_one] at h1
  have := h1.add h2
  convert this using 1
  · norm_num
    try ring

theorem hasDerivAt_pfD1 (K : ℕ) (a1 a2 : ℕ → ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (pfD1 K a1 a2) (pfD2 K a1 a2 t) t := by
  unfold pfD1 pfD2
  refine HasDerivAt.fun_sum fun k _ => ?_
  have h1 := hasDerivAt_shift 1 k ht (-a1 k)
  have h2 := hasDerivAt_shift 2 k ht (-(2 * a2 k))
  have := h1.add h2
  convert this using 1
  · norm_num
    try ring

theorem deriv_of_eqOn {g : ℝ → ℝ} {K : ℕ} {a1 a2 : ℕ → ℝ} (hg : ∀ t > 0, g t = pfFun K a1 a2 t)
    {t : ℝ} (ht : 0 < t) : deriv g t = pfD1 K a1 a2 t := by
  have hev : g =ᶠ[nhds t] pfFun K a1 a2 :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun x hx => hg x hx
  exact ((hasDerivAt_pfFun K a1 a2 ht).congr_of_eventuallyEq hev).deriv

theorem deriv_deriv_of_eqOn {g : ℝ → ℝ} {K : ℕ} {a1 a2 : ℕ → ℝ} (hg : ∀ t > 0, g t = pfFun K a1 a2 t)
    {t : ℝ} (ht : 0 < t) : deriv (deriv g) t = pfD2 K a1 a2 t := by
  have hev : deriv g =ᶠ[nhds t] pfD1 K a1 a2 :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds ht) fun x hx => deriv_of_eqOn hg hx
  exact ((hasDerivAt_pfD1 K a1 a2 ht).congr_of_eventuallyEq hev).deriv

theorem summable_zetaTerm (s : ℕ) (hs : 2 ≤ s) :
    Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ s) := by
  have h := (Real.summable_one_div_nat_pow (p := s)).2 (by omega)
  have := (summable_nat_add_iff 1).2 h
  simpa [one_div] using this

/-- `∑_{m ≥ 0} 1/(m+1+k)^s = ζ(s) - H_k(s)`. -/
theorem tsum_tail (s k : ℕ) (hs : 2 ≤ s) :
    ∑' m : ℕ, 1 / ((m : ℝ) + 1 + k) ^ s = zetaSum s - harm s k := by
  have h := (summable_zetaTerm s hs).sum_add_tsum_nat_add k
  unfold zetaSum harm
  rw [← h]
  have : (fun m : ℕ => 1 / ((m : ℝ) + 1 + k) ^ s) = fun m : ℕ => 1 / (((m + k : ℕ) : ℝ) + 1) ^ s := by
    funext m; push_cast; ring_nf
  rw [this]; ring

theorem summable_tail (s k : ℕ) (hs : 2 ≤ s) :
    Summable (fun m : ℕ => 1 / ((m : ℝ) + 1 + k) ^ s) := by
  have := (summable_nat_add_iff k).2 (summable_zetaTerm s hs)
  convert this using 2 with m
  push_cast; ring_nf

/-- **The moment functional.**  If `∑ a1 = 0`, and `g` agrees with `pfFun` on `(0, ∞)`, then
`c1 ∑_{m≥1} g'(m) + c2 ∑_{m≥1} g''(m)` is explicit in harmonic numbers, `ζ(3)` and `ζ(4)`. -/
theorem moment (K : ℕ) (a1 a2 : ℕ → ℝ) (g : ℝ → ℝ) (hg : ∀ t > 0, g t = pfFun K a1 a2 t)
    (h1 : ∑ k ∈ range (K + 1), a1 k = 0) (c1 c2 : ℝ) :
    c1 * ∑' m : ℕ, deriv g ((m : ℝ) + 1) + c2 * ∑' m : ℕ, deriv (deriv g) ((m : ℝ) + 1) =
      ∑ k ∈ range (K + 1), (a1 k * (c1 * harm 2 k - 2 * c2 * harm 3 k) +
        a2 k * (2 * c1 * harm 3 k - 6 * c2 * harm 4 k)) +
      (∑ k ∈ range (K + 1), a2 k) * (-2 * c1 * zetaSum 3 + 6 * c2 * zetaSum 4) := by
  have hpos : ∀ m : ℕ, (0 : ℝ) < (m : ℝ) + 1 := fun m => by positivity
  have e1 : ∀ m : ℕ, deriv g ((m : ℝ) + 1) = ∑ k ∈ range (K + 1),
      (-a1 k * (1 / ((m : ℝ) + 1 + k) ^ 2) + -(2 * a2 k) * (1 / ((m : ℝ) + 1 + k) ^ 3)) := by
    intro m
    rw [deriv_of_eqOn hg (hpos m)]
    unfold pfD1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have e2 : ∀ m : ℕ, deriv (deriv g) ((m : ℝ) + 1) = ∑ k ∈ range (K + 1),
      (2 * a1 k * (1 / ((m : ℝ) + 1 + k) ^ 3) + 6 * a2 k * (1 / ((m : ℝ) + 1 + k) ^ 4)) := by
    intro m
    rw [deriv_deriv_of_eqOn hg (hpos m)]
    unfold pfD2
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have t1 : ∑' m : ℕ, deriv g ((m : ℝ) + 1) = ∑ k ∈ range (K + 1),
      (-a1 k * (zetaSum 2 - harm 2 k) + -(2 * a2 k) * (zetaSum 3 - harm 3 k)) := by
    simp_rw [e1]
    rw [Summable.tsum_finsetSum fun k _ => ((summable_tail 2 k le_rfl).mul_left _).add
      ((summable_tail 3 k (by norm_num)).mul_left _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Summable.tsum_add ((summable_tail 2 k le_rfl).mul_left _)
      ((summable_tail 3 k (by norm_num)).mul_left _),
      tsum_mul_left, tsum_mul_left, tsum_tail 2 k le_rfl, tsum_tail 3 k (by norm_num)]
  have t2 : ∑' m : ℕ, deriv (deriv g) ((m : ℝ) + 1) = ∑ k ∈ range (K + 1),
      (2 * a1 k * (zetaSum 3 - harm 3 k) + 6 * a2 k * (zetaSum 4 - harm 4 k)) := by
    simp_rw [e2]
    rw [Summable.tsum_finsetSum fun k _ => ((summable_tail 3 k (by norm_num)).mul_left _).add
      ((summable_tail 4 k (by norm_num)).mul_left _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Summable.tsum_add ((summable_tail 3 k (by norm_num)).mul_left _)
      ((summable_tail 4 k (by norm_num)).mul_left _),
      tsum_mul_left, tsum_mul_left, tsum_tail 3 k (by norm_num), tsum_tail 4 k (by norm_num)]
  rw [t1, t2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  have hz : ∑ k ∈ range (K + 1), a1 k * zetaSum 2 = 0 := by rw [← Finset.sum_mul, h1, zero_mul]
  have hz3 : ∑ k ∈ range (K + 1), a1 k * zetaSum 3 = 0 := by rw [← Finset.sum_mul, h1, zero_mul]
  have key : ∀ k ∈ range (K + 1),
      c1 * (-a1 k * (zetaSum 2 - harm 2 k) + -(2 * a2 k) * (zetaSum 3 - harm 3 k)) +
        c2 * (2 * a1 k * (zetaSum 3 - harm 3 k) + 6 * a2 k * (zetaSum 4 - harm 4 k)) =
      (a1 k * (c1 * harm 2 k - 2 * c2 * harm 3 k) + a2 k * (2 * c1 * harm 3 k - 6 * c2 * harm 4 k)) +
        a2 k * (-2 * c1 * zetaSum 3 + 6 * c2 * zetaSum 4) +
        (a1 k * zetaSum 3 * (2 * c2) - a1 k * zetaSum 2 * c1) := by
    intro k _; ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hs : ∑ k ∈ range (K + 1), (a1 k * zetaSum 3 * (2 * c2) - a1 k * zetaSum 2 * c1) = 0 := by
    have : ∑ k ∈ range (K + 1), (a1 k * zetaSum 3 * (2 * c2) - a1 k * zetaSum 2 * c1) =
        (∑ k ∈ range (K + 1), a1 k) * (zetaSum 3 * (2 * c2) - zetaSum 2 * c1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, h1, zero_mul]
  rw [hs]; ring

end Moment

end CatalanCore.Lai.DoublePole
