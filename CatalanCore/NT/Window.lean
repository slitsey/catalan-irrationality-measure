module

public import CatalanCore.NT.Interval
public import CatalanCore.Frame.Spec
public import CatalanCore.Measure.Sep

@[expose] public section

/-!
# Prime windows in a residue class avoiding bad primes (design WP5, `exists_prime_window`)

`PrimeRule` (frozen in `Frame/Spec.lean`) documents `weight` as a bound on the product of the
bad primes, but carries no field for it.  The bound is therefore a hypothesis here,
`PrimeRule.BadBound`, and `badBound_of_pow_dvd` discharges it for the two rules in use
(`Bad l q := l ∣ q`, weight `1`; `Bad l q := l² ∣ q ∧ …`, weight `1/2`).
-/

open Filter Topology

namespace CatalanCore

/-- The product of any set of distinct bad primes for `q` is at most `q ^ weight`. -/
def PrimeRule.BadBound (R : PrimeRule) : Prop :=
  ∀ q : ℕ, 0 < q → ∀ S : Finset ℕ, (∀ l ∈ S, l.Prime ∧ R.Bad l q) →
    ((∏ l ∈ S, l : ℕ) : ℝ) ≤ (q : ℝ) ^ (R.weight : ℝ)

/-- If `Bad l q` forces `l ^ k ∣ q` and `weight ≥ 1/k`, the bad-prime product bound holds. -/
theorem PrimeRule.badBound_of_pow_dvd (R : PrimeRule) {k : ℕ} (hk : 0 < k)
    (hBad : ∀ l q, R.Bad l q → l ^ k ∣ q) (hw : (1 : ℚ) / k ≤ R.weight) : R.BadBound := by
  intro q hq S hS
  have hdvd : ∏ l ∈ S, l ^ k ∣ q := by
    classical
    revert hS
    induction S using Finset.induction_on with
    | empty => intro _; simp
    | @insert p s hps ih =>
      intro hS'
      rw [Finset.prod_insert hps]
      have hcop : Nat.Coprime (p ^ k) (∏ x ∈ s, x ^ k) := by
        apply Nat.coprime_prod_right_iff.mpr
        intro x hx
        have hpx : p ≠ x := by intro he; exact hps (he.symm ▸ hx)
        exact ((Nat.coprime_primes (hS' p (Finset.mem_insert_self p s)).1
          (hS' x (Finset.mem_insert_of_mem hx)).1).mpr hpx).pow k k
      exact hcop.mul_dvd_of_dvd_of_dvd (hBad p q (hS' p (Finset.mem_insert_self p s)).2)
        (ih (fun x hx ↦ hS' x (Finset.mem_insert_of_mem hx)))
  have hle : (∏ l ∈ S, l) ^ k ≤ q := by
    rw [← Finset.prod_pow]; exact Nat.le_of_dvd hq hdvd
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hP : 0 ≤ ((∏ l ∈ S, l : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : (((∏ l ∈ S, l : ℕ) : ℝ)) ^ k ≤ q := by exact_mod_cast hle
  have h2 : ((∏ l ∈ S, l : ℕ) : ℝ) ≤ (q : ℝ) ^ ((1 : ℝ) / k) := by
    have := Real.rpow_le_rpow (by positivity) h1 (by positivity : (0 : ℝ) ≤ 1 / k)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hP, mul_one_div_cancel hkR.ne',
      Real.rpow_one] at this
  refine h2.trans (Real.rpow_le_rpow_of_exponent_le hq1 ?_)
  have h3 : ((1 / k : ℚ) : ℝ) ≤ (R.weight : ℝ) := Rat.cast_le.mpr hw
  push_cast at h3
  exact h3

end CatalanCore

namespace CatalanCore.NT

open Chebyshev in
/-- **Prime window in a union of classes** (G3).  `S` is a nonempty set of unit classes mod `R.m`
(for instance one class with some sub-classes removed to dodge a bad residue).  For `a > 0` and
`a + weight · φ(m) / |S| < b`, every large `q` has a prime `l` with `(l : ZMod m) ∈ S` in
`(a log q, b log q]` that is not bad for `q`.  The single-class `exists_prime_window` is the case
`S = {R.r}`. -/
theorem exists_prime_window_set (R : PrimeRule) [NeZero R.m] (hB : R.BadBound)
    (S : Finset (ZMod R.m)) (hS : ∀ c ∈ S, IsUnit c) (hne : S.Nonempty) {a b : ℝ}
    (ha : 0 < a) (hab : a + R.weight * (Nat.totient R.m : ℝ) / (S.card : ℝ) < b) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∃ l : ℕ, l.Prime ∧ (l : ZMod R.m) ∈ S ∧
      a * Real.log q < l ∧ (l : ℝ) ≤ b * Real.log q ∧ ¬ R.Bad l q := by
  set w : ℝ := (R.weight : ℝ) with hwdef
  set φ : ℝ := (Nat.totient R.m : ℝ) with hφdef
  set n : ℝ := (S.card : ℝ) with hndef
  have hφ : 0 < φ := by
    rw [hφdef]; exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne R.m))
  have hn : 0 < n := by rw [hndef]; exact_mod_cast hne.card_pos
  -- the weight is nonnegative (empty bad set at `q = 2`)
  have hw0 : 0 ≤ w := by
    by_contra hneg
    push Not at hneg
    have h : (1 : ℝ) ≤ (2 : ℝ) ^ w := by simpa using hB 2 (by norm_num) ∅ (by simp)
    have : (2 : ℝ) ^ w < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hneg
    linarith
  have hwφ : w * φ < (b - a) * n := by
    have : w * φ / n < b - a := by linarith
    rwa [div_lt_iff₀ hn] at this
  have hab' : a ≤ b := by
    have : 0 ≤ w * φ := mul_nonneg hw0 hφ.le
    by_contra h
    push Not at h
    nlinarith
  set δ : ℝ := (b - a) * n / φ - w with hδdef
  have hδ : 0 < δ := by
    rw [hδdef, sub_pos, lt_div_iff₀ hφ]; linarith
  have hb : 0 < b := by linarith
  set ε : ℝ := δ / (2 * n * (a + b)) with hεdef
  have hε : 0 < ε := by rw [hεdef]; positivity
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    ((Filter.eventually_all_finset S).2 fun c hc ↦
      (thetaClass_lower (hS c hc) hε).and (thetaClass_upper (hS c hc) hε))
  refine ⟨⌈Real.exp (max (X₀ / a) 1)⌉₊, fun q hq ↦ ?_⟩
  have hqR : Real.exp (max (X₀ / a) 1) ≤ q := (Nat.ceil_le.mp hq)
  have hL : max (X₀ / a) 1 ≤ Real.log q := by
    have hpos : 0 < Real.exp (max (X₀ / a) 1) := Real.exp_pos _
    have := Real.log_le_log hpos hqR
    rwa [Real.log_exp] at this
  have hL1 : 1 ≤ Real.log q := le_trans (le_max_right _ _) hL
  have hL0 : 0 < Real.log q := by linarith
  have hq0 : 0 < q := by
    by_contra h0
    have : q = 0 := by omega
    subst this
    simp at hL0
  set L : ℝ := Real.log q with hLdef
  have haL : X₀ ≤ a * L := by
    have := le_trans (le_max_left _ _) hL
    rwa [div_le_iff₀ ha, mul_comm] at this
  have hbL : X₀ ≤ b * L := le_trans haL (mul_le_mul_of_nonneg_right hab' hL0.le)
  by_contra hcon
  push Not at hcon
  have haL0 : 0 ≤ a * L := by positivity
  set F : Finset ℕ := (Finset.Ioc ⌊a * L⌋₊ ⌊b * L⌋₊).filter
    (fun m : ℕ ↦ m.Prime ∧ (m : ZMod R.m) ∈ S) with hF
  have hSbad : ∀ l ∈ F, l.Prime ∧ R.Bad l q := by
    intro l hl
    rw [hF, Finset.mem_filter, Finset.mem_Ioc] at hl
    obtain ⟨⟨h1, h2⟩, hp, hlr⟩ := hl
    have h1' : a * L < l := (Nat.floor_lt haL0).mp h1
    have h2' : (l : ℝ) ≤ b * L := (Nat.le_floor_iff (by positivity)).mp h2
    refine ⟨hp, ?_⟩
    by_contra hnb
    exact absurd (hcon l hp hlr h1' h2') (by simpa using hnb)
  have hprod := hB q hq0 F hSbad
  have hprodpos : (0 : ℝ) < ((∏ l ∈ F, l : ℕ) : ℝ) := by
    rw [Nat.cast_prod]
    refine Finset.prod_pos fun l hl ↦ ?_
    exact_mod_cast (hSbad l hl).1.pos
  have hlog := Real.log_le_log hprodpos hprod
  rw [Real.log_rpow (by exact_mod_cast hq0), Nat.cast_prod,
    Real.log_prod (fun l hl ↦ by exact_mod_cast (hSbad l hl).1.ne_zero)] at hlog
  -- the window sum is the sum of the class increments
  have hle : ⌊a * L⌋₊ ≤ ⌊b * L⌋₊ := Nat.floor_le_floor (mul_le_mul_of_nonneg_right hab' hL0.le)
  have hsub : ∑ c ∈ S, (thetaClass R.m c (b * L) - thetaClass R.m c (a * L)) =
      ∑ l ∈ F, Real.log l := by
    rw [hF, ← Finset.sum_fiberwise_of_maps_to (s := (Finset.Ioc ⌊a * L⌋₊ ⌊b * L⌋₊).filter
      (fun m : ℕ ↦ m.Prime ∧ (m : ZMod R.m) ∈ S)) (t := S) (g := fun m : ℕ ↦ (m : ZMod R.m))
      (fun m hm ↦ (Finset.mem_filter.1 hm).2.2)]
    refine Finset.sum_congr rfl fun c hc ↦ ?_
    have := thetaClassN_sub R.m c hle
    unfold thetaClass
    rw [this]
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext m
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2, h3 ▸ hc⟩, h3⟩
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩; exact ⟨h1, h2, h4⟩
  have hlow : ∀ c ∈ S, (φ⁻¹ - ε) * (b * L) ≤ thetaClass R.m c (b * L) := fun c hc ↦
    (hX₀ (b * L) hbL c hc).1
  have hup : ∀ c ∈ S, thetaClass R.m c (a * L) ≤ (φ⁻¹ + ε) * (a * L) := fun c hc ↦
    (hX₀ (a * L) haL c hc).2
  have hsum : n * ((φ⁻¹ - ε) * (b * L) - (φ⁻¹ + ε) * (a * L)) ≤
      ∑ c ∈ S, (thetaClass R.m c (b * L) - thetaClass R.m c (a * L)) := by
    have : ∑ _c ∈ S, ((φ⁻¹ - ε) * (b * L) - (φ⁻¹ + ε) * (a * L)) ≤
        ∑ c ∈ S, (thetaClass R.m c (b * L) - thetaClass R.m c (a * L)) :=
      Finset.sum_le_sum fun c hc ↦ sub_le_sub (hlow c hc) (hup c hc)
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have e1 : n * ε * (a + b) = δ / 2 := by
    rw [hεdef]; have : 0 < a + b := by linarith
    field_simp
  have e4 : δ * L = φ⁻¹ * (b - a) * n * L - w * L := by
    rw [hδdef]; field_simp
  have hδL : 0 < δ * L := mul_pos hδ hL0
  have e5 : n * ((φ⁻¹ - ε) * (b * L) - (φ⁻¹ + ε) * (a * L)) =
      φ⁻¹ * (b - a) * n * L - n * ε * (a + b) * L := by ring
  rw [e1] at e5
  nlinarith

/-- **Prime window.**  For `a > 0` and `a + weight · φ(m) < b`, every large `q` has a prime
`l ≡ r (mod m)` in `(a log q, b log q]` that is not bad for `q`.  The case `S = {R.r}` of
`exists_prime_window_set`. -/
theorem exists_prime_window (R : PrimeRule) [NeZero R.m] (hB : R.BadBound) {a b : ℝ}
    (ha : 0 < a) (hab : a + R.weight * (Nat.totient R.m : ℝ) < b) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∃ l : ℕ, l.Prime ∧ (l : ZMod R.m) = R.r ∧
      a * Real.log q < l ∧ (l : ℝ) ≤ b * Real.log q ∧ ¬ R.Bad l q := by
  obtain ⟨q₀, H⟩ := exists_prime_window_set R hB {R.r} (by simpa using R.hr) (by simp) ha
    (by simpa using hab)
  exact ⟨q₀, fun q hq ↦ by simpa using H q hq⟩

end CatalanCore.NT

namespace CatalanCore

/-- `exists_prime_window` in the form WP6 consumes: `R.HasWindow`. -/
theorem PrimeRule.hasWindow (R : PrimeRule) [NeZero R.m] (hB : R.BadBound) : R.HasWindow := by
  intro a b ha hab
  refine NT.exists_prime_window R hB ha ?_
  have : ((R.s : ℚ) : ℝ) = (R.weight : ℝ) * (Nat.totient R.m : ℝ) := by
    simp [PrimeRule.s]
  linarith

end CatalanCore
