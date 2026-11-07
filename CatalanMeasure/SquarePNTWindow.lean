module
public import Mathlib.Data.Nat.GCD.BigOperators
public import CatalanMeasure.PrimeWindow
public import OAI.NumberTheory.Catalan.PrimeLimits.ImportedPNTCoreBridge
@[expose] public section
open Real Filter Chebyshev Polynomial Finset
open scoped Topology BigOperators
namespace CatalanMeasure
/-! Prime windows for nonvanishing under the weaker condition p² ∤ b. -/

theorem prod_prime_squares_dvd (b : ℕ) (s : Finset ℕ)
    (hp : ∀ p ∈ s, p.Prime) (hd : ∀ p ∈ s, p^2 ∣ b) :
    (∏ p ∈ s, p^2) ∣ b := by
  classical
  revert hp hd
  induction s using Finset.induction_on with
  | empty => intro hp hd; simp
  | @insert p s hps ih =>
    intro hp hd
    rw [Finset.prod_insert hps]
    have hcop : Nat.Coprime (p^2) (∏ q ∈ s, q^2) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      have hpq : p ≠ q := by intro he; exact hps (he.symm ▸ hq)
      exact ((Nat.coprime_primes (hp p (mem_insert_self p s))
        (hp q (mem_insert_of_mem hq))).mpr hpq).pow 2 2
    exact hcop.mul_dvd_of_dvd_of_dvd (hd p (mem_insert_self p s))
      (ih (fun q hq => hp q (mem_insert_of_mem hq))
          (fun q hq => hd q (mem_insert_of_mem hq)))

theorem theta_window_square_le_log {b : ℕ} (hb : 0 < b) {X Y : ℝ}
    (hX : 0 ≤ X) (hXY : X ≤ Y)
    (hall : ∀ p : ℕ, p.Prime → X < p → (p : ℝ) ≤ Y → p^2 ∣ b) :
    2 * (θ Y - θ X) ≤ log b := by
  rw [theta_sub_eq_sum_window hXY]
  have hdiv : ∀ p ∈ windowPrimes X Y, p^2 ∣ b := by
    intro p hp
    simp only [windowPrimes, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hlo,hhi⟩,hprime⟩ := hp
    exact hall p hprime ((Nat.floor_lt hX).mp hlo)
      ((Nat.le_floor_iff (by linarith)).mp hhi)
  have hprod := prod_prime_squares_dvd b (windowPrimes X Y)
    (fun p hp => (Finset.mem_filter.mp hp).2) hdiv
  have hprod_le : (∏ p ∈ windowPrimes X Y, p^2) ≤ b := Nat.le_of_dvd hb hprod
  have hpos : ∀ p ∈ windowPrimes X Y, (0 : ℝ) < p := by
    intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.pos
  have hlog : log (∏ p ∈ windowPrimes X Y, (p : ℝ)^2) ≤ log b := by
    apply Real.log_le_log
    · exact Finset.prod_pos (fun p hp => pow_pos (hpos p hp) 2)
    · exact_mod_cast hprod_le
  rw [Real.log_prod (fun p hp => (pow_pos (hpos p hp) 2).ne')] at hlog
  simp_rw [Real.log_pow] at hlog
  simpa only [Nat.cast_ofNat, ← Finset.mul_sum] using hlog

theorem eventually_prime_window_not_square_dvd {ε c : ℝ} (hε : 0 < ε) (hc : 1 < c) :
    ∀ᶠ X : ℝ in atTop, ∀ b : ℕ, 0 < b → log b ≤ 2 * ε * X / c →
      ∃ p : ℕ, p.Prime ∧ X < p ∧ (p : ℝ) ≤ (1 + ε) * X ∧ ¬ p ^ 2 ∣ b := by
  have hc0 : 0 < c := by linarith
  set δ : ℝ := ε * (c - 1) / (2 * c * (2 + ε)) with hδdef
  have hδ0 : 0 < δ := by
    have : 0 < c - 1 := by linarith
    positivity
  have hδ : δ * (2 + ε) = ε * (c - 1) / (2 * c) := by
    rw [hδdef]
    field_simp
  have hθ := OAI.Zeta5.W12.ImportedPNTCoreBridge.theta_ratio_tendsto_one
  have hlo : ∀ᶠ x : ℝ in atTop, 1 - δ < θ x / x := (tendsto_order.mp hθ).1 _ (by linarith)
  have hhi : ∀ᶠ x : ℝ in atTop, θ x / x < 1 + δ := (tendsto_order.mp hθ).2 _ (by linarith)
  have hscale : Tendsto (fun X : ℝ => (1 + ε) * X) atTop atTop :=
    tendsto_id.const_mul_atTop (by linarith)
  filter_upwards [hhi, hscale.eventually hlo, eventually_gt_atTop (0 : ℝ)] with X hX1 hX2 hX0
  intro b hb hlogb
  by_contra hcon
  push Not at hcon
  have hY : X ≤ (1 + ε) * X := by nlinarith
  have hw := theta_window_square_le_log hb hX0.le hY hcon
  have h1 : (1 - δ) * ((1 + ε) * X) < θ ((1 + ε) * X) :=
    (lt_div_iff₀ (by positivity)).mp hX2
  have h2 : θ X < (1 + δ) * X := (div_lt_iff₀ hX0).mp hX1
  have hδX : δ * (2 + ε) * X = ε * (c - 1) / (2 * c) * X := by rw [hδ]
  have hkey : ε * X / c ≤ ε * X - ε * (c - 1) / (2 * c) * X := by
    have hεX : 0 < ε * X := mul_pos hε hX0
    have : ε * X - ε * (c - 1) / (2 * c) * X - ε * X / c = ε * X * (c - 1) / (2 * c) := by
      field_simp
      ring
    have h3 : 0 ≤ ε * X * (c - 1) / (2 * c) := by
      have : 0 ≤ c - 1 := by linarith
      positivity
    linarith
  have hdiff : ε * X - δ * (2 + ε) * X < θ ((1 + ε) * X) - θ X := by
    nlinarith [h1, h2]
  have hgap : ε * X / c < θ ((1 + ε) * X) - θ X := by
    apply lt_of_le_of_lt _ hdiff
    rw [hδX]
    exact hkey
  have heq : 2 * ε * X / c = 2 * (ε * X / c) := by ring
  rw [heq] at hlogb
  linarith

end CatalanMeasure
