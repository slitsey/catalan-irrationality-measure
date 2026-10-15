module

public import CatalanMeasure.RecycledPNTWindow

@[expose] public section

/-!
# Recycling with a real, eventually valid degree coefficient

Integer evaluation uses the actual natural degree. The real degree bound
is applied only after proving the recycled logarithmic base is nonnegative.
The previously published natural-degree criterion is unchanged.
-/

open Real Filter Chebyshev Polynomial Finset
open scoped Topology BigOperators

namespace CatalanMeasure

/-- Real-degree form of the recycled criterion. Only the selected large
    prime indices need the degree estimate. -/
theorem irrationality_measure_of_recycled_polynomials_real_degree_square_pnt
    (G d : ℝ) {η ρ κ δ : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hκ : 2 < κ) (hδ : 0 < δ)
    (hwindow : 1 < 2 * (1 - δ * (2 * κ - 1)))
    (hlinear : η < 2 * (d : ℝ))
    (hpay : (d : ℝ) + 4 * d * δ * κ < η * κ)
    (Q : ℕ → ℤ[X]) (P₀ : ℕ)
    (hdeg : ∀ p, P₀ ≤ p → p.Prime → ((Q p).natDegree : ℝ) ≤ d * p)
    (hnz : ∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
      aeval ((a : ℝ) / b) (Q p) ≠ 0)
    (hcoeff : ∀ p, P₀ ≤ p → p.Prime → ∀ q : ℕ,
      q.Prime → p < q → q ≤ 2 * p →
      ∀ i ≤ (Q p).natDegree, (q : ℤ) ^ (2 * i) ∣ (Q p).coeff i)
    (hsmall : ∀ p, P₀ ≤ p → p.Prime → ∀ x : ℝ,
      |x - G| ≤ exp (-(ρ * p)) → |aeval x (Q p)| ≤ exp (-(η * (p : ℝ) ^ 2))) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(ρ * κ)) < |G - a / b| := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hκ0 : 0 < κ := by linarith
  have hκ1 : 0 < κ - 1 := by linarith
  have hθ := OAI.Zeta5.W12.ImportedPNTCoreBridge.theta_ratio_tendsto_one
  have hlo : ∀ᶠ x : ℝ in atTop, (1 - δ) * x ≤ θ x := by
    filter_upwards [(tendsto_order.mp hθ).1 (1 - δ) (by linarith),
      eventually_gt_atTop (0 : ℝ)] with x hx hx0
    exact ((le_div_iff₀ hx0).mp hx.le)
  have hhi : ∀ᶠ x : ℝ in atTop, θ x ≤ (1 + δ) * x := by
    filter_upwards [(tendsto_order.mp hθ).2 (1 + δ) (by linarith),
      eventually_gt_atTop (0 : ℝ)] with x hx hx0
    exact ((div_le_iff₀ hx0).mp hx.le)
  obtain ⟨X₀, htheta⟩ := eventually_atTop.mp (hlo.and hhi)
  have hlogb : Tendsto (fun b : ℕ => (κ - 1) * log b) atTop atTop :=
    Tendsto.const_mul_atTop hκ1 (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hbig := hlogb.eventually (eventually_ge_atTop (max X₀ (max (P₀ : ℝ) 1)))
  filter_upwards [hbig, eventually_ge_atTop 2] with b hb hb2 a
  by_contra hcon
  push Not at hcon
  have hb0 : 0 < b := by omega
  have hbR : (1 : ℝ) < b := by exact_mod_cast (show 1 < b by omega)
  have hb0R : (0 : ℝ) < b := by linarith
  have hL : 0 < log (b : ℝ) := Real.log_pos hbR
  let L : ℝ := log b
  let U : ℝ := κ * L
  let V : ℝ := (κ - 1) * L
  have hV0 : 0 ≤ V := by dsimp [V, L]; positivity
  have hVU : V ≤ U := by dsimp [V, U]; nlinarith
  have hXV : X₀ ≤ V := le_trans (le_max_left _ _) hb
  have hPV : (P₀ : ℝ) ≤ V := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hb)
  have hV1 : (1 : ℝ) ≤ V := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hb)
  have hthetaV := htheta V hXV
  have hthetaU := htheta U (le_trans hXV hVU)
  have hgap : log b < 2 * (θ U - θ V) := by
    have hw := mul_pos (sub_pos.mpr hwindow) hL
    dsimp [U, V] at hthetaU hthetaV
    change L < 2 * (θ U - θ V)
    nlinarith only [hthetaU.1, hthetaV.2, hw]
  obtain ⟨p, hp, hpV, hpU, hpb, hafter⟩ :=
    exists_largest_prime_window_not_square_dvd hb0 hV0 hVU hgap
  have hP₀ : P₀ ≤ p := by exact_mod_cast (le_trans hPV hpV.le)
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpθ := htheta p (le_trans hXV hpV.le)
  have hpU0 : (0 : ℝ) ≤ p := hp0R.le
  let S := windowPrimes (p : ℝ) U
  let B : ℕ := ∏ q ∈ S, q ^ 2
  have hSprime : ∀ q ∈ S, q.Prime := by
    intro q hq
    exact ((mem_windowPrimes_iff_of_nonneg hpU0 hpU).mp hq).1
  have hSdiv : ∀ q ∈ S, q ^ 2 ∣ b := by
    intro q hq
    obtain ⟨hqprime, hpq, hqU⟩ := (mem_windowPrimes_iff_of_nonneg hpU0 hpU).mp hq
    exact hafter q hqprime hpq hqU
  have hScoeff : ∀ q ∈ S, ∀ i ≤ (Q p).natDegree,
      (q : ℤ) ^ (2 * i) ∣ (Q p).coeff i := by
    intro q hq
    obtain ⟨hqprime, hpq, hqU⟩ := (mem_windowPrimes_iff_of_nonneg hpU0 hpU).mp hq
    have hpqN : p < q := by exact_mod_cast hpq
    have hq2p : q ≤ 2 * p := by
      have hscale : U < 2 * V := by
        dsimp [U, V]
        nlinarith only [mul_pos (sub_pos.mpr hκ) hL]
      have : (q : ℝ) ≤ 2 * p := by linarith
      exact_mod_cast this
    exact hcoeff p hP₀ hp q hqprime hpqN hq2p
  have hBdiv : B ∣ b := prime_square_prod_dvd S b hSprime hSdiv
  have hBpos : 0 < B := Nat.pos_of_dvd_of_pos hBdiv hb0
  have hB0R : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hlogB : log (B : ℝ) = 2 * (θ U - θ p) :=
    log_prime_square_window_product hpU0 hpU
  have hclose : |(a : ℝ) / b - G| ≤ exp (-(ρ * p)) := by
    rw [abs_sub_comm]
    refine hcon.trans ?_
    rw [Real.rpow_def_of_pos hb0R]
    apply Real.exp_le_exp.mpr
    have hρp := mul_le_mul_of_nonneg_left hpU hρ.le
    dsimp [U, L] at hρp
    nlinarith only [hρp]
  have hsmallQ := hsmall p hP₀ hp _ hclose
  have hne := hnz p hP₀ hp a b hb0 hpb
  have h1 := one_le_prime_square_prod_recycled_pow_mul_abs_aeval
    (Q p) (le_refl _) a hb0 S hSprime hSdiv hScoeff hne
  have hpow : ((b : ℝ) / B) ^ (Q p).natDegree =
      exp (((Q p).natDegree : ℝ) * (L - 2 * (θ U - θ p))) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (div_pos hb0R hB0R),
      Real.log_div hb0R.ne' hB0R.ne', hlogB]
    congr 1
    ring
  have hBleb : (B : ℝ) ≤ b := by
    exact_mod_cast Nat.le_of_dvd hb0 hBdiv
  have hbase : 0 ≤ L - 2 * (θ U - θ p) := by
    have hlog := Real.log_le_log hB0R hBleb
    rw [hlogB] at hlog
    change 0 ≤ log (b : ℝ) - 2 * (θ U - θ p)
    linarith only [hlog]
  have hdegree_cost : ((Q p).natDegree : ℝ) * (L - 2 * (θ U - θ p)) ≤
      d * p * (L - 2 * (θ U - θ p)) :=
    mul_le_mul_of_nonneg_right (hdeg p hP₀ hp) hbase
  have he : 1 ≤ exp (d * p * (L - 2 * (θ U - θ p)) - η * (p : ℝ)^2) := by
    calc
      (1 : ℝ) ≤ ((b : ℝ) / B) ^ (Q p).natDegree *
          |aeval ((a : ℝ) / b) (Q p)| := h1
      _ ≤ exp (d * p * (L - 2 * (θ U - θ p))) *
          |aeval ((a : ℝ) / b) (Q p)| := by
        rw [hpow]
        exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr hdegree_cost) (abs_nonneg _)
      _ ≤ exp (d * p * (L - 2 * (θ U - θ p))) *
          exp (-(η * (p : ℝ)^2)) :=
        mul_le_mul_of_nonneg_left hsmallQ (exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; rfl
  have hexp := Real.one_le_exp_iff.mp he
  have hpkey : η * p ≤ (d : ℝ) * (L - 2 * (θ U - θ p)) := by
    by_contra hh
    have hh' : (d : ℝ) * (L - 2 * (θ U - θ p)) - η * p < 0 := by linarith
    have := mul_neg_of_pos_of_neg hp0R hh'
    nlinarith only [hexp, this]
  have hT : U - p - 2 * δ * U ≤ θ U - θ p := by
    have hδp := mul_le_mul_of_nonneg_left hpU hδ.le
    nlinarith only [hthetaU.1, hpθ.2, hδp]
  have hdT := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ 2 * d)
  have htop := mul_le_mul_of_nonneg_left hpU (by linarith : (0 : ℝ) ≤ 2 * d - η)
  have hpaid := mul_pos (sub_pos.mpr hpay) hL
  dsimp [U, L] at hdT htop hpkey
  nlinarith only [hdT, htop, hpkey, hpaid]

/-- A bounded additive degree error is negligible in the real coefficient.
    In particular this pays the rounding term in floor-order derivative families. -/
theorem asymptotic_real_degree_bound_of_eventual_affine (Q : ℕ → ℤ[X]) (d c : ℝ)
    (hdeg : ∀ᶠ p : ℕ in atTop, ((Q p).natDegree : ℝ) ≤ d * p + c) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ p : ℕ in atTop, ((Q p).natDegree : ℝ) ≤ (d + ε) * p := by
  intro ε hε
  have ht : Tendsto (fun p : ℕ => ε * (p : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hε tendsto_natCast_atTop_atTop
  filter_upwards [hdeg, ht.eventually (eventually_ge_atTop c)] with p hp hpc
  nlinarith only [hp, hpc]

/-- An eventual real degree bound can have its own cutoff, independently
    of the nonvanishing, coefficient and interval hypotheses. -/
theorem irrationality_measure_of_recycled_polynomials_eventual_real_degree_square_pnt
    (G d : ℝ) {η ρ κ δ : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hκ : 2 < κ) (hδ : 0 < δ)
    (hwindow : 1 < 2 * (1 - δ * (2 * κ - 1)))
    (hlinear : η < 2 * d) (hpay : d + 4 * d * δ * κ < η * κ)
    (Q : ℕ → ℤ[X]) (P₀ : ℕ)
    (hdeg : ∀ᶠ p : ℕ in atTop, ((Q p).natDegree : ℝ) ≤ d * p)
    (hnz : ∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
      aeval ((a : ℝ) / b) (Q p) ≠ 0)
    (hcoeff : ∀ p, P₀ ≤ p → p.Prime → ∀ q : ℕ,
      q.Prime → p < q → q ≤ 2 * p →
      ∀ i ≤ (Q p).natDegree, (q : ℤ) ^ (2 * i) ∣ (Q p).coeff i)
    (hsmall : ∀ p, P₀ ≤ p → p.Prime → ∀ x : ℝ,
      |x - G| ≤ exp (-(ρ * p)) → |aeval x (Q p)| ≤ exp (-(η * (p : ℝ) ^ 2))) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(ρ * κ)) < |G - a / b| := by
  obtain ⟨P₁, hP₁⟩ := eventually_atTop.mp hdeg
  apply irrationality_measure_of_recycled_polynomials_real_degree_square_pnt
    G d hη hρ hκ hδ hwindow hlinear hpay Q (max P₀ P₁)
  · intro p hp _
    exact hP₁ p (le_trans (le_max_right _ _) hp)
  · intro p hp hprime
    exact hnz p (le_trans (le_max_left _ _) hp) hprime
  · intro p hp hprime
    exact hcoeff p (le_trans (le_max_left _ _) hp) hprime
  · intro p hp hprime
    exact hsmall p (le_trans (le_max_left _ _) hp) hprime

/-- Asymptotic degree coefficient: bounded additive rounding losses, or
    any sublinear degree error, require no rounding of `d` to a natural. -/
theorem irrationality_measure_of_recycled_polynomials_asymptotic_real_degree_square_pnt
    (G d : ℝ) {η ρ κ δ : ℝ}
    (hη : 0 < η) (hρ : 0 < ρ) (hκ : 2 < κ) (hδ : 0 < δ)
    (hwindow : 1 < 2 * (1 - δ * (2 * κ - 1)))
    (hlinear : η < 2 * d) (hpay : d + 4 * d * δ * κ < η * κ)
    (Q : ℕ → ℤ[X]) (P₀ : ℕ)
    (hdeg : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ p : ℕ in atTop, ((Q p).natDegree : ℝ) ≤ (d + ε) * p)
    (hnz : ∀ p, P₀ ≤ p → p.Prime → ∀ (a : ℤ) (b : ℕ), 0 < b → ¬ p ^ 2 ∣ b →
      aeval ((a : ℝ) / b) (Q p) ≠ 0)
    (hcoeff : ∀ p, P₀ ≤ p → p.Prime → ∀ q : ℕ,
      q.Prime → p < q → q ≤ 2 * p →
      ∀ i ≤ (Q p).natDegree, (q : ℤ) ^ (2 * i) ∣ (Q p).coeff i)
    (hsmall : ∀ p, P₀ ≤ p → p.Prime → ∀ x : ℝ,
      |x - G| ≤ exp (-(ρ * p)) → |aeval x (Q p)| ≤ exp (-(η * (p : ℝ) ^ 2))) :
    ∀ᶠ b : ℕ in atTop, ∀ a : ℤ,
      (b : ℝ) ^ (-(ρ * κ)) < |G - a / b| := by
  have hκ0 : 0 < κ := by linarith
  let A : ℝ := 1 + 4 * δ * κ
  have hA : 0 < A := by dsimp [A]; positivity
  let ε : ℝ := (η * κ - (d + 4 * d * δ * κ)) / (2 * A)
  have hε : 0 < ε := div_pos (sub_pos.mpr hpay) (by positivity)
  have hεA : ε * A = (η * κ - (d + 4 * d * δ * κ)) / 2 := by
    dsimp [ε]
    field_simp
  have hpay' : (d + ε) + 4 * (d + ε) * δ * κ < η * κ := by
    calc
      _ = (d + 4 * d * δ * κ) + ε * A := by dsimp [A]; ring
      _ = (d + 4 * d * δ * κ) + (η * κ - (d + 4 * d * δ * κ)) / 2 := by rw [hεA]
      _ < η * κ := by linarith only [hpay]
  apply irrationality_measure_of_recycled_polynomials_eventual_real_degree_square_pnt
    G (d + ε) hη hρ hκ hδ hwindow (by linarith only [hlinear, hε]) hpay'
    Q P₀ (hdeg ε hε) hnz hcoeff hsmall

end CatalanMeasure
