module

public import CatalanCore.Zeta5.Local.Val
public import CatalanCore.Zeta5.Local.BinomBasis
public import CatalanCore.Zeta5.Local.TauBound
public import CatalanCore.Zeta5.Local.IntPoly
public import CatalanCore.Zeta5.Local.PoleFun
public import CatalanCore.Zeta5.Local.DirectBound
public import CatalanCore.Zeta5.Local.DirectPoly
public import CatalanCore.Zeta5.Local.Pullback
public import CatalanCore.Zeta5.Local.MomentVal
public import CatalanCore.Zeta5.Local.SmallPrime
public import CatalanCore.Zeta5.Local.SmallPrimeRes
public import CatalanCore.Zeta5.Local.SmallPrimeTau
public import CatalanCore.Zeta5.Local.BasisChange
public import CatalanCore.Zeta5.Local.SmallPrimeF
public import CatalanCore.Zeta5.Local.SValuation
public import CatalanCore.Zeta5.Local.GleBridge
public import CatalanCore.Zeta5.Local.Reflect
public import CatalanCore.Zeta5.Local.Shift
public import CatalanCore.Zeta5.Local.Tate
public import CatalanCore.Zeta5.Local.Difference
public import CatalanCore.Zeta5.Local.CrudeMax
public import CatalanCore.Zeta5.Local.Basis

@[expose] public section

/-!
# Content ledger rows ZC01–ZC09 and ZC16: the local arithmetic, in one place

Each ledger row (`CONTENT-LEDGER.md` §A) is restated here as a theorem whose statement is the
ledger statement, proved from the modules of this directory.

| row | theorem here | source module |
|---|---|---|
| ZC01 | `zc01_mu_mono`, `zc01_mu_pole` (the definitions are `Port.Construction`: `μmono`, `poleValue`, `μX`, `G`, `Δ`, `S`, `F`) | Rows, Port |
| ZC02 | `zc02_pullback` (and `tau_pull_poly`) | Pullback |
| ZC03 | `zc03_reflect`, `zc03_shift` (poly forms `tau_comp_neg_sub_one`, `tau_shift`, `Lb_shift`) | Reflect, Shift |
| ZC04 | `zc04_kappa`, `zc04_kappa_int`, `zc04_tate` | Tate |
| ZC05 | `zc05_I3` (finite form), `zc05_direct` (the direct bound, `tauX_direct`) | Tate, DirectPoly |
| ZC06 | `zc06_direct` (the direct bound replacing (I4)–(I5); see NOTES) | DirectPoly |
| ZC07 | `zc07_diff` (I6), `zc07_crude` (I8) | Difference, CrudeMax |
| ZC08 | `zc08_det_basis`, `zc08_int` | Basis |
| ZC09 | `zc09_small_prime` | SmallPrimeF |
| ZC16 | `zc16_vS` | SValuation |
-/

open Finset Polynomial

namespace Apery

/-! ### ZC01: the defining values -/

/-- `μ_X(t^e) = (-1)^e B_{2e+2}(2e+3)(2e+4)(2e+5)/24` (as `P = t^e D_K`, i.e. `R = t^e`). -/
theorem zc01_mu_mono (K e : ℕ) : μX K (D K * X ^ e) = C (μmono e) := by
  unfold μX
  rw [mul_divByMonic_cancel_left _ (D_monic K)]
  have h0 : ∀ j ∈ Icc 1 K, (D K * X ^ e).eval (-(j : ℚ) ^ 2) = 0 := by
    intro j hj
    rw [eval_mul]
    have : (D K).eval (-(j : ℚ) ^ 2) = 0 := by
      unfold D; rw [eval_prod]
      exact Finset.prod_eq_zero hj (by simp)
    rw [this, zero_mul]
  rw [Finset.sum_eq_zero fun j hj => by rw [h0 j hj, zero_div, C_0, zero_mul], add_zero]
  congr 1
  unfold μpoly
  rw [← monomial_one_right_eq_X_pow, Polynomial.sum_monomial_index _ _ (by simp), one_mul]

/-- `μ_X(1/(t+j²)) = j⁴(X - H_j^{(5)}) - 1/4 + 1/(2j)` for `1 ≤ j ≤ K`
(`R = 1/(t+j²)`, i.e. `P = ∏_{i ≠ j}(t + i²)`). -/
theorem zc01_mu_pole {K j : ℕ} (hj : j ∈ Icc 1 K) :
    μX K (∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2))) = poleValue j := by
  set P := ∏ i ∈ (Icc 1 K).erase j, (X + C ((i : ℚ) ^ 2)) with hP
  have hD : D K = (X + C ((j : ℚ) ^ 2)) * P := by
    unfold D; rw [← Finset.mul_prod_erase _ _ hj]
  have hdeg : P.natDegree < K := by
    rw [hP, natDegree_prod_of_monic _ _ fun i _ => monic_X_add_C _]
    rw [Finset.sum_congr rfl fun (i : ℕ) _ => natDegree_X_add_C ((i : ℚ) ^ 2)]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.card_erase_of_mem hj]
    have h12 := Finset.mem_Icc.mp hj
    simp; omega
  have hq : P /ₘ D K = 0 := by
    rw [divByMonic_eq_zero_iff (D_monic K), degree_eq_natDegree (D_monic K).ne_zero, natDegree_D]
    have hP0 : P ≠ 0 := (monic_prod_of_monic _ _ fun i _ => monic_X_add_C _).ne_zero
    rw [degree_eq_natDegree hP0]
    exact_mod_cast hdeg
  have hroot : ∀ i ∈ (Icc 1 K).erase j, P.eval (-(i : ℚ) ^ 2) = 0 := by
    intro i hi
    rw [hP, eval_prod]
    exact Finset.prod_eq_zero hi (by simp)
  have hPj : P.eval (-(j : ℚ) ^ 2) ≠ 0 := by
    rw [hP, eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    simp only [eval_add, eval_X, eval_C]
    intro h
    have h1 : ((i : ℚ) - j) * ((i : ℚ) + j) = 0 := by linarith [h]
    have hi1 := (Finset.mem_Icc.mp (Finset.mem_erase.mp hi).2).1
    have hj1 := (Finset.mem_Icc.mp hj).1
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hij (by exact_mod_cast sub_eq_zero.mp h2)
    · have : (i : ℚ) + j = ((i + j : ℕ) : ℚ) := by push_cast; ring
      rw [this] at h2
      have : i + j = 0 := by exact_mod_cast h2
      omega
  unfold μX
  rw [hq]
  have hpoly : μpoly 0 = 0 := by simp [μpoly]
  rw [hpoly, C_0, zero_add, Finset.sum_eq_single j]
  · have hder : (derivative (D K)).eval (-(j : ℚ) ^ 2) = P.eval (-(j : ℚ) ^ 2) := by
      rw [hD, derivative_mul, derivative_add, derivative_X, derivative_C, add_zero]
      simp only [eval_add, eval_mul, eval_one, eval_X, eval_C]
      ring
    rw [hder, div_self hPj, C_1, one_mul]
  · intro i hi hij
    rw [hroot i (Finset.mem_erase.mpr ⟨hij, hi⟩), zero_div, C_0, zero_mul]
  · intro h; exact absurd hj h

/-! ### ZC02 -/

/-- **ZC02**: `μ_X(P/D_K) = τ_X(x⁵ P(-x²)/D_K(-x²))`, in the numerator form `(-1)^K x⁵ P(-x²)` over
the poles `±1, …, ±K`. -/
theorem zc02_pullback (K : ℕ) (P : ℚ[X]) : μX K P = tauX (pull K P) (PlK K) := μX_eq_tauX K P

/-! ### ZC03 -/

/-- **ZC03, reflection**: `τ_X(g(-1-x)) = -τ_X(g(x))`. -/
theorem zc03_reflect (A : ℚ[X]) (Pl : Finset ℤ) :
    tauX (reflNum Pl A) (Pl.image refl) = -tauX A Pl := tauX_reflect A Pl

/-- **ZC03, shift**: `τ_X(g(x+1) - g(x)) = g⁗(0)/24` for `g` regular at `0`. -/
theorem zc03_shift (A : ℚ[X]) (Pl : Finset ℤ) (h0 : (0 : ℤ) ∉ Pl) :
    tauX (shiftNum Pl A) (Pl ∪ shiftPoles Pl) =
      C (PowerSeries.coeff 4 ((A : PowerSeries ℚ) * ((piPl Pl : ℚ[X]) : PowerSeries ℚ)⁻¹)) :=
  tauX_shift A Pl h0

/-! ### ZC04 -/

theorem zc04_kappa {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (d : ℕ) :
    VG p (tau (X ^ d)) (-1) := VG_tau_X_pow hp5 d

theorem zc04_kappa_int {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {d : ℕ} (hd : d ≤ p + 1) :
    VG p (tau (X ^ d)) 0 := VG_tau_X_pow_int hp5 hd

theorem zc04_tate {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {P : ℚ[X]} (hP : GV p P 0) :
    VG p (tau P) (-1) := VG_tau hp5 hP

/-! ### ZC05, ZC06 -/

/-- **ZC05, (I3)** (finite form). -/
theorem zc05_I3 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (Pl : Finset ℤ)
    (hunit : ∀ r ∈ Pl, ∀ s ∈ Pl, r ≠ s → ¬ (p : ℤ) ∣ r - s) (hdd : ∀ r ∈ Pl, dd r < p)
    (J : ℕ) (U : ℕ → ℚ[X]) (hU : ∀ j < J, GV p (U j) 0) (hU0 : (U 0).natDegree ≤ p + 1)
    (Y : ℚ[X]) (hY : GV p Y 0) :
    GV p ((tauX (∑ j ∈ range J, C ((p : ℚ) ^ j) * U j) Pl).comp Y) 0 :=
  tauX_I3 hp5 Pl hunit hdd J U hU hU0 Y hY

/-- **ZC05/ZC06, direct bound** (replaces the Tate-algebra/distribution argument, (I3)–(I5), with the
same loss `p^{-4}`): for `g = κ ∏_{ζ ∈ Z}(x - ζ) / ∏_{r ∈ Pl}(x - r)`, `v_p^G(τ_X(g)) ≥ min_c (e_c - ℓ_c) - 4`. -/
theorem zc06_direct {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (κ : ℚ) (hκ : VG p κ 0) (Z : Multiset ℤ)
    (Pl : Finset ℤ) (hsep : Sep p Pl) (hH : ∀ r ∈ Pl, dd r < p ^ 2)
    (hdeg : Z.card - Pl.card + 1 < p ^ 2) (β : ℚ)
    (hβ : ∀ c : ZMod p, β ≤ (cnt p Z c : ℚ) - (plc p Pl c).card) :
    GV p (tauX (numOf κ Z) Pl) (β - 4) :=
  tauX_direct hp5 κ hκ Z Pl hsep hH hdeg β hβ

/-! ### ZC07 -/

/-- **ZC07, (I6)**. -/
theorem zc07_diff {p : ℕ} [Fact p.Prime] {A : ℚ[X]} {d : ℕ} (hd : A.natDegree ≤ d)
    (hint : ∀ z : ℤ, VG p (A.eval (z : ℚ)) 0) (x y : ℤ) :
    VG p (A.eval (x : ℚ) - A.eval (y : ℚ))
      ((padicValRat p ((x - y : ℤ) : ℚ) : ℚ) - Nat.log p (max 1 d)) :=
  VG_poly_diff hd hint x y

/-- **ZC07, (I8)**. -/
theorem zc07_crude {p : ℕ} [Fact p.Prime] {K d : ℕ} (hK : 1 ≤ K) (A : ℚ[X]) (hA : A.natDegree ≤ d)
    (hint : ∀ z : ℤ, VG p (A.eval (z : ℚ)) 0) :
    GV p (tauX (C ((K.factorial : ℚ) ^ 2) * A) (PlK K))
      (-6 * (Nat.log p (max (2 * K) (d + 1)) : ℚ) - padicValNat p 24) :=
  crude_tauX_max hK A hA hint

/-! ### ZC08, ZC09 -/

theorem zc08_det_basis (n : ℕ) :
    F n = (Matrix.of fun a b : Fin (37 * n) =>
      C (((40 * n).factorial : ℚ) ^ 2) * μX (40 * n) (fpoly n a * fpoly n b)).det :=
  F_eq_det_basis n

theorem zc08_int (n a : ℕ) (z : ℤ) : ∃ w : ℤ, (fpoly n a).eval (-(z : ℚ) ^ 2) = w :=
  fpoly_eval_int n a z

/-- **ZC09**: at every prime `v_p^G(F_K) ≥ -6h⌊log_p 5K⌋ - h v_p(24)`, `K = 40n`, `h = 37n`. -/
theorem zc09_small_prime {n : ℕ} (hn : 1 ≤ n) (p : ℕ) [Fact p.Prime] :
    GV p (F n) (-(6 * (37 * n : ℕ) * (Nat.log p (5 * (40 * n)) : ℚ) +
      (37 * n : ℕ) * padicValNat p 24)) := by
  have := small_prime_bound (p := p) hn
  rwa [show 5 * (40 * n) = 200 * n by ring]

/-! ### ZC16 -/

theorem zc16_vS {n : ℕ} (hn : 0 < n) {p : ℕ} (hp : p.Prime) :
    padicValRat p (S n) =
      2 * (37 * n : ℤ) * padicValNat p (40 * n).factorial -
        12 * (37 * n : ℤ) * padicValNat p (3 * n).factorial -
        2 * ∑ i ∈ Icc 1 (37 * n - 1), (padicValNat p (2 * i).factorial : ℤ) +
        ((37 * n : ℤ) - 1) * padicValNat p 4 := vS_eq hn hp

end Apery
