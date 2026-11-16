module

public import Mathlib.Data.Nat.Prime.Factorial
public import CatalanCore.Zeta5.Frames.Outer
public import CatalanCore.Zeta5.Local.Rows

@[expose] public section

/-! Assembly pattern ported from mo271/Zeta5 (Apache-2.0), commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
Apery/Norm.lean (Moritz Firsching): `rat_int_of_VG`, `padicValRat_mN`, `integral_mN`, `vSK_big`;
changes: local exponents are the ledger ones (I19): small primes (ZC09), inner (ZC12), outer
(ZC14, I17), `p > K` (I18); signed `L_p`, parameter `M`. -/

/-!
# ZC15: the signed normaliser `m_{K,M}` (INTEGRALITY (I19))

For `M ≥ 40`, `K = 40 n ≥ 200 M²`: `m n = ∏_{p ≤ 2h} p^{-L_p}`, `0 < m n`, `m n • F_K ∈ ℤ[X]`, and
`log m n = -∑_p L_p log p` (`log_mKM`), with `L_p = v_p(S_K) + γ_p` (signed).
-/

open Finset Polynomial

namespace Apery

/-- `v_p(S_K)`. -/
noncomputable def vSK (n p : ℕ) : ℤ := padicValRat p (S n)

/-- The small-prime exponent `-6h⌊log_p 5K⌋ - h v_p(24)`. -/
noncomputable def LsmallN (n p : ℕ) : ℤ :=
  -(6 * ((37 * n : ℕ) : ℤ) * (Nat.log p (200 * n) : ℤ) + ((37 * n : ℕ) : ℤ) * (padicValNat p 24 : ℤ))

open Classical in
/-- The inner exponent `γ_p^in = 2 ∑ w` (an integer, `inner_gamma_int`), reserve `L₀ = 4M + 10`. -/
noncomputable def gammaIn (M n p : ℕ) : ℤ :=
  if H : InnerHyp p n M (4 * M + 10) then
    ⌊2 * ∑ s : (Σ a : Fin (p / 2 + 1), Fin (innerL p n (4 * M + 10) a)),
      winner H.m_pos (innerL p n (4 * M + 10)) (Bse p (40 * n) (3 * n)) s⌋
  else 0

open Classical in
/-- The local exponent `L_p` of (I19). -/
noncomputable def LpKM (M n p : ℕ) : ℤ :=
  if p * M ≤ 40 * n then LsmallN n p
  else if 3 * p ≤ 40 * n then vSK n p + gammaIn M n p
  else if p ≤ 40 * n then vSK n p + gammaOut n p
  else vSK n p

/-- **The normaliser** `m_{K,M} = ∏_{p ≤ 2h} p^{-L_p}`. -/
noncomputable def mKM (M n : ℕ) : ℚ :=
  ∏ p ∈ (range (2 * (37 * n) + 1)).filter Nat.Prime, (p : ℚ) ^ (-LpKM M n p)

lemma mKM_pos (M n : ℕ) : 0 < mKM M n := by
  unfold mKM
  apply Finset.prod_pos
  intro p hp
  have : 0 < p := (Finset.mem_filter.mp hp).2.pos
  exact zpow_pos (by exact_mod_cast this) _

/-- **Signed cost.** `log m = -∑_p L_p log p`. -/
lemma log_mKM (M n : ℕ) :
    Real.log (mKM M n) = -∑ p ∈ (range (2 * (37 * n) + 1)).filter Nat.Prime,
      (LpKM M n p : ℝ) * Real.log p := by
  unfold mKM
  rw [Rat.cast_prod]
  simp only [Rat.cast_zpow, Rat.cast_natCast]
  rw [Real.log_prod (fun p hp => by
    have : 0 < p := (Finset.mem_filter.mp hp).2.pos
    exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr this.ne'))]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Real.log_zpow]; push_cast; ring

variable {p : ℕ} [hp : Fact p.Prime]

lemma GV_F_of_Δ {n : ℕ} {r : ℚ} (h : GV p (Δ n) r) : GV p (F n) ((vSK n p : ℚ) + r) := by
  unfold F
  have hS : VG p (S n) (vSK n p) := by
    unfold vSK; right; exact le_refl _
  exact GV.C_mul hS h

/-- Every local exponent is valid. -/
theorem GV_F_LpKM {M n : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ 40 * n) :
    GV p (F n) (LpKM M n p : ℚ) := by
  have hn : 1 ≤ n := by nlinarith
  unfold LpKM
  by_cases h1 : p * M ≤ 40 * n
  · rw [if_pos h1]
    refine (zc09_small_prime hn p).mono (le_of_eq ?_)
    simp only [LsmallN, Int.cast_neg, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat,
      show 5 * (40 * n) = 200 * n by ring]
  rw [if_neg h1]
  by_cases h2 : 3 * p ≤ 40 * n
  · rw [if_pos h2]
    have H : InnerHyp p n M (4 * M + 10) :=
      ⟨hp.out, hM, hK, by omega, h2, by omega, by omega⟩
    have hΔ := H.zc12_inner
    have := GV_F_of_Δ hΔ
    refine this.mono ?_
    unfold gammaIn
    rw [dif_pos H]
    push_cast
    have := Int.floor_le (2 * ∑ s : (Σ a : Fin (p / 2 + 1), Fin (innerL p n (4 * M + 10) a)),
      winner H.m_pos (innerL p n (4 * M + 10)) (Bse p (40 * n) (3 * n)) s)
    linarith
  rw [if_neg h2]
  by_cases h3 : p ≤ 40 * n
  · rw [if_pos h3]
    have := GV_F_of_Δ (zc14_outer (p := p) hn (by omega) h3)
    push_cast
    exact this
  · rw [if_neg h3]
    have := GV_F_of_Δ (zc14_big (p := p) hn (by omega))
    simpa using this

lemma padicValNat_factorial_lt' {k : ℕ} (hk : k < p) : padicValNat p k.factorial = 0 :=
  padicValNat.eq_zero_of_not_dvd (fun h => by
    have := (Nat.Prime.dvd_factorial hp.out).mp h; omega)

lemma vSK_big {n : ℕ} (hn : 1 ≤ n) (hbig : 2 * (37 * n) < p) : vSK n p = 0 := by
  have h := vS_eq (by omega : 0 < n) hp.out
  unfold vSK
  rw [h, padicValNat_factorial_lt' (by omega), padicValNat_factorial_lt' (by omega)]
  have h4 : padicValNat p 4 = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun hd => by have := Nat.le_of_dvd (by norm_num) hd; omega)
  rw [h4, Finset.sum_eq_zero (fun i hi => by
    rw [padicValNat_factorial_lt' (by have := Finset.mem_Icc.mp hi; omega)]; rfl)]
  simp

lemma GV_F_big {n : ℕ} (hn : 1 ≤ n) (hbig : 2 * (37 * n) < p) : GV p (F n) 0 := by
  have := GV_F_of_Δ (zc14_big (p := p) hn (by omega))
  rw [vSK_big hn hbig] at this
  simpa using this

omit hp in
lemma padicValRat_mKM (M n : ℕ) (p : ℕ) [Fact p.Prime] :
    padicValRat p (mKM M n) = if p ≤ 2 * (37 * n) then -LpKM M n p else 0 := by
  unfold mKM
  rw [padicValRat_finset_prod _ _ (fun q hq => by
    have := (Finset.mem_filter.mp hq).2.pos
    exact zpow_ne_zero _ (by exact_mod_cast this.ne'))]
  simp only [padicValRat.zpow, padicValRat.of_nat]
  have hval : ∀ q ∈ (range (2 * (37 * n) + 1)).filter Nat.Prime,
      (padicValNat p q : ℤ) = if q = p then 1 else 0 := by
    intro q hq
    have hq' : q.Prime := (Finset.mem_filter.mp hq).2
    have := Fact.mk hq'
    split_ifs with h
    · subst h; simp [padicValNat.self (Fact.out : q.Prime).one_lt]
    · rw [padicValNat_primes (Ne.symm h)]; rfl
  rw [Finset.sum_congr rfl (fun q hq => by rw [hval q hq])]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  by_cases h : p ≤ 2 * (37 * n)
  · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Fact.out⟩), if_pos h]
  · rw [if_neg (fun hm => h (by have := Finset.mem_range.mp (Finset.mem_filter.mp hm).1; omega)),
      if_neg h]

/-- A rational number which is `p`-integral at every prime is an integer. -/
lemma rat_int_of_VG {q : ℚ} (h : ∀ p : ℕ, ∀ _ : Fact p.Prime, VG p q 0) : ∃ z : ℤ, q = z := by
  by_contra hne
  have hden : q.den ≠ 1 := fun h1 => hne ⟨q.num, (Rat.coe_int_num_of_den_eq_one h1).symm⟩
  set p := q.den.minFac with hpdef
  have hpp : p.Prime := Nat.minFac_prime hden
  have := Fact.mk hpp
  have hdvd : p ∣ q.den := Nat.minFac_dvd _
  rcases h p ‹_› with h0 | hv
  · exact hne ⟨0, by simp [h0]⟩
  · have hnum : ¬ (p : ℤ) ∣ q.num := by
      intro hd
      have hc := q.reduced
      have : p ∣ Nat.gcd q.num.natAbs q.den :=
        Nat.dvd_gcd (Int.natCast_dvd.mp hd) hdvd
      rw [hc] at this
      exact hpp.one_lt.ne' (Nat.dvd_one.mp this)
    have h1 : padicValInt p q.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
    have h2 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_ne_zero hdvd
    have e : padicValRat p q = padicValInt p q.num - padicValNat p q.den := rfl
    have hlt : padicValRat p q < 0 := by rw [e, h1]; omega
    have : (padicValRat p q : ℚ) < 0 := by exact_mod_cast hlt
    linarith

/-- **ZC15 (I19).** For `M ≥ 40` and `K = 40 n ≥ 200 M²`: `m_{K,M} > 0` and
`m_{K,M} F_K ∈ ℤ[X]`. -/
theorem zc15_normaliser {M n : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ 40 * n) :
    0 < mKM M n ∧ ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = C (mKM M n) * F n := by
  refine ⟨mKM_pos M n, ?_⟩
  have hn : 1 ≤ n := by nlinarith
  have hall : ∀ p : ℕ, ∀ _ : Fact p.Prime, GV p (C (mKM M n) * F n) 0 := by
    intro p _
    have hm : VG p (mKM M n) (if p ≤ 2 * (37 * n) then -LpKM M n p else 0 : ℤ) := by
      right; rw [padicValRat_mKM]
    by_cases hbig : p ≤ 2 * (37 * n)
    · rw [if_pos hbig] at hm
      have := GV.C_mul hm (GV_F_LpKM (p := p) hM hK)
      refine this.mono ?_
      push_cast; linarith
    · rw [if_neg hbig] at hm
      have := GV.C_mul hm (GV_F_big (p := p) hn (by omega))
      simpa using this
  have hcoef : ∀ k, ∃ z : ℤ, (C (mKM M n) * F n).coeff k = z := fun k =>
    rat_int_of_VG fun p hp => hall p hp k
  have hlift : C (mKM M n) * F n ∈ lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro k
    obtain ⟨z, hz⟩ := hcoef k
    exact ⟨z, by simp [hz]⟩
  obtain ⟨Q, hQ⟩ := hlift
  exact ⟨Q, hQ⟩

end Apery
