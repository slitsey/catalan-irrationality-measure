module

public import CatalanCore.Zeta5.Content.Parity
public import CatalanCore.Zeta5.CostOut.ExtCost

@[expose] public section

/-!
# ZC32: the extended signed normaliser `m_C`

The local exponent `L_p^C` of ZC32 refines `LpKM` (ZC15) in two bands:

* inner, `K/200 ≤ p ≤ K/3`: `v_p(S_K) + γ_p^in + k_p` with the parity gain `k_p` (`kpar`); valid
  under the hypothesis `hpar : ParityGain`;
* outer, `K/3 < p ≤ K` with `ExtHyp`: `v_p(S_K) + max (γ_p^out, γ_p^ext)` (`zc19_exponent`; the
  extension exponent is an integer, `ext_gamma_int`).

`mC M n = ∏_{p ≤ 2h} p^{-L_p^C}` is a positive rational with `m_C F_K ∈ ℤ[X]` (`zc32_normaliser`)
and `log m_C = -∑_p L_p^C log p` (`log_mC`).
-/

open Finset Polynomial

namespace CatalanCore.Zeta5.Content

open Apery CatalanCore.Zeta5.CostOut

open Classical in
/-- The extended local exponent `L_p^C`. -/
noncomputable def LpC (M n p : ℕ) : ℤ :=
  if p * M ≤ 40 * n then LsmallN n p
  else if 3 * p ≤ 40 * n then
    vSK n p + gammaIn M n p + (if 40 * n ≤ 200 * p then (kpar p n (4 * M + 10) : ℤ) else 0)
  else if H : ExtHyp p n then vSK n p + max (gammaOut n p) ⌊gammaExt H⌋
  else LpKM M n p

/-- **The extended normaliser** `m_C = ∏_{p ≤ 2h} p^{-L_p^C}`. -/
noncomputable def mC (M n : ℕ) : ℚ :=
  ∏ p ∈ (range (2 * (37 * n) + 1)).filter Nat.Prime, (p : ℚ) ^ (-LpC M n p)

lemma mC_pos (M n : ℕ) : 0 < mC M n := by
  unfold mC
  apply Finset.prod_pos
  intro p hp
  have : 0 < p := (Finset.mem_filter.mp hp).2.pos
  exact zpow_pos (by exact_mod_cast this) _

/-- **Signed cost.** `log m_C = -∑_p L_p^C log p`. -/
lemma log_mC (M n : ℕ) :
    Real.log (mC M n) = -∑ p ∈ (range (2 * (37 * n) + 1)).filter Nat.Prime,
      (LpC M n p : ℝ) * Real.log p := by
  unfold mC
  rw [Rat.cast_prod]
  simp only [Rat.cast_zpow, Rat.cast_natCast]
  rw [Real.log_prod (fun p hp => by
    have : 0 < p := (Finset.mem_filter.mp hp).2.pos
    exact zpow_ne_zero _ (Nat.cast_ne_zero.mpr this.ne'))]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Real.log_zpow]; push_cast; ring

section
variable {p : ℕ} [hp : Fact p.Prime]

/-- Every extended local exponent is valid, given the parity gain. -/
theorem GV_F_LpC (hpar : ParityGain) {M n : ℕ} (hM : 40 ≤ M) (hK : 200 * M ^ 2 ≤ 40 * n) :
    GV p (F n) (LpC M n p : ℚ) := by
  have hbase := GV_F_LpKM (p := p) hM hK
  unfold LpC
  by_cases h1 : p * M ≤ 40 * n
  · rw [if_pos h1]
    unfold LpKM at hbase; rwa [if_pos h1] at hbase
  rw [if_neg h1]
  by_cases h2 : 3 * p ≤ 40 * n
  · rw [if_pos h2]
    by_cases h3 : 40 * n ≤ 200 * p
    · rw [if_pos h3]
      have H : InnerHyp p n M (4 * M + 10) :=
        ⟨hp.out, hM, hK, by omega, h2, by omega, by omega⟩
      have := GV_F_of_Δ (hpar p n M H h3)
      refine this.mono ?_
      unfold gammaIn
      rw [dif_pos H]
      push_cast
      have := Int.floor_le (2 * ∑ s : (Σ a : Fin (p / 2 + 1), Fin (innerL p n (4 * M + 10) a)),
        winner H.m_pos (innerL p n (4 * M + 10)) (Bse p (40 * n) (3 * n)) s)
      linarith
    · rw [if_neg h3, add_zero]
      unfold LpKM at hbase; rwa [if_neg h1, if_pos h2] at hbase
  rw [if_neg h2]
  by_cases hE : ExtHyp p n
  · rw [dif_pos hE]
    have := GV_F_of_Δ (zc19_exponent hE)
    refine this.mono ?_
    push_cast
    have hfl := Int.floor_le (gammaExt hE)
    have : max ((gammaOut n p : ℤ) : ℚ) ((⌊gammaExt hE⌋ : ℤ) : ℚ) ≤
        max ((gammaOut n p : ℤ) : ℚ) (gammaExt hE) := max_le_max le_rfl hfl
    linarith
  · rw [dif_neg hE]; exact hbase

end

lemma padicValRat_mC (M n : ℕ) (p : ℕ) [Fact p.Prime] :
    padicValRat p (mC M n) = if p ≤ 2 * (37 * n) then -LpC M n p else 0 := by
  unfold mC
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

/-- **ZC32, integrality.** Given the parity gain, for `M ≥ 40` and `K = 40 n ≥ 200 M²`:
`m_C > 0` and `m_C F_K ∈ ℤ[X]`. -/
theorem zc32_normaliser (hpar : ParityGain) {M n : ℕ} (hM : 40 ≤ M)
    (hK : 200 * M ^ 2 ≤ 40 * n) :
    0 < mC M n ∧ ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) = C (mC M n) * F n := by
  refine ⟨mC_pos M n, ?_⟩
  have hn : 1 ≤ n := by nlinarith
  have hall : ∀ p : ℕ, ∀ _ : Fact p.Prime, GV p (C (mC M n) * F n) 0 := by
    intro p _
    have hm : VG p (mC M n) (if p ≤ 2 * (37 * n) then -LpC M n p else 0 : ℤ) := by
      right; rw [padicValRat_mC]
    by_cases hbig : p ≤ 2 * (37 * n)
    · rw [if_pos hbig] at hm
      have := GV.C_mul hm (GV_F_LpC (p := p) hpar hM hK)
      refine this.mono ?_
      push_cast; linarith
    · rw [if_neg hbig] at hm
      have := GV.C_mul hm (GV_F_big (p := p) hn (by omega))
      simpa using this
  have hcoef : ∀ k, ∃ z : ℤ, (C (mC M n) * F n).coeff k = z := fun k =>
    rat_int_of_VG fun p hp => hall p hp k
  have hlift : C (mC M n) * F n ∈ lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro k
    obtain ⟨z, hz⟩ := hcoef k
    exact ⟨z, by simp [hz]⟩
  obtain ⟨Q, hQ⟩ := hlift
  exact ⟨Q, hQ⟩

end CatalanCore.Zeta5.Content
