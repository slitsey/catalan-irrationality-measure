import CatalanCore.Uniform.Decay.NearFast.Rep2
set_option Elab.async false

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells

theorem fDZ_toC (z0 e : CQ) : (fDZ z0 e).toC = (fD z0 e : ℂ) * (1 - z0.toC) := by
  unfold fDZ
  rw [GZ.toC_sub, fZ_toC]
  have : (GZ.toC ⟨(fD z0 e : ℤ), 0⟩) = (fD z0 e : ℂ) := by
    apply Complex.ext <;> simp [GZ.toC]
  rw [this]; ring

theorem fD_ne (z0 e : CQ) : (fD z0 e : ℂ) ≠ 0 := by
  exact_mod_cast (fD_pos z0 e).ne'

theorem q1_rep (z0 e : CQ) (h1 : (CQ.sub CQ.one z0).nsq ≠ 0) :
    (q1of z0 e).toC * ((fQD1 z0 e : ℤ) : ℂ) = (fQN1 z0 e).toC := by
  have hne : (1 : ℂ) - z0.toC ≠ 0 := by
    have := CQ.toC_ne_zero h1
    rwa [CQ.toC_sub, CQ.toC_one] at this
  have hq : (q1of z0 e).toC = e.toC / (1 - z0.toC) := by
    unfold q1of; rw [CQ.toC_div _ _ h1, CQ.toC_sub, CQ.toC_one]
  unfold fQN1 fQD1
  rw [← GZ.toC_mul_conj, GZ.toC_mul, GZ.toC_conj, fE_toC, fDZ_toC, hq]
  have hD := fD_ne z0 e
  rw [map_mul, map_natCast]
  field_simp

theorem q0_rep (z0 e : CQ) (h0 : z0.nsq ≠ 0) :
    (q0of z0 e).toC * ((fQD0 z0 e : ℤ) : ℂ) = (fQN0 z0 e).toC := by
  have hne : z0.toC ≠ 0 := CQ.toC_ne_zero h0
  have hq : (q0of z0 e).toC = -(e.toC / z0.toC) := by
    unfold q0of; rw [CQ.toC_neg, CQ.toC_div _ _ h0]
  unfold fQN0 fQD0
  rw [← GZ.toC_mul_conj, GZ.toC_sub, GZ.toC_mul, GZ.toC_conj, GZ.toC_zero, fE_toC, fZ_toC, hq]
  have hD := fD_ne z0 e
  rw [map_mul, map_natCast]
  field_simp
  ring

theorem fQD1_pos (z0 e : CQ) (h1 : (CQ.sub CQ.one z0).nsq ≠ 0) : 0 < fQD1 z0 e := by
  have hne : (1 : ℂ) - z0.toC ≠ 0 := by
    have := CQ.toC_ne_zero h1
    rwa [CQ.toC_sub, CQ.toC_one] at this
  have hD := fD_ne z0 e
  have hnz : ((fDZ z0 e).toC) ≠ 0 := by rw [fDZ_toC]; exact mul_ne_zero hD hne
  have h2 : ((fQD1 z0 e : ℤ) : ℂ) ≠ 0 := by
    unfold fQD1; rw [← GZ.toC_mul_conj]
    exact mul_ne_zero hnz (by simpa using hnz)
  have h3 : fQD1 z0 e ≠ 0 := by intro h; apply h2; rw [h]; simp
  have h4 : 0 ≤ fQD1 z0 e := by
    unfold fQD1 GZ.nsq; exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  exact lt_of_le_of_ne h4 (Ne.symm h3)

theorem fQD0_pos (z0 e : CQ) (h0 : z0.nsq ≠ 0) : 0 < fQD0 z0 e := by
  have hne : z0.toC ≠ 0 := CQ.toC_ne_zero h0
  have hD := fD_ne z0 e
  have hnz : ((fZ z0 e).toC) ≠ 0 := by rw [fZ_toC]; exact mul_ne_zero hne hD
  have h2 : ((fQD0 z0 e : ℤ) : ℂ) ≠ 0 := by
    unfold fQD0; rw [← GZ.toC_mul_conj]
    exact mul_ne_zero hnz (by simpa using hnz)
  have h3 : fQD0 z0 e ≠ 0 := by intro h; apply h2; rw [h]; simp
  have h4 : 0 ≤ fQD0 z0 e := by
    unfold fQD0 GZ.nsq; exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  exact lt_of_le_of_ne h4 (Ne.symm h3)

/-- Jets: `jetc P q m` against the integer data. -/
theorem jet_rep (P : ℕ → CQ) (q : CQ) (PAI : ℕ → GZ) (QN : GZ) (QD DP : ℤ) (Fn m : ℕ)
    (hP : ∀ j, j < m → (P j).toC * (DP : ℂ) = (PAI j).toC)
    (hq : q.toC * (QD : ℂ) = QN.toC) (hQD : (QD : ℂ) ≠ 0) (hDP : (DP : ℂ) ≠ 0)
    (hF : ∀ j, j < m → (m - j) ∣ Fn) :
    ((jetc P q m).toC * ((DP : ℂ) * (Fn : ℂ) * (QD : ℂ) ^ m))
      = -∑ j ∈ range m, (((Fn / (m - j) : ℕ)) : ℂ) * ((PAI j).toC * (QD : ℂ) ^ j * QN.toC ^ (m - j)) := by
  unfold jetc
  simp only [CQ.toC_sumTo, CQ.toC_smul, CQ.toC_mul, CQ.toC_pow]
  rw [Finset.sum_range_succ, if_pos rfl]
  simp only [Rat.cast_zero, zero_mul, add_zero]
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < m := Finset.mem_range.1 hj
  have hjm : j ≠ m := by omega
  rw [if_neg hjm]
  have hdiv : ((((Fn / (m - j) : ℕ)) : ℂ)) = (Fn : ℂ) / ((m - j : ℕ) : ℂ) :=
    Nat.cast_div_charZero (hF j hj')
  have hmj : ((m - j : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : m - j ≠ 0)
  have hPj : (P j).toC = (PAI j).toC / (DP : ℂ) := by
    rw [eq_div_iff hDP]; exact hP j hj'
  have hqq : q.toC = QN.toC / (QD : ℂ) := by
    rw [eq_div_iff hQD]; exact hq
  have hpow : (QD : ℂ) ^ m = (QD : ℂ) ^ j * (QD : ℂ) ^ (m - j) := by
    rw [← pow_add]; congr 1; omega
  have hQp : (QD : ℂ) ^ (m - j) ≠ 0 := pow_ne_zero _ hQD
  rw [hdiv, hPj, hqq, hpow, div_pow]
  push_cast
  field_simp

end CatalanCore.Uniform.Decay.NearFast
