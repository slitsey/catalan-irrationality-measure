import CatalanCore.Uniform.Decay.NearFast.Rep1
set_option Elab.async false

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells

theorem reindex_sum (G : ℕ → ℕ → ℂ) (d : ℕ) :
    ∑ k ∈ range (d + 1), ∑ i ∈ range (k + 1), G k i
      = ∑ j ∈ range (d + 1), ∑ k ∈ range (d + 1), if j ≤ k then G k (k - j) else 0 := by
  have h1 : ∀ k ∈ range (d + 1), ∑ i ∈ range (k + 1), G k i
      = ∑ j ∈ range (d + 1), if j ≤ k then G k (k - j) else 0 := by
    intro k hk
    have hk' : k < d + 1 := Finset.mem_range.1 hk
    have e1 : ∑ i ∈ range (k + 1), G k i = ∑ j ∈ range (k + 1), G k (k - j) := by
      have := Finset.sum_range_reflect (G k) (k + 1)
      simpa using this.symm
    rw [e1, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]

/-- The weight sum `S_j = ∑_{k ≥ j} w_k / (k - j + 1)`. -/
noncomputable def Sj (a : ℕ → ℚ) (d j : ℕ) : ℂ :=
  ∑ k ∈ range (d + 1), if j ≤ k then (wq a k : ℂ) / (((k - j : ℕ) : ℂ) + 1) else 0

theorem frI_cast (a : ℕ → ℚ) (d j : ℕ) :
    ((frI a d j : ℤ) : ℂ) = Sj a d j * (fDw a d : ℂ) * (((d + 1).factorial : ℕ) : ℂ) := by
  unfold frI Sj
  rw [cast_sumI, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < d + 1 := Finset.mem_range.1 hk
  by_cases hjk : j ≤ k
  · simp only [hjk, ite_true]
    have hdvd : (k - j + 1) ∣ (d + 1).factorial := Nat.dvd_factorial (by omega) (by omega)
    have hdiv : ((((d + 1).factorial / (k - j + 1) : ℕ)) : ℂ)
        = (((d + 1).factorial : ℕ) : ℂ) / (((k - j + 1 : ℕ)) : ℂ) := Nat.cast_div_charZero hdvd
    have hne : (((k - j : ℕ) : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k - j)
    rw [Int.cast_mul, Int.cast_natCast, hdiv, fwI_castC a d k (by omega)]
    push_cast
    field_simp
  · simp [hjk]

theorem Rc_rep (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) {Dp : List ℤ} {Zp Ep : List GZ} {rIt : List ℤ}
    (hD : ∀ i, i < d + 2 → iget Dp i = (fD z0 e : ℤ) ^ i)
    (hZ : ∀ i, i < d + 2 → (gget Zp i).toC = (fZ z0 e).toC ^ i)
    (hR : ∀ j, j < d + 1 → iget rIt j = frI a d j) (m : ℕ)
    (hE : (gget Ep m).toC = (fE z0 e).toC ^ m) :
    (Rc a d z0 e m).toC * ((fDw a d : ℂ) * (((d + 1).factorial : ℕ) : ℂ) * (fD z0 e : ℂ) ^ d)
      = -(fRRm d rIt Dp Zp Ep m).toC := by
  unfold Rc fRRm
  rw [GZ.toC_mul, toC_sumG, hE]
  simp only [CQ.toC_neg, CQ.toC_sumTo, CQ.toC_smul, CQ.toC_mul, CQ.toC_pow, GZ.toC_smul]
  rw [neg_mul, neg_inj]
  have step1 : ∑ k ∈ range (d + 1), (wq a k : ℂ) * ∑ i ∈ range (k + 1),
      (((1 / ((i : ℚ) + 1)) * (((k - i).choose m : ℕ) : ℚ) : ℚ) : ℂ) * (e.toC ^ m * z0.toC ^ (k - i - m))
      = ∑ k ∈ range (d + 1), ∑ i ∈ range (k + 1), (wq a k : ℂ) *
        ((((1 / ((i : ℚ) + 1)) * (((k - i).choose m : ℕ) : ℚ) : ℚ) : ℂ) * (e.toC ^ m * z0.toC ^ (k - i - m))) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  rw [step1, reindex_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < d + 1 := Finset.mem_range.1 hj
  rw [hZ (j - m) (by omega), fZ_toC, fE_toC, hD (d - j) (by omega), hR j hj']
  have hsum : ∑ k ∈ range (d + 1), (if j ≤ k then (wq a k : ℂ) *
        ((((1 / (((k - j : ℕ) : ℚ) + 1)) * (((k - (k - j)).choose m : ℕ) : ℚ) : ℚ) : ℂ) *
          (e.toC ^ m * z0.toC ^ (k - (k - j) - m))) else 0)
      = Sj a d j * (((j.choose m : ℕ) : ℂ) * (e.toC ^ m * z0.toC ^ (j - m))) := by
    unfold Sj
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    by_cases hjk : j ≤ k
    · simp only [hjk, ite_true]
      rw [Nat.sub_sub_self hjk]
      push_cast
      ring
    · simp [hjk]
  rw [hsum]
  push_cast
  rw [frI_cast]
  rcases Nat.lt_or_ge j m with hlt | hge
  · rw [Nat.choose_eq_zero_of_lt hlt, chooseFast_eq, Nat.choose_eq_zero_of_lt hlt]; simp
  · have key : (fD z0 e : ℂ) ^ d =
        (fD z0 e : ℂ) ^ (d - j) * (fD z0 e : ℂ) ^ m * (fD z0 e : ℂ) ^ (j - m) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [key, chooseFast_eq]
    push_cast
    simp only [mul_pow]
    ring

end CatalanCore.Uniform.Decay.NearFast
