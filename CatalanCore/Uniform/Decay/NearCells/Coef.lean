module

public import CatalanCore.Uniform.Decay.NearCells.Expand

@[expose] public section

/-!
# Kernel-computable polynomial coefficients (lane D, package D6b)

`PBc`, `PAc`, `Rc` are the coefficients in `s` of `PB(ζ₀ + e s)`, `mass - PB`, `R` over `CQ`;
`jetc` is the coefficient list of D1's `jet`.  Each has an expansion lemma against the
complex-valued definitions.
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset Complex CatalanCore.Uniform.Decay.Tools

def PBc (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) (m : ℕ) : CQ :=
  CQ.sumTo (fun k => CQ.smul (wq a k * (((k + 1).choose m : ℕ) : ℚ))
    (CQ.mul (CQ.pow e m) (CQ.pow z0 (k + 1 - m)))) (d + 1)

def PAc (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) (m : ℕ) : CQ :=
  CQ.sub (CQ.ofQ (if m = 0 then massQ a d else 0)) (PBc a d z0 e m)

def Rc (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) (m : ℕ) : CQ :=
  CQ.neg (CQ.sumTo (fun k => CQ.smul (wq a k)
    (CQ.sumTo (fun i => CQ.smul ((1 / ((i : ℚ) + 1)) * (((k - i).choose m : ℕ) : ℚ))
      (CQ.mul (CQ.pow e m) (CQ.pow z0 (k - i - m)))) (k + 1))) (d + 1))

def jetc (P : ℕ → CQ) (q : CQ) (m : ℕ) : CQ :=
  CQ.sumTo (fun j => CQ.smul (if j = m then 0 else -(1 / (((m - j : ℕ)) : ℚ)))
    (CQ.mul (P j) (CQ.pow q (m - j)))) (m + 1)

theorem PB_expand (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) (s : ℂ) (n : ℕ) (hn : d + 2 ≤ n) :
    ∑ m ∈ range n, (PBc a d z0 e m).toC * s ^ m = PBf a d (z0.toC + e.toC * s) := by
  unfold PBf
  have h : ∀ k ∈ range (d + 1), (wq a k : ℂ) * (z0.toC + e.toC * s) ^ (k + 1)
      = ∑ m ∈ range n, (wq a k : ℂ) *
          (e.toC ^ m * (((k + 1).choose m : ℕ) : ℂ) * z0.toC ^ (k + 1 - m)) * s ^ m := by
    intro k hk
    rw [binom_expand _ _ _ (k + 1) n (by simp at hk; omega), Finset.mul_sum]
    apply Finset.sum_congr rfl; intros; ring
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [PBc, CQ.toC_sumTo, CQ.toC_smul, CQ.toC_mul, CQ.toC_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast; ring

theorem PA_expand (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) (s : ℂ) (n : ℕ) (hn : d + 2 ≤ n) :
    ∑ m ∈ range n, (PAc a d z0 e m).toC * s ^ m
      = ((massQ a d : ℚ) : ℂ) - PBf a d (z0.toC + e.toC * s) := by
  rw [← PB_expand a d z0 e s n hn]
  have h : ∀ m ∈ range n, (PAc a d z0 e m).toC * s ^ m
      = (if m = 0 then ((massQ a d : ℚ) : ℂ) else 0) * s ^ m
        - (PBc a d z0 e m).toC * s ^ m := by
    intro m _
    simp only [PAc, CQ.toC_sub, CQ.toC_ofQ]
    split_ifs <;> simp [sub_mul]
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib]
  congr 1
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' (range n) 0]
  simp only [mem_range]
  rw [if_pos (by omega)]; simp

theorem R_expand (a : ℕ → ℚ) (d : ℕ) (z0 e : CQ) (s : ℂ) (n : ℕ) (hn : d + 1 ≤ n) :
    ∑ m ∈ range n, (Rc a d z0 e m).toC * s ^ m = Rf a d (z0.toC + e.toC * s) := by
  unfold Rf
  have h : ∀ k ∈ range (d + 1), ∀ i ∈ range (k + 1),
      (z0.toC + e.toC * s) ^ (k - i) / ((i : ℂ) + 1)
      = ∑ m ∈ range n, (1 / ((i : ℂ) + 1)) *
          (e.toC ^ m * (((k - i).choose m : ℕ) : ℂ) * z0.toC ^ (k - i - m)) * s ^ m := by
    intro k hk i hi
    rw [binom_expand _ _ _ (k - i) n (by simp at hk; omega), div_eq_mul_inv, mul_comm,
      Finset.mul_sum]
    apply Finset.sum_congr rfl; intros; ring
  have h2 : ∀ k ∈ range (d + 1), (wq a k : ℂ) *
      ∑ i ∈ range (k + 1), (z0.toC + e.toC * s) ^ (k - i) / ((i : ℂ) + 1)
      = ∑ m ∈ range n, (wq a k : ℂ) * ∑ i ∈ range (k + 1), (1 / ((i : ℂ) + 1)) *
          (e.toC ^ m * (((k - i).choose m : ℕ) : ℂ) * z0.toC ^ (k - i - m)) * s ^ m := by
    intro k hk
    rw [Finset.sum_congr rfl (h k hk), Finset.sum_comm, Finset.mul_sum]
  rw [Finset.sum_congr rfl h2, Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Rc, CQ.toC_neg, CQ.toC_sumTo, CQ.toC_smul, CQ.toC_mul, CQ.toC_pow, neg_mul,
    Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [CQ.toC_sumTo, CQ.toC_smul, CQ.toC_mul, CQ.toC_pow, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

theorem jet_expand (P : ℕ → CQ) (q : CQ) (s : ℂ) (n : ℕ) :
    jet n (fun j => (P j).toC) q.toC s = ∑ m ∈ range n, (jetc P q m).toC * s ^ m := by
  unfold jet termJet logJet
  have h1 : ∀ j ∈ range n, -((P j).toC * s ^ j * ∑ k ∈ range (n - j), (q.toC * s) ^ k / (k : ℂ))
      = ∑ k ∈ range (n - j), -((P j).toC * s ^ j * ((q.toC * s) ^ k / (k : ℂ))) := by
    intro j _; rw [Finset.mul_sum, Finset.sum_neg_distrib]
  rw [Finset.sum_congr rfl h1]
  rw [← Finset.sum_range_diag_flip n (fun j k => -((P j).toC * s ^ j * ((q.toC * s) ^ k / (k : ℂ))))]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [jetc, CQ.toC_sumTo, CQ.toC_smul, CQ.toC_mul, CQ.toC_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ m := by simp at hj; omega
  by_cases hjm : j = m
  · subst hjm; simp
  · have hne : ((m - j : ℕ) : ℂ) ≠ 0 := by
      have : (m - j : ℕ) ≠ 0 := by omega
      exact_mod_cast this
    have e1 : s ^ m = s ^ j * s ^ (m - j) := by rw [← pow_add]; congr 1; omega
    rw [if_neg hjm, e1]
    push_cast
    field_simp
    ring

end CatalanCore.Uniform.Decay.NearCells
