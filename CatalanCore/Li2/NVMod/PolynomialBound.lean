module
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialLists
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1500000
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod.PolynomialCert
noncomputable section
/-- Convolution bounded by the number of coefficients in the first factor. -/
theorem coeff_mul_bound (f g : ℤ[X]) (d : ℕ) (a b : ℤ)
    (hd : f.natDegree≤d) (ha : 0≤a) (hb : 0≤b)
    (hf : ∀ j,|f.coeff j|≤a) (hg : ∀ j,|g.coeff j|≤b) (k : ℕ) :
    |(f*g).coeff k|≤(d+1)*a*b := by
  have he : f=∑ i∈range (d+1),C (f.coeff i)*X^i :=
    f.as_sum_range_C_mul_X_pow' (by omega)
  conv_lhs => rw [he]
  rw [Finset.sum_mul,Polynomial.finsetSum_coeff]
  calc
    |∑ i∈range (d+1),((C (f.coeff i)*X^i)*g).coeff k|≤
        ∑ i∈range (d+1),|((C (f.coeff i)*X^i)*g).coeff k| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑ _i∈range (d+1),a*b := by
      apply Finset.sum_le_sum
      intro i hi
      have hx : (C (f.coeff i)*X^i)*g=C (f.coeff i)*(g*X^i) := by ring
      rw [hx,Polynomial.coeff_C_mul,Polynomial.coeff_mul_X_pow']
      split_ifs
      · rw [abs_mul]
        exact mul_le_mul (hf i) (hg (k-i)) (abs_nonneg _) ha
      · simp only [mul_zero,abs_zero]
        exact mul_nonneg ha hb
    _=(d+1)*a*b := by simp [mul_assoc]
/-- The n-fold convolution loses only n-1 factors of d+1. -/
theorem list_prod_coeff_bound (xs : List ℤ[X]) (d : ℕ) (p : ℤ) (hp : 0≤p)
    (hxs : ∀ f∈xs,f.natDegree≤d ∧ ∀ j,|f.coeff j|≤p) (j : ℕ) :
    |xs.prod.coeff j|≤(d+1:ℤ)^(xs.length-1)*p^xs.length := by
  induction xs generalizing j with
  | nil => simp only [List.prod_nil,List.length_nil,Nat.zero_sub,pow_zero,mul_one]
           simpa only [Polynomial.coeff_one] using (show |(if j=0 then (1:ℤ) else 0)|≤1 by split_ifs <;> norm_num)
  | cons f fs ih =>
    have hf := hxs f (by simp)
    cases fs with
    | nil => simpa using hf.2 j
    | cons g gs =>
      have hr : ∀ f∈g::gs,f.natDegree≤d ∧ ∀ j,|f.coeff j|≤p :=
        fun f hf=>hxs f (by simp [hf])
      have hh := coeff_mul_bound f (g::gs).prod d p
        ((d+1:ℤ)^((g::gs).length-1)*p^(g::gs).length) hf.1 hp
        (by positivity) hf.2 (fun k=>ih hr k) j
      simpa only [List.prod_cons,List.length_cons,Nat.add_sub_cancel,pow_succ,mul_assoc,mul_comm,mul_left_comm] using hh
/-- NZ4: Leibniz coefficient bound for a polynomial matrix. -/
theorem det_coeff_bound (n d : ℕ) (p : ℤ) (hp : 0≤p)
    (M : Matrix (Fin n) (Fin n) ℤ[X])
    (hM : ∀ i j,(M i j).natDegree≤d ∧ ∀ k,|(M i j).coeff k|≤p) (k : ℕ) :
    |M.det.coeff k|≤n.factorial*(d+1:ℤ)^(n-1)*p^n := by
  classical
  rw [Matrix.det_apply,Polynomial.finsetSum_coeff]
  calc
    |∑ σ : Equiv.Perm (Fin n),(Equiv.Perm.sign σ • ∏ i,M (σ i) i).coeff k|≤
        ∑ σ : Equiv.Perm (Fin n),|(Equiv.Perm.sign σ • ∏ i,M (σ i) i).coeff k| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑ _σ : Equiv.Perm (Fin n),(d+1:ℤ)^(n-1)*p^n := by
      apply Finset.sum_le_sum
      intro σ hσ
      have hh := list_prod_coeff_bound (List.ofFn (fun i : Fin n=>M (σ i) i)) d p hp
        (by intro f hf;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hf;exact hM (σ i) i) k
      simpa only [List.prod_ofFn,List.length_ofFn,Polynomial.coeff_smul,Units.smul_def,smul_eq_mul,
        abs_mul,Equiv.Perm.sign_abs,one_mul] using hh
    _=n.factorial*(d+1:ℤ)^(n-1)*p^n := by simp [Fintype.card_perm,mul_assoc]
#print axioms det_coeff_bound
end
end CatalanCore.Li2.NVMod.PolynomialCert

