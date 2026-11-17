module

public import CatalanCore.Lai.ContentLaw
public import CatalanCore.Zeta5.Local.BinomBasis
public import CatalanCore.NT.WeightedPrimeSum
public import Mathlib.Data.Nat.Choose.Dvd

@[expose] public section

/-!
# `CatalanCore.Lai.ContentPrimes`: classical `p`-adic estimates for `J_n` (LC02) and the small primes (LC22)

Paper: Lai, arXiv 2610.06838, Lemma 4.1 and (5.6)-(5.7); `N9-LAI-CONTENT-2026-11-16.md` (Theorem A).

* `laiJ_eq_det_bin` : `J_n = det (L_n(binom(t,x) binom(t,y)))_{x,y<3n}` (the basis change of (4.1) is unimodular);
* `lai_vp_lower` (**LC02, Lemma 4.1 (1)**): for every prime `p`, `v_p(J_n) ≥ -12 n ⌊log_p(8n)⌋`
  in the Gauss valuation (`GV p (-(12 n ⌊log_p (8n)⌋)) (laiJ n)`);
* `lai_vp_lower_sqrt` (Lemma 4.1 (2)): `8n < p²` gives `v_p(J_n) ≥ -12 n`;
* `lai_vp_nonneg` (Lemma 4.1 (3)): `p > 6n` gives `v_p(J_n) ≥ 0`;
* `lai_small_primes` (**LC22**): `Σ_{p ≤ δ n} 12 n ⌊log_p(8n)⌋ log p ≤ (12 δ + ε) n²` eventually;
(LC25, LC26 are in `CatalanCore.Lai.ContentTables`.)
-/

set_option linter.deprecated false

open Finset MvPolynomial CatalanCore.Basic CatalanCore.Content
open scoped Nat

namespace CatalanCore.Lai

section Loc

variable {p : ℕ} [hp : Fact p.Prime]

/-- `p^L / m` is `p`-integral for `1 ≤ m` and `⌊log_p m⌋ ≤ L`. -/
lemma pow_div_mem {L m : ℕ} (hm : 1 ≤ m) (hL : Nat.log p m ≤ L) :
    (p : ℚ) ^ L / (m : ℚ) ∈ LocRing p := by
  obtain ⟨a, u, hu, hmu⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := m) (by omega) p hp.out.ne_one
  have hu0 : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; exact hu (dvd_zero p))
  have ha : a ≤ L := by
    refine le_trans (Nat.le_log_of_pow_le hp.out.one_lt ?_) hL
    rw [hmu]; exact Nat.le_mul_of_pos_right _ hu0
  rw [hmu]
  have hpa : (p : ℚ) ^ L = (p : ℚ) ^ (L - a) * (p : ℚ) ^ a := by
    rw [← pow_add]; congr 1; omega
  have hp0 := p_ne_zero' (p := p)
  have hu' : (u : ℚ) ≠ 0 := by exact_mod_cast hu0.ne'
  have : (p : ℚ) ^ L / ((p ^ a * u : ℕ) : ℚ) = (p : ℚ) ^ (L - a) * ((u : ℚ))⁻¹ := by
    rw [hpa]; push_cast; field_simp
  rw [this]
  exact (LocRing p).mul_mem (natPow_mem _) (inv_natCast_mem_locRing hu)

/-- `p^{sL} H_k(s)` is `p`-integral when `⌊log_p k⌋ ≤ L`. -/
lemma Hq_scaled_mem (s k L : ℕ) (hk : Nat.log p k ≤ L) :
    (p : ℚ) ^ (s * L) * Hq s k ∈ LocRing p := by
  unfold Hq
  rw [Finset.mul_sum]
  refine (LocRing p).sum_mem fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have h1 : Nat.log p (i + 1) ≤ L := (Nat.log_mono_right (by omega)).trans hk
  have := (LocRing p).pow_mem (pow_div_mem (p := p) (by omega : 1 ≤ i + 1) h1) s
  convert this using 1
  rw [div_pow, ← pow_mul, mul_comm L s]
  push_cast
  ring

lemma Hq_scaled_mem' (s t k L : ℕ) (hst : s ≤ t) (hk : Nat.log p k ≤ L) :
    (p : ℚ) ^ (t * L) * Hq s k ∈ LocRing p := by
  have h := Hq_scaled_mem (p := p) s k L hk
  have e : (p : ℚ) ^ (t * L) = (p : ℚ) ^ ((t - s) * L) * (p : ℚ) ^ (s * L) := by
    rw [← pow_add, ← add_mul]; congr 2; omega
  rw [e, mul_assoc]
  exact (LocRing p).mul_mem (natPow_mem _) h

end Loc

section Bin

open Apery Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

lemma bin_pascal_eval (i : ℕ) (x : ℚ) :
    (bin (i + 1)).eval (x + 1) = (bin (i + 1)).eval x + (bin i).eval x := by
  have := congrArg (Polynomial.eval x) (bin_comp_add_one i)
  simpa [Polynomial.eval_comp] using this

/-- `binom(t, i)` takes integer values at `t = -m`. -/
lemma bin_eval_negnat (i m : ℕ) : ∃ z : ℤ, (bin i).eval (-(m : ℚ)) = z := by
  induction i generalizing m with
  | zero => exact ⟨1, by simp [bin_zero]⟩
  | succ i ih =>
    induction m with
    | zero => exact ⟨0, by simp [bin_eval_zero (Nat.succ_pos i)]⟩
    | succ m ihm =>
      obtain ⟨z1, hz1⟩ := ihm
      obtain ⟨z2, hz2⟩ := ih (m + 1)
      refine ⟨z1 - z2, ?_⟩
      have h := bin_pascal_eval i (-((m + 1 : ℕ) : ℚ))
      have e : -((m + 1 : ℕ) : ℚ) + 1 = -(m : ℚ) := by push_cast; ring
      rw [e, hz1, hz2] at h
      push_cast
      push_cast at h
      linarith

lemma bin_eval_negnat_mem (i m : ℕ) : (bin i).eval (-(m : ℚ)) ∈ LocRing p := by
  obtain ⟨z, hz⟩ := bin_eval_negnat i m
  rw [hz]; exact int_mem_locRing z

/-- Zudilin's lemma in the form used: `p^L · d/dt binom(t,i) |_{t=-k}` is `p`-integral when
`⌊log_p i⌋ ≤ L`. -/
lemma bin_deriv_mem {L i : ℕ} (hi : Nat.log p i ≤ L) (k : ℕ) :
    (p : ℚ) ^ L * (bin i).derivative.eval (-(k : ℚ)) ∈ LocRing p := by
  rw [derivative_bin, Polynomial.eval_finset_sum, Finset.mul_sum]
  refine (LocRing p).sum_mem fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  obtain ⟨z, hz⟩ := bin_eval_negnat (i - j) k
  rw [hz]
  have hdc : (p : ℚ) ^ L * dcoef j ∈ LocRing p := by
    unfold dcoef
    have e : (p : ℚ) ^ L * ((-1) ^ (j - 1) / (j : ℚ)) = (-1) ^ (j - 1) * ((p : ℚ) ^ L / j) := by ring
    rw [e]
    refine (LocRing p).mul_mem ?_ (pow_div_mem (by omega) ((Nat.log_mono_right hj.2).trans hi))
    exact (LocRing p).pow_mem ((LocRing p).neg_mem (LocRing p).one_mem) _
  rw [← mul_assoc]
  exact (LocRing p).mul_mem hdc (int_mem_locRing z)

lemma bin_natDegree_le (k : ℕ) : (bin k).natDegree ≤ k := by
  unfold bin
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [descPochhammer_natDegree]

lemma bin_coeff_self (k : ℕ) : (bin k).coeff k = ((k ! : ℚ))⁻¹ := by
  unfold bin
  rw [Polynomial.coeff_C_mul]
  have := (monic_descPochhammer ℚ k).coeff_natDegree
  rw [descPochhammer_natDegree] at this
  rw [this, mul_one]

end Bin

section Gram

open Apery Polynomial

lemma det_coeffMat_bin (n : ℕ) :
    (coeffMat n (fun x : Fin (3 * n) => Apery.bin (x : ℕ))).det =
      MvPolynomial.C ((∏ i ∈ range (3 * n), ((i ! : ℚ)))⁻¹) := by
  have hlow : (coeffMat n (fun x : Fin (3 * n) => Apery.bin (x : ℕ))).IsLowerTriangular := by
    intro x i hxi
    simp only [coeffMat, Matrix.of_apply]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (bin_natDegree_le x) (by exact_mod_cast hxi))]
    simp
  rw [Matrix.det_of_isLowerTriangular _ hlow]
  simp only [coeffMat, Matrix.of_apply, bin_coeff_self]
  rw [← map_prod, Finset.prod_inv_distrib]
  congr 2
  exact Fin.prod_univ_eq_prod_range (fun i => ((i ! : ℚ))) (3 * n)

theorem laiJ_eq_det_bin (n : ℕ) :
    laiJ n = (Matrix.of fun x y : Fin (3 * n) =>
      laiL n (Apery.bin (x : ℕ) * Apery.bin (y : ℕ))).det := by
  have hf : ∀ x : Fin (3 * n), (Apery.bin (x : ℕ)).natDegree < 3 * n := fun x =>
    lt_of_le_of_lt (bin_natDegree_le x) x.2
  rw [gram_det_fin n (fun x : Fin (3 * n) => Apery.bin (x : ℕ)) hf, det_coeffMat_bin]
  unfold laiJ
  have h2 : ((∏ i ∈ range (3 * n), ((i ! : ℚ)))⁻¹) ^ 2 = (∏ i ∈ range (3 * n), ((i ! : ℚ)) ^ 2)⁻¹ := by
    rw [inv_pow, Finset.prod_pow]
  rw [← map_pow, h2]

end Gram

section Entries

open Apery Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

lemma laiU_GV (k L : ℕ) (hk : Nat.log p k ≤ L) : GV p (-((3 * L : ℕ) : ℤ)) (laiU k) := by
  unfold laiU
  refine GV.add (GV_CX_nat _ _ _ ?_) (GV_CX_nat _ _ _ ?_)
  · rw [show (p : ℚ) ^ (3 * L) * (-3 * Hq 2 k) = -3 * ((p : ℚ) ^ (3 * L) * Hq 2 k) by ring]
    exact (LocRing p).mul_mem lm3 (Hq_scaled_mem' 2 3 k L (by norm_num) hk)
  · rw [show (p : ℚ) ^ (3 * L) * (-2 * Hq 3 k) = -2 * ((p : ℚ) ^ (3 * L) * Hq 3 k) by ring]
    exact (LocRing p).mul_mem lm2 (Hq_scaled_mem' 3 3 k L le_rfl hk)

lemma laiH_scaled_mem (n k L : ℕ) (hL : Nat.log p (8 * n) ≤ L) (hk : k ≤ 6 * n) :
    (p : ℚ) ^ L * laiH n k ∈ LocRing p := by
  unfold laiH
  have h1 := Hq_scaled_mem' (p := p) 1 1 (2 * n + k) L le_rfl
    ((Nat.log_mono_right (by omega)).trans hL)
  have h2 := Hq_scaled_mem' (p := p) 1 1 (6 * n - k) L le_rfl
    ((Nat.log_mono_right (by omega)).trans hL)
  have h3 := Hq_scaled_mem' (p := p) 1 1 k L le_rfl
    ((Nat.log_mono_right (by omega)).trans hL)
  simp only [one_mul] at h1 h2 h3
  have e : (p : ℚ) ^ L * (3 * Hq 1 (2 * n + k) + 2 * Hq 1 (6 * n - k) - 5 * Hq 1 k) =
      3 * ((p : ℚ) ^ L * Hq 1 (2 * n + k)) + 2 * ((p : ℚ) ^ L * Hq 1 (6 * n - k)) -
        5 * ((p : ℚ) ^ L * Hq 1 k) := by ring
  rw [e]
  exact (LocRing p).sub_mem
    ((LocRing p).add_mem ((LocRing p).mul_mem l3 h1) ((LocRing p).mul_mem l2 h2))
    ((LocRing p).mul_mem l5 h3)

lemma laiV_GV (n k L : ℕ) (hL : Nat.log p (8 * n) ≤ L) (hk : k ≤ 6 * n) :
    GV p (-((4 * L : ℕ) : ℤ)) (laiV n k) := by
  have hlk : Nat.log p k ≤ L := (Nat.log_mono_right (by omega)).trans hL
  have g1 : GV p (-(L : ℤ)) (MvPolynomial.C (laiH n k) : MP) := by
    refine GV.const ?_
    simpa [zpow_natCast] using laiH_scaled_mem n k L hL hk
  have g2 : GV p (-((3 * L : ℕ) : ℤ))
      (MvPolynomial.C (3 * Hq 2 k) * MvPolynomial.X 0 + MvPolynomial.C (2 * Hq 3 k) * MvPolynomial.X 1 : MP) := by
    refine GV.add (GV_CX_nat _ _ _ ?_) (GV_CX_nat _ _ _ ?_)
    · rw [show (p : ℚ) ^ (3 * L) * (3 * Hq 2 k) = 3 * ((p : ℚ) ^ (3 * L) * Hq 2 k) by ring]
      exact (LocRing p).mul_mem l3 (Hq_scaled_mem' 2 3 k L (by norm_num) hlk)
    · rw [show (p : ℚ) ^ (3 * L) * (2 * Hq 3 k) = 2 * ((p : ℚ) ^ (3 * L) * Hq 3 k) by ring]
      exact (LocRing p).mul_mem l2 (Hq_scaled_mem' 3 3 k L le_rfl hlk)
  have g12 := (g1.mul g2).mono (e' := -((4 * L : ℕ) : ℤ)) (by push_cast; omega)
  have g3 : GV p (-((4 * L : ℕ) : ℤ))
      (MvPolynomial.X 2 - MvPolynomial.C (Hq 3 k) * MvPolynomial.X 0 -
        MvPolynomial.C (Hq 4 k) * MvPolynomial.X 1 : MP) := by
    refine GV.sub (GV.sub ((GV.var 2).mono (by omega)) (GV_CX_nat _ _ _ ?_)) (GV_CX_nat _ _ _ ?_)
    · exact Hq_scaled_mem' 3 4 k L (by norm_num) hlk
    · exact Hq_scaled_mem' 4 4 k L le_rfl hlk
  have g6 : GV p 0 (MvPolynomial.C (6 : ℚ) : MP) := GV.const_loc (by exact_mod_cast natq_mem (p := p) 6)
  have g36 := (g6.mul g3).mono (e' := -((4 * L : ℕ) : ℤ)) (by omega)
  unfold laiV
  exact GV.add g12 g36

end Entries

section Main

open Apery Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

lemma bin_prod_eval_mem (x y k : ℕ) :
    ((bin x * bin y).eval (-(k : ℚ))) ∈ LocRing p := by
  rw [Polynomial.eval_mul]
  exact (LocRing p).mul_mem (bin_eval_negnat_mem x k) (bin_eval_negnat_mem y k)

lemma bin_prod_deriv_mem {L x y : ℕ} (hx : Nat.log p x ≤ L) (hy : Nat.log p y ≤ L) (k : ℕ) :
    (p : ℚ) ^ L * ((bin x * bin y).derivative.eval (-(k : ℚ))) ∈ LocRing p := by
  rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
    mul_add]
  refine (LocRing p).add_mem ?_ ?_
  · rw [← mul_assoc]
    exact (LocRing p).mul_mem (bin_deriv_mem hx k) (bin_eval_negnat_mem y k)
  · rw [mul_left_comm]
    exact (LocRing p).mul_mem (bin_eval_negnat_mem x k) (bin_deriv_mem hy k)

/-- Every Gram entry of `L_n` in the binomial basis has Gauss valuation `≥ -4 ⌊log_p (8n)⌋`. -/
theorem laiL_bin_GV (n L : ℕ) (hL : Nat.log p (8 * n) ≤ L) {x y : ℕ} (hx : x < 3 * n)
    (hy : y < 3 * n) : GV p (-((4 * L : ℕ) : ℤ)) (laiL n (bin x * bin y)) := by
  unfold laiL
  refine GV.sum fun k hk => ?_
  have hk6 : k ≤ 6 * n := by have := Finset.mem_range.1 hk; omega
  have hlk : Nat.log p k ≤ L := (Nat.log_mono_right (by omega)).trans hL
  have hlx : Nat.log p x ≤ L := (Nat.log_mono_right (by omega)).trans hL
  have hly : Nat.log p y ≤ L := (Nat.log_mono_right (by omega)).trans hL
  have hc : GV p 0 (MvPolynomial.C (laiCoef n k : ℚ) : MP) := GV.const_loc (natq_mem _)
  have hU := laiU_GV k L hlk
  have hPd : GV p (-(L : ℤ))
      (MvPolynomial.C ((bin x * bin y).derivative.eval (-(k : ℚ))) : MP) := by
    refine GV.const ?_
    simpa [zpow_natCast] using bin_prod_deriv_mem hlx hly k
  have hV := laiV_GV n k L hL hk6
  have hP0 : GV p 0 (MvPolynomial.C ((bin x * bin y).eval (-(k : ℚ))) : MP) :=
    GV.const_loc (bin_prod_eval_mem x y k)
  have t1 := (hU.mul hPd).mono (e' := -((4 * L : ℕ) : ℤ)) (by push_cast; omega)
  have t2 := (hV.mul hP0).mono (e' := -((4 * L : ℕ) : ℤ)) (by omega)
  have := hc.mul (t1.add t2)
  simpa using this

/-- **LC02, Lai Lemma 4.1 (1).** For every prime `p`: `v_p(J_n) ≥ -12 n ⌊log_p(8n)⌋` (Gauss valuation). -/
theorem lai_vp_lower (n : ℕ) :
    GV p (-((12 * n * Nat.log p (8 * n) : ℕ) : ℤ)) (laiJ n) := by
  rw [laiJ_eq_det_bin]
  have h := GV.det (p := p)
    (Matrix.of fun x y : Fin (3 * n) => laiL n (bin (x : ℕ) * bin (y : ℕ)))
    (fun _ => -((4 * Nat.log p (8 * n) : ℕ) : ℤ)) (fun _ => 0)
    (fun x y => by simpa using laiL_bin_GV n _ le_rfl x.2 y.2)
  refine h.mono (le_of_eq ?_)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **Lai Lemma 4.1 (2).** For `8n < p²`: `v_p(J_n) ≥ -12 n`. -/
theorem lai_vp_lower_sqrt {n : ℕ} (h8 : 8 * n < p ^ 2) : GV p (-((12 * n : ℕ) : ℤ)) (laiJ n) := by
  refine (lai_vp_lower (p := p) n).mono ?_
  have : Nat.log p (8 * n) ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have := Nat.log_lt_of_lt_pow (b := p) (x := 2) (by omega) h8
      omega
  push_cast
  have h2 : (12 * n * Nat.log p (8 * n) : ℤ) ≤ 12 * n * 1 := by
    have : ((Nat.log p (8 * n) : ℕ) : ℤ) ≤ 1 := by exact_mod_cast this
    nlinarith [Int.natCast_nonneg n]
  linarith

end Main

section Nonneg

open Apery Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

lemma laiU_GV0 (k : ℕ) (hk : k < p) : GV p 0 (laiU k) := by
  have := laiU_GV (p := p) k 0 (by simp [Nat.log_of_lt hk])
  simpa using this

/-- `c_k · (3H_{2n+k} + 2H_{6n-k} - 5H_k)` is `p`-integral for `p > 6n`: the pole of `H_{2n+k}` at `p`
is cancelled by `p ∣ C(2n+k, k)`. -/
lemma cH_mem (n k : ℕ) (hp6 : 6 * n < p) (hk : k ≤ 6 * n) :
    (laiCoef n k : ℚ) * laiH n k ∈ LocRing p := by
  have hk1 : k < p := by omega
  have h6 : 6 * n - k < p := by omega
  have hc : ((laiCoef n k : ℕ) : ℚ) ∈ LocRing p := natq_mem _
  by_cases h2 : 2 * n + k < p
  · have e1 := Hq_mem (p := p) 1 (2 * n + k) h2
    have e2 := Hq_mem (p := p) 1 (6 * n - k) h6
    have e3 := Hq_mem (p := p) 1 k hk1
    refine (LocRing p).mul_mem hc ?_
    unfold laiH
    exact (LocRing p).sub_mem
      ((LocRing p).add_mem ((LocRing p).mul_mem l3 e1) ((LocRing p).mul_mem l2 e2))
      ((LocRing p).mul_mem l5 e3)
  · have hdvd : p ∣ (2 * n + k).choose k := by
      refine Nat.Prime.dvd_choose hp.out (by omega) (by omega) (by omega)
    obtain ⟨m, hm⟩ : p ∣ laiCoef n k := by
      unfold laiCoef
      exact Dvd.dvd.mul_left (dvd_pow hdvd (by norm_num)) _
    have hlt : (2 * n + k) / p < p := by
      rw [Nat.div_lt_iff_lt_mul hp.out.pos]
      have : 2 * n + k ≤ 8 * n := by omega
      have h8 : 8 * n < p * p := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · have := hp.out.pos; positivity
        · nlinarith [hp.out.two_le]
      omega
    have e1 : (p : ℚ) ^ 1 * Hq 1 (2 * n + k) ∈ LocRing p := harm_pole_mem 1 (2 * n + k) hlt
    have e2 := Hq_mem (p := p) 1 (6 * n - k) h6
    have e3 := Hq_mem (p := p) 1 k hk1
    have hmq : (m : ℚ) ∈ LocRing p := natq_mem _
    have hpq : (p : ℚ) ∈ LocRing p := lp
    have e : (laiCoef n k : ℚ) * laiH n k =
        (m : ℚ) * (3 * ((p : ℚ) ^ 1 * Hq 1 (2 * n + k)) +
          (p : ℚ) * (2 * Hq 1 (6 * n - k) - 5 * Hq 1 k)) := by
      unfold laiH
      rw [hm]; push_cast; ring
    rw [e]
    refine (LocRing p).mul_mem hmq ((LocRing p).add_mem ((LocRing p).mul_mem l3 e1) ?_)
    exact (LocRing p).mul_mem hpq ((LocRing p).sub_mem ((LocRing p).mul_mem l2 e2)
      ((LocRing p).mul_mem l5 e3))

lemma cV_GV0 (n k : ℕ) (hp6 : 6 * n < p) (hk : k ≤ 6 * n) :
    GV p 0 (MvPolynomial.C (laiCoef n k : ℚ) * laiV n k : MP) := by
  have hk1 : k < p := by omega
  have hc : GV p 0 (MvPolynomial.C (laiCoef n k : ℚ) : MP) := GV.const_loc (natq_mem _)
  have hH : GV p 0 (MvPolynomial.C ((laiCoef n k : ℚ) * laiH n k) : MP) :=
    GV.const_loc (cH_mem n k hp6 hk)
  have gB : GV p 0 (MvPolynomial.C (3 * Hq 2 k) * MvPolynomial.X 0 +
      MvPolynomial.C (2 * Hq 3 k) * MvPolynomial.X 1 : MP) := by
    have := GV.add (GV_CX_nat (p := p) 0 (3 * Hq 2 k) 0 (by
        simpa using (LocRing p).mul_mem l3 (Hq_mem (p := p) 2 k hk1)))
      (GV_CX_nat (p := p) 0 (2 * Hq 3 k) 1 (by
        simpa using (LocRing p).mul_mem l2 (Hq_mem (p := p) 3 k hk1)))
    simpa using this
  have gD : GV p 0 (MvPolynomial.X 2 - MvPolynomial.C (Hq 3 k) * MvPolynomial.X 0 -
      MvPolynomial.C (Hq 4 k) * MvPolynomial.X 1 : MP) := by
    have := GV.sub (GV.sub (GV.var (p := p) (2 : Fin 3))
      (GV_CX_nat (p := p) 0 (Hq 3 k) 0 (by simpa using Hq_mem (p := p) 3 k hk1)))
      (GV_CX_nat (p := p) 0 (Hq 4 k) 1 (by simpa using Hq_mem (p := p) 4 k hk1))
    simpa using this
  have g6 : GV p 0 (MvPolynomial.C (6 : ℚ) : MP) := GV.const_loc (by exact_mod_cast natq_mem (p := p) 6)
  have e : (MvPolynomial.C (laiCoef n k : ℚ) * laiV n k : MP) =
      MvPolynomial.C ((laiCoef n k : ℚ) * laiH n k) *
          (MvPolynomial.C (3 * Hq 2 k) * MvPolynomial.X 0 + MvPolynomial.C (2 * Hq 3 k) * MvPolynomial.X 1) +
        MvPolynomial.C (laiCoef n k : ℚ) * (MvPolynomial.C 6 * (MvPolynomial.X 2 -
          MvPolynomial.C (Hq 3 k) * MvPolynomial.X 0 - MvPolynomial.C (Hq 4 k) * MvPolynomial.X 1)) := by
    unfold laiV
    simp only [map_mul]; ring
  rw [e]
  have := GV.add (hH.mul gB) (hc.mul (g6.mul gD))
  simpa using this

theorem laiL_bin_GV0 (n : ℕ) (hp6 : 6 * n < p) {x y : ℕ} (hx : x < 3 * n) (hy : y < 3 * n) :
    GV p 0 (laiL n (bin x * bin y)) := by
  unfold laiL
  refine GV.sum fun k hk => ?_
  have hk6 : k ≤ 6 * n := by have := Finset.mem_range.1 hk; omega
  have hc : GV p 0 (MvPolynomial.C (laiCoef n k : ℚ) : MP) := GV.const_loc (natq_mem _)
  have hU := laiU_GV0 (p := p) k (by omega)
  have hPd : GV p 0 (MvPolynomial.C ((bin x * bin y).derivative.eval (-(k : ℚ))) : MP) := by
    refine GV.const_loc ?_
    have := bin_prod_deriv_mem (p := p) (L := 0) (x := x) (y := y)
      (by simp [Nat.log_of_lt (show x < p by omega)])
      (by simp [Nat.log_of_lt (show y < p by omega)]) k
    simpa using this
  have hV := cV_GV0 n k hp6 hk6
  have hP0 : GV p 0 (MvPolynomial.C ((bin x * bin y).eval (-(k : ℚ))) : MP) :=
    GV.const_loc (bin_prod_eval_mem x y k)
  have e : (MvPolynomial.C (laiCoef n k : ℚ) *
      (laiU k * MvPolynomial.C ((bin x * bin y).derivative.eval (-(k : ℚ))) +
        laiV n k * MvPolynomial.C ((bin x * bin y).eval (-(k : ℚ)))) : MP) =
      (MvPolynomial.C (laiCoef n k : ℚ) * laiU k) *
          MvPolynomial.C ((bin x * bin y).derivative.eval (-(k : ℚ))) +
        (MvPolynomial.C (laiCoef n k : ℚ) * laiV n k) *
          MvPolynomial.C ((bin x * bin y).eval (-(k : ℚ))) := by ring
  rw [e]
  have := GV.add ((hc.mul hU).mul hPd) (hV.mul hP0)
  simpa using this

/-- **Lai Lemma 4.1 (3).** For `p > 6n`: `v_p(J_n) ≥ 0`. -/
theorem lai_vp_nonneg {n : ℕ} (hp6 : 6 * n < p) : GV p 0 (laiJ n) := by
  rw [laiJ_eq_det_bin]
  have h := GV.det (p := p)
    (Matrix.of fun x y : Fin (3 * n) => laiL n (bin (x : ℕ) * bin (y : ℕ)))
    (fun _ => 0) (fun _ => 0)
    (fun x y => by simpa using laiL_bin_GV0 n hp6 x.2 y.2)
  simpa using h

end Nonneg

section SmallPrimes

open CatalanCore.NT.WeightedPrimeSum

/-- The `p`-power denominator that Lemma 4.1 (1) clears at the primes `p ≤ δ n`:
`∏_{p ≤ δ n} p^{12 n ⌊log_p(8n)⌋}`. -/
noncomputable def laiSmallDen (δ : ℝ) (n : ℕ) : ℕ :=
  ∏ p ∈ smallPrimes δ n, p ^ (12 * n * Nat.log p (8 * n))

theorem laiSmallDen_pos (δ : ℝ) (n : ℕ) : 0 < laiSmallDen δ n := by
  unfold laiSmallDen
  refine Finset.prod_pos fun p hp => ?_
  exact pow_pos (Nat.pos_of_ne_zero (fun h => by
    simp [smallPrimes, h] at hp)) _

theorem log_laiSmallDen (δ : ℝ) (n : ℕ) :
    Real.log (laiSmallDen δ n : ℝ) =
      ∑ p ∈ smallPrimes δ n, ((12 * n * Nat.log p (8 * n) : ℕ) : ℝ) * Real.log (p : ℝ) := by
  unfold laiSmallDen
  rw [Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have : p ≠ 0 := fun h => by simp [smallPrimes, h] at hp
    exact_mod_cast pow_ne_zero _ this

/-- **LC22.** The primes `p ≤ δ n` contribute at most `(12 δ + ε) n²` to `log` of the denominator of
`J_n` that Lemma 4.1 (1) clears (Lai (5.6)-(5.7)). -/
theorem lai_small_primes {δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, Real.log (laiSmallDen δ n : ℝ) ≤ (12 * δ + ε) * (n : ℝ) ^ 2 := by
  have := small_primes_cost hδ (fun n p => ((12 * n * Nat.log p (8 * n) : ℕ) : ℝ))
    (fun n p _ _ => by push_cast; exact le_refl _) hε
  filter_upwards [this] with n hn
  rw [log_laiSmallDen]
  exact hn

end SmallPrimes




end CatalanCore.Lai

#print axioms CatalanCore.Lai.laiJ_eq_det_bin
#print axioms CatalanCore.Lai.lai_vp_lower
#print axioms CatalanCore.Lai.lai_vp_lower_sqrt
#print axioms CatalanCore.Lai.lai_vp_nonneg
#print axioms CatalanCore.Lai.lai_small_primes
