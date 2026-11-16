module

public import CatalanCore.Zeta5.Port.Degree
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Data.Matrix.Mul

@[expose] public section

/-!
# The residue identity (ledger ZR01)

With `K = 40 n`, `N = 3 n`, `h = 37 n`, `u_j = j/K`, `p(t) = q(K² t)` and `A_K = K^(12N-2K+6)`:

  `qᵀ M_K q = A_K Σ_{N < j ≤ K} r_j p(-u_j²)²`,
  `r_j = u_j⁴ ∏_{l ≤ N} (u_l² - u_j²)^5 / ∏_{N < k ≤ K, k ≠ j} (u_k² - u_j²)`,

where `M_K = [X] G_K` is the matrix of `X`-coefficients, from `coeff_G_one`
(`M_K = Vᵀ diag(w) V`, Vandermonde of the nodes `-j²`).
-/

namespace CatalanCore.Zeta5.Rho

open Apery Polynomial Finset Matrix

/-- `u_j = j / K`, `K = 40 n`. -/
noncomputable def uu (n j : ℕ) : ℝ := (j : ℝ) / (40 * n : ℝ)

/-- `r_j` of ZR01. -/
noncomputable def rj (n j : ℕ) : ℝ :=
  uu n j ^ 4 * (∏ l ∈ Icc 1 (3 * n), (uu n l ^ 2 - uu n j ^ 2) ^ 5) /
    ∏ k ∈ (Ioc (3 * n) (40 * n)).erase j, (uu n k ^ 2 - uu n j ^ 2)

/-- `A_K = K^(12N + 6) / K^(2K)`, i.e. `K^(12N-2K+6)`. -/
noncomputable def AK (n : ℕ) : ℝ := (40 * n : ℝ) ^ (12 * (3 * n) + 6) / (40 * n : ℝ) ^ (2 * (40 * n))

/-- The matrix `M_K = [X] G_K` of `X`-coefficients, over `ℝ`. -/
noncomputable def M0 (n : ℕ) : Matrix (Fin (37 * n)) (Fin (37 * n)) ℝ :=
  Matrix.of fun i j => (((G n i j).coeff 1 : ℚ) : ℝ)

/-- `p(t) = q(K² t)` for `q(X) = Σ x_i X^i`. -/
noncomputable def Pfun (n : ℕ) (x : Fin (37 * n) → ℝ) (t : ℝ) : ℝ :=
  ∑ i, x i * ((40 * n : ℝ) ^ 2 * t) ^ (i : ℕ)

/-- `p` as a real polynomial in `t`. -/
noncomputable def Ppoly (n : ℕ) (x : Fin (37 * n) → ℝ) : ℝ[X] :=
  ∑ i : Fin (37 * n), C (x i * ((40 * n : ℝ) ^ 2) ^ (i : ℕ)) * X ^ (i : ℕ)

theorem eval_Ppoly (n : ℕ) (x : Fin (37 * n) → ℝ) (t : ℝ) :
    (Ppoly n x).eval t = Pfun n x t := by
  simp only [Ppoly, Pfun, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_pow]; ring

theorem natDegree_Ppoly_lt (n : ℕ) (hn : 0 < n) (x : Fin (37 * n) → ℝ) :
    (Ppoly n x).natDegree < 37 * n := by
  have h1 : (Ppoly n x).natDegree ≤ 37 * n - 1 := by
    unfold Ppoly
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    have := i.isLt
    omega
  omega

/-- Entry formula `(M_K)_{ij} = Σ_k node_k^i w_k node_k^j`. -/
theorem coeff_entry (n : ℕ) (i j : Fin (37 * n)) :
    (G n i j).coeff 1 = ∑ k : Fin (37 * n), node n k ^ (i : ℕ) * weight n k * node n k ^ (j : ℕ) := by
  have h := congrFun (congrFun (coeff_G_one n) i) j
  simp only [Matrix.of_apply] at h
  rw [Matrix.mul_apply] at h
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
    vandermonde_apply] at h
  rw [h]

theorem quadForm_nodes (n : ℕ) (x : Fin (37 * n) → ℝ) :
    x ⬝ᵥ (M0 n *ᵥ x) =
      ∑ k : Fin (37 * n), (weight n k : ℝ) *
        (∑ i : Fin (37 * n), x i * (node n k : ℝ) ^ (i : ℕ)) ^ 2 := by
  set F : Fin (37 * n) → Fin (37 * n) → Fin (37 * n) → ℝ := fun i j k =>
    x i * ((node n k : ℝ) ^ (i : ℕ) * (weight n k : ℝ) * (node n k : ℝ) ^ (j : ℕ)) * x j with hF
  have hL : x ⬝ᵥ (M0 n *ᵥ x) = ∑ i, ∑ j, ∑ k, F i j k := by
    simp only [dotProduct, Matrix.mulVec, M0, Matrix.of_apply, coeff_entry]
    push_cast
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine sum_congr rfl fun k _ => ?_
    simp only [hF]; ring
  have hR : ∀ k, (weight n k : ℝ) *
        (∑ i : Fin (37 * n), x i * (node n k : ℝ) ^ (i : ℕ)) ^ 2 = ∑ i, ∑ j, F i j k := by
    intro k
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [hF]; ring
  rw [hL, sum_congr rfl fun k _ => hR k]
  calc ∑ i, ∑ j, ∑ k, F i j k = ∑ i, ∑ k, ∑ j, F i j k :=
        sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem sum_fin_eq_sum_Ioc (n : ℕ) (f : ℕ → ℝ) :
    ∑ k : Fin (37 * n), f (3 * n + 1 + (k : ℕ)) = ∑ j ∈ Ioc (3 * n) (40 * n), f j := by
  rw [Fin.sum_univ_eq_sum_range (fun k => f (3 * n + 1 + k)) (37 * n)]
  have h1 := Finset.sum_Ico_eq_sum_range f (3 * n + 1) (40 * n + 1)
  rw [show 40 * n + 1 - (3 * n + 1) = 37 * n by omega] at h1
  rw [← h1]
  congr 1
  ext j; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega


theorem erase_split {K N j : ℕ} (hNj : N < j) (hjK : j ≤ K) :
    (Icc 1 K).erase j = Icc 1 N ∪ (Ioc N K).erase j := by
  ext i
  simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
  omega

theorem real_core (K N j : ℕ) (hK : 0 < K) (hNj : N < j) (hjK : j ≤ K) :
    (∏ l ∈ Icc 1 N, (((l : ℝ) ^ 2 - (j : ℝ) ^ 2))) ^ 6 * (j : ℝ) ^ 4 /
        ∏ i ∈ (Icc 1 K).erase j, ((i : ℝ) ^ 2 - (j : ℝ) ^ 2) =
      (K : ℝ) ^ (12 * N + 6) / (K : ℝ) ^ (2 * K) *
        (((j : ℝ) / K) ^ 4 *
          (∏ l ∈ Icc 1 N, ((((l : ℝ) / K) ^ 2 - ((j : ℝ) / K) ^ 2)) ^ 5) /
          ∏ k ∈ (Ioc N K).erase j, (((k : ℝ) / K) ^ 2 - ((j : ℝ) / K) ^ 2)) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  set Kr : ℝ := (K : ℝ) with hKrdef
  have e1 : ∀ l : ℕ, ((l : ℝ) ^ 2 - (j : ℝ) ^ 2) =
      Kr ^ 2 * (((l : ℝ) / Kr) ^ 2 - ((j : ℝ) / Kr) ^ 2) := fun l => by field_simp
  have hjmem : j ∈ Ioc N K := Finset.mem_Ioc.mpr ⟨hNj, hjK⟩
  set A : ℝ := ∏ l ∈ Icc 1 N, (((l : ℝ) / Kr) ^ 2 - ((j : ℝ) / Kr) ^ 2) with hA
  set B : ℝ := ∏ k ∈ (Ioc N K).erase j, (((k : ℝ) / Kr) ^ 2 - ((j : ℝ) / Kr) ^ 2) with hB
  have hP1 : ∏ l ∈ Icc 1 N, ((l : ℝ) ^ 2 - (j : ℝ) ^ 2) = Kr ^ (2 * N) * A := by
    rw [Finset.prod_congr rfl (fun l _ => e1 l), Finset.prod_mul_distrib, Finset.prod_const,
      Nat.card_Icc, ← pow_mul]
    simp [hA]
  have hP2 : ∏ k ∈ (Ioc N K).erase j, ((k : ℝ) ^ 2 - (j : ℝ) ^ 2) =
      Kr ^ (2 * (K - N - 1)) * B := by
    rw [Finset.prod_congr rfl (fun l _ => e1 l), Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_erase_of_mem hjmem, Nat.card_Ioc, ← pow_mul]
  have hsplit : ∏ i ∈ (Icc 1 K).erase j, ((i : ℝ) ^ 2 - (j : ℝ) ^ 2) =
      (Kr ^ (2 * N) * A) * (Kr ^ (2 * (K - N - 1)) * B) := by
    rw [erase_split hNj hjK, Finset.prod_union, hP1, hP2]
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_Ioc] at hi hi'
    omega
  have hA0 : A ≠ 0 := by
    rw [hA]
    refine Finset.prod_ne_zero_iff.mpr fun l hl => ?_
    have hl' := Finset.mem_Icc.mp hl
    have : (l : ℝ) < j := by exact_mod_cast (by omega : l < j)
    have h0 : (0 : ℝ) ≤ l := by positivity
    intro h
    have h2 : ((l : ℝ) / Kr) ^ 2 = ((j : ℝ) / Kr) ^ 2 := by linarith
    have h3 : ((l : ℝ) / Kr) = ((j : ℝ) / Kr) := by
      have := (sq_eq_sq₀ (div_nonneg h0 hKr.le) (div_nonneg (by positivity) hKr.le)).mp h2
      exact this
    have := (div_left_inj' hKr.ne').mp h3
    linarith
  have hB0 : B ≠ 0 := by
    rw [hB]
    refine Finset.prod_ne_zero_iff.mpr fun k hk => ?_
    have hk' := Finset.mem_erase.mp hk
    have hk2 := Finset.mem_Ioc.mp hk'.2
    have hkj : (k : ℝ) ≠ j := by exact_mod_cast hk'.1
    have h0 : (0 : ℝ) ≤ k := by positivity
    have h1 : (0 : ℝ) ≤ j := by positivity
    intro h
    have h2 : ((k : ℝ) / Kr) ^ 2 = ((j : ℝ) / Kr) ^ 2 := by linarith
    have h3 : ((k : ℝ) / Kr) = ((j : ℝ) / Kr) :=
      (sq_eq_sq₀ (div_nonneg h0 hKr.le) (div_nonneg h1 hKr.le)).mp h2
    exact hkj ((div_left_inj' hKr.ne').mp h3)
  have hexp : Kr ^ (2 * K) = Kr ^ (2 * N) * Kr ^ (2 * (K - N - 1)) * Kr ^ 2 := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hpow : ∏ l ∈ Icc 1 N, ((((l : ℝ) / Kr) ^ 2 - ((j : ℝ) / Kr) ^ 2)) ^ 5 = A ^ 5 := by
    rw [Finset.prod_pow]
  rw [hsplit, hP1, hpow, hexp]
  have hq : ((j : ℝ) / Kr) ^ 4 = (j : ℝ) ^ 4 / Kr ^ 4 := by rw [div_pow]
  have h12 : Kr ^ (12 * N + 6) = Kr ^ (12 * N) * Kr ^ 4 * Kr ^ 2 := by
    rw [← pow_add, ← pow_add]
  rw [hq, h12, show Kr ^ (12 * N) = (Kr ^ (2 * N)) ^ 6 by rw [← pow_mul]; congr 1; omega]
  have : Kr ^ (2 * N) ≠ 0 := pow_ne_zero _ hKr.ne'
  have : Kr ^ (2 * (K - N - 1)) ≠ 0 := pow_ne_zero _ hKr.ne'
  field_simp


theorem mem_Ioc_of_fin (n : ℕ) (k : Fin (37 * n)) : 3 * n + 1 + (k : ℕ) ∈ Ioc (3 * n) (40 * n) := by
  have := k.isLt
  rw [Finset.mem_Ioc]; omega

theorem weight_real (n : ℕ) (k : Fin (37 * n)) :
    (weight n k : ℝ) =
      (∏ l ∈ Icc 1 (3 * n), (((l : ℝ) ^ 2 - ((3 * n + 1 + (k : ℕ) : ℕ) : ℝ) ^ 2))) ^ 6 *
        ((3 * n + 1 + (k : ℕ) : ℕ) : ℝ) ^ 4 /
      ∏ i ∈ (Icc 1 (40 * n)).erase (3 * n + 1 + (k : ℕ)),
        ((i : ℝ) ^ 2 - ((3 * n + 1 + (k : ℕ) : ℕ) : ℝ) ^ 2) := by
  have hj : 3 * n + 1 + (k : ℕ) ∈ Icc 1 (40 * n) := by
    have := k.isLt
    rw [Finset.mem_Icc]; omega
  unfold weight
  have hnode : node n k = -((3 * n + 1 + (k : ℕ) : ℕ) : ℚ) ^ 2 := rfl
  rw [hnode, eval_derivative_D hj, eval_D]
  push_cast
  congr 2
  · refine congrArg (· ^ 6) (prod_congr rfl fun l _ => ?_)
    push_cast; ring

theorem weight_eq (n : ℕ) (hn : 0 < n) (k : Fin (37 * n)) :
    (weight n k : ℝ) = AK n * rj n (3 * n + 1 + (k : ℕ)) := by
  have hmem := Finset.mem_Ioc.mp (mem_Ioc_of_fin n k)
  rw [weight_real, real_core (40 * n) (3 * n) (3 * n + 1 + (k : ℕ)) (by omega) hmem.1 hmem.2]
  simp only [AK, rj, uu]
  push_cast
  rfl

theorem node_eval (n : ℕ) (hn : 0 < n) (x : Fin (37 * n) → ℝ) (k : Fin (37 * n)) :
    ∑ i : Fin (37 * n), x i * (node n k : ℝ) ^ (i : ℕ) =
      Pfun n x (-(uu n (3 * n + 1 + (k : ℕ))) ^ 2) := by
  unfold Pfun
  refine sum_congr rfl fun i _ => ?_
  congr 2
  simp only [node, uu]
  push_cast
  have : (40 * (n : ℝ)) ≠ 0 := by positivity
  field_simp

/-- **ZR01.**  The residue identity for the quadratic form of `M_K = [X] G_K`. -/
theorem residue_identity (n : ℕ) (hn : 0 < n) (x : Fin (37 * n) → ℝ) :
    x ⬝ᵥ (M0 n *ᵥ x) =
      AK n * ∑ j ∈ Ioc (3 * n) (40 * n), rj n j * (Pfun n x (-(uu n j) ^ 2)) ^ 2 := by
  rw [quadForm_nodes, Finset.mul_sum, ← sum_fin_eq_sum_Ioc n
    (fun j => AK n * (rj n j * (Pfun n x (-(uu n j) ^ 2)) ^ 2))]
  refine sum_congr rfl fun k _ => ?_
  rw [node_eval n hn, weight_eq n hn]
  ring

end CatalanCore.Zeta5.Rho
