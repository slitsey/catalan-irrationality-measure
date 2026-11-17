module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Matrix.Block
public import CatalanCore.Arith.Hybrid.RankGLE
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

/-! # `CatalanCore.Lai.NVCore`: generic nonvanishing of node-block Hankel determinants modulo `ℓ`. -/


/-!
# Gram criterion for Hankel determinants (generic)

For a linear functional `L : K[X] → K` on polynomials over a field, the Hankel matrix
`H_{ij} = L(X^{i+j})`, `i, j < N`, has nonzero determinant as soon as some family `φ : ι → K[X]`
of `N` polynomials of degree `< N` has an invertible Gram matrix `L(φ_x φ_y)`.  (Linear independence of
the family is not assumed: it is a consequence.)  No prime, no weight, no design is involved.
-/

open Polynomial Matrix

namespace CatalanCore.Lai.NV

variable {K : Type*} [Field K]

theorem eq_sum_fin {N : ℕ} (f : K[X]) (hf : f.degree < N) :
    f = ∑ i : Fin N, C (f.coeff i) * X ^ (i : ℕ) := by
  by_cases h0 : f = 0
  · subst h0; simp
  · have hn : f.natDegree < N := (natDegree_lt_iff_degree_lt h0).2 hf
    conv_lhs => rw [as_sum_range' f N hn]
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i) N]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [C_mul_X_pow_eq_monomial]

theorem L_mul_eq {N : ℕ} (L : K[X] →ₗ[K] K) (f g : K[X]) (hf : f.degree < N) (hg : g.degree < N) :
    L (f * g) = ∑ i : Fin N, ∑ j : Fin N, f.coeff i * g.coeff j * L (X ^ ((i : ℕ) + j)) := by
  conv_lhs => rw [eq_sum_fin f hf, eq_sum_fin g hg]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : C (f.coeff i) * X ^ (i : ℕ) * (C (g.coeff j) * X ^ (j : ℕ)) =
      (f.coeff i * g.coeff j) • (X ^ ((i : ℕ) + j) : K[X]) := by
    rw [smul_eq_C_mul, C_mul, pow_add]; ring
  rw [this, map_smul, smul_eq_mul]

/-- The Gram matrix factors through the coefficient matrix: `Gram = T H Tᵀ`. -/
theorem gram_eq_fin {N : ℕ} (L : K[X] →ₗ[K] K) (φ : Fin N → K[X]) (hφ : ∀ x, (φ x).degree < N) :
    (Matrix.of fun x y => L (φ x * φ y)) =
      (Matrix.of fun x (j : Fin N) => (φ x).coeff j) *
        (Matrix.of fun i j : Fin N => L (X ^ ((i : ℕ) + j))) *
        (Matrix.of fun x (j : Fin N) => (φ x).coeff j).transpose := by
  ext x y
  rw [Matrix.of_apply, L_mul_eq L _ _ (hφ x) (hφ y), Matrix.mul_apply]
  simp_rw [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

theorem det_gram_fin {N : ℕ} (L : K[X] →ₗ[K] K) (φ : Fin N → K[X]) (hφ : ∀ x, (φ x).degree < N) :
    (Matrix.of fun x y => L (φ x * φ y)).det =
      (Matrix.of fun x (j : Fin N) => (φ x).coeff j).det ^ 2 *
        (Matrix.of fun i j : Fin N => L (X ^ ((i : ℕ) + j))).det := by
  rw [gram_eq_fin L φ hφ, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- **Gram criterion**, index `Fin N`. -/
theorem hankel_det_ne_zero_of_gram_fin {N : ℕ} (L : K[X] →ₗ[K] K) (φ : Fin N → K[X])
    (hφ : ∀ x, (φ x).degree < N)
    (hG : (Matrix.of fun x y => L (φ x * φ y)).det ≠ 0) :
    (Matrix.of fun i j : Fin N => L (X ^ ((i : ℕ) + j))).det ≠ 0 := by
  intro h
  apply hG
  rw [det_gram_fin L φ hφ, h, mul_zero]

/-- **Gram criterion**, arbitrary finite index set with an equivalence to `Fin N`. -/
theorem hankel_det_ne_zero_of_gram {N : ℕ} (L : K[X] →ₗ[K] K) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (e : ι ≃ Fin N) (φ : ι → K[X]) (hφ : ∀ x, (φ x).degree < N)
    (hG : (Matrix.of fun x y => L (φ x * φ y)).det ≠ 0) :
    (Matrix.of fun i j : Fin N => L (X ^ ((i : ℕ) + j))).det ≠ 0 := by
  refine hankel_det_ne_zero_of_gram_fin L (fun i => φ (e.symm i)) (fun i => hφ _) ?_
  have := Matrix.det_submatrix_equiv_self e.symm (Matrix.of fun x y => L (φ x * φ y))
  rw [← this] at hG
  exact hG

end CatalanCore.Lai.NV


/-!
# The Hermite lattice of Lai's nonvanishing theorem, over `ℤ_(ℓ)` (generic in `s ≤ ℓ`)

For `i < s`, `F_i(t) = ∏_{μ<s, μ≠i}(t + μ)/(μ - i)` has coefficients in `ℤ_(ℓ)` as soon as `s ≤ ℓ`, and
`P̃_i = (1 - 2 c_i (t + i)) F_i²`, `Q̃_i = (t + i) F_i²` (with `c_i = F_i'(-i)`) interpolate the Hermite
data at the nodes `-μ`, `μ < s`:
`(P̃_i, P̃_i') = (δ, 0)` and `(Q̃_i, Q̃_i') = (0, δ)`, with `δ = [μ = i]`.
Nothing here depends on Lai's design.
-/

open Polynomial Finset CatalanCore.Basic

namespace CatalanCore.Lai.NV

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The inverse of the Lagrange denominator. -/
noncomputable def lagNorm (s i : ℕ) : LocRing ℓ :=
  Ring.inverse (∏ ν ∈ (range s).erase i, ((ν : LocRing ℓ) - (i : LocRing ℓ)))

/-- `F_i`. -/
noncomputable def lag (s i : ℕ) : (LocRing ℓ)[X] :=
  C (lagNorm ℓ s i) * ∏ ν ∈ (range s).erase i, (X + C (ν : LocRing ℓ))

/-- `c_i = F_i'(-i)`. -/
noncomputable def lagC (s i : ℕ) : LocRing ℓ := (lag ℓ s i).derivative.eval (-(i : LocRing ℓ))

/-- `P̃_i = (1 - 2 c_i (t + i)) F_i²`. -/
noncomputable def Pt (s i : ℕ) : (LocRing ℓ)[X] :=
  (1 - C (2 * lagC ℓ s i) * (X + C (i : LocRing ℓ))) * lag ℓ s i ^ 2

/-- `Q̃_i = (t + i) F_i²`. -/
noncomputable def Qt (s i : ℕ) : (LocRing ℓ)[X] := (X + C (i : LocRing ℓ)) * lag ℓ s i ^ 2

variable {ℓ}

theorem isUnit_intCast {z : ℤ} (hz : ¬ (ℓ : ℤ) ∣ z) : IsUnit ((z : ℤ) : LocRing ℓ) := by
  have hz0 : z ≠ 0 := fun h => hz (h ▸ dvd_zero _)
  have hmem : ((z : ℚ))⁻¹ ∈ LocRing ℓ := by
    rw [mem_locRing, Rat.inv_intCast_den, if_neg hz0]
    intro hd
    exact hz (Int.natCast_dvd.2 hd)
  refine IsUnit.of_mul_eq_one (⟨(z : ℚ)⁻¹, hmem⟩ : LocRing ℓ) ?_
  apply Subtype.ext
  simp [hz0]

theorem isUnit_nat_sub {s i ν : ℕ} (hs : s ≤ ℓ) (hi : i < s) (hν : ν < s) (hne : ν ≠ i) :
    IsUnit ((ν : LocRing ℓ) - (i : LocRing ℓ)) := by
  have h : ((ν : LocRing ℓ) - (i : LocRing ℓ)) = (((ν : ℤ) - (i : ℤ) : ℤ) : LocRing ℓ) := by
    push_cast; ring
  rw [h]
  refine isUnit_intCast fun hd => hne ?_
  have h0 := Int.eq_zero_of_abs_lt_dvd hd (by
    rw [abs_lt]; constructor <;> omega)
  omega

theorem isUnit_lagDen {s i : ℕ} (hs : s ≤ ℓ) (hi : i < s) :
    IsUnit (∏ ν ∈ (range s).erase i, ((ν : LocRing ℓ) - (i : LocRing ℓ))) := by
  rw [IsUnit.prod_iff]
  intro ν hν
  obtain ⟨hne, hν'⟩ := Finset.mem_erase.1 hν
  exact isUnit_nat_sub hs hi (Finset.mem_range.1 hν') hne

theorem lag_eval_node {s i μ : ℕ} (hs : s ≤ ℓ) (hi : i < s) (hμ : μ < s) :
    (lag ℓ s i).eval (-(μ : LocRing ℓ)) = if μ = i then 1 else 0 := by
  unfold lag
  rw [eval_mul, eval_C, eval_prod]
  simp only [eval_add, eval_X, eval_C]
  by_cases h : μ = i
  · subst h
    rw [if_pos rfl]
    have : ∏ ν ∈ (range s).erase μ, (-(μ : LocRing ℓ) + (ν : LocRing ℓ)) =
        ∏ ν ∈ (range s).erase μ, ((ν : LocRing ℓ) - (μ : LocRing ℓ)) :=
      Finset.prod_congr rfl fun ν _ => by ring
    rw [this]
    unfold lagNorm
    exact Ring.inverse_mul_cancel _ (isUnit_lagDen hs hi)
  · rw [if_neg h]
    have hm : μ ∈ (range s).erase i := Finset.mem_erase.2 ⟨h, Finset.mem_range.2 hμ⟩
    rw [Finset.prod_eq_zero hm (by ring), mul_zero]

theorem lag_sq_deriv_node {s i μ : ℕ} (hs : s ≤ ℓ) (hi : i < s) (hμ : μ < s) (h : μ ≠ i) :
    (lag ℓ s i).eval (-(μ : LocRing ℓ)) = 0 ∧
      (lag ℓ s i ^ 2).derivative.eval (-(μ : LocRing ℓ)) = 0 := by
  have h0 := lag_eval_node hs hi hμ
  rw [if_neg h] at h0
  refine ⟨h0, ?_⟩
  rw [derivative_pow]
  simp [h0]

theorem Pt_eval_node {s i μ : ℕ} (hs : s ≤ ℓ) (hi : i < s) (hμ : μ < s) :
    (Pt ℓ s i).eval (-(μ : LocRing ℓ)) = if μ = i then 1 else 0 := by
  unfold Pt
  rw [eval_mul, eval_pow, lag_eval_node hs hi hμ]
  by_cases h : μ = i
  · subst h; simp
  · simp [h]

theorem Qt_eval_node {s i μ : ℕ} (hs : s ≤ ℓ) (hi : i < s) (hμ : μ < s) :
    (Qt ℓ s i).eval (-(μ : LocRing ℓ)) = 0 := by
  unfold Qt
  rw [eval_mul, eval_pow, lag_eval_node hs hi hμ]
  by_cases h : μ = i
  · subst h; simp
  · simp [h]

theorem Pt_deriv_node {s i μ : ℕ} (hs : s ≤ ℓ) (hi : i < s) (hμ : μ < s) :
    (Pt ℓ s i).derivative.eval (-(μ : LocRing ℓ)) = 0 := by
  by_cases h : μ = i
  · subst h
    have h1 := lag_eval_node hs hi hμ
    rw [if_pos rfl] at h1
    unfold Pt
    rw [derivative_mul, eval_add, eval_mul, eval_mul, eval_pow, h1, derivative_pow]
    simp only [derivative_sub, derivative_one, derivative_mul, derivative_C, derivative_add,
      derivative_X, eval_sub, eval_one, eval_add, eval_mul, eval_C, eval_X, eval_zero, zero_mul,
      zero_add, eval_pow, h1, eval_natCast, derivative_X_pow, eval_ofNat]
    unfold lagC
    simp
  · obtain ⟨h0, h2⟩ := lag_sq_deriv_node hs hi hμ h
    unfold Pt
    rw [derivative_mul, eval_add, eval_mul, eval_mul, h2, eval_pow, h0]
    simp

theorem Qt_deriv_node {s i μ : ℕ} (hs : s ≤ ℓ) (hi : i < s) (hμ : μ < s) :
    (Qt ℓ s i).derivative.eval (-(μ : LocRing ℓ)) = if μ = i then 1 else 0 := by
  by_cases h : μ = i
  · subst h
    have h1 := lag_eval_node hs hi hμ
    rw [if_pos rfl] at h1
    unfold Qt
    rw [derivative_mul, eval_add, eval_mul, eval_mul, eval_pow, h1, if_pos rfl]
    simp [derivative_pow, h1]
  · obtain ⟨h0, h2⟩ := lag_sq_deriv_node hs hi hμ h
    unfold Qt
    rw [derivative_mul, eval_add, eval_mul, eval_mul, h2, eval_pow, h0, if_neg h]
    simp

theorem natDegree_lag_le (s i : ℕ) (hi : i < s) : (lag ℓ s i).natDegree ≤ s - 1 := by
  unfold lag
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_prod_of_monic _ _ fun _ _ => (monic_X_add_C _)]
  simp only [natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
  have := Finset.card_erase_of_mem (s := range s) (a := i) (Finset.mem_range.2 hi)
  simp only [Finset.card_range] at this
  omega

theorem natDegree_Pt_le (s i : ℕ) (hi : i < s) : (Pt ℓ s i).natDegree ≤ 2 * s - 1 := by
  unfold Pt
  have h1 : (1 - C (2 * lagC ℓ s i) * (X + C (i : LocRing ℓ))).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    refine (natDegree_C_mul_le _ _).trans ?_
    exact (natDegree_X_add_C (i : LocRing ℓ)).le
  have h2 : (lag ℓ s i ^ 2).natDegree ≤ 2 * (s - 1) :=
    natDegree_pow_le.trans (by have := natDegree_lag_le (ℓ := ℓ) s i hi; omega)
  refine natDegree_mul_le.trans ?_
  omega

theorem natDegree_Qt_le (s i : ℕ) (hi : i < s) : (Qt ℓ s i).natDegree ≤ 2 * s - 1 := by
  unfold Qt
  have h1 : (X + C (i : LocRing ℓ)).natDegree ≤ 1 := (natDegree_X_add_C (i : LocRing ℓ)).le
  have h2 : (lag ℓ s i ^ 2).natDegree ≤ 2 * (s - 1) :=
    natDegree_pow_le.trans (by have := natDegree_lag_le (ℓ := ℓ) s i hi; omega)
  refine natDegree_mul_le.trans ?_
  omega

end CatalanCore.Lai.NV


/-!
# Nonvanishing of node-block Hankel determinants modulo `ℓ` (generic)

Let `L f = ∑_{k ≤ N} w_k (u_k f'(-k) + e_k f(-k))` be a functional on `ℚ[X]` with nodes `-k`,
`0 ≤ k < ℓ + s` (`s ≤ ℓ`), weights `w_k ∈ ℤ_(ℓ)` and `ℓ³ u_k = U_k`, `ℓ⁴ e_k = E_k` in `ℤ_(ℓ)`.
Three classes of nodes:
* low `k < s`: `ℓ² ∣ U_k`, `ℓ ∣ E_k`;
* mid `s ≤ k < ℓ`: `ℓ² ∣ w_k`, `ℓ² ∣ U_k`, `ℓ ∣ E_k`;
* high `k = ℓ + μ`, `μ < s`: `w_k` a unit and `U_k ≡ -ε` modulo `ℓ²`, with `ε` a unit.

Then the Hankel determinant `det [L(X^{i+j})]_{i,j < 2s}` is nonzero.  The proof evaluates the Gram
matrix of `L` on the Hermite lattice `ℓ²P̃_i, ℓQ̃_i` modulo `ℓ`: it is block diagonal with blocks of
determinant `-w̄² ε̄²`.
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid Matrix

namespace CatalanCore.Lai.NV

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- The node functional. -/
noncomputable def nodeL (N : ℕ) (w u e : ℕ → ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  ∑ k ∈ range (N + 1), ((w k * u k) • (Polynomial.leval (-(k : ℚ)) ∘ₗ Polynomial.derivative) +
    (w k * e k) • Polynomial.leval (-(k : ℚ)))

theorem nodeL_apply (N : ℕ) (w u e : ℕ → ℚ) (f : ℚ[X]) :
    nodeL N w u e f = ∑ k ∈ range (N + 1),
      w k * (u k * f.derivative.eval (-(k : ℚ)) + e k * f.eval (-(k : ℚ))) := by
  unfold nodeL
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    Polynomial.leval_apply, smul_eq_mul]
  ring

section Residue

theorem redQ_natCast_self : redQ ℓ (ℓ : LocRing ℓ) = 0 :=
  (redQ_eq_zero_iff ℓ _).2 dvd_rfl

theorem redQ_eq_zero_of_dvd {x : LocRing ℓ} (h : (ℓ : LocRing ℓ) ∣ x) : redQ ℓ x = 0 :=
  (redQ_eq_zero_iff ℓ x).2 h

theorem redQ_eq_zero_of_sq_dvd {x : LocRing ℓ} (h : (ℓ : LocRing ℓ) ^ 2 ∣ x) : redQ ℓ x = 0 :=
  redQ_eq_zero_of_dvd (dvd_trans (dvd_pow_self _ (by norm_num)) h)

end Residue

section KLevel

variable (ℓ)

theorem l_ne_zero : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero

variable {ℓ}

theorem T_PP (w U E pv pd pv' pd' : LocRing ℓ) (u e : ℚ)
    (hu : (ℓ : ℚ) ^ 3 * u = (U : ℚ)) (he : (ℓ : ℚ) ^ 4 * e = (E : ℚ)) :
    (w : ℚ) * (u * (((ℓ : ℚ) ^ 2 * pd) * ((ℓ : ℚ) ^ 2 * pv') +
        ((ℓ : ℚ) ^ 2 * pv) * ((ℓ : ℚ) ^ 2 * pd')) + e * (((ℓ : ℚ) ^ 2 * pv) * ((ℓ : ℚ) ^ 2 * pv'))) =
      ((w * ((ℓ : LocRing ℓ) * U * (pd * pv' + pv * pd') + E * pv * pv') : LocRing ℓ) : ℚ) := by
  have hl := l_ne_zero ℓ
  have hu' : u = (U : ℚ) / (ℓ : ℚ) ^ 3 := by
    rw [eq_div_iff (pow_ne_zero _ hl)]; linarith
  have he' : e = (E : ℚ) / (ℓ : ℚ) ^ 4 := by
    rw [eq_div_iff (pow_ne_zero _ hl)]; linarith
  rw [hu', he']
  push_cast
  field_simp

theorem T_PQ (w U E pv pd qh qd : LocRing ℓ) (qv : LocRing ℓ) (u e : ℚ)
    (hu : (ℓ : ℚ) ^ 3 * u = (U : ℚ)) (he : (ℓ : ℚ) ^ 4 * e = (E : ℚ)) (hq : qv = (ℓ : LocRing ℓ) * qh) :
    (w : ℚ) * (u * (((ℓ : ℚ) ^ 2 * pd) * ((ℓ : ℚ) ^ 1 * qv) +
        ((ℓ : ℚ) ^ 2 * pv) * ((ℓ : ℚ) ^ 1 * qd)) + e * (((ℓ : ℚ) ^ 2 * pv) * ((ℓ : ℚ) ^ 1 * qv))) =
      ((w * ((ℓ : LocRing ℓ) * U * pd * qh + U * pv * qd + E * pv * qh) : LocRing ℓ) : ℚ) := by
  have hl := l_ne_zero ℓ
  have hu' : u = (U : ℚ) / (ℓ : ℚ) ^ 3 := by
    rw [eq_div_iff (pow_ne_zero _ hl)]; linarith
  have he' : e = (E : ℚ) / (ℓ : ℚ) ^ 4 := by
    rw [eq_div_iff (pow_ne_zero _ hl)]; linarith
  subst hq
  rw [hu', he']
  push_cast
  field_simp

theorem T_PQ' (w' U E' pv pd qv qd : LocRing ℓ) (u e : ℚ)
    (hu : (ℓ : ℚ) ^ 3 * u = (U : ℚ)) (he : (ℓ : ℚ) ^ 4 * e = ((ℓ : LocRing ℓ) * E' : LocRing ℓ)) :
    (((ℓ : LocRing ℓ) ^ 2 * w' : LocRing ℓ) : ℚ) * (u * (((ℓ : ℚ) ^ 2 * pd) * ((ℓ : ℚ) ^ 1 * qv) +
        ((ℓ : ℚ) ^ 2 * pv) * ((ℓ : ℚ) ^ 1 * qd)) + e * (((ℓ : ℚ) ^ 2 * pv) * ((ℓ : ℚ) ^ 1 * qv))) =
      (((ℓ : LocRing ℓ) ^ 2 * w' * (U * (pd * qv + pv * qd) + E' * pv * qv) : LocRing ℓ) : ℚ) := by
  have hl := l_ne_zero ℓ
  have hu' : u = (U : ℚ) / (ℓ : ℚ) ^ 3 := by
    rw [eq_div_iff (pow_ne_zero _ hl)]; linarith
  have he' : e = (E' : ℚ) / (ℓ : ℚ) ^ 3 := by
    rw [eq_div_iff (pow_ne_zero _ hl)]
    push_cast at he
    apply mul_left_cancel₀ hl
    linear_combination he
  rw [hu', he']
  push_cast
  field_simp

theorem T_QQ (w U E qh qd qh' qd' : LocRing ℓ) (qv qv' : LocRing ℓ) (u e : ℚ)
    (hu : (ℓ : ℚ) ^ 3 * u = (U : ℚ)) (he : (ℓ : ℚ) ^ 4 * e = (E : ℚ))
    (hq : qv = (ℓ : LocRing ℓ) * qh) (hq' : qv' = (ℓ : LocRing ℓ) * qh') :
    (w : ℚ) * (u * (((ℓ : ℚ) ^ 1 * qd) * ((ℓ : ℚ) ^ 1 * qv') +
        ((ℓ : ℚ) ^ 1 * qv) * ((ℓ : ℚ) ^ 1 * qd')) + e * (((ℓ : ℚ) ^ 1 * qv) * ((ℓ : ℚ) ^ 1 * qv'))) =
      ((w * (U * (qd * qh' + qh * qd') + E * qh * qh') : LocRing ℓ) : ℚ) := by
  have hl := l_ne_zero ℓ
  have hu' : u = (U : ℚ) / (ℓ : ℚ) ^ 3 := by
    rw [eq_div_iff (pow_ne_zero _ hl)]; linarith
  have he' : e = (E : ℚ) / (ℓ : ℚ) ^ 4 := by
    rw [eq_div_iff (pow_ne_zero _ hl)]; linarith
  subst hq hq'
  rw [hu', he']
  push_cast
  field_simp

theorem T_QQ' (w' U E qv qd qv' qd' : LocRing ℓ) (u e : ℚ)
    (hu : (ℓ : ℚ) ^ 3 * u = (U : ℚ)) (he : (ℓ : ℚ) ^ 4 * e = (E : ℚ)) :
    (((ℓ : LocRing ℓ) ^ 2 * w' : LocRing ℓ) : ℚ) * (u * (((ℓ : ℚ) ^ 1 * qd) * ((ℓ : ℚ) ^ 1 * qv') +
        ((ℓ : ℚ) ^ 1 * qv) * ((ℓ : ℚ) ^ 1 * qd')) + e * (((ℓ : ℚ) ^ 1 * qv) * ((ℓ : ℚ) ^ 1 * qv'))) =
      ((w' * ((ℓ : LocRing ℓ) * U * (qd * qv' + qv * qd') + E * qv * qv') : LocRing ℓ) : ℚ) := by
  have hl := l_ne_zero ℓ
  have hu' : u = (U : ℚ) / (ℓ : ℚ) ^ 3 := by
    rw [eq_div_iff (pow_ne_zero _ hl)]; linarith
  have he' : e = (E : ℚ) / (ℓ : ℚ) ^ 4 := by
    rw [eq_div_iff (pow_ne_zero _ hl)]; linarith
  rw [hu', he']
  push_cast
  field_simp

end KLevel

end CatalanCore.Lai.NV


open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid Matrix

namespace CatalanCore.Lai.NV

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

/-- Data of a node block: weights, scaled coefficients and the divisibility classes. -/
structure NodeData (ℓ : ℕ) [Fact ℓ.Prime] (s : ℕ) where
  w : ℕ → LocRing ℓ
  u : ℕ → ℚ
  e : ℕ → ℚ
  U : ℕ → LocRing ℓ
  E : ℕ → LocRing ℓ
  ε : LocRing ℓ
  hs1 : 1 ≤ s
  hsℓ : s ≤ ℓ
  hU : ∀ k < ℓ + s, (ℓ : ℚ) ^ 3 * u k = (U k : ℚ)
  hE : ∀ k < ℓ + s, (ℓ : ℚ) ^ 4 * e k = (E k : ℚ)
  low : ∀ k < s, (ℓ : LocRing ℓ) ^ 2 ∣ U k ∧ (ℓ : LocRing ℓ) ∣ E k
  mid : ∀ k, s ≤ k → k < ℓ →
    (ℓ : LocRing ℓ) ^ 2 ∣ w k ∧ (ℓ : LocRing ℓ) ^ 2 ∣ U k ∧ (ℓ : LocRing ℓ) ∣ E k
  high : ∀ μ < s, redQ ℓ (w (ℓ + μ)) ≠ 0 ∧ (ℓ : LocRing ℓ) ^ 2 ∣ U (ℓ + μ) + ε
  hε : redQ ℓ ε ≠ 0

section Basis

variable (ℓ) (s : ℕ)

/-- The basis element of type `b` (`0 = P̃`, `1 = Q̃`). -/
noncomputable def bas (b : Fin 2) (i : ℕ) : (LocRing ℓ)[X] := if b = 0 then Pt ℓ s i else Qt ℓ s i

/-- The `ℓ`-power by which the lattice vector is scaled. -/
def sc (b : Fin 2) : ℕ := if b = 0 then 2 else 1

/-- The lattice vectors `ℓ²P̃_i` and `ℓQ̃_i` as rational polynomials. -/
noncomputable def phi (b : Fin 2) (i : ℕ) : ℚ[X] := C ((ℓ : ℚ) ^ sc b) * toQ ℓ (bas ℓ s b i)

variable {ℓ s}

@[simp] theorem sc_zero : sc 0 = 2 := rfl
@[simp] theorem sc_one : sc 1 = 1 := rfl
@[simp] theorem bas_zero (i : ℕ) : bas ℓ s 0 i = Pt ℓ s i := rfl
@[simp] theorem bas_one (i : ℕ) : bas ℓ s 1 i = Qt ℓ s i := rfl

theorem eval_toQ (g : (LocRing ℓ)[X]) (r : LocRing ℓ) :
    (toQ ℓ g).eval (r : ℚ) = ((g.eval r : LocRing ℓ) : ℚ) := by
  unfold toQ
  rw [Polynomial.coe_mapRingHom, Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply (LocRing ℓ).subtype r

theorem derivative_toQ (g : (LocRing ℓ)[X]) : (toQ ℓ g).derivative = toQ ℓ g.derivative := by
  unfold toQ
  rw [Polynomial.coe_mapRingHom, Polynomial.derivative_map]

theorem phi_eval (b : Fin 2) (i k : ℕ) :
    (phi ℓ s b i).eval (-(k : ℚ)) =
      (ℓ : ℚ) ^ sc b * (((bas ℓ s b i).eval (-(k : LocRing ℓ)) : LocRing ℓ) : ℚ) := by
  unfold phi
  rw [eval_mul, eval_C]
  congr 1
  have : (-(k : ℚ)) = ((-(k : LocRing ℓ) : LocRing ℓ) : ℚ) := by push_cast; rfl
  rw [this, eval_toQ]

theorem phi_deriv_eval (b : Fin 2) (i k : ℕ) :
    (phi ℓ s b i).derivative.eval (-(k : ℚ)) =
      (ℓ : ℚ) ^ sc b * (((bas ℓ s b i).derivative.eval (-(k : LocRing ℓ)) : LocRing ℓ) : ℚ) := by
  unfold phi
  rw [derivative_mul, derivative_C, zero_mul, zero_add, eval_mul, eval_C, derivative_toQ]
  congr 1
  have : (-(k : ℚ)) = ((-(k : LocRing ℓ) : LocRing ℓ) : ℚ) := by push_cast; rfl
  rw [this, eval_toQ]

/-- The term of the node functional at node `k` on `φ_x φ_y`. -/
noncomputable def Tn (D : NodeData ℓ s) (x y : Fin 2 × Fin s) (k : ℕ) : ℚ :=
  (D.w k : ℚ) * (D.u k * ((phi ℓ s x.1 x.2 * phi ℓ s y.1 y.2).derivative.eval (-(k : ℚ))) +
    D.e k * ((phi ℓ s x.1 x.2 * phi ℓ s y.1 y.2).eval (-(k : ℚ))))

theorem Tn_eq (D : NodeData ℓ s) (x y : Fin 2 × Fin s) (k : ℕ) :
    Tn D x y k = (D.w k : ℚ) * (D.u k *
      (((ℓ : ℚ) ^ sc x.1 * (((bas ℓ s x.1 x.2).derivative.eval (-(k : LocRing ℓ)) : LocRing ℓ) : ℚ)) *
        ((ℓ : ℚ) ^ sc y.1 * (((bas ℓ s y.1 y.2).eval (-(k : LocRing ℓ)) : LocRing ℓ) : ℚ)) +
       ((ℓ : ℚ) ^ sc x.1 * (((bas ℓ s x.1 x.2).eval (-(k : LocRing ℓ)) : LocRing ℓ) : ℚ)) *
        ((ℓ : ℚ) ^ sc y.1 * (((bas ℓ s y.1 y.2).derivative.eval (-(k : LocRing ℓ)) : LocRing ℓ) : ℚ))) +
      D.e k * (((ℓ : ℚ) ^ sc x.1 * (((bas ℓ s x.1 x.2).eval (-(k : LocRing ℓ)) : LocRing ℓ) : ℚ)) *
        ((ℓ : ℚ) ^ sc y.1 * (((bas ℓ s y.1 y.2).eval (-(k : LocRing ℓ)) : LocRing ℓ) : ℚ)))) := by
  unfold Tn
  rw [derivative_mul, eval_add, eval_mul, eval_mul, eval_mul, phi_eval, phi_eval, phi_deriv_eval,
    phi_deriv_eval]

theorem Tn_comm (D : NodeData ℓ s) (x y : Fin 2 × Fin s) (k : ℕ) : Tn D x y k = Tn D y x k := by
  unfold Tn
  rw [mul_comm (phi ℓ s x.1 x.2)]

end Basis

end CatalanCore.Lai.NV


open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid Matrix

namespace CatalanCore.Lai.NV

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime]

section High

variable {s : ℕ}

/-- `δ̄ = [μ = i]` in `𝔽_ℓ`. -/
def dl (ℓ : ℕ) [Fact ℓ.Prime] (μ i : ℕ) : ZMod ℓ := if μ = i then 1 else 0

theorem redQ_ite (μ i : ℕ) : redQ ℓ (if μ = i then (1 : LocRing ℓ) else 0) = dl ℓ μ i := by
  unfold dl; split_ifs <;> simp

theorem node_shift (μ : ℕ) :
    (-((ℓ + μ : ℕ) : LocRing ℓ)) = -(μ : LocRing ℓ) + -(ℓ : LocRing ℓ) := by
  push_cast; ring

/-- Taylor expansion of `P̃_i` at the node `-(ℓ + μ)` about `-μ`. -/
theorem high_P (hs : s ≤ ℓ) {i μ : ℕ} (hi : i < s) (hμ : μ < s) :
    ∃ κ1 κ2 : LocRing ℓ,
      (Pt ℓ s i).eval (-((ℓ + μ : ℕ) : LocRing ℓ)) =
        (if μ = i then 1 else 0) + (ℓ : LocRing ℓ) ^ 2 * κ1 ∧
      (Pt ℓ s i).derivative.eval (-((ℓ + μ : ℕ) : LocRing ℓ)) = (ℓ : LocRing ℓ) * κ2 := by
  have e := node_shift (ℓ := ℓ) μ
  obtain ⟨k1, hk1⟩ := binomExpansion (Pt ℓ s i) (-(μ : LocRing ℓ)) (-(ℓ : LocRing ℓ))
  obtain ⟨k2, hk2⟩ := binomExpansion (Pt ℓ s i).derivative (-(μ : LocRing ℓ)) (-(ℓ : LocRing ℓ))
  rw [Pt_eval_node hs hi hμ, Pt_deriv_node hs hi hμ] at hk1
  rw [Pt_deriv_node hs hi hμ] at hk2
  refine ⟨k1, -((Pt ℓ s i).derivative.derivative.eval (-(μ : LocRing ℓ))) + (ℓ : LocRing ℓ) * k2, ?_, ?_⟩
  · rw [e, hk1]; ring
  · rw [e, hk2]; ring

theorem high_Q (hs : s ≤ ℓ) {i μ : ℕ} (hi : i < s) (hμ : μ < s) :
    ∃ κ3 κ4 : LocRing ℓ,
      (Qt ℓ s i).eval (-((ℓ + μ : ℕ) : LocRing ℓ)) =
        (ℓ : LocRing ℓ) * (-(if μ = i then 1 else 0) + (ℓ : LocRing ℓ) * κ3) ∧
      (Qt ℓ s i).derivative.eval (-((ℓ + μ : ℕ) : LocRing ℓ)) =
        (if μ = i then 1 else 0) + (ℓ : LocRing ℓ) * κ4 := by
  have e := node_shift (ℓ := ℓ) μ
  obtain ⟨k1, hk1⟩ := binomExpansion (Qt ℓ s i) (-(μ : LocRing ℓ)) (-(ℓ : LocRing ℓ))
  obtain ⟨k2, hk2⟩ := binomExpansion (Qt ℓ s i).derivative (-(μ : LocRing ℓ)) (-(ℓ : LocRing ℓ))
  rw [Qt_eval_node hs hi hμ, Qt_deriv_node hs hi hμ] at hk1
  rw [Qt_deriv_node hs hi hμ] at hk2
  refine ⟨k1, -((Qt ℓ s i).derivative.derivative.eval (-(μ : LocRing ℓ))) + (ℓ : LocRing ℓ) * k2, ?_, ?_⟩
  · rw [e, hk1]; ring
  · rw [e, hk2]; ring

end High

section Nodes

variable {s : ℕ} (D : NodeData ℓ s)

/-- Residue of the block at node `k`. -/
noncomputable def blk (k : ℕ) : Fin 2 → Fin 2 → ZMod ℓ :=
  ![![redQ ℓ (D.w k) * redQ ℓ (D.E k),
      -(redQ ℓ (D.w k) * redQ ℓ D.ε + redQ ℓ (D.w k) * redQ ℓ (D.E k))],
    ![-(redQ ℓ (D.w k) * redQ ℓ D.ε + redQ ℓ (D.w k) * redQ ℓ (D.E k)),
      2 * (redQ ℓ (D.w k) * redQ ℓ D.ε) + redQ ℓ (D.w k) * redQ ℓ (D.E k)]]

theorem redQ_U_high {μ : ℕ} (hμ : μ < s) : redQ ℓ (D.U (ℓ + μ)) = -redQ ℓ D.ε := by
  have h := redQ_eq_zero_of_sq_dvd (D.high μ hμ).2
  rw [map_add] at h
  linear_combination h

include hℓ in
theorem node_PP (i j : Fin s) (k : ℕ) (hk : k < ℓ + s) :
    ∃ τ : LocRing ℓ, Tn D (0, i) (0, j) k = (τ : ℚ) ∧ (k < ℓ → redQ ℓ τ = 0) ∧
      (ℓ ≤ k → redQ ℓ τ = dl ℓ (k - ℓ) i * dl ℓ (k - ℓ) j * blk D k 0 0) := by
  rw [Tn_eq]
  simp only [sc_zero, bas_zero]
  rw [T_PP (D.w k) (D.U k) (D.E k) _ _ _ _ (D.u k) (D.e k) (D.hU k hk) (D.hE k hk)]
  refine ⟨_, rfl, ?_, ?_⟩
  · intro hkℓ
    by_cases hks : k < s
    · obtain ⟨_, hEd⟩ := D.low k hks
      have hE0 : redQ ℓ (D.E k) = 0 := redQ_eq_zero_of_dvd hEd
      simp [hE0, redQ_natCast_self]
    · have hw0 : redQ ℓ (D.w k) = 0 := redQ_eq_zero_of_sq_dvd (D.mid k (not_lt.1 hks) hkℓ).1
      simp [hw0]
  · intro hkℓ
    obtain ⟨μ, rfl⟩ : ∃ μ, k = ℓ + μ := ⟨k - ℓ, by omega⟩
    have hμ : μ < s := by omega
    obtain ⟨a1, a2, ha1, ha2⟩ := high_P D.hsℓ i.2 hμ
    obtain ⟨b1, b2, hb1, hb2⟩ := high_P D.hsℓ j.2 hμ
    rw [ha1, ha2, hb1, hb2]
    have h0 : ℓ + μ - ℓ = μ := by omega
    rw [h0]
    simp only [map_mul, map_add, map_pow, redQ_natCast_self, redQ_ite, blk, Matrix.cons_val_zero]
    simp
    ring

include hℓ in
theorem node_PQ (i j : Fin s) (k : ℕ) (hk : k < ℓ + s) :
    ∃ τ : LocRing ℓ, Tn D (0, i) (1, j) k = (τ : ℚ) ∧ (k < ℓ → redQ ℓ τ = 0) ∧
      (ℓ ≤ k → redQ ℓ τ = dl ℓ (k - ℓ) i * dl ℓ (k - ℓ) j * blk D k 0 1) := by
  rw [Tn_eq]
  simp only [sc_zero, sc_one, bas_zero, bas_one]
  by_cases hks : k < s
  · obtain ⟨hU2, _⟩ := D.low k hks
    have hU0 : redQ ℓ (D.U k) = 0 := redQ_eq_zero_of_sq_dvd hU2
    have hq : (Qt ℓ s j).eval (-(k : LocRing ℓ)) = (ℓ : LocRing ℓ) * 0 := by
      rw [Qt_eval_node D.hsℓ j.2 hks]; simp
    rw [T_PQ _ _ _ _ _ 0 _ _ _ _ (D.hU k hk) (D.hE k hk) hq]
    refine ⟨_, rfl, fun _ => ?_, fun h => absurd (lt_of_lt_of_le hks D.hsℓ) (not_lt.2 h)⟩
    simp [hU0]
  · by_cases hkℓ : k < ℓ
    · obtain ⟨⟨w', hw'⟩, -, ⟨E', hE'⟩⟩ := D.mid k (not_lt.1 hks) hkℓ
      have he : (ℓ : ℚ) ^ 4 * D.e k = ((ℓ * E' : LocRing ℓ) : ℚ) := by
        rw [← hE']; exact D.hE k hk
      rw [hw', T_PQ' w' (D.U k) E' _ _ _ _ (D.u k) (D.e k) (D.hU k hk) he]
      refine ⟨_, rfl, fun _ => ?_, fun h => absurd hkℓ (not_lt.2 h)⟩
      simp [redQ_natCast_self]
    · obtain ⟨μ, rfl⟩ : ∃ μ, k = ℓ + μ := ⟨k - ℓ, by omega⟩
      have hμ : μ < s := by omega
      obtain ⟨a1, a2, ha1, ha2⟩ := high_P D.hsℓ i.2 hμ
      obtain ⟨c3, c4, hc3, hc4⟩ := high_Q D.hsℓ j.2 hμ
      rw [T_PQ _ _ _ _ _ (-(if μ = (j : ℕ) then 1 else 0) + (ℓ : LocRing ℓ) * c3) _ _ _ _
        (D.hU _ hk) (D.hE _ hk) hc3]
      refine ⟨_, rfl, fun h => absurd h hkℓ, fun _ => ?_⟩
      rw [ha1, ha2, hc4]
      have h0 : ℓ + μ - ℓ = μ := by omega
      rw [h0]
      simp only [map_mul, map_add, map_neg, map_pow, redQ_natCast_self, redQ_ite,
        redQ_U_high D hμ, blk, Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, zero_mul,
        add_zero, zero_add, zero_pow (two_ne_zero), map_ofNat]
      ring

include hℓ in
theorem node_QQ (i j : Fin s) (k : ℕ) (hk : k < ℓ + s) :
    ∃ τ : LocRing ℓ, Tn D (1, i) (1, j) k = (τ : ℚ) ∧ (k < ℓ → redQ ℓ τ = 0) ∧
      (ℓ ≤ k → redQ ℓ τ = dl ℓ (k - ℓ) i * dl ℓ (k - ℓ) j * blk D k 1 1) := by
  rw [Tn_eq]
  simp only [sc_one, bas_one]
  by_cases hks : k < s
  · have hqi : (Qt ℓ s i).eval (-(k : LocRing ℓ)) = (ℓ : LocRing ℓ) * 0 := by
      rw [Qt_eval_node D.hsℓ i.2 hks]; simp
    have hqj : (Qt ℓ s j).eval (-(k : LocRing ℓ)) = (ℓ : LocRing ℓ) * 0 := by
      rw [Qt_eval_node D.hsℓ j.2 hks]; simp
    rw [T_QQ _ _ _ 0 _ 0 _ _ _ _ _ (D.hU k hk) (D.hE k hk) hqi hqj]
    refine ⟨_, rfl, fun _ => ?_, fun h => absurd (lt_of_lt_of_le hks D.hsℓ) (not_lt.2 h)⟩
    simp
  · by_cases hkℓ : k < ℓ
    · obtain ⟨⟨w', hw'⟩, -, hEd⟩ := D.mid k (not_lt.1 hks) hkℓ
      have hE0 : redQ ℓ (D.E k) = 0 := redQ_eq_zero_of_dvd hEd
      rw [hw', T_QQ' w' (D.U k) (D.E k) _ _ _ _ (D.u k) (D.e k) (D.hU k hk) (D.hE k hk)]
      refine ⟨_, rfl, fun _ => ?_, fun h => absurd hkℓ (not_lt.2 h)⟩
      simp [redQ_natCast_self, hE0]
    · obtain ⟨μ, rfl⟩ : ∃ μ, k = ℓ + μ := ⟨k - ℓ, by omega⟩
      have hμ : μ < s := by omega
      obtain ⟨c3, c4, hc3, hc4⟩ := high_Q D.hsℓ i.2 hμ
      obtain ⟨d3, d4, hd3, hd4⟩ := high_Q D.hsℓ j.2 hμ
      rw [T_QQ _ _ _ (-(if μ = (i : ℕ) then 1 else 0) + (ℓ : LocRing ℓ) * c3) _
        (-(if μ = (j : ℕ) then 1 else 0) + (ℓ : LocRing ℓ) * d3) _ _ _ _ _ (D.hU _ hk) (D.hE _ hk) hc3 hd3]
      refine ⟨_, rfl, fun h => absurd h hkℓ, fun _ => ?_⟩
      rw [hc4, hd4]
      have h0 : ℓ + μ - ℓ = μ := by omega
      rw [h0]
      simp only [map_mul, map_add, map_neg, map_pow, redQ_natCast_self, redQ_ite,
        redQ_U_high D hμ, blk, Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, zero_mul,
        add_zero, zero_add, zero_pow (two_ne_zero), map_ofNat]
      ring

end Nodes

end CatalanCore.Lai.NV


open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid Matrix

namespace CatalanCore.Lai.NV

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {s : ℕ} (D : NodeData ℓ s)

theorem blk_symm (k : ℕ) : blk D k 1 0 = blk D k 0 1 := by
  simp [blk]

include hℓ in
theorem node_any (x y : Fin 2 × Fin s) (k : ℕ) (hk : k < ℓ + s) :
    ∃ τ : LocRing ℓ, Tn D x y k = (τ : ℚ) ∧ (k < ℓ → redQ ℓ τ = 0) ∧
      (ℓ ≤ k → redQ ℓ τ = dl ℓ (k - ℓ) x.2 * dl ℓ (k - ℓ) y.2 * blk D k x.1 y.1) := by
  obtain ⟨b, i⟩ := x
  obtain ⟨b', j⟩ := y
  fin_cases b <;> fin_cases b'
  · exact node_PP D i j k hk
  · exact node_PQ D i j k hk
  · obtain ⟨τ, h1, h2, h3⟩ := node_PQ D j i k hk
    refine ⟨τ, by rw [Tn_comm]; exact h1, h2, fun h => ?_⟩
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] at h3 ⊢
    rw [h3 h, blk_symm]
    ring
  · exact node_QQ D i j k hk

theorem sum_delta (i j : Fin s) (c : ℕ → ZMod ℓ) :
    ∑ μ ∈ range s, dl ℓ μ i * dl ℓ μ j * c μ = if i = j then c i else 0 := by
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single (i : ℕ)]
    · simp [dl]
    · intro μ _ hμ
      simp [dl, hμ]
    · intro h; exact absurd (Finset.mem_range.2 i.2) h
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun μ _ => ?_
    by_cases h1 : μ = (i : ℕ)
    · have h2 : μ ≠ (j : ℕ) := fun h2 => h (Fin.ext (h1.symm.trans h2))
      simp [dl, h2]
    · simp [dl, h1]

include hℓ in
theorem gram_entry (x y : Fin 2 × Fin s) :
    ∃ g : LocRing ℓ,
      (g : ℚ) = nodeL (ℓ + s - 1) (fun k => (D.w k : ℚ)) D.u D.e (phi ℓ s x.1 x.2 * phi ℓ s y.1 y.2) ∧
      redQ ℓ g = if x.2 = y.2 then blk D (ℓ + x.2) x.1 y.1 else 0 := by
  have h : ∀ k, ∃ τ : LocRing ℓ, k < ℓ + s → (Tn D x y k = (τ : ℚ) ∧ (k < ℓ → redQ ℓ τ = 0) ∧
      (ℓ ≤ k → redQ ℓ τ = dl ℓ (k - ℓ) x.2 * dl ℓ (k - ℓ) y.2 * blk D k x.1 y.1)) := by
    intro k
    by_cases hk : k < ℓ + s
    · obtain ⟨τ, hτ⟩ := node_any D x y k hk
      exact ⟨τ, fun _ => hτ⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose τ hτ using h
  refine ⟨∑ k ∈ range (ℓ + s), τ k, ?_, ?_⟩
  · rw [nodeL_apply, show ℓ + s - 1 + 1 = ℓ + s by have := D.hs1; omega]
    push_cast
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← (hτ k (Finset.mem_range.1 hk)).1]
    rfl
  · rw [map_sum, Finset.sum_range_add]
    have h1 : ∑ k ∈ range ℓ, redQ ℓ (τ k) = 0 :=
      Finset.sum_eq_zero fun k hk =>
        (hτ k (by have := Finset.mem_range.1 hk; have := D.hsℓ; omega)).2.1 (Finset.mem_range.1 hk)
    have h2 : ∑ μ ∈ range s, redQ ℓ (τ (ℓ + μ)) =
        ∑ μ ∈ range s, dl ℓ μ x.2 * dl ℓ μ y.2 * blk D (ℓ + μ) x.1 y.1 := by
      refine Finset.sum_congr rfl fun μ hμ => ?_
      have hμ' := Finset.mem_range.1 hμ
      have := (hτ (ℓ + μ) (by omega)).2.2 (by omega)
      rw [this]
      have e : ℓ + μ - ℓ = μ := by omega
      rw [e]
    rw [h1, zero_add, h2]
    exact sum_delta x.2 y.2 (fun μ => blk D (ℓ + μ) x.1 y.1)

theorem natDegree_phi_le (b : Fin 2) (i : Fin s) (hs : 1 ≤ s) : (phi ℓ s b i).natDegree ≤ 2 * s - 1 := by
  unfold phi
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_map_le).trans ?_
  fin_cases b
  · exact natDegree_Pt_le s i i.2
  · exact natDegree_Qt_le s i i.2

theorem degree_phi_lt (b : Fin 2) (i : Fin s) (hs : 1 ≤ s) : (phi ℓ s b i).degree < ((2 * s : ℕ) : WithBot ℕ) := by
  refine lt_of_le_of_lt degree_le_natDegree ?_
  have := natDegree_phi_le (ℓ := ℓ) b i hs
  exact_mod_cast (by omega : (phi ℓ s b i).natDegree < 2 * s)

/-- The Gram matrix of the node functional on the Hermite lattice has a unit determinant. -/
theorem NodeData.exists_gram :
    ∃ G : Matrix (Fin 2 × Fin s) (Fin 2 × Fin s) (LocRing ℓ),
      (∀ x y, (G x y : ℚ) = nodeL (ℓ + s - 1) (fun k => (D.w k : ℚ)) D.u D.e
        (phi ℓ s x.1 x.2 * phi ℓ s y.1 y.2)) ∧ redQ ℓ G.det ≠ 0 := by
  choose Gm hGm using fun x y : Fin 2 × Fin s => gram_entry D x y
  set G : Matrix (Fin 2 × Fin s) (Fin 2 × Fin s) (LocRing ℓ) := Matrix.of fun x y => Gm x y with hG
  have hmap : (redQ ℓ).mapMatrix G =
      Matrix.blockDiagonal (fun i : Fin s => Matrix.of fun b b' : Fin 2 => blk D (ℓ + i) b b') := by
    ext ⟨b, i⟩ ⟨b', j⟩
    rw [Matrix.blockDiagonal_apply]
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hG, Matrix.of_apply]
    rw [(hGm (b, i) (b', j)).2]
  have hdet : (redQ ℓ) G.det ≠ 0 := by
    rw [RingHom.map_det, hmap, Matrix.det_blockDiagonal]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    rw [Matrix.det_fin_two]
    have hw : redQ ℓ (D.w (ℓ + i)) ≠ 0 := (D.high i i.2).1
    have he : redQ ℓ D.ε ≠ 0 := D.hε
    simp only [blk, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    have : ((redQ ℓ (D.w (ℓ + i))) * (redQ ℓ (D.E (ℓ + i)))) *
          (2 * (redQ ℓ (D.w (ℓ + i)) * redQ ℓ D.ε) + redQ ℓ (D.w (ℓ + i)) * redQ ℓ (D.E (ℓ + i))) -
        (-(redQ ℓ (D.w (ℓ + i)) * redQ ℓ D.ε + redQ ℓ (D.w (ℓ + i)) * redQ ℓ (D.E (ℓ + i)))) *
          (-(redQ ℓ (D.w (ℓ + i)) * redQ ℓ D.ε + redQ ℓ (D.w (ℓ + i)) * redQ ℓ (D.E (ℓ + i)))) =
        -((redQ ℓ (D.w (ℓ + i))) ^ 2 * (redQ ℓ D.ε) ^ 2) := by ring
    rw [this]
    exact neg_ne_zero.2 (mul_ne_zero (pow_ne_zero _ hw) (pow_ne_zero _ he))
  exact ⟨G, fun x y => (hGm x y).1, hdet⟩

/-- **The node-block Hankel determinant does not vanish.** -/
theorem NodeData.hankel_det_ne_zero {N : ℕ} (hN : 2 * s = N) :
    (Matrix.of fun i j : Fin N =>
      nodeL (ℓ + s - 1) (fun k => (D.w k : ℚ)) D.u D.e (X ^ ((i : ℕ) + j))).det ≠ 0 := by
  subst hN
  refine hankel_det_ne_zero_of_gram _ finProdFinEquiv (fun x => phi ℓ s x.1 x.2)
    (fun x => degree_phi_lt x.1 x.2 D.hs1) ?_
  obtain ⟨G, hG, hdet⟩ := D.exists_gram
  have hent : (Matrix.of fun x y : Fin 2 × Fin s => nodeL (ℓ + s - 1) (fun k => (D.w k : ℚ)) D.u D.e
      (phi ℓ s x.1 x.2 * phi ℓ s y.1 y.2)) = (LocRing ℓ).subtype.mapMatrix G := by
    ext x y
    simp [hG x y]
  have hdet' : G.det ≠ 0 := fun h => hdet (by rw [h]; exact map_zero _)
  rw [hent, ← RingHom.map_det]
  exact fun h => hdet' (Subtype.ext (by simpa using h))

end CatalanCore.Lai.NV


/-!
# Exact valuation of the node-block Hankel determinant (the index of the Hermite lattice)

`det [L(X^{i+j})]_{i,j<2s} = g / (ℓ^{6s} t²)` with `g, t` units of `ℤ_(ℓ)`: the coefficient matrix of
`P̃_i, Q̃_i` is invertible modulo `ℓ` (its rows are independent because the Hermite data at the nodes
`-μ` separate them), so the lattice `⟨ℓ²P̃_i, ℓQ̃_i⟩` has index exactly `ℓ^{3s}`.
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Arith.Hybrid Matrix

namespace CatalanCore.Lai.NV

variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] {s : ℕ}

theorem natDegree_bas_le (b : Fin 2) (i : Fin s) : (bas ℓ s b i).natDegree ≤ 2 * s - 1 := by
  fin_cases b
  · exact natDegree_Pt_le s i i.2
  · exact natDegree_Qt_le s i i.2

theorem redQ_eval_map (g : (LocRing ℓ)[X]) (a : LocRing ℓ) :
    (g.map (redQ ℓ)).eval (redQ ℓ a) = redQ ℓ (g.eval a) := by
  rw [Polynomial.eval_map]; exact Polynomial.eval₂_at_apply (redQ ℓ) a

theorem neg_natCast_redQ (μ : ℕ) : -((μ : ℕ) : ZMod ℓ) = redQ ℓ (-(μ : LocRing ℓ)) := by simp

theorem bas_node_eval (hsℓ : s ≤ ℓ) (b : Fin 2) (i μ : Fin s) :
    ((bas ℓ s b i).map (redQ ℓ)).eval (-((μ : ℕ) : ZMod ℓ)) = if b = 0 then dl ℓ μ i else 0 := by
  rw [neg_natCast_redQ, redQ_eval_map]
  fin_cases b
  · simp only [Fin.zero_eta, Fin.isValue, bas_zero, if_true]
    rw [Pt_eval_node hsℓ i.2 μ.2, redQ_ite]
  · simp [Qt_eval_node hsℓ i.2 μ.2]

theorem bas_node_deriv (hsℓ : s ≤ ℓ) (b : Fin 2) (i μ : Fin s) :
    ((bas ℓ s b i).map (redQ ℓ)).derivative.eval (-((μ : ℕ) : ZMod ℓ)) =
      if b = 1 then dl ℓ μ i else 0 := by
  rw [Polynomial.derivative_map, neg_natCast_redQ, redQ_eval_map]
  fin_cases b
  · simp [Pt_deriv_node hsℓ i.2 μ.2]
  · simp only [Fin.mk_one, Fin.isValue, bas_one, if_true]
    rw [Qt_deriv_node hsℓ i.2 μ.2, redQ_ite]

theorem sum_dl (μ : Fin s) (c : Fin s → ZMod ℓ) : ∑ i : Fin s, c i * dl ℓ μ i = c μ := by
  rw [Finset.sum_eq_single μ]
  · simp [dl]
  · intro i _ hi
    have : (μ : ℕ) ≠ i := fun h => hi (Fin.ext h.symm)
    simp [dl, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The coefficient matrix of `P̃_i, Q̃_i` is invertible modulo `ℓ`. -/
theorem coeff_matrix_redQ_ne (hs1 : 1 ≤ s) (hsℓ : s ≤ ℓ) {N : ℕ} (hN : 2 * s = N)
    (e : Fin 2 × Fin s ≃ Fin N) :
    redQ ℓ (Matrix.of fun (i j : Fin N) =>
      (bas ℓ s (e.symm i).1 (e.symm i).2).coeff (j : ℕ)).det ≠ 0 := by
  intro h0
  set M : Matrix (Fin N) (Fin N) (LocRing ℓ) := Matrix.of fun (i j : Fin N) =>
      (bas ℓ s (e.symm i).1 (e.symm i).2).coeff (j : ℕ) with hM
  have hdet : (Matrix.of fun i j : Fin N => redQ ℓ (M i j)).det = 0 := by
    have := RingHom.map_det (redQ ℓ) M
    rw [h0] at this
    exact this.symm
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
  set f : (ZMod ℓ)[X] := ∑ i : Fin N, C (v i) * (bas ℓ s (e.symm i).1 (e.symm i).2).map (redQ ℓ)
    with hf
  have hf0 : f = 0 := by
    ext j
    simp only [hf, finset_sum_coeff, coeff_C_mul, coeff_map, coeff_zero]
    by_cases hj : j < N
    · have := congrFun hv ⟨j, hj⟩
      simpa [Matrix.vecMul, dotProduct, hM] using this
    · refine Finset.sum_eq_zero fun i _ => ?_
      have : (bas ℓ s (e.symm i).1 (e.symm i).2).coeff j = 0 :=
        coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_bas_le _ _) (by omega))
      simp [this]
  apply hv0
  funext i
  obtain ⟨⟨b, μ⟩, rfl⟩ := e.surjective i
  have hev : f.eval (-((μ : ℕ) : ZMod ℓ)) = 0 := by rw [hf0]; simp
  have hdv : f.derivative.eval (-((μ : ℕ) : ZMod ℓ)) = 0 := by rw [hf0]; simp
  simp only [hf, eval_finset_sum, eval_mul, eval_C, derivative_sum, derivative_C_mul] at hev hdv
  rw [← e.sum_comp, Fintype.sum_prod_type] at hev hdv
  simp only [Equiv.symm_apply_apply, Fin.sum_univ_two] at hev hdv
  fin_cases b
  · simp only [bas_node_eval hsℓ, Fin.isValue, Fin.zero_eta, if_true, mul_zero, sum_dl,
      Finset.sum_const_zero, add_zero, Fin.one_eq_zero_iff, OfNat.ofNat_ne_zero, if_false] at hev
    have := hev
    simpa using this
  · simp only [bas_node_deriv hsℓ, Fin.isValue, Fin.mk_one, if_true, mul_zero,
      Finset.sum_const_zero, zero_add] at hdv
    have := hdv
    simpa [sum_dl] using this

theorem sum_sc : ∑ y : Fin 2 × Fin s, sc y.1 = 3 * s := by
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]
  ring

/-- **Exact valuation.**  `det H = g / (ℓ^{6s} t²)` with `g, t` units of `ℤ_(ℓ)`. -/
theorem NodeData.hankel_det_val (D : NodeData ℓ s) {N : ℕ} (hN : 2 * s = N) :
    ∃ t g : LocRing ℓ, redQ ℓ t ≠ 0 ∧ redQ ℓ g ≠ 0 ∧
      (Matrix.of fun i j : Fin N =>
        nodeL (ℓ + s - 1) (fun k => (D.w k : ℚ)) D.u D.e (X ^ ((i : ℕ) + j))).det *
          ((ℓ : ℚ) ^ (6 * s) * (t : ℚ) ^ 2) = (g : ℚ) := by
  subst hN
  set e : Fin 2 × Fin s ≃ Fin (2 * s) := finProdFinEquiv with he
  set φ' : Fin (2 * s) → ℚ[X] := fun i => phi ℓ s (e.symm i).1 (e.symm i).2 with hφ'
  have hφ : ∀ x, (φ' x).degree < ((2 * s : ℕ) : WithBot ℕ) := fun x =>
    degree_phi_lt (e.symm x).1 (e.symm x).2 D.hs1
  obtain ⟨G, hG, hdetG⟩ := D.exists_gram
  set L := nodeL (ℓ + s - 1) (fun k => (D.w k : ℚ)) D.u D.e with hL
  have hgram : (Matrix.of fun x y : Fin (2 * s) => L (φ' x * φ' y)).det = ((G.det : LocRing ℓ) : ℚ) := by
    have h1 : (Matrix.of fun x y : Fin (2 * s) => L (φ' x * φ' y)) =
        ((LocRing ℓ).subtype.mapMatrix G).submatrix e.symm e.symm := by
      ext x y
      simp [hG, hφ', hL]
    rw [h1, Matrix.det_submatrix_equiv_self, ← RingHom.map_det]
    rfl
  set Tt : Matrix (Fin (2 * s)) (Fin (2 * s)) (LocRing ℓ) := Matrix.of fun (i j : Fin (2 * s)) =>
      (bas ℓ s (e.symm i).1 (e.symm i).2).coeff (j : ℕ) with hTt
  have hT : (Matrix.of fun x (j : Fin (2 * s)) => (φ' x).coeff j) =
      Matrix.of fun i j => (ℓ : ℚ) ^ sc (e.symm i).1 * ((LocRing ℓ).subtype.mapMatrix Tt) i j := by
    ext i j
    simp only [hφ', phi, Matrix.of_apply, coeff_C_mul, toQ_coeff, hTt, RingHom.mapMatrix_apply,
      Matrix.map_apply]
    rfl
  have hdetT : (Matrix.of fun x (j : Fin (2 * s)) => (φ' x).coeff j).det =
      (ℓ : ℚ) ^ (3 * s) * ((Tt.det : LocRing ℓ) : ℚ) := by
    rw [hT, Matrix.det_mul_column, Finset.prod_pow_eq_pow_sum, ← RingHom.map_det]
    congr 1
    congr 1
    rw [← sum_sc (s := s)]
    exact Equiv.sum_comp e.symm (fun y => sc y.1)
  have hdet := det_gram_fin L φ' hφ
  rw [hgram, hdetT] at hdet
  refine ⟨Tt.det, G.det, coeff_matrix_redQ_ne D.hs1 D.hsℓ rfl e, hdetG, ?_⟩
  rw [hdet]
  ring

/-- A unit of `ℤ_(ℓ)` (nonzero residue) has `ℓ`-adic valuation `0`. -/
theorem padicValRat_of_redQ_ne (x : LocRing ℓ) (h : redQ ℓ x ≠ 0) : padicValRat ℓ (x : ℚ) = 0 := by
  have hden : ¬ ℓ ∣ (x : ℚ).den := x.2
  have hnum : ¬ (ℓ : ℤ) ∣ (x : ℚ).num := by
    intro hd
    apply h
    rw [redQ_apply, Rat.cast_def]
    have : (((x : ℚ).num : ℤ) : ZMod ℓ) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hd
    simp [this]
  unfold padicValRat
  rw [padicValInt.eq_zero_of_not_dvd hnum, padicValNat.eq_zero_of_not_dvd hden]
  simp

theorem ne_zero_of_redQ_ne (x : LocRing ℓ) (h : redQ ℓ x ≠ 0) : (x : ℚ) ≠ 0 := by
  intro h0
  apply h
  have : x = 0 := Subtype.ext h0
  rw [this, map_zero]

/-- If `J · ℓ^k · t = g` with `t, g` units of `ℤ_(ℓ)`, then `v_ℓ(J) = -k`. -/
theorem padicValRat_of_unit_rel (J : ℚ) (k : ℕ) (t g : LocRing ℓ) (ht : redQ ℓ t ≠ 0)
    (hg : redQ ℓ g ≠ 0) (h : J * ((ℓ : ℚ) ^ k * (t : ℚ)) = (g : ℚ)) : padicValRat ℓ J = -(k : ℤ) := by
  have hJ : J ≠ 0 := by
    rintro rfl
    exact ne_zero_of_redQ_ne g hg (by rw [← h]; simp)
  have hl : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.out.ne_zero
  have htq := ne_zero_of_redQ_ne t ht
  have h1 := congrArg (padicValRat ℓ) h
  rw [padicValRat.mul hJ (mul_ne_zero (pow_ne_zero _ hl) htq),
    padicValRat.mul (pow_ne_zero _ hl) htq, padicValRat.pow (ℓ : ℚ),
    padicValRat.self hℓ.out.one_lt, padicValRat_of_redQ_ne t ht, padicValRat_of_redQ_ne g hg] at h1
  simp at h1
  omega

end CatalanCore.Lai.NV
