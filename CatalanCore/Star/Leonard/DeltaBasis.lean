module

public import CatalanCore.Star.Leonard.DeltaCB
public import CatalanCore.Star.Leonard.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Prop hDelta, step (3): Hankel determinant in the monic bases `φ_p, ψ_q`

For monic polynomials `φ_p`, `ψ_q` of degree `p`, `q` (`p, q < m`):
`det[∑_a ρ(a) φ_p(a) ψ_q(a)] = det[∑_a ρ(a) a^{p+q}]` (unitriangular change of basis, both sides).
-/

@[expose] public section

open Finset Matrix Polynomial

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F]

/-- coefficient matrix of monic polynomials `φ_p` (`p < m`): `L p k = coeff k` -/
noncomputable def coefMat {m : ℕ} (φ : Fin m → F[X]) : Matrix (Fin m) (Fin m) F :=
  Matrix.of fun p k => (φ p).coeff k

lemma coefMat_det {m : ℕ} (φ : Fin m → F[X]) (hmon : ∀ p, (φ p).Monic)
    (hdeg : ∀ p, (φ p).natDegree = p) : (coefMat φ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [coefMat, Finset.prod_eq_one, fun p => by simpa [hdeg p] using (hmon p).coeff_natDegree]
  · intro p k hpk
    simp only [coefMat, Matrix.of_apply]
    exact coeff_eq_zero_of_natDegree_lt (by rw [hdeg p]; exact hpk)

lemma eval_eq_coefMat {m : ℕ} (φ : Fin m → F[X]) (hdeg : ∀ p, (φ p).natDegree = p) (p : Fin m) (x : F) :
    (φ p).eval x = ∑ k : Fin m, coefMat φ p k * x ^ (k : ℕ) := by
  rw [Polynomial.eval_eq_sum_range' (n := m) (by rw [hdeg p]; exact p.2)]
  rw [← Fin.sum_univ_eq_sum_range (fun k => (φ p).coeff k * x ^ k) m]
  rfl

/-- **Step (3a).** -/
theorem hankel_basis_change {K m : ℕ} (ρ : Fin K → F) (φ ψ : Fin m → F[X])
    (hφm : ∀ p, (φ p).Monic) (hφd : ∀ p, (φ p).natDegree = p)
    (hψm : ∀ p, (ψ p).Monic) (hψd : ∀ p, (ψ p).natDegree = p) :
    (Matrix.of fun (p q : Fin m) => ∑ a : Fin K, ρ a * (φ p).eval ((a : ℕ) : F) *
        (ψ q).eval ((a : ℕ) : F)).det =
      ((Vm K m : Matrix (Fin K) (Fin m) F)ᵀ * Matrix.diagonal ρ * Vm K m).det := by
  have hV : ∀ (χ : Fin m → F[X]), (∀ p, (χ p).natDegree = p) →
      (Matrix.of fun (a : Fin K) (p : Fin m) => (χ p).eval ((a : ℕ) : F)) =
        (Vm K m : Matrix (Fin K) (Fin m) F) * (coefMat χ)ᵀ := by
    intro χ hχ
    ext a p
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Vm]
    rw [eval_eq_coefMat χ hχ p]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have h : (Matrix.of fun (p q : Fin m) => ∑ a : Fin K, ρ a * (φ p).eval ((a : ℕ) : F) *
        (ψ q).eval ((a : ℕ) : F)) =
      coefMat φ * ((Vm K m : Matrix (Fin K) (Fin m) F)ᵀ * Matrix.diagonal ρ * Vm K m) *
        (coefMat ψ)ᵀ := by
    have h1 : (Matrix.of fun (p q : Fin m) => ∑ a : Fin K, ρ a * (φ p).eval ((a : ℕ) : F) *
        (ψ q).eval ((a : ℕ) : F)) =
        (Matrix.of fun (a : Fin K) (p : Fin m) => (φ p).eval ((a : ℕ) : F))ᵀ * Matrix.diagonal ρ *
          (Matrix.of fun (a : Fin K) (p : Fin m) => (ψ p).eval ((a : ℕ) : F)) := by
      ext p q
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.of_apply, Matrix.transpose_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    rw [h1, hV φ hφd, hV ψ hψd, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, coefMat_det φ hφm hφd,
    coefMat_det ψ hψm hψd]
  ring

/-! ### Step (3c): telescoping of reciprocal rising factorials -/

/-- rising factorial `c (c+1) … (c+L-1)` -/
def pochr (c : F) (L : ℕ) : F := ∏ i ∈ Finset.range L, (c + (i : F))

lemma pochr_succ_right (c : F) (L : ℕ) : pochr c (L + 1) = pochr c L * (c + (L : F)) := by
  simp [pochr, Finset.prod_range_succ]

lemma pochr_succ_left (c : F) (L : ℕ) : pochr c (L + 1) = c * pochr (c + 1) L := by
  unfold pochr
  rw [Finset.prod_range_succ']
  simp only [Nat.cast_zero, add_zero, Nat.cast_add, Nat.cast_one]
  rw [mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun i _ => by ring

lemma pochr_ne_zero (c : F) (L : ℕ) (h : ∀ i : ℕ, i < L → c + (i : F) ≠ 0) : pochr c L ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i hi => h i (Finset.mem_range.1 hi)

lemma recip_diff (z : F) (L : ℕ) (h : ∀ i : ℕ, i < L + 1 → z + (i : F) ≠ 0) :
    (pochr z L)⁻¹ - (pochr (z + 1) L)⁻¹ = (L : F) * (pochr z (L + 1))⁻¹ := by
  have h1 : z ≠ 0 := by simpa using h 0 (by omega)
  have hL : pochr z L ≠ 0 := pochr_ne_zero z L fun i hi => h i (by omega)
  have hL1 : pochr (z + 1) L ≠ 0 := pochr_ne_zero (z + 1) L fun i hi => by
    have := h (i + 1) (by omega)
    intro h0; apply this; push_cast; linear_combination h0
  have hz : z + (L : F) ≠ 0 := h L (by omega)
  have e1 := pochr_succ_right z L
  have e2 := pochr_succ_left z L
  have hz1 : pochr z (L + 1) ≠ 0 := by rw [e1]; exact mul_ne_zero hL hz
  have hA : (pochr z L)⁻¹ = (z + (L : F)) * (pochr z (L + 1))⁻¹ := by
    rw [e1]; field_simp
  have hB : (pochr (z + 1) L)⁻¹ = z * (pochr z (L + 1))⁻¹ := by
    rw [e2]; field_simp
  rw [hA, hB]
  ring

/-- **Step (3c).** `L' ∑_{a<K} 1/(c+a)_{L'+1} = 1/(c)_{L'} - 1/(c+K)_{L'}`. -/
theorem tele_sum (c : F) (L' : ℕ) (K : ℕ) (h : ∀ i : ℕ, i < K + L' + 1 → c + (i : F) ≠ 0) :
    (L' : F) * ∑ a ∈ Finset.range K, (pochr (c + (a : F)) (L' + 1))⁻¹ =
      (pochr c L')⁻¹ - (pochr (c + (K : F)) L')⁻¹ := by
  induction K with
  | zero => simp
  | succ K ih =>
    have ih' := ih fun i hi => h i (by omega)
    rw [Finset.sum_range_succ, mul_add, ih']
    have := recip_diff (c + (K : F)) L' fun i hi => by
      have := h (K + i) (by omega)
      intro h0; apply this; push_cast; linear_combination h0
    have e : c + ((K + 1 : ℕ) : F) = c + (K : F) + 1 := by push_cast; ring
    rw [e]
    linear_combination (-1 : F) * this

/-! ### Step (3b): the monic bases and the entries -/

/-- `φ_p(a) = (a+θ+1)_p` -/
noncomputable def phiPoly (θ : F) (p : ℕ) : F[X] := ∏ i ∈ Finset.range p, (X + C (θ + 1 + (i : F)))

/-- `ψ_q(a) = (a+θ+2m-q+1)_q` -/
noncomputable def psiPoly (θ : F) (m q : ℕ) : F[X] :=
  ∏ i ∈ Finset.range q, (X + C (θ + ((2 * m - q : ℕ) : F) + 1 + (i : F)))

lemma phiPoly_monic (θ : F) (p : ℕ) : (phiPoly θ p).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _

lemma phiPoly_natDegree (θ : F) (p : ℕ) : (phiPoly θ p).natDegree = p := by
  unfold phiPoly
  rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

lemma psiPoly_monic (θ : F) (m q : ℕ) : (psiPoly θ m q).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _

lemma psiPoly_natDegree (θ : F) (m q : ℕ) : (psiPoly θ m q).natDegree = q := by
  unfold psiPoly
  rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

lemma prod_pairs (t : F) (m : ℕ) :
    ∏ i ∈ Finset.range m, ((t + (2 + 2 * (i : F))) * (t + (1 + 2 * (i : F)))) =
      ∏ i ∈ Finset.range (2 * m), (t + 1 + (i : F)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      Finset.prod_range_succ, Finset.prod_range_succ]
    push_cast; ring

/-- the shifts `x_j = θ+2+2j`, `y_j = θ+1+2j` -/
def xsθ (θ : F) (m : ℕ) : Fin m → F := fun j => θ + 2 + 2 * ((j : ℕ) : F)
def ysθ (θ : F) (m : ℕ) : Fin m → F := fun j => θ + 1 + 2 * ((j : ℕ) : F)

lemma rho_eq_inv (θ : F) (m a : ℕ) :
    rho (xsθ θ m) (ysθ θ m) a = (∏ i ∈ Finset.range (2 * m), ((a : F) + θ + 1 + (i : F)))⁻¹ := by
  unfold rho
  congr 1
  simp only [xsθ, ysθ]
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => (((a : F) + (θ + 2 + 2 * (j : F))) *
    ((a : F) + (θ + 1 + 2 * (j : F))))) m]
  rw [show (∏ j ∈ Finset.range m, (((a : F) + (θ + 2 + 2 * (j : F))) *
    ((a : F) + (θ + 1 + 2 * (j : F))))) = ∏ j ∈ Finset.range m,
      ((((a : F) + θ) + (2 + 2 * (j : F))) * (((a : F) + θ) + (1 + 2 * (j : F)))) from
    Finset.prod_congr rfl fun j _ => by ring, prod_pairs]

/-- **Step (3b).**  `ρ(a) φ_p(a) ψ_q(a) = 1/(a+θ+p+1)_{2m-p-q}`. -/
lemma entry_eq (θ : F) (hθ : Gen θ) (m p q : ℕ) (hp : p < m) (hq : q < m) (a : ℕ) :
    rho (xsθ θ m) (ysθ θ m) a * (phiPoly θ p).eval (a : F) * (psiPoly θ m q).eval (a : F) =
      (pochr ((a : F) + θ + (p : F) + 1) (2 * m - p - q))⁻¹ := by
  have hg : ∀ z : ℤ, (a : F) + θ + (z : F) ≠ 0 := fun z h => by
    have := hθ ((a : ℤ) + z); push_cast at this; apply this; linear_combination h
  rw [rho_eq_inv]
  have hsplit : ∏ i ∈ Finset.range (2 * m), ((a : F) + θ + 1 + (i : F)) =
      (phiPoly θ p).eval (a : F) * pochr ((a : F) + θ + (p : F) + 1) (2 * m - p - q) *
        (psiPoly θ m q).eval (a : F) := by
    have h2m : 2 * m = p + ((2 * m - p - q) + q) := by omega
    conv_lhs => rw [h2m]
    rw [Finset.prod_range_add, Finset.prod_range_add]
    have e1 : (phiPoly θ p).eval (a : F) = ∏ i ∈ Finset.range p, ((a : F) + θ + 1 + (i : F)) := by
      simp [phiPoly, Polynomial.eval_prod]; exact Finset.prod_congr rfl fun i _ => by ring
    have e2 : pochr ((a : F) + θ + (p : F) + 1) (2 * m - p - q) =
        ∏ i ∈ Finset.range (2 * m - p - q), ((a : F) + θ + 1 + ((p + i : ℕ) : F)) := by
      unfold pochr
      exact Finset.prod_congr rfl fun i _ => by push_cast; ring
    have e3 : (psiPoly θ m q).eval (a : F) =
        ∏ i ∈ Finset.range q, ((a : F) + θ + 1 + ((p + (2 * m - p - q) + i : ℕ) : F)) := by
      simp only [psiPoly, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
        Polynomial.eval_C]
      refine Finset.prod_congr rfl fun i _ => ?_
      have : p + (2 * m - p - q) = 2 * m - q := by omega
      rw [this]; push_cast; ring
    rw [e1, e2, e3]
    ring
  rw [hsplit]
  have hP1 : (phiPoly θ p).eval (a : F) ≠ 0 := by
    simp only [phiPoly, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    have := hg (1 + (i : ℤ)); push_cast at this
    intro h; apply this; linear_combination h
  have hP3 : (psiPoly θ m q).eval (a : F) ≠ 0 := by
    simp only [psiPoly, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
    refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
    have := hg (((2 * m - q : ℕ) : ℤ) + 1 + (i : ℤ)); push_cast at this
    intro h; apply this; linear_combination h
  have hMid : pochr ((a : F) + θ + (p : F) + 1) (2 * m - p - q) ≠ 0 := by
    refine pochr_ne_zero _ _ fun i _ => ?_
    have := hg ((p : ℤ) + 1 + (i : ℤ)); push_cast at this
    intro h; apply this; linear_combination h
  field_simp

/-- **Prop hDelta, steps (1)–(3):** `Δ = V(x) V(y) · det[∑_{a<K} 1/(a+θ+p+1)_{2m-p-q}]_{p,q<m}`. -/
theorem delta_E (θ : F) (hθ : Gen θ) (K m : ℕ) :
    ((Cm K (xsθ θ m))ᵀ * Cm K (ysθ θ m)).det =
      Vprod (xsθ θ m) * Vprod (ysθ θ m) *
        (Matrix.of fun (p q : Fin m) => ∑ a : Fin K,
          (pochr (((a : ℕ) : F) + θ + ((p : ℕ) : F) + 1) (2 * m - (p : ℕ) - (q : ℕ)))⁻¹).det := by
  have hg : ∀ (a : ℕ) (z : ℤ), (a : F) + θ + (z : F) ≠ 0 := fun a z h => by
    have := hθ ((a : ℤ) + z); push_cast at this; apply this; linear_combination h
  rw [delta_eq_hankel (xsθ θ m) (ysθ θ m)
    (fun a i => by
      have := hg (a : ℕ) (2 + 2 * ((i : ℕ) : ℤ)); push_cast at this
      intro h; apply this; simp only [xsθ] at h; linear_combination h)
    (fun a i => by
      have := hg (a : ℕ) (1 + 2 * ((i : ℕ) : ℤ)); push_cast at this
      intro h; apply this; simp only [ysθ] at h; linear_combination h)]
  congr 1
  rw [← hankel_basis_change (fun a : Fin K => rho (xsθ θ m) (ysθ θ m) (a : ℕ))
    (fun p : Fin m => phiPoly θ p) (fun q : Fin m => psiPoly θ m q)
    (fun p => phiPoly_monic θ p) (fun p => phiPoly_natDegree θ p)
    (fun p => psiPoly_monic θ m p) (fun p => psiPoly_natDegree θ m p)]
  congr 1
  ext p q
  simp only [Matrix.of_apply]
  exact Finset.sum_congr rfl fun a _ => entry_eq θ hθ m p q p.2 q.2 a

end CatalanCore.Star.Leonard
