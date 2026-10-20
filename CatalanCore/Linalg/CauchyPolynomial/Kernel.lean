module

public import CatalanCore.Linalg.CauchyPolynomial
public import Mathlib.Algebra.Polynomial.OfFn

@[expose] public section

open scoped BigOperators
open Polynomial Matrix
namespace CatalanCore.Linalg.CauchyPolynomial
variable {k : Type*} [Field k] [DecidableEq k] {K m n : ℕ}

lemma basis_mulVec (low : Fin K → k) (B : k[X]) (v : Fin n → k) :
    residueBasis low B n *ᵥ v = residueVec low B (ofFn n v) := by
  classical
  ext a
  simp only [Matrix.mulVec, dotProduct, residueBasis, residueVec,
    ofFn_eq_sum_monomial, eval_finsetSum, eval_monomial]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma basis_injective (low : Fin K → k) (hinj : Function.Injective low)
    (B : k[X]) (hB : ∀ a, B.eval (low a) ≠ 0) (hn : 0 < n) (hnK : n ≤ K) :
    Function.Injective (Matrix.toLin' (residueBasis low B n)) := by
  classical
  apply (injective_iff_map_eq_zero _).2
  intro v hv
  have hz : ofFn n v = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj
    · intro a
      have ha := congrFun hv a
      change (residueBasis low B n *ᵥ v) a = 0 at ha
      rw [basis_mulVec] at ha
      exact (mul_eq_zero.mp ((mul_eq_zero.mp ha).resolve_right
        (nodeWeight_ne_zero low hinj a))).resolve_left (hB a)
    · simpa using lt_of_lt_of_le (ofFn_natDegree_lt hn v) hnK
  exact (injective_ofFn n) (by simpa using hz)

lemma basis_cauchy_zero (low : Fin K → k) (hinj : Function.Injective low)
    (border : Fin m → k) (hd : ∀ j a, border j ≠ low a)
    (hdeg : m + n ≤ K) (v : Fin n → k) :
    (cauchy low border).transpose *ᵥ (residueBasis low (denom border) n *ᵥ v) = 0 := by
  classical
  have hb : (denom border).natDegree + n ≤ K := by
    simpa [denom, Lagrange.natDegree_nodal] using hdeg
  have he : (cauchy low border).transpose * residueBasis low (denom border) n = 0 := by
    ext j i
    have hs := basis_sum low hinj (denom border) hb i (border j) (hd j)
    have hz : (denom border).eval (border j) = 0 :=
      Lagrange.eval_nodal_at_node (Finset.mem_univ j)
    simpa [Matrix.mul_apply, Matrix.transpose_apply, cauchy, div_eq_mul_inv,
      mul_comm, hz] using hs
  rw [Matrix.mulVec_mulVec, he, Matrix.zero_mulVec]



lemma cauchy_kernel_exists (low : Fin K → k) (hinj : Function.Injective low)
    (border : Fin m → k) (hbinj : Function.Injective border)
    (hd : ∀ j a, border j ≠ low a) (hn : 0 < n) (hsize : m + n = K)
    (v : Fin K → k) (hv : (cauchy low border).transpose *ᵥ v = 0) :
    ∃ w : Fin n → k, residueBasis low (denom border) n *ᵥ w = v := by
  classical
  let f := Lagrange.interpolate Finset.univ low (fun a => v a / nodeWeight low a)
  have hf : f.natDegree < K := by
    by_cases hz : f = 0
    · simp [hz]; omega
    · apply (natDegree_lt_iff_degree_lt hz).mpr
      simpa [f] using Lagrange.degree_interpolate_lt
        (s := Finset.univ) (r := fun a => v a / nodeWeight low a) hinj.injOn
  have hfa (a : Fin K) : f.eval (low a) = v a / nodeWeight low a :=
    Lagrange.eval_interpolate_at_node (fun a => v a / nodeWeight low a) hinj.injOn (Finset.mem_univ a)
  have hfj (j : Fin m) : f.eval (border j) = 0 := by
    have hs := sum_residue_div low hinj f hf (border j) (hd j)
    have he : (∑ a, nodeWeight low a * f.eval (low a) / (border j - low a)) = 0 := by
      have hvj := congrFun hv j
      change (∑ a, (1 / (border j - low a)) * v a) = 0 at hvj
      simp_rw [hfa, mul_div_cancel₀ _ (nodeWeight_ne_zero low hinj _)]
      simpa [div_eq_mul_inv, mul_comm] using hvj
    rw [he] at hs
    exact (div_eq_zero_iff).mp hs.symm |>.resolve_right
      (Lagrange.eval_nodal_not_at_node (fun a _ => hd j a))
  have hdiv : denom border ∣ f := by
    simpa [denom, Lagrange.nodal] using
      Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hbinj)
        (fun j => (dvd_iff_isRoot).mpr (hfj j))
  obtain ⟨p, hp⟩ := hdiv
  have hpdeg : p.natDegree < n := by
    by_cases hz : p = 0
    · simp [hz]; exact hn
    · rw [hp, natDegree_mul (show denom border ≠ 0 from Lagrange.nodal_ne_zero) hz] at hf
      simp only [denom, Lagrange.natDegree_nodal, Finset.card_univ, Fintype.card_fin] at hf
      omega
  refine ⟨toFn n p, ?_⟩
  rw [basis_mulVec, ofFn_comp_toFn_eq_id_of_natDegree_lt hpdeg]
  ext a
  have ha := hfa a
  rw [hp, eval_mul] at ha
  simp only [residueVec]
  rw [ha, div_mul_cancel₀ _ (nodeWeight_ne_zero low hinj a)]





/-- Residue polynomials give all, and only, Cauchy null vectors. -/
theorem range_basis_eq_ker (low : Fin K → k) (hinj : Function.Injective low)
    (border : Fin m → k) (hbinj : Function.Injective border)
    (hd : ∀ j a, border j ≠ low a) (hn : 0 < n) (hsize : m + n = K) :
    LinearMap.range (Matrix.toLin' (residueBasis low (denom border) n)) =
      LinearMap.ker (Matrix.toLin' (cauchy low border).transpose) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact basis_cauchy_zero low hinj border hd hsize.le w
  · intro hv
    exact cauchy_kernel_exists low hinj border hbinj hd hn hsize v hv

end CatalanCore.Linalg.CauchyPolynomial


#print axioms CatalanCore.Linalg.CauchyPolynomial.range_basis_eq_ker
#print axioms CatalanCore.Linalg.CauchyPolynomial.basis_injective
