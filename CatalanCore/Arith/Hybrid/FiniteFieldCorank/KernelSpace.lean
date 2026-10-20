module

public import CatalanCore.Arith.Hybrid.FiniteFieldCorank.Moments
public import CatalanCore.Arith.Hybrid.FiniteFieldCorank

@[expose] public section

open Polynomial Matrix Module

namespace CatalanCore.Arith.Hybrid.FiniteFieldCorank

variable {k : Type*} [Field k] [DecidableEq k] {n : ℕ}

noncomputable def kernelPolynomialSpace (M : Matrix (Fin n) (Fin n) k) :
    Submodule k k[X] :=
  LinearMap.range ((Polynomial.ofFn n).comp (LinearMap.ker M.mulVecLin).subtype)

instance (M : Matrix (Fin n) (Fin n) k) : FiniteDimensional k (kernelPolynomialSpace M) := by
  unfold kernelPolynomialSpace
  infer_instance

lemma finrank_kernelPolynomialSpace (M : Matrix (Fin n) (Fin n) k) :
    finrank k (kernelPolynomialSpace M) = finrank k (LinearMap.ker M.mulVecLin) := by
  apply LinearMap.finrank_range_of_inj
  exact (Polynomial.injective_ofFn n).comp Subtype.val_injective

lemma kernelPolynomialSpace_degree (M : Matrix (Fin n) (Fin n) k) (hn : 1 ≤ n)
    (P : kernelPolynomialSpace M) : (P : k[X]).natDegree < n := by
  have hmem : ∃ v : LinearMap.ker M.mulVecLin,
      Polynomial.ofFn n (v : Fin n → k) = (P : k[X]) := P.property
  obtain ⟨v, hv⟩ := hmem
  calc
    (P : k[X]).natDegree = (Polynomial.ofFn n (v : Fin n → k)).natDegree :=
      congrArg Polynomial.natDegree hv.symm
    _ < n := ofFn_natDegree_lt hn (v : Fin n → k)

lemma kernelPolynomialSpace_moments (s : Finset k) (w : k → k)
    (P : kernelPolynomialSpace (momentMatrix s w n)) (j : ℕ) (hj : j < n) :
    ∑ y ∈ s, w y * (P : k[X]).eval y * y ^ j = 0 := by
  have hmem : ∃ v : LinearMap.ker (momentMatrix s w n).mulVecLin,
      Polynomial.ofFn n (v : Fin n → k) = (P : k[X]) := P.property
  obtain ⟨v, hv⟩ := hmem
  have hz := congrFun v.property ⟨j, hj⟩
  change (momentMatrix s w n *ᵥ (v : Fin n → k)) ⟨j, hj⟩ = 0 at hz
  rw [momentMatrix_mulVec] at hz
  simpa only [hv] using hz

end CatalanCore.Arith.Hybrid.FiniteFieldCorank
