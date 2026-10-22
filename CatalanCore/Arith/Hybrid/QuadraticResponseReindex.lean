module
public import CatalanCore.Arith.Hybrid.FreeLongBoundary
@[expose] public section
open Finset Matrix
namespace CatalanCore.Arith.Hybrid

section Reindex
variable {K ι ι' : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- The inverse quadratic response is invariant under a relabelling of the index set.  Together with
`completion_quadraticResponse` this is the combinatorial half of `response_long_eq`: a free residue
chain is the source chain, or the source chain completed by one node, up to such a relabelling. -/
theorem quadraticResponse_reindex (e : ι ≃ ι') (Q : Matrix ι ι K) (Q' : Matrix ι' ι' K)
    (u : ι → K) (u' : ι' → K) (hQ : ∀ i j, Q' (e i) (e j) = Q i j) (hu : ∀ i, u' (e i) = u i) :
    quadraticResponse Q' u' = quadraticResponse Q u := by
  have hsub : Q = Q'.submatrix e e := by ext i j; exact (hQ i j).symm
  have hu' : u = u' ∘ e := by funext i; exact (hu i).symm
  unfold quadraticResponse
  rw [hsub, Matrix.inv_submatrix_equiv, hu']
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Function.comp_apply]
  rw [← Equiv.sum_comp e.symm]
  simp only [Equiv.apply_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← Equiv.sum_comp e.symm]
  simp [Equiv.apply_symm_apply]

end Reindex

#print axioms quadraticResponse_reindex
end CatalanCore.Arith.Hybrid
