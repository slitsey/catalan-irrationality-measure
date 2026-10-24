module
public import CatalanCore.Basic.ZModGood
public import CatalanArchive.CatalanCore.Linalg.CauchyPolynomial.Kernel
@[expose] public section
open Finset Polynomial Matrix CatalanCore
namespace CatalanCore.Arith.Hybrid
open CatalanCore.Linalg.CauchyPolynomial
variable {p K m n : ℕ} [Fact p.Prime]

/-- Barycentric Cauchy-kernel coordinates reduce entrywise. All denominators
are differences of distinct zone residues, so the basis is independent of U. -/
theorem good_cauchy_residue_basis (x : Fin K→ℚ) (y : Fin m→ℚ)
    (xb : Fin K→ZMod p) (yb : Fin m→ZMod p)
    (hx : ∀i,Good p (x i) (xb i)) (hy : ∀j,Good p (y j) (yb j))
    (hxi : Function.Injective xb) (hxy : ∀j i,yb j≠xb i)
    (i : Fin K) (j : Fin n) :
    Good p (residueBasis x (denom y) n i j) (residueBasis xb (denom yb) n i j) := by
  have hB : Good p ((denom y).eval (x i)) ((denom yb).eval (xb i)) := by
    simpa only [denom,Lagrange.eval_nodal] using
      Good.prod univ (fun a=>x i-y a) (fun a=>xb i-yb a) (fun a _=>(hx i).sub (hy a))
  have hW : Good p (nodeWeight x i) (nodeWeight xb i) := by
    unfold nodeWeight Lagrange.nodalWeight
    apply Good.prod
    intro a ha
    apply ((hx i).sub (hx a)).inv
    exact sub_ne_zero.mpr (fun H=>(mem_erase.mp ha).1 (hxi H).symm)
  exact (hB.mul hW).mul ((hx i).pow' j.val)

/-- The full residue basis has prime-unit determinant. Its initial columns
are the exact rational Cauchy kernel, so no residue-function-field lifts are needed. -/
theorem cauchy_residue_basis_unit (x : Fin K→ℚ) (y : Fin m→ℚ)
    (xb : Fin K→ZMod p) (yb : Fin m→ZMod p)
    (hx : ∀i,Good p (x i) (xb i)) (hy : ∀j,Good p (y j) (yb j))
    (hxi : Function.Injective xb) (hxy : ∀j i,yb j≠xb i) :
    Good p (residueBasis x (denom y) K).det (residueBasis xb (denom yb) K).det ∧
      (residueBasis xb (denom yb) K).det≠0 := by
  refine ⟨red_det _ _ (good_cauchy_residue_basis x y xb yb hx hy hxi hxy),?_⟩
  by_cases hK : K=0
  · subst K;simpa using (one_ne_zero : (1:ZMod p)≠0)
  have hB : ∀i,(denom yb).eval (xb i)≠0 := by
    intro i
    exact Lagrange.eval_nodal_not_at_node (fun j _=>(hxy j i).symm)
  have hi := basis_injective xb hxi (denom yb) hB (Nat.pos_of_ne_zero hK) (le_refl K)
  have hu : IsUnit (residueBasis xb (denom yb) K) :=
    Matrix.mulVec_injective_iff_isUnit.mp hi
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)

theorem rational_cauchy_kernel_zero (x : Fin K→ℚ) (y : Fin m→ℚ)
    (xb : Fin K→ZMod p) (yb : Fin m→ZMod p)
    (hx : ∀i,Good p (x i) (xb i)) (hy : ∀j,Good p (y j) (yb j))
    (hxi : Function.Injective xb) (hxy : ∀j i,yb j≠xb i)
    (hsize : m+n≤K) (v : Fin n→ℚ) :
    (cauchy x y).transpose *ᵥ (residueBasis x (denom y) n *ᵥ v)=0 := by
  have hxinj : Function.Injective x := by
    intro i j hij
    apply hxi
    have H:=congrArg (red p) hij
    simpa only [(hx i).eq,(hx j).eq] using H
  have hdis : ∀j i,y j≠x i := by
    intro j i H
    apply hxy j i
    have H':=congrArg (red p) H
    simpa only [(hy j).eq,(hx i).eq] using H'
  exact basis_cauchy_zero x hxinj y hdis hsize v
end CatalanCore.Arith.Hybrid
