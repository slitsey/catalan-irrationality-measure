module
public import CatalanArchive.CatalanCore.Linalg.CauchyPolynomial.Kernel
public import CatalanArchive.CatalanCore.Linalg.PrincipalDeletion.BorderRescue
@[expose] public section
open Polynomial Matrix
namespace CatalanCore.Linalg.CauchyPolynomial
variable {k : Type*} [Field k] [DecidableEq k] {K m n : ℕ}

/-- Cauchy residue coordinates reduce low-principal rescue to compressed nullity. -/
theorem exists_low_minor_ne (low : Fin K → k) (hinj : Function.Injective low)
    (bx byn : Fin m → k) (hbx : Function.Injective bx) (hby : Function.Injective byn)
    (hdx : ∀ j a, bx j ≠ low a) (hdy : ∀ j a, byn j ≠ low a)
    (hn : 0 < n) (hsize : m + n = K) (M : Matrix (Fin K) (Fin K) k)
    (hGram : ((cauchy low bx).transpose * cauchy low byn).det ≠ 0)
    (hSym : ((residueBasis low (denom byn) n).transpose * M *
      residueBasis low (denom bx) n).transpose =
      (residueBasis low (denom byn) n).transpose * M * residueBasis low (denom bx) n) :
    ∃ s : Finset (Fin K), s.card = Module.finrank k
      (LinearMap.ker ((residueBasis low (denom byn) n).transpose * M *
        residueBasis low (denom bx) n).mulVecLin) ∧
      ((Matrix.fromBlocks M (cauchy low byn) (cauchy low bx).transpose 0).submatrix
        (Sum.map (Subtype.val : {a // a ∉ s} → Fin K) id)
        (Sum.map (Subtype.val : {a // a ∉ s} → Fin K) id)).det ≠ 0 := by
  let V := residueBasis low (denom bx) n
  let W := residueBasis low (denom byn) n
  let E := residueBasis low (1 : k[X]) n
  have hV : (cauchy low bx).transpose * V = 0 := by
    apply Matrix.mulVec_injective
    funext v
    simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using
      basis_cauchy_zero low hinj bx hdx (by omega : m + n ≤ K) v
  have hW : (cauchy low byn).transpose * W = 0 := by
    apply Matrix.mulVec_injective
    funext v
    simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using
      basis_cauchy_zero low hinj byn hdy (by omega : m + n ≤ K) v
  have hdx' : ∀ a, (denom bx).eval (low a) ≠ 0 := fun a =>
    Lagrange.eval_nodal_not_at_node (fun j _ => (hdx j a).symm)
  have hdy' : ∀ a, (denom byn).eval (low a) ≠ 0 := fun a =>
    Lagrange.eval_nodal_not_at_node (fun j _ => (hdy j a).symm)
  obtain ⟨s, hs, hdet⟩ := PrincipalDeletion.exists_bordered_principal_compl_ne_zero
    M (cauchy low bx) (cauchy low byn) V W E
    (fun a => (denom bx).eval (low a)) (fun a => (denom byn).eval (low a))
    hdx' hdy' hGram hV hW
    (cauchy_kernel_exists low hinj bx hbx hdx hn hsize)
    (cauchy_kernel_exists low hinj byn hby hdy hn hsize) hSym
    (by intro p a; simp only [V, E, Matrix.mulVec, dotProduct, residueBasis,
                              Polynomial.eval_one, one_mul, Finset.mul_sum]; congr 1; ext i; ring)
    (by intro p a; simp only [W, E, Matrix.mulVec, dotProduct, residueBasis,
                              Polynomial.eval_one, one_mul, Finset.mul_sum]; congr 1; ext i; ring)
    (basis_injective low hinj 1 (by simp) hn (by omega))
  exact ⟨s, hs, by rwa [PrincipalDeletion.det_low_compl_eq] at hdet⟩
end CatalanCore.Linalg.CauchyPolynomial
#print axioms CatalanCore.Linalg.CauchyPolynomial.exists_low_minor_ne
