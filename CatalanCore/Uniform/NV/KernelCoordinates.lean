module
public import CatalanCore.Uniform.NV.PairSpace
@[expose] public section
open Polynomial Finset Matrix
open CatalanCore.Arith.Hybrid.FiniteFieldCorank
open CatalanCore.Rect.CharZeroNV
namespace CatalanCore.Uniform.NV
variable {K : Type*} [Field K] [DecidableEq K]

/-- A square indexing of arbitrary row and column sets, fixing common nodes. -/
structure NodeGeometry where
  rows : Finset K
  cols : Finset K
  equiv : rows ≃ cols
  align : ∀ a : (rows ∩ cols : Finset K), (equiv ⟨a.val,(mem_inter.mp a.property).1⟩).val = a.val
namespace NodeGeometry
variable (G : NodeGeometry (K := K))
def common (a : (G.rows ∩ G.cols : Finset K)) : G.rows := ⟨a.val,(mem_inter.mp a.property).1⟩
theorem common_injective : Function.Injective G.common := by
  intro a b h
  exact Subtype.ext (congrArg (fun x : G.rows => x.val) h)
theorem card_cols : G.cols.card = G.rows.card := by
  have h := Fintype.card_congr G.equiv
  simpa only [Fintype.card_coe] using h.symm

noncomputable def matrix (f tau : K → K) : Matrix G.rows G.rows K :=
  fun a b => loewnerEntry f tau a.val (G.equiv b).val
noncomputable def kernelWeights (v : G.rows → K) (x : K) : K :=
  if hx : x ∈ G.cols then v (G.equiv.symm ⟨x,hx⟩) else 0
@[simp] theorem kernelWeights_equiv (v : G.rows → K) (j : G.rows) :
    G.kernelWeights v (G.equiv j).val = v j := by simp [kernelWeights]

theorem row_eq (f tau : K → K) (v : G.rows → K) (a : G.rows) :
    loewnerRow G.cols f tau (G.kernelWeights v) a.val = (G.matrix f tau *ᵥ v) a := by
  calc
    _ = ∑ b : G.cols, loewnerEntry f tau a.val b.val*G.kernelWeights v b.val :=
      (Finset.sum_coe_sort G.cols (fun b : K => loewnerEntry f tau a.val b*G.kernelWeights v b)).symm
    _ = ∑ j : G.rows, loewnerEntry f tau a.val (G.equiv j).val*v j := by
      rw [← Equiv.sum_comp G.equiv]
      simp
    _ = _ := rfl

theorem kernel_hermite (f tau : K → K) (v : G.rows → K)
    (hv : G.matrix f tau *ᵥ v = 0) :
    Hermite (G.rows ∪ G.cols) (G.rows ∩ G.cols) f tau
      (numerator G.cols (G.kernelWeights v))
      (numerator G.cols (fun b => G.kernelWeights v b*f b)) where
  value x hx := by
    by_cases hb : x ∈ G.cols
    · exact kernel_value_inside G.cols f (G.kernelWeights v) x hb
    · have ha : x ∈ G.rows := (mem_union.mp hx).resolve_right hb
      apply kernel_value_outside G.cols f tau (G.kernelWeights v) x hb
      rw [G.row_eq f tau v ⟨x,ha⟩,hv]
      rfl
  jet x hx := by
    have ha := mem_inter.mp hx
    apply kernel_jet G.cols f tau (G.kernelWeights v) x ha.2
    rw [G.row_eq f tau v ⟨x,ha.1⟩,hv]
    rfl

noncomputable def pairs (f tau : K → K) :=
  pairSpace (G.rows ∪ G.cols) (G.rows ∩ G.cols) f tau (G.rows.card-1)
noncomputable def rightCoords (f tau : K → K) : G.pairs f tau →ₗ[K] (G.rows → K) where
  toFun P j := P.val.1.eval (G.equiv j).val / (punctured G.cols (G.equiv j).val).eval (G.equiv j).val
  map_add' := by intros;ext j;simp [add_div]
  map_smul' := by intros;ext j;simp [smul_eq_mul,mul_div_assoc]
noncomputable def leftCoords (f tau : K → K) : G.pairs f tau →ₗ[K] (G.rows → K) where
  toFun P j := P.val.1.eval j.val / (punctured G.rows j.val).eval j.val
  map_add' := by intros;ext j;simp [add_div]
  map_smul' := by intros;ext j;simp [smul_eq_mul,mul_div_assoc]
noncomputable def commonEval (f tau : K → K) :
    G.pairs f tau →ₗ[K] ((G.rows ∩ G.cols : Finset K) → K) where
  toFun P a := P.val.1.eval a.val
  map_add' := by intros;ext a;simp
  map_smul' := by intros;ext a;simp

theorem rightCoords_onto_kernel (f tau : K → K) (v : G.rows → K)
    (hv : G.matrix f tau *ᵥ v = 0) : ∃ P, G.rightCoords f tau P = v := by
  let p := numerator G.cols (G.kernelWeights v)
  let q := numerator G.cols (fun b => G.kernelWeights v b*f b)
  have hp : p.natDegree ≤ G.rows.card-1 := by
    simpa [G.card_cols] using natDegree_numerator_le G.cols (G.kernelWeights v)
  have hq : q.natDegree ≤ G.rows.card-1 := by
    simpa [G.card_cols] using natDegree_numerator_le G.cols (fun b => G.kernelWeights v b*f b)
  let P : G.pairs f tau := ⟨(p,q),hp,hq,G.kernel_hermite f tau v hv⟩
  refine ⟨P,?_⟩
  ext j
  change p.eval (G.equiv j).val / _ = v j
  rw [show p.eval (G.equiv j).val = G.kernelWeights v (G.equiv j).val *
      (punctured G.cols (G.equiv j).val).eval (G.equiv j).val from
    eval_numerator_punctured G.cols (G.kernelWeights v) (G.equiv j).property]
  rw [G.kernelWeights_equiv]
  exact mul_div_cancel_right₀ _ (punctured_eval_ne_zero _ _)

theorem leftCoords_in_kernel (f tau : K → K) (hn : 1 ≤ G.rows.card) (P : G.pairs f tau) :
    (G.matrix f tau).transpose *ᵥ G.leftCoords f tau P = 0 := by
  ext i
  have hrow : loewnerRow G.rows f tau
      (fun a => P.val.1.eval a / (punctured G.rows a).eval a) (G.equiv i).val = 0 := by
    apply pair_gives_kernel_row G.rows hn f tau P.val.1 P.val.2 P.property.1 P.property.2.1
    · intro b hb
      exact P.property.2.2.value b (mem_union.mpr (Or.inl hb))
    · exact P.property.2.2.value _ (mem_union.mpr (Or.inr (G.equiv i).property))
    · intro ha
      exact P.property.2.2.jet _ (mem_inter.mpr ⟨ha,(G.equiv i).property⟩)
  calc
    _ = ∑ j : G.rows, loewnerEntry f tau (G.equiv i).val j.val *
        (P.val.1.eval j.val / (punctured G.rows j.val).eval j.val) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun z : K => z*(P.val.1.eval j.val / (punctured G.rows j.val).eval j.val))
        (loewnerEntry_symm f tau j.val (G.equiv i).val)
    _ = loewnerRow G.rows f tau
        (fun a => P.val.1.eval a / (punctured G.rows a).eval a) (G.equiv i).val :=
      Finset.sum_coe_sort G.rows (fun a : K => loewnerEntry f tau (G.equiv i).val a *
        (P.val.1.eval a / (punctured G.rows a).eval a))
    _ = 0 := hrow

theorem rightCoords_common (f tau : K → K) (P : G.pairs f tau)
    (a : (G.rows ∩ G.cols : Finset K)) :
    G.rightCoords f tau P (G.common a) =
      ((punctured G.cols a.val).eval a.val)⁻¹*G.commonEval f tau P a := by
  change P.val.1.eval (G.equiv (G.common a)).val / _ = _
  have halign : (G.equiv (G.common a)).val = a.val := G.align a
  rw [halign]
  exact div_eq_inv_mul _ _
theorem leftCoords_common (f tau : K → K) (P : G.pairs f tau)
    (a : (G.rows ∩ G.cols : Finset K)) :
    G.leftCoords f tau P (G.common a) =
      ((punctured G.rows a.val).eval a.val)⁻¹*G.commonEval f tau P a := div_eq_inv_mul _ _
end NodeGeometry
end CatalanCore.Uniform.NV

