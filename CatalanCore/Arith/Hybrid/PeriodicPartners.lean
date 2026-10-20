module
public import CatalanCore.Arith.Hybrid.PeriodicModelBounds
public import CatalanCore.Arith.Hybrid.ChainAlgebra
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.Periodic.Model
open LemmaE ChainClasses ChainModel
variable {p r N : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}

lemma chainMatrix_primitive (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) {z : ℕ} : gn p (chainMatrix (p:=p) Fr r z).det=1 := by
  apply prim_det_shift
  intro i j
  exact D.square_mem hN ((chainNode i).isLt.trans_le hr) ((chainNode j).isLt.trans_le hr)

lemma chainMatrix_cng (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) {z w : ℕ} (hzw : z≤w) (hc : NoCut (Cut p r D.singular) z w)
    (i j : ChainIndex p r z) :
    Cng p (chainMatrix (p:=p) Fr r z i j)
      (chainMatrix (p:=p) Fr r w (chainTransport hzw hc i) (chainTransport hzw hc j)) := by
  have H := D.chain_cng hN hr hzw hc i j
  simpa only [chainMatrix, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, Equiv.apply_eq_iff_eq] using
    H.add (Cng.refl (X*(if i=j then 1 else 0)))

lemma Sr_chain_solve (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (z : Z) (hz : r≤xs z) (i : ChainIndex p r (xs z)) :
    ((fun j : ChainIndex p r (xs z) => Sr Fr p r xs ys z (chainNode j)) ᵥ*
      chainMatrix (p:=p) Fr r (xs z)) i =
      h Fr p r xs ys * C2 Fr p r xs ys z (chainNode i) := by
  have Hv := vecMul_restrict (Q0 Fr p r xs ys) (Sr Fr p r xs ys z)
    (@chainNode p r (xs z)) (chainNode_injective (Fact.out : p.Prime).pos)
    (fun a ha => Sr_support D hN hr z a (by
      intro he; exact ha (chain_image_of_mod hz a he.symm))) i
  rw [Q0_chain] at Hv
  refine (show _ = _ from Hv).trans ?_
  have H := congrArg (fun M => M z (chainNode i))
    (modelRow_mul (fun a : Fin r => a.val%p) (fun z=>xs z%p)
      (Q0 Fr p r xs ys) (C2 Fr p r xs ys))
  simpa only [Sr, h, Matrix.mul_apply, Matrix.vecMul, dotProduct,
    Matrix.smul_apply, smul_eq_mul, blockRect, chainNode_mod, ite_true] using H

lemma Sc_chain_solve (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (y : Z) (hy : r≤ys y) (i : ChainIndex p r (ys y)) :
    (chainMatrix (p:=p) Fr r (ys y) *ᵥ
      (fun j : ChainIndex p r (ys y) => Sc Fr p r xs ys (chainNode j) y)) i =
      h Fr p r xs ys * B2 Fr p r xs ys (chainNode i) y := by
  have Hv := mulVec_restrict (Q0 Fr p r xs ys) (fun a=>Sc Fr p r xs ys a y)
    (@chainNode p r (ys y)) (chainNode_injective (Fact.out : p.Prime).pos)
    (fun a ha => Sc_support D hN hr a y (by
      intro he; exact ha (chain_image_of_mod hy a he))) i
  rw [Q0_chain] at Hv
  refine (show _ = _ from Hv).trans ?_
  have H := congrArg (fun M => M (chainNode i) y)
    (mul_modelCol (fun a : Fin r => a.val%p) (fun y=>ys y%p)
      (Q0 Fr p r xs ys) (B2 Fr p r xs ys))
  simpa only [Sc, h, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.smul_apply, smul_eq_mul, blockRect, chainNode_mod, ite_true] using H

theorem partners_chain_cng (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y) (hzy : xs z≤ys y)
    (hc : NoCut (Cut p r D.singular) (xs z) (ys y))
    (i : ChainIndex p r (xs z)) :
    Cng p (Sr Fr p r xs ys z (chainNode i))
      (Sc Fr p r xs ys (chainNode (chainTransport hzy hc i)) y) := by
  let e := chainTransport hzy hc
  let M := chainMatrix (p:=p) Fr r (xs z)
  let M' := (chainMatrix (p:=p) Fr r (ys y)).submatrix e e
  let v := fun j : ChainIndex p r (xs z) => Sr Fr p r xs ys z (chainNode j)
  let w := fun j : ChainIndex p r (xs z) => Sc Fr p r xs ys (chainNode (e j)) y
  apply row_partners_cng M M'
    (fun a b => by
      change Int1 p (chainMatrix (p:=p) Fr r (xs z) a b)
      rw [←Q0_chain (xs:=xs) (ys:=ys)]
      exact Q0_int1 D hN hr _ _)
    (chainMatrix_primitive D hN hr) v w
    (fun j=>Sc_int1 D hN hr hyN _ _)
    (fun a b=>(chainMatrix_cng D hN hr hzy hc a b).symm)
  intro j
  have Hv := Sr_chain_solve (ys:=ys) D hN hr z hz j
  have Hw := Sc_chain_solve (xs:=xs) D hN hr y hy (e j)
  have Hw' : (w ᵥ* M') j = h Fr p r xs ys * B2 Fr p r xs ys (chainNode (e j)) y := by
    change (∑a, Sc Fr p r xs ys (chainNode (e a)) y *
      chainMatrix (p:=p) Fr r (ys y) (e a) (e j)) = _
    have he := e.sum_comp (fun a => Sc Fr p r xs ys (chainNode a) y *
      chainMatrix (p:=p) Fr r (ys y) a (e j))
    rw [he]
    convert Hw using 1
    apply Finset.sum_congr rfl
    intro a _
    rw [chainMatrix_symmetric, mul_comm]
  change Cng p ((v ᵥ* M) j) ((w ᵥ* M') j)
  rw [show (v ᵥ* M) j = _ from Hv, Hw']
  apply Cng.mul_left_integral
  · exact det_int1 (Q0_int1 D hN hr)
  · rw [C2_apply, B2_apply]
    rw [Mn_symm (Fr:=Fr) (xs z) (chainNode j).val]
    exact D.zone_chain_cng hN hr (hxN z) (hyN y) hzy hc j
end CatalanCore.Arith.Hybrid.Periodic.Model
