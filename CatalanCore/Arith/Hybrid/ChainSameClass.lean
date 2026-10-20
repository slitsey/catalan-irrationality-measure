module
public import CatalanCore.Arith.Hybrid.ChainCancellation
public import CatalanCore.Arith.Hybrid.ChainDeltaBounds
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE ChainClasses
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}
theorem delta_int1_ordered (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk4 : (4:ZMod p)*k=o) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y) (hzy : xs z≤ys y)
    (hc : NoCut (Cut p r (Singular p o)) (xs z) (ys y))
    (hd : (ys y : ZMod p)-(xs z : ZMod p)≠0) :
    Int1 p (delta Fr p r xs ys z y) := by
  let e:=chainTransport hzy hc
  let er : ChainIndex p r (xs z) → Fin r := chainNode
  let ec : ChainIndex p r (xs z) → Fin r := fun i=>chainNode (e i)
  have her : Function.Injective er:=chainNode_injective (Fact.out : p.Prime).pos
  have hec : Function.Injective ec:=(chainNode_injective (Fact.out : p.Prime).pos).comp e.injective
  have hr0 (a : Fin r) (ha : a∉Set.range er) : Sr Fr p r xs ys z a=0 := by
    apply Sr_support hL hp5 hN hr
    intro H
    exact ha (chain_image_of_mod hz a H.symm)
  have hc0 (a : Fin r) (ha : a∉Set.range ec) : Sc Fr p r xs ys a y=0 := by
    apply Sc_support hL hp5 hN hr
    intro H
    obtain ⟨j,hj⟩:=chain_image_of_mod hy a H
    exact ha ⟨e.symm j,by simpa [ec] using hj⟩
  have hrSum (f : Fin r→ℚ[X]) :
      (∑a,Sr Fr p r xs ys z a*f a)=∑i,Sr Fr p r xs ys z (er i)*f (er i) := by
    symm
    apply Fintype.sum_of_injective er her
    · intro a ha; rw [hr0 a ha,zero_mul]
    · intro i; rfl
  have hcSum (f : Fin r→ℚ[X]) :
      (∑a,f a*Sc Fr p r xs ys a y)=∑i,f (ec i)*Sc Fr p r xs ys (ec i) y := by
    symm
    apply Fintype.sum_of_injective ec hec
    · intro a ha; rw [hc0 a ha,mul_zero]
    · intro i; rfl
  have hneq (i j : ChainIndex p r (xs z)) : er i≠ec j := by
    intro H
    apply hd
    apply sub_eq_zero.mpr
    have H': ((er i).val : ZMod p)=((ec j).val : ZMod p):=congrArg (fun a:Fin r=>(a.val:ZMod p)) H
    simpa [er,ec,chainNode_zmod] using H'.symm
  have HB : ((Sr Fr p r xs ys)*(full Fr p r xs ys).toBlocks₁₂) z y =
      ∑i,Sr Fr p r xs ys z (er i)*C (Fr.Mn (er i).val (ys y)) := by
    rw [Matrix.mul_apply,hrSum]
    simp only [full_B_apply]
  have HC : ((full Fr p r xs ys).toBlocks₂₁*Sc Fr p r xs ys) z y =
      ∑i,C (Fr.Mn (xs z) (ec i).val)*Sc Fr p r xs ys (ec i) y := by
    rw [Matrix.mul_apply,hcSum]
    simp only [full_C_apply]
  have HA : (Sr Fr p r xs ys*(full Fr p r xs ys).toBlocks₁₁*Sc Fr p r xs ys) z y =
      ∑i,∑j,Sr Fr p r xs ys z (er i)*C (Fr.Mn (er i).val (ec j).val)*Sc Fr p r xs ys (ec j) y := by
    rw [Matrix.mul_apply,hcSum]
    simp only [Matrix.mul_apply]
    simp_rw [hrSum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [full_A_apply_ne _ _ (hneq i j)]
  have H:=restricted_delta_int1 hL hp5 hN hr hk4 hxN hyN z y hz hy hzy hc hd
  change Int1 p (_ - _ - _ + _) at H
  simpa only [delta,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    full_D_apply,HB,HC,HA,er,ec,e] using H
end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.delta_int1_ordered
