module
public import CatalanCore.Arith.Hybrid.PeriodicPartners
public import CatalanCore.Arith.Hybrid.ChainAlgebra
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.Periodic.Model
open LemmaE ChainClasses ChainModel
variable {p r N : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}

lemma loewner_entry_cng (D : PoleData Fr p N) {A B : ℕ}
    (hA : A<N) (hB : B<N) {d a b : ZMod p} (hd : d≠0)
    (hdisp : (B:ZMod p)-A=d) (ha : D.V A=a) (hb : D.V B=b) :
    Cng p (C ((p:ℚ)*Fr.Mn A B))
      (C (residueLift (((red p Fr.norm)*d)⁻¹)) *
        (C (residueLift b)-C (residueLift a))) := by
  have g:=D.good_cross hA hB (by rwa [hdisp])
  rw [hdisp,ha,hb] at g
  have gm := (good_residueLift (((red p Fr.norm)*d)⁻¹)).mul
    ((good_residueLift b).sub (good_residueLift a))
  have H := good_constants_cng g gm
  simpa only [C_mul,C_sub] using H

theorem restricted_delta_int1 (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y) (hzy : xs z≤ys y)
    (hc : NoCut (Cut p r D.singular) (xs z) (ys y))
    (hd : (ys y : ZMod p)-(xs z : ZMod p)≠0) :
    let e := chainTransport hzy hc
    let sr := fun i : ChainIndex p r (xs z) => Sr Fr p r xs ys z (chainNode i)
    let sc := fun i : ChainIndex p r (xs z) => Sc Fr p r xs ys (chainNode (e i)) y
    Int1 p ((h Fr p r xs ys)^2*C (Fr.Mn (xs z) (ys y))-
      h Fr p r xs ys*(∑i,sr i*C (Fr.Mn (chainNode i).val (ys y)))-
      h Fr p r xs ys*(∑i,C (Fr.Mn (xs z) (chainNode (e i)).val)*sc i)+
      ∑i,∑j,sr i*C (Fr.Mn (chainNode i).val (chainNode (e j)).val)*sc j) := by
  dsimp only
  let e := chainTransport hzy hc
  let V := D.V
  let gamma := C (residueLift (((red p Fr.norm)*((ys y : ZMod p)-(xs z : ZMod p)))⁻¹))
  let l := C (residueLift (V (xs z)))
  let L := fun i : ChainIndex p r (xs z) => C (residueLift (V (chainNode i).val))
  have hzone : V (xs z)=V (ys y) := D.V_zone hzy (hyN y) hc
  have hchain (i : ChainIndex p r (xs z)) : V (chainNode i).val=V (chainNode (e i)).val :=
    D.V_chain hr hzy hc i
  apply same_class_delta_int1 _ _ gamma l L
    (fun i=>Sr Fr p r xs ys z (chainNode i))
    (fun i=>Sc Fr p r xs ys (chainNode (e i)) y)
  · exact det_int1 (Q0_int1 D hN hr)
  · exact residueLift_int1 _
  · exact residueLift_int1 _
  · intro i; exact residueLift_int1 _
  · exact fun i=>Sr_int1 D hN hr hxN _ _
  · exact fun i=>Sc_int1 D hN hr hyN _ _
  · exact fun i=>(partners_chain_cng D hN hr hxN hyN z y hz hy hzy hc i).symm
  · have H := loewner_entry_cng D (hxN z) (hyN y) hd rfl rfl hzone.symm
    simpa only [V, ←C_mul, sub_self, mul_zero] using H
  · intro i
    have H := loewner_entry_cng D
      ((chainNode i).isLt.trans_le hr) (hyN y) hd
      (by rw [chainNode_zmod]) rfl hzone.symm
    simpa only [←C_mul] using H
  · intro i
    have H := loewner_entry_cng D
      (hxN z) ((chainNode (e i)).isLt.trans_le hr) hd
      (by rw [chainNode_zmod]) rfl (hchain i).symm
    simpa only [←C_mul] using H
  · intro i j
    have H := loewner_entry_cng D
      ((chainNode i).isLt.trans_le hr) ((chainNode (e j)).isLt.trans_le hr) hd
      (by rw [chainNode_zmod,chainNode_zmod]) rfl (hchain j).symm
    simpa only [←C_mul] using H

theorem delta_int1_ordered (D : PoleData Fr p N) (hN : N<p*p)
    (hr : r≤N) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y) (hzy : xs z≤ys y)
    (hc : NoCut (Cut p r D.singular) (xs z) (ys y))
    (hd : (ys y : ZMod p)-(xs z : ZMod p)≠0) :
    Int1 p (delta Fr p r xs ys z y) := by
  let e:=chainTransport hzy hc
  let er : ChainIndex p r (xs z) → Fin r := chainNode
  let ec : ChainIndex p r (xs z) → Fin r := fun i=>chainNode (e i)
  have her : Function.Injective er:=chainNode_injective (Fact.out : p.Prime).pos
  have hec : Function.Injective ec:=(chainNode_injective (Fact.out : p.Prime).pos).comp e.injective
  have hr0 (a : Fin r) (ha : a∉Set.range er) : Sr Fr p r xs ys z a=0 := by
    apply Sr_support D hN hr
    intro H
    exact ha (chain_image_of_mod hz a H.symm)
  have hc0 (a : Fin r) (ha : a∉Set.range ec) : Sc Fr p r xs ys a y=0 := by
    apply Sc_support D hN hr
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
  have H:=restricted_delta_int1 D hN hr hxN hyN z y hz hy hzy hc hd
  change Int1 p (_ - _ - _ + _) at H
  simpa only [delta,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,
    full_D_apply,HB,HC,HA,er,ec,e] using H
end CatalanCore.Arith.Hybrid.Periodic.Model
