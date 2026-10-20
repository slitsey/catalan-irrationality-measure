module
public import CatalanCore.Arith.Hybrid.ChainPartners
public import CatalanCore.Arith.Hybrid.ChainLoewner
@[expose] public section
open Matrix Polynomial CatalanCore
namespace CatalanCore.Arith.Hybrid.ChainModel
open LemmaE ChainClasses
variable {p r N o k : ℕ} [Fact p.Prime] {Fr : Frame}
  {Z : Type} [Fintype Z] [DecidableEq Z] {xs ys : Z→ℕ}

/-- Actual-frame first-order cancellation along an arbitrary cut-free pair of chains. -/
theorem restricted_delta_int1 (hL : LamData Fr o) (hp5 : 5≤p) (hN : 4*N<p*p)
    (hr : r≤N) (hk4 : (4:ZMod p)*k=o) (hxN : ∀z,xs z<N) (hyN : ∀y,ys y<N)
    (z y : Z) (hz : r≤xs z) (hy : r≤ys y) (hzy : xs z≤ys y)
    (hc : NoCut (Cut p r (Singular p o)) (xs z) (ys y))
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
  let V := fun n=>Lv (singularNodes p o N) (deltaResidue p o) n
  let gamma := C (residueLift ((16*((ys y : ZMod p)-(xs z : ZMod p)))⁻¹))
  let l := C (residueLift (V (xs z)))
  let L := fun i : ChainIndex p r (xs z) => C (residueLift (V (chainNode i).val))
  have hzone : V (xs z)=V (ys y) := uniform_Lv_zone_eq hL.o_le hzy hc _
  have hchain (i : ChainIndex p r (xs z)) : V (chainNode i).val=V (chainNode (e i)).val :=
    uniform_Lv_chain_eq hL.o_le hzy hc _ i
  apply same_class_delta_int1 _ _ gamma l L
    (fun i=>Sr Fr p r xs ys z (chainNode i))
    (fun i=>Sc Fr p r xs ys (chainNode (e i)) y)
  · exact det_int1 (Q0_int1 hL hp5 hN hr)
  · exact residueLift_int1 _
  · exact residueLift_int1 _
  · intro i; exact residueLift_int1 _
  · exact fun i=>Sr_int1 hL hp5 hN hr hxN _ _
  · exact fun i=>Sc_int1 hL hp5 hN hr hyN _ _
  · exact fun i=>(partners_chain_cng hL hp5 hN hr hxN hyN z y hz hy hzy hc i).symm
  · have H := loewner_entry_cng hL hp5 hN hk4 (hxN z) (hyN y) hd rfl rfl hzone.symm
    simpa only [V, ←C_mul, sub_self, mul_zero] using H
  · intro i
    have H := loewner_entry_cng hL hp5 hN hk4
      ((chainNode i).isLt.trans_le hr) (hyN y) hd
      (by rw [chainNode_zmod]) rfl hzone.symm
    simpa only [←C_mul] using H
  · intro i
    have H := loewner_entry_cng hL hp5 hN hk4
      (hxN z) ((chainNode (e i)).isLt.trans_le hr) hd
      (by rw [chainNode_zmod]) rfl (hchain i).symm
    simpa only [←C_mul] using H
  · intro i j
    have H := loewner_entry_cng hL hp5 hN hk4
      ((chainNode i).isLt.trans_le hr) ((chainNode (e j)).isLt.trans_le hr) hd
      (by rw [chainNode_zmod,chainNode_zmod]) rfl (hchain j).symm
    simpa only [←C_mul] using H
end CatalanCore.Arith.Hybrid.ChainModel
#print axioms CatalanCore.Arith.Hybrid.ChainModel.restricted_delta_int1
