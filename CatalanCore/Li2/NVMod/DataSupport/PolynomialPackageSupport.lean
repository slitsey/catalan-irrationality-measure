module
public import CatalanCore.Li2.NVMod.PolynomialTransfer
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators
namespace CatalanCore.Li2.NVMod.DataSupport
noncomputable section

def momentResidueCheck (p n : ℕ) (source target : List (List ℤ)) : Bool :=
  decide (target=(source.take (2*n-1)).map (fun xs=>xs.map (fun (z : ℤ)=>z%(p:ℤ))))

theorem momentResidueCheck_sound (p n : ℕ) (source target : List (List ℤ))
    (hc : momentResidueCheck p n source target=true) (hlen : target.length=2*n-1)
    (e : ℕ) (he : e<2*n-1) :
    (coefficientsPoly (target.getD e [])).map (Int.castRingHom (ZMod p))=
      (coefficientsPoly (source.getD e [])).map (Int.castRingHom (ZMod p)) := by
  have ht : target=(source.take (2*n-1)).map (fun xs=>xs.map (fun (z : ℤ)=>z%(p:ℤ))) :=
    of_decide_eq_true hc
  have htake : e<(source.take (2*n-1)).length := by
    rw [ht,List.length_map] at hlen
    rwa [hlen]
  have hsrc : e<source.length:=by
    have hm:=htake
    rw [List.length_take] at hm
    omega
  have hrow : target.getD e []=(source.getD e []).map (fun (z : ℤ)=>z%(p:ℤ)) := by
    rw [ht]
    change ((source.take (2*n-1)).map (fun xs=>xs.map (fun (z : ℤ)=>z%(p:ℤ)))).getD e
      (([]:List ℤ).map (fun (z : ℤ)=>z%(p:ℤ)))=_
    rw [List.getD_map]
    congr 1
    rw [List.getD_eq_getElem _ _ htake,List.getD_eq_getElem _ _ hsrc,List.getElem_take]
  rw [hrow,coefficientsPoly_map,coefficientsPoly_map]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro z hz
  simp only [Function.comp_apply,Int.coe_castRingHom,ZMod.intCast_mod]

def oneOrderWith (h : ℤ) (size : ℕ) : ℤ :=
  (∑ i : Fin size,if 0≤h then -max 0 ((i.val:ℤ)-((h+1)/2).toNat) else -(i.val:ℤ))+
  (∑ j : Fin size,if 0≤h then -max 0 ((j.val:ℤ)-(h/2).toNat) else h-(j.val:ℤ))

theorem oneOrderWith_spec (A : TypeKey) : oneOrder A=oneOrderWith (h0 A) A.size := by
  rfl

structure KeyCertificate where
  input : EndpointInput
  prime : input.p.Prime
  endpoint0 : chk0 input=true
  endpoint1 : chk1 input=true
  endpointInf : chkInf input=true
  interior : PolynomialCert.InteriorChecked input

#print axioms oneOrderWith_spec
#print axioms momentResidueCheck_sound
end
end CatalanCore.Li2.NVMod.DataSupport
