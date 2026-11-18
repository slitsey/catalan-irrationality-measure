module
public import CatalanCore.Li2.NVMod.ResRec
public import CatalanCore.Linalg.HankelRecurrence
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod
noncomputable section

structure ScalarTable where
  residues : List ℕ
  values : List ℕ

def scalarTableCheck (I : EndpointInput) [Fact I.p.Prime] (C : ScalarTable) : Bool :=
  decide ((I.D:ZMod I.p)≠0) &&
    C.residues == (List.range (I.p-2)).map (·+2) &&
    C.values.length == C.residues.length &&
    (List.range C.residues.length).all (fun j=>
      let r := C.residues.getD j 0
      let v := C.values.getD j 0
      decide (v<I.p) && v != 0 &&
        decide (CatalanCore.Linalg.scalarEval I.key.size (momentRow I.p I.key r)=some (v:ZMod I.p)))

structure ScalarTableChecked (I : EndpointInput) [Fact I.p.Prime] (C : ScalarTable) : Prop where
  good_prime : goodFormulaPrime I.key I.p
  checked : scalarTableCheck I C=true

theorem momentRow_getD (p : ℕ) [Fact p.Prime] (A : TypeKey) (r e : ℕ) (he : e<2*A.size-1) :
    (momentRow p A r).getD e 0=momentFormula (ZMod p) A (r:ZMod p) e := by
  rw [List.getD_eq_getElem _ _ (by simpa only [momentRow,List.length_map,List.length_range] using he)]
  simp only [momentRow,List.getElem_map,List.getElem_range,momentNat,ZMod.natCast_zmod_val]

theorem scalar_table_sound (I : EndpointInput) [Fact I.p.Prime]
    (C : ScalarTable) (hC : ScalarTableChecked I C) (r : ZMod I.p)
    (hr : r≠0) (h1 : r≠1) : ((I.F).map (Int.castRingHom (ZMod I.p))).eval r≠0 := by
  have hc : (I.D:ZMod I.p)≠0 ∧
      C.residues=(List.range (I.p-2)).map (·+2) ∧
      C.values.length=C.residues.length ∧
      ∀ j<C.residues.length,C.values.getD j 0<I.p ∧ C.values.getD j 0≠0 ∧
        CatalanCore.Linalg.scalarEval I.key.size (momentRow I.p I.key (C.residues.getD j 0))=
          some (C.values.getD j 0:ZMod I.p) := by
    simpa [scalarTableCheck,and_assoc] using hC.checked
  have hr0 : r.val≠0 := by
    intro hz
    have he := ZMod.natCast_zmod_val r
    rw [hz,Nat.cast_zero] at he
    exact hr he.symm
  have hr1 : r.val≠1 := by
    intro hz
    have he := ZMod.natCast_zmod_val r
    rw [hz,Nat.cast_one] at he
    exact h1 he.symm
  have hrp : r.val<I.p := ZMod.val_lt r
  have hlen : C.residues.length=I.p-2 := by rw [hc.2.1];simp
  let j := r.val-2
  have hj : j<C.residues.length := by rw [hlen];dsimp only [j];omega
  have hres : C.residues.getD j 0=r.val := by
    rw [hc.2.1]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_map,List.length_range];rw [←hlen];exact hj)]
    simp only [List.getElem_map,List.getElem_range]
    dsimp only [j]
    omega
  have hv := hc.2.2.2 j hj
  rw [hres] at hv
  have hv0 : (C.values.getD j 0:ZMod I.p)≠0 :=
    natCast_zmod_ne_zero_lt I.p _ (by omega) hv.1
  have hd := CatalanCore.Linalg.scalarEval_sound I.key.size (momentRow I.p I.key r.val)
    (C.values.getD j 0:ZMod I.p) hv.2.2
  let M := CatalanCore.Linalg.hankel (momentRow I.p I.key r.val) I.key.size 0
  have hm : M.det≠0 := by rw [←hd];exact hv0
  let φ : ℤ[X]→+*ZMod I.p := Polynomial.eval₂RingHom (Int.castRingHom (ZMod I.p)) r
  let s : ZMod I.p := (I.D:ZMod I.p)*r^I.clearZ*(1-r)^I.clearOne
  have hs : s≠0 := mul_ne_zero (mul_ne_zero hc.1 (pow_ne_zero _ hr))
    (pow_ne_zero _ (sub_ne_zero.mpr h1.symm))
  have hmat : φ.mapMatrix (Matrix.of fun i j : Fin I.key.size=>I.mz (i.val+j.val))=s • M := by
    apply Matrix.ext
    intro i k
    change (I.mz (i.val+k.val)).eval₂ (Int.castRingHom (ZMod I.p)) r=
      s*(momentRow I.p I.key r.val).getD (0+i.val+k.val) 0
    rw [←Polynomial.eval_map]
    rw [zero_add,momentRow_getD I.p I.key r.val (i.val+k.val) (by have hi:=i.isLt;have hk:=k.isLt;omega),
      ZMod.natCast_zmod_val]
    exact moment_formula_mod I hC.good_prime r hr h1 i k
  have he : ((I.F).map (Int.castRingHom (ZMod I.p))).eval r=s^I.key.size*M.det := by
    rw [Polynomial.eval_map]
    change φ I.F=_
    rw [EndpointInput.F,RingHom.map_det,hmat,Matrix.det_smul,Fintype.card_fin]
  rw [he]
  exact mul_ne_zero (pow_ne_zero _ hs) hm

#print axioms scalar_table_sound
end
end CatalanCore.Li2.NVMod
