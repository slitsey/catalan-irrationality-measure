module
public import CatalanCore.Li2.DecayCert.Lattice.Defs
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Lists.Stieltjes
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Transport
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open Polynomial Set
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.LatticeGate

def energyCenter (d : LatticeInput) (w : LatticeEnergyWitness) : ℚ :=
  d.first.mid.1-d.first.half.1*((w.phi+w.phi⁻¹)/2)

def energyRatio (d : LatticeInput) (w : LatticeEnergyWitness) : ℚ :=
  (|d.second.mid.1-energyCenter d w|+|d.second.half.1|)/(-energyCenter d w)

def energyShapeCheck (d : LatticeInput) (w : LatticeEnergyWitness) : Bool :=
  decide (1<w.phi ∧ energyCenter d w<0 ∧ 0≤energyRatio d w ∧ energyRatio d w<1)

noncomputable def energyCrossQ (d : LatticeInput) (w : LatticeEnergyWitness) : ℚ :=
  ((List.range w.order).map (fun k : ℕ=>
    realSegMoment d.second (energyCenter d w) (k+1)*stieltjesQ d.first w.phi (k+1)/(k+1:ℚ))).sum

def crossUpperQ (S : ℤ) (K : ℕ) (upper : List ℤ) : ℚ :=
  ((List.range K).map (fun k : ℕ=>(getI upper k:ℚ)/(S:ℚ))).sum

def energyBody (d : LatticeInput) (w : LatticeEnergyWitness) (cross : ℚ) : SE :=
  let U0 := seAdd (seScale (d.first.c 0)
    (seSub (seSub (.log w.terms 2) (.log w.terms d.first.half.1)) (.log w.terms w.phi)))
    (seRat (((List.range (d.first.coeff.length-1)).map (fun k : ℕ=>
      d.first.c (k+1)*(-1:ℚ)^(k+1)*w.phi^(-(k+1:ℤ))/(k+1:ℚ))).sum))
  let v := energyRatio d w
  let err := 2*d.second.c 0*d.first.c 0*v^(w.order+1)/((w.order+1:ℚ)*(1-v))
  seSum [selfEnergyExpr w.terms d.first,selfEnergyExpr w.terms d.second,
    seScale (2*d.second.c 0) U0,seRat (2*cross+err)]

theorem latticeEnergyExpr_body (d : LatticeInput) (w : LatticeEnergyWitness)
    (hc : energyShapeCheck d w=true) :
    latticeEnergyExpr d w=some (energyBody d w (energyCrossQ d w)) := by
  have hg : 1<w.phi ∧ energyCenter d w<0 ∧ 0≤energyRatio d w ∧ energyRatio d w<1 := of_decide_eq_true hc
  unfold latticeEnergyExpr
  have he : (1<w.phi ∧ d.first.mid.1-d.first.half.1*((w.phi+w.phi⁻¹)/2)<0 ∧
      0≤(|d.second.mid.1-(d.first.mid.1-d.first.half.1*((w.phi+w.phi⁻¹)/2))|+|d.second.half.1|)/
        (-(d.first.mid.1-d.first.half.1*((w.phi+w.phi⁻¹)/2))) ∧
      (|d.second.mid.1-(d.first.mid.1-d.first.half.1*((w.phi+w.phi⁻¹)/2))|+|d.second.half.1|)/
        (-(d.first.mid.1-d.first.half.1*((w.phi+w.phi⁻¹)/2)))<1) := hg
  rw [if_pos he]
  rfl

theorem energyBody_mono (d : LatticeInput) (w : LatticeEnergyWitness)
    (a b : ℚ) (hab : a≤b) : (energyBody d w a).value≤(energyBody d w b).value := by
  simp only [energyBody,scalarSum_value,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,seRat_value]
  have hh : (a:ℝ)≤(b:ℝ) := by exact_mod_cast hab
  push_cast
  linarith

def energyTableCheck (d : LatticeInput) (w : LatticeEnergyWitness) (S : ℤ)
    (mu sm : List ℚ) (upper : List ℤ) (cap : ℚ) : Bool :=
  decide (0<S) && ordinaryMomentFast d.second (energyCenter d w) w.order mu &&
    stieltjesMomentFast d.first w.phi w.order sm &&
    (List.range w.order).all (fun k : ℕ=>decide
      (coeffQ mu (k+1)*coeffQ sm (k+1)/(k+1:ℚ)≤(getI upper k:ℚ)/(S:ℚ))) &&
    energyShapeCheck d w && scalarUpperCheck (energyBody d w (crossUpperQ S w.order upper)) cap

theorem energyTableCheck_sound (d : LatticeInput) (w : LatticeEnergyWitness) (S : ℤ)
    (mu sm : List ℚ) (upper : List ℤ) (cap : ℚ)
    (hc : energyTableCheck d w S mu sm upper cap=true) :
    ∃ e : SE,latticeEnergyExpr d w=some e ∧ e.value≤(cap:ℝ) := by
  have hh : 0<S ∧ ordinaryMomentFast d.second (energyCenter d w) w.order mu=true ∧
      stieltjesMomentFast d.first w.phi w.order sm=true ∧
      (∀ k∈List.range w.order,coeffQ mu (k+1)*coeffQ sm (k+1)/(k+1:ℚ)≤(getI upper k:ℚ)/(S:ℚ)) ∧
      energyShapeCheck d w=true ∧ scalarUpperCheck (energyBody d w (crossUpperQ S w.order upper)) cap=true := by
    simpa only [energyTableCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,and_assoc] using hc
  rcases hh with ⟨hS,hOrd,hSt,hCross,hShape,hScalar⟩
  rw [ordinaryMomentFast_eq] at hOrd
  rw [stieltjesMomentFast_eq] at hSt
  simp only [ordinaryMomentCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hOrd
  simp only [stieltjesMomentCheck,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hSt
  have hcross : energyCrossQ d w≤crossUpperQ S w.order upper := by
    unfold energyCrossQ crossUpperQ
    rw [list_sum_map_range,list_sum_map_range]
    apply Finset.sum_le_sum
    intro k hk
    have hkn : k<w.order := Finset.mem_range.mp hk
    have ho := hOrd.2 (k+1) (List.mem_range.mpr (by omega))
    have hs := hSt.2 (k+1) (List.mem_range.mpr (by omega))
    unfold realSegMoment
    rw [← ho,← hs]
    exact hCross k (List.mem_range.mpr hkn)
  exact ⟨energyBody d w (energyCrossQ d w),latticeEnergyExpr_body d w hShape,
    (energyBody_mono d w _ _ hcross).trans (scalarUpperCheck_sound _ cap hScalar)⟩

#print axioms latticeEnergyExpr_body
#print axioms energyTableCheck_sound
end CatalanCore.Li2.DecayCert.LatticeGate
