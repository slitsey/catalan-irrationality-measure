module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Energy.Tables
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Li2.DecayCert.LatticeGate
 theorem scalarUpperCheck_add_rat_mono (seed : SE) (a b cap : ℚ) (hab : a≤b)
    (hc : scalarUpperCheck (seAdd seed (seRat b)) cap=true) :
    scalarUpperCheck (seAdd seed (seRat a)) cap=true := by
  cases hb : seed.check with
  | none => simp [scalarUpperCheck,seAdd,seRat,ScalarExpr.check,hb] at hc
  | some box =>
    simp only [scalarUpperCheck,seAdd,seRat,ScalarExpr.check,hb] at hc ⊢
    change decide (box.2+b≤cap)=true at hc
    change decide (box.2+a≤cap)=true
    simp only [decide_eq_true_eq] at hc ⊢
    linarith
 theorem scalarLowerCheck_add_rat_mono (seed : SE) (a b lower : ℚ) (hab : a≤b)
    (hc : scalarLowerCheck lower (seAdd seed (seRat a))=true) :
    scalarLowerCheck lower (seAdd seed (seRat b))=true := by
  cases hb : seed.check with
  | none => simp [scalarLowerCheck,seAdd,seRat,ScalarExpr.check,hb] at hc
  | some box =>
    simp only [scalarLowerCheck,seAdd,seRat,ScalarExpr.check,hb] at hc ⊢
    change decide (lower≤box.1+a)=true at hc
    change decide (lower≤box.1+b)=true
    simp only [decide_eq_true_eq] at hc ⊢
    linarith
 theorem energyBody_check_mono (d : LatticeInput) (w : LatticeEnergyWitness)
    (a b cap : ℚ) (hab : a≤b)
    (hc : scalarUpperCheck (energyBody d w b) cap=true) :
    scalarUpperCheck (energyBody d w a) cap=true := by
  unfold energyBody seSum at hc ⊢
  simp only [List.foldl_cons,List.foldl_nil] at hc ⊢
  exact scalarUpperCheck_add_rat_mono _ _ _ cap (by linarith) hc
 theorem energyTableCheck_raw (d : LatticeInput) (w : LatticeEnergyWitness) (S : ℤ)
    (mu sm : List ℚ) (upper : List ℤ) (cap : ℚ)
    (hc : energyTableCheck d w S mu sm upper cap=true) :
    (match latticeEnergyExpr d w with | some e=>scalarUpperCheck e cap | none=>false)=true := by
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
  rw [latticeEnergyExpr_body d w hShape]
  exact energyBody_check_mono d w _ _ cap hcross hScalar
 theorem latticePairScalar_of_caps (d : LatticeInput) (c : LatticeSetup) (p : LatticeCert)
    (pw pa : ℚ) (hw : latticePW d c≤pw) (ha : latticePA d c p≤pa)
    (hc : scalarLowerCheck p.lower (seSum [seScale (-12) (.log c.terms 2),
      seRat (-4-c.Iup-2*c.theta-2*pw-pa)])=true) :
    scalarLowerCheck p.lower (seSum [seScale (-12) (.log c.terms 2),
      seRat (-4-c.Iup-2*c.theta-2*latticePW d c-latticePA d c p)])=true := by
  unfold seSum at hc ⊢
  simp only [List.foldl_cons,List.foldl_nil] at hc ⊢
  exact scalarLowerCheck_add_rat_mono _ _ _ p.lower (by linarith) hc
#print axioms scalarUpperCheck_add_rat_mono
#print axioms scalarLowerCheck_add_rat_mono
#print axioms energyTableCheck_raw
#print axioms latticePairScalar_of_caps
end CatalanCore.Li2.DecayCert.LatticeGate
