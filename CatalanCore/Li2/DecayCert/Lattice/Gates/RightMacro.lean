module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Right
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Leaves
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 800000
open Set Polynomial MeasureTheory
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.LatticeGate
open CatalanCore.Li2.Decay BernsteinGrid

def rightCenter (c : RightCell) : ℚ := (c.left+c.right)/2
def rightRadius (c : RightCell) : ℚ := (c.right-c.left)/2
noncomputable def rightParameter (c : RightCell) (t : ℝ) : ℝ := (rightRadius c:ℝ)*(t+1)

theorem rightParameter_spec (c : RightCell) (hab : c.left≤c.right) (t : ℝ) (ht : t∈Icc (-1:ℝ) 1) :
    rightParameter c t∈Icc (0:ℝ) ((c.right-c.left:ℚ):ℝ) ∧
      (c.left:ℝ)+rightParameter c t=(rightCenter c:ℝ)+(rightRadius c:ℝ)*t := by
  have hr : (0:ℝ)≤(rightRadius c:ℝ) := by
    exact_mod_cast (show (0:ℚ)≤rightRadius c from div_nonneg (sub_nonneg.mpr hab) (by norm_num))
  have hw : ((c.right-c.left:ℚ):ℝ)=2*(rightRadius c:ℝ) := by
    dsimp only [rightRadius]
    push_cast
    ring
  refine ⟨⟨mul_nonneg hr (by linarith [ht.1]),?_⟩,?_⟩
  · rw [hw]
    dsimp only [rightParameter]
    nlinarith [ht.2]
  · dsimp only [rightParameter,rightCenter,rightRadius]
    push_cast
    ring

def rightBase (z : ℚ) (d : LatticeInput) (c : RightCell) : CellExpr :=
  .add (fieldExpr c.terms z (rightCenter c,0) (rightRadius c,0))
    (.scale 2 (.constant (segConstant c.terms d.first (1/c.r,0))))
noncomputable def rightMacroFun (z : ℚ) (d : LatticeInput) (c : RightCell) (t : ℝ) : ℝ :=
  (rightBase z d c).value t-2*U d.second.measure
    (((rightCenter c:ℝ)+(rightRadius c:ℝ)*t:ℝ):ℂ)

theorem rightMacroFun_value (z : ℚ) (d : LatticeInput) (c : RightCell)
    (hY : 0<d.Y) (hc : rightGeometryCheck d c=true) (t : ℝ) (ht : t∈Icc (-1:ℝ) 1) :
    rightMacroFun z d c t=(rightCellSource z d c).value (rightParameter c t) := by
  have hg : d.Y≤c.left ∧ c.left<c.right ∧ 0<c.r ∧ c.r<1 ∧
      c.right=d.Y*(1+c.r)^2/(4*c.r) := of_decide_eq_true hc
  have hu := rightParameter_spec c hg.2.1.le t ht
  have hleft : (d.Y:ℝ)≤(c.left:ℝ) := by exact_mod_cast hg.1
  have hy : (0:ℝ)<(d.Y:ℝ) := by exact_mod_cast hY
  have hnon : (0:ℝ)≤(rightCenter c:ℝ)+(rightRadius c:ℝ)*t := by
    rw [← hu.2]
    linarith [hu.1.1]
  have hpt1 : cqReal (rightCenter c,0)+cqReal (rightRadius c,0)*(t:ℂ)=
      (((rightCenter c:ℝ)+(rightRadius c:ℝ)*t:ℝ):ℂ) := by simp [cqReal]
  have hpt2 : cqReal (c.left,0)+cqReal (1,0)*((rightParameter c t):ℂ)=
      (((c.left:ℝ)+rightParameter c t:ℝ):ℂ) := by simp [cqReal]
  have he1 := fieldExpr_value c.terms z (rightCenter c,0) (rightRadius c,0) t
    (by simpa [cqReal] using hnon) (by simp [cqReal])
  have he2 := fieldExpr_value c.terms z (c.left,0) (1,0) (rightParameter c t)
    (by simpa [cqReal] using (show (0:ℝ)≤(c.left:ℝ)+rightParameter c t by rw [hu.2];exact hnon))
    (by simp [cqReal])
  rw [hpt1] at he1
  rw [hpt2,hu.2] at he2
  have hf := he1.trans he2.symm
  simp only [rightMacroFun,rightBase,rightCellSource,CellExpr.value,Rat.cast_ofNat]
  rw [hf,hpt2,hu.2]
  dsimp only [U]
  ring

theorem rightMacroFun_majorizes (z : ℚ) (hz : z≠0) (d : LatticeInput)
    (dw : DensityWitness) (hd : datumCheck d.data dw=true) (hshape : latticeShapeCheck d=true)
    (c : RightCell) (hc : rightGeometryCheck d c=true) :
    ∀t∈Icc (-1:ℝ) 1,W (z:ℝ) d.data.dual.σ
      (((rightCenter c:ℝ)+(rightRadius c:ℝ)*t:ℝ):ℂ)≤rightMacroFun z d c t := by
  have hg : d.Y≤c.left ∧ c.left<c.right ∧ 0<c.r ∧ c.r<1 ∧
      c.right=d.Y*(1+c.r)^2/(4*c.r) := of_decide_eq_true hc
  intro t ht
  have hu := rightParameter_spec c hg.2.1.le t ht
  have h := rightCellSource_majorizes z hz d dw hd hshape c hc (rightParameter c t) hu.1
  rw [hu.2,← rightMacroFun_value z d c (latticeShapeCheck_parts d hshape).1 hc t ht] at h
  exact h

noncomputable def rightMacroModel (z : ℚ) (d : LatticeInput) (c : RightCell)
    (y0 H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness) : Option CompiledModel := do
  let b ← compileModel (-1) 1 (rightBase z d c) base
  pure (addCompiled b (scaleCompiled (-2)
    (affineCompiled (farModel c.terms (d.second.c 0) mu y0 H
      (rightCenter c) (rightRadius c) K J) 0 (rightRadius c))))

noncomputable def rightMacroParentCheck (z : ℚ) (d : LatticeInput) (c : RightCell)
    (y0 L Y H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness)
    (S : ℤ) (w : CellWitness) (boxes : List (ℤ×ℤ)) : Bool :=
  rightGeometryCheck d c && farModelCheck d.second mu y0 L Y H (rightCenter c) (rightRadius c) K &&
    (match rightMacroModel z d c y0 H mu K J base with
     | none=>false | some m=>bernParentCheck S m w boxes)

theorem rightMacroModel_sound (z : ℚ) (d : LatticeInput) (dw : DensityWitness)
    (hd : datumCheck d.data dw=true) (c : RightCell)
    (y0 L Y H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness)
    (hfar : farModelCheck d.second mu y0 L Y H (rightCenter c) (rightRadius c) K=true)
    (m : CompiledModel) (hm : rightMacroModel z d c y0 H mu K J base=some m) :
    ModelsOn (rightMacroFun z d c) (m.coeff.map ScalarExpr.value) (-1) 1 m.error.value := by
  unfold rightMacroModel at hm
  cases hb : compileModel (-1) 1 (rightBase z d c) base with
  | none => simp [hb] at hm
  | some b =>
    simp [hb] at hm
    subst m
    have hpos : PositiveSources (rightBase z d c) := by simp [rightBase,fieldExpr,exprSum,PositiveSources]
    have hbase := compileModel_sound (-1) 1 _ base b (by norm_num) hpos hb
    simp only [Rat.cast_neg,Rat.cast_one] at hbase
    have hp := (datum_source_data d.data dw hd d.second (lattice_second_mem d)).2.2
    have hs := farModelCheck_sound c.terms d.second mu y0 L Y H (rightCenter c) (rightRadius c) K J hp hfar
    have hh : realSupportCheck d.second L Y=true ∧ ordinaryMomentCheck d.second y0 K mu=true ∧
        (0≤H ∧ 0≤rightRadius c ∧ H<rightCenter c-y0-rightRadius c ∧ |L-y0|≤H ∧ |Y-y0|≤H) := by
      simpa only [farModelCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hfar
    have ha : affineDomainCheck 0 (rightRadius c) (rightRadius c)=true := by
      simp [affineDomainCheck,abs_of_nonneg hh.2.2.2.1]
    have hnorm := affineCompiled_sound _ 0 (rightRadius c) (rightRadius c) _ hs ha
    simp only [Rat.cast_zero,zero_add] at hnorm
    have hsum := addCompiled_sound b _ _ _ hbase (scaleCompiled_sound (-2) _ _ hnorm)
    apply modelsOn_congr_domain hsum
    intro t ht
    simp only [rightMacroFun,Rat.cast_neg,Rat.cast_ofNat,neg_mul,sub_eq_add_neg]

theorem rightMacroParentCheck_sound (z : ℚ) (d : LatticeInput) (dw : DensityWitness)
    (hd : datumCheck d.data dw=true) (c : RightCell)
    (y0 L Y H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness)
    (S : ℤ) (w : CellWitness) (root : List (ℤ×ℤ))
    (hc : rightMacroParentCheck z d c y0 L Y H mu K J base S w root=true) :
    ModelsOn (rightMacroFun z d c) ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) (-1) 1 w.remainder ∧
    TableEncloses S root (canonicalControls (qListPoly (gridCoeffs S w)) (-1) 1 (w.coeff.length-1)) := by
  have hh : rightGeometryCheck d c=true ∧
      farModelCheck d.second mu y0 L Y H (rightCenter c) (rightRadius c) K=true ∧
      (match rightMacroModel z d c y0 H mu K J base with
       | none=>false | some m=>bernParentCheck S m w root)=true := by
    simpa only [rightMacroParentCheck,Bool.and_eq_true,and_assoc] using hc
  cases hm : rightMacroModel z d c y0 H mu K J base with
  | none => simp [hm] at hh
  | some m =>
    have hcheck : bernParentCheck S m w root=true := by simpa only [hm] using hh.2.2
    exact ⟨(bernParentCheck_sound S m w root _
      (rightMacroModel_sound z d dw hd c y0 L Y H mu K J base hh.2.1 m hm) hcheck).1,
      bernParentCheck_table S m w root hcheck⟩

theorem rightMacroLeafCheck_sound (z : ℚ) (hz : z≠0) (d : LatticeInput)
    (dw : DensityWitness) (hd : datumCheck d.data dw=true) (hshape : latticeShapeCheck d=true)
    (c : RightCell) (y0 L Y H : ℚ) (mu : List ℚ) (K J : ℕ) (base : ModelWitness)
    (S : ℤ) (w : CellWitness) (root : List (ℤ×ℤ))
    (hp : rightMacroParentCheck z d c y0 L Y H mu K J base S w root=true)
    (path : List Bool) (err lo hi : ℤ) (boxes : List (ℤ×ℤ))
    (hc : macroLeafCheck S w root path err lo hi boxes=true) :
    ∀t∈Icc (((childInterval path (-1) 1).1:ℚ):ℝ) (((childInterval path (-1) 1).2:ℚ):ℝ),
      W (z:ℝ) d.data.dual.σ (((rightCenter c:ℝ)+(rightRadius c:ℝ)*t:ℝ):ℂ)≤((hi:ℚ)/(S:ℚ):ℝ) := by
  have hs := rightMacroParentCheck_sound z d dw hd c y0 L Y H mu K J base S w root hp
  have hl := macroLeafCheck_sound S w root path err lo hi boxes _ hs.1 hs.2 hc
  have hg : rightGeometryCheck d c=true := by
    have hh : rightGeometryCheck d c=true ∧
        farModelCheck d.second mu y0 L Y H (rightCenter c) (rightRadius c) K=true ∧
        (match rightMacroModel z d c y0 H mu K J base with
         | none=>false | some m=>bernParentCheck S m w root)=true := by
      simpa only [rightMacroParentCheck,Bool.and_eq_true,and_assoc] using hp
    exact hh.1
  have hb := childInterval_bounds path (-1) 1 (by norm_num) le_rfl le_rfl
  intro t ht
  have ht' : t∈Icc (-1:ℝ) 1 := by
    have ha : (-1:ℝ)≤((childInterval path (-1) 1).1:ℝ) := by exact_mod_cast hb.1
    have hb' : ((childInterval path (-1) 1).2:ℝ)≤1 := by exact_mod_cast hb.2.2
    exact ⟨ha.trans ht.1,ht.2.trans hb'⟩
  exact (rightMacroFun_majorizes z hz d dw hd hshape c hg t ht').trans (hl t ht).2
#print axioms rightMacroFun_value
#print axioms rightMacroParentCheck_sound
#print axioms rightMacroLeafCheck_sound
end CatalanCore.Li2.DecayCert.LatticeGate
