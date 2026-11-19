module
public import CatalanArchive.Li2.DecayCert.Lattice.MacroDefs
public import CatalanCore.Li2.DecayCert.Lattice.CellPenalty
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 800000
open Polynomial Set MeasureTheory
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.LatticeMacro
open CatalanCore.Li2.Decay LatticeGate BernsteinGrid
noncomputable section
theorem positive_model_integral_sub (f g : ℝ→ℝ) (co : List ℚ) (hne : co≠[])
    (a b E kappa : ℚ) (hab : a≤b) (ha : -1≤a) (hb : b≤1)
    (hf : ContinuousOn f (Icc (a:ℝ) (b:ℝ)))
    (hm : ModelsOn g (co.map (fun q : ℚ => (q:ℝ))) (-1) 1 E)
    (bs : List (ℚ×ℚ))
    (ht : CellBoxRep (qListPoly co) a b (co.length-1) bs)
    (hmajor : ∀x∈Icc (a:ℝ) (b:ℝ),f x≤g x)
    (hfloor : ∀x∈Icc (a:ℝ) (b:ℝ),(kappa:ℝ)≤g x) :
    (∫x in (a:ℝ)..(b:ℝ),pos (f x-(kappa:ℝ)))≤
      ((b:ℝ)-a)*((upperMeanQ bs:ℝ)+(E:ℝ)-(kappa:ℝ)) := by
  have hn := qListPoly_natDegree_lt co hne
  let p := (qListPoly co).map (Rat.castHom ℝ)
  have he (x : ℝ) : p.eval x=evalModel (co.map (fun q : ℚ => (q:ℝ))) x := by
    dsimp only [p]
    rw [Polynomial.eval_map,Polynomial.eval₂_eq_sum_range' (Rat.castHom ℝ) hn]
    simp only [qListPoly_coeff,evalModel_map_rat]
    rfl
  have habR : (a:ℝ)≤(b:ℝ) := by exact_mod_cast hab
  have hp : Continuous (fun x : ℝ=>p.eval x) := p.continuous
  have hpos : ContinuousOn (fun x=>pos (f x-(kappa:ℝ))) (Icc (a:ℝ) (b:ℝ)) :=
    fun x hx=>((hf x hx).sub_const (kappa:ℝ)).max tendsto_const_nhds
  have hpoly := cell_polynomial_integral_upper (qListPoly co) a b (co.length-1)
    (by omega) hab bs ht
  calc
    _≤∫x in (a:ℝ)..(b:ℝ),p.eval x+((E:ℝ)-(kappa:ℝ)) := by
      apply intervalIntegral.integral_mono_on habR (hpos.intervalIntegrable_of_Icc habR)
        ((hp.add continuous_const).intervalIntegrable _ _)
      intro x hx
      change max (f x-(kappa:ℝ)) 0≤p.eval x+((E:ℝ)-(kappa:ℝ))
      rw [he]
      have hx' : x∈Icc (-1:ℝ) 1 := by
        have haR : (-1:ℝ)≤(a:ℝ) := by exact_mod_cast ha
        have hbR : (b:ℝ)≤1 := by exact_mod_cast hb
        exact ⟨haR.trans hx.1,hx.2.trans hbR⟩
      have hh := (abs_le.mp (hm.2.2 x hx')).2
      have hfloorx := hfloor x hx
      have hfg := hmajor x hx
      apply max_le <;> linarith
    _=(∫x in (a:ℝ)..(b:ℝ),p.eval x)+((b:ℝ)-a)*((E:ℝ)-(kappa:ℝ)) := by
      rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)]
      simp only [intervalIntegral.integral_const,smul_eq_mul]
    _≤((b:ℝ)-a)*(upperMeanQ bs:ℝ)+((b:ℝ)-a)*((E:ℝ)-(kappa:ℝ)) := by
      dsimp only [p]
      linarith only [hpoly]
    _=_ := by ring

theorem thresholdPenaltyQ_sound (S err lo hi : ℤ) (a b E kappa : ℚ)
    (boxes : List (ℤ×ℤ)) (f g : ℝ→ℝ) (co : List ℚ) (hne : co≠[])
    (hf : ContinuousOn f (Icc (a:ℝ) (b:ℝ)))
    (hm : ModelsOn g (co.map (fun q : ℚ => (q:ℝ))) (-1) 1 E)
    (hmajor : ∀x∈Icc (a:ℝ) (b:ℝ),f x≤g x)
    (ht : TableEncloses S boxes (canonicalControls (qListPoly co) a b (co.length-1)))
    (hc : bernPenaltyCheck S err lo hi a b E boxes=true) :
    (∫x in (a:ℝ)..(b:ℝ),pos (f x-(kappa:ℝ)))≤
      (thresholdPenaltyQ S err lo hi a b kappa boxes:ℝ) := by
  have hh : (-1≤a ∧ a≤b ∧ b≤1) ∧ bernLeafCheck S err lo hi E boxes=true := by
    simpa only [bernPenaltyCheck,Bool.and_eq_true,decide_eq_true_eq] using hc
  rcases hh with ⟨⟨ha,hab,hb⟩,hleaf⟩
  have hgeom : 0<S ∧ E≤(err:ℚ)/(S:ℚ) := by
    have hh := hleaf
    simp only [bernLeafCheck,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.1
  have hpoint := bernLeafCheck_sound S err lo hi E boxes g co hne a b hab ha hb hm ht hleaf
  simp only [← Rat.cast_div] at hpoint
  have habR : (a:ℝ)≤(b:ℝ) := by exact_mod_cast hab
  have hfsub : ContinuousOn (fun x=>f x-(kappa:ℝ)) (Icc (a:ℝ) (b:ℝ)) :=
    hf.sub continuousOn_const
  by_cases hhi : (hi:ℚ)/(S:ℚ)≤kappa
  · have hhR : (((hi:ℚ)/(S:ℚ):ℚ):ℝ)≤(kappa:ℝ) := by exact_mod_cast hhi
    have hp := pos_integral_zero (fun x=>f x-(kappa:ℝ)) _ _ habR
      (fun x hx=>sub_nonpos.mpr ((hmajor x hx).trans ((hpoint x hx).2.trans hhR)))
    simpa only [thresholdPenaltyQ,hhi,ite_true,Rat.cast_zero] using hp.le
  · by_cases hlo : kappa≤(lo:ℚ)/(S:ℚ)
    · have hloR : (kappa:ℝ)≤(((lo:ℚ)/(S:ℚ):ℚ):ℝ) := by exact_mod_cast hlo
      have hp := positive_model_integral_sub f g co hne a b E kappa hab ha hb hf hm
        (decodedBoxes S boxes) (tableEncloses_CellBoxRep S hgeom.1 boxes _ a b _ ht) hmajor
        (fun x hx=>hloR.trans (hpoint x hx).1)
      have herr : (E:ℝ)≤(((err:ℚ)/(S:ℚ):ℚ):ℝ) := by exact_mod_cast hgeom.2
      simp only [thresholdPenaltyQ,hhi,hlo,ite_false,ite_true,Rat.cast_max,Rat.cast_zero]
      apply le_trans ?_ (le_max_left _ 0)
      push_cast at herr ⊢
      apply hp.trans
      apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr habR)
      linarith
    · have hp := pos_integral_constant (fun x=>f x-(kappa:ℝ)) (a:ℝ) (b:ℝ)
        ((((hi:ℚ)/(S:ℚ):ℚ):ℝ)-(kappa:ℝ)) habR hfsub
        (fun x hx=>sub_le_sub_right ((hmajor x hx).trans (hpoint x hx).2) _)
      simpa only [thresholdPenaltyQ,hhi,hlo,ite_false,Rat.cast_mul,Rat.cast_sub,
        Rat.cast_max,Rat.cast_zero,Rat.cast_div,Rat.cast_intCast] using hp
theorem affine_penalty_bound (f : ℝ→ℝ) (p r a b kappa cap : ℚ)
    (hr : 0≤r)
    (hb : (∫t in (a:ℝ)..(b:ℝ),pos (f ((p:ℝ)+(r:ℝ)*t)-(kappa:ℝ)))≤(cap:ℝ)) :
    (∫x in ((p+r*a:ℚ):ℝ)..((p+r*b:ℚ):ℝ),pos (f x-(kappa:ℝ)))≤((r*cap:ℚ):ℝ) := by
  have hrR : (0:ℝ)≤(r:ℝ) := by exact_mod_cast hr
  have he := intervalIntegral.smul_integral_comp_add_mul
    (fun x : ℝ=>pos (f x-(kappa:ℝ))) (a:=(a:ℝ)) (b:=(b:ℝ)) (r:ℝ) (p:ℝ)
  have hh := mul_le_mul_of_nonneg_left hb hrR
  simp only [smul_eq_mul] at he
  push_cast
  rw [← he]
  exact hh

theorem Leaf.penalty_sound (l : Leaf) (S : ℤ) (w : CellWitness) (root : List (ℤ×ℤ))
    (f g : ℝ→ℝ) (p r kappa : ℚ) (hr : 0≤r) (hf : Continuous f)
    (hm : ModelsOn g ((gridCoeffs S w).map (fun q : ℚ=>(q:ℝ))) (-1) 1 w.remainder)
    (ht : TableEncloses S root (canonicalControls (qListPoly (gridCoeffs S w)) (-1) 1 (w.coeff.length-1)))
    (hc : l.check S w root=true)
    (hmajor : ∀t∈Icc (-1:ℝ) 1,f ((p:ℝ)+(r:ℝ)*t)≤g t) :
    (∫x in ((l.interval p r).left:ℝ)..((l.interval p r).right:ℝ),pos (f x-(kappa:ℝ)))≤
      (l.penalty S r kappa:ℝ) := by
  have hh : (0<S ∧ w.coeff≠[]) ∧ childBoxes l.path root=l.boxes ∧
      bernLeafCheck S l.error l.lower l.upper w.remainder l.boxes=true := by
    simpa only [Leaf.check,macroLeafCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc
  have hd := childInterval_bounds l.path (-1) 1 (by norm_num) le_rfl le_rfl
  have hne : gridCoeffs S w≠[] := by
    intro hz
    have hl := congrArg List.length hz
    simp only [gridCoeffs,List.length_map,List.length_nil] at hl
    exact hh.1.2 (List.eq_nil_of_length_eq_zero hl)
  have ht' := macroLeafCheck_table S w root l.path l.error l.lower l.upper l.boxes ht hc
  have hlen : (gridCoeffs S w).length=w.coeff.length := by simp [gridCoeffs]
  rw [← hlen] at ht'
  have hbern : bernPenaltyCheck S l.error l.lower l.upper l.normalInterval.1 l.normalInterval.2 w.remainder l.boxes=true := by
    simp only [bernPenaltyCheck,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨hd,hh.2.2⟩
  have hcont : Continuous (fun t : ℝ=>f ((p:ℝ)+(r:ℝ)*t)) :=
    hf.comp (continuous_const.add (continuous_const.mul continuous_id))
  have hsub : ∀t∈Icc ((l.normalInterval.1:ℚ):ℝ) ((l.normalInterval.2:ℚ):ℝ),t∈Icc (-1:ℝ) 1 := by
    intro t ht
    have ha : (-1:ℝ)≤(l.normalInterval.1:ℝ) := by exact_mod_cast hd.1
    have hb : (l.normalInterval.2:ℝ)≤1 := by exact_mod_cast hd.2.2
    exact ⟨ha.trans ht.1,ht.2.trans hb⟩
  have hp := thresholdPenaltyQ_sound S l.error l.lower l.upper l.normalInterval.1 l.normalInterval.2
    w.remainder kappa l.boxes (fun t=>f ((p:ℝ)+(r:ℝ)*t)) g (gridCoeffs S w) hne
    hcont.continuousOn hm (fun t ht=>hmajor t (hsub t ht)) ht' hbern
  exact affine_penalty_bound f p r l.normalInterval.1 l.normalInterval.2 kappa _ hr hp
theorem WCell.penalty_sound (z : ℚ) (hz : z≠0) (d : LatticeInput) (dw : DensityWitness)
    (hd : datumCheck d.data dw=true) (c : WCell) (kappa : ℚ)
    (hl : 0≤c.interval.left) (hw : c.interval.left≤c.interval.right)
    (hc : c.check z d=true) :
    (∫x in (c.interval.left:ℝ)..(c.interval.right:ℝ),
      pos (W (z:ℝ) d.data.dual.σ (x:ℂ)-(kappa:ℝ)))≤(c.penalty kappa:ℝ) := by
  cases c with
  | physical c => exact fullLatticeCell_penalty z hz d dw hd c kappa hl hw hc
  | «macro» p l =>
    have hh : p.check z d=true ∧ l.check p.scale p.witness p.boxes=true := by
      simpa only [WCell.check,Bool.and_eq_true] using hc
    have hp : 0<p.radius ∧ WMacroParentCheck p.terms z d p.point p.radius p.center
        p.sourceLeft p.sourceRight p.sourceRadius p.moments p.order p.jetOrder p.base
        p.scale p.witness p.boxes=true := by
      simpa only [WParent.check,Bool.and_eq_true,decide_eq_true_eq] using hh.1
    have hs := WMacroParentCheck_sound p.terms z hz d dw hd p.point p.radius p.center
      p.sourceLeft p.sourceRight p.sourceRadius p.moments p.order p.jetOrder p.base
      p.scale p.witness p.boxes hp.2
    exact l.penalty_sound p.scale p.witness p.boxes
      (fun x=>W (z:ℝ) d.data.dual.σ (x:ℂ)) _ p.point p.radius kappa hp.1.le
      (continuous_W_real _ _) hs.1 hs.2 hh.2 (fun _ _=>le_rfl)

theorem AtomCell.penalty_sound (z : ℚ) (hz : z≠0) (d : LatticeInput) (dw : DensityWitness)
    (hd : datumCheck d.data dw=true) (c : LatticeMacro.AtomCell) (kappa : ℚ)
    (hl : 1≤c.interval.left) (hr : c.interval.right≤4) (hw : c.interval.left≤c.interval.right)
    (hc : c.check z d=true) :
    (∫x in (c.interval.left:ℝ)..(c.interval.right:ℝ),
      pos (omega (z:ℝ) x-2*U d.data.dual.σ (-(x:ℂ))-(kappa:ℝ)))≤(c.penalty kappa:ℝ) := by
  cases c with
  | physical c => exact latticeAtomCell_penalty z hz d dw hd c kappa hl hr hw hc
  | «macro» p l =>
    have hh : p.check z d=true ∧ l.check p.scale p.witness p.boxes=true := by
      simpa only [AtomCell.check,Bool.and_eq_true] using hc
    have hp : 0<p.radius ∧ atomMacroParentCheck p.terms z d p.point p.radius p.phi
        p.supportEnd p.sourceRadius p.moments p.order p.base p.scale p.witness p.boxes=true := by
      simpa only [AtomParent.check,Bool.and_eq_true,decide_eq_true_eq] using hh.1
    have hs := atomMacroParentCheck_sound p.terms z hz d dw hd p.point p.radius p.phi
      p.supportEnd p.sourceRadius p.moments p.order p.base p.scale p.witness p.boxes hp.2
    have hf : Continuous (fun x : ℝ=>omega (z:ℝ) x-2*U d.data.dual.σ (-(x:ℂ))) := by
      convert continuous_A_real (z:ℝ) 0 d.data.dual using 1
      funext x
      simp only [A,sub_zero]
    exact l.penalty_sound p.scale p.witness p.boxes _ _ p.point p.radius kappa hp.1.le hf
      hs.1 hs.2 hh.2 (fun _ _=>le_rfl)

theorem RCell.penalty_sound (z : ℚ) (hz : z≠0) (d : LatticeInput) (dw : DensityWitness)
    (hd : datumCheck d.data dw=true) (hshape : latticeShapeCheck d=true)
    (c : RCell) (kappa : ℚ) (hc : c.check z d=true) :
    (∫x in (c.interval.left:ℝ)..(c.interval.right:ℝ),
      pos (W (z:ℝ) d.data.dual.σ (x:ℂ)-(kappa:ℝ)))≤(c.penalty kappa:ℝ) := by
  cases c with
  | physical c => exact rightCell_penalty z hz d dw hd hshape c kappa hc
  | «macro» p l =>
    have hh : p.check z d=true ∧ l.check p.scale p.witness p.boxes=true := by
      simpa only [RCell.check,Bool.and_eq_true] using hc
    have hp : rightMacroParentCheck z d p.cell p.center p.sourceLeft p.sourceRight p.sourceRadius
        p.moments p.order p.jetOrder p.base p.scale p.witness p.boxes=true := hh.1
    have hg : rightGeometryCheck d p.cell=true := by
      have h:=hp
      simp only [rightMacroParentCheck,Bool.and_eq_true] at h
      exact h.1.1
    have hg' : d.Y≤p.cell.left ∧ p.cell.left<p.cell.right ∧ 0<p.cell.r ∧ p.cell.r<1 ∧
        p.cell.right=d.Y*(1+p.cell.r)^2/(4*p.cell.r) := of_decide_eq_true hg
    have hr : 0≤rightRadius p.cell := by dsimp [rightRadius]; linarith [hg'.2.1]
    have hs := rightMacroParentCheck_sound z d dw hd p.cell p.center p.sourceLeft p.sourceRight
      p.sourceRadius p.moments p.order p.jetOrder p.base p.scale p.witness p.boxes hp
    exact l.penalty_sound p.scale p.witness p.boxes
      (fun x=>W (z:ℝ) d.data.dual.σ (x:ℂ)) _ (rightCenter p.cell) (rightRadius p.cell)
      kappa hr (continuous_W_real _ _) hs.1 hs.2 hh.2
      (rightMacroFun_majorizes z hz d dw hd hshape p.cell hg)
#print axioms Leaf.penalty_sound
#print axioms WCell.penalty_sound
#print axioms AtomCell.penalty_sound
#print axioms RCell.penalty_sound
end
end CatalanCore.Li2.DecayCert.LatticeMacro
