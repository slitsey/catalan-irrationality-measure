module
public import CatalanCore.Li2.DecayCert.Compile.Dispatch
public import CatalanCore.Li2.DecayCert.SourceBridge.Primitive
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem cellUBF_parts (x : CellInput) (w : CellWitness) (hc : cellUBF x w=true) :
    ∃ m : CompiledModel, compileModel x.lo x.hi x.expr w.model=some m ∧
      x.lo ≤ x.hi ∧ coefficientCheck x.scale m w=true ∧
      remainderCheck x.scale (max |x.lo| |x.hi|) m w=true ∧
      polyUBQ (gridCoeffs x.scale w) x.lo x.hi+w.remainder ≤ w.ub ∧
      w.lb ≤ polyLBQ (gridCoeffs x.scale w) x.lo x.hi-w.remainder := by
  unfold cellUBF at hc
  split at hc
  · contradiction
  · rename_i m hm
    simp only [Bool.and_eq_true,decide_eq_true_eq] at hc
    exact ⟨m,hm,hc.1.1.1,hc.1.1.2,hc.1.2,hc.2.1,hc.2.2⟩

theorem cellUBF_model (x : CellInput) (w : CellWitness) (hp : PositiveSources x.expr)
    (hc : cellUBF x w=true) :
    ModelsOn x.expr.value ((gridCoeffs x.scale w).map (fun q : ℚ => (q:ℝ)))
      x.lo x.hi w.remainder := by
  rcases cellUBF_parts x w hc with ⟨m,hm,hdom,hco,hr,hub,hlb⟩
  exact roundModel_sound x.scale x.lo x.hi m w x.expr.value
    (compileModel_sound x.lo x.hi x.expr w.model m hdom hp hm) hco hr

theorem cellUBF_spec (x : CellInput) (w : CellWitness)
    (hpos : PositiveSources x.expr) (hc : cellUBF x w=true) :
    ∀ u ∈ Icc (x.lo:ℝ) (x.hi:ℝ),x.expr.value u ∈ Icc (w.lb:ℝ) (w.ub:ℝ) := by
  rcases cellUBF_parts x w hc with ⟨m,hm,hdom,hco,hr,hub,hlb⟩
  have h := cell_ub_lb x.expr.value (gridCoeffs x.scale w) x.lo x.hi w.remainder (cellUBF_model x w hpos hc)
  intro u hu
  have hv := h u hu
  have hlow : (w.lb:ℝ) ≤ ((polyLBQ (gridCoeffs x.scale w) x.lo x.hi-w.remainder:ℚ):ℝ) := by exact_mod_cast hlb
  have hupp : ((polyUBQ (gridCoeffs x.scale w) x.lo x.hi+w.remainder:ℚ):ℝ) ≤ (w.ub:ℝ) := by exact_mod_cast hub
  exact ⟨hlow.trans hv.1,hv.2.trans hupp⟩

theorem taylorCellF_ub (x : CellInput) (w : CellWitness)
    (hpos : PositiveSources x.expr) (hcheck : cellUBF x w=true) :
    ∀ u ∈ Icc (x.lo:ℝ) (x.hi:ℝ),cellFun x u ≤ (w.ub:ℝ) :=
  fun u hu => (cellUBF_spec x w hpos hcheck u hu).2

theorem taylorCellF_lb (x : CellInput) (w : CellWitness)
    (hpos : PositiveSources x.expr) (hcheck : cellUBF x w=true) :
    ∀ u ∈ Icc (x.lo:ℝ) (x.hi:ℝ),(w.lb:ℝ) ≤ cellFun x u :=
  fun u hu => (cellUBF_spec x w hpos hcheck u hu).1

theorem quadratic_chord_upper (c R u : ℝ) (hu : u ∈ Icc 0 R) :
    c*u^2 ≤ c*R*u+(if c < 0 then -c*R^2/4 else 0) := by
  split_ifs with hc
  · nlinarith [mul_nonneg (neg_nonneg.mpr hc.le) (sq_nonneg (u-R/2))]
  · have hc' : 0 ≤ c := le_of_not_gt hc
    nlinarith [mul_nonneg hc' (mul_nonneg hu.1 (sub_nonneg.mpr hu.2))]

theorem upperLine_bound (co : List ℚ) (R err : ℚ) (u : ℝ)
    (hu : u ∈ Icc 0 (R:ℝ)) :
    evalModel (co.map (fun q : ℚ => (q:ℝ))) u+(err:ℝ) ≤
      ((upperLine co R err).1:ℝ)+((upperLine co R err).2:ℝ)*u := by
  have hR : 0 ≤ (R:ℝ) := hu.1.trans hu.2
  have huabs : |u| ≤ (R:ℝ) := by simpa only [abs_of_nonneg hu.1] using hu.2
  have htail : (∑ j ∈ Finset.range co.length,if 3 ≤ j then (coeffQ co j:ℝ)*u^j else 0) ≤
      ∑ j ∈ Finset.range co.length,if 3 ≤ j then |(coeffQ co j:ℝ)| *(R:ℝ)^j else 0 := by
    apply Finset.sum_le_sum
    intro j hj
    split_ifs
    · calc
        _ ≤ |(coeffQ co j:ℝ)*u^j| := le_abs_self _
        _ = |(coeffQ co j:ℝ)| *|u|^j := by rw [abs_mul,abs_pow]
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg u) huabs j) (abs_nonneg _)
    · exact le_rfl
  have hq := quadratic_chord_upper (coeffQ co 2:ℝ) R u hu
  have hsum : (∑ j ∈ Finset.range co.length,((if 3 ≤ j then |coeffQ co j| *R^j else 0:ℚ):ℝ)) =
      ∑ j ∈ Finset.range co.length,if 3 ≤ j then |(coeffQ co j:ℝ)| *(R:ℝ)^j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs <;> push_cast <;> rfl
  have hline : ((upperLine co R err).1:ℝ)+((upperLine co R err).2:ℝ)*u =
      (coeffQ co 0:ℝ)+(err:ℝ)+
      (∑ j ∈ Finset.range co.length,if 3 ≤ j then |(coeffQ co j:ℝ)| *(R:ℝ)^j else 0)+
      (if (coeffQ co 2:ℝ)<0 then -(coeffQ co 2:ℝ)*(R:ℝ)^2/4 else 0)+
      ((coeffQ co 1:ℝ)+(coeffQ co 2:ℝ)*(R:ℝ))*u := by
    unfold upperLine
    dsimp only
    rw [list_sum_map_range]
    by_cases hc : coeffQ co 2 < 0
    · have hcR : (coeffQ co 2:ℝ)<0 := by exact_mod_cast hc
      simp only [if_pos hc,if_pos hcR]
      push_cast
      rw [hsum]
      ring
    · have hcR : ¬(coeffQ co 2:ℝ)<0 := by exact_mod_cast hc
      simp only [if_neg hc,if_neg hcR]
      push_cast
      rw [hsum]
      ring
  rw [hline,evalModel_map_rat,sum_range_three_tail co.length (fun j => (coeffQ co j:ℝ)*u^j)
    (by intro j hj; rw [coeffQ_eq_zero_of_ge co j hj]; simp)]
  simp only [pow_zero,mul_one,pow_one]
  linarith

theorem lineCellF_spec (x : CellInput) (w : LineWitness)
    (hpos : PositiveSources x.expr) (hc : lineCellF x w=true) :
    ∀ u ∈ Icc 0 (x.hi:ℝ),x.expr.value u ≤ (w.a:ℝ)+(w.b:ℝ)*u := by
  simp only [lineCellF,Bool.and_eq_true,decide_eq_true_eq] at hc
  rcases hc with ⟨⟨hcell,hlo,hhi⟩,hleft,hright⟩
  have hm := cellUBF_model x w.cell hpos hcell
  intro u hu
  have hu' : u ∈ Icc (x.lo:ℝ) (x.hi:ℝ) := by simpa only [hlo,Rat.cast_zero] using hu
  have hv := (abs_le.mp (hm.2.2 u hu')).2
  have hub := upperLine_bound (gridCoeffs x.scale w.cell) x.hi w.cell.remainder u hu
  have he0 : ((upperLine (gridCoeffs x.scale w.cell) x.hi w.cell.remainder).1:ℝ) ≤ (w.a:ℝ) := by exact_mod_cast hleft
  have he1 : ((upperLine (gridCoeffs x.scale w.cell) x.hi w.cell.remainder).1:ℝ)+
      ((upperLine (gridCoeffs x.scale w.cell) x.hi w.cell.remainder).2:ℝ)*(x.hi:ℝ) ≤
      (w.a:ℝ)+(w.b:ℝ)*(x.hi:ℝ) := by exact_mod_cast hright
  have hg : ((upperLine (gridCoeffs x.scale w.cell) x.hi w.cell.remainder).1:ℝ)+
      (((upperLine (gridCoeffs x.scale w.cell) x.hi w.cell.remainder).2:ℝ)-(w.b:ℝ))*u ≤ (w.a:ℝ) := by
    by_cases hb : 0 ≤ ((upperLine (gridCoeffs x.scale w.cell) x.hi w.cell.remainder).2:ℝ)-(w.b:ℝ)
    · nlinarith [mul_nonneg hb (sub_nonneg.mpr hu.2)]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hb)) hu.1]
  linarith

theorem phi0_cell (p e : CQ) (lo hi : ℚ) (S : ℤ) (w : CellWitness)
    (hgeom : ∀ u ∈ Icc (lo:ℝ) (hi:ℝ),0 ≤ (cqReal p+cqReal e*(u:ℂ)).re)
    (hc : cellUBF ⟨phi0Expr p e,lo,hi,S⟩ w=true) :
    ModelsOn (fun u => phi0 (cqReal p+cqReal e*(u:ℂ)))
      ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) lo hi w.remainder := by
  have hp : PositiveSources (phi0Expr p e) := by simp [phi0Expr,exprSum,PositiveSources]
  have hm := cellUBF_model ⟨phi0Expr p e,lo,hi,S⟩ w hp hc
  refine ⟨hm.1,hm.2.1,?_⟩
  intro u hu
  have he : (phi0Expr p e).value u=phi0 (cqReal p+cqReal e*(u:ℂ)) := by
    rw [phi0_eq_freValue _ (hgeom u hu)]
    simp only [phi0Expr,exprSum,List.foldl_cons,List.foldl_nil,CellExpr.value,ScalarExpr.value]
    simp only [cqReal_add]
    norm_num only [Rat.cast_ofNat,Rat.cast_neg,cqReal,Rat.cast_zero,Rat.cast_one,zero_mul,mul_zero,add_zero]
    unfold freValue
    congr 1 <;> ring
  change |phi0 (cqReal p+cqReal e*(u:ℂ))-evalModel ((gridCoeffs S w).map (fun q : ℚ => (q:ℝ))) u| ≤ _
  rw [← he]
  exact hm.2.2 u hu
#print axioms cellUBF_model
#print axioms cellUBF_spec
#print axioms taylorCellF_ub
#print axioms taylorCellF_lb
#print axioms quadratic_chord_upper
#print axioms upperLine_bound
#print axioms lineCellF_spec
#print axioms phi0_cell
end
end CatalanCore.Li2.DecayCert
