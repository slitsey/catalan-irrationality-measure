module
public import CatalanCore.Li2.DecayCert.Density
public import CatalanCore.Li2.DecayCert.SourceBridge.Primitive
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Decay.ComplexEnergy
noncomputable section

theorem exprSum_value (xs : List CellExpr) (u : ℝ) :
    (exprSum xs).value u=(xs.map (fun e => e.value u)).sum := by
  have hh : ∀ xs : List CellExpr,∀ b : CellExpr,
      (xs.foldl CellExpr.add b).value u=b.value u+(xs.map (fun e => e.value u)).sum := by
    intro xs
    induction xs with
    | nil => intro b; simp
    | cons e xs ih =>
      intro b
      simp only [List.foldl_cons,List.map_cons,List.sum_cons]
      rw [ih]
      change b.value u+e.value u+_=_
      ring
  simpa only [exprSum,CellExpr.value,ScalarExpr.value,Rat.cast_zero,zero_add] using hh xs (.constant (.rat 0))

theorem checked_sources_pointLog_integrable (ss : List QSegment) (R : ℚ) (dw : DensityWitness)
    (hd : sourceDataCheck ss R dw=true) (z : ℂ) :
    Integrable (fun u => Real.log ‖z-u‖) (ss.map QSegment.measure).sum := by
  rcases checkedDatum_exists ss R dw hd with ⟨d,he⟩
  rw [← he]
  exact d.pointLogIntegrable z

theorem checked_sources_P_sum (ss : List QSegment) (R : ℚ) (dw : DensityWitness)
    (hd : sourceDataCheck ss R dw=true) (z : ℂ) :
    P (ss.map QSegment.measure).sum z=(ss.map (fun s => P s.measure z)).sum := by
  have hi := checked_sources_pointLog_integrable ss R dw hd z
  have hgeneric : ∀ ss : List QSegment, Integrable (fun u => Real.log ‖z-u‖) (ss.map QSegment.measure).sum →
      P (ss.map QSegment.measure).sum z=(ss.map (fun s => P s.measure z)).sum := by
    intro ss
    induction ss with
    | nil => intro hi; simp [P]
    | cons s ss ih =>
      intro hi
      simp only [List.map_cons,List.sum_cons] at hi ⊢
      have hparts := integrable_add_measure.mp hi
      change (∫ u,Real.log ‖z-u‖ ∂(s.measure+(ss.map QSegment.measure).sum))=_
      rw [integral_add_measure hparts.1 hparts.2]
      exact congrArg (fun x => P s.measure z+x) (ih hparts.2)
  exact hgeneric ss hi

theorem fieldExpr_value (terms : ℕ) (z : ℚ) (p e : CQ) (u : ℝ)
    (hre : 0 ≤ (cqReal p+cqReal e*(u:ℂ)).re)
    (him : 0 ≤ (cqReal p+cqReal e*(u:ℂ)).im) :
    (fieldExpr terms z p e).value u=V (z:ℝ) (cqReal p+cqReal e*(u:ℂ)) := by
  let s := cqReal p+cqReal e*(u:ℂ)
  have h1 : cqReal (cqAdd p (1,0))+cqReal e*(u:ℂ)=s+1 := by
    dsimp only [s]
    rw [cqReal_add]
    norm_num [cqReal]
    ring
  have h4 : cqReal (cqAdd p (4,0))+cqReal e*(u:ℂ)=s+4 := by
    dsimp only [s]
    rw [cqReal_add]
    norm_num [cqReal]
    ring
  have hsR : s.re=(p.1:ℝ)+(e.1:ℝ)*u := by
    dsimp only [s]
    rw [cqReal_mk,cqReal_mk]
    simp
  have hsI : s.im=(p.2:ℝ)+(e.2:ℝ)*u := by
    dsimp only [s]
    rw [cqReal_mk,cqReal_mk]
    simp
  have hkap : (((if (0:ℚ)<z then 2 else 1):ℚ):ℝ)*Real.pi=kappaRate (z:ℝ) := by
    by_cases h : 0<z
    · have hR : 0<(z:ℝ) := by exact_mod_cast h
      simp [h,hR,kappaRate]
    · have hR : ¬ 0<(z:ℝ) := by exact_mod_cast h
      simp [h,hR,kappaRate]
  simp only [fieldExpr,exprSum,List.foldl_cons,List.foldl_nil,CellExpr.value,seSub,seAdd,seNeg,seScale,
    seMul,seRat,ScalarExpr.value,Rat.cast_zero,Rat.cast_one,Rat.cast_ofNat,Rat.cast_neg,Rat.cast_abs,Rat.cast_mul,zero_add]
  rw [h1,h4]
  simp only [← sub_eq_add_neg]
  change 3*freValue (s+1)+(-2)*freValue s+(-1)*freValue (s+4)+
      (((p.1:ℝ)*Real.log |(z:ℝ)|-(((if (0:ℚ)<z then 2 else 1):ℚ):ℝ)*(p.2:ℝ)*Real.pi)+
      (((e.1:ℝ)*Real.log |(z:ℝ)|-(((if (0:ℚ)<z then 2 else 1):ℚ):ℝ)*(e.2:ℝ)*Real.pi)*u))=_
  rw [V,abs_of_nonneg him,phi0_eq_freValue s hre,hsR,hsI]
  rw [← hkap]
  ring

theorem sum_map_two_mul {α : Type*} (xs : List α) (f : α → ℝ) :
    (xs.map (fun x => 2*f x)).sum=2*(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; ring

theorem exprSum_segment_value (ss : List QSegment) (R : ℚ) (dw : DensityWitness)
    (hd : sourceDataCheck ss R dw=true) (p e : CQ) (u : ℝ) :
    (exprSum (ss.map (fun s => .scale 2 (.segment s p e)))).value u =
      2*P (ss.map QSegment.measure).sum (cqReal p+cqReal e*(u:ℂ)) := by
  rw [exprSum_value,List.map_map]
  simp only [Function.comp_def,CellExpr.value]
  norm_num only [Rat.cast_ofNat]
  rw [sum_map_two_mul,checked_sources_P_sum ss R dw hd]

theorem WExpr_value (terms : ℕ) (z : ℚ) (hz : z ≠ 0) (d : SegmentDatum)
    (dw : DensityWitness) (hd : datumCheck d dw=true) (p e : CQ) (u : ℝ)
    (hre : 0 ≤ (cqReal p+cqReal e*(u:ℂ)).re) (him : 0 ≤ (cqReal p+cqReal e*(u:ℂ)).im) :
    (WExpr terms z d.segments p e).value u=W (z:ℝ) d.dual.σ (cqReal p+cqReal e*(u:ℂ)) := by
  change (fieldExpr terms z p e).value u+
    (exprSum (d.segments.map (fun s => .scale 2 (.segment s p e)))).value u=_
  rw [fieldExpr_value terms z p e u hre him,exprSum_segment_value d.segments d.radius dw hd p e u]
  rw [W,U,d.measure_eq]
  ring

theorem atomExpr_value (terms : ℕ) (z : ℚ) (hz : z ≠ 0) (d : SegmentDatum)
    (dw : DensityWitness) (hd : datumCheck d dw=true) (x dir : ℚ) (u : ℝ)
    (hu : (x:ℝ)+(dir:ℝ)*u ∈ Icc 1 4) :
    (atomExpr terms z d.segments x dir).value u =
      omega (z:ℝ) ((x:ℝ)+(dir:ℝ)*u)-2*U d.dual.σ (-((x:ℝ)+(dir:ℝ)*u:ℂ)) := by
  let xx : ℝ := (x:ℝ)+(dir:ℝ)*u
  have hpoint : cqReal (-x,0)+cqReal (-dir,0)*(u:ℂ)= -(xx:ℂ) := by
    dsimp only [xx]
    simp [cqReal]
    push_cast
    ring
  have hA : (x:ℝ)-1+(dir:ℝ)*u=xx-1 := by dsimp [xx]; ring
  have hB : 4-(x:ℝ)+(-(dir:ℝ))*u=4-xx := by dsimp [xx]; ring
  simp only [atomExpr,exprSum_value,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    CellExpr.value,List.map_map,Function.comp_def,seAdd,seScale,seMul,seRat,ScalarExpr.value,
    Rat.cast_ofNat,Rat.cast_one,Rat.cast_neg,Rat.cast_sub,Rat.cast_mul,Rat.cast_abs,add_zero,zero_add]
  rw [hA,hB,hpoint,sum_map_two_mul]
  have hrpoint : -(((x:ℝ):ℂ)+((dir:ℝ):ℂ)*(u:ℂ))= -(xx:ℂ) := by
    dsimp only [xx]
    push_cast
    rfl
  rw [hrpoint]
  rw [omega,phi0_negative_formula,U,d.measure_eq,checked_sources_P_sum d.segments d.radius dw hd]
  dsimp only [xlog,xx]
  ring

#print axioms sum_map_two_mul
#print axioms exprSum_segment_value
#print axioms WExpr_value
#print axioms atomExpr_value

#print axioms exprSum_value
#print axioms checked_sources_pointLog_integrable
#print axioms checked_sources_P_sum
#print axioms fieldExpr_value
end
end CatalanCore.Li2.DecayCert
