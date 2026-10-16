module
public import CatalanMeasure.GapCircle.Checks0
public import CatalanMeasure.GapCircle.Checks1
public import CatalanMeasure.GapCircle.Checks2
public import CatalanMeasure.GapCircle.Checks3
public import CatalanMeasure.GapCircle.Checks4
public import CatalanMeasure.GapCircle.Checks5
public import CatalanMeasure.GapCircle.Checks6
public import CatalanMeasure.GapCircle.Checks7
public import CatalanMeasure.GapCircle.Checks8
public import CatalanMeasure.GapCircle.Checks9
public import CatalanMeasure.GapCircle.Checks10
public import CatalanMeasure.GapCircle.Checks11
public import CatalanMeasure.GapCircle.Checks12
public import CatalanMeasure.GapCircle.Checks13
@[expose] public section
namespace CatalanMeasure.GapCircle
open CatalanMeasure.Parametric
set_option maxRecDepth 1000000
set_option maxHeartbeats 6000000
theorem all_checks : pieces.all GapCirclePiece.OK=true := by
  simp only [pieces,List.all_cons,List.all_nil,Bool.and_eq_true]
  exact ⟨check0,check1,check2,check3,check4,check5,check6,check7,check8,check9,check10,check11,check12,check13,check14,check15,check16,check17,check18,check19,check20,check21,check22,check23,check24,check25,check26,check27,check28,check29,check30,check31,check32,check33,check34,check35,check36,check37,check38,check39,check40,check41,check42,check43,check44,check45,check46,check47,check48,check49,check50,check51,check52,check53,check54,True.intro⟩
theorem circle_bound (N : ℕ) (z : ℂ) (hz : ‖z‖=(1001/1000:ℝ)) :
    ‖((gapPolynomial (interpolationGap:ℝ) N).map (algebraMap ℝ ℂ)).eval z‖ *
      ‖(1:ℂ)-z‖^(2*N)≤Real.exp (gapWeightCost*N) :=
  gap_circle_bound_of_cover cover all_checks N z hz
end CatalanMeasure.GapCircle
