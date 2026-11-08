module

public import CatalanMeasure.GenD.Signed.RouteI.T4LeafDefs
public import CatalanMeasure.GenD.Signed.RouteI.T4LeafSheets
public import CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys0
public import CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys1
public import CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys2
public import CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys3
public import CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys4
public import CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys5
public import CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys6
public import CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys7

@[expose] public section

/-!
# T4 leaf data: assembled statements

The `Fin`-indexed statements in the shape of the fields of `TerminalC.NearData` (`hP2`, `hPW`, `hPφ`, `hPω`, `hΔ0`, `hs`, `hs'`,
`hF0`, `hη`), `LargeData.hPoly` and `FirstData.hPoly`.  The piece data (`A B nC fC rs np`) are the `T4LeafDefs` functions.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.T4LeafAll
open CatalanMeasure.GenD.Signed.RouteI.T4Instance CatalanMeasure.GenD.Signed.RouteI.T4LeafDefs
noncomputable section

theorem lC_η_pos : 0 < lC.η := by norm_num [lC]

theorem phys_hF0 : (physF0 : ℝ) = testF 0 := by
  rw [testF_zero_val]; norm_num [physF0]

set_option maxHeartbeats 4000000 in
theorem phys_hAB : ∀ j : Fin 64, physA j < physB j := by
  intro j; fin_cases j <;> norm_num [physA, physB, physAL, physBL]

theorem phys_hA0 : ∀ j : Fin 64, 0 ≤ physA j := by
  intro j; fin_cases j <;> norm_num [physA, physAL]

theorem phys_hB1 : ∀ j : Fin 64, physB j ≤ a1Q := by
  intro j; fin_cases j <;> norm_num [physB, physBL, a1Q]

set_option maxHeartbeats 4000000 in
theorem phys_hΔ0 : ∀ j : Fin 64, 0 ≤ (physΔ j : ℝ) := by
  intro j; fin_cases j <;> norm_num [physΔ, physΔL]

set_option maxHeartbeats 4000000 in
theorem phys_hs : ∀ j : Fin 64, Real.sqrt (7877 / 10000 * ((physΔ j : ℝ) / 2)) ≤ physS j := by
  intro j
  rw [Real.sqrt_le_iff]
  fin_cases j <;> norm_num [physΔ, physΔL, physS, physSL]

set_option maxHeartbeats 4000000 in
theorem phys_hs' : ∀ j : Fin 64, Real.sqrt (2 * ((physΔ j : ℝ) / 2)) ≤ physS' j := by
  intro j
  rw [Real.sqrt_le_iff]
  fin_cases j <;> norm_num [physΔ, physΔL, physS', physS'L]

theorem large_hAB : ∀ k : Fin 6, largeA k < largeB k := by
  intro k; fin_cases k <;> norm_num [largeA, largeB]

theorem first_hAB : ∀ k : Fin 6, firstA k < firstB k := by
  intro k; fin_cases k <;> norm_num [firstA, firstB]

theorem large_hA0 : ∀ k : Fin 6, (51 / 500 : ℝ) ≤ largeA k := by
  intro k; fin_cases k <;> norm_num [largeA]

theorem first_hA0 : ∀ k : Fin 6, 0 ≤ firstA k := by
  intro k; fin_cases k <;> norm_num [firstA]

theorem large_hB1 : ∀ k : Fin 6, largeB k ≤ 1 := by
  intro k; fin_cases k <;> norm_num [largeB]

theorem first_hB1 : ∀ k : Fin 6, firstB k ≤ 1 := by
  intro k; fin_cases k <;> norm_num [firstB]

theorem phys_hPW : ∀ j : Fin 64, PolyNonneg (wPq lC.σ lC.η (physΔ j) physNC physFC physRS physNP) (physA j) (physB j) := by
  intro j
  fin_cases j
  · exact T4LeafPhys0.physW_0
  · exact T4LeafPhys0.physW_1
  · exact T4LeafPhys0.physW_2
  · exact T4LeafPhys0.physW_3
  · exact T4LeafPhys0.physW_4
  · exact T4LeafPhys0.physW_5
  · exact T4LeafPhys0.physW_6
  · exact T4LeafPhys0.physW_7
  · exact T4LeafPhys1.physW_8
  · exact T4LeafPhys1.physW_9
  · exact T4LeafPhys1.physW_10
  · exact T4LeafPhys1.physW_11
  · exact T4LeafPhys1.physW_12
  · exact T4LeafPhys1.physW_13
  · exact T4LeafPhys1.physW_14
  · exact T4LeafPhys1.physW_15
  · exact T4LeafPhys2.physW_16
  · exact T4LeafPhys2.physW_17
  · exact T4LeafPhys2.physW_18
  · exact T4LeafPhys2.physW_19
  · exact T4LeafPhys2.physW_20
  · exact T4LeafPhys2.physW_21
  · exact T4LeafPhys2.physW_22
  · exact T4LeafPhys2.physW_23
  · exact T4LeafPhys3.physW_24
  · exact T4LeafPhys3.physW_25
  · exact T4LeafPhys3.physW_26
  · exact T4LeafPhys3.physW_27
  · exact T4LeafPhys3.physW_28
  · exact T4LeafPhys3.physW_29
  · exact T4LeafPhys3.physW_30
  · exact T4LeafPhys3.physW_31
  · exact T4LeafPhys4.physW_32
  · exact T4LeafPhys4.physW_33
  · exact T4LeafPhys4.physW_34
  · exact T4LeafPhys4.physW_35
  · exact T4LeafPhys4.physW_36
  · exact T4LeafPhys4.physW_37
  · exact T4LeafPhys4.physW_38
  · exact T4LeafPhys4.physW_39
  · exact T4LeafPhys5.physW_40
  · exact T4LeafPhys5.physW_41
  · exact T4LeafPhys5.physW_42
  · exact T4LeafPhys5.physW_43
  · exact T4LeafPhys5.physW_44
  · exact T4LeafPhys5.physW_45
  · exact T4LeafPhys5.physW_46
  · exact T4LeafPhys5.physW_47
  · exact T4LeafPhys6.physW_48
  · exact T4LeafPhys6.physW_49
  · exact T4LeafPhys6.physW_50
  · exact T4LeafPhys6.physW_51
  · exact T4LeafPhys6.physW_52
  · exact T4LeafPhys6.physW_53
  · exact T4LeafPhys6.physW_54
  · exact T4LeafPhys6.physW_55
  · exact T4LeafPhys7.physW_56
  · exact T4LeafPhys7.physW_57
  · exact T4LeafPhys7.physW_58
  · exact T4LeafPhys7.physW_59
  · exact T4LeafPhys7.physW_60
  · exact T4LeafPhys7.physW_61
  · exact T4LeafPhys7.physW_62
  · exact T4LeafPhys7.physW_63

theorem phys_hPφ : ∀ j : Fin 64, PolyNonneg (addQ [-lC.η] (phiQ physF0 physU physFU (physS j))) (physA j) (physB j) := by
  intro j
  fin_cases j
  · exact T4LeafPhys0.physPhi_0
  · exact T4LeafPhys0.physPhi_1
  · exact T4LeafPhys0.physPhi_2
  · exact T4LeafPhys0.physPhi_3
  · exact T4LeafPhys0.physPhi_4
  · exact T4LeafPhys0.physPhi_5
  · exact T4LeafPhys0.physPhi_6
  · exact T4LeafPhys0.physPhi_7
  · exact T4LeafPhys1.physPhi_8
  · exact T4LeafPhys1.physPhi_9
  · exact T4LeafPhys1.physPhi_10
  · exact T4LeafPhys1.physPhi_11
  · exact T4LeafPhys1.physPhi_12
  · exact T4LeafPhys1.physPhi_13
  · exact T4LeafPhys1.physPhi_14
  · exact T4LeafPhys1.physPhi_15
  · exact T4LeafPhys2.physPhi_16
  · exact T4LeafPhys2.physPhi_17
  · exact T4LeafPhys2.physPhi_18
  · exact T4LeafPhys2.physPhi_19
  · exact T4LeafPhys2.physPhi_20
  · exact T4LeafPhys2.physPhi_21
  · exact T4LeafPhys2.physPhi_22
  · exact T4LeafPhys2.physPhi_23
  · exact T4LeafPhys3.physPhi_24
  · exact T4LeafPhys3.physPhi_25
  · exact T4LeafPhys3.physPhi_26
  · exact T4LeafPhys3.physPhi_27
  · exact T4LeafPhys3.physPhi_28
  · exact T4LeafPhys3.physPhi_29
  · exact T4LeafPhys3.physPhi_30
  · exact T4LeafPhys3.physPhi_31
  · exact T4LeafPhys4.physPhi_32
  · exact T4LeafPhys4.physPhi_33
  · exact T4LeafPhys4.physPhi_34
  · exact T4LeafPhys4.physPhi_35
  · exact T4LeafPhys4.physPhi_36
  · exact T4LeafPhys4.physPhi_37
  · exact T4LeafPhys4.physPhi_38
  · exact T4LeafPhys4.physPhi_39
  · exact T4LeafPhys5.physPhi_40
  · exact T4LeafPhys5.physPhi_41
  · exact T4LeafPhys5.physPhi_42
  · exact T4LeafPhys5.physPhi_43
  · exact T4LeafPhys5.physPhi_44
  · exact T4LeafPhys5.physPhi_45
  · exact T4LeafPhys5.physPhi_46
  · exact T4LeafPhys5.physPhi_47
  · exact T4LeafPhys6.physPhi_48
  · exact T4LeafPhys6.physPhi_49
  · exact T4LeafPhys6.physPhi_50
  · exact T4LeafPhys6.physPhi_51
  · exact T4LeafPhys6.physPhi_52
  · exact T4LeafPhys6.physPhi_53
  · exact T4LeafPhys6.physPhi_54
  · exact T4LeafPhys6.physPhi_55
  · exact T4LeafPhys7.physPhi_56
  · exact T4LeafPhys7.physPhi_57
  · exact T4LeafPhys7.physPhi_58
  · exact T4LeafPhys7.physPhi_59
  · exact T4LeafPhys7.physPhi_60
  · exact T4LeafPhys7.physPhi_61
  · exact T4LeafPhys7.physPhi_62
  · exact T4LeafPhys7.physPhi_63

theorem phys_hPω : ∀ j : Fin 64, PolyNonneg (addQ [-lC.η] (omQ physP2 physDU2 (physS' j))) (physA j) (physB j) := by
  intro j
  fin_cases j
  · exact T4LeafPhys0.physOm_0
  · exact T4LeafPhys0.physOm_1
  · exact T4LeafPhys0.physOm_2
  · exact T4LeafPhys0.physOm_3
  · exact T4LeafPhys0.physOm_4
  · exact T4LeafPhys0.physOm_5
  · exact T4LeafPhys0.physOm_6
  · exact T4LeafPhys0.physOm_7
  · exact T4LeafPhys1.physOm_8
  · exact T4LeafPhys1.physOm_9
  · exact T4LeafPhys1.physOm_10
  · exact T4LeafPhys1.physOm_11
  · exact T4LeafPhys1.physOm_12
  · exact T4LeafPhys1.physOm_13
  · exact T4LeafPhys1.physOm_14
  · exact T4LeafPhys1.physOm_15
  · exact T4LeafPhys2.physOm_16
  · exact T4LeafPhys2.physOm_17
  · exact T4LeafPhys2.physOm_18
  · exact T4LeafPhys2.physOm_19
  · exact T4LeafPhys2.physOm_20
  · exact T4LeafPhys2.physOm_21
  · exact T4LeafPhys2.physOm_22
  · exact T4LeafPhys2.physOm_23
  · exact T4LeafPhys3.physOm_24
  · exact T4LeafPhys3.physOm_25
  · exact T4LeafPhys3.physOm_26
  · exact T4LeafPhys3.physOm_27
  · exact T4LeafPhys3.physOm_28
  · exact T4LeafPhys3.physOm_29
  · exact T4LeafPhys3.physOm_30
  · exact T4LeafPhys3.physOm_31
  · exact T4LeafPhys4.physOm_32
  · exact T4LeafPhys4.physOm_33
  · exact T4LeafPhys4.physOm_34
  · exact T4LeafPhys4.physOm_35
  · exact T4LeafPhys4.physOm_36
  · exact T4LeafPhys4.physOm_37
  · exact T4LeafPhys4.physOm_38
  · exact T4LeafPhys4.physOm_39
  · exact T4LeafPhys5.physOm_40
  · exact T4LeafPhys5.physOm_41
  · exact T4LeafPhys5.physOm_42
  · exact T4LeafPhys5.physOm_43
  · exact T4LeafPhys5.physOm_44
  · exact T4LeafPhys5.physOm_45
  · exact T4LeafPhys5.physOm_46
  · exact T4LeafPhys5.physOm_47
  · exact T4LeafPhys6.physOm_48
  · exact T4LeafPhys6.physOm_49
  · exact T4LeafPhys6.physOm_50
  · exact T4LeafPhys6.physOm_51
  · exact T4LeafPhys6.physOm_52
  · exact T4LeafPhys6.physOm_53
  · exact T4LeafPhys6.physOm_54
  · exact T4LeafPhys6.physOm_55
  · exact T4LeafPhys7.physOm_56
  · exact T4LeafPhys7.physOm_57
  · exact T4LeafPhys7.physOm_58
  · exact T4LeafPhys7.physOm_59
  · exact T4LeafPhys7.physOm_60
  · exact T4LeafPhys7.physOm_61
  · exact T4LeafPhys7.physOm_62
  · exact T4LeafPhys7.physOm_63

theorem large_hPoly : ∀ k : Fin 6, PolyNonneg (wPq lC.σ lC.η 0 (largeNC k) (largeFC k) (largeRs k) (largeNp k)) (largeA k) (largeB k) := by
  intro k
  fin_cases k
  · exact T4LeafSheets.largeW_0
  · exact T4LeafSheets.largeW_1
  · exact T4LeafSheets.largeW_2
  · exact T4LeafSheets.largeW_3
  · exact T4LeafSheets.largeW_4
  · exact T4LeafSheets.largeW_5

theorem first_hPoly : ∀ k : Fin 6, PolyNonneg (wPq lC.σ lC.η 0 (firstNC k) (firstFC k) (firstRs k) (firstNp k)) (firstA k) (firstB k) := by
  intro k
  fin_cases k
  · exact T4LeafSheets.firstW_0
  · exact T4LeafSheets.firstW_1
  · exact T4LeafSheets.firstW_2
  · exact T4LeafSheets.firstW_3
  · exact T4LeafSheets.firstW_4
  · exact T4LeafSheets.firstW_5

theorem sig_hP2 : PolyNonneg (sigP2 lC) aeQ a1Q := T4LeafSheets.sigP2_ok

theorem sig_hP1 : PolyNonneg (sigP1 lC) 0 aeQ := T4LeafSheets.sigP1_ok

end
end CatalanMeasure.GenD.Signed.RouteI.T4LeafAll

#print axioms CatalanMeasure.GenD.Signed.RouteI.T4LeafAll.phys_hPW
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4LeafAll.phys_hPφ
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4LeafAll.phys_hPω
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4LeafAll.large_hPoly
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4LeafAll.first_hPoly
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4LeafAll.sig_hP1
#print axioms CatalanMeasure.GenD.Signed.RouteI.T4LeafAll.sig_hP2
