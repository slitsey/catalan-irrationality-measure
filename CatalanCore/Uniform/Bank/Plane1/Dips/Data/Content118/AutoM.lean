module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Data
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
theorem cellsM1_ok : cells1.all (fun c => c.ok bankM.α (kappaOf bankM.toK 1 0) (kappaOf bankM.toK 1 1))=true := by
  change cells1.all (fun c => c.ok (1/8) (1/3) (1/2))=true
  simp only [cells1,List.all_cons,List.all_nil,cell1_0_ok, cell1_1_ok, cell1_2_ok, cell1_3_ok, cell1_4_ok, cell1_5_ok, cell1_6_ok, cell1_7_ok, cell1_8_ok, cell1_9_ok, cell1_10_ok, cell1_11_ok, cell1_12_ok, cell1_13_ok, cell1_14_ok, cell1_15_ok, cell1_16_ok, cell1_17_ok, cell1_18_ok, cell1_19_ok, cell1_20_ok, cell1_21_ok, cell1_22_ok, cell1_23_ok, cell1_24_ok, cell1_25_ok, cell1_26_ok, cell1_27_ok, cell1_28_ok, cell1_29_ok, cell1_30_ok, cell1_31_ok, cell1_32_ok, cell1_33_ok, cell1_34_ok, cell1_35_ok, cell1_36_ok, cell1_37_ok, cell1_38_ok, cell1_39_ok, cell1_40_ok, cell1_41_ok, cell1_42_ok, cell1_43_ok, cell1_44_ok, cell1_45_ok, cell1_46_ok, cell1_47_ok, cell1_48_ok, cell1_49_ok, cell1_50_ok, cell1_51_ok, cell1_52_ok, cell1_53_ok, cell1_54_ok, Bool.and_self]
theorem headsM1_ok : kpieceAll bankM.toK 1 headsM1=true := by
  change kpieceAll (header 1 5).toK 1 headsM1=true
  have h0 := headM1_0_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h0
  have h1 := headM1_1_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h1
  have h2 := headM1_2_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h2
  have h3 := headM1_3_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h3
  have h4 := headM1_4_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h4
  have h5 := headM1_5_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h5
  have h6 := headM1_6_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h6
  have h7 := headM1_7_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h7
  have h8 := headM1_8_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h8
  have h9 := headM1_9_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h9
  have h10 := headM1_10_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h10
  have h11 := headM1_11_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h11
  have h12 := headM1_12_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h12
  have h13 := headM1_13_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h13
  have h14 := headM1_14_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h14
  have h15 := headM1_15_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h15
  have h16 := headM1_16_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h16
  have h17 := headM1_17_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h17
  have h18 := headM1_18_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h18
  have h19 := headM1_19_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h19
  have h20 := headM1_20_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h20
  have h21 := headM1_21_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h21
  have h22 := headM1_22_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h22
  have h23 := headM1_23_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h23
  have h24 := headM1_24_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h24
  have h25 := headM1_25_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h25
  have h26 := headM1_26_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h26
  have h27 := headM1_27_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h27
  have h28 := headM1_28_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h28
  have h29 := headM1_29_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h29
  have h30 := headM1_30_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h30
  have h31 := headM1_31_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h31
  have h32 := headM1_32_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h32
  have h33 := headM1_33_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h33
  have h34 := headM1_34_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h34
  have h35 := headM1_35_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h35
  have h36 := headM1_36_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h36
  have h37 := headM1_37_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h37
  have h38 := headM1_38_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h38
  have h39 := headM1_39_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h39
  have h40 := headM1_40_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h40
  have h41 := headM1_41_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h41
  have h42 := headM1_42_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h42
  have h43 := headM1_43_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h43
  have h44 := headM1_44_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h44
  have h45 := headM1_45_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h45
  have h46 := headM1_46_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h46
  have h47 := headM1_47_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h47
  have h48 := headM1_48_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h48
  simp only [kpieceAll,headsM1,List.all_cons,List.all_nil,h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48,Bool.true_and]
theorem cellsM5_ok : cells5.all (fun c => c.ok bankM.α (kappaOf bankM.toK 5 0) (kappaOf bankM.toK 5 1))=true := by
  change cells5.all (fun c => c.ok (1/8) (2/3) (1/2))=true
  simp only [cells5,List.all_cons,List.all_nil,cell5_0_ok, cell5_1_ok, cell5_2_ok, cell5_3_ok, cell5_4_ok, cell5_5_ok, cell5_6_ok, cell5_7_ok, cell5_8_ok, cell5_9_ok, cell5_10_ok, cell5_11_ok, cell5_12_ok, cell5_13_ok, cell5_14_ok, cell5_15_ok, cell5_16_ok, cell5_17_ok, cell5_18_ok, cell5_19_ok, cell5_20_ok, cell5_21_ok, cell5_22_ok, cell5_23_ok, cell5_24_ok, cell5_25_ok, cell5_26_ok, cell5_27_ok, cell5_28_ok, cell5_29_ok, cell5_30_ok, cell5_31_ok, cell5_32_ok, cell5_33_ok, cell5_34_ok, cell5_35_ok, cell5_36_ok, cell5_37_ok, cell5_38_ok, cell5_39_ok, cell5_40_ok, cell5_41_ok, cell5_42_ok, cell5_43_ok, cell5_44_ok, cell5_45_ok, cell5_46_ok, cell5_47_ok, cell5_48_ok, cell5_49_ok, cell5_50_ok, cell5_51_ok, cell5_52_ok, cell5_53_ok, cell5_54_ok, Bool.and_self]
theorem headsM5_ok : kpieceAll bankM.toK 5 headsM5=true := by
  change kpieceAll (header 1 5).toK 5 headsM5=true
  have h0 := headM5_0_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h0
  have h1 := headM5_1_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h1
  have h2 := headM5_2_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h2
  have h3 := headM5_3_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h3
  have h4 := headM5_4_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h4
  have h5 := headM5_5_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h5
  have h6 := headM5_6_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h6
  have h7 := headM5_7_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h7
  have h8 := headM5_8_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h8
  have h9 := headM5_9_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h9
  have h10 := headM5_10_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h10
  have h11 := headM5_11_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h11
  have h12 := headM5_12_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h12
  have h13 := headM5_13_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h13
  have h14 := headM5_14_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h14
  have h15 := headM5_15_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h15
  have h16 := headM5_16_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h16
  have h17 := headM5_17_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h17
  have h18 := headM5_18_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h18
  have h19 := headM5_19_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h19
  have h20 := headM5_20_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h20
  have h21 := headM5_21_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h21
  have h22 := headM5_22_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h22
  have h23 := headM5_23_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h23
  have h24 := headM5_24_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h24
  have h25 := headM5_25_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h25
  have h26 := headM5_26_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h26
  have h27 := headM5_27_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h27
  have h28 := headM5_28_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h28
  have h29 := headM5_29_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h29
  have h30 := headM5_30_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h30
  have h31 := headM5_31_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h31
  have h32 := headM5_32_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h32
  have h33 := headM5_33_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h33
  have h34 := headM5_34_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h34
  have h35 := headM5_35_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h35
  have h36 := headM5_36_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h36
  have h37 := headM5_37_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h37
  have h38 := headM5_38_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h38
  have h39 := headM5_39_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h39
  have h40 := headM5_40_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h40
  have h41 := headM5_41_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h41
  have h42 := headM5_42_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h42
  have h43 := headM5_43_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h43
  have h44 := headM5_44_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h44
  have h45 := headM5_45_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h45
  have h46 := headM5_46_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h46
  have h47 := headM5_47_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h47
  have h48 := headM5_48_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h48
  have h49 := headM5_49_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h49
  simp only [kpieceAll,headsM5,List.all_cons,List.all_nil,h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49,Bool.true_and]
-- kcost: complete finite params metadata; worst full-family metadata measured322.269s/9.625GiB.
set_option profiler true in
theorem paramsM_ok : kcParams bankM=true := by decide +kernel
#print axioms paramsM_ok
-- kcost: complete finite heads metadata; worst full-family metadata measured322.269s/9.625GiB.
set_option profiler true in
theorem headsM_ok : kcHeads bankM=true := by decide +kernel
#print axioms headsM_ok
-- kcost: complete finite classes metadata; worst full-family metadata measured322.269s/9.625GiB.
set_option profiler true in
theorem classesM_ok : kcClass bankM=true := by decide +kernel
#print axioms classesM_ok
theorem bankM_check : kcheckC bankM=true := by
  have hc : kcCells bankM=true := by
    change (cells1.all (fun c => c.ok bankM.α (kappaOf bankM.toK 1 0) (kappaOf bankM.toK 1 1)) &&
      (cells5.all (fun c => c.ok bankM.α (kappaOf bankM.toK 5 0) (kappaOf bankM.toK 5 1)) && true))=true
    rw [cellsM1_ok,cellsM5_ok]
    rfl
  have hp : kcPieces bankM=true := by
    change (kpieceAll bankM.toK 1 headsM1 && (kpieceAll bankM.toK 5 headsM5 && true))=true
    rw [headsM1_ok,headsM5_ok]
    rfl
  unfold kcheckC
  rw [paramsM_ok,headsM_ok,hc,hp,classesM_ok]
  rfl
#print axioms bankM_check
end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
