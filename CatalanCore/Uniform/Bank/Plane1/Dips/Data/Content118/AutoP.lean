module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Data
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
theorem cellsP1_ok : cells1.all (fun c => c.ok bankP.α (kappaOf bankP.toK 1 0) (kappaOf bankP.toK 1 1))=true := by
  change cells1.all (fun c => c.ok (1/8) (1/3) (1/2))=true
  simp only [cells1,List.all_cons,List.all_nil,cell1_0_ok, cell1_1_ok, cell1_2_ok, cell1_3_ok, cell1_4_ok, cell1_5_ok, cell1_6_ok, cell1_7_ok, cell1_8_ok, cell1_9_ok, cell1_10_ok, cell1_11_ok, cell1_12_ok, cell1_13_ok, cell1_14_ok, cell1_15_ok, cell1_16_ok, cell1_17_ok, cell1_18_ok, cell1_19_ok, cell1_20_ok, cell1_21_ok, cell1_22_ok, cell1_23_ok, cell1_24_ok, cell1_25_ok, cell1_26_ok, cell1_27_ok, cell1_28_ok, cell1_29_ok, cell1_30_ok, cell1_31_ok, cell1_32_ok, cell1_33_ok, cell1_34_ok, cell1_35_ok, cell1_36_ok, cell1_37_ok, cell1_38_ok, cell1_39_ok, cell1_40_ok, cell1_41_ok, cell1_42_ok, cell1_43_ok, cell1_44_ok, cell1_45_ok, cell1_46_ok, cell1_47_ok, cell1_48_ok, cell1_49_ok, cell1_50_ok, cell1_51_ok, cell1_52_ok, cell1_53_ok, cell1_54_ok, Bool.and_self]
theorem headsP1_ok : kpieceAll bankP.toK 1 headsP1=true := by
  change kpieceAll (header 2 1).toK 1 headsP1=true
  have h0 := headP1_0_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h0
  have h1 := headP1_1_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h1
  have h2 := headP1_2_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h2
  have h3 := headP1_3_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h3
  have h4 := headP1_4_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h4
  have h5 := headP1_5_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h5
  have h6 := headP1_6_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h6
  have h7 := headP1_7_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h7
  have h8 := headP1_8_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h8
  have h9 := headP1_9_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h9
  have h10 := headP1_10_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h10
  have h11 := headP1_11_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h11
  have h12 := headP1_12_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h12
  have h13 := headP1_13_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h13
  have h14 := headP1_14_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h14
  have h15 := headP1_15_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h15
  have h16 := headP1_16_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h16
  have h17 := headP1_17_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h17
  have h18 := headP1_18_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h18
  have h19 := headP1_19_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h19
  have h20 := headP1_20_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h20
  have h21 := headP1_21_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h21
  have h22 := headP1_22_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h22
  have h23 := headP1_23_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h23
  have h24 := headP1_24_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h24
  have h25 := headP1_25_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h25
  have h26 := headP1_26_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h26
  have h27 := headP1_27_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h27
  have h28 := headP1_28_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h28
  have h29 := headP1_29_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h29
  have h30 := headP1_30_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h30
  have h31 := headP1_31_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h31
  have h32 := headP1_32_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h32
  have h33 := headP1_33_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h33
  have h34 := headP1_34_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h34
  have h35 := headP1_35_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h35
  have h36 := headP1_36_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h36
  have h37 := headP1_37_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h37
  have h38 := headP1_38_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h38
  have h39 := headP1_39_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h39
  have h40 := headP1_40_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h40
  have h41 := headP1_41_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h41
  have h42 := headP1_42_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h42
  have h43 := headP1_43_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h43
  have h44 := headP1_44_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h44
  have h45 := headP1_45_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h45
  have h46 := headP1_46_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h46
  have h47 := headP1_47_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h47
  have h48 := headP1_48_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h48
  simp only [kpieceAll,headsP1,List.all_cons,List.all_nil,h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48,Bool.true_and]
theorem cellsP5_ok : cells5.all (fun c => c.ok bankP.α (kappaOf bankP.toK 5 0) (kappaOf bankP.toK 5 1))=true := by
  change cells5.all (fun c => c.ok (1/8) (2/3) (1/2))=true
  simp only [cells5,List.all_cons,List.all_nil,cell5_0_ok, cell5_1_ok, cell5_2_ok, cell5_3_ok, cell5_4_ok, cell5_5_ok, cell5_6_ok, cell5_7_ok, cell5_8_ok, cell5_9_ok, cell5_10_ok, cell5_11_ok, cell5_12_ok, cell5_13_ok, cell5_14_ok, cell5_15_ok, cell5_16_ok, cell5_17_ok, cell5_18_ok, cell5_19_ok, cell5_20_ok, cell5_21_ok, cell5_22_ok, cell5_23_ok, cell5_24_ok, cell5_25_ok, cell5_26_ok, cell5_27_ok, cell5_28_ok, cell5_29_ok, cell5_30_ok, cell5_31_ok, cell5_32_ok, cell5_33_ok, cell5_34_ok, cell5_35_ok, cell5_36_ok, cell5_37_ok, cell5_38_ok, cell5_39_ok, cell5_40_ok, cell5_41_ok, cell5_42_ok, cell5_43_ok, cell5_44_ok, cell5_45_ok, cell5_46_ok, cell5_47_ok, cell5_48_ok, cell5_49_ok, cell5_50_ok, cell5_51_ok, cell5_52_ok, cell5_53_ok, cell5_54_ok, Bool.and_self]
theorem headsP5_ok : kpieceAll bankP.toK 5 headsP5=true := by
  change kpieceAll (header 2 1).toK 5 headsP5=true
  have h0 := headP5_0_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h0
  have h1 := headP5_1_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h1
  have h2 := headP5_2_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h2
  have h3 := headP5_3_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h3
  have h4 := headP5_4_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h4
  have h5 := headP5_5_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h5
  have h6 := headP5_6_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h6
  have h7 := headP5_7_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h7
  have h8 := headP5_8_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h8
  have h9 := headP5_9_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h9
  have h10 := headP5_10_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h10
  have h11 := headP5_11_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h11
  have h12 := headP5_12_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h12
  have h13 := headP5_13_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h13
  have h14 := headP5_14_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h14
  have h15 := headP5_15_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h15
  have h16 := headP5_16_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h16
  have h17 := headP5_17_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h17
  have h18 := headP5_18_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h18
  have h19 := headP5_19_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h19
  have h20 := headP5_20_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h20
  have h21 := headP5_21_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h21
  have h22 := headP5_22_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h22
  have h23 := headP5_23_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h23
  have h24 := headP5_24_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h24
  have h25 := headP5_25_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h25
  have h26 := headP5_26_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h26
  have h27 := headP5_27_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h27
  have h28 := headP5_28_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h28
  have h29 := headP5_29_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h29
  have h30 := headP5_30_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h30
  have h31 := headP5_31_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h31
  have h32 := headP5_32_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h32
  have h33 := headP5_33_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h33
  have h34 := headP5_34_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h34
  have h35 := headP5_35_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h35
  have h36 := headP5_36_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h36
  have h37 := headP5_37_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h37
  have h38 := headP5_38_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h38
  have h39 := headP5_39_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h39
  have h40 := headP5_40_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h40
  have h41 := headP5_41_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h41
  have h42 := headP5_42_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h42
  have h43 := headP5_43_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h43
  have h44 := headP5_44_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h44
  have h45 := headP5_45_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h45
  have h46 := headP5_46_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h46
  have h47 := headP5_47_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h47
  have h48 := headP5_48_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h48
  have h49 := headP5_49_ok
  simp only [kpieceAll,List.all_cons,List.all_nil,Bool.and_true] at h49
  simp only [kpieceAll,headsP5,List.all_cons,List.all_nil,h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49,Bool.true_and]
-- kcost: complete finite params metadata; worst full-family metadata measured322.269s/9.625GiB.
set_option profiler true in
theorem paramsP_ok : kcParams bankP=true := by decide +kernel
#print axioms paramsP_ok
-- kcost: complete finite heads metadata; worst full-family metadata measured322.269s/9.625GiB.
set_option profiler true in
theorem headsP_ok : kcHeads bankP=true := by decide +kernel
#print axioms headsP_ok
-- kcost: complete finite classes metadata; worst full-family metadata measured322.269s/9.625GiB.
set_option profiler true in
theorem classesP_ok : kcClass bankP=true := by decide +kernel
#print axioms classesP_ok
theorem bankP_check : kcheckC bankP=true := by
  have hc : kcCells bankP=true := by
    change (cells1.all (fun c => c.ok bankP.α (kappaOf bankP.toK 1 0) (kappaOf bankP.toK 1 1)) &&
      (cells5.all (fun c => c.ok bankP.α (kappaOf bankP.toK 5 0) (kappaOf bankP.toK 5 1)) && true))=true
    rw [cellsP1_ok,cellsP5_ok]
    rfl
  have hp : kcPieces bankP=true := by
    change (kpieceAll bankP.toK 1 headsP1 && (kpieceAll bankP.toK 5 headsP5 && true))=true
    rw [headsP1_ok,headsP5_ok]
    rfl
  unfold kcheckC
  rw [paramsP_ok,headsP_ok,hc,hp,classesP_ok]
  rfl
#print axioms bankP_check
end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
