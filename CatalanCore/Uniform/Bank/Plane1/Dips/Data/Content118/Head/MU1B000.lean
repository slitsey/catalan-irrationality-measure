module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
def headM1_0 : QPiece × Cert := (⟨(rq (raw_ints% [1,8])), (rq (raw_ints% [5,38])), (rq (raw_ints% [5,2])), (rq (raw_ints% [-2,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨25, [], [], (rq (raw_ints% [864,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_0_ok : kpieceAll (header 1 5).toK 1 [headM1_0]=true := by decide +kernel
#print axioms headM1_0_ok
def headM1_1 : QPiece × Cert := (⟨(rq (raw_ints% [5,38])), (rq (raw_ints% [9,68])), (rq (raw_ints% [5,4])), (rq (raw_ints% [15,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨25, [], [], (rq (raw_ints% [19494,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_1_ok : kpieceAll (header 1 5).toK 1 [headM1_1]=true := by decide +kernel
#print axioms headM1_1_ok
def headM1_2 : QPiece × Cert := (⟨(rq (raw_ints% [9,68])), (rq (raw_ints% [2,15])), (rq (raw_ints% [7,2])), (rq (raw_ints% [-19,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨24, [], [], (rq (raw_ints% [2312,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_2_ok : kpieceAll (header 1 5).toK 1 [headM1_2]=true := by decide +kernel
#print axioms headM1_2_ok
def headM1_3 : QPiece × Cert := (⟨(rq (raw_ints% [2,15])), (rq (raw_ints% [15,112])), (rq (raw_ints% [5,2])), (rq (raw_ints% [-2,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨24, [], [], (rq (raw_ints% [6075,8]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_3_ok : kpieceAll (header 1 5).toK 1 [headM1_3]=true := by decide +kernel
#print axioms headM1_3_ok
def headM1_4 : QPiece × Cert := (⟨(rq (raw_ints% [15,112])), (rq (raw_ints% [27,200])), (rq (raw_ints% [5,4])), (rq (raw_ints% [22,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨24, [], [], (rq (raw_ints% [18816,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_4_ok : kpieceAll (header 1 5).toK 1 [headM1_4]=true := by decide +kernel
#print axioms headM1_4_ok
def headM1_5 : QPiece × Cert := (⟨(rq (raw_ints% [27,200])), (rq (raw_ints% [3,22])), (rq (raw_ints% [7,2])), (rq (raw_ints% [-28,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [20000,27]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_5_ok : kpieceAll (header 1 5).toK 1 [headM1_5]=true := by decide +kernel
#print axioms headM1_5_ok
def headM1_6 : QPiece × Cert := (⟨(rq (raw_ints% [3,22])), (rq (raw_ints% [5,36])), (rq (raw_ints% [5,2])), (rq (raw_ints% [-2,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [726,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_6_ok : kpieceAll (header 1 5).toK 1 [headM1_6]=true := by decide +kernel
#print axioms headM1_6_ok
def headM1_7 : QPiece × Cert := (⟨(rq (raw_ints% [5,36])), (rq (raw_ints% [9,64])), (rq (raw_ints% [5,4])), (rq (raw_ints% [7,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [17496,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_7_ok : kpieceAll (header 1 5).toK 1 [headM1_7]=true := by decide +kernel
#print axioms headM1_7_ok
def headM1_8 : QPiece × Cert := (⟨(rq (raw_ints% [9,64])), (rq (raw_ints% [1,7])), (rq (raw_ints% [7,2])), (rq (raw_ints% [-9,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [2048,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_8_ok : kpieceAll (header 1 5).toK 1 [headM1_8]=true := by decide +kernel
#print axioms headM1_8_ok
def headM1_9 : QPiece × Cert := (⟨(rq (raw_ints% [1,7])), (rq (raw_ints% [5,34])), (rq (raw_ints% [5,2])), (rq (raw_ints% [-2,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨25, [], [], (rq (raw_ints% [1323,2]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_9_ok : kpieceAll (header 1 5).toK 1 [headM1_9]=true := by decide +kernel
#print axioms headM1_9_ok
def headM1_10 : QPiece × Cert := (⟨(rq (raw_ints% [5,34])), (rq (raw_ints% [3,20])), (rq (raw_ints% [5,4])), (rq (raw_ints% [13,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨25, [], [], (rq (raw_ints% [15606,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_10_ok : kpieceAll (header 1 5).toK 1 [headM1_10]=true := by decide +kernel
#print axioms headM1_10_ok
def headM1_11 : QPiece × Cert := (⟨(rq (raw_ints% [3,20])), (rq (raw_ints% [27,176])), (rq (raw_ints% [19,8])), (rq (raw_ints% [-1,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨1, [], [], (rq (raw_ints% [600,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_11_ok : kpieceAll (header 1 5).toK 1 [headM1_11]=true := by decide +kernel
#print axioms headM1_11_ok
def headM1_12 : QPiece × Cert := (⟨(rq (raw_ints% [27,176])), (rq (raw_ints% [5,32])), (rq (raw_ints% [7,2])), (rq (raw_ints% [-25,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [15488,27]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_12_ok : kpieceAll (header 1 5).toK 1 [headM1_12]=true := by decide +kernel
#print axioms headM1_12_ok
def headM1_13 : QPiece × Cert := (⟨(rq (raw_ints% [5,32])), (rq (raw_ints% [3,19])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [13824,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_13_ok : kpieceAll (header 1 5).toK 1 [headM1_13]=true := by decide +kernel
#print axioms headM1_13_ok
def headM1_14 : QPiece × Cert := (⟨(rq (raw_ints% [3,19])), (rq (raw_ints% [9,56])), (rq (raw_ints% [5,4])), (rq (raw_ints% [6,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [1083,2]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_14_ok : kpieceAll (header 1 5).toK 1 [headM1_14]=true := by decide +kernel
#print axioms headM1_14_ok
def headM1_15 : QPiece × Cert := (⟨(rq (raw_ints% [9,56])), (rq (raw_ints% [1,6])), (rq (raw_ints% [7,2])), (rq (raw_ints% [-8,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [1568,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_15_ok : kpieceAll (header 1 5).toK 1 [headM1_15]=true := by decide +kernel
#print axioms headM1_15_ok
def headM1_16 : QPiece × Cert := (⟨(rq (raw_ints% [1,6])), (rq (raw_ints% [9,52])), (rq (raw_ints% [5,4])), (rq (raw_ints% [11,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨25, [(rq (raw_ints% [15,88]))], [], (rq (raw_ints% [486,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_16_ok : kpieceAll (header 1 5).toK 1 [headM1_16]=true := by decide +kernel
#print axioms headM1_16_ok
def headM1_17 : QPiece × Cert := (⟨(rq (raw_ints% [9,52])), (rq (raw_ints% [27,152])), (rq (raw_ints% [19,8])), (rq (raw_ints% [-1,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨1, [], [], (rq (raw_ints% [1352,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_17_ok : kpieceAll (header 1 5).toK 1 [headM1_17]=true := by decide +kernel
#print axioms headM1_17_ok
def headM1_18 : QPiece × Cert := (⟨(rq (raw_ints% [27,152])), (rq (raw_ints% [5,28])), (rq (raw_ints% [7,2])), (rq (raw_ints% [-22,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [11552,27]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_18_ok : kpieceAll (header 1 5).toK 1 [headM1_18]=true := by decide +kernel
#print axioms headM1_18_ok
def headM1_19 : QPiece × Cert := (⟨(rq (raw_ints% [5,28])), (rq (raw_ints% [3,16])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [10584,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_19_ok : kpieceAll (header 1 5).toK 1 [headM1_19]=true := by decide +kernel
#print axioms headM1_19_ok
def headM1_20 : QPiece × Cert := (⟨(rq (raw_ints% [3,16])), (rq (raw_ints% [5,26])), (rq (raw_ints% [7,2])), (rq (raw_ints% [-7,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [384,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_20_ok : kpieceAll (header 1 5).toK 1 [headM1_20]=true := by decide +kernel
#print axioms headM1_20_ok
def headM1_21 : QPiece × Cert := (⟨(rq (raw_ints% [5,26])), (rq (raw_ints% [1,5])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [(rq (raw_ints% [15,76]))], [], (rq (raw_ints% [9126,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_21_ok : kpieceAll (header 1 5).toK 1 [headM1_21]=true := by decide +kernel
#print axioms headM1_21_ok
def headM1_22 : QPiece × Cert := (⟨(rq (raw_ints% [1,5])), (rq (raw_ints% [9,44])), (rq (raw_ints% [5,4])), (rq (raw_ints% [9,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨25, [], [], (rq (raw_ints% [675,2]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_22_ok : kpieceAll (header 1 5).toK 1 [headM1_22]=true := by decide +kernel
#print axioms headM1_22_ok
def headM1_23 : QPiece × Cert := (⟨(rq (raw_ints% [9,44])), (rq (raw_ints% [9,40])), (rq (raw_ints% [19,8])), (rq (raw_ints% [-1,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨1, [], [], (rq (raw_ints% [968,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_23_ok : kpieceAll (header 1 5).toK 1 [headM1_23]=true := by decide +kernel
#print axioms headM1_23_ok

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
