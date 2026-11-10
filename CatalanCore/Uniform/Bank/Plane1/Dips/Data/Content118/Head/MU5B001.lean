module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
def headM5_24 : QPiece × Cert := (⟨(rq (raw_ints% [9,44])), (rq (raw_ints% [5,24])), (rq (raw_ints% [7,2])), (rq (raw_ints% [-13,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [968,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_24_ok : kpieceAll (header 1 5).toK 5 [headM5_24]=true := by decide +kernel
#print axioms headM5_24_ok
def headM5_25 : QPiece × Cert := (⟨(rq (raw_ints% [5,24])), (rq (raw_ints% [2,9])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [(rq (raw_ints% [3,14]))], [], (rq (raw_ints% [7776,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_25_ok : kpieceAll (header 1 5).toK 5 [headM5_25]=true := by decide +kernel
#print axioms headM5_25_ok
def headM5_26 : QPiece × Cert := (⟨(rq (raw_ints% [2,9])), (rq (raw_ints% [9,40])), (rq (raw_ints% [5,4])), (rq (raw_ints% [4,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [2187,8]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_26_ok : kpieceAll (header 1 5).toK 5 [headM5_26]=true := by decide +kernel
#print axioms headM5_26_ok
def headM5_27 : QPiece × Cert := (⟨(rq (raw_ints% [9,40])), (rq (raw_ints% [1,4])), (rq (raw_ints% [19,8])), (rq (raw_ints% [-1,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨1, [], [], (rq (raw_ints% [800,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_27_ok : kpieceAll (header 1 5).toK 5 [headM5_27]=true := by decide +kernel
#print axioms headM5_27_ok
def headM5_28 : QPiece × Cert := (⟨(rq (raw_ints% [1,4])), (rq (raw_ints% [5,18])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [(rq (raw_ints% [15,56]))], [], (rq (raw_ints% [216,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_28_ok : kpieceAll (header 1 5).toK 5 [headM5_28]=true := by decide +kernel
#print axioms headM5_28_ok
def headM5_29 : QPiece × Cert := (⟨(rq (raw_ints% [5,18])), (rq (raw_ints% [9,32])), (rq (raw_ints% [1,1])), (rq (raw_ints% [4,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [4374,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_29_ok : kpieceAll (header 1 5).toK 5 [headM5_29]=true := by decide +kernel
#print axioms headM5_29_ok
def headM5_30 : QPiece × Cert := (⟨(rq (raw_ints% [9,32])), (rq (raw_ints% [9,28])), (rq (raw_ints% [17,8])), (rq (raw_ints% [0,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨1, [], [], (rq (raw_ints% [512,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_30_ok : kpieceAll (header 1 5).toK 5 [headM5_30]=true := by decide +kernel
#print axioms headM5_30_ok
def headM5_31 : QPiece × Cert := (⟨(rq (raw_ints% [9,28])), (rq (raw_ints% [1,3])), (rq (raw_ints% [13,4])), (rq (raw_ints% [-7,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨8, [], [], (rq (raw_ints% [392,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_31_ok : kpieceAll (header 1 5).toK 5 [headM5_31]=true := by decide +kernel
#print axioms headM5_31_ok
def headM5_32 : QPiece × Cert := (⟨(rq (raw_ints% [1,3])), (rq (raw_ints% [5,14])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [(rq (raw_ints% [15,44]))], [], (rq (raw_ints% [243,2]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_32_ok : kpieceAll (header 1 5).toK 5 [headM5_32]=true := by decide +kernel
#print axioms headM5_32_ok
def headM5_33 : QPiece × Cert := (⟨(rq (raw_ints% [5,14])), (rq (raw_ints% [3,8])), (rq (raw_ints% [1,1])), (rq (raw_ints% [3,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [2646,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_33_ok : kpieceAll (header 1 5).toK 5 [headM5_33]=true := by decide +kernel
#print axioms headM5_33_ok
def headM5_34 : QPiece × Cert := (⟨(rq (raw_ints% [3,8])), (rq (raw_ints% [5,12])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [96,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_34_ok : kpieceAll (header 1 5).toK 5 [headM5_34]=true := by decide +kernel
#print axioms headM5_34_ok
def headM5_35 : QPiece × Cert := (⟨(rq (raw_ints% [5,12])), (rq (raw_ints% [27,64])), (rq (raw_ints% [1,1])), (rq (raw_ints% [8,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [1944,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_35_ok : kpieceAll (header 1 5).toK 5 [headM5_35]=true := by decide +kernel
#print axioms headM5_35_ok
def headM5_36 : QPiece × Cert := (⟨(rq (raw_ints% [27,64])), (rq (raw_ints% [9,20])), (rq (raw_ints% [17,8])), (rq (raw_ints% [0,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨1, [], [], (rq (raw_ints% [2048,27]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_36_ok : kpieceAll (header 1 5).toK 5 [headM5_36]=true := by decide +kernel
#print axioms headM5_36_ok
def headM5_37 : QPiece × Cert := (⟨(rq (raw_ints% [9,20])), (rq (raw_ints% [1,2])), (rq (raw_ints% [13,4])), (rq (raw_ints% [-5,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨8, [(rq (raw_ints% [15,32]))], [], (rq (raw_ints% [200,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_37_ok : kpieceAll (header 1 5).toK 5 [headM5_37]=true := by decide +kernel
#print axioms headM5_37_ok
def headM5_38 : QPiece × Cert := (⟨(rq (raw_ints% [1,2])), (rq (raw_ints% [9,16])), (rq (raw_ints% [1,1])), (rq (raw_ints% [2,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [54,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_38_ok : kpieceAll (header 1 5).toK 5 [headM5_38]=true := by decide +kernel
#print axioms headM5_38_ok
def headM5_39 : QPiece × Cert := (⟨(rq (raw_ints% [9,16])), (rq (raw_ints% [3,5])), (rq (raw_ints% [13,4])), (rq (raw_ints% [-2,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [128,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_39_ok : kpieceAll (header 1 5).toK 5 [headM5_39]=true := by decide +kernel
#print axioms headM5_39_ok
def headM5_40 : QPiece × Cert := (⟨(rq (raw_ints% [3,5])), (rq (raw_ints% [5,8])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [75,2]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_40_ok : kpieceAll (header 1 5).toK 5 [headM5_40]=true := by decide +kernel
#print axioms headM5_40_ok
def headM5_41 : QPiece × Cert := (⟨(rq (raw_ints% [5,8])), (rq (raw_ints% [27,40])), (rq (raw_ints% [1,1])), (rq (raw_ints% [5,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [864,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_41_ok : kpieceAll (header 1 5).toK 5 [headM5_41]=true := by decide +kernel
#print axioms headM5_41_ok
def headM5_42 : QPiece × Cert := (⟨(rq (raw_ints% [27,40])), (rq (raw_ints% [3,4])), (rq (raw_ints% [17,8])), (rq (raw_ints% [0,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨1, [], [], (rq (raw_ints% [800,27]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_42_ok : kpieceAll (header 1 5).toK 5 [headM5_42]=true := by decide +kernel
#print axioms headM5_42_ok
def headM5_43 : QPiece × Cert := (⟨(rq (raw_ints% [3,4])), (rq (raw_ints% [5,6])), (rq (raw_ints% [13,4])), (rq (raw_ints% [-3,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨2, [], [], (rq (raw_ints% [24,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_43_ok : kpieceAll (header 1 5).toK 5 [headM5_43]=true := by decide +kernel
#print axioms headM5_43_ok
def headM5_44 : QPiece × Cert := (⟨(rq (raw_ints% [5,6])), (rq (raw_ints% [5,4])), (rq (raw_ints% [9,2])), (rq (raw_ints% [-3,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨7, [(rq (raw_ints% [1,1]))], [], (rq (raw_ints% [102,5]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_44_ok : kpieceAll (header 1 5).toK 5 [headM5_44]=true := by decide +kernel
#print axioms headM5_44_ok
def headM5_45 : QPiece × Cert := (⟨(rq (raw_ints% [5,4])), (rq (raw_ints% [3,2])), (rq (raw_ints% [2,1])), (rq (raw_ints% [-1,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨7, [], [], (rq (raw_ints% [68,5]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_45_ok : kpieceAll (header 1 5).toK 5 [headM5_45]=true := by decide +kernel
#print axioms headM5_45_ok
def headM5_46 : QPiece × Cert := (⟨(rq (raw_ints% [3,2])), (rq (raw_ints% [15,8])), (rq (raw_ints% [1,1])), (rq (raw_ints% [-1,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨7, [], [], (rq (raw_ints% [34,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_46_ok : kpieceAll (header 1 5).toK 5 [headM5_46]=true := by decide +kernel
#print axioms headM5_46_ok
def headM5_47 : QPiece × Cert := (⟨(rq (raw_ints% [15,8])), (rq (raw_ints% [2,1])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨3, [], [], (rq (raw_ints% [96,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_47_ok : kpieceAll (header 1 5).toK 5 [headM5_47]=true := by decide +kernel
#print axioms headM5_47_ok

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
