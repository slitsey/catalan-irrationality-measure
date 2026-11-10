module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
def headP5_24 : QPiece × Cert := (⟨(rq (raw_ints% [9,44])), (rq (raw_ints% [5,24])), (rq (raw_ints% [7,2])), (rq (raw_ints% [-13,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [968,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_24_ok : kpieceAll (header 2 1).toK 5 [headP5_24]=true := by decide +kernel
#print axioms headP5_24_ok
def headP5_25 : QPiece × Cert := (⟨(rq (raw_ints% [5,24])), (rq (raw_ints% [2,9])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [(rq (raw_ints% [3,14]))], [], (rq (raw_ints% [7776,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_25_ok : kpieceAll (header 2 1).toK 5 [headP5_25]=true := by decide +kernel
#print axioms headP5_25_ok
def headP5_26 : QPiece × Cert := (⟨(rq (raw_ints% [2,9])), (rq (raw_ints% [9,40])), (rq (raw_ints% [5,4])), (rq (raw_ints% [4,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [2187,8]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_26_ok : kpieceAll (header 2 1).toK 5 [headP5_26]=true := by decide +kernel
#print axioms headP5_26_ok
def headP5_27 : QPiece × Cert := (⟨(rq (raw_ints% [9,40])), (rq (raw_ints% [1,4])), (rq (raw_ints% [19,8])), (rq (raw_ints% [-1,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨1, [], [], (rq (raw_ints% [800,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_27_ok : kpieceAll (header 2 1).toK 5 [headP5_27]=true := by decide +kernel
#print axioms headP5_27_ok
def headP5_28 : QPiece × Cert := (⟨(rq (raw_ints% [1,4])), (rq (raw_ints% [5,18])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [(rq (raw_ints% [15,56]))], [], (rq (raw_ints% [216,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_28_ok : kpieceAll (header 2 1).toK 5 [headP5_28]=true := by decide +kernel
#print axioms headP5_28_ok
def headP5_29 : QPiece × Cert := (⟨(rq (raw_ints% [5,18])), (rq (raw_ints% [9,32])), (rq (raw_ints% [1,1])), (rq (raw_ints% [4,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [4374,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_29_ok : kpieceAll (header 2 1).toK 5 [headP5_29]=true := by decide +kernel
#print axioms headP5_29_ok
def headP5_30 : QPiece × Cert := (⟨(rq (raw_ints% [9,32])), (rq (raw_ints% [9,28])), (rq (raw_ints% [17,8])), (rq (raw_ints% [0,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨1, [], [], (rq (raw_ints% [512,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_30_ok : kpieceAll (header 2 1).toK 5 [headP5_30]=true := by decide +kernel
#print axioms headP5_30_ok
def headP5_31 : QPiece × Cert := (⟨(rq (raw_ints% [9,28])), (rq (raw_ints% [1,3])), (rq (raw_ints% [13,4])), (rq (raw_ints% [-7,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨8, [], [], (rq (raw_ints% [392,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_31_ok : kpieceAll (header 2 1).toK 5 [headP5_31]=true := by decide +kernel
#print axioms headP5_31_ok
def headP5_32 : QPiece × Cert := (⟨(rq (raw_ints% [1,3])), (rq (raw_ints% [5,14])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [(rq (raw_ints% [15,44]))], [], (rq (raw_ints% [243,2]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_32_ok : kpieceAll (header 2 1).toK 5 [headP5_32]=true := by decide +kernel
#print axioms headP5_32_ok
def headP5_33 : QPiece × Cert := (⟨(rq (raw_ints% [5,14])), (rq (raw_ints% [3,8])), (rq (raw_ints% [1,1])), (rq (raw_ints% [3,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [2646,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_33_ok : kpieceAll (header 2 1).toK 5 [headP5_33]=true := by decide +kernel
#print axioms headP5_33_ok
def headP5_34 : QPiece × Cert := (⟨(rq (raw_ints% [3,8])), (rq (raw_ints% [5,12])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [96,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_34_ok : kpieceAll (header 2 1).toK 5 [headP5_34]=true := by decide +kernel
#print axioms headP5_34_ok
def headP5_35 : QPiece × Cert := (⟨(rq (raw_ints% [5,12])), (rq (raw_ints% [27,64])), (rq (raw_ints% [1,1])), (rq (raw_ints% [8,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [1944,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_35_ok : kpieceAll (header 2 1).toK 5 [headP5_35]=true := by decide +kernel
#print axioms headP5_35_ok
def headP5_36 : QPiece × Cert := (⟨(rq (raw_ints% [27,64])), (rq (raw_ints% [9,20])), (rq (raw_ints% [17,8])), (rq (raw_ints% [0,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨1, [], [], (rq (raw_ints% [2048,27]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_36_ok : kpieceAll (header 2 1).toK 5 [headP5_36]=true := by decide +kernel
#print axioms headP5_36_ok
def headP5_37 : QPiece × Cert := (⟨(rq (raw_ints% [9,20])), (rq (raw_ints% [1,2])), (rq (raw_ints% [13,4])), (rq (raw_ints% [-5,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨8, [(rq (raw_ints% [15,32]))], [], (rq (raw_ints% [200,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_37_ok : kpieceAll (header 2 1).toK 5 [headP5_37]=true := by decide +kernel
#print axioms headP5_37_ok
def headP5_38 : QPiece × Cert := (⟨(rq (raw_ints% [1,2])), (rq (raw_ints% [9,16])), (rq (raw_ints% [1,1])), (rq (raw_ints% [2,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [54,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_38_ok : kpieceAll (header 2 1).toK 5 [headP5_38]=true := by decide +kernel
#print axioms headP5_38_ok
def headP5_39 : QPiece × Cert := (⟨(rq (raw_ints% [9,16])), (rq (raw_ints% [3,5])), (rq (raw_ints% [13,4])), (rq (raw_ints% [-2,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [128,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_39_ok : kpieceAll (header 2 1).toK 5 [headP5_39]=true := by decide +kernel
#print axioms headP5_39_ok
def headP5_40 : QPiece × Cert := (⟨(rq (raw_ints% [3,5])), (rq (raw_ints% [5,8])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [75,2]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_40_ok : kpieceAll (header 2 1).toK 5 [headP5_40]=true := by decide +kernel
#print axioms headP5_40_ok
def headP5_41 : QPiece × Cert := (⟨(rq (raw_ints% [5,8])), (rq (raw_ints% [27,40])), (rq (raw_ints% [1,1])), (rq (raw_ints% [5,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [864,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_41_ok : kpieceAll (header 2 1).toK 5 [headP5_41]=true := by decide +kernel
#print axioms headP5_41_ok
def headP5_42 : QPiece × Cert := (⟨(rq (raw_ints% [27,40])), (rq (raw_ints% [3,4])), (rq (raw_ints% [17,8])), (rq (raw_ints% [0,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨1, [], [], (rq (raw_ints% [800,27]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_42_ok : kpieceAll (header 2 1).toK 5 [headP5_42]=true := by decide +kernel
#print axioms headP5_42_ok
def headP5_43 : QPiece × Cert := (⟨(rq (raw_ints% [3,4])), (rq (raw_ints% [5,6])), (rq (raw_ints% [13,4])), (rq (raw_ints% [-3,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨2, [], [], (rq (raw_ints% [24,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_43_ok : kpieceAll (header 2 1).toK 5 [headP5_43]=true := by decide +kernel
#print axioms headP5_43_ok
def headP5_44 : QPiece × Cert := (⟨(rq (raw_ints% [5,6])), (rq (raw_ints% [5,4])), (rq (raw_ints% [9,2])), (rq (raw_ints% [-3,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨7, [(rq (raw_ints% [1,1]))], [], (rq (raw_ints% [486,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_44_ok : kpieceAll (header 2 1).toK 5 [headP5_44]=true := by decide +kernel
#print axioms headP5_44_ok
def headP5_45 : QPiece × Cert := (⟨(rq (raw_ints% [5,4])), (rq (raw_ints% [3,2])), (rq (raw_ints% [2,1])), (rq (raw_ints% [-1,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨7, [], [], (rq (raw_ints% [44,5]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_45_ok : kpieceAll (header 2 1).toK 5 [headP5_45]=true := by decide +kernel
#print axioms headP5_45_ok
def headP5_46 : QPiece × Cert := (⟨(rq (raw_ints% [3,2])), (rq (raw_ints% [15,8])), (rq (raw_ints% [1,1])), (rq (raw_ints% [-1,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨7, [], [], (rq (raw_ints% [22,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_46_ok : kpieceAll (header 2 1).toK 5 [headP5_46]=true := by decide +kernel
#print axioms headP5_46_ok
def headP5_47 : QPiece × Cert := (⟨(rq (raw_ints% [15,8])), (rq (raw_ints% [2,1])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨3, [], [], (rq (raw_ints% [96,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP5_47_ok : kpieceAll (header 2 1).toK 5 [headP5_47]=true := by decide +kernel
#print axioms headP5_47_ok

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
