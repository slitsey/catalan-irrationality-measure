module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
def headP1_24 : QPiece × Cert := (⟨(rq (raw_ints% [9,40])), (rq (raw_ints% [5,22])), (rq (raw_ints% [7,2])), (rq (raw_ints% [-6,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [800,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_24_ok : kpieceAll (header 2 1).toK 1 [headP1_24]=true := by decide +kernel
#print axioms headP1_24_ok
def headP1_25 : QPiece × Cert := (⟨(rq (raw_ints% [5,22])), (rq (raw_ints% [1,4])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [(rq (raw_ints% [15,64]))], [], (rq (raw_ints% [6534,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_25_ok : kpieceAll (header 2 1).toK 1 [headP1_25]=true := by decide +kernel
#print axioms headP1_25_ok
def headP1_26 : QPiece × Cert := (⟨(rq (raw_ints% [1,4])), (rq (raw_ints% [9,32])), (rq (raw_ints% [17,8])), (rq (raw_ints% [0,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨1, [], [], (rq (raw_ints% [216,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_26_ok : kpieceAll (header 2 1).toK 1 [headP1_26]=true := by decide +kernel
#print axioms headP1_26_ok
def headP1_27 : QPiece × Cert := (⟨(rq (raw_ints% [9,32])), (rq (raw_ints% [2,7])), (rq (raw_ints% [13,4])), (rq (raw_ints% [-4,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [512,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_27_ok : kpieceAll (header 2 1).toK 1 [headP1_27]=true := by decide +kernel
#print axioms headP1_27_ok
def headP1_28 : QPiece × Cert := (⟨(rq (raw_ints% [2,7])), (rq (raw_ints% [5,16])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [(rq (raw_ints% [3,10]))], [], (rq (raw_ints% [1323,8]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_28_ok : kpieceAll (header 2 1).toK 1 [headP1_28]=true := by decide +kernel
#print axioms headP1_28_ok
def headP1_29 : QPiece × Cert := (⟨(rq (raw_ints% [5,16])), (rq (raw_ints% [9,28])), (rq (raw_ints% [1,1])), (rq (raw_ints% [7,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [3456,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_29_ok : kpieceAll (header 2 1).toK 1 [headP1_29]=true := by decide +kernel
#print axioms headP1_29_ok
def headP1_30 : QPiece × Cert := (⟨(rq (raw_ints% [9,28])), (rq (raw_ints% [3,8])), (rq (raw_ints% [17,8])), (rq (raw_ints% [0,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨1, [], [], (rq (raw_ints% [392,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_30_ok : kpieceAll (header 2 1).toK 1 [headP1_30]=true := by decide +kernel
#print axioms headP1_30_ok
def headP1_31 : QPiece × Cert := (⟨(rq (raw_ints% [3,8])), (rq (raw_ints% [2,5])), (rq (raw_ints% [13,4])), (rq (raw_ints% [-3,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [96,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_31_ok : kpieceAll (header 2 1).toK 1 [headP1_31]=true := by decide +kernel
#print axioms headP1_31_ok
def headP1_32 : QPiece × Cert := (⟨(rq (raw_ints% [2,5])), (rq (raw_ints% [5,12])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [675,8]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_32_ok : kpieceAll (header 2 1).toK 1 [headP1_32]=true := by decide +kernel
#print axioms headP1_32_ok
def headP1_33 : QPiece × Cert := (⟨(rq (raw_ints% [5,12])), (rq (raw_ints% [9,20])), (rq (raw_ints% [1,1])), (rq (raw_ints% [5,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [(rq (raw_ints% [3,7]))], [], (rq (raw_ints% [1944,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_33_ok : kpieceAll (header 2 1).toK 1 [headP1_33]=true := by decide +kernel
#print axioms headP1_33_ok
def headP1_34 : QPiece × Cert := (⟨(rq (raw_ints% [9,20])), (rq (raw_ints% [27,56])), (rq (raw_ints% [17,8])), (rq (raw_ints% [0,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨1, [], [], (rq (raw_ints% [200,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_34_ok : kpieceAll (header 2 1).toK 1 [headP1_34]=true := by decide +kernel
#print axioms headP1_34_ok
def headP1_35 : QPiece × Cert := (⟨(rq (raw_ints% [27,56])), (rq (raw_ints% [1,2])), (rq (raw_ints% [13,4])), (rq (raw_ints% [-7,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨8, [], [], (rq (raw_ints% [1568,27]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_35_ok : kpieceAll (header 2 1).toK 1 [headP1_35]=true := by decide +kernel
#print axioms headP1_35_ok
def headP1_36 : QPiece × Cert := (⟨(rq (raw_ints% [1,2])), (rq (raw_ints% [15,28])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [54,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_36_ok : kpieceAll (header 2 1).toK 1 [headP1_36]=true := by decide +kernel
#print axioms headP1_36_ok
def headP1_37 : QPiece × Cert := (⟨(rq (raw_ints% [15,28])), (rq (raw_ints% [9,16])), (rq (raw_ints% [1,1])), (rq (raw_ints% [2,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨21, [], [], (rq (raw_ints% [1176,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_37_ok : kpieceAll (header 2 1).toK 1 [headP1_37]=true := by decide +kernel
#print axioms headP1_37_ok
def headP1_38 : QPiece × Cert := (⟨(rq (raw_ints% [9,16])), (rq (raw_ints% [5,8])), (rq (raw_ints% [13,4])), (rq (raw_ints% [-2,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [128,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_38_ok : kpieceAll (header 2 1).toK 1 [headP1_38]=true := by decide +kernel
#print axioms headP1_38_ok
def headP1_39 : QPiece × Cert := (⟨(rq (raw_ints% [5,8])), (rq (raw_ints% [2,3])), (rq (raw_ints% [2,1])), (rq (raw_ints% [0,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [864,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_39_ok : kpieceAll (header 2 1).toK 1 [headP1_39]=true := by decide +kernel
#print axioms headP1_39_ok
def headP1_40 : QPiece × Cert := (⟨(rq (raw_ints% [2,3])), (rq (raw_ints% [3,4])), (rq (raw_ints% [1,1])), (rq (raw_ints% [3,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨12, [], [], (rq (raw_ints% [243,8]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_40_ok : kpieceAll (header 2 1).toK 1 [headP1_40]=true := by decide +kernel
#print axioms headP1_40_ok
def headP1_41 : QPiece × Cert := (⟨(rq (raw_ints% [3,4])), (rq (raw_ints% [5,6])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-1,6])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨11, [], [], (rq (raw_ints% [24,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_41_ok : kpieceAll (header 2 1).toK 1 [headP1_41]=true := by decide +kernel
#print axioms headP1_41_ok
def headP1_42 : QPiece × Cert := (⟨(rq (raw_ints% [5,6])), (rq (raw_ints% [27,32])), (rq (raw_ints% [1,1])), (rq (raw_ints% [4,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨11, [], [], (rq (raw_ints% [486,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_42_ok : kpieceAll (header 2 1).toK 1 [headP1_42]=true := by decide +kernel
#print axioms headP1_42_ok
def headP1_43 : QPiece × Cert := (⟨(rq (raw_ints% [27,32])), (rq (raw_ints% [15,16])), (rq (raw_ints% [13,4])), (rq (raw_ints% [-4,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨2, [], [], (rq (raw_ints% [512,27]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_43_ok : kpieceAll (header 2 1).toK 1 [headP1_43]=true := by decide +kernel
#print axioms headP1_43_ok
def headP1_44 : QPiece × Cert := (⟨(rq (raw_ints% [15,16])), (rq (raw_ints% [1,1])), (rq (raw_ints% [9,2])), (rq (raw_ints% [-8,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨2, [], [], (rq (raw_ints% [384,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_44_ok : kpieceAll (header 2 1).toK 1 [headP1_44]=true := by decide +kernel
#print axioms headP1_44_ok
def headP1_45 : QPiece × Cert := (⟨(rq (raw_ints% [1,1])), (rq (raw_ints% [5,4])), (rq (raw_ints% [7,2])), (rq (raw_ints% [-5,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨3, [], [], (rq (raw_ints% [27,2]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_45_ok : kpieceAll (header 2 1).toK 1 [headP1_45]=true := by decide +kernel
#print axioms headP1_45_ok
def headP1_46 : QPiece × Cert := (⟨(rq (raw_ints% [5,4])), (rq (raw_ints% [3,1])), (rq (raw_ints% [9,4])), (rq (raw_ints% [-2,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨3, [], [], (rq (raw_ints% [216,25]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_46_ok : kpieceAll (header 2 1).toK 1 [headP1_46]=true := by decide +kernel
#print axioms headP1_46_ok
def headP1_47 : QPiece × Cert := (⟨(rq (raw_ints% [3,1])), (rq (raw_ints% [15,4])), (rq (raw_ints% [5,4])), (rq (raw_ints% [-1,3])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨4, [], [], (rq (raw_ints% [5,1]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headP1_47_ok : kpieceAll (header 2 1).toK 1 [headP1_47]=true := by decide +kernel
#print axioms headP1_47_ok

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
