module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
def headM5_48 : QPiece × Cert := (⟨(rq (raw_ints% [2,1])), (rq (raw_ints% [5,2])), (rq (raw_ints% [5,4])), (rq (raw_ints% [-1,2])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨4, [], [], (rq (raw_ints% [27,8]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_48_ok : kpieceAll (header 1 5).toK 5 [headM5_48]=true := by decide +kernel
#print axioms headM5_48_ok
def headM5_49 : QPiece × Cert := (⟨(rq (raw_ints% [5,2])), (rq (raw_ints% [9,1])), (rq (raw_ints% [0,1])), (rq (raw_ints% [0,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨4, [], [], (rq (raw_ints% [12,5]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM5_49_ok : kpieceAll (header 1 5).toK 5 [headM5_49]=true := by decide +kernel
#print axioms headM5_49_ok

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
