module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
def headM1_48 : QPiece × Cert := (⟨(rq (raw_ints% [15,4])), (rq (raw_ints% [9,1])), (rq (raw_ints% [0,1])), (rq (raw_ints% [0,1])), (rq (raw_ints% [1000000000000,1]))⟩, ⟨4, [], [], (rq (raw_ints% [8,3]))⟩)
-- kcost: one full actual Z/PRE/head certificate including strips, root and R; actual24mixed15.669s.
set_option profiler true in
theorem headM1_48_ok : kpieceAll (header 1 5).toK 1 [headM1_48]=true := by decide +kernel
#print axioms headM1_48_ok

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
