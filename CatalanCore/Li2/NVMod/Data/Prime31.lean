module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanCore.Li2.NVMod.Data.Prime31
instance primeFact : Fact (Nat.Prime 31) := ⟨by decide +kernel⟩
def inverses : PrimeInverseTable := ⟨[0, 1, 16, 21, 8, 25, 26, 9, 4, 7, 28, 17, 13, 12, 20, 29, 2, 11, 19, 18, 14, 3, 24, 27, 22, 5, 6, 23, 10, 15, 30]⟩
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem inverses_ok : inverseTableCheck 31 inverses=true := by decide +kernel
def interiorResidues : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]
theorem interiorResidues_eq : interiorResidues=(List.range (31-2)).map (·+2) := by decide +kernel
#print axioms inverses_ok
#print axioms interiorResidues_eq
end CatalanCore.Li2.NVMod.Data.Prime31
