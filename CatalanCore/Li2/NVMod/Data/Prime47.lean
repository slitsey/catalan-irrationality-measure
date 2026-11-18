module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanCore.Li2.NVMod.Data.Prime47
instance primeFact : Fact (Nat.Prime 47) := ⟨by decide +kernel⟩
def inverses : PrimeInverseTable := ⟨[0, 1, 24, 16, 12, 19, 8, 27, 6, 21, 33, 30, 4, 29, 37, 22, 3, 36, 34, 5, 40, 9, 15, 45, 2, 32, 38, 7, 42, 13, 11, 44, 25, 10, 18, 43, 17, 14, 26, 41, 20, 39, 28, 35, 31, 23, 46]⟩
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem inverses_ok : inverseTableCheck 47 inverses=true := by decide +kernel
def interiorResidues : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46]
theorem interiorResidues_eq : interiorResidues=(List.range (47-2)).map (·+2) := by decide +kernel
#print axioms inverses_ok
#print axioms interiorResidues_eq
end CatalanCore.Li2.NVMod.Data.Prime47
