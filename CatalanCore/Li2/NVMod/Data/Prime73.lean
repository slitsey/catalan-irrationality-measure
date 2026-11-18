module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanCore.Li2.NVMod.Data.Prime73
instance primeFact : Fact (Nat.Prime 73) := ⟨by decide +kernel⟩
def inverses : PrimeInverseTable := ⟨[0, 1, 37, 49, 55, 44, 61, 21, 64, 65, 22, 20, 67, 45, 47, 39, 32, 43, 69, 50, 11, 7, 10, 54, 70, 38, 59, 46, 60, 68, 56, 33, 16, 31, 58, 48, 71, 2, 25, 15, 42, 57, 40, 17, 5, 13, 27, 14, 35, 3, 19, 63, 66, 62, 23, 4, 30, 41, 34, 26, 28, 6, 53, 51, 8, 9, 52, 12, 29, 18, 24, 36, 72]⟩
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem inverses_ok : inverseTableCheck 73 inverses=true := by decide +kernel
def interiorResidues : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72]
theorem interiorResidues_eq : interiorResidues=(List.range (73-2)).map (·+2) := by decide +kernel
#print axioms inverses_ok
#print axioms interiorResidues_eq
end CatalanCore.Li2.NVMod.Data.Prime73
