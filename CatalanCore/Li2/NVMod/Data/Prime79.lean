module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanCore.Li2.NVMod.Data.Prime79
instance primeFact : Fact (Nat.Prime 79) := ⟨by decide +kernel⟩
def inverses : PrimeInverseTable := ⟨[0, 1, 40, 53, 20, 16, 66, 34, 10, 44, 8, 36, 33, 73, 17, 58, 5, 14, 22, 25, 4, 64, 18, 55, 56, 19, 76, 41, 48, 30, 29, 51, 42, 12, 7, 70, 11, 47, 52, 77, 2, 27, 32, 68, 9, 72, 67, 37, 28, 50, 49, 31, 38, 3, 60, 23, 24, 61, 15, 75, 54, 57, 65, 74, 21, 62, 6, 46, 43, 71, 35, 69, 45, 13, 63, 59, 26, 39, 78]⟩
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem inverses_ok : inverseTableCheck 79 inverses=true := by decide +kernel
def interiorResidues : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78]
theorem interiorResidues_eq : interiorResidues=(List.range (79-2)).map (·+2) := by decide +kernel
#print axioms inverses_ok
#print axioms interiorResidues_eq
end CatalanCore.Li2.NVMod.Data.Prime79
