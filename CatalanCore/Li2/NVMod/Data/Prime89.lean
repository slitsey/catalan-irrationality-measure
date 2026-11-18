module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanCore.Li2.NVMod.Data.Prime89
instance primeFact : Fact (Nat.Prime 89) := ⟨by decide +kernel⟩
def inverses : PrimeInverseTable := ⟨[0, 1, 45, 30, 67, 18, 15, 51, 78, 10, 9, 81, 52, 48, 70, 6, 39, 21, 5, 75, 49, 17, 85, 31, 26, 57, 24, 33, 35, 43, 3, 23, 64, 27, 55, 28, 47, 77, 82, 16, 69, 76, 53, 29, 87, 2, 60, 36, 13, 20, 73, 7, 12, 42, 61, 34, 62, 25, 66, 86, 46, 54, 56, 65, 32, 63, 58, 4, 72, 40, 14, 84, 68, 50, 83, 19, 41, 37, 8, 80, 79, 11, 38, 74, 71, 22, 59, 44, 88]⟩
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem inverses_ok : inverseTableCheck 89 inverses=true := by decide +kernel
def interiorResidues : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88]
theorem interiorResidues_eq : interiorResidues=(List.range (89-2)).map (·+2) := by decide +kernel
#print axioms inverses_ok
#print axioms interiorResidues_eq
end CatalanCore.Li2.NVMod.Data.Prime89
