module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanCore.Li2.NVMod.Data.Prime83
instance primeFact : Fact (Nat.Prime 83) := ⟨by decide +kernel⟩
def inverses : PrimeInverseTable := ⟨[0, 1, 42, 28, 21, 50, 14, 12, 52, 37, 25, 68, 7, 32, 6, 72, 26, 44, 60, 35, 54, 4, 34, 65, 45, 10, 16, 40, 3, 63, 36, 75, 13, 78, 22, 19, 30, 9, 59, 66, 27, 81, 2, 56, 17, 24, 74, 53, 64, 61, 5, 70, 8, 47, 20, 80, 43, 67, 73, 38, 18, 49, 79, 29, 48, 23, 39, 57, 11, 77, 51, 76, 15, 58, 46, 31, 71, 69, 33, 62, 55, 41, 82]⟩
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem inverses_ok : inverseTableCheck 83 inverses=true := by decide +kernel
def interiorResidues : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82]
theorem interiorResidues_eq : interiorResidues=(List.range (83-2)).map (·+2) := by decide +kernel
#print axioms inverses_ok
#print axioms interiorResidues_eq
end CatalanCore.Li2.NVMod.Data.Prime83
