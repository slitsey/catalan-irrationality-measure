module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanCore.Li2.NVMod.Data.Prime67
instance primeFact : Fact (Nat.Prime 67) := ⟨by decide +kernel⟩
def inverses : PrimeInverseTable := ⟨[0, 1, 34, 45, 17, 27, 56, 48, 42, 15, 47, 61, 28, 31, 24, 9, 21, 4, 41, 60, 57, 16, 64, 35, 14, 59, 49, 5, 12, 37, 38, 13, 44, 65, 2, 23, 54, 29, 30, 55, 62, 18, 8, 53, 32, 3, 51, 10, 7, 26, 63, 46, 58, 43, 36, 39, 6, 20, 52, 25, 19, 11, 40, 50, 22, 33, 66]⟩
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem inverses_ok : inverseTableCheck 67 inverses=true := by decide +kernel
def interiorResidues : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66]
theorem interiorResidues_eq : interiorResidues=(List.range (67-2)).map (·+2) := by decide +kernel
#print axioms inverses_ok
#print axioms interiorResidues_eq
end CatalanCore.Li2.NVMod.Data.Prime67
