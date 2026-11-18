module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanCore.Li2.NVMod.Data.Prime61
instance primeFact : Fact (Nat.Prime 61) := ⟨by decide +kernel⟩
def inverses : PrimeInverseTable := ⟨[0, 1, 31, 41, 46, 49, 51, 35, 23, 34, 55, 50, 56, 47, 48, 57, 42, 18, 17, 45, 58, 32, 25, 8, 28, 22, 54, 52, 24, 40, 59, 2, 21, 37, 9, 7, 39, 33, 53, 36, 29, 3, 16, 44, 43, 19, 4, 13, 14, 5, 11, 6, 27, 38, 26, 10, 12, 15, 20, 30, 60]⟩
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem inverses_ok : inverseTableCheck 61 inverses=true := by decide +kernel
def interiorResidues : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60]
theorem interiorResidues_eq : interiorResidues=(List.range (61-2)).map (·+2) := by decide +kernel
#print axioms inverses_ok
#print axioms interiorResidues_eq
end CatalanCore.Li2.NVMod.Data.Prime61
