module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanCore.Li2.NVMod.Data.Prime59
instance primeFact : Fact (Nat.Prime 59) := ⟨by decide +kernel⟩
def inverses : PrimeInverseTable := ⟨[0, 1, 30, 20, 15, 12, 10, 17, 37, 46, 6, 43, 5, 50, 38, 4, 48, 7, 23, 28, 3, 45, 51, 18, 32, 26, 25, 35, 19, 57, 2, 40, 24, 34, 33, 27, 41, 8, 14, 56, 31, 36, 52, 11, 55, 21, 9, 54, 16, 53, 13, 22, 42, 49, 47, 44, 39, 29, 58]⟩
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem inverses_ok : inverseTableCheck 59 inverses=true := by decide +kernel
def interiorResidues : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]
theorem interiorResidues_eq : interiorResidues=(List.range (59-2)).map (·+2) := by decide +kernel
#print axioms inverses_ok
#print axioms interiorResidues_eq
end CatalanCore.Li2.NVMod.Data.Prime59
