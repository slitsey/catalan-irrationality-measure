module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanCore.Li2.NVMod.Data.Prime53
instance primeFact : Fact (Nat.Prime 53) := ⟨by decide +kernel⟩
def inverses : PrimeInverseTable := ⟨[0, 1, 27, 18, 40, 32, 9, 38, 20, 6, 16, 29, 31, 49, 19, 46, 10, 25, 3, 14, 8, 48, 41, 30, 42, 17, 51, 2, 36, 11, 23, 12, 5, 45, 39, 50, 28, 43, 7, 34, 4, 22, 24, 37, 47, 33, 15, 44, 21, 13, 35, 26, 52]⟩
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem inverses_ok : inverseTableCheck 53 inverses=true := by decide +kernel
def interiorResidues : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52]
theorem interiorResidues_eq : interiorResidues=(List.range (53-2)).map (·+2) := by decide +kernel
#print axioms inverses_ok
#print axioms interiorResidues_eq
end CatalanCore.Li2.NVMod.Data.Prime53
