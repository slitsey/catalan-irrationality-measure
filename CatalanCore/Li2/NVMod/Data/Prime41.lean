module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanCore.Li2.NVMod.Data.Prime41
instance primeFact : Fact (Nat.Prime 41) := ⟨by decide +kernel⟩
def inverses : PrimeInverseTable := ⟨[0, 1, 21, 14, 31, 33, 7, 6, 36, 32, 37, 15, 24, 19, 3, 11, 18, 29, 16, 13, 39, 2, 28, 25, 12, 23, 30, 38, 22, 17, 26, 4, 9, 5, 35, 34, 8, 10, 27, 20, 40]⟩
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem inverses_ok : inverseTableCheck 41 inverses=true := by decide +kernel
def interiorResidues : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40]
theorem interiorResidues_eq : interiorResidues=(List.range (41-2)).map (·+2) := by decide +kernel
#print axioms inverses_ok
#print axioms interiorResidues_eq
end CatalanCore.Li2.NVMod.Data.Prime41
