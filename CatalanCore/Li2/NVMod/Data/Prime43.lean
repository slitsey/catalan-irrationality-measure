module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanCore.Li2.NVMod.Data.Prime43
instance primeFact : Fact (Nat.Prime 43) := ⟨by decide +kernel⟩
def inverses : PrimeInverseTable := ⟨[0, 1, 22, 29, 11, 26, 36, 37, 27, 24, 13, 4, 18, 10, 40, 23, 35, 38, 12, 34, 28, 41, 2, 15, 9, 31, 5, 8, 20, 3, 33, 25, 39, 30, 19, 16, 6, 7, 17, 32, 14, 21, 42]⟩
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem inverses_ok : inverseTableCheck 43 inverses=true := by decide +kernel
def interiorResidues : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42]
theorem interiorResidues_eq : interiorResidues=(List.range (43-2)).map (·+2) := by decide +kernel
#print axioms inverses_ok
#print axioms interiorResidues_eq
end CatalanCore.Li2.NVMod.Data.Prime43
