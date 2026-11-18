module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanCore.Li2.NVMod.Data.Prime37
instance primeFact : Fact (Nat.Prime 37) := ⟨by decide +kernel⟩
def inverses : PrimeInverseTable := ⟨[0, 1, 19, 25, 28, 15, 31, 16, 14, 33, 26, 27, 34, 20, 8, 5, 7, 24, 35, 2, 13, 30, 32, 29, 17, 3, 10, 11, 4, 23, 21, 6, 22, 9, 12, 18, 36]⟩
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem inverses_ok : inverseTableCheck 37 inverses=true := by decide +kernel
def interiorResidues : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36]
theorem interiorResidues_eq : interiorResidues=(List.range (37-2)).map (·+2) := by decide +kernel
#print axioms inverses_ok
#print axioms interiorResidues_eq
end CatalanCore.Li2.NVMod.Data.Prime37
