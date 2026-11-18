module
public import CatalanCore.Li2.NVMod.ResBase
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
namespace CatalanCore.Li2.NVMod.Data.Prime13
instance primeFact : Fact (Nat.Prime 13) := ⟨by decide +kernel⟩
def inverses : PrimeInverseTable := ⟨[0, 1, 7, 9, 10, 8, 11, 2, 5, 3, 4, 6, 12]⟩
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem inverses_ok : inverseTableCheck 13 inverses=true := by decide +kernel
def interiorResidues : List ℕ := [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
theorem interiorResidues_eq : interiorResidues=(List.range (13-2)).map (·+2) := by decide +kernel
#print axioms inverses_ok
#print axioms interiorResidues_eq
end CatalanCore.Li2.NVMod.Data.Prime13
