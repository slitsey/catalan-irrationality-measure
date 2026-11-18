module
public import CatalanCore.Li2.NVMod.Data.Prime5
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace CatalanCore.Li2.NVMod.Data.Numeric.U0C3S3
def row_2 : List ℕ := [1, 0, 3, 4, 2]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_2 : scalarEvalNat 5 Prime5.inverses 3 row_2=some 3 := by decide +kernel
def row_3 : List ℕ := [0, 1, 4, 1, 3]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_3 : scalarEvalNat 5 Prime5.inverses 3 row_3=some 1 := by decide +kernel
def row_4 : List ℕ := [4, 3, 0, 0, 4]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_4 : scalarEvalNat 5 Prime5.inverses 3 row_4=some 4 := by decide +kernel
#print axioms check_2
#print axioms check_4
end CatalanCore.Li2.NVMod.Data.Numeric.U0C3S3
