module
public import CatalanCore.Li2.NVMod.Data.Prime7
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace CatalanCore.Li2.NVMod.Data.Numeric.V2C5S2
def row_2 : List ℕ := [4, 4, 5]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_2 : scalarEvalNat 7 Prime7.inverses 2 row_2=some 4 := by decide +kernel
def row_3 : List ℕ := [4, 0, 2]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_3 : scalarEvalNat 7 Prime7.inverses 2 row_3=some 1 := by decide +kernel
def row_4 : List ℕ := [4, 3, 1]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_4 : scalarEvalNat 7 Prime7.inverses 2 row_4=some 2 := by decide +kernel
def row_5 : List ℕ := [5, 2, 0]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_5 : scalarEvalNat 7 Prime7.inverses 2 row_5=some 3 := by decide +kernel
def row_6 : List ℕ := [4, 0, 1]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_6 : scalarEvalNat 7 Prime7.inverses 2 row_6=some 4 := by decide +kernel
#print axioms check_2
#print axioms check_6
end CatalanCore.Li2.NVMod.Data.Numeric.V2C5S2
