module
public import CatalanCore.Li2.NVMod.Data.Prime11
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace CatalanCore.Li2.NVMod.Data.Numeric.U1C7S4
def row_2 : List ℕ := [1, 6, 2, 9, 7, 5, 6]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_2 : scalarEvalNat 11 Prime11.inverses 4 row_2=some 5 := by decide +kernel
def row_3 : List ℕ := [0, 7, 3, 7, 3, 7, 9]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_3 : scalarEvalNat 11 Prime11.inverses 4 row_3=some 5 := by decide +kernel
def row_4 : List ℕ := [5, 0, 5, 3, 4, 1, 0]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_4 : scalarEvalNat 11 Prime11.inverses 4 row_4=some 9 := by decide +kernel
def row_5 : List ℕ := [3, 5, 10, 0, 10, 0, 3]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_5 : scalarEvalNat 11 Prime11.inverses 4 row_5=some 3 := by decide +kernel
def row_6 : List ℕ := [8, 6, 7, 6, 8, 0, 4]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_6 : scalarEvalNat 11 Prime11.inverses 4 row_6=some 7 := by decide +kernel
def row_7 : List ℕ := [9, 9, 6, 1, 3, 0, 10]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_7 : scalarEvalNat 11 Prime11.inverses 4 row_7=some 3 := by decide +kernel
def row_8 : List ℕ := [2, 10, 1, 0, 2, 1, 10]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_8 : scalarEvalNat 11 Prime11.inverses 4 row_8=some 1 := by decide +kernel
def row_9 : List ℕ := [2, 1, 3, 7, 4, 8, 10]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_9 : scalarEvalNat 11 Prime11.inverses 4 row_9=some 8 := by decide +kernel
def row_10 : List ℕ := [2, 2, 0, 7, 7, 4, 3]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_10 : scalarEvalNat 11 Prime11.inverses 4 row_10=some 1 := by decide +kernel
#print axioms check_2
#print axioms check_10
end CatalanCore.Li2.NVMod.Data.Numeric.U1C7S4
