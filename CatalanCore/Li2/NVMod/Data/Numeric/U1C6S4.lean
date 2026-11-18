module
public import CatalanCore.Li2.NVMod.Data.Prime11
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace CatalanCore.Li2.NVMod.Data.Numeric.U1C6S4
def row_2 : List ℕ := [2, 0, 1, 4, 10, 8, 3]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_2 : scalarEvalNat 11 Prime11.inverses 4 row_2=some 10 := by decide +kernel
def row_3 : List ℕ := [7, 8, 6, 8, 6, 3, 10]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_3 : scalarEvalNat 11 Prime11.inverses 4 row_3=some 9 := by decide +kernel
def row_4 : List ℕ := [2, 5, 5, 3, 7, 7, 1]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_4 : scalarEvalNat 11 Prime11.inverses 4 row_4=some 10 := by decide +kernel
def row_5 : List ℕ := [4, 1, 4, 10, 4, 3, 8]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_5 : scalarEvalNat 11 Prime11.inverses 4 row_5=some 2 := by decide +kernel
def row_6 : List ℕ := [7, 5, 0, 6, 1, 4, 1]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_6 : scalarEvalNat 11 Prime11.inverses 4 row_6=some 5 := by decide +kernel
def row_7 : List ℕ := [6, 3, 10, 10, 10, 10, 7]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_7 : scalarEvalNat 11 Prime11.inverses 4 row_7=some 7 := by decide +kernel
def row_8 : List ℕ := [2, 5, 7, 2, 4, 6, 9]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_8 : scalarEvalNat 11 Prime11.inverses 4 row_8=some 9 := by decide +kernel
def row_9 : List ℕ := [4, 10, 6, 9, 3, 0, 8]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_9 : scalarEvalNat 11 Prime11.inverses 4 row_9=some 7 := by decide +kernel
def row_10 : List ℕ := [5, 3, 7, 1, 9, 9, 4]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_10 : scalarEvalNat 11 Prime11.inverses 4 row_10=some 6 := by decide +kernel
#print axioms check_2
#print axioms check_10
end CatalanCore.Li2.NVMod.Data.Numeric.U1C6S4
