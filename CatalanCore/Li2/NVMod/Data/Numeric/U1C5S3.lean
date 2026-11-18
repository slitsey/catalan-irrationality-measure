module
public import CatalanCore.Li2.NVMod.Data.Prime13
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace CatalanCore.Li2.NVMod.Data.Numeric.U1C5S3
def row_2 : List ℕ := [2, 8, 3, 10, 9]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_2 : scalarEvalNat 13 Prime13.inverses 3 row_2=some 4 := by decide +kernel
def row_3 : List ℕ := [2, 8, 6, 0, 10]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_3 : scalarEvalNat 13 Prime13.inverses 3 row_3=some 5 := by decide +kernel
def row_4 : List ℕ := [1, 3, 12, 3, 10]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_4 : scalarEvalNat 13 Prime13.inverses 3 row_4=some 4 := by decide +kernel
def row_5 : List ℕ := [0, 7, 3, 1, 7]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_5 : scalarEvalNat 13 Prime13.inverses 3 row_5=some 10 := by decide +kernel
def row_6 : List ℕ := [11, 9, 12, 6, 11]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_6 : scalarEvalNat 13 Prime13.inverses 3 row_6=some 6 := by decide +kernel
def row_7 : List ℕ := [6, 6, 10, 11, 2]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_7 : scalarEvalNat 13 Prime13.inverses 3 row_7=some 6 := by decide +kernel
def row_8 : List ℕ := [8, 4, 5, 8, 7]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_8 : scalarEvalNat 13 Prime13.inverses 3 row_8=some 7 := by decide +kernel
def row_9 : List ℕ := [2, 1, 7, 4, 10]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_9 : scalarEvalNat 13 Prime13.inverses 3 row_9=some 6 := by decide +kernel
def row_10 : List ℕ := [1, 10, 7, 6, 8]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_10 : scalarEvalNat 13 Prime13.inverses 3 row_10=some 3 := by decide +kernel
def row_11 : List ℕ := [10, 5, 9, 1, 6]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_11 : scalarEvalNat 13 Prime13.inverses 3 row_11=some 1 := by decide +kernel
def row_12 : List ℕ := [2, 3, 5, 5, 9]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_12 : scalarEvalNat 13 Prime13.inverses 3 row_12=some 10 := by decide +kernel
#print axioms check_2
#print axioms check_12
end CatalanCore.Li2.NVMod.Data.Numeric.U1C5S3
