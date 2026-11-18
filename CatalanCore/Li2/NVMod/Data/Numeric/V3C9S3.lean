module
public import CatalanCore.Li2.NVMod.Data.Prime13
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace CatalanCore.Li2.NVMod.Data.Numeric.V3C9S3
def row_2 : List ℕ := [0, 9, 1, 4, 10]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_2 : scalarEvalNat 13 Prime13.inverses 3 row_2=some 2 := by decide +kernel
def row_3 : List ℕ := [9, 6, 7, 12, 3]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_3 : scalarEvalNat 13 Prime13.inverses 3 row_3=some 9 := by decide +kernel
def row_4 : List ℕ := [4, 9, 7, 4, 3]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_4 : scalarEvalNat 13 Prime13.inverses 3 row_4=some 3 := by decide +kernel
def row_5 : List ℕ := [4, 4, 5, 9, 11]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_5 : scalarEvalNat 13 Prime13.inverses 3 row_5=some 7 := by decide +kernel
def row_6 : List ℕ := [0, 12, 7, 2, 12]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_6 : scalarEvalNat 13 Prime13.inverses 3 row_6=some 7 := by decide +kernel
def row_7 : List ℕ := [5, 2, 9, 12, 1]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_7 : scalarEvalNat 13 Prime13.inverses 3 row_7=some 12 := by decide +kernel
def row_8 : List ℕ := [8, 10, 10, 1, 4]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_8 : scalarEvalNat 13 Prime13.inverses 3 row_8=some 9 := by decide +kernel
def row_9 : List ℕ := [9, 0, 2, 11, 9]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_9 : scalarEvalNat 13 Prime13.inverses 3 row_9=some 1 := by decide +kernel
def row_10 : List ℕ := [9, 12, 0, 8, 6]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_10 : scalarEvalNat 13 Prime13.inverses 3 row_10=some 3 := by decide +kernel
def row_11 : List ℕ := [10, 9, 0, 10, 5]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_11 : scalarEvalNat 13 Prime13.inverses 3 row_11=some 12 := by decide +kernel
def row_12 : List ℕ := [4, 0, 12, 9, 8]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_12 : scalarEvalNat 13 Prime13.inverses 3 row_12=some 9 := by decide +kernel
#print axioms check_2
#print axioms check_12
end CatalanCore.Li2.NVMod.Data.Numeric.V3C9S3
