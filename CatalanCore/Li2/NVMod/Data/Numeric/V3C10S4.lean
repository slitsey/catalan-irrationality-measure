module
public import CatalanCore.Li2.NVMod.Data.Prime11
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
namespace CatalanCore.Li2.NVMod.Data.Numeric.V3C10S4
def row_2 : List ℕ := [0, 0, 1, 0, 10, 9, 10]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_2 : scalarEvalNat 11 Prime11.inverses 4 row_2=some 2 := by decide +kernel
def row_3 : List ℕ := [7, 2, 6, 8, 4, 4, 9]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_3 : scalarEvalNat 11 Prime11.inverses 4 row_3=some 10 := by decide +kernel
def row_4 : List ℕ := [6, 2, 1, 6, 3, 2, 1]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_4 : scalarEvalNat 11 Prime11.inverses 4 row_4=some 5 := by decide +kernel
def row_5 : List ℕ := [7, 0, 7, 10, 10, 9, 3]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_5 : scalarEvalNat 11 Prime11.inverses 4 row_5=some 8 := by decide +kernel
def row_6 : List ℕ := [6, 8, 4, 5, 6, 6, 7]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_6 : scalarEvalNat 11 Prime11.inverses 4 row_6=some 2 := by decide +kernel
def row_7 : List ℕ := [0, 6, 7, 0, 1, 4, 2]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_7 : scalarEvalNat 11 Prime11.inverses 4 row_7=some 4 := by decide +kernel
def row_8 : List ℕ := [8, 6, 10, 2, 1, 9, 0]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_8 : scalarEvalNat 11 Prime11.inverses 4 row_8=some 1 := by decide +kernel
def row_9 : List ℕ := [2, 3, 5, 4, 9, 4, 0]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_9 : scalarEvalNat 11 Prime11.inverses 4 row_9=some 8 := by decide +kernel
def row_10 : List ℕ := [4, 10, 3, 8, 2, 1, 5]
set_option trace.profiler.threshold 0 in
set_option trace.profiler true in
theorem check_10 : scalarEvalNat 11 Prime11.inverses 4 row_10=some 2 := by decide +kernel
#print axioms check_2
#print axioms check_10
end CatalanCore.Li2.NVMod.Data.Numeric.V3C10S4
