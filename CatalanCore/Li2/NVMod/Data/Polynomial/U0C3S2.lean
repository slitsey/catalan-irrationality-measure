module
public import CatalanCore.Li2.NVMod.PolynomialCompute
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CatalanCore.Li2.NVMod.PolynomialData.U0C3S2
open CatalanCore.Li2.NVMod.PolynomialCompute
def m0 : List ℤ := raw_ints% [0x0,0x2,0x3,0x1,0x1,0x3]
def m1 : List ℤ := raw_ints% [0x0,0x4,0x0,0x3,0x3]
def m2 : List ℤ := raw_ints% [0x0,0x3,0x2,0x2,0x3]
def moments : List (List ℤ) := [m0,m1,m2]
def u : List ℤ := raw_ints% [0x2,0x2,0x4]
def v : List ℤ := raw_ints% [0x1,0x4,0x0,0x4,0x3,0x2,0x3,0x3,0x4]
def k : List ℤ := raw_ints% [0x0,0x1,-0x3,0x3,-0x5,0x5,-0x4,-0x1,0xa,0x0,0x5,0x8]
def data : Data := ⟨moments,u,v,k,5,19,0xa⟩
set_option trace.profiler true
set_option trace.profiler.threshold 0
-- kcost: 2 s estimated from measured largest-key whole bound check; checked coefficient/radix bindings
theorem bounds_ok : boundsCheckNat 2 5 data=true := by decide +kernel
-- kcost: 12 s measured largest-key reference; same structural DJ/Horner/Bezout evaluator
theorem arithmetic_ok : arithmeticCheck 2 5 data=true := by decide +kernel
#print axioms bounds_ok
#print axioms arithmetic_ok
end CatalanCore.Li2.NVMod.PolynomialData.U0C3S2
