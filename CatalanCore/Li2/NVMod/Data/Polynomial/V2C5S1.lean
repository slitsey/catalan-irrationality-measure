module
public import CatalanCore.Li2.NVMod.PolynomialCompute
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace CatalanCore.Li2.NVMod.PolynomialData.V2C5S1
open CatalanCore.Li2.NVMod.PolynomialCompute
def m0 : List ℤ := raw_ints% [0x0,0x2,0x1,0x1,0x2,0x4]
def moments : List (List ℤ) := [m0]
def u : List ℤ := raw_ints% [0x1]
def v : List ℤ := raw_ints% [0x1,0x2,0x1]
def k : List ℤ := raw_ints% [0x0,0x1,0x1,0x1,0x1,0x1]
def data : Data := ⟨moments,u,v,k,5,13,0x1⟩
set_option trace.profiler true
set_option trace.profiler.threshold 0
-- kcost: 2 s estimated from measured largest-key whole bound check; checked coefficient/radix bindings
theorem bounds_ok : boundsCheckNat 1 5 data=true := by decide +kernel
-- kcost: 12 s measured largest-key reference; same structural DJ/Horner/Bezout evaluator
theorem arithmetic_ok : arithmeticCheck 1 5 data=true := by decide +kernel
#print axioms bounds_ok
#print axioms arithmetic_ok
end CatalanCore.Li2.NVMod.PolynomialData.V2C5S1
