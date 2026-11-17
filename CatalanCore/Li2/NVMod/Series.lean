module

public import CatalanCore.Li2.NVMod.Definitions
public import Mathlib.RingTheory.HahnSeries.PowerSeries
public import Mathlib.RingTheory.HahnSeries.Summable

@[expose] public section

namespace CatalanCore.Li2.NVMod

noncomputable section

def hX {F : Type*} [Field F] : HahnSeries ℤ F := HahnSeries.single 1 1

def expandRF {F : Type*} [Field F] [Algebra ℚ F]
    (f : RatFunc ℚ) (Y : HahnSeries ℤ F) : HahnSeries ℤ F :=
  f.num.eval₂ (algebraMap ℚ (HahnSeries ℤ F)) Y /
    f.denom.eval₂ (algebraMap ℚ (HahnSeries ℤ F)) Y

def atZero (f : RatFunc ℚ) : HahnSeries ℤ ℚ := expandRF f hX

def atOne (f : RatFunc ℚ) : HahnSeries ℤ ℚ := expandRF f (1-hX)

def atInf (f : RatFunc ℚ) : HahnSeries ℤ ℚ := expandRF f hX⁻¹

def Oge {F : Type*} [Zero F] (f : HahnSeries ℤ F) (e : ℤ) : Prop :=
  ∀ j : ℤ, j < e → f.coeff j = 0

end
end CatalanCore.Li2.NVMod
