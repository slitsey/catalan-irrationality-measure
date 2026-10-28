module
public import CatalanMeasure.GenD.Uniform.W.Slots.HLB
public import CatalanMeasure.GenD.Uniform.W.Slots.PFam
public import CatalanMeasure.GenD.Uniform.W.Slots.HPSLB
@[expose] public section
open CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.Parametric

def D58 : Parameters := ⟨58, 9, 3, 5, 3⟩
example : hpVal D58 15 131 8 (-1) 5 = 10 := by decide +kernel
example : hpVal D58 21 163 9 (-1) 6 = 16 := by decide +kernel
example : hpVal D58 18 139 9 (-1) 6 = 7 := by decide +kernel
example : hpVal D58 15 103 10 (-1) 7 = 0 := by decide +kernel
example : perVal D58 15 103 10 (-1) 7 5 = 10 := by decide +kernel
example : perVal D58 21 163 9 (-1) 6 0 = 5 := by decide +kernel
example : perVal D58 18 139 9 (-1) 6 0 = 5 := by decide +kernel
example : hpKap D58 15 131 = 10 := by decide +kernel
example : hpKap D58 21 163 = 16 := by decide +kernel
example : hpVal D58 21 163 9 (-1) 6 + perVal D58 21 163 9 (-1) 6 0 = 21 := by decide +kernel
example : hpVal D58 18 139 9 (-1) 6 + perVal D58 18 139 9 (-1) 6 0 = 12 := by decide +kernel
