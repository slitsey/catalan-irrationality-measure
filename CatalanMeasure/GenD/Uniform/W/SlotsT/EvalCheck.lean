module
public import CatalanMeasure.GenD.Uniform.W.SlotsT.Combine
public import CatalanMeasure.GenD.Uniform.W.SlotsT.GlueVal
@[expose] public section
open CatalanMeasure.GenD.Uniform.W.SlotsT CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.Parametric CatalanMeasure.GenD.Uniform.W.Thin

def D58 : Parameters := ⟨58, 9, 3, 5, 3⟩
instance : Fact (Nat.Prime 131) := ⟨by decide +kernel⟩
instance : Fact (Nat.Prime 157) := ⟨by decide +kernel⟩

-- N = 30, p = 131 (H/p = 17.86): window s = 17, blocks -1..12 (K = 14), 19 offsets
example : mtOK D58 30 131 17 19 0 := by decide +kernel
example : (mtJJ D58 30 131 17 19 0).card = 14 := by decide +kernel
example : virtCount D58 30 131 14 19 (-1) = 2 := by decide +kernel
example : tpVirt D58 30 131 14 20 (-1) = 2 := by decide +kernel
example : mtVal D58 30 131 17 14 (-1) 19 0 = 18 := by decide +kernel

example : mixMiss D58 30 131 14 19 (-1) = 2 := by decide +kernel
-- the proof4 closed form: 19 + 20 - 2 - 17 = 20 = the exact nullity of D58 N = 30, p = 131
example : mtVal2 D58 30 131 17 14 19 0 (-1) = 20 := by decide +kernel
instance : Fact (Nat.Prime 157) := ⟨by decide +kernel⟩
instance : Fact (Nat.Prime 109) := ⟨by decide +kernel⟩
instance : Fact (Nat.Prime 149) := ⟨by decide +kernel⟩
instance : Fact (Nat.Prime 193) := ⟨by decide +kernel⟩
instance : Fact (Nat.Prime 101) := ⟨by decide +kernel⟩
instance : Fact (Nat.Prime 127) := ⟨by decide +kernel⟩

-- proof4 table (N, p) -> exact nullity = closed form (thmMT.py: countMT)
example : mtVal2 D58 36 157 17 14 23 0 (-1) = 27 := by decide +kernel
example : mtVal2 D58 25 109 17 14 16 0 (-1) = 19 := by decide +kernel
example : mtMinusVal D58 32 149 16 13 (-1) 11 0 = 11 := by decide +kernel
example : mtMinusVal D58 42 193 16 13 (-1) 17 3 = 14 := by decide +kernel
example : mtMinusVal D58 22 101 16 13 (-1) 9 3 = 6 := by decide +kernel
example : mtMinusVal D58 29 127 17 14 (-1) 12 0 = 12 := by decide +kernel

-- Theorem MT (b), m = 1: proof4 thmMT2 countMTo(kind = 'b') = 20, 3, 2
instance : Fact (Nat.Prime 151) := ⟨by decide +kernel⟩
instance : Fact (Nat.Prime 61) := ⟨by decide +kernel⟩
instance : Fact (Nat.Prime 73) := ⟨by decide +kernel⟩
example : mtGlueVal1 D58 35 151 17 14 24 0 (-1) = 20 := by decide +kernel
example : mtGlueVal1 D58 15 61 18 15 14 0 (-1) = 3 := by decide +kernel
example : mtGlueVal1 D58 18 73 18 15 17 1 (-1) = 2 := by decide +kernel
