module

public import CatalanArchive.CatalanMeasure.GenD.P20.Main
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Statement check: the wrapper has exactly the statement of `Challenge.lean`. -/

example : ∀ᶠ b : ℕ in Filter.atTop, ∀ a : ℤ,
    (b : ℝ) ^ (-(728 : ℝ)) <
      |(∑' j : ℕ, (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) - a / b| :=
  CatalanMeasure.G728.catalan_irrationalityMeasure_728
