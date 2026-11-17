module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

public import CatalanCore.Lai.Roots
public import CatalanCore.Lai.ContentBand7
public import CatalanCore.Lai.ContentPrefix
public import CatalanCore.Lai.DecayFinal
public import CatalanCore.Lai.Ratios

public section

/-!
Irrationality measures of the Lai plane `a ζ(3) + b ζ(4)` (`b ≠ 0`, `μ ≤ 34.14`) and of `ζ(3)/π⁴`
(`μ ≤ 55.50`): for all sufficiently large `q` and all integers `p`, `|x - p/q| > q^(-μ)`.
-/

namespace LaiIrrationalityMeasure

open CatalanCore.Lai

theorem lai_inputs : CatalanCore.Lai.LaiInputs :=
  ⟨band7_proof, ⟨_, _, _, _, _, _, DecayFinal.laiDecayData⟩,
    ContentPrefix.Shat, ContentPrefix.hS, ContentPrefix.hR⟩

theorem lai_plane_measure_34_14 (a b : ℤ) (hb : b ≠ 0) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(34.14 : ℝ)) <
        |((a : ℝ) * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) +
          (b : ℝ) * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 4)) - (p : ℝ) / q| :=
  (lai_roots_of lai_inputs).1 a b hb

theorem lai_ratio_measure_55_50 :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(55.50 : ℝ)) <
        |(∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) / Real.pi ^ 4 - (p : ℝ) / q| :=
  (lai_roots_of lai_inputs).2

theorem lai_ratio_mobius_measure_55_50 (a b c d : ℤ) (hdet : a * d - b * c ≠ 0) :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(55.50 : ℝ)) <
        |((a : ℝ) * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) + (b : ℝ) * Real.pi ^ 4) /
            ((c : ℝ) * (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3) + (d : ℝ) * Real.pi ^ 4) - (p : ℝ) / q| :=
  lai_mobius_of lai_inputs a b c d hdet

#print axioms lai_plane_measure_34_14
#print axioms lai_ratio_measure_55_50
#print axioms lai_ratio_mobius_measure_55_50

end LaiIrrationalityMeasure
