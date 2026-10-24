module

public import CatalanArchive.CatalanMeasure.Parametric.TwentyGroupedPhysicalFields
public import CatalanArchive.CatalanMeasure.Parametric.TwentyPhysicalConstants

@[expose] public section

namespace CatalanMeasure.Parametric

open OAI.InternalCatalan

noncomputable section

theorem twenty_grouped_constant_relation {N r a b : ℕ} (hN : 0 < N)
    (hcount : r + a + b = twenty.n N) :
    groupedPhysicalConstant twenty N r a b = populationPhysicalConstant twenty N r -
      (2 / 5 : ℝ) * (((a + b : ℕ) : ℝ) / (twenty.n N : ℝ)) * Real.log 2 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hC1 : 1 ≤ twenty.C N := by rw [twenty_C]; omega
  have hM : twenty.n N - twenty.g N - 1 = 18 * N - 1 := by
    change 20 * N - 2 * N - 1 = 18 * N - 1
    omega
  have hr : (r : ℝ) = 20 * N - a - b := by
    have hc : (r : ℝ) + a + b = 20 * N := by exact_mod_cast hcount
    linarith only [hc]
  unfold groupedPhysicalConstant populationPhysicalConstant
  rw [hM, twenty_C]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_choose_two, Nat.cast_sub (by omega : 1 ≤ 18 * N),
    Nat.cast_sub (by omega : 1 ≤ 26 * N), Parameters.n, twenty]
  push_cast
  rw [hr]
  field_simp
  ring

theorem twenty_grouped_constant_le {N r a b : ℕ} (hN : 0 < N)
    (hcount : r + a + b = twenty.n N) :
    groupedPhysicalConstant twenty N r a b -
        (1 / 2 : ℝ) * ((((r + a : ℕ) : ℝ) / (twenty.n N : ℝ)) ^ 2 +
          ((b : ℝ) / (twenty.n N : ℝ)) ^ 2) * Real.log 2 -
        (3 / 2 : ℝ) * ((r : ℝ) / (twenty.n N : ℝ)) ^ 2 * Real.log 2 ≤
      (-(1 / 5 : ℝ) + (8 / 5) * (((a + b : ℕ) : ℝ) / (twenty.n N : ℝ)) -
        (((a + b : ℕ) : ℝ) / (twenty.n N : ℝ)) ^ 2 +
        (b : ℝ) / (twenty.n N : ℝ) - ((b : ℝ) / (twenty.n N : ℝ)) ^ 2) * Real.log 2 := by
  have hpm : r + (a + b) = twenty.n N := by omega
  have hc := twenty_physical_two_constant_le hN hpm
  have hn : (twenty.n N : ℝ) ≠ 0 := by exact_mod_cast (n_pos twenty_admissible hN).ne'
  have hfra : ((r + a : ℕ) : ℝ) / (twenty.n N : ℝ) =
      1 - (b : ℝ) / (twenty.n N : ℝ) := by
    have ht : ((r + a : ℕ) : ℝ) + b = (twenty.n N : ℝ) := by exact_mod_cast hcount
    apply (div_eq_iff hn).mpr
    field_simp
    linarith only [ht]
  rw [twenty_grouped_constant_relation hN hcount, hfra]
  nlinarith only [hc]

end

end CatalanMeasure.Parametric
