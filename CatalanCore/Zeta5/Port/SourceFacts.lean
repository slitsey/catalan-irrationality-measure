module

public import CatalanCore.Zeta5.Port.Degree
public import CatalanCore.Zeta5.Port.Positivity

@[expose] public section

/-!
# Positivity of `F_K(ζ(5))` (ledger ZA09) and the degree bound (ZA05)

New file (not in mo271/Zeta5): the two statements below are assembled from the ported
`S_pos`, `natDegree_Δ`, `natDegree_F` (`Degree`) and `Δ_pos` (`Positivity`).
-/

open Polynomial

namespace Apery

/-- **ZA05.** Every entry of `G_K(X)` is affine in `X`, so `deg_X Δ_K ≤ h = 37 n`. (Here the exact
degree `natDegree_Δ` is also available.) -/
theorem natDegree_Δ_le (n : ℕ) : (Δ n).natDegree ≤ 37 * n :=
  (natDegree_Δ n).le

/-- **ZA09.** `F_K(ζ(5)) = S_K Δ_K(ζ(5)) > 0`. -/
theorem F_pos (n : ℕ) (hn : 0 < n) : 0 < aeval zeta5 (F n) := by
  unfold F
  rw [map_mul, aeval_C]
  have hS : (0 : ℝ) < algebraMap ℚ ℝ (S n) := by
    rw [eq_ratCast]; exact_mod_cast S_pos n
  exact mul_pos hS (Δ_pos n hn)

/-- **ZA09.** `Q_{K,M}(ξ) = m F_K(ξ) > 0` for every positive rational normalisation `m`. -/
theorem Q_pos (n : ℕ) (hn : 0 < n) (m : ℚ) (hm : 0 < m) :
    0 < aeval zeta5 (C m * F n) := by
  rw [map_mul, aeval_C]
  have hm' : (0 : ℝ) < algebraMap ℚ ℝ m := by
    rw [eq_ratCast]; exact_mod_cast hm
  exact mul_pos hm' (F_pos n hn)

end Apery
