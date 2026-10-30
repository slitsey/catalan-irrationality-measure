import CatalanCore.Uniform.Bank.Sevenths.UF
import CatalanCore.Uniform.Bank.Sevenths.Roots
import CatalanCore.Uniform.Bank.Sevenths.Rounding
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.UFSimple

/-- All compact-band primes satisfy the actual closed-UF source hypotheses. -/
theorem sevenths_closedHyp (a : Fin 6) (r p : ℕ) [Fact p.Prime]
    (hr : r % 2 = 0) (hr12 : 12 ≤ r) (hp64 : 64 ≤ p) (hrp : r ≤ 6 * p) :
    ClosedHyp (1 / 6) one_sixth_pos (seventhsFrameAt a) 7
      (7 - seventhNumerator a) r p (seventhRho a p) := by
  have hb := seventhRho_bounds a p (by omega)
  have ho := seventhOffset_bounds a
  have hpp : 64 * p ≤ p * p := Nat.mul_le_mul_right p hp64
  refine ⟨hr, by omega, F7_border_pos hr hr12, by nlinarith,
    F7_border_twice_le hr hrp, by omega, by omega, by omega, ?_, ?_, ?_,
    seventhRho_dvd a p (by omega), hb.1, hb.2⟩
  · intro t ht htN hd
    have hpos : 0 < 7 * t - (7 - seventhNumerator a) := by
      change 0 < 7 * t - seventhOffset a
      omega
    have hlt : 7 * t - (7 - seventhNumerator a) < p ^ 2 := by
      have ht7 : 7 * t < 49 * p := by omega
      nlinarith
    have := Nat.le_of_dvd hpos hd
    omega
  · change (49 : ℚ) ∈ S p
    exact (Good.natCast (ℓ := p) 49).mem
  · change red p (49 : ℚ) ≠ 0
    rw [(Good.natCast (ℓ := p) 49).eq]
    exact natCast_ne_zero' (by norm_num) (by omega)

#print axioms sevenths_closedHyp
end CatalanCore.Uniform.Bank.Sevenths
