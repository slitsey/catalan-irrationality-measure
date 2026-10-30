import CatalanCore.Uniform.Bank.Sevenths.TwoTerm
import CatalanCore.Uniform.Bank.Sevenths.Roots
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Sevenths
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Smith
  CatalanCore.Arith.Hybrid.Periodic

theorem sevenths_norm_good_of_eight (a : Fin 6) (p : ℕ) [Fact p.Prime] (hp8 : 8 ≤ p) :
    (seventhsFrameAt a).norm ∈ S p ∧ red p (seventhsFrameAt a).norm ≠ 0 := by
  constructor
  · change (49 : ℚ) ∈ S p
    exact (Good.natCast (ℓ := p) 49).mem
  · change red p (49 : ℚ) ≠ 0
    rw [(Good.natCast (ℓ := p) 49).eq]
    rw [show (49 : ZMod p) = (7 : ZMod p) ^ 2 by norm_num]
    exact pow_ne_zero _ (natCast_ne_zero' (by norm_num : 0 < 7) (by omega))

theorem sevenths_norm_good (a : Fin 6) (p : ℕ) [Fact p.Prime] (hp64 : 64 ≤ p) :
    (seventhsFrameAt a).norm ∈ S p ∧ red p (seventhsFrameAt a).norm ≠ 0 :=
  sevenths_norm_good_of_eight a p (by omega)

theorem sevenths_simple_poles (a : Fin 6) (p N : ℕ) (hN : 7 * N ≤ p * p) :
    ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ 7 * t - (7 - seventhNumerator a) := by
  intro t ht htN hd
  have ho := seventhOffset_bounds a
  have hpos : 0 < 7 * t - (7 - seventhNumerator a) := by
    change 0 < 7 * t - seventhOffset a
    omega
  have hlt : 7 * t - (7 - seventhNumerator a) < p ^ 2 := by nlinarith
  have := Nat.le_of_dvd hpos hd
  omega

noncomputable def sevenths_poleData_of_eight (a : Fin 6) (p N : ℕ) [Fact p.Prime]
    (hp8 : 8 ≤ p) (hN : 7 * N ≤ p * p) : PoleData (seventhsFrameAt a) p N :=
  (sevenths_twoTerm a).twoTermPoleData (by omega) (sevenths_simple_poles a p N hN)
    (sevenths_norm_good_of_eight a p hp8).1 (sevenths_norm_good_of_eight a p hp8).2

noncomputable def sevenths_poleData (a : Fin 6) (p N : ℕ) [Fact p.Prime]
    (hp64 : 64 ≤ p) (hN : 7 * N ≤ p * p) : PoleData (seventhsFrameAt a) p N :=
  (sevenths_twoTerm a).twoTermPoleData (by omega) (sevenths_simple_poles a p N hN)
    (sevenths_norm_good a p hp64).1 (sevenths_norm_good a p hp64).2

#print axioms sevenths_poleData
end CatalanCore.Uniform.Bank.Sevenths
