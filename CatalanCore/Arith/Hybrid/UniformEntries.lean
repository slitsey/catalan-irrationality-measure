module

public import CatalanCore.Arith.Hybrid.SingularData

@[expose] public section

/-! # Uniform entry reductions for every residue-chain length

The finite singular-set interface remains the old `SgData` interface.  The
additional square-level formula treats any distance at once, so no table of
one-, two-, or four-node chains is needed.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {o N : ℕ}

theorem good_interval_delta (hL : LamData Fr o) (hN : 4 * N < p * p)
    {A B : ℕ} (hB : B < N) :
    Good p ((p : ℚ) * ∑ t ∈ Ioc A B, Fr.Delta t)
      (∑ t ∈ Ioc A B, deltaResidue p o t) := by
  rw [Finset.mul_sum]
  exact Good.sum _ _ _ fun t ht =>
    good_Delta_uniform hL hN (by have := (Finset.mem_Ioc.mp ht).1; omega)
      (by have := (Finset.mem_Ioc.mp ht).2; omega)

theorem good_prefix_dsq (hL : LamData Fr o) (hN : 4 * N < p * p)
    {A : ℕ} (hA : A < N) :
    Good p ((p : ℚ) ^ 2 * ∑ t ∈ Icc 1 A, Fr.Dsq t)
      (∑ t ∈ Icc 1 A, dsqResidue p o t) := by
  rw [Finset.mul_sum]
  exact Good.sum _ _ _ fun t ht =>
    good_Dsq_uniform hL hN (Finset.mem_Icc.mp ht).1
      (by have := (Finset.mem_Icc.mp ht).2; omega)

theorem good_Mn_square_uniform (hL : LamData Fr o) (hp5 : 5 ≤ p)
    (hN : 4 * N < p * p) {A B : ℕ} (hAB : A < B) (hB : B < N) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A B)
      ((16 : ZMod p)⁻¹ * invResidue p (B - A) *
        ∑ t ∈ Ioc A B, deltaResidue p o t) := by
  have h16 : (16 : ZMod p) ≠ 0 := by
    have h4 := four_ne_zmod p hp5
    have he : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [he]; exact mul_ne_zero h4 h4
  have g16 := (Good.one (ℓ := p)).div (Good.ofNat (ℓ := p) 16) h16
  have gd := good_scaled_inverse (p := p) (n := B - A) (by omega) (by omega)
  have gs := good_interval_delta hL hN hB (A := A)
  have g := (g16.mul gd).mul gs
  refine (g.congr' ?_).congr (by simp only [one_div])
  rw [Mn_lt hL hAB]
  have hcast : ((B - A : ℕ) : ℚ) = (B : ℚ) - A := by
    exact Nat.cast_sub hAB.le
  rw [hcast]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem good_Mn_diag_uniform (hL : LamData Fr o) (hp5 : 5 ≤ p)
    (hN : 4 * N < p * p) {A : ℕ} (hA : A < N) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A A)
      (-(16 : ZMod p)⁻¹ * ∑ t ∈ Icc 1 A, dsqResidue p o t) := by
  have h16 : (16 : ZMod p) ≠ 0 := by
    have h4 := four_ne_zmod p hp5
    have he : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [he]; exact mul_ne_zero h4 h4
  have g16 := ((Good.one (ℓ := p)).div (Good.ofNat (ℓ := p) 16) h16).neg
  have g := g16.mul (good_prefix_dsq hL hN hA)
  refine (g.congr' ?_).congr (by simp only [one_div])
  rw [Frame.Mn, if_pos rfl, hL.norm_eq]
  ring

theorem deltaResidue_eq_zero {t : ℕ} (ht : ¬ p ∣ t) (ht4 : ¬ p ∣ 4 * t - o) :
    deltaResidue p o t = 0 := by simp [deltaResidue, invResidue, ht, ht4]

theorem dsqResidue_eq_zero {t : ℕ} (ht : ¬ p ∣ t) (ht4 : ¬ p ∣ 4 * t - o) :
    dsqResidue p o t = 0 := by simp [dsqResidue, invResidue, ht, ht4]

theorem Mn_square_mem (hL : LamData Fr o) (hp5 : 5 ≤ p) (hN : 4 * N < p * p)
    {A B : ℕ} (hA : A < N) (hB : B < N) :
    (p : ℚ) ^ 2 * Fr.Mn A B ∈ S p := by
  rcases lt_trichotomy A B with h | rfl | h
  · exact (good_Mn_square_uniform hL hp5 hN h hB).mem
  · exact (good_Mn_diag_uniform hL hp5 hN hA).mem
  · rw [Mn_symm]
    exact (good_Mn_square_uniform hL hp5 hN h hA).mem

/-- The first-order Loewner formula, with no ordering restriction on the nodes. -/
theorem good_Mn_cross_uniform (hL : LamData Fr o) (hp5 : 5 ≤ p)
    (hN : 4 * N < p * p) {k A B : ℕ}
    (hk4 : (4 : ZMod p) * k = (o : ZMod p)) (hA : A < N) (hB : B < N)
    (hd : (B : ZMod p) - A ≠ 0) :
    Good p ((p : ℚ) * Fr.Mn A B)
      ((16 * ((B : ZMod p) - A))⁻¹ *
        (Lv (singularNodes p o N) (deltaResidue p o) B -
          Lv (singularNodes p o N) (deltaResidue p o) A)) := by
  have D := uniform_sgData hL hN hk4
  rcases lt_trichotomy A B with h | rfl | h
  · exact tab_P1 hL hp5 D h hB hd
  · exact False.elim (hd (sub_self _))
  · have hd' : (A : ZMod p) - B ≠ 0 := by
      intro he
      apply hd
      linear_combination -he
    have g := tab_P1 hL hp5 D h hA hd'
    rw [Mn_symm]
    refine g.congr ?_
    have he : (A : ZMod p) - B = -((B : ZMod p) - A) := by ring
    rw [he, mul_neg, inv_neg]
    ring

theorem good_Mn_cross_square_zero (hL : LamData Fr o) (hp5 : 5 ≤ p)
    (hN : 4 * N < p * p) {k A B : ℕ}
    (hk4 : (4 : ZMod p) * k = (o : ZMod p)) (hA : A < N) (hB : B < N)
    (hd : (B : ZMod p) - A ≠ 0) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn A B) 0 := by
  have g := (good_Mn_cross_uniform hL hp5 hN hk4 hA hB hd).ell_mul
  exact g.congr' (by ring)

end CatalanCore.Arith.Hybrid
