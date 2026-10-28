module

public import CatalanCore.Uniform.Content.UFFamily.Closed
public import CatalanCore.Uniform.Content.UFWedge.Cert
public import CatalanCore.Uniform.Content.UFWedge.Shift

@[expose] public section

/-!
# UF families: entries of the evaluated fiber as reductions of rationals (lane H10)

For nodes of the same residue class modulo `p` the entries of the evaluated bordered fiber
(`nodeFib (evP p u₀)`) are the images of the rationals

  `off-diagonal  nrm⁻¹ (L_b - L_a) / (d_b - d_a)`,  `diagonal  u₀ - nrm⁻¹ E_a`,
  `border  nrm⁻¹ (L_a - L_t) / (d_a - d_t)`,  `prefix  L_a`,  `border prefix  L_t`

(`d = ⌊·/p⌋` the block digit, `L = V`, `E = W` the prefix residues of `Closed`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFFamily

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame}

theorem good_PF1 (D : PoleData Fr p N) {b : ℕ} (hb : b < N) : Good p ((p : ℚ) * Fp Fr b) (D.V b) := by
  have g := D.sum_delta hb (a := 0)
  have he : Icc 1 b = Ioc 0 b := by ext k; simp only [mem_Icc, mem_Ioc]; omega
  unfold PoleData.V
  rw [he]
  exact g

theorem inv_digit {a b : ℕ} (hab : a < b) (hmod : (a : ZMod p) = (b : ZMod p)) :
    invResidue p (b - a) = (((b / p : ℕ) : ZMod p) - ((a / p : ℕ) : ZMod p))⁻¹ := by
  have hp := (Fact.out : p.Prime)
  have h1 : a % p = b % p := (ZMod.natCast_eq_natCast_iff' a b p).1 hmod
  have h2 : p ∣ b - a := (Nat.modEq_iff_dvd' hab.le).1 h1
  obtain ⟨k, hk⟩ := h2
  have hb : b = a + p * k := by omega
  have hdiv : b / p = a / p + k := by rw [hb, Nat.add_mul_div_left _ _ hp.pos]
  have hkk : (b - a) / p = k := by rw [hk, Nat.mul_div_cancel_left _ hp.pos]
  have : p ∣ b - a := ⟨k, hk⟩
  rw [invResidue, if_pos this, hkk, hdiv]
  push_cast
  congr 1
  ring

/-- Off-diagonal entries: `p² Mn a b` reduces to `nrm⁻¹ (V b - V a) / (d_b - d_a)`. -/
theorem good_Mn_off (D : PoleData Fr p N) (hN : N < p * p) {a b : ℕ} (hab : a ≠ b)
    (hmod : (a : ZMod p) = (b : ZMod p)) (ha : a < N) (hb : b < N) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn a b)
      ((red p Fr.norm)⁻¹ * (D.V b - D.V a) *
        (((b / p : ℕ) : ZMod p) - ((a / p : ℕ) : ZMod p))⁻¹) := by
  rcases lt_or_gt_of_ne hab with h | h
  · have g := D.good_square hN h hb
    rw [inv_digit h hmod] at g
    exact g.congr (by ring)
  · have g := D.good_square hN h ha
    rw [inv_digit h hmod.symm] at g
    rw [UFMoments.frame_Mn_symm Fr a b]
    refine g.congr ?_
    have e1 : ((b / p : ℕ) : ZMod p) - ((a / p : ℕ) : ZMod p) =
        -(((a / p : ℕ) : ZMod p) - ((b / p : ℕ) : ZMod p)) := by ring
    rw [e1, inv_neg]; ring

theorem good_Mn_diag (D : PoleData Fr p N) {a : ℕ} (ha : a < N) :
    Good p ((p : ℚ) ^ 2 * Fr.Mn a a) (-(red p Fr.norm)⁻¹ * D.W a) := D.good_diagonal ha

section Eval

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem evP_C_liftQ (u0 : ZMod p) {x : ℚ} {y : ZMod p} (h : Good p x y) :
    evP p u0 (Polynomial.C (Hybrid.liftQ p x)) = y := by
  simp [evP, Hybrid.redQ_liftQ h]

theorem evP_core_off (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (u0 : ZMod p) {a b : ι}
    (hab : a ≠ b) {y : ZMod p} (h : Good p ((p : ℚ) ^ 2 * Fr.Mn (c a) (c b)) y) :
    evP p u0 ((sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ a b) = y := by
  rw [sLift_core_entry D hN c xs ys hc hx hy a b, if_neg hab, add_zero]
  exact evP_C_liftQ u0 h

theorem evP_core_diag (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (u0 : ZMod p) {a : ι}
    {y : ZMod p} (h : Good p ((p : ℚ) ^ 2 * Fr.Mn (c a) (c a)) y) :
    evP p u0 ((sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ a a) = u0 + y := by
  rw [sLift_core_entry D hN c xs ys hc hx hy a a, if_pos rfl]
  simp [evP, Hybrid.redQ_liftQ h]
  ring

theorem evP_loewRow (c : ι → ℕ) (t : ℕ) (u0 : ZMod p) (a : ι) {y : ZMod p}
    (h : Good p ((p : ℚ) ^ 2 * Fr.Mn t (c a)) y) :
    evP p u0 (loewRow p Fr c t a) = y := evP_C_liftQ u0 h

theorem evP_PF1 (u0 : ZMod p) (a : ℕ) {y : ZMod p} (h : Good p ((p : ℚ) * Fp Fr a) y) :
    evP p u0 (PF1 p Fr a) = y := evP_C_liftQ u0 h

end Eval

end CatalanCore.Uniform.Content.UFFamily
