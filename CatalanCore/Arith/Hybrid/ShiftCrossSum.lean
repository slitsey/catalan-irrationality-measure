module
public import CatalanCore.Arith.Hybrid.ShiftV
public import CatalanCore.Arith.Hybrid.ShiftZero
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

/-! # First-order cross-chain coefficients

For a zone row node `x = xs z` and a core node `j` of another residue, the coefficient of `V_j` in
`-h (Cx adjQ0 ω)_z + (Sr O adjQ0 ω)_z` is `p · c'_j`, and `c̄'_j = h̄ (16 (j - x))⁻¹ ū_j` with
`ū_j = A - B L̄_j` (the source moments of the chain of `x`).  The terms `L̄_j - L̄_x` of the two pieces
cancel; only the source moment combination survives. -/

section Coef
open ChainModel ChainClasses LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}

theorem coef_reduce (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx : ∀ z, xs z<N) (z : Z) (hxz : r ≤ xs z) (j : Fin r) (hj : j.val % p ≠ xs z % p) :
    ∃ c' : ℚ[X], GLE p 0 c' ∧
      (-(ChainModel.h Fr p r xs ys * Cx Fr p r xs ys z j) +
          ∑ m, Sr Fr p r xs ys z m * Ocross Fr p r xs ys m j) = C (p : ℚ) * c' ∧
      redI p c' = redI p (ChainModel.h Fr p r xs ys) *
        rfC p ((16 * (((j.val : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p)))⁻¹) *
        (srcA Fr p o r (xs z) - srcB Fr p o r (xs z) * poleL Fr p o j.val) := by
  classical
  set x := xs z with hxdef
  have hjN : j.val < N := lt_of_lt_of_le j.isLt hr
  have hdx : ((x : ℕ) : ZMod p) - ((j.val : ℕ) : ZMod p) ≠ 0 := by
    intro he
    have : ((x : ℕ) : ZMod p) = ((j.val : ℕ) : ZMod p) := sub_eq_zero.1 he
    exact hj ((ZMod.natCast_eq_natCast_iff' _ _ _).1 this).symm
  have hdj : ((j.val : ℕ) : ZMod p) - ((x : ℕ) : ZMod p) ≠ 0 := by
    intro he; apply hdx; linear_combination -he
  -- cross entries
  have hmemx := (good_pMn_cross_sym hL hp hN (A := x) (B := j.val) (hx z) hjN hdj)
  have hCx : Cx Fr p r xs ys z j = C (p : ℚ) * C ((p : ℚ) * Fr.Mn x j.val) := by
    have h0 : blockRect (fun z => xs z % p) (fun i : Fin r => i.val % p) (C2 Fr p r xs ys) z j = 0 := by
      simp only [blockRect]; exact if_neg (fun h => hj h.symm)
    simp only [Cx, Matrix.sub_apply, h0, sub_zero, C2_apply]
    rw [← map_mul]; congr 1; ring
  have hSO : ∀ m : Fin r, Sr Fr p r xs ys z m * Ocross Fr p r xs ys m j =
      C (p : ℚ) * (Sr Fr p r xs ys z m * C ((p : ℚ) * Fr.Mn m.val j.val)) := by
    intro m
    by_cases hmx : m.val % p = x % p
    · have hmj : m.val % p ≠ j.val % p := by rw [hmx]; exact Ne.symm hj
      have hne : m ≠ j := fun h => hmj (by rw [h])
      rw [Ocross_apply, if_neg hmj, Q_apply, if_neg hne, mul_zero, add_zero]
      rw [show C ((p : ℚ) ^ 2 * Fr.Mn m.val j.val) = C (p : ℚ) * C ((p : ℚ) * Fr.Mn m.val j.val) by
        rw [← map_mul]; congr 1; ring]
      ring
    · rw [Sr_support hL hp hN hr z m (fun h => hmx h.symm)]; simp
  have hf : ∀ m : Fin r, GLE p 0 (Sr Fr p r xs ys z m * C ((p : ℚ) * Fr.Mn m.val j.val)) := by
    intro m
    by_cases hmx : m.val % p = x % p
    · have hmj : m.val % p ≠ j.val % p := by rw [hmx]; exact Ne.symm hj
      have hdmj : ((j.val : ℕ) : ZMod p) - ((m.val : ℕ) : ZMod p) ≠ 0 := by
        intro he
        have : ((j.val : ℕ) : ZMod p) = ((m.val : ℕ) : ZMod p) := sub_eq_zero.1 he
        exact hmj ((ZMod.natCast_eq_natCast_iff' _ _ _).1 this).symm
      have hmem := (good_pMn_cross_sym hL hp hN (A := m.val) (B := j.val)
        (lt_of_lt_of_le m.isLt hr) hjN hdmj).1
      exact gle0_mul (gle0_of_int1 (Sr_int1 hL hp hN hr hx z m)) (GLE.C_iff.2 (by simpa using hmem))
    · rw [Sr_support hL hp hN hr z m (fun h => hmx h.symm)]; simpa using GLE.zero 0
  have hh := gle0_h (xs := xs) (ys := ys) hL hp hN hr
  have hC : GLE p 0 (C ((p : ℚ) * Fr.Mn x j.val)) := GLE.C_iff.2 (by simpa using hmemx.1)
  -- the integral coefficient
  refine ⟨(∑ m, Sr Fr p r xs ys z m * C ((p : ℚ) * Fr.Mn m.val j.val)) -
      ChainModel.h Fr p r xs ys * C ((p : ℚ) * Fr.Mn x j.val), ?_, ?_, ?_⟩
  · -- integrality
    exact gle0_of_int1 ((int1_of_gle0 (GLE.sum fun m _ => hf m)).sub
      (int1_of_gle0 (gle0_mul hh hC)))
  · -- the exact identity
    rw [hCx]
    simp_rw [hSO]
    rw [← Finset.mul_sum]
    ring
  · -- the reduction
    rw [redI_sub (GLE.sum fun m _ => hf m) (gle0_mul hh hC), redI_sum _ _ (fun m _ => hf m),
      redI_mul hh hC, hmemx.2]
    set M := poleRed Fr p o (fun q : ChainIndex p r x => (chainNode q).val) with hM
    set G : ChainIndex p r x → RatFunc (ZMod p) :=
      fun q => (M⁻¹ *ᵥ (fun i => rfC p (red p (poleScaledEntry Fr p o (chainNode i).val x)))) q with hG
    have hSr : ∀ m, GLE p 0 (Sr Fr p r xs ys z m) := fun m =>
      gle0_of_int1 (Sr_int1 hL hp hN hr hx z m)
    -- the chain nodes
    have hq : ∀ q : ChainIndex p r x, GLE p 0 (C ((p : ℚ) * Fr.Mn (chainNode q).val j.val)) ∧
        redI p (C ((p : ℚ) * Fr.Mn (chainNode q).val j.val)) =
          rfC p ((16 * (((j.val : ℕ) : ZMod p) - ((x : ℕ) : ZMod p)))⁻¹) *
            (poleL Fr p o j.val - poleL Fr p o (chainNode q).val) := by
      intro q
      have hmj : (chainNode q).val % p ≠ j.val % p := by rw [chainNode_mod]; exact Ne.symm hj
      have hdmj : ((j.val : ℕ) : ZMod p) - (((chainNode q).val : ℕ) : ZMod p) ≠ 0 := by
        intro he
        have : ((j.val : ℕ) : ZMod p) = (((chainNode q).val : ℕ) : ZMod p) := sub_eq_zero.1 he
        exact hmj ((ZMod.natCast_eq_natCast_iff' _ _ _).1 this).symm
      have H := good_pMn_cross_sym hL hp hN (A := (chainNode q).val) (B := j.val)
        (lt_of_lt_of_le (chainNode q).isLt hr) hjN hdmj
      refine ⟨GLE.C_iff.2 (by simpa using H.1), ?_⟩
      rw [H.2, chainNode_zmod]
    have hsum : ∑ m, redI p (Sr Fr p r xs ys z m * C ((p : ℚ) * Fr.Mn m.val j.val)) =
        ∑ q : ChainIndex p r x, redI p (Sr Fr p r xs ys z (chainNode q)) *
          redI p (C ((p : ℚ) * Fr.Mn (chainNode q).val j.val)) := by
      rw [sum_chain (p := p) hxz (fun m => redI p (Sr Fr p r xs ys z m *
        C ((p : ℚ) * Fr.Mn m.val j.val)))]
      · apply Finset.sum_congr rfl; intro q _
        exact redI_mul (hSr _) (hq q).1
      · intro m hm
        rw [Sr_support hL hp hN hr z m (fun h => hm h.symm), zero_mul, redI_zero]
    rw [hsum]
    have hq2 : ∀ q : ChainIndex p r x, redI p (Sr Fr p r xs ys z (chainNode q)) *
          redI p (C ((p : ℚ) * Fr.Mn (chainNode q).val j.val)) =
        redI p (ChainModel.h Fr p r xs ys) *
          rfC p ((16 * (((j.val : ℕ) : ZMod p) - ((x : ℕ) : ZMod p)))⁻¹) *
          (G q * (poleL Fr p o j.val - poleL Fr p o (chainNode q).val)) := by
      intro q
      rw [redI_Sr_chain (ys := ys) hL hp hN hr hx z hxz q, (hq q).2]
      ring
    simp only [hq2, ← Finset.mul_sum]
    have hA : srcA Fr p o r x = poleL Fr p o x - ∑ q, G q * poleL Fr p o (chainNode q).val := rfl
    have hB : srcB Fr p o r x = 1 - ∑ q, G q := rfl
    rw [hA, hB]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.mul_sum, ← Finset.mul_sum]
    ring

end Coef

#print axioms CatalanCore.Arith.Hybrid.coef_reduce
end CatalanCore.Arith.Hybrid
