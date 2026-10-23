module
public import CatalanCore.Arith.Hybrid.ShiftCrossSum
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

/-! # The cross-chain part of the one-node residual, reduced

`Z_reduce`: the cross-chain terms `-h (Cx V)_z + (Sr O V)_z` of `rho(z)` (with `V = adj(Q0) ω`,
`ω_k = a pPf(k) - b`) equal `p · Y`, and
`Y ≡ - h̄² ḡ ∑_{c} (16 (c - x))⁻¹ c̄(c)`, where `c̄(c) = respAt c` is the reduced response of the chain
of the residue `c` (the classes `c ≡ x` drop out because `0⁻¹ = 0`). -/

section ZReduce
open ChainModel ChainClasses LemmaE
variable {p r N o : ℕ} [Fact p.Prime] {Fr : Frame} {Z : Type} [Fintype Z] [DecidableEq Z]
  {xs ys : Z → ℕ}

lemma coefZ_same_class (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (z : Z) (j : Fin r) (hj : j.val % p = xs z % p) :
    -(ChainModel.h Fr p r xs ys * Cx Fr p r xs ys z j) +
      ∑ m, Sr Fr p r xs ys z m * Ocross Fr p r xs ys m j = 0 := by
  have h0 : Cx Fr p r xs ys z j = 0 := by
    have : blockRect (fun z => xs z % p) (fun i : Fin r => i.val % p) (C2 Fr p r xs ys) z j =
        C2 Fr p r xs ys z j := by
      simp only [blockRect]; exact if_pos hj.symm
    simp [Cx, this]
  have h1 : ∀ m : Fin r, Sr Fr p r xs ys z m * Ocross Fr p r xs ys m j = 0 := by
    intro m
    by_cases hmx : m.val % p = xs z % p
    · rw [Ocross_apply, if_pos (by rw [hmx, hj]), mul_zero]
    · rw [Sr_support hL hp hN hr z m (fun h => hmx h.symm), zero_mul]
  simp [h0, h1]

/-- **The cross-chain terms of `ρ`.** -/
theorem Z_reduce (hL : LamData Fr o) (hp : 5≤p) (hN : 4*N<p*p) (hr : r≤N)
    (hx : ∀ z, xs z<N) {a b : ℚ[X]} (ha : GLE p 0 a) (hb : GLE p 0 b) (gb : RatFunc (ZMod p))
    (z : Z) (hxz : r ≤ xs z)
    (hA : redI p a = gb * srcB Fr p o r (xs z)) (hB : redI p b = gb * srcA Fr p o r (xs z)) :
    ∃ Y : ℚ[X], GLE p 0 Y ∧
      (-(ChainModel.h Fr p r xs ys * ∑ j, Cx Fr p r xs ys z j *
            Vw Fr p r xs ys (fun m => omegaW Fr p a b m.val) j) +
        ∑ m, Sr Fr p r xs ys z m * ∑ j, Ocross Fr p r xs ys m j *
            Vw Fr p r xs ys (fun m => omegaW Fr p a b m.val) j) = C (p : ℚ) * Y ∧
      redI p Y = -(redI p (ChainModel.h Fr p r xs ys))^2 * gb *
        ∑ c : ZMod p, rfC p ((16 * (c - ((xs z : ℕ) : ZMod p)))⁻¹) *
          respAt Fr p o r c (srcA Fr p o r (xs z)) (srcB Fr p o r (xs z)) := by
  classical
  set x := xs z with hxdef
  set w : Fin r → ℚ[X] := fun m => omegaW Fr p a b m.val with hw
  have hwg : ∀ m, GLE p 0 (w m) := fun m =>
    gle0_of_int1 ((int1_of_gle0 (gle0_mul ha (ChainModel.gle0_pPf hL hp hN hr
      (lt_of_lt_of_le m.isLt hr)))).sub (int1_of_gle0 hb))
  have hV : ∀ m, GLE p 0 (Vw Fr p r xs ys w m) := gle0_Vw hL hp hN hr w hwg
  -- coefficient polynomials
  have hc : ∀ j : Fin r, ∃ c' : ℚ[X], GLE p 0 c' ∧
      (-(ChainModel.h Fr p r xs ys * Cx Fr p r xs ys z j) +
          ∑ m, Sr Fr p r xs ys z m * Ocross Fr p r xs ys m j) = C (p : ℚ) * c' ∧
      redI p c' = if j.val % p ≠ x % p then
        redI p (ChainModel.h Fr p r xs ys) *
          rfC p ((16 * (((j.val : ℕ) : ZMod p) - ((x : ℕ) : ZMod p)))⁻¹) *
          (srcA Fr p o r x - srcB Fr p o r x * poleL Fr p o j.val) else 0 := by
    intro j
    by_cases hj : j.val % p ≠ x % p
    · obtain ⟨c', h1, h2, h3⟩ := coef_reduce (ys := ys) hL hp hN hr hx z hxz j hj
      exact ⟨c', h1, h2, by rw [if_pos hj]; exact h3⟩
    · push_neg at hj
      refine ⟨0, GLE.zero 0, ?_, by rw [if_neg (not_not.2 hj)]; exact redI_zero⟩
      rw [coefZ_same_class (ys := ys) hL hp hN hr z j hj]; simp
  choose c' hc1 hc2 hc3 using hc
  refine ⟨∑ j, c' j * Vw Fr p r xs ys w j, GLE.sum fun j _ => gle0_mul (hc1 j) (hV j), ?_, ?_⟩
  · -- exact identity
    have e : (-(ChainModel.h Fr p r xs ys * ∑ j, Cx Fr p r xs ys z j * Vw Fr p r xs ys w j) +
        ∑ m, Sr Fr p r xs ys z m * ∑ j, Ocross Fr p r xs ys m j * Vw Fr p r xs ys w j) =
        ∑ j, (-(ChainModel.h Fr p r xs ys * Cx Fr p r xs ys z j) +
          ∑ m, Sr Fr p r xs ys z m * Ocross Fr p r xs ys m j) * Vw Fr p r xs ys w j := by
      simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, neg_mul, Finset.sum_neg_distrib,
        Finset.mul_sum]
      congr 1
      · apply congrArg Neg.neg
        exact Finset.sum_congr rfl fun j _ => by ring
      · rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by ring
    rw [e, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hc2 j]; ring
  · rw [redI_sum _ _ (fun j _ => gle0_mul (hc1 j) (hV j))]
    simp only [redI_mul (hc1 _) (hV _), hc3]
    rw [sum_fin_by_class (p := p), Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hq : ∀ q : ChainIndex p r (c.val + p * r), (chainNode q).val % p = c.val := fun q => by
      rw [chainNode_mod, chain_rep_mod]
    have hxc : ((c.val + p * r : ℕ) : ZMod p) = c := by
      push_cast; simp [ZMod.natCast_self]
    by_cases hcx : c = ((x : ℕ) : ZMod p)
    · have hval : c.val = x % p := by rw [hcx, ZMod.val_natCast]
      simp only [hq, hval, ne_eq, not_true_eq_false, if_false, zero_mul, Finset.sum_const_zero]
      rw [hcx]; simp [rfC]
    · have hne : c.val ≠ x % p := fun h => hcx (natCast_of_mod h.symm).symm
      simp only [hq, ne_eq, hne, not_false_eq_true, if_true]
      set M := poleRed Fr p o (fun q : ChainIndex p r (c.val + p * r) => (chainNode q).val) with hM
      set u : ChainIndex p r (c.val + p * r) → RatFunc (ZMod p) :=
        fun q => srcA Fr p o r x - srcB Fr p o r x * poleL Fr p o (chainNode q).val with hu
      have hom : ∀ q : ChainIndex p r (c.val + p * r), redI p (w (chainNode q)) = -gb * u q := by
        intro q
        have e1 : w (chainNode q) = a * C ((p : ℚ) * fullPrefix Fr (chainNode q).val) - b := rfl
        rw [e1, redI_sub (gle0_mul ha (ChainModel.gle0_pPf hL hp hN hr
          (lt_of_lt_of_le (chainNode q).isLt hr))) hb,
          redI_mul ha (ChainModel.gle0_pPf hL hp hN hr (lt_of_lt_of_le (chainNode q).isLt hr)),
          redI_pPf hL hN (lt_of_lt_of_le (chainNode q).isLt hr), hA, hB]
        simp only [hu]; ring
      have hVq : ∀ q : ChainIndex p r (c.val + p * r),
          redI p (Vw Fr p r xs ys w (chainNode q)) =
            redI p (ChainModel.h Fr p r xs ys) * ((-gb) • (M⁻¹ *ᵥ u)) q := by
        intro q
        rw [redI_Vw_chain (ys := ys) hL hp hN hr w hwg (le_chain_rep c) q]
        congr 1
        have : (fun i => redI p (w (chainNode i))) = (-gb) • u := funext fun i => by
          rw [hom i]; simp
        rw [this, Matrix.mulVec_smul]
      have hresp : respAt Fr p o r c (srcA Fr p o r x) (srcB Fr p o r x) = u ⬝ᵥ (M⁻¹ *ᵥ u) := rfl
      simp only [hVq, hresp, dotProduct, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [chainNode_zmod, hxc]
      simp only [hu]
      ring

end ZReduce

#print axioms CatalanCore.Arith.Hybrid.Z_reduce
end CatalanCore.Arith.Hybrid
