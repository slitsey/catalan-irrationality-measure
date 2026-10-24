module
public import CatalanCore.Arith.Hybrid.ShiftChainReduce
public import CatalanCore.Arith.Hybrid.ShiftRho
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

/-! # First-order cross-chain entries

For core nodes `A < B < N` in different residue classes, `p Mn(A,B)` is `p`-integral and reduces to
`(16 (B - A))⁻¹ (p F(B) - p F(A))`, i.e. in the reduced model `(16 d)⁻¹ (L̄_B - L̄_A)`.  This is the
first-order content of every cross-chain entry `C2_xi = p · (p Mn)`, `O_mj = p · (p Mn)`. -/

section Cross
variable {p N o : ℕ} [Fact p.Prime] {Fr : Frame}

lemma fullPrefix_sub {A B : ℕ} (hAB : A ≤ B) :
    fullPrefix Fr B - fullPrefix Fr A = ∑ t ∈ Ioc A B, Fr.Delta t := by
  have he (n : ℕ) : Icc 1 n = Ioc 0 n := by ext k; simp only [mem_Icc, mem_Ioc]; omega
  unfold fullPrefix
  rw [he, he, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le A) hAB]
  ring

theorem good_pMn_cross (hL : LamData Fr o) (hp : 5 ≤ p) (hN : 4 * N < p * p) {A B : ℕ}
    (hAB : A < B) (hB : B < N) (hd : ((B : ZMod p) - A) ≠ 0) :
    Good p ((p : ℚ) * Fr.Mn A B)
      ((16 * ((B : ZMod p) - A))⁻¹ *
        (red p ((p : ℚ) * fullPrefix Fr B) - red p ((p : ℚ) * fullPrefix Fr A))) := by
  have h4 := four_ne_zmod p hp
  have h16 : (16 : ZMod p) ≠ 0 := by
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h4 h4
  have gden : Good p (16 * ((B : ℚ) - A)) (16 * ((B : ZMod p) - A)) :=
    (Good.ofNat (ℓ := p) 16).mul ((Good.natCast (ℓ := p) B).sub (Good.natCast (ℓ := p) A))
  have gu := gden.inv (mul_ne_zero h16 hd)
  have hFB := good_red (ChainModel.pPf_mem (Fr := Fr) (o := o) hL hp hN hB)
  have hFA := good_red (ChainModel.pPf_mem (Fr := Fr) (o := o) hL hp hN (hAB.trans hB))
  have gs : Good p ((p : ℚ) * (fullPrefix Fr B - fullPrefix Fr A))
      (red p ((p : ℚ) * fullPrefix Fr B) - red p ((p : ℚ) * fullPrefix Fr A)) :=
    (hFB.sub hFA).congr' (by ring)
  refine (gu.mul gs).congr' ?_
  rw [Mn_lt hL hAB, fullPrefix_sub hAB.le, one_div]
  ring

theorem redI_pMn_cross (hL : LamData Fr o) (hp : 5 ≤ p) (hN : 4 * N < p * p) {A B : ℕ}
    (hAB : A < B) (hB : B < N) (hd : ((B : ZMod p) - A) ≠ 0) :
    redI p (C ((p : ℚ) * Fr.Mn A B)) =
      rfC p ((16 * ((B : ZMod p) - A))⁻¹) * (poleL Fr p o B - poleL Fr p o A) := by
  have g := good_pMn_cross hL hp hN hAB hB hd
  rw [redI_C g.mem, g.eq]
  unfold poleL
  rw [← red_pPf_eq_poleL hL hN hB, ← red_pPf_eq_poleL hL hN (hAB.trans hB)]
  simp only [← rfCHom_apply, map_mul, map_sub]

end Cross


section CrossSym
variable {p N o : ℕ} [Fact p.Prime] {Fr : Frame}

/-- The cross entry in either order. -/
theorem good_pMn_cross_sym (hL : LamData Fr o) (hp : 5 ≤ p) (hN : 4 * N < p * p) {A B : ℕ}
    (hA : A < N) (hB : B < N) (hd : ((B : ZMod p) - A) ≠ 0) :
    (p : ℚ) * Fr.Mn A B ∈ LocRing p ∧
    redI p (C ((p : ℚ) * Fr.Mn A B)) =
      rfC p ((16 * ((B : ZMod p) - A))⁻¹) * (poleL Fr p o B - poleL Fr p o A) := by
  rcases lt_trichotomy A B with h | h | h
  · exact ⟨(good_pMn_cross hL hp hN h hB hd).mem, redI_pMn_cross hL hp hN h hB hd⟩
  · subst h; exact absurd (sub_self _) hd
  · have hd' : ((A : ZMod p) - B) ≠ 0 := by
      intro he; apply hd; linear_combination -he
    refine ⟨?_, ?_⟩
    · rw [Mn_symm]; exact (good_pMn_cross hL hp hN h hA hd').mem
    · rw [Mn_symm, redI_pMn_cross hL hp hN h hA hd']
      have e : (16 * ((B : ZMod p) - A))⁻¹ = -(16 * ((A : ZMod p) - B))⁻¹ := by
        rw [show (16 * ((B : ZMod p) - A)) = -(16 * ((A : ZMod p) - B)) by ring, inv_neg]
      rw [e]
      simp only [← rfCHom_apply, map_neg]
      ring

end CrossSym

#print axioms good_pMn_cross_sym
end CatalanCore.Arith.Hybrid
