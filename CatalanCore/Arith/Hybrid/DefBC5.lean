module

public import CatalanCore.Arith.Hybrid.DefB
public import CatalanCore.Arith.Hybrid.DefC5
public import CatalanCore.Arith.Hybrid.DefRank

@[expose] public section

/-!
# Theorems B and C5 at a prime: assembly of the rank count with the rank principle

`defAt_B` and `defAt_C5` combine the linear-algebra rank counts (`DefB`, `DefC5`) with
`defAt_of_rank`.  What is left to the caller are exactly the entry computations of the paper:

* `hB` : the scaled entries `p^{u_a+v_b} Full_ab` are integral with reduction `Bbar (e a) (e' b)`,
  where `Bbar` is the block matrix of the proof (`BbarB`, resp. `fromBlocks T Up Wp Mp`);
* the Schur identities (`hS` : `A0 - π⁻¹ V Vᵀ = s₀ I - κ E Eᵀ` for B; `hSchur` for C5);
* the shape of the zone rows and columns;
* `hopt` : the weights `(u, v)` are tropically optimal, `∑u + ∑v ≤ tropExp`.
-/

open Polynomial CatalanCore.Basic CatalanCore.Linalg Matrix

namespace CatalanCore.Arith.Hybrid

variable {Fr : Frame} (I : HybInst Fr) (r m : ℕ) (p : ℕ) [Fact p.Prime]

section B



/-- **Theorem B at a prime** (`r < p < r + m`, `d = p - r`, `D` of size `d`): deficit `m - d`. -/
theorem defAt_B {B0 B1 X Y D : Type} [Fintype B0] [Fintype B1] [Fintype X] [Fintype Y]
    [Fintype D] [DecidableEq B0] [DecidableEq B1] [DecidableEq X] [DecidableEq Y]
    [DecidableEq D]
    (hB0 : Fintype.card B1 + Fintype.card B0 = r) (_hX : Fintype.card X = m)
    (hY : Fintype.card Y = m) (hdm : Fintype.card D ≤ m)
    (e : Fin r ⊕ Fin m ≃ (B0 ⊕ X) ⊕ B1) (e' : Fin r ⊕ Fin m ≃ (B0 ⊕ Y) ⊕ B1)
    (u v : Fin r ⊕ Fin m → ℕ) (hopt : ∑ a, u a + ∑ b, v b ≤ tropExp I r m p)
    (hk : m - Fintype.card D ≤ ∑ a, u a + ∑ b, v b)
    (A0 : Matrix B0 B0 (RatFunc (ZMod p))) (V : Matrix B0 B1 (RatFunc (ZMod p)))
    (π s0 κ lam σ : RatFunc (ZMod p)) (hπ : π ≠ 0) (hs0 : s0 ≠ 0) (E : Matrix B0 D (RatFunc (ZMod p)))
    (hS : A0 - π⁻¹ • (V * Vᵀ) = s0 • (1 : Matrix B0 B0 _) - κ • (E * Eᵀ))
    (Gx : Matrix X B0 (RatFunc (ZMod p))) (Gy : Matrix B0 Y (RatFunc (ZMod p)))
    (lowX : X → Prop) (lowY : Y → Prop) [DecidablePred lowX] [DecidablePred lowY]
    (iX : X → D) (iY : Y → D) (cX : X → B0) (cY : Y → B0)
    (hGx : ∀ x w, Gx x w = if lowX x then -lam * E w (iX x) else (if w = cX x then σ else 0))
    (hGy : ∀ w y, Gy w y = if lowY y then -lam * E w (iY y) else (if w = cY y then σ else 0))
    (hdisj : ∀ x y, lowX x → lowY y → iX x ≠ iY y)
    (hc : ∀ x y, ¬ lowX x → ¬ lowY y → cX x ≠ cY y)
    (hred : ∀ a b, ∃ g : (LocRing p)[X],
      toQ p g = C ((p : ℚ) ^ (u a + v b)) * fullEntry Fr r m a b ∧
        phiP p g = BbarB A0 V π Gx Gy (e a) (e' b)) :
    m - Fintype.card D ≤ tropExp I r m p ∧
      GLE p (tropExp I r m p - (m - Fintype.card D)) (Fr.fullPoly r m) := by
  have hrank := rank_BbarB_le A0 V π s0 κ lam σ hπ hs0 E hS Gx Gy lowX lowY iX iY cX cY hGx hGy
    hdisj hc
  refine defAt_of_rank I r m p u v hopt
    ((BbarB A0 V π Gx Gy).submatrix e e') hred (m - Fintype.card D) hk ?_
  rw [Matrix.rank_submatrix _ e e']
  omega
end B

section C5

/-- **Theorem C5 at a prime** (deficit `L - m`, `L = |LX| + |LY|`). -/
theorem defAt_C5 {U P X Y : Type} [Fintype U] [Fintype P] [Fintype X] [Fintype Y]
    [DecidableEq U] [DecidableEq P] [DecidableEq X] [DecidableEq Y]
    (hUP : Fintype.card P + Fintype.card U = r) (hX : Fintype.card X = m)
    (hY : Fintype.card Y = m)
    (e : Fin r ⊕ Fin m ≃ (U ⊕ X) ⊕ P) (e' : Fin r ⊕ Fin m ≃ (U ⊕ Y) ⊕ P)
    (u v : Fin r ⊕ Fin m → ℕ) (hopt : ∑ a, u a + ∑ b, v b ≤ tropExp I r m p)
    (LX : Finset X) (LY : Finset Y) (hL : m ≤ LX.card + LY.card)
    (hk : LX.card + LY.card - m ≤ ∑ a, u a + ∑ b, v b)
    (T : Matrix (U ⊕ X) (U ⊕ Y) (RatFunc (ZMod p))) (Up : Matrix (U ⊕ X) P (RatFunc (ZMod p)))
    (Wp : Matrix P (U ⊕ Y) (RatFunc (ZMod p))) (Mp : Matrix P P (RatFunc (ZMod p)))
    [Invertible Mp] (s0 : RatFunc (ZMod p)) (hs0 : s0 ≠ 0)
    (Gx : Matrix X U (RatFunc (ZMod p))) (Gy : Matrix U Y (RatFunc (ZMod p)))
    (hSchur : T - Up * ⅟Mp * Wp = fromBlocks (s0 • (1 : Matrix U U _)) Gy Gx 0)
    (cX : X → U) (cY : Y → U) (σ : RatFunc (ZMod p))
    (hGx : ∀ x ∈ LX, ∀ w, Gx x w = if w = cX x then σ else 0)
    (hGy : ∀ y ∈ LY, ∀ w, Gy w y = if w = cY y then σ else 0)
    (hc : ∀ x ∈ LX, ∀ y ∈ LY, cX x ≠ cY y)
    (hred : ∀ a b, ∃ g : (LocRing p)[X],
      toQ p g = C ((p : ℚ) ^ (u a + v b)) * fullEntry Fr r m a b ∧
        phiP p g = (fromBlocks T Up Wp Mp) (e a) (e' b)) :
    LX.card + LY.card - m ≤ tropExp I r m p ∧
      GLE p (tropExp I r m p - (LX.card + LY.card - m)) (Fr.fullPoly r m) := by
  have hrank := rank_BbarC5_le T Up Wp Mp s0 hs0 Gx Gy hSchur LX LY cX cY σ hGx hGy hc
  rw [hX, hY] at hrank
  have h1 : LX.card ≤ m := hX ▸ Finset.card_le_univ LX
  have h2 : LY.card ≤ m := hY ▸ Finset.card_le_univ LY
  refine defAt_of_rank I r m p u v hopt ((fromBlocks T Up Wp Mp).submatrix e e') hred
    (LX.card + LY.card - m) hk ?_
  rw [Matrix.rank_submatrix _ e e']
  omega

end C5

end CatalanCore.Arith.Hybrid
