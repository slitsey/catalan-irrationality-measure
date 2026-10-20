module

public import CatalanCore.Decay.Rect.IntegR
public import CatalanCore.Decay.Rect.Energy2
public import CatalanCore.Rect.Geometry

@[expose] public section

/-!
# Rectangular window: `det Full(const + t)` for the hybrid family (WP-H2-core)

`window_rect` : if for every kept-node pattern `s : Fin k → Fin (r + m)` (all extra nodes kept) the
two-family energy bound `RectEnergy` holds with exponent `T0 + r (N - k) cc` (`N = r + m`), then
`|Q_{(r,m)}(const + t)| ≤ 2^r exp (T0 + N log M0)` for `|t| ≤ exp (-cc r)`, where
`Q_{(r,m)} = Frame.fullPoly r m`.  Uses `det_fullN_expansion` (WP-H1) and `theoremN_rect`.
-/

open Finset Polynomial

namespace CatalanCore.Rect

def commonIdx {ι : Type*} (r m : ℕ) (c : ι → Fin r) : (ι ⊕ Fin m) → Fin (r + m) :=
  Sum.elim (fun a => ⟨c a, (c a).isLt.trans_le (Nat.le_add_right r m)⟩)
    (fun j => ⟨r + (j : ℕ), Nat.add_lt_add_left j.isLt r⟩)

theorem commonIdx_injective {ι : Type*} (r m : ℕ) (c : ι → Fin r)
    (hc : Function.Injective c) : Function.Injective (commonIdx r m c) := by
  intro p q h
  rcases p with a | i <;> rcases q with b | j
  · simp only [commonIdx, Sum.elim_inl, Fin.mk.injEq] at h
    exact congrArg Sum.inl (hc (Fin.ext h))
  · simp only [commonIdx, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h
    have := (c a).isLt; omega
  · simp only [commonIdx, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h
    have := (c b).isLt; omega
  · simp only [commonIdx, Sum.elim_inr, Fin.mk.injEq] at h
    exact congrArg Sum.inr (Fin.ext (by omega))

theorem fullN_common_const {ι : Type} [Fintype ι] [DecidableEq ι]
    (Fr : Frame) (r m : ℕ) (c : ι → Fin r) (hc : Function.Injective c) :
    FullN Fr (fun a => (c a : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
      (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Fr.const : ℝ) =
      Matrix.of fun p q => Fr.Tent (Decay.xnode r (commonIdx r m c p))
        (Decay.ynode r (commonIdx r m c q)) := by
  have hxj : ∀ j : ℕ, Decay.xnode r (r + j) = r + 2 * j := fun j => by simp [Decay.xnode]
  have hyj : ∀ j : ℕ, Decay.ynode r (r + j) = r + 2 * j + 1 := fun j => by simp [Decay.ynode]
  ext p q
  rcases p with a | i <;> rcases q with b | j
  · have he : ((c a : ℕ) = (c b : ℕ)) ↔ a = b :=
      ⟨fun h => hc (Fin.ext h), fun h => by rw [h]⟩
    simp [FullN, Blk, blkA, Matrix.fromBlocks, Matrix.one_apply, commonIdx,
      Decay.xnode_lt r (c a).isLt, Decay.ynode_lt r (c b).isLt, Frame.Tent, he, add_comm]
  · have hne : (c a : ℕ) ≠ r + 2 * (j : ℕ) + 1 := by have := (c a).isLt; omega
    simp [FullN, Blk, blkB, Matrix.fromBlocks, commonIdx,
      Decay.xnode_lt r (c a).isLt, hyj, Frame.Tent, hne]
  · have hne : r + 2 * (i : ℕ) ≠ (c b : ℕ) := by have := (c b).isLt; omega
    simp [FullN, Blk, blkC, Matrix.fromBlocks, commonIdx,
      Decay.ynode_lt r (c b).isLt, hxj, Frame.Tent, hne]
  · have hne : r + 2 * (i : ℕ) ≠ r + 2 * (j : ℕ) + 1 := by omega
    simp [FullN, Blk, blkD, Matrix.fromBlocks, commonIdx, hxj, hyj, Frame.Tent, hne]


variable (Fr : Frame) (r m : ℕ)

theorem fullPoly_eq_FullN :
    Fr.fullPoly r m = (FullN Fr (fun c : Fin r => (c : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
      (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det := by
  unfold Frame.fullPoly
  congr 1
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [FullN, Blk, blkA, blkB, blkC, blkD, Matrix.fromBlocks, Matrix.one_apply,
      Frame.hybRow, Frame.hybCol, Matrix.of_apply, add_comm]

theorem aeval_fullPoly (x : ℝ) :
    Polynomial.aeval x (Fr.fullPoly r m)
      = (FullN Fr (fun c : Fin r => (c : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
          (fun i : Fin m => r + 2 * (i : ℕ) + 1) x).det := by
  rw [fullPoly_eq_FullN]
  have h2 : (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] ℝ)
      (FullN Fr (fun c : Fin r => (c : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det
      = ((FullN Fr (fun c : Fin r => (c : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).map
          (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] ℝ)).det :=
    map_det' (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] ℝ).toRingHom _
  rw [h2, map_fullN]

/-- The embedding of the node index set `S ⊕ Fin m` into `Fin (r + m)`. -/
def hybIdx (S : Finset (Fin r)) : (↥S ⊕ Fin m) → Fin (r + m) :=
  Sum.elim (fun a => ⟨((a.1 : Fin r) : ℕ), Nat.lt_of_lt_of_le a.1.isLt (Nat.le_add_right r m)⟩)
    (fun j => ⟨r + (j : ℕ), Nat.add_lt_add_left j.isLt r⟩)

theorem hybIdx_inj (S : Finset (Fin r)) : Function.Injective (hybIdx r m S) :=
  commonIdx_injective r m (fun a : S => a.1) Subtype.val_injective

theorem fullNS_eq (S : Finset (Fin r)) :
    FullN Fr (fun a : ↥S => ((a.1 : Fin r) : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ))
        (fun i : Fin m => r + 2 * (i : ℕ) + 1) (Fr.const : ℝ)
      = Matrix.of fun p q => Fr.Tent (Decay.xnode r (hybIdx r m S p)) (Decay.ynode r (hybIdx r m S q)) :=
  fullN_common_const Fr r m (fun a : S => a.1) Subtype.val_injective

end CatalanCore.Rect
