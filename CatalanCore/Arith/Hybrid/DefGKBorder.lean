module

public import CatalanCore.Arith.Hybrid.DefGKBorderCore
public import CatalanCore.Arith.Hybrid.DefGKFam
public import CatalanCore.Arith.Hybrid.BorderDef

@[expose] public section

/-!
# GK for the second member `afterTop r m` (bordered T-route; no new entry tables)

The determinant of `Full(afterTop r m)` is the determinant of `topMat Fr r m` (`Frame.fullPoly r m`'s
matrix bordered by the node `b = r + 2m`).  Reindexing `Option (Fin r ⊕ Fin m)` as
`Fin r ⊕ Option (Fin m)` (clean block, zone, border) the inner `Fin r ⊕ Fin m` block is exactly
`Matrix.of (fullEntry Fr r m)`, so the GK data of the first member (`Atil_int`, `Atil_prim`,
`hL_bound`, `hL'_bound`, `hDelta_bound`, the partners `alphaM`, `betaM`) is reused verbatim, and
`tcore_vec_border` (generic) adds the border at the cost `2 topW`.

* `gle_fullTop_of_vec` : the bordered conclusion from the `tcore_vec` data (generic over frame data);
* `gleTop_GK1` / `gleTop_GK3` : the two GK classes, for any offset `o`;
* `defHypTop_GK_o` : GK as one `DefHypTop` family (deficit `m` on `LowCleanO`), against `T ≥ 2r + m`.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Rect Matrix
open CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanCore.Arith.Hybrid

/-- `Fin r ⊕ Option (Fin m) ≃ Option (Fin r ⊕ Fin m)` (the border is `none`). -/
def borderEquiv (r m : ℕ) : Fin r ⊕ Option (Fin m) ≃ Option (Fin r ⊕ Fin m) where
  toFun
    | Sum.inl c => some (Sum.inl c)
    | Sum.inr none => none
    | Sum.inr (some j) => some (Sum.inr j)
  invFun
    | none => Sum.inr none
    | some (Sum.inl c) => Sum.inl c
    | some (Sum.inr j) => Sum.inr (some j)
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl

section Vec

variable {Fr : Frame} (I : HybInst Fr) (r m : ℕ) (p : ℕ) [Fact p.Prime]

/-- **Bordered `tcore_vec`** for `det Full(afterTop r m)`: the `tcore_vec` data of the inner block
`Frame.fullPoly r m` (with integral partners) gives `GLE p (2r + 2 topW)`. -/
theorem gle_fullTop_of_vec
    (hI : ∀ i j, Int1 p (Atil p (fun _ : Fin r => 1) (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ i j))
    (hprim : gn p (Atil p (fun _ : Fin r => 1) (Matrix.of (fullEntry Fr r m)).toBlocks₁₁).det = 1)
    (α : Matrix (Fin m) (Fin r) ℚ[X]) (β : Matrix (Fin r) (Fin m) ℚ[X])
    (hα : ∀ z c, Int1 p (α z c)) (hβ : ∀ c y, Int1 p (β c y))
    (hL : ∀ z c, gn p (((Matrix.of (fullEntry Fr r m)).toBlocks₂₁ - α *
      (Matrix.of (fullEntry Fr r m)).toBlocks₁₁) z c) ≤ p)
    (hL' : ∀ c y, gn p (((Matrix.of (fullEntry Fr r m)).toBlocks₁₂ -
      (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ * β) c y) ≤ p)
    (hΔ : ∀ z y, Int1 p (((Matrix.of (fullEntry Fr r m)).toBlocks₂₂ -
      α * (Matrix.of (fullEntry Fr r m)).toBlocks₁₂ -
      (Matrix.of (fullEntry Fr r m)).toBlocks₂₁ * β +
      α * (Matrix.of (fullEntry Fr r m)).toBlocks₁₁ * β) z y)) :
    GLE p (2 * r + (topW I r m p + topW I r m p)) ((afterTop r m).fullPolyG Fr) := by
  classical
  rw [← det_topMat, ← Matrix.det_submatrix_equiv_self (borderEquiv r m) (topMat Fr r m)]
  have h := tcore_vec_border (p := p)
    ((topMat Fr r m).submatrix (borderEquiv r m) (borderEquiv r m))
    (Matrix.of (fullEntry Fr r m))
    (fun a b => by
      rcases a with c | j <;> rcases b with c' | j' <;>
        simp [Matrix.submatrix_apply, borderEquiv, topMat_inner])
    (topW I r m p) hI hprim α β hα hβ hL hL' hΔ
    (fun c => by
      have := gle_top_entry I r m p (hybCol_le r m (Sum.inl c))
      rw [← topMat_col] at this
      exact (int1_Cpow_iff _ _).2 this)
    (fun c => by
      have := gle_entry_top I r m p (hybRow_le r m (Sum.inl c))
      rw [← topMat_row] at this
      exact (int1_Cpow_iff _ _).2 this)
    (fun y => by
      have := gle_top_entry I r m p (hybCol_le r m (Sum.inr y))
      rw [← topMat_col] at this
      exact (int1_Cpow_iff _ _).2 this)
    (fun z => by
      have := gle_entry_top I r m p (hybRow_le r m (Sum.inr z))
      rw [← topMat_row] at this
      exact (int1_Cpow_iff _ _).2 this)
    (by
      refine (int1_Cpow_iff _ _).2 ?_
      show GLE p _ (topMat Fr r m none none)
      rw [topMat_corner]
      exact (GLE.X.mono (Nat.zero_le _)).add
        ((gle_entry_top I r m p (le_refl _)).mono (Nat.le_add_left _ _)))
  rw [Fintype.card_fin] at h
  exact h

end Vec

namespace GK1

variable {o p : ℕ} [Fact p.Prime] {k : ℕ} {Fr : Frame} {r m : ℕ}

/-- **GK (class 1) for `afterTop`.** -/
theorem gleTop_GK1 (I : HybInst Fr) (hL : LamData Fr o) (S : GKS1 o p r m k) :
    GLE p (2 * r + (topW I r m p + topW I r m p)) ((afterTop r m).fullPolyG Fr) :=
  gle_fullTop_of_vec I r m p (Atil_int hL S) (Atil_prim hL S) (alphaM Fr p r m) (betaM Fr p r m)
    (fun _ c => avec_int S.p13 S.h1009 _ c) (fun c _ => avec_int S.p13 S.h1009 _ c)
    (hL_bound hL S) (hL'_bound hL S) (hDelta_bound hL S)

end GK1

section GK3

variable {o p : ℕ} [Fact p.Prime] {k : ℕ} {Fr : Frame} {r m : ℕ}

/-- **GK (class 3) for `afterTop`.** -/
theorem gleTop_GK3 (I : HybInst Fr) (hL : LamData Fr o) (S : GKS3 o p r m k) :
    GLE p (2 * r + (topW I r m p + topW I r m p)) ((afterTop r m).fullPolyG Fr) :=
  gle_fullTop_of_vec I r m p (Atil_int hL S) (Atil_prim hL S) (alphaM Fr p r m) (betaM Fr p r m)
    (fun _ c => avec_int S.p13 S.h139 _ c) (fun c _ => avec_int S.p13 S.h139 _ c)
    (hL_bound hL S) (hL'_bound hL S) (hDelta_bound hL S)

end GK3

open Classical in
/-- **GK as a `DefHypTop` family, generic in the offset `o`**: deficit `m` on `LowCleanO`, against
any `T ≥ 2r + m` (the border costs `2 topW + 1`, absorbed by `topC`; one unit of slack). -/
theorem defHypTop_GK_o {Fr : Frame} (I : HybInst Fr) {o : ℕ} (ho : o = 1 ∨ o = 3)
    (hL : LamData Fr o) (r m : ℕ) (hm : 0 < m)
    (T : ℕ → ℕ) (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → LowCleanO o r m p → 2 * r + m ≤ T p) :
    DefHypTop I r m T (fun p => if LowCleanO o r m p then m else 0) := by
  refine defHypTop_of_local T _ hT (LowCleanO o r m) (fun p hp => by simp [hp]) ?_
  intro p hp hb hW hf
  have hd := hTd p hp hW
  have hg : GLE p (2 * r + (topW I r m p + topW I r m p)) ((afterTop r m).fullPolyG Fr) := by
    rcases hW with ⟨h13, hmod, hx, hr, hN⟩ | ⟨h13, hmod, hx, hr, hN⟩
    · exact gleTop_GK3 I hL (gks3_of ho h13 hmod hx hr hN hm)
    · exact GK1.gleTop_GK1 I hL (gks1_of ho h13 hmod hx hr hN hm)
  simp only [if_pos hW]
  refine hg.mono ?_
  unfold topC
  omega

end CatalanCore.Arith.Hybrid
