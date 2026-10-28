module

public import CatalanCore.Uniform.Content.Wire.Shape
public import CatalanCore.Uniform.Content.Layers.DelWitness

@[expose] public section

/-!
# M3D as a `DebitLayer` of a hybrid-shaped block geometry (lane H6, task 4)

H4's `M3D_debit` is stated for the deletion member with core `{c : Fin r // c ∉ I}` and border
`r + 2i`, `r + 2j + 1`.  Here the member `(r, S)` of `G.family` (retained set `S ⊆ C_r`, with
`C_r = [0, r)` by `HybShape`) is relabelled onto that model (`fullN_reindex`), giving a debit-0
layer `m3dLayer` for the window `m3dValid`.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Arith
  CatalanCore.Arith.Hybrid.ChainClasses CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.Wire

variable {ι ι' κ : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype κ] [DecidableEq κ]

/-- Reindexing the common nodes by an equivalence conjugates `FullN`. -/
theorem fullN_reindex (Fr : Frame) (c : ι → ℕ) (c' : ι' → ℕ) (f : ι' ≃ ι)
    (hf : ∀ a, c' a = c (f a)) (xs ys : κ → ℕ) :
    FullN Fr c' xs ys (X : ℚ[X]) =
      (FullN Fr c xs ys (X : ℚ[X])).submatrix (Equiv.sumCongr f (Equiv.refl κ))
        (Equiv.sumCongr f (Equiv.refl κ)) := by
  ext i j
  rcases i with a | a <;> rcases j with b | b <;>
    simp [FullN, Blk, blkA, blkB, blkC, blkD, Matrix.one_apply, hf, f.injective.eq_iff]

theorem det_fullN_reindex (Fr : Frame) (c : ι → ℕ) (c' : ι' → ℕ) (f : ι' ≃ ι)
    (hf : ∀ a, c' a = c (f a)) (xs ys : κ → ℕ) :
    (FullN Fr c' xs ys (X : ℚ[X])).det = (FullN Fr c xs ys (X : ℚ[X])).det := by
  rw [fullN_reindex Fr c c' f hf xs ys]
  exact Matrix.det_submatrix_equiv_self (Equiv.sumCongr f (Equiv.refl κ)) _

/-- The window of M3D at `(r, p)`: all hypotheses of `M3D_debit` for the geometry with
`m = (G.geometry r).k`, with the witness segment `[a r p, b r p)`. -/
def m3dValid (G : BlockGeom) (Fr : Frame) (a b : ℕ → ℕ → ℕ) (r p : ℕ) : Prop :=
  HybShape G r ∧ ∀ [Fact p.Prime], ∃ D : PoleData Fr p (r + 2 * (G.geometry r).k),
    r + 2 * (G.geometry r).k < p * p ∧
    r ≤ a r p ∧ a r p ≤ b r p ∧ b r p ≤ r + 2 * (G.geometry r).k ∧ b r p ≤ r + p ∧
    max (a r p) (r + 2 * (G.geometry r).k - p) ≤ b r p ∧
    ∀ x y : ℕ, a r p ≤ x → x < b r p → a r p ≤ y → y < b r p →
      NoCut (Cut p r D.singular) (min (x : ℤ) y) (max (x : ℤ) y)

/-- The full-member price `P3 = 2r + (2m - (b - a'))` of M3D. -/
def m3dBase (G : BlockGeom) (a b : ℕ → ℕ → ℕ) (r p : ℕ) : ℕ :=
  2 * r + (2 * (G.geometry r).k - (b r p - max (a r p) (r + 2 * (G.geometry r).k - p)))

/-- **M3D layer (debit 0).** -/
noncomputable def m3dLayer (G : BlockGeom) (Fr : Frame) (depth : ℕ) (a b : ℕ → ℕ → ℕ) :
    DebitLayer G Fr depth where
  base := m3dBase G a b
  debit := 0
  valid := m3dValid G Fr a b
  gle := by
    intro i _ p hp hv
    rcases i with ⟨r, S⟩
    obtain ⟨hs, hv⟩ := hv
    obtain ⟨D, hN, h1, h2, h3, h4, h5, hcut⟩ := hv
    have hCmem : ∀ x : (G.geometry r).C, x.1 < r := by
      intro x
      have h : x.1 ∈ Finset.range r := by
        rw [← hs.C_eq]; exact x.2
      exact Finset.mem_range.mp h
    -- the deleted set of residues of the member
    let I : Finset ℕ := (Finset.range r).filter (fun x => ∀ s ∈ S, s.1 ≠ x)
    have hI : ∀ u ∈ I, u < r := fun u hu => Finset.mem_range.mp (Finset.mem_filter.mp hu).1
    have hM := Layers.Del.M3D_debit D hN I hI h1 h2 h3 h4 h5 hcut
    have hxs : (G.geometry r).xs = fun i : Fin (G.geometry r).k => r + 2 * i.val := funext hs.xs_eq
    have hys : (G.geometry r).ys = fun i : Fin (G.geometry r).k => r + 2 * i.val + 1 :=
      funext hs.ys_eq
    have hnI : ∀ c : Fin r, c.val ∉ I → ∃ s ∈ S, s.1 = c.val := by
      intro c hc
      by_contra hne
      push Not at hne
      exact hc (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr c.isLt, hne⟩)
    have hmemI : ∀ s ∈ S, s.1 ∉ I := by
      intro s hsS hsI
      exact (Finset.mem_filter.mp hsI).2 s hsS rfl
    -- relabel the retained set onto the subtype model
    let f : {c : Fin r // c.val ∉ I} ≃ S :=
      { toFun := fun c => ⟨(hnI c.1 c.2).choose, (hnI c.1 c.2).choose_spec.1⟩
        invFun := fun s => ⟨⟨s.1.1, hCmem s.1⟩, hmemI s.1 s.2⟩
        left_inv := fun c => Subtype.ext (Fin.ext (hnI c.1 c.2).choose_spec.2)
        right_inv := fun s => Subtype.ext (Subtype.ext
          (hnI ⟨s.1.1, hCmem s.1⟩ (hmemI s.1 s.2)).choose_spec.2) }
    have hdet := det_fullN_reindex Fr (fun a : S => ((a.1 : (G.geometry r).C) : ℕ))
      (fun i : {c : Fin r // c.val ∉ I} => i.1.val) f (fun a => by
        have := (hnI a.1 a.2).choose_spec.2
        exact this.symm)
      (G.geometry r).xs (G.geometry r).ys
    change GLE p (m3dBase G a b r p + 0 * delCount G ⟨r, S⟩)
      (Rect.FullN Fr (fun a : S => ((a.1 : (G.geometry r).C) : ℕ)) (G.geometry r).xs
        (G.geometry r).ys (X : ℚ[X])).det
    rw [← hdet, hxs, hys, zero_mul, add_zero]
    exact hM.mono (Nat.sub_le _ _)

end CatalanCore.Uniform.Content.Wire
