module

public import CatalanCore.Rect.Geometry
public import CatalanCore.NV.ModL

@[expose] public section

/-! # Frame-independent low/common/border reduction geometry

Shared node scalings, Cauchy columns and reindexing for arbitrary common sets.
The compatibility frame modules re-export these definitions.
-/
open Finset Matrix CatalanCore CatalanCore.Rect
namespace CatalanCore.NV

/-- scale factor: `1` on low nodes `p < K`, `ℓ` on high nodes -/
def Dq (ℓ K p : ℕ) : ℚ := if p < K then 1 else ℓ

section Setup

variable {ℓ K : ℕ} [Fact ℓ.Prime] (G : Geometry)

/-- the high common nodes -/
abbrev HiC (K : ℕ) (G : Geometry) := {b : G.C // ¬ (b : ℕ) < K}

/-- `Cauchy` column of the node `n`, indexed by the low nodes `a < K`: `1/(a - n)` in `𝔽_ℓ`. -/
noncomputable def Wnode (ℓ K : ℕ) [Fact ℓ.Prime] (n : ℕ) : Fin K → ZMod ℓ :=
  fun a => 1 / (((a : ℕ) : ZMod ℓ) - (n : ZMod ℓ))

noncomputable def WC (ℓ K : ℕ) [Fact ℓ.Prime] (G : Geometry) : Matrix (Fin K) (HiC K G) (ZMod ℓ) :=
  Matrix.of fun a b => Wnode ℓ K (b.1 : ℕ) a

noncomputable def WX (ℓ K : ℕ) [Fact ℓ.Prime] (G : Geometry) : Matrix (Fin K) (Fin G.k) (ZMod ℓ) :=
  Matrix.of fun a i => Wnode ℓ K (G.xs i) a

noncomputable def WY (ℓ K : ℕ) [Fact ℓ.Prime] (G : Geometry) : Matrix (Fin K) (Fin G.k) (ZMod ℓ) :=
  Matrix.of fun a i => Wnode ℓ K (G.ys i) a

/-- Cauchy columns of a family of (absent) nodes -/
noncomputable def Gcols (ℓ K : ℕ) [Fact ℓ.Prime] {g : Type} (nd : g → ℕ) :
    Matrix (Fin K) g (ZMod ℓ) :=
  Matrix.of fun a i => Wnode ℓ K (nd i) a

/-- the low common nodes are `Fin K` -/
def eLow (K : ℕ) (G : Geometry) (hlow : ∀ n, n < K → n ∈ G.C) :
    Fin K ≃ {b : G.C // (b : ℕ) < K} where
  toFun a := ⟨⟨a, hlow a a.2⟩, a.2⟩
  invFun b := ⟨b.1.1, b.2⟩
  left_inv a := rfl
  right_inv b := rfl

def eIdx (K : ℕ) (G : Geometry) (hlow : ∀ n, n < K → n ∈ G.C) :
    (Fin K ⊕ HiC K G) ⊕ Fin G.k ≃ G.C ⊕ Fin G.k :=
  Equiv.sumCongr ((Equiv.sumCongr (eLow K G hlow) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun b : G.C => (b : ℕ) < K))) (Equiv.refl _)

end Setup

section Entries

variable (Fr : Frame)

lemma full_ll (G : Geometry) (x : ℚ) (a b : G.C) :
    G.Full Fr x (Sum.inl a) (Sum.inl b) = (if a = b then x else 0) + Fr.Mn a b := by
  simp [Geometry.Full, FullN, Blk, blkA, Matrix.one_apply, add_comm]

lemma full_lr (G : Geometry) (x : ℚ) (a : G.C) (j : Fin G.k) :
    G.Full Fr x (Sum.inl a) (Sum.inr j) = 0 + Fr.Mn a (G.ys j) := by
  simp [Geometry.Full, FullN, Blk, blkB]

lemma full_rl (G : Geometry) (x : ℚ) (i : Fin G.k) (b : G.C) :
    G.Full Fr x (Sum.inr i) (Sum.inl b) = 0 + Fr.Mn (G.xs i) b := by
  simp [Geometry.Full, FullN, Blk, blkC]

lemma full_rr (G : Geometry) (x : ℚ) (i j : Fin G.k) :
    G.Full Fr x (Sum.inr i) (Sum.inr j) = 0 + Fr.Mn (G.xs i) (G.ys j) := by
  simp [Geometry.Full, FullN, Blk, blkD]

end Entries

lemma xs_mem (G : Geometry) (i : Fin G.k) : G.xs i ∈ G.X' := Finset.orderEmbOfFin_mem _ _ _
lemma ys_mem (G : Geometry) (i : Fin G.k) : G.ys i ∈ G.Y' := Finset.orderEmbOfFin_mem _ _ _

end CatalanCore.NV
