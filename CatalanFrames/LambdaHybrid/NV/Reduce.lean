module

public import CatalanFrames.LambdaHybrid.NV.Schur
public import CatalanCore.Rect.Geometry
public import CatalanCore.NV.ModL

/-!
# Generic mod-`ℓ` reduction of `Full(x)` for a hybrid geometry (DO Prop 1.3, frame-generic)

Everything here is parametrised by a `Frame` `Fr`, a prime `ℓ` and a threshold `K` (the first
`ℓ`-singular node index: `4K - 1 = ℓ` for λ).  The frame/prime-class specific input is packaged
in `ModData Fr ℓ K`: the node-level `ℓ`-integrality of the `Dq`-scaled entries with their
reductions, the low block `A`, and the harmonic identity `A = κ (W_all W_allᵀ + h)` (DO Lemma 1.2
at `h = ℓ`).  The λ values are supplied by `NV/LamData.lean`.
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

/-- scale factor: `1` on low nodes `p < K`, `ℓ` on high nodes -/
def Dq (ℓ K p : ℕ) : ℚ := if p < K then 1 else ℓ

/-- Frame/prime-class data for the mod-`ℓ` reduction. `t`: cross coefficient, `d`: high diagonal,
`κ`: harmonic scale, `h`: harmonic constant. -/
structure ModData (Fr : Frame) (ℓ K : ℕ) [Fact ℓ.Prime] where
  t : ZMod ℓ
  d : ZMod ℓ
  κ : ZMod ℓ
  h : ZMod ℓ
  A : Matrix (Fin K) (Fin K) (ZMod ℓ)
  ht : t ≠ 0
  hd : d ≠ 0
  hκ : κ ≠ 0
  htk : t * t = -d * κ
  low : ∀ (a a' : Fin K) {e : ℚ} {eb : ZMod ℓ}, Good ℓ e eb →
    Good ℓ (Dq ℓ K a * Dq ℓ K a' * (e + Fr.Mn a a')) (eb + A a a')
  lh : ∀ p q : ℕ, p < K → K ≤ q → q < ℓ →
    Good ℓ (Dq ℓ K p * Dq ℓ K q * (0 + Fr.Mn p q)) (-(t * (1 / ((p : ZMod ℓ) - q))))
  hl : ∀ p q : ℕ, K ≤ p → p < ℓ → q < K →
    Good ℓ (Dq ℓ K p * Dq ℓ K q * (0 + Fr.Mn p q)) (-(t * (1 / ((q : ZMod ℓ) - p))))
  hhOff : ∀ p q : ℕ, K ≤ p → p < ℓ → K ≤ q → q < ℓ → p ≠ q →
    Good ℓ (Dq ℓ K p * Dq ℓ K q * (0 + Fr.Mn p q)) 0
  hhDiag : ∀ p : ℕ, K ≤ p → p < ℓ → ∀ {e : ℚ} {eb : ZMod ℓ}, Good ℓ e eb →
    Good ℓ (Dq ℓ K p * Dq ℓ K p * (e + Fr.Mn p p)) (-d)
  harm : ∀ a a' : Fin K, A a a' = κ * ((if a = a' then h else 0) +
    ∑ n ∈ Ico K ℓ, (1 / (((a : ℕ) : ZMod ℓ) - n)) * (1 / (((a' : ℕ) : ZMod ℓ) - n)))

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

section YGood

variable {ℓ K : ℕ} [Fact ℓ.Prime]

/-- row node / column node of the `FullN` index. -/
noncomputable def rn (G : Geometry) : G.C ⊕ Fin G.k → ℕ := Sum.elim (fun a : G.C => (a : ℕ)) G.xs
noncomputable def cn (G : Geometry) : G.C ⊕ Fin G.k → ℕ := Sum.elim (fun a : G.C => (a : ℕ)) G.ys

/-- the negated, `D`-scaled hybrid matrix. -/
noncomputable def Ncell (Fr : Frame) (ℓ K : ℕ) (G : Geometry) (x : ℚ) :
    Matrix (G.C ⊕ Fin G.k) (G.C ⊕ Fin G.k) ℚ :=
  Matrix.of fun i j => -(Dq ℓ K (rn G i) * Dq ℓ K (cn G j) * G.Full Fr x i j)

lemma xs_mem (G : Geometry) (i : Fin G.k) : G.xs i ∈ G.X' := Finset.orderEmbOfFin_mem _ _ _
lemma ys_mem (G : Geometry) (i : Fin G.k) : G.ys i ∈ G.Y' := Finset.orderEmbOfFin_mem _ _ _

end YGood

end CatalanFrames.LambdaHybrid.NV
