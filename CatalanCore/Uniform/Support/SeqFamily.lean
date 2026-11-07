module

public import CatalanCore.Rect.PairFam
public import CatalanCore.Uniform.Frame.Block

@[expose] public section

/-!
# The Löwner family of two sequences (lane H, wave H2; ledger S02)

For sequences `f g : ℕ → ℚ` (for a support datum: `f_t = ∑_{k<t} δ(k)`, `g_t = e_t`) the Löwner entry is
`lw f g a b = (f b - f a)/(b - a)` for `a ≠ b` and `-g a` for `a = b`.  `seqFullN f g c xs ys x` is the
hybrid block matrix on common nodes `c`, row nodes `xs`, column nodes `ys`, with `x` added at the common
diagonal: `Rect.Blk` of the four blocks, exactly as `Rect.FullN` is for a `Frame`, and `Rect.FullN Fr`
is `seqFullN` of the frame's own sequences.

`seqFamily f g const G depth` is the `PolyFamily` of the minors `det seqFullN … X` over the retained common
nodes of the node geometry `G` (`NodeFamily`), in the same indexing as `NodeFamily.family`.  Nothing here
depends on the datum: the minors are of the matrix of any two sequences.
-/

open Polynomial Finset Matrix

namespace CatalanCore.Uniform.Support

open CatalanCore CatalanCore.Rect

/-- The Löwner entry of the sequences `(f, g)`. -/
def lw (f g : ℕ → ℚ) (a b : ℕ) : ℚ := if a = b then -g a else (f b - f a) / ((b : ℚ) - a)

section Def

variable {R : Type*} [CommRing R] [Algebra ℚ R]
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The hybrid block matrix of `(f, g)`: Löwner entries on rows `c ⊔ xs`, columns `c ⊔ ys`, with `x` added
at the cells `(a, a)`, `a` a common node. -/
def seqFullN (f g : ℕ → ℚ) (c : ι → ℕ) (xs ys : κ → ℕ) (x : R) : Matrix (ι ⊕ κ) (ι ⊕ κ) R :=
  Blk (Matrix.of fun a b => algebraMap ℚ R (lw f g (c a) (c b)))
    (Matrix.of fun a j => algebraMap ℚ R (lw f g (c a) (ys j)))
    (Matrix.of fun i b => algebraMap ℚ R (lw f g (xs i) (c b)))
    (Matrix.of fun i j => algebraMap ℚ R (lw f g (xs i) (ys j))) x

end Def

section Basic

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem natDegree_seqFullN_entry_le (f g : ℕ → ℚ) (c : ι → ℕ) (xs ys : κ → ℕ) (a b : ι ⊕ κ) :
    ((seqFullN f g c xs ys (X : ℚ[X])) a b).natDegree ≤ (if b.isLeft then 1 else 0) := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp [seqFullN, Blk, Matrix.fromBlocks, Matrix.one_apply]
  split_ifs <;> simp

/-- `deg det seqFullN(X) ≤ |ι|`. -/
theorem natDegree_seqFullN_le (f g : ℕ → ℚ) (c : ι → ℕ) (xs ys : κ → ℕ) :
    (seqFullN f g c xs ys (X : ℚ[X])).det.natDegree ≤ Fintype.card ι := by
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun σ _ => ?_)
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ i, ((seqFullN f g c xs ys (X : ℚ[X])) (σ i) i).natDegree
      ≤ ∑ i : ι ⊕ κ, (if i.isLeft then 1 else 0) :=
        Finset.sum_le_sum (fun i _ => natDegree_seqFullN_entry_le f g c xs ys (σ i) i)
    _ = Fintype.card ι := by
        rw [Fintype.sum_sum_type]
        simp

/-- Evaluating `seqFullN … X` at `x` gives `seqFullN … x`. -/
theorem seqFullN_map_eval (f g : ℕ → ℚ) (c : ι → ℕ) (xs ys : κ → ℕ) (x : ℚ) :
    (Polynomial.evalRingHom x).mapMatrix (seqFullN f g c xs ys (X : ℚ[X])) = seqFullN f g c xs ys x := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [seqFullN, Blk, Matrix.fromBlocks, Matrix.one_apply]
  by_cases h : a = b <;> simp [h]

theorem seqFullN_map_aeval (f g : ℕ → ℚ) (c : ι → ℕ) (xs ys : κ → ℕ) (x : ℝ) :
    (seqFullN f g c xs ys (X : ℚ[X])).map (Polynomial.aeval x : ℚ[X] →ₐ[ℚ] ℝ)
      = seqFullN f g c xs ys x := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [seqFullN, Blk, Matrix.fromBlocks, Matrix.one_apply]
  by_cases h : a = b <;> simp [h]

end Basic

/-! ### The family -/

namespace SeqFamily

open CatalanCore.Uniform

/-- The minor polynomial of the member `i = (r, S)`. -/
noncomputable def poly (f g : ℕ → ℚ) (G : NodeFamily) (i : G.Index) : ℚ[X] :=
  (seqFullN f g (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ)) (G i.1).xs (G i.1).ys (X : ℚ[X])).det

end SeqFamily

/-- The family of the Löwner minors of `(f, g)` over the retained common nodes of `G`: the member
`(r, S)` has degree budget `|S|` and is admissible when at most `depth` common nodes are deleted
(S02). -/
noncomputable abbrev seqFamily (f g : ℕ → ℚ) (const : ℝ) (G : NodeFamily) (depth : ℕ) : PolyFamily where
  const := const
  ι := G.Index
  deg := fun i => i.2.card
  Adm := fun i => (G i.1).C.card - i.2.card ≤ depth
  Q := SeqFamily.poly f g G

namespace SeqFamily

/-- Scale of a member: the scale index `r`. -/
abbrev scale (G : NodeFamily) (i : G.Index) : ℕ := i.1

variable (f g : ℕ → ℚ) (const : ℝ) (G : NodeFamily) (depth : ℕ)

theorem poly_natDegree (i : G.Index) : (poly f g G i).natDegree ≤ i.2.card := by
  simpa [poly] using natDegree_seqFullN_le f g (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ)) (G i.1).xs (G i.1).ys

/-- Degree bound of the family. -/
theorem family_degree (i : (seqFamily f g const G depth).ι) :
    ((seqFamily f g const G depth).Q i).natDegree ≤ (seqFamily f g const G depth).deg i :=
  poly_natDegree f g G i

theorem deg_le_common (i : (seqFamily f g const G depth).ι) :
    (seqFamily f g const G depth).deg i ≤ (G i.1).C.card := by
  simpa using Finset.card_le_univ i.2

/-- Rational evaluation is the determinant of the actual Löwner matrix. -/
theorem evalQ_poly (i : (seqFamily f g const G depth).ι) (x : ℚ) :
    (seqFamily f g const G depth).evalQ i x =
      (seqFullN f g (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ)) (G i.1).xs (G i.1).ys x).det := by
  change (poly f g G i).eval x = _
  unfold poly
  have h := (Polynomial.evalRingHom x).map_det
    (seqFullN f g (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ)) (G i.1).xs (G i.1).ys (X : ℚ[X]))
  rw [seqFullN_map_eval] at h
  exact h

/-- Real evaluation uses the same matrix and normalization. -/
theorem evalR_poly (i : (seqFamily f g const G depth).ι) (x : ℝ) :
    (seqFamily f g const G depth).evalR i x =
      (seqFullN f g (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ)) (G i.1).xs (G i.1).ys x).det := by
  change Polynomial.aeval x (poly f g G i) = _
  unfold poly
  have h := (Polynomial.aeval x).toRingHom.map_det
    (seqFullN f g (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ)) (G i.1).xs (G i.1).ys (X : ℚ[X]))
  change Polynomial.aeval x
      (seqFullN f g (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ)) (G i.1).xs (G i.1).ys (X : ℚ[X])).det =
    ((seqFullN f g (fun a : i.2 => ((a.1 : (G i.1).C) : ℕ)) (G i.1).xs (G i.1).ys
      (X : ℚ[X])).map (Polynomial.aeval x)).det at h
  rw [seqFullN_map_aeval] at h
  exact h

/-- The selector adapter: nonvanishing minors of bounded deletion give `HasNV0`. -/
theorem hasNV0_of_minors (R0 : ℕ)
    (hnv : ∀ r, R0 ≤ r → ∀ x : ℚ, ∃ S : Finset (G r).C,
      (G r).C.card - S.card ≤ depth ∧
      (seqFullN f g (fun a : S => ((a.1 : (G r).C) : ℕ)) (G r).xs (G r).ys x).det ≠ 0) :
    HasNV0 (seqFamily f g const G depth) (scale G) := by
  refine ⟨R0, ?_⟩
  intro r hr x
  obtain ⟨S, hS, hdet⟩ := hnv r hr x
  refine ⟨⟨r, S⟩, hS, rfl, ?_⟩
  rw [evalQ_poly]
  exact hdet

end SeqFamily

/-- The Löwner family over a periodic block geometry: scale and degree bound as for `BlockGeom.family`. -/
noncomputable abbrev _root_.CatalanCore.Uniform.BlockGeom.seqFamily (B : BlockGeom) (f g : ℕ → ℚ) (const : ℝ) (depth : ℕ) :
    PolyFamily :=
  CatalanCore.Uniform.Support.seqFamily f g const B.geometry depth

theorem _root_.CatalanCore.Uniform.BlockGeom.seq_degree_bound (B : BlockGeom) (f g : ℕ → ℚ) (const : ℝ) (depth : ℕ)
    (i : (B.seqFamily f g const depth).ι) :
    ((B.seqFamily f g const depth).deg i : ℝ) ≤ (B.common.mass : ℝ) * (SeqFamily.scale B.geometry i) +
      B.common.n := by
  have hd := SeqFamily.deg_le_common f g const B.geometry depth i
  have hc := (B.card_common i.1).2
  have hdc : ((B.seqFamily f g const depth).deg i : ℚ) ≤ (B.geometry i.1).C.card := by
    exact_mod_cast hd
  have : ((B.seqFamily f g const depth).deg i : ℚ) ≤ B.common.mass * (i.1 : ℚ) + B.common.n :=
    hdc.trans hc
  have h2 : (((B.seqFamily f g const depth).deg i : ℚ) : ℝ) ≤
      ((B.common.mass * (i.1 : ℚ) + B.common.n : ℚ) : ℝ) := by exact_mod_cast this
  simpa using h2

end CatalanCore.Uniform.Support
