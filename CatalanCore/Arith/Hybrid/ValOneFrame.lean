module

public import CatalanCore.Arith.Hybrid.ValOne
public import CatalanCore.NV.LevelData

@[expose] public section

/-! # Frame-generic exponent-one nonvanishing

Reuse the existing level data, adding only integrality of off-diagonal mid
entries. Common nodes may be any finite set containing the low interval.
-/

open Finset Matrix CatalanCore CatalanCore.Rect CatalanCore.NV

namespace CatalanCore.Arith.Hybrid.ValOne

variable {Fr : Frame} {ℓ K T : ℕ} [Fact ℓ.Prime]

/-- The extra column multiplier: common mid columns only. -/
def colFactor (G : Geometry) : ((Fin K ⊕ HiC K G) ⊕ Fin G.k) → ℚ
  | .inl (.inr _) => ℓ
  | _ => 1

/-- Entrywise asymmetric reduction. No harmonic identity or border inverse is used. -/
theorem frame_good (D : ModData3 Fr ℓ K T)
    (hhMem : ∀ a b : ℕ, K ≤ a → a < T → K ≤ b → b < T → a ≠ b → Fr.Mn a b ∈ S ℓ)
    (G : Geometry) (hlow : ∀ n, n < K → n ∈ G.C)
    (hlt : ∀ n, n ∈ G.C ∨ n ∈ G.X' ∨ n ∈ G.Y' → n < T)
    (hhi : ∀ n, n ∈ G.X' ∨ n ∈ G.Y' → K ≤ n)
    {x : ℚ} {u : ZMod ℓ} (hx : Good ℓ ((ℓ : ℚ) * x) u)
    (i j : (Fin K ⊕ HiC K G) ⊕ Fin G.k) :
    Good ℓ ((ℓ : ℚ) * (G.Full Fr x) (eIdx K G hlow i) (eIdx K G hlow j) *
        colFactor (ℓ := ℓ) G j)
      (limit u D.d D.t (WX ℓ K G) (WY ℓ K G) (-D.t • (WC ℓ K G).transpose) i j) := by
  have hxs : ∀ i : Fin G.k, K ≤ G.xs i ∧ G.xs i < T := fun i =>
    ⟨hhi _ (Or.inl (xs_mem G i)), hlt _ (Or.inr (Or.inl (xs_mem G i)))⟩
  have hys : ∀ i : Fin G.k, K ≤ G.ys i ∧ G.ys i < T := fun i =>
    ⟨hhi _ (Or.inr (ys_mem G i)), hlt _ (Or.inr (Or.inr (ys_mem G i)))⟩
  have hCl : ∀ b : G.C, (b : ℕ) < T := fun b => hlt _ (Or.inl b.2)
  have hCH : ∀ b : HiC K G, K ≤ (b.1 : ℕ) := fun b => Nat.le_of_not_gt b.2
  have hCys : ∀ (b : G.C) (i : Fin G.k), (b : ℕ) ≠ G.ys i := fun b i h =>
    Finset.disjoint_left.1 G.disjCY b.2 (h ▸ ys_mem G i)
  have hCxs : ∀ (b : G.C) (i : Fin G.k), (b : ℕ) ≠ G.xs i := fun b i h =>
    Finset.disjoint_left.1 G.disjCX b.2 (h ▸ xs_mem G i)
  have hxy : ∀ i j : Fin G.k, G.xs i ≠ G.ys j := fun i j h =>
    Finset.disjoint_left.1 G.disjXY (xs_mem G i) (h ▸ ys_mem G j)
  have hoff : ∀ a b, K ≤ a → a < T → K ≤ b → b < T → a ≠ b →
      Good ℓ ((ℓ : ℚ) * Fr.Mn a b) 0 := fun a b ha ha' hb hb' hab =>
    (good_red (hhMem a b ha ha' hb hb' hab)).ell_mul
  rcases i with (a | b) | i <;> rcases j with (a' | b') | j
  · have hg := D.low a a' (Good.zero (ℓ := ℓ))
    simp only [Dq, a.2, a'.2, ite_true, one_mul, zero_add] at hg
    have hm := hg.ell_mul
    by_cases haa : a = a'
    · subst a'
      simpa [eIdx, eLow, full_ll, colFactor, limit, mul_add] using hx.add hm
    · have hval : (a : ℕ) ≠ (a' : ℕ) := fun h => haa (Fin.ext h)
      simpa [eIdx, eLow, full_ll, colFactor, limit, haa, hval] using hm
  · have hne : (a : ℕ) ≠ (b'.1 : ℕ) := by have := a.2; have := hCH b'; omega
    have hg := (D.lh a b'.1.1 a.2 (hCH b') (hCl b'.1)).ell_mul
    simpa [Dq, a.2, not_lt.mpr (hCH b'), eIdx, eLow, full_ll, colFactor,
      limit, Subtype.ext_iff, hne, mul_assoc, mul_comm, mul_left_comm] using hg
  · have hg := D.lh a (G.ys j) a.2 (hys j).1 (hys j).2
    simpa [Dq, a.2, not_lt.mpr (hys j).1, eIdx, eLow, full_lr, colFactor,
      limit, WY, Wnode, neg_mul] using hg
  · have hne : (b.1 : ℕ) ≠ (a' : ℕ) := by have := a'.2; have := hCH b; omega
    have hg := D.hl b.1.1 a' (hCH b) (hCl b.1) a'.2
    simpa [Dq, a'.2, not_lt.mpr (hCH b), eIdx, eLow, full_ll, colFactor,
      limit, WC, Wnode, Subtype.ext_iff, hne, neg_mul] using hg
  · by_cases hbb : b = b'
    · subst b'
      have hg := D.hhDiag b.1.1 (hCH b) (hCl b.1) (Good.zero (ℓ := ℓ))
      have he := hx.ell_mul
      simp only [Dq, not_lt.mpr (hCH b), ite_false, zero_add] at hg
      have hall := he.add hg
      convert hall using 1 <;> simp [eIdx, eLow, full_ll, colFactor, limit] <;> ring
    · have hne : (b.1 : ℕ) ≠ (b'.1 : ℕ) := fun h => hbb (Subtype.ext (Subtype.ext h))
      have hne' : b.1 ≠ b'.1 := fun h => hne (congrArg Subtype.val h)
      have hg := D.hhOff b.1.1 b'.1.1 (hCH b) (hCl b.1) (hCH b') (hCl b'.1) hne
      simpa [Dq, not_lt.mpr (hCH b), not_lt.mpr (hCH b'), eIdx, eLow,
        full_ll, colFactor, limit, hbb, hne', mul_assoc, mul_comm, mul_left_comm] using hg
  · have hg := hoff b.1.1 (G.ys j) (hCH b) (hCl b.1) (hys j).1 (hys j).2 (hCys b.1 j)
    simpa [eIdx, eLow, full_lr, colFactor, limit] using hg
  · have hg := D.hl (G.xs i) a' (hxs i).1 (hxs i).2 a'.2
    simpa [Dq, a'.2, not_lt.mpr (hxs i).1, eIdx, eLow, full_rl, colFactor,
      limit, WX, Wnode, neg_mul] using hg
  · have hg := D.hhOff (G.xs i) b'.1.1 (hxs i).1 (hxs i).2 (hCH b') (hCl b'.1)
      (Ne.symm (hCxs b'.1 i))
    simpa [Dq, not_lt.mpr (hxs i).1, not_lt.mpr (hCH b'), eIdx, eLow,
      full_rl, colFactor, limit, mul_assoc, mul_comm, mul_left_comm] using hg
  · have hg := hoff (G.xs i) (G.ys j) (hxs i).1 (hxs i).2 (hys j).1 (hys j).2 (hxy i j)
    simpa [eIdx, eLow, full_rr, colFactor, limit] using hg

/-- Full determinant nonvanishing for any admissible mid-level common-node set. -/
theorem frame_det_ne_zero (D : ModData3 Fr ℓ K T)
    (hhMem : ∀ a b : ℕ, K ≤ a → a < T → K ≤ b → b < T → a ≠ b → Fr.Mn a b ∈ S ℓ)
    (G : Geometry) (hlow : ∀ n, n < K → n ∈ G.C)
    (hlt : ∀ n, n ∈ G.C ∨ n ∈ G.X' ∨ n ∈ G.Y' → n < T)
    (hhi : ∀ n, n ∈ G.X' ∨ n ∈ G.Y' → K ≤ n)
    (hGram : ((WX ℓ K G).transpose * WY ℓ K G).det ≠ 0)
    {x : ℚ} {u : ZMod ℓ} (hx : Good ℓ ((ℓ : ℚ) * x) u) (hu : u ≠ 0) :
    (G.Full Fr x).det ≠ 0 := by
  have h := det_ne_zero_of_good
    ((G.Full Fr x).submatrix (eIdx K G hlow) (eIdx K G hlow))
    (fun _ => (ℓ : ℚ)) (colFactor (ℓ := ℓ) G) u D.d D.t (WX ℓ K G) (WY ℓ K G)
    (-D.t • (WC ℓ K G).transpose) hu D.hd D.ht hGram
    (frame_good D hhMem G hlow hlt hhi hx)
  rwa [Matrix.det_submatrix_equiv_self] at h

end CatalanCore.Arith.Hybrid.ValOne

#print axioms CatalanCore.Arith.Hybrid.ValOne.frame_det_ne_zero
