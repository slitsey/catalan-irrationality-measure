module

public import CatalanCore.Arith.Hybrid.DefRank
public import CatalanCore.Arith.Hybrid.RankWit
public import CatalanCore.Rect.BorderFull

@[expose] public section

/-!
# The bordered deficit interface `DefHypTop` (MEM2C)

For a `HybInst I`, the second member `afterTop r m` has the determinant
`(afterTop r m).fullPolyG Fr` = `det` of `Frame.fullPoly r m`'s matrix bordered by the node
`r + 2m`.  This file defines

* `topW I r m p` : a `p`-adic weight bounding the border entries (`cOf` plus the maximal level
  weight of the pair `(a, r+2m)`), `topC := 2 topW + 1` the total cost of the border;
* `gle_fullTop_of_rank'` : the rank principle for the bordered determinant, in the form
  `GLE p (∑u + ∑v - k + topC)`: **the drop-in replacement of `gle_full_of_rank`**, with the same
  hypotheses `(u, v, Bbar, hB, k, hrk)`;
* `fullTop_gle` : the tropical bound `GLE p (tropExp + topC)`;
* `DefHypTop T δ` : the bordered twin of `DefHypT T δ`, with `defHypTop_of_local`, `.add`, `.mono_T`.
-/

open Polynomial Finset CatalanCore.Basic CatalanCore.Rect

namespace CatalanCore.Arith.Hybrid

section Top

variable {Fr : Frame} (I : HybInst Fr) (r m : ℕ)

/-- Border weight at the prime `p`. -/
noncomputable def topW (p : ℕ) : ℕ :=
  cOf I p + (Finset.range (r + 2 * m + 1)).sup (fun a => levels I.lev p (Elev I r m) a (r + 2 * m))

/-- Total cost of the border (`2 topW` for the weights, `+1` for the rank). -/
noncomputable def topC (p : ℕ) : ℕ := topW I r m p + topW I r m p + 1

lemma levels_comm' (lev : ℕ → ℕ → ℕ) (p E A B : ℕ) :
    levels lev p E A B = levels lev p E B A := by
  unfold levels; exact Finset.sum_congr rfl fun e _ => wt_comm _ _ _ _

variable (p : ℕ) [Fact p.Prime]

lemma topW_ge {a : ℕ} (ha : a ≤ r + 2 * m) :
    cOf I p + levels I.lev p (Elev I r m) a (r + 2 * m) ≤ topW I r m p := by
  unfold topW
  have := Finset.le_sup (f := fun a => levels I.lev p (Elev I r m) a (r + 2 * m))
    (Finset.mem_range.2 (show a < r + 2 * m + 1 by omega))
  omega

lemma gle_entry_top {a : ℕ} (ha : a ≤ r + 2 * m) :
    GLE p (topW I r m p) (C (Fr.Mn a (r + 2 * m))) := by
  have := entry_gle I p (cOf I p) (cOf_mem I p) (Elev_lt I p (Fact.out : p.Prime).two_le r m).1
    (Elev_lt I p (Fact.out : p.Prime).two_le r m).2 ha (le_refl (r + 2 * m))
  exact (GLE.C_iff.2 this).mono (topW_ge I r m p ha)

lemma gle_top_entry {a : ℕ} (ha : a ≤ r + 2 * m) :
    GLE p (topW I r m p) (C (Fr.Mn (r + 2 * m) a)) := by
  have := entry_gle I p (cOf I p) (cOf_mem I p) (Elev_lt I p (Fact.out : p.Prime).two_le r m).1
    (Elev_lt I p (Fact.out : p.Prime).two_le r m).2 (le_refl (r + 2 * m)) ha
  rw [levels_comm'] at this
  exact (GLE.C_iff.2 this).mono (topW_ge I r m p ha)

/-- **Rank principle for the bordered determinant** (drop-in replacement of `gle_full_of_rank`). -/
theorem gle_fullTop_of_rank' (u v : Fin r ⊕ Fin m → ℕ)
    (Bbar : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) (RatFunc (ZMod p)))
    (hB : ∀ a b, ∃ g : (LocRing p)[X],
      toQ p g = C ((p : ℚ) ^ (u a + v b)) * fullEntry Fr r m a b ∧ phiP p g = Bbar a b)
    (k : ℕ) (hrk : Bbar.rank + k ≤ r + m) :
    GLE p (∑ a, u a + ∑ b, v b - k + topC I r m p) ((afterTop r m).fullPolyG Fr) := by
  have h := gle_fullTop_of_rank Fr r m p u v Bbar hB k hrk (topW I r m p)
    (fun a => GLE.C_iff.1 (gle_entry_top I r m p (hybRow_le r m a)))
    (fun b => GLE.C_iff.1 (gle_top_entry I r m p (hybCol_le r m b)))
    (GLE.C_iff.1 ((gle_entry_top I r m p (le_refl _)).mono (Nat.le_add_left _ _)))
  refine h.mono ?_
  unfold topC
  omega

/-- The tropical bound for the bordered determinant. -/
theorem fullTop_gle' :
    GLE p (tropExp I r m p + (topW I r m p + topW I r m p)) ((afterTop r m).fullPolyG Fr) := by
  rw [← det_topMat]
  have h := det_gle_border p (topMat Fr r m) (hybW I r m p)
    (fun a b => by
      rw [topMat_inner]
      have h1 : GLE p (hybW I r m p a b)
          (C (Fr.Mn (Frame.hybRow r m a) (Frame.hybCol r m b))) := by
        rw [GLE.C_iff]
        exact entry_gle I p _ (cOf_mem I p) (Elev_lt I p (Fact.out : p.Prime).two_le r m).1
          (Elev_lt I p (Fact.out : p.Prime).two_le r m).2 (hybRow_le r m a) (hybCol_le r m b)
      have hX : GLE p (hybW I r m p a b) (X : ℚ[X]) := GLE.X.mono (Nat.zero_le _)
      rcases a with c | i <;> rcases b with c' | j
      · by_cases h : c = c'
        · simpa [fullEntry, h] using hX.add h1
        · simpa [fullEntry, h] using h1
      all_goals simpa [fullEntry] using h1)
    (topW I r m p)
    (fun a => by rw [topMat_row]; exact gle_entry_top I r m p (hybRow_le r m a))
    (fun b => by rw [topMat_col]; exact gle_top_entry I r m p (hybCol_le r m b))
    (by
      rw [topMat_corner]
      exact (GLE.X.mono (Nat.zero_le _)).add
        ((gle_entry_top I r m p (le_refl _)).mono (Nat.le_add_left _ _)))
  exact h

/-- The tropical bound for the bordered determinant (with the rank `+1`). -/
theorem fullTop_gle :
    GLE p (tropExp I r m p + topC I r m p) ((afterTop r m).fullPolyG Fr) :=
  (fullTop_gle' I r m p).mono (by unfold topC; omega)

theorem topW_eq_zero_of_ge (hp : p.Prime) (hb : Bnd I r m ≤ p) : topW I r m p = 0 := by
  have hnb : p ∉ I.cd.bad := by
    intro h
    have := Finset.le_sup (f := id) h
    unfold Bnd at hb
    simp at this
    omega
  unfold topW
  rw [cOf_eq_zero I hp hnb, zero_add]
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro a ha
  have haN : a ≤ r + 2 * m := by have := Finset.mem_range.1 ha; omega
  unfold levels
  rw [Finset.sum_eq_zero]
  intro e he
  refine wt_eq_zero_of_large I hp hnb (Finset.mem_Icc.1 he).1 ?_ haN le_rfl
  have : p ≤ p ^ e := Nat.le_self_pow (by have := (Finset.mem_Icc.1 he).1; omega) p
  unfold Bnd at hb
  omega

end Top

/-! ### The bordered deficit interface -/

section DefTop

variable {Fr : Frame} (I : HybInst Fr) (r m : ℕ)

/-- Bordered twin of `DefHypT`: `p^{T p - δ p + topC}` clears the denominators of
`det Full(afterTop r m)` at every prime `p < Bnd`. -/
def DefHypTop (T δ : ℕ → ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p < Bnd I r m →
    ∀ [Fact p.Prime], GLE p (T p - δ p + topC I r m p) ((afterTop r m).fullPolyG Fr)

variable {I r m}

lemma DefHypTop.mono_T {T T' δ : ℕ → ℕ} (h : DefHypTop I r m T δ)
    (hle : ∀ p, p.Prime → p < Bnd I r m → T p ≤ T' p) : DefHypTop I r m T' δ := by
  intro p hp hb _
  exact (h p hp hb).mono (by have := hle p hp hb; omega)

/-- Disjoint supports add (the bordered twin of `defHypT_add`; here the deficits only enter
through `T - δ`, so each summand needs `δ_i ≤ T`, supplied by the unbordered family). -/
lemma DefHypTop.add {T δ₁ δ₂ : ℕ → ℕ} (h1 : DefHypTop I r m T δ₁) (h2 : DefHypTop I r m T δ₂)
    (hdisj : ∀ p, p.Prime → p < Bnd I r m → δ₁ p = 0 ∨ δ₂ p = 0) :
    DefHypTop I r m T (fun p => δ₁ p + δ₂ p) := by
  intro p hp hb _
  rcases hdisj p hp hb with h | h
  · simp only [h, zero_add]; exact h2 p hp hb
  · simp only [h, add_zero]; exact h1 p hp hb

/-- Assemble from local conclusions on a set `S` of primes. -/
theorem defHypTop_of_local (T δ : ℕ → ℕ)
    (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (S : ℕ → Prop) (hδ : ∀ p, ¬ S p → δ p = 0)
    (hS : ∀ p : ℕ, p.Prime → p < Bnd I r m → S p → ∀ [Fact p.Prime],
      GLE p (T p - δ p + topC I r m p) ((afterTop r m).fullPolyG Fr)) :
    DefHypTop I r m T δ := by
  intro p hp hb _
  by_cases h : S p
  · exact hS p hp hb h
  · rw [hδ p h]
    simpa using (fullTop_gle I r m p).mono (by have := hT p hp hb; omega)

end DefTop

end CatalanCore.Arith.Hybrid

namespace CatalanCore.Arith.Hybrid

/-- **The generic bordering lemma**: a rank witness for `Full(X)` of `Frame.fullPoly r m` gives the
bordered statement for `det Full(afterTop r m)` at the cost `topC`.  This is the single place where
member 2 inherits the rank-route deficits. -/
theorem HasRankWit.border {Fr : Frame} (I : HybInst Fr) {p : ℕ} [Fact p.Prime] {r m : ℕ}
    {u v : Fin r ⊕ Fin m → ℕ} {k : ℕ} (h : HasRankWit Fr p r m u v k) :
    GLE p (∑ a, u a + ∑ b, v b - k + topC I r m p) ((afterTop r m).fullPolyG Fr) := by
  obtain ⟨Bbar, hB, hrk⟩ := h
  exact gle_fullTop_of_rank' I r m p u v Bbar hB k hrk

end CatalanCore.Arith.Hybrid
