module
public import CatalanCore.Arith.Hybrid.ShiftMember2
public import CatalanCore.Arith.Hybrid.ResponseLongChain
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid

/-! # The weight of the weighted congruence, and its zero pattern from the long responses

The weight is `w(c) = α (c̄_C - c̄(c)) + β 1_S(c)` (`zoneWeight`), `c̄_C` the response of the source
chain, `c̄(c)` the response of the chain of the residue `c` (`respAt`), `S` the short arc.
`zoneZero_of_response` proves the `zero` field of `ShiftCauchyData` from the free-long and
occupied-long response equalities (`response_long_eq_free`, `response_long_eq_occupied`), for any
`α, β`.  `WeightedSameCell` is the remaining obligation N1, stated for the whole cell. -/

open ChainClasses

section Defs
variable (Fr : Frame) (p o r : ℕ) [Fact p.Prime]

/-- Reduced response of the chain of the residue `c` (core nodes `< r` with that residue). -/
noncomputable def respAt (c : ZMod p) (A B : RatFunc (ZMod p)) : RatFunc (ZMod p) :=
  cResp Fr p o (fun i : ChainIndex p r (c.val + p * r) => (chainNode i).val) A B

/-- Source moments of the node `x`. -/
noncomputable def srcA (x : ℕ) : RatFunc (ZMod p) :=
  sourceA Fr p o (fun i : ChainIndex p r x => (chainNode i).val) x

noncomputable def srcB (x : ℕ) : RatFunc (ZMod p) :=
  sourceB Fr p o (fun i : ChainIndex p r x => (chainNode i).val) x

/-- Response of the source chain of `x`. -/
noncomputable def srcC (x : ℕ) : RatFunc (ZMod p) :=
  cResp Fr p o (fun i : ChainIndex p r x => (chainNode i).val) (srcA Fr p o r x) (srcB Fr p o r x)

/-- The short arc of `h` (the root of `4 h = o`): `[0,h)` if `2h < p`, else `[h,p)`. -/
noncomputable def shortArc (h : ℕ) : Finset (ZMod p) :=
  open Classical in Finset.univ.filter fun c => if 2 * h < p then c.val < h else h ≤ c.val

/-- The weight of the weighted congruence for the source node `x`. -/
noncomputable def zoneWeight (h x : ℕ) (α β : RatFunc (ZMod p)) (c : ZMod p) : RatFunc (ZMod p) :=
  α * (srcC Fr p o r x - respAt Fr p o r c (srcA Fr p o r x) (srcB Fr p o r x)) +
    β * (open Classical in if c ∈ shortArc p h then 1 else 0)

/-- The uncovered short residues: short, and not the residue of any node of `[r, r + 2m)`. -/
noncomputable def zoneSb (r m h : ℕ) : Finset (ZMod p) :=
  open Classical in (shortArc p h).filter fun c => ¬ ∃ k, r ≤ k ∧ k < r + 2 * m ∧ ((k : ℕ) : ZMod p) = c

/-- Rows / columns of the zone lying in the interval `[a, b)`. -/
def cellRows (r m a b : ℕ) : Finset (Fin m) :=
  open Classical in Finset.univ.filter fun i => a ≤ r + 2 * i.val ∧ r + 2 * i.val < b

def cellCols (r m a b : ℕ) : Finset (Fin m) :=
  open Classical in Finset.univ.filter fun j => a ≤ r + 2 * j.val + 1 ∧ r + 2 * j.val + 1 < b

end Defs

section Lemmas
variable {Fr : Frame} {p o r : ℕ} [Fact p.Prime]

lemma val_eq_of_natCast {k : ℕ} {c : ZMod p} (h : ((k : ℕ) : ZMod p) = c) : k % p = c.val := by
  rw [← ZMod.val_natCast, h]

lemma natCast_of_mod {k : ℕ} {c : ZMod p} (h : k % p = c.val) : ((k : ℕ) : ZMod p) = c := by
  rw [← ZMod.natCast_mod, h, ZMod.natCast_zmod_val]

/-- The response of a chain only depends on the residue. -/
lemma cResp_chain_congr {z1 z2 : ℕ} (h1 : r ≤ z1) (h2 : r ≤ z2) (hm : z1 % p = z2 % p)
    (A B : RatFunc (ZMod p)) :
    cResp Fr p o (fun i : ChainIndex p r z1 => (chainNode i).val) A B =
      cResp Fr p o (fun i : ChainIndex p r z2 => (chainNode i).val) A B := by
  obtain ⟨hi1, hr1, -⟩ := chain_family (p := p) h1
  obtain ⟨hi2, hr2, -⟩ := chain_family (p := p) h2
  unfold cResp poleRed
  exact quadraticResponse_of_range (fun i : ChainIndex p r z2 => (chainNode i).val)
    (fun i : ChainIndex p r z1 => (chainNode i).val) hi2 hi1
    (fun x => by rw [hr1, hr2, hm])
    (fun x y => rfC p (red p (poleScaledEntry Fr p o x y))) (rfX p)
    (fun x => A - B * poleL Fr p o x)

/-- A cut-free interval does not contain a multiple of `p` in its interior. -/
lemma div_eq_of_noCut {x y : ℕ} (hxy : x ≤ y)
    (h : NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (x : ℤ) (y : ℤ)) :
    x / p = y / p := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  by_contra hne
  have hle : x / p ≤ y / p := Nat.div_le_div_right hxy
  have hlt : x / p + 1 ≤ y / p := by omega
  have h1 : x < (x / p + 1) * p := by
    have := Nat.lt_div_mul_add (a := x) hp0
    nlinarith [Nat.div_add_mod x p, Nat.mod_lt x hp0]
  have h2 : (x / p + 1) * p ≤ y := by
    calc (x / p + 1) * p ≤ (y / p) * p := Nat.mul_le_mul_right p hlt
      _ ≤ y := Nat.div_mul_le_self y p
  apply h (((x / p + 1) * p : ℕ) : ℤ) (by exact_mod_cast h1) (by exact_mod_cast h2)
  exact Or.inr (Or.inl ⟨((x / p + 1 : ℕ) : ℤ), by push_cast; ring⟩)

end Lemmas

section Zero
variable {Fr : Frame} {p o r m : ℕ} [Fact p.Prime]

lemma zone_node_cases {k : ℕ} (hk : r ≤ k) (hk2 : k < r + 2 * m) :
    (∃ i : Fin m, k = r + 2 * i.val) ∨ (∃ j : Fin m, k = r + 2 * j.val + 1) := by
  by_cases he : (k - r) % 2 = 0
  · exact Or.inl ⟨⟨(k - r) / 2, by omega⟩, by simp only; omega⟩
  · exact Or.inr ⟨⟨(k - r) / 2, by omega⟩, by simp only; omega⟩

lemma nat_eq_div_mod (x : ℕ) : x = x % p + (x / p) * p := by
  have := Nat.mod_add_div x p
  rw [mul_comm] at this
  omega

lemma chain_rep_mod (c : ZMod p) : (c.val + p * r) % p = c.val := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (ZMod.val_lt c)]

lemma le_chain_rep (c : ZMod p) : r ≤ c.val + p * r := by
  have hp0 : 1 ≤ p := (Fact.out : p.Prime).pos
  nlinarith

/-- Free long residue: its chain has the source response. -/
lemma respAt_eq_srcC_free (hL : LamData Fr o) (hp : 5 ≤ p) (hm : 2 * m < p)
    (hN : 4 * (r + 2 * m) < p * p) {h : ℕ} (hh : h < p) (hroot : 4 * (h : ZMod p) = (o : ZMod p))
    {x : ℕ} (hxr : r ≤ x) (hxN : x < r + 2 * m) {c : ZMod p}
    (harc : (c.val < h ∧ x % p < h) ∨ (h ≤ c.val ∧ h ≤ x % p))
    (hfree : ∀ k, r ≤ k → k < r + 2 * m → k % p ≠ c.val) :
    respAt Fr p o r c (srcA Fr p o r x) (srcB Fr p o r x) = srcC Fr p o r x :=
  response_long_eq_free hL hp hN hh hroot (c := c.val) (c0 := x % p) (q := x / p)
    (z' := c.val + p * r) (ZMod.val_lt c) (Nat.mod_lt _ (Fact.out : p.Prime).pos)
    (nat_eq_div_mod x) hxr hxN (by omega) harc hfree (le_chain_rep c) (chain_rep_mod c)

/-- Occupied long residue inside the source cell: its chain has the source response. -/
lemma respAt_eq_srcC_occ (hL : LamData Fr o) (hp : 5 ≤ p) (hm : 2 * m < p)
    (hN : 4 * (r + 2 * m) < p * p) {h : ℕ} (hh : h < p) (hroot : 4 * (h : ZMod p) = (o : ZMod p))
    {x k : ℕ} (hxr : r ≤ x) (hxN : x < r + 2 * m) (hkr : r ≤ k) (hkN : k < r + 2 * m)
    (hdiv : k / p = x / p) {c : ZMod p} (hkc : k % p = c.val)
    (harc : (c.val < h ∧ x % p < h) ∨ (h ≤ c.val ∧ h ≤ x % p)) :
    respAt Fr p o r c (srcA Fr p o r x) (srcB Fr p o r x) = srcC Fr p o r x := by
  have H := response_long_eq_occupied hL hp hN hh hroot (c := c.val) (c0 := x % p) (q := x / p)
    (z := x) (w := k) (ZMod.val_lt c) (Nat.mod_lt _ (Fact.out : p.Prime).pos)
    (nat_eq_div_mod x) (by rw [← hdiv, ← hkc]; exact nat_eq_div_mod k) hxr hxN hkr hkN (by omega) harc
  have H2 := cResp_chain_congr (Fr := Fr) (o := o) (le_chain_rep c) hkr
    (by rw [chain_rep_mod, hkc]) (srcA Fr p o r x) (srcB Fr p o r x)
  exact H2.trans H

end Zero


section ZeroMain
variable {Fr : Frame} {p o r m : ℕ} [Fact p.Prime]

lemma mem_cellRows {a b : ℕ} {i : Fin m} :
    i ∈ cellRows r m a b ↔ a ≤ r + 2 * i.val ∧ r + 2 * i.val < b := by
  classical simp [cellRows]

lemma mem_cellCols {a b : ℕ} {j : Fin m} :
    j ∈ cellCols r m a b ↔ a ≤ r + 2 * j.val + 1 ∧ r + 2 * j.val + 1 < b := by
  classical simp [cellCols]

/-- An interval cut-free for all pairs gives the cell geometry of rows and of columns. -/
lemma zoneCell_of_cut {a b : ℕ}
    (hcut : ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (min (x : ℤ) y) (max (x : ℤ) y)) :
    ChainModel.ZoneCell p o r m (cellRows r m a b) (cellCols r m a b) := by
  have key : ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b → x ≤ y →
      NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (x : ℤ) (y : ℤ) := by
    intro x y h1 h2 h3 h4 hxy
    have := hcut x y h1 h2 h3 h4
    rwa [min_eq_left (by exact_mod_cast hxy), max_eq_right (by exact_mod_cast hxy)] at this
  refine ⟨fun z hz z' hz' hle => ?_, fun y hy y' hy' hle => ?_⟩
  · rw [mem_cellRows] at hz hz'
    exact key _ _ hz.1 hz.2 hz'.1 hz'.2 hle
  · rw [mem_cellCols] at hy hy'
    exact key _ _ hy.1 hy.2 hy'.1 hy'.2 hle

/-- The weight vanishes at the residue of every node of the cell. -/
theorem zoneWeight_zero_of_cell (hL : LamData Fr o) (hp : 5 ≤ p) (hm : 2 * m < p)
    (hN : 4 * (r + 2 * m) < p * p) {h : ℕ} (hh : h < p) (hroot : 4 * (h : ZMod p) = (o : ZMod p))
    {a b : ℕ}
    (hcut : ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (min (x : ℤ) y) (max (x : ℤ) y))
    (z0 : Fin m) (hz0 : a ≤ r + 2 * z0.val ∧ r + 2 * z0.val < b)
    (hlong : ∀ k, a ≤ k → k < b → r ≤ k → k < r + 2 * m → ((k : ℕ) : ZMod p) ∉ shortArc p h)
    (α β : RatFunc (ZMod p)) {k : ℕ} (hk1 : r ≤ k) (hk2 : k < r + 2 * m) (hka : a ≤ k) (hkb : k < b) :
    zoneWeight Fr p o r h (r + 2 * z0.val) α β ((k : ℕ) : ZMod p) = 0 := by
  classical
  have hx0r : r ≤ r + 2 * z0.val := by omega
  have hx0N : r + 2 * z0.val < r + 2 * m := by have := z0.isLt; omega
  have hsrc_long : ((r + 2 * z0.val : ℕ) : ZMod p) ∉ shortArc p h :=
    hlong _ hz0.1 hz0.2 hx0r hx0N
  have hcl : ((k : ℕ) : ZMod p) ∉ shortArc p h := hlong k hka hkb hk1 hk2
  have hkmod : k % p = (((k : ℕ) : ZMod p)).val := (val_eq_of_natCast rfl)
  have harc : ((((k : ℕ) : ZMod p)).val < h ∧ (r + 2 * z0.val) % p < h) ∨
      (h ≤ (((k : ℕ) : ZMod p)).val ∧ h ≤ (r + 2 * z0.val) % p) := by
    have h1 : (((r + 2 * z0.val : ℕ) : ZMod p)).val = (r + 2 * z0.val) % p := ZMod.val_natCast p _
    simp only [shortArc, Finset.mem_filter, Finset.mem_univ, true_and] at hcl hsrc_long
    rw [h1] at hsrc_long
    by_cases h2 : 2 * h < p
    · simp only [h2, if_true] at hcl hsrc_long; right; omega
    · simp only [h2, if_false] at hcl hsrc_long; left; omega
  have hdiv : k / p = (r + 2 * z0.val) / p := by
    rcases le_total k (r + 2 * z0.val) with hle | hle
    · apply div_eq_of_noCut (o := o) (r := r) hle
      have := hcut k _ hka hkb hz0.1 hz0.2
      rwa [min_eq_left (by exact_mod_cast hle), max_eq_right (by exact_mod_cast hle)] at this
    · symm
      apply div_eq_of_noCut (o := o) (r := r) hle
      have := hcut k _ hka hkb hz0.1 hz0.2
      rwa [min_eq_right (by exact_mod_cast hle), max_eq_left (by exact_mod_cast hle)] at this
  have hresp := respAt_eq_srcC_occ hL hp hm hN hh hroot hx0r hx0N hk1 hk2 hdiv hkmod harc
  unfold zoneWeight
  rw [hresp, if_neg hcl]
  ring

/-- **The zero pattern.**  For every `α, β` the weight `zoneWeight` vanishes at each long residue
that is free or occupied inside the cell, so `ZoneZero` holds with the uncovered short residues. -/
theorem zoneZero_of_response (hL : LamData Fr o) (hp : 5 ≤ p) (hm : 2 * m < p)
    (hN : 4 * (r + 2 * m) < p * p) {h : ℕ} (hh : h < p) (hroot : 4 * (h : ZMod p) = (o : ZMod p))
    {a b : ℕ}
    (hcut : ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut (p : ℤ) (r : ℤ) (Singular (p : ℤ) (o : ℤ))) (min (x : ℤ) y) (max (x : ℤ) y))
    (z0 : Fin m) (hz0 : a ≤ r + 2 * z0.val ∧ r + 2 * z0.val < b)
    (hlong : ∀ k, a ≤ k → k < b → r ≤ k → k < r + 2 * m → ((k : ℕ) : ZMod p) ∉ shortArc p h)
    (α β : RatFunc (ZMod p)) :
    ChainModel.ZoneZero p r m (cellRows r m a b) (cellCols r m a b)
      (zoneWeight Fr p o r h (r + 2 * z0.val) α β) (zoneSb p r m h) := by
  classical
  intro c hc
  have hx0r : r ≤ r + 2 * z0.val := by omega
  have hx0N : r + 2 * z0.val < r + 2 * m := by have := z0.isLt; omega
  -- a long residue c has the same side of h as the source residue
  have hsrc_long : ((r + 2 * z0.val : ℕ) : ZMod p) ∉ shortArc p h :=
    hlong _ hz0.1 hz0.2 hx0r hx0N
  have harc : c ∉ shortArc p h → (c.val < h ∧ (r + 2 * z0.val) % p < h) ∨
      (h ≤ c.val ∧ h ≤ (r + 2 * z0.val) % p) := by
    intro hcl
    have h1 : (((r + 2 * z0.val : ℕ) : ZMod p)).val = (r + 2 * z0.val) % p := ZMod.val_natCast p _
    simp only [shortArc, Finset.mem_filter, Finset.mem_univ, true_and] at hcl hsrc_long
    rw [h1] at hsrc_long
    by_cases h2 : 2 * h < p
    · simp only [h2, if_true] at hcl hsrc_long; right; omega
    · simp only [h2, if_false] at hcl hsrc_long; left; omega
  -- the zero of the weight at a long residue whose response equals the source response
  have wz : c ∉ shortArc p h →
      respAt Fr p o r c (srcA Fr p o r (r + 2 * z0.val)) (srcB Fr p o r (r + 2 * z0.val)) =
        srcC Fr p o r (r + 2 * z0.val) → zoneWeight Fr p o r h (r + 2 * z0.val) α β c = 0 := by
    intro hcl hresp
    unfold zoneWeight
    rw [hresp, if_neg hcl]
    ring
  by_cases hcS : c ∈ shortArc p h
  · have hocc : ∃ k, r ≤ k ∧ k < r + 2 * m ∧ ((k : ℕ) : ZMod p) = c := by
      by_contra hno
      exact hc (by simp only [zoneSb, Finset.mem_filter]; exact ⟨hcS, hno⟩)
    obtain ⟨k, hk1, hk2, hkc⟩ := hocc
    rcases zone_node_cases hk1 hk2 with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · refine Or.inr (Or.inr ⟨i, fun hi => ?_, hkc⟩)
      rw [mem_cellRows] at hi
      exact hlong _ hi.1 hi.2 hk1 hk2 (hkc ▸ hcS) |>.elim
    · refine Or.inr (Or.inl ⟨j, fun hj => ?_, hkc⟩)
      rw [mem_cellCols] at hj
      exact hlong _ hj.1 hj.2 hk1 hk2 (hkc ▸ hcS) |>.elim
  · by_cases hocc : ∃ k, r ≤ k ∧ k < r + 2 * m ∧ ((k : ℕ) : ZMod p) = c
    · obtain ⟨k, hk1, hk2, hkc⟩ := hocc
      have hkmod : k % p = c.val := val_eq_of_natCast hkc
      -- the zero from an occupied node inside the cell
      have inCell : a ≤ k → k < b → zoneWeight Fr p o r h (r + 2 * z0.val) α β c = 0 := by
        intro hka hkb
        rw [← hkc]
        exact zoneWeight_zero_of_cell hL hp hm hN hh hroot hcut z0 hz0 hlong α β hk1 hk2 hka hkb
      rcases zone_node_cases hk1 hk2 with ⟨i, rfl⟩ | ⟨j, rfl⟩
      · by_cases hi : i ∈ cellRows r m a b
        · rw [mem_cellRows] at hi; exact Or.inl (inCell hi.1 hi.2)
        · exact Or.inr (Or.inr ⟨i, hi, hkc⟩)
      · by_cases hj : j ∈ cellCols r m a b
        · rw [mem_cellCols] at hj; exact Or.inl (inCell hj.1 hj.2)
        · exact Or.inr (Or.inl ⟨j, hj, hkc⟩)
    · refine Or.inl (wz hcS ?_)
      refine respAt_eq_srcC_free hL hp hm hN hh hroot hx0r hx0N (harc hcS) ?_
      intro k hk1 hk2 hkm
      exact hocc ⟨k, hk1, hk2, natCast_of_mod hkm⟩

end ZeroMain

#print axioms zoneZero_of_response
end CatalanCore.Arith.Hybrid
