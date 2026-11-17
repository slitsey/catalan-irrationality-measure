module

public import CatalanCore.Content.ContentLaw

@[expose] public section

/-!
# Class sizes `|Z|, |W|, |N|` and the second-level bookkeeping (Lemma T consumers)

For `√(8n) < p < 3n` the residues `s < p` fall into the four intervals `A, B, C, D`
(`σ = 0, 3, 2, 5`) with explicit sizes in `r₆, r₂, p`.  The tie classes are those with
`σ ≡ λ (mod 2)`: `(A, C)` for even `λ`, `(B, D)` for odd `λ`; `Z` is the smaller and `W` the larger,
`N` the union of the other two.  We prove `|Z| + |W| + |N| = p` (with `|N|` the `Ncnt` of Lemma T),
and from Lemma T and `lemmaT_tail`: if the second level is active (`x₂ > 0`) then
`λ = 2 q₆ - 3 q₂ - 3` and `2d + 2 = |Z| + |W|`, so `x₁ = d - |Z| = (|W| - |Z| - 2)/2` and
`x₂ = x₁ - |N|`.
-/

open Finset CatalanCore.Content

namespace CatalanCore.Lai

section ClassCount

variable {n p : ℕ}

/-- sizes of the four classes (`σ = 0, 3, 2, 5`). -/
def szA (n p : ℕ) : ℕ := min (r6 n p + 1) (p - r2 n p)
def szB (n p : ℕ) : ℕ := (r6 n p + 1) - (p - r2 n p)
def szC (n p : ℕ) : ℕ := (p - r2 n p) - (r6 n p + 1)
def szD (n p : ℕ) : ℕ := p - max (r6 n p + 1) (p - r2 n p)

lemma sig_cases (n p s : ℕ) :
    (s ≤ r6 n p ∧ ¬ p - r2 n p ≤ s ∧ sig n p s = 0) ∨ (s ≤ r6 n p ∧ p - r2 n p ≤ s ∧ sig n p s = 3) ∨
    (¬ s ≤ r6 n p ∧ ¬ p - r2 n p ≤ s ∧ sig n p s = 2) ∨ (¬ s ≤ r6 n p ∧ p - r2 n p ≤ s ∧ sig n p s = 5) := by
  unfold sig
  by_cases a : s ≤ r6 n p <;> by_cases b : p - r2 n p ≤ s <;> simp [a, b]

lemma sz_sum (h : Rng n p) : szA n p + szB n p + szC n p + szD n p = p := by
  have hp := h.p5
  have h1 := r6_lt n p (by omega)
  have h2 := r2_lt n p (by omega)
  unfold szA szB szC szD
  omega

lemma card_sig_zero (h : Rng n p) : ((range p).filter (fun s => sig n p s = 0)).card = szA n p := by
  have hp := h.p5
  have h1 := r6_lt n p (by omega)
  have h2 := r2_lt n p (by omega)
  have : (range p).filter (fun s => sig n p s = 0) = range (szA n p) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range]
    simp only [szA]
    rcases sig_cases n p s with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> omega
  rw [this, card_range]

lemma card_sig_three (h : Rng n p) : ((range p).filter (fun s => sig n p s = 3)).card = szB n p := by
  have hp := h.p5
  have h1 := r6_lt n p (by omega)
  have h2 := r2_lt n p (by omega)
  have : (range p).filter (fun s => sig n p s = 3) = Ico (p - r2 n p) (r6 n p + 1) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    rcases sig_cases n p s with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> omega
  rw [this, Nat.card_Ico]; rfl

lemma card_sig_two (h : Rng n p) : ((range p).filter (fun s => sig n p s = 2)).card = szC n p := by
  have hp := h.p5
  have h1 := r6_lt n p (by omega)
  have h2 := r2_lt n p (by omega)
  have : (range p).filter (fun s => sig n p s = 2) = Ico (r6 n p + 1) (p - r2 n p) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    rcases sig_cases n p s with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> omega
  rw [this, Nat.card_Ico]; rfl

lemma card_sig_five (h : Rng n p) : ((range p).filter (fun s => sig n p s = 5)).card = szD n p := by
  have hp := h.p5
  have h1 := r6_lt n p (by omega)
  have h2 := r2_lt n p (by omega)
  have : (range p).filter (fun s => sig n p s = 5) = Ico (max (r6 n p + 1) (p - r2 n p)) p := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    rcases sig_cases n p s with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> omega
  rw [this, Nat.card_Ico]; rfl

/-- `|N|`: the parity-odd classes. -/
theorem Ncnt_eq (h : Rng n p) :
    Ncnt n p = if lam n p % 2 = 0 then szB n p + szD n p else szA n p + szC n p := by
  have hp := h.p5
  have h1 := r6_lt n p (by omega)
  have h2 := r2_lt n p (by omega)
  unfold Ncnt
  by_cases hl : lam n p % 2 = 0
  · rw [if_pos hl, ← card_sig_three h, ← card_sig_five h,
      ← Finset.card_union_of_disjoint]
    · congr 1
      ext s
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
      rcases sig_cases n p s with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> omega
    · rw [Finset.disjoint_left]
      intro s hs1 hs2
      simp only [Finset.mem_filter] at hs1 hs2
      omega
  · rw [if_neg hl, ← card_sig_zero h, ← card_sig_two h,
      ← Finset.card_union_of_disjoint]
    · congr 1
      ext s
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
      rcases sig_cases n p s with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ <;> omega
    · rw [Finset.disjoint_left]
      intro s hs1 hs2
      simp only [Finset.mem_filter] at hs1 hs2
      omega

/-- the tie class sizes: `Z` the smaller, `W` the larger. -/
def tieZ (n p : ℕ) [Decidable (lam n p % 2 = 0)] : ℕ :=
  if lam n p % 2 = 0 then min (szA n p) (szC n p) else min (szB n p) (szD n p)
def tieW (n p : ℕ) [Decidable (lam n p % 2 = 0)] : ℕ :=
  if lam n p % 2 = 0 then max (szA n p) (szC n p) else max (szB n p) (szD n p)

open Classical in
/-- `|Z| + |W| + |N| = p`. -/
theorem tie_sum (h : Rng n p) : tieZ n p + tieW n p + Ncnt n p = p := by
  have := sz_sum h
  rw [Ncnt_eq h]
  unfold tieZ tieW
  split_ifs <;> omega

open Classical in
/-- `|Z| + |N| ≥ 1`: the residues do not form a single class. -/
theorem ZN_pos (h : Rng n p) : 0 < tieZ n p + Ncnt n p := by
  by_contra hc
  have hz : tieZ n p = 0 := by omega
  have hn : Ncnt n p = 0 := by omega
  have hsum := tie_sum h
  have hW : tieW n p = p := by omega
  have hne := sig_zero_ne_sig_last h
  have hp := h.p5
  have h1 := r6_lt n p (by omega)
  have h2 := r2_lt n p (by omega)
  have hs := sz_sum h
  rw [Ncnt_eq h] at hn
  simp only [tieZ, tieW] at hz hW
  unfold sig at hne
  unfold szA szB szC szD at *
  split_ifs at * <;> omega

open Classical in
/-- The second level bookkeeping.  `x₁ = max 0 (min (d - |Z|) (|W| - d))`, `x₂ = max 0 (x₁ - |N|)`. -/
noncomputable def xone (n p : ℕ) : ℤ :=
  max 0 (min ((dcnt n p : ℤ) - tieZ n p) ((tieW n p : ℤ) - dcnt n p))

noncomputable def xtwo (n p : ℕ) : ℤ := max 0 (xone n p - Ncnt n p)

open Classical in
/-- **Lemma T consequences.**  If `x₂ > 0` then `λ = 2 q₆ - 3 q₂ - 3`, `2d + 2 = |Z| + |W|`,
`x₁ = d - |Z|` and `2 x₁ = |W| - |Z| - 2`. -/
theorem law_second_level (h : Rng n p) (hx2 : 0 < xtwo n p) :
    lam n p = 2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 3 ∧
    2 * (dcnt n p : ℤ) + 2 = tieZ n p + tieW n p ∧
    xone n p = (dcnt n p : ℤ) - tieZ n p ∧
    2 * xone n p = (tieW n p : ℤ) - tieZ n p - 2 := by
  have hT := lemmaT h
  have hsum := tie_sum h
  have hZN := ZN_pos h
  unfold xtwo xone at hx2
  have hx : tieZ n p + Ncnt n p < dcnt n p := by omega
  have hd : dcnt n p + Ncnt n p < tieW n p := by omega
  obtain ⟨hk, hd2⟩ := lemmaT_tail p (dcnt n p) (tieZ n p) (tieW n p) (Ncnt n p)
    (2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 2 - lam n p) hsum.symm.symm.symm (by
      have := hT; linarith) hx hd hZN
  unfold xone
  refine ⟨by omega, by exact_mod_cast hd2, by omega, by omega⟩

end ClassCount

end CatalanCore.Lai

#print axioms CatalanCore.Lai.Ncnt_eq
#print axioms CatalanCore.Lai.tie_sum
#print axioms CatalanCore.Lai.ZN_pos
#print axioms CatalanCore.Lai.law_second_level
