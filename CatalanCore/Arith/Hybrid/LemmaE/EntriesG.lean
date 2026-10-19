module

public import CatalanCore.Arith.Hybrid.LamEntries

@[expose] public section

/-!
# Pole-order table with an arbitrary finite set of singular indices

For labels `A < B < N`, a finite set `Sg` of singular indices carrying residues `ρ t` of `p Δ_t`
(and `ρ2 t` of `p² D_t`), all other `1 ≤ t < N` regular.  For weights `w ≥ 1` (so no regular
sum appears) and `w ≥ 2` when `B - A = p`:

* `p^w Mn A B` is `p`-integral with reduction `TEoG w A B`:
  `16⁻¹ · ∑ρ` if `B - A = p, w = 2`; `(16 (B-A))⁻¹ · ∑ρ` if `B - A ≠ p, w = 1`; else `0`;
* `p^w Mn A A` has reduction `TEdG w A = -(1/16) ∑ρ2` if `w = 2`, else `0`.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime] {Fr : Frame}

/-- Singular data. -/
structure SingData (p N : ℕ) [Fact p.Prime] where
  Sg : Finset ℕ
  ρ : ℕ → ZMod p
  ρ2 : ℕ → ZMod p
  pos : ∀ t ∈ Sg, 1 ≤ t
  reg : ∀ t, 1 ≤ t → t < N → t ∉ Sg → Reg p t

variable {N : ℕ}

/-- Sum of the residues of `Δ` over `(A, B]`. -/
def singG (D : SingData p N) (A B : ℕ) : ZMod p :=
  ∑ t ∈ D.Sg.filter (fun t => A < t ∧ t ≤ B), D.ρ t

/-- Sum of the residues of `D` over `[1, A]`. -/
def singG2 (D : SingData p N) (A : ℕ) : ZMod p :=
  ∑ t ∈ D.Sg.filter (fun t => t ≤ A), D.ρ2 t

noncomputable def TEoG (D : SingData p N) (w A B : ℕ) : ZMod p :=
  if B - A = p then (if w = 2 then (16 : ZMod p)⁻¹ * singG D A B else 0)
  else if w = 1 then (16 * ((B : ZMod p) - A))⁻¹ * singG D A B else 0

noncomputable def TEdG (D : SingData p N) (w A : ℕ) : ZMod p :=
  if w = 2 then -(1 / 16 : ZMod p) * singG2 D A else 0

/-- The hypotheses on the singular residues. -/
structure SingGood (Fr : Frame) (D : SingData p N) : Prop where
  hΔ : ∀ t ∈ D.Sg, Good p ((p : ℚ) * Fr.Delta t) (D.ρ t)
  hD : ∀ t ∈ D.Sg, Good p ((p : ℚ) ^ 2 * Fr.Dsq t) (D.ρ2 t)

theorem good_TEoG (hL : LamData Fr) (hp5 : 5 ≤ p) (D : SingData p N) (hG : SingGood Fr D)
    {A B w : ℕ} (hAB : A < B) (hB : B < N) (hw : 1 ≤ w) (hdiff : B - A < 2 * p)
    (hpair : B - A = p → 2 ≤ w) :
    Good p ((p : ℚ) ^ w * Fr.Mn A B) (TEoG D w A B) := by
  set S0 : Finset ℕ := D.Sg.filter (fun t => A < t ∧ t ≤ B) with hS0
  have hmem : ∀ t, t ∈ S0 ↔ t ∈ D.Sg ∧ A < t ∧ t ≤ B := by
    intro t; simp [hS0]
  have hsub : S0 ⊆ Ioc A B := fun t ht => by
    have := (hmem t).1 ht
    exact Finset.mem_Ioc.2 ⟨this.2.1, this.2.2⟩
  have h1 : ∀ t ∈ Ioc A B \ S0, 1 ≤ t := fun t ht => by
    have := Finset.mem_Ioc.1 (Finset.mem_sdiff.1 ht).1; omega
  have hsing : ∀ t ∈ S0, Good p ((p : ℚ) * Fr.Delta t) (D.ρ t) :=
    fun t ht => hG.hΔ t ((hmem t).1 ht).1
  have hr : ∀ t ∈ Ioc A B \ S0, Reg p t := fun t ht => by
    obtain ⟨hI, hn⟩ := Finset.mem_sdiff.1 ht
    have hI' := Finset.mem_Ioc.1 hI
    have hns : t ∉ D.Sg := fun e => hn ((hmem t).2 ⟨e, hI'⟩)
    exact D.reg t (by omega) (by omega) hns
  have hsum : singG D A B = ∑ t ∈ S0, D.ρ t := rfl
  by_cases hBA : B - A = p
  · have hw2 := hpair hBA
    have key := Mn_goodPP hL hp5 hAB hBA S0 hsub h1 D.ρ hsing hr
    rw [← hsum] at key
    unfold TEoG
    rw [if_pos hBA]
    by_cases h2 : w = 2
    · subst h2; rw [if_pos rfl]; exact key
    · rw [if_neg h2]
      obtain ⟨w', rfl⟩ : ∃ w', w = w' + 2 := ⟨w - 2, by omega⟩
      have := good_pow_mul_zero key (n := w') (by omega)
      refine this.congr' ?_
      ring
  · have hd : ((B : ZMod p) - A) ≠ 0 := sub_ne_zero_of_ne hAB hdiff hBA
    have key := Mn_goodP hL hp5 hAB S0 hsub h1 D.ρ hsing hr hd
    rw [← hsum] at key
    unfold TEoG
    rw [if_neg hBA]
    by_cases h1' : w = 1
    · subst h1'; rw [if_pos rfl, pow_one]; exact key
    · rw [if_neg h1']
      obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
      have := good_pow_mul_zero key (n := w') (by omega)
      refine this.congr' ?_ |>.congr (by simp)
      ring

theorem good_TEdG (hL : LamData Fr) (hp5 : 5 ≤ p) (D : SingData p N) (hG : SingGood Fr D)
    {A w : ℕ} (hA : A < N) (hw : w = 2) :
    Good p ((p : ℚ) ^ w * Fr.Mn A A) (TEdG D w A) := by
  subst hw
  set S0 : Finset ℕ := D.Sg.filter (fun t => t ≤ A) with hS0
  have hmem : ∀ t, t ∈ S0 ↔ t ∈ D.Sg ∧ t ≤ A := by
    intro t; simp [hS0]
  have hsub : S0 ⊆ Icc 1 A := fun t ht => by
    have := (hmem t).1 ht
    exact Finset.mem_Icc.2 ⟨D.pos t this.1, this.2⟩
  have hsing : ∀ t ∈ S0, Good p ((p : ℚ) ^ 2 * Fr.Dsq t) (D.ρ2 t) :=
    fun t ht => hG.hD t ((hmem t).1 ht).1
  have hr : ∀ t ∈ Icc 1 A \ S0, Reg p t := fun t ht => by
    obtain ⟨hI, hn⟩ := Finset.mem_sdiff.1 ht
    have hI' := Finset.mem_Icc.1 hI
    have hns : t ∉ D.Sg := fun e => hn ((hmem t).2 ⟨e, hI'.2⟩)
    exact D.reg t hI'.1 (by omega) hns
  have key := Mn_diag_goodP2 hL hp5 (A := A) S0 hsub D.ρ2 hsing hr
  unfold TEdG
  rw [if_pos rfl]
  exact key

end

end CatalanCore.Arith.Hybrid
