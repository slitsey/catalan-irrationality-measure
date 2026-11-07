module

public import CatalanCore.Arith.Hybrid.LemmaE.Class3E

@[expose] public section

/-!
# Lemma E, class 3: the block `M0` on `Pt = C \ Cz` is a "diagonal plus pairs" matrix

`M0 c c' = rfC (TEw3 c c')` equals `pairMatG tau3 (rfC ∘ dZ) (rfC ∘ eZ)`; it is invertible when
`p ∤ 6255` (the two kinds of 2×2 blocks have determinants `-9/256` and `6255/6400`).
-/

open Finset Polynomial CatalanCore CatalanCore.Basic Matrix

namespace CatalanCore.Arith.Hybrid

section

variable {o p : ℕ} [Fact p.Prime] {r m k1 : ℕ}

variable (S : ESetup3 o p r m k1)

include S

lemma tauN3_ok {a : ℕ} (ha : a < r) (hnc : ¬ isCz p r m a) :
    tauN p r a < r ∧ ¬ isCz p r m (tauN p r a) := by
  have := S.hpr; have := S.hk2r; have := S.hk1o; have := S.hN
  unfold tauN isCz at *
  split_ifs <;> omega

/-- The partner map on `Pt`. -/
def tau3 (c : Pt3 p r m) : Pt3 p r m :=
  ⟨⟨tauN p r c.1.val, (tauN3_ok S c.1.2 c.2).1⟩, (tauN3_ok S c.1.2 c.2).2⟩

lemma tau3_val (c : Pt3 p r m) : ((tau3 S c).1 : ℕ) = tauN p r c.1.val := rfl

lemma tau3_invol (c : Pt3 p r m) : tau3 S (tau3 S c) = c := by
  have := S.hpr; have := S.hk2r; have := S.hk1o; have := S.hN; have := c.2; have := c.1.2
  apply Subtype.ext; apply Fin.ext
  show tauN p r (tauN p r c.1.val) = c.1.val
  unfold tauN
  split_ifs <;> omega

lemma tau3_fix (c : Pt3 p r m) :
    tau3 S c = c ↔ ¬ ((c.1 : ℕ) < r - p) ∧ ¬ (p ≤ (c.1 : ℕ)) := by
  have := S.hpr; have := S.hk2r; have := S.hk1o; have := S.hN; have := c.1.2
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  constructor
  · intro hh
    have := congrArg (fun t : Pt3 p r m => (t.1 : ℕ)) hh
    simp only [tau3_val] at this
    unfold tauN at this
    split_ifs at this <;> omega
  · intro hh
    apply Subtype.ext; apply Fin.ext
    rw [tau3_val]; unfold tauN
    split_ifs <;> omega

/-- Diagonal entries. -/
noncomputable def dZ (a : ℕ) : ZMod p := -(1 / 16 : ZMod p) * singG2 (sd3 S) a

/-- Coupling entries. -/
noncomputable def eZ (a : ℕ) : ZMod p :=
  if a < r - p then (16 : ZMod p)⁻¹ * singG (sd3 S) a (a + p)
  else (16 : ZMod p)⁻¹ * singG (sd3 S) (a - p) a

lemma eZ_tau {a : ℕ} (ha : a < r) (hnc : ¬ isCz p r m a) : eZ S (tauN p r a) = eZ S a := by
  have := S.hpr; have := S.hk2r; have := S.hk1o; have := S.hN
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  unfold eZ tauN isCz at *
  by_cases h1 : a < r - p
  · have h2 : ¬ (a + p < r - p) := by omega
    rw [if_pos h1]
    simp only [if_pos h1, if_neg h2]
    rw [Nat.add_sub_cancel]
  · by_cases h2 : p ≤ a
    · have h3 : a - p < r - p := by omega
      simp only [if_neg h1, if_pos h2, if_pos h3]
      rw [Nat.sub_add_cancel h2]
    · simp only [if_neg h1, if_neg h2]

lemma TE3_PP {a b : ℕ} (ha : a < r) (haP : ¬ isCz p r m a) (hb : b < r) (hbP : ¬ isCz p r m b) :
    TEw3 p r m (sd3 S) a b =
      if b = a then dZ S a else if b = tauN p r a then eZ S a else 0 := by
  have := S.hpr; have := S.hk2r; have := S.hk1o; have := S.hN
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hw : wr p r m a + wc p r m b = 2 := by
    unfold wr wc; rw [if_pos ha, if_pos hb, if_neg haP, if_neg hbP]
  by_cases hab : b = a
  · subst hab
    rw [if_pos rfl, TEw3_eq, hw, TEdG_two]
    rfl
  · rw [if_neg hab]
    rcases lt_or_gt_of_ne hab with h | h
    · -- b < a
      rw [TEw3_gt _ h, hw, TEoG_two]
      by_cases hd : a - b = p
      · have ht : tauN p r a = a - p := by
          unfold tauN; rw [if_neg (by omega), if_pos (by omega)]
        rw [if_pos hd, if_pos (by omega)]
        unfold eZ
        rw [if_neg (by omega)]
        have hb' : b = a - p := by omega
        rw [hb']
      · rw [if_neg hd, if_neg]
        intro hh
        unfold tauN at hh
        split_ifs at hh <;> omega
    · -- a < b
      rw [TEw3_lt _ h, hw, TEoG_two]
      by_cases hd : b - a = p
      · have ht : tauN p r a = a + p := by
          unfold tauN; rw [if_pos (by omega)]
        rw [if_pos hd, if_pos (by omega)]
        unfold eZ
        rw [if_pos (by omega)]
        congr 3
        omega
      · rw [if_neg hd, if_neg]
        intro hh
        unfold tauN at hh
        split_ifs at hh <;> omega

end

end CatalanCore.Arith.Hybrid
