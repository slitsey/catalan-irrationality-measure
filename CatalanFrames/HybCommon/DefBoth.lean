module

public import CatalanFrames.HybCommon.EN
public import CatalanCore.Arith.Hybrid.BorderC7
public import CatalanCore.Arith.Hybrid.BorderDef

@[expose] public section

/-!
# Member-1 and member-2 deficit families together (`DefBothG`), generic in the offset

`DefBothG I r T δ` is `DefHypT` (member 1) and `DefHypTop` (member 2, bordered) with the same `δ`.
Every rank-route window (E both classes, B, C5, C7) gives a `DefBothG` family from its rank witness
(`defBoth_of_wit`), and the five windows add (they are pairwise disjoint).  GK is not bordered and is
not part of this family.
-/

open Finset Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Rect

namespace CatalanFrames.HybCommon

variable {Fr : Frame}

/-- Member-1 and member-2 deficit hypotheses together. -/
def DefBothG (I : HybInst Fr) (r : ℕ) (T δ : ℕ → ℕ) : Prop :=
  DefHypT I r (r / 8) T δ ∧ DefHypTop I r (r / 8) T δ

lemma DefBothG.mono_T {I : HybInst Fr} {r : ℕ} {T T' δ : ℕ → ℕ} (h : DefBothG I r T δ)
    (hle : ∀ p, p.Prime → p < Bnd I r (r / 8) → T p ≤ T' p) : DefBothG I r T' δ :=
  ⟨h.1.mono_T hle, h.2.mono_T hle⟩

lemma DefBothG.add {I : HybInst Fr} {r : ℕ} {T δ₁ δ₂ : ℕ → ℕ} (h1 : DefBothG I r T δ₁)
    (h2 : DefBothG I r T δ₂)
    (hdisj : ∀ p, p.Prime → p < Bnd I r (r / 8) → δ₁ p = 0 ∨ δ₂ p = 0) :
    DefBothG I r T (fun p => δ₁ p + δ₂ p) := by
  refine ⟨?_, h1.2.add h2.2 hdisj⟩
  intro p hp hb
  rcases hdisj p hp hb with h | h
  · simp only [h, zero_add]; exact h2.1 p hp hb
  · simp only [h, add_zero]; exact h1.1 p hp hb

/-- **A `DefBothG` family from rank witnesses.** -/
theorem defBoth_of_wit (I : HybInst Fr) (r : ℕ) (T δ : ℕ → ℕ)
    (hT : ∀ p, p.Prime → p < Bnd I r (r / 8) → tropExp I r (r / 8) p ≤ T p) (W : ℕ → Prop)
    (hδ : ∀ p, ¬ W p → δ p = 0)
    (hW : ∀ p : ℕ, p.Prime → W p → ∀ [Fact p.Prime], ∃ u v : Fin r ⊕ Fin (r / 8) → ℕ,
      HasRankWit Fr p r (r / 8) u v (δ p) ∧ ∑ a, u a + ∑ b, v b ≤ T p)
    (hδT : ∀ p, p.Prime → p < Bnd I r (r / 8) → W p → δ p ≤ T p) : DefBothG I r T δ := by
  refine ⟨?_, defHypTop_of_wit I r (r / 8) T δ hT W hδ hW⟩
  refine defHypT_of_local I r (r / 8) T δ hT W hδ ?_
  intro p hp hb hWp
  refine ⟨hδT p hp hb hWp, fun [Fact p.Prime] => ?_⟩
  obtain ⟨u, v, hw, hle⟩ := hW p hp hWp
  exact hw.gle.mono (by omega)

/-! ### The five windows -/

/-- The five deficits. -/
noncomputable def dE1 (o r p : ℕ) : ℕ := if cleanE1G o r p then r / 8 else 0
noncomputable def dE3 (o r p : ℕ) : ℕ := if cleanE3G o r p then r / 8 else 0
noncomputable def dB (r p : ℕ) : ℕ := if WBG r p then r / 8 - (p - r) else 0
noncomputable def dC5 (o r p : ℕ) : ℕ := if WC5G o r p then p + (p + o) / 4 - r - r / 8 else 0
noncomputable def dC7 (o r p : ℕ) : ℕ := if WC7G o r p then p + (3 * p + o) / 4 - r - r / 8 else 0

section Windows

variable {I : HybInst Fr} {o : ℕ} {r : ℕ}

lemma TfunG_ge_trop (p : ℕ) : tropExp I r (r / 8) p ≤ TfunG o I r p := le_max_left _ _
lemma TfunG_ge_eNG (p : ℕ) : eNG o r p ≤ TfunG o I r p := le_max_right _ _

theorem defBoth_E1 (hL : LamData Fr o) (ho : o = 1 ∨ o = 3) :
    DefBothG I r (TfunG o I r) (dE1 o r) := by
  refine defBoth_of_wit I r _ _ (fun p _ _ => TfunG_ge_trop p) (cleanE1G o r)
    (fun p hp => by simp [dE1, hp]) ?_ ?_
  · intro p hp hW _
    have S := eSetup1_of_clean ho hW
    refine ⟨_, _, ?_, ?_⟩
    · have e : dE1 o r p = r / 8 := by simp [dE1, hW]
      rw [e]; exact gleAt_E1_wit hL S
    · rw [wE_sum_gen S]
      have := (eNG_E1 hW).trans (TfunG_ge_eNG (I := I) p)
      unfold dualE1G at this; exact this
  · intro p hp hb hW
    have := (eNG_E1 hW).trans (TfunG_ge_eNG (I := I) p)
    unfold dualE1G at this
    have e : dE1 o r p = r / 8 := by simp [dE1, hW]
    rw [e]; omega

theorem defBoth_E3 (hL : LamData Fr o) (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) :
    DefBothG I r (TfunG o I r) (dE3 o r) := by
  refine defBoth_of_wit I r _ _ (fun p _ _ => TfunG_ge_trop p) (cleanE3G o r)
    (fun p hp => by simp [dE3, hp]) ?_ ?_
  · intro p hp hW _
    have S := eSetup3_of_clean ho hr hW
    refine ⟨_, _, ?_, ?_⟩
    · have e : dE3 o r p = r / 8 := by simp [dE3, hW]
      rw [e]; exact gleAt_E3_wit S hL hW.2.2.2.2
    · rw [wrc_sum S]
      exact (eNG_E3 hW).trans (TfunG_ge_eNG (I := I) p)
  · intro p hp hb hW
    have := (eNG_E3 hW).trans (TfunG_ge_eNG (I := I) p)
    have e : dE3 o r p = r / 8 := by simp [dE3, hW]
    rw [e]; omega

theorem defBoth_B (hL : LamData Fr o) (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) :
    DefBothG I r (TfunG o I r) (dB r) := by
  refine defBoth_of_wit I r _ _ (fun p _ _ => TfunG_ge_trop p) (WBG r)
    (fun p hp => by simp [dB, hp]) ?_ ?_
  · intro p hp hW _
    have S := bsetup_of_G ho hr hW.1 hW.2.1 hW.2.2
    refine ⟨_, _, ?_, ?_⟩
    · have e : dB r p = r / 8 - (p - r) := by simp [dB, hW]
      rw [e]; exact gleAt_B_lam_wit hL S hW.2.2
    · have := (eNG_B (o := o) hW).trans (TfunG_ge_eNG (I := I) p)
      unfold dualBG at this; exact this
  · intro p hp hb hW
    have S := bsetup_of_G ho hr hW.1 hW.2.1 hW.2.2
    have h1 := uPot_sum_ge (p := p) (r := r) (m := r / 8) (k := kBG o p) hW.2.1
    have := (eNG_B (o := o) hW).trans (TfunG_ge_eNG (I := I) p)
    unfold dualBG at this
    have e : dB r p = r / 8 - (p - r) := by simp [dB, hW]
    rw [e]; omega

theorem defBoth_C5 (hL : LamData Fr o) (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) :
    DefBothG I r (TfunG o I r) (dC5 o r) := by
  refine defBoth_of_wit I r _ _ (fun p _ _ => TfunG_ge_trop p) (WC5G o r)
    (fun p hp => by simp [dC5, hp]) ?_ ?_
  · intro p hp hW _
    have S := csetup5_of_G ho hr hW
    refine ⟨_, _, ?_, ?_⟩
    · have e : dC5 o r p = p + (p + o) / 4 - r - r / 8 := by simp [dC5, hW]
      rw [e]; exact gleAt_C5_lam_wit S hL
    · rw [CatalanFrames.Lambda.wC_dual_eq S]
      exact (eNG_C5 hW).trans (TfunG_ge_eNG (I := I) p)
  · intro p hp hb hW
    have S := csetup5_of_G ho hr hW
    have := (eNG_C5 hW).trans (TfunG_ge_eNG (I := I) p)
    have h1 := S.hLhi; have h2 := S.hLlo
    have e : dC5 o r p = p + (p + o) / 4 - r - r / 8 := by simp [dC5, hW]
    rw [e]; omega

theorem defBoth_C7 (hL : LamData Fr o) (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) :
    DefBothG I r (TfunG o I r) (dC7 o r) := by
  refine defBoth_of_wit I r _ _ (fun p _ _ => TfunG_ge_trop p) (WC7G o r)
    (fun p hp => by simp [dC7, hp]) ?_ ?_
  · intro p hp hW _
    have S := csetup7_of_G ho hr hW
    refine ⟨_, _, ?_, ?_⟩
    · have e : dC7 o r p = p + (3 * p + o) / 4 - r - r / 8 := by simp [dC7, hW]
      rw [e]; exact gleAt_C7_lam_wit S hL
    · rw [CatalanFrames.Lambda.wC7_dual_eq S]
      exact (eNG_C7 hW).trans (TfunG_ge_eNG (I := I) p)
  · intro p hp hb hW
    have S := csetup7_of_G ho hr hW
    have := (eNG_C7 hW).trans (TfunG_ge_eNG (I := I) p)
    have h1 := S.hLhi; have h2 := S.hLlo
    have e : dC7 o r p = p + (3 * p + o) / 4 - r - r / 8 := by simp [dC7, hW]
    rw [e]; omega

end Windows

/-- The sum of the five deficits. -/
noncomputable def dAll5 (o r p : ℕ) : ℕ := dE1 o r p + dE3 o r p + dB r p + dC5 o r p + dC7 o r p

/-- **E (both classes), B, C5, C7 as a single `DefBothG` family.** -/
theorem defBoth_all5 (hL : LamData Fr o) (ho : o = 1 ∨ o = 3) {I : HybInst Fr} {r : ℕ}
    (hr : 16 ≤ r) : DefBothG I r (TfunG o I r) (dAll5 o r) := by
  have h1 := defBoth_E1 (I := I) (r := r) hL ho
  have h3 := defBoth_E3 (I := I) (r := r) hL ho hr
  have hB := defBoth_B (I := I) (r := r) hL ho hr
  have h5 := defBoth_C5 (I := I) (r := r) hL ho hr
  have h7 := defBoth_C7 (I := I) (r := r) hL ho hr
  refine (((h1.add h3 ?_).add hB ?_).add h5 ?_).add h7 ?_
  · intro p _ _
    by_cases hc : cleanE1G o r p
    · right; have := disj_e3 ho hr (p := p); simp only [dE3]
      rw [if_neg (fun h => this h hc)]
    · left; simp [dE1, hc]
  · intro p _ _
    by_cases hw : WBG r p
    · left
      obtain ⟨n1, n2⟩ := disj_b ho hr hw
      simp [dE1, dE3, n1, n2]
    · right; simp [dB, hw]
  · intro p _ _
    by_cases hw : WC5G o r p
    · left
      obtain ⟨n1, n2, n3⟩ := disj_c5 ho hr hw
      simp [dE1, dE3, dB, n1, n2, n3]
    · right; simp [dC5, hw]
  · intro p _ _
    by_cases hw : WC7G o r p
    · left
      obtain ⟨n1, n2, n3, n4⟩ := disj_c7 ho hr hw
      simp [dE1, dE3, dB, dC5, n1, n2, n3, n4]
    · right; simp [dC7, hw]

end CatalanFrames.HybCommon
