module

public import CatalanFrames.Lambda.HybDefC7Lam
public import CatalanCore.Arith.Hybrid.LemmaE.Class1U
public import CatalanCore.Arith.Hybrid.DefGKFam

@[expose] public section

/-!
# The deficit side of the hybrid content bound, generic in the offset `o` (class dictionary)

Windows, setups, dual values and the glued `DefHypT` family for E (both classes), B, C5, C7 and GK, for
any `HybInst Fr` with `hL : LamData Fr o`, `o ∈ {1, 3}`.  The classes are indexed by `j`:

* `j = 3` : `p ≡ o (mod 4)`, `k = (3p + o)/4` (E1, C7, GK1 (`LowCleanO` second branch));
* `j = 1` : `p ≡ 4 - o (mod 4)`, `k = (p + o)/4` (E3, C5, GK3).

For λ (`o = 1`) these are the windows of `HybDefE/E3/EB/C5Lam/C7Lam`; for the mirror (`o = 3`) the residue
classes are swapped.  The exceptional primes: `¬ p ∣ 6255` for E3 (`139` for λ, none for the mirror),
`ExcJ1 o, ExcJ3 o` for GK.
-/

open Finset Classical CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.HybCommon

variable {Fr : Frame}

/-- Clean primes of E, class `j = 3`. -/
def cleanE1G (o r p : ℕ) : Prop := p.Prime ∧ p % 4 = o ∧ 5 * r + 8 ≤ 7 * p ∧ p < r

/-- Dual value of the E1 potentials. -/
def dualE1G (o r m p : ℕ) : ℕ := 2 * ((r - p) + (r - (3 * p + o) / 4)) + 4 * m

/-- Clean primes of E, class `j = 1`. -/
def cleanE3G (o r p : ℕ) : Prop :=
  p.Prime ∧ p % 4 = 4 - o ∧ 5 * r + 8 ≤ 8 * p ∧ 5 * p + 5 ≤ 4 * r ∧ ¬ p ∣ 6255

/-- Window of Theorem B. -/
def WBG (r p : ℕ) : Prop := p.Prime ∧ r < p ∧ p < r + r / 8

/-- The singular block start of Theorem B. -/
def kBG (o p : ℕ) : ℕ := if p % 4 = o then (3 * p + o) / 4 else (p + o) / 4

/-- Dual value of the D4 potentials of Theorem B. -/
def dualBG (o r m p : ℕ) : ℕ :=
  ∑ a : Fin r ⊕ Fin m, uPot p r (kBG o p) (Frame.hybRow r m a) +
    ∑ b : Fin r ⊕ Fin m, uPot p r (kBG o p) (Frame.hybCol r m b)

/-- Window of C5 (`j = 1`). -/
def WC5G (o r p : ℕ) : Prop :=
  p.Prime ∧ p % 4 = 4 - o ∧ 4 * (r + r / 8) ≤ 5 * p + o ∧ 5 * p + o < 4 * (r + 2 * (r / 8)) ∧ p < r

/-- Window of C7 (`j = 3`). -/
def WC7G (o r p : ℕ) : Prop :=
  p.Prime ∧ p % 4 = o ∧ 4 * (r + r / 8) ≤ 7 * p + o ∧ 7 * p + o < 4 * r + 8 * (r / 8)

/-- The dual excess of all windows. -/
noncomputable def eNG (o r p : ℕ) : ℕ :=
  max (max (max (if cleanE1G o r p then dualE1G o r (r / 8) p else 0)
      (if cleanE3G o r p then 2 * r + r / 8 else 0))
    (max (if WBG r p then dualBG o r (r / 8) p else 0)
      (if WC5G o r p then 2 * r + 2 * (r / 8) - (p + (p + o) / 4 - r) else 0)))
    (max (if WC7G o r p then 2 * r + 2 * (r / 8) - (p + (3 * p + o) / 4 - r) else 0)
      (if LowCleanO o r (r / 8) p then 2 * r + r / 8 else 0))

/-- The exponent bound. -/
noncomputable def TfunG (o : ℕ) (I : HybInst Fr) (r p : ℕ) : ℕ :=
  max (tropExp I r (r / 8) p) (eNG o r p)

section Setups

variable {o r p : ℕ}

lemma eSetup1_of_clean (ho : o = 1 ∨ o = 3) (h : cleanE1G o r p) :
    ESetup o p r (r / 8) 3 ((3 * p + o) / 4) := by
  obtain ⟨hp, h4, h7, hpr⟩ := h
  have hodd := hp.eq_two_or_odd
  rcases ho with rfl | rfl
  · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, hpr,
      by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, hpr,
      by omega, by omega⟩

lemma eSetup3_of_clean (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : cleanE3G o r p) :
    ESetup3 o p r (r / 8) ((p + o) / 4) := by
  obtain ⟨hp, h4, h8, h5, h6255⟩ := h
  have hodd := hp.eq_two_or_odd
  rcases ho with rfl | rfl
  · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

lemma bsetup_of_G (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (hp : p.Prime) (h1 : r < p)
    (h2 : p < r + r / 8) :
    BSetup o p r (r / 8) (if p % 4 = o then 3 else 1) (kBG o p) := by
  have hodd : p % 2 = 1 := by
    by_contra h
    have h2' : 2 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2'
    omega
  unfold kBG
  by_cases h4 : p % 4 = o
  · simp only [if_pos h4]
    rcases ho with rfl | rfl
    · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega⟩
    · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega⟩
  · simp only [if_neg h4]
    rcases ho with rfl | rfl
    · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega⟩
    · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega⟩

lemma bsetup_k_G {j k : ℕ} (ho : o = 1 ∨ o = 3) (hp : p.Prime) (S : BSetup o p r (r / 8) j k) :
    k = kBG o p := by
  have hp5 := S.p5
  have hodd : p % 2 = 1 := by
    by_contra h
    have h2' : 2 ∣ p := by omega
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2'
    omega
  have hk := S.hk
  have hkp := S.hkp
  have hj : j < 4 := by
    by_contra h
    have : 4 * p ≤ j * p := Nat.mul_le_mul_right p (by omega)
    omega
  have hj0 := S.hj0
  unfold kBG
  interval_cases j <;> split_ifs <;> omega

lemma csetup5_of_G (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : WC5G o r p) :
    CSetup o p r (r / 8) ((p + o) / 4) := by
  obtain ⟨hp, h4, h1, h2, h3⟩ := h
  have hodd := hp.eq_two_or_odd
  rcases ho with rfl | rfl
  · exact ⟨by omega, by omega, by omega, by omega, by omega, h3, by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega, by omega, by omega, h3, by omega, by omega, by omega⟩

lemma csetup7_of_G (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : WC7G o r p) :
    CSetup7 o p r (r / 8) ((3 * p + o) / 4) := by
  obtain ⟨hp, h4, h1, h2⟩ := h
  have hodd := hp.eq_two_or_odd
  rcases ho with rfl | rfl
  · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

end Setups

section Disjoint

variable {o r p : ℕ}

lemma disj_lc (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : LowCleanO o r (r / 8) p) :
    ¬ cleanE1G o r p ∧ ¬ cleanE3G o r p ∧ ¬ WBG r p ∧ ¬ WC5G o r p ∧ ¬ WC7G o r p := by
  rcases h with ⟨g1, g2, _, g3, g4⟩ | ⟨g1, g2, _, g3, g4⟩ <;>
  refine ⟨fun ⟨_, c2, c3, c4⟩ => ?_, fun ⟨_, c2, c3, c4, _⟩ => ?_, fun ⟨_, c2, c3⟩ => ?_,
    fun ⟨_, c2, c3, c4, c5⟩ => ?_, fun ⟨_, c2, c3, c4⟩ => ?_⟩ <;>
  rcases ho with rfl | rfl <;> omega

lemma disj_c7 (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : WC7G o r p) :
    ¬ cleanE1G o r p ∧ ¬ cleanE3G o r p ∧ ¬ WBG r p ∧ ¬ WC5G o r p := by
  obtain ⟨_, g2, g3, g4⟩ := h
  refine ⟨fun ⟨_, c2, c3, c4⟩ => ?_, fun ⟨_, c2, c3, c4, _⟩ => ?_, fun ⟨_, c2, c3⟩ => ?_,
    fun ⟨_, c2, c3, c4, c5⟩ => ?_⟩ <;>
  rcases ho with rfl | rfl <;> omega

lemma disj_c5 (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : WC5G o r p) :
    ¬ cleanE1G o r p ∧ ¬ cleanE3G o r p ∧ ¬ WBG r p := by
  obtain ⟨_, g2, g3, g4, g5⟩ := h
  refine ⟨fun ⟨_, c2, c3, c4⟩ => ?_, fun ⟨_, c2, c3, c4, _⟩ => ?_, fun ⟨_, c2, c3⟩ => ?_⟩ <;>
  rcases ho with rfl | rfl <;> omega

lemma disj_b (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : WBG r p) :
    ¬ cleanE1G o r p ∧ ¬ cleanE3G o r p := by
  obtain ⟨_, g2, g3⟩ := h
  refine ⟨fun ⟨_, c2, c3, c4⟩ => ?_, fun ⟨_, c2, c3, c4, _⟩ => ?_⟩ <;>
  rcases ho with rfl | rfl <;> omega

lemma disj_e3 (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : cleanE3G o r p) : ¬ cleanE1G o r p := by
  obtain ⟨_, g2, g3, g4, _⟩ := h
  rintro ⟨_, c2, c3, c4⟩
  rcases ho with rfl | rfl <;> omega

end Disjoint

/-- The glued deficit family (piecewise; the windows are pairwise disjoint). -/
noncomputable def defG (o r p : ℕ) : ℕ :=
  if LowCleanO o r (r / 8) p then r / 8
  else if WC7G o r p then p + (3 * p + o) / 4 - r - r / 8
  else if WC5G o r p then p + (p + o) / 4 - r - r / 8
  else if WBG r p then r / 8 - (p - r)
  else if cleanE3G o r p then r / 8
  else if cleanE1G o r p then r / 8 else 0

section Glue

variable {o r p : ℕ}

lemma eNG_E1 (h : cleanE1G o r p) : dualE1G o r (r / 8) p ≤ eNG o r p := by
  unfold eNG
  exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_left (by rw [if_pos h])))

lemma eNG_E3 (h : cleanE3G o r p) : 2 * r + r / 8 ≤ eNG o r p := by
  unfold eNG
  exact le_max_of_le_left (le_max_of_le_left (le_max_of_le_right (by rw [if_pos h])))

lemma eNG_B (h : WBG r p) : dualBG o r (r / 8) p ≤ eNG o r p := by
  unfold eNG
  exact le_max_of_le_left (le_max_of_le_right (le_max_of_le_left (by rw [if_pos h])))

lemma eNG_C5 (h : WC5G o r p) : 2 * r + 2 * (r / 8) - (p + (p + o) / 4 - r) ≤ eNG o r p := by
  unfold eNG
  exact le_max_of_le_left (le_max_of_le_right (le_max_of_le_right (by rw [if_pos h])))

lemma eNG_C7 (h : WC7G o r p) : 2 * r + 2 * (r / 8) - (p + (3 * p + o) / 4 - r) ≤ eNG o r p := by
  unfold eNG
  exact le_max_of_le_right (le_max_of_le_left (by rw [if_pos h]))

lemma eNG_GK (h : LowCleanO o r (r / 8) p) : 2 * r + r / 8 ≤ eNG o r p := by
  unfold eNG
  exact le_max_of_le_right (le_max_of_le_right (by rw [if_pos h]))

/-- **E (both classes), B, C5, C7 and GK as a single `DefHypT` family, for any offset `o`.** -/
theorem defHypT_allG (I : HybInst Fr) {o : ℕ} (hL : LamData Fr o) (ho : o = 1 ∨ o = 3) {r : ℕ}
    (hr : 16 ≤ r) : DefHypT I r (r / 8) (TfunG o I r) (defG o r) := by
  refine defHypT_of_local I r (r / 8) (TfunG o I r) (defG o r) (fun p _ _ => le_max_left _ _)
    (fun p => LowCleanO o r (r / 8) p ∨ WC7G o r p ∨ WC5G o r p ∨ WBG r p ∨ cleanE3G o r p ∨
      cleanE1G o r p) ?_ ?_
  · intro p hn
    simp only [not_or] at hn
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hn
    simp only [defG, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_neg n6]
  · intro p hp hb hS
    haveI : Fact p.Prime := ⟨hp⟩
    have hT : ∀ x, eNG o r p ≤ TfunG o I r p → x ≤ eNG o r p → x ≤ TfunG o I r p :=
      fun x h1 h2 => h2.trans h1
    have hTe : eNG o r p ≤ TfunG o I r p := le_max_right _ _
    rcases hS with h | h | h | h | h | h
    · -- GK
      have e : defG o r p = r / 8 := by simp only [defG, if_pos h]
      have hd := eNG_GK h
      have hm : 0 < r / 8 := by omega
      have hg : GLE p (2 * r) (Fr.fullPoly r (r / 8)) := by
        rcases h with ⟨h13, hmod, hx, hr', hN⟩ | ⟨h13, hmod, hx, hr', hN⟩
        · exact gleAt_GK3 hL (gks3_of ho h13 hmod hx hr' hN hm)
        · exact GK1.gleAt_GK1 hL (gks1_of ho h13 hmod hx hr' hN hm)
      rw [e]
      exact ⟨by omega, hg.mono (by omega)⟩
    · -- C7
      obtain ⟨n1⟩ : Nonempty (¬ LowCleanO o r (r / 8) p) := ⟨fun c => (disj_lc ho hr c).2.2.2.2 h⟩
      have e : defG o r p = p + (3 * p + o) / 4 - r - r / 8 := by
        simp only [defG, if_neg n1, if_pos h]
      have S := csetup7_of_G ho hr h
      have hg := gleAt_C7_lam S hL
      rw [CatalanFrames.Lambda.wC7_dual_eq S] at hg
      have hd := eNG_C7 h
      have hS' := S.hLhi; have hS'' := S.hLlo
      rw [e]
      exact ⟨by omega, hg.mono (by omega)⟩
    · -- C5
      have n1 : ¬ LowCleanO o r (r / 8) p := fun c => (disj_lc ho hr c).2.2.2.1 h
      have n2 : ¬ WC7G o r p := fun c => (disj_c7 ho hr c).2.2.2 h
      have e : defG o r p = p + (p + o) / 4 - r - r / 8 := by
        simp only [defG, if_neg n1, if_neg n2, if_pos h]
      have S := csetup5_of_G ho hr h
      have hg := gleAt_C5_lam S hL
      rw [CatalanFrames.Lambda.wC_dual_eq S] at hg
      have hd := eNG_C5 h
      have hS' := S.hLhi; have hS'' := S.hLlo
      rw [e]
      exact ⟨by omega, hg.mono (by omega)⟩
    · -- B
      have n1 : ¬ LowCleanO o r (r / 8) p := fun c => (disj_lc ho hr c).2.2.1 h
      have n2 : ¬ WC7G o r p := fun c => (disj_c7 ho hr c).2.2.1 h
      have n3 : ¬ WC5G o r p := fun c => (disj_c5 ho hr c).2.2 h
      have e : defG o r p = r / 8 - (p - r) := by
        simp only [defG, if_neg n1, if_neg n2, if_neg n3, if_pos h]
      have S := bsetup_of_G ho hr h.1 h.2.1 h.2.2
      have hg := gleAt_B_lam hL S h.2.2
      have hd := eNG_B (o := o) h
      have h1 := uPot_sum_ge (p := p) (r := r) (m := r / 8) (k := kBG o p) h.2.1
      have := h.2.2
      unfold dualBG at hd
      rw [e]
      exact ⟨by omega, hg.mono (by omega)⟩
    · -- E3
      have n1 : ¬ LowCleanO o r (r / 8) p := fun c => (disj_lc ho hr c).2.1 h
      have n2 : ¬ WC7G o r p := fun c => (disj_c7 ho hr c).2.1 h
      have n3 : ¬ WC5G o r p := fun c => (disj_c5 ho hr c).2.1 h
      have n4 : ¬ WBG r p := fun c => (disj_b ho hr c).2 h
      have e : defG o r p = r / 8 := by
        simp only [defG, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_pos h]
      have S := eSetup3_of_clean ho hr h
      have hg := gleAt_E3 S hL h.2.2.2.2
      rw [wrc_sum S] at hg
      have hd := eNG_E3 h
      rw [e]
      exact ⟨by omega, hg.mono (by omega)⟩
    · -- E1
      have n1 : ¬ LowCleanO o r (r / 8) p := fun c => (disj_lc ho hr c).1 h
      have n2 : ¬ WC7G o r p := fun c => (disj_c7 ho hr c).1 h
      have n3 : ¬ WC5G o r p := fun c => (disj_c5 ho hr c).1 h
      have n4 : ¬ WBG r p := fun c => (disj_b ho hr c).1 h
      have n5 : ¬ cleanE3G o r p := fun c => disj_e3 ho hr c h
      have e : defG o r p = r / 8 := by
        simp only [defG, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_pos h]
      have S := eSetup1_of_clean ho h
      have hg := (gleAt_E1_wit hL S).gle
      rw [wE_sum_gen S] at hg
      have hd := eNG_E1 h
      unfold dualE1G at hd
      rw [e]
      exact ⟨by omega, hg.mono (by omega)⟩

/-! ### The values of the glued deficit on each window -/

lemma defG_lc (h : LowCleanO o r (r / 8) p) : defG o r p = r / 8 := by
  simp only [defG, if_pos h]

lemma defG_c7 (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : WC7G o r p) :
    defG o r p = p + (3 * p + o) / 4 - r - r / 8 := by
  have n1 : ¬ LowCleanO o r (r / 8) p := fun c => (disj_lc ho hr c).2.2.2.2 h
  simp only [defG, if_neg n1, if_pos h]

lemma defG_c5 (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : WC5G o r p) :
    defG o r p = p + (p + o) / 4 - r - r / 8 := by
  have n1 : ¬ LowCleanO o r (r / 8) p := fun c => (disj_lc ho hr c).2.2.2.1 h
  have n2 : ¬ WC7G o r p := fun c => (disj_c7 ho hr c).2.2.2 h
  simp only [defG, if_neg n1, if_neg n2, if_pos h]

lemma defG_b (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : WBG r p) :
    defG o r p = r / 8 - (p - r) := by
  have n1 : ¬ LowCleanO o r (r / 8) p := fun c => (disj_lc ho hr c).2.2.1 h
  have n2 : ¬ WC7G o r p := fun c => (disj_c7 ho hr c).2.2.1 h
  have n3 : ¬ WC5G o r p := fun c => (disj_c5 ho hr c).2.2 h
  simp only [defG, if_neg n1, if_neg n2, if_neg n3, if_pos h]

lemma defG_e3 (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : cleanE3G o r p) : defG o r p = r / 8 := by
  have n1 : ¬ LowCleanO o r (r / 8) p := fun c => (disj_lc ho hr c).2.1 h
  have n2 : ¬ WC7G o r p := fun c => (disj_c7 ho hr c).2.1 h
  have n3 : ¬ WC5G o r p := fun c => (disj_c5 ho hr c).2.1 h
  have n4 : ¬ WBG r p := fun c => (disj_b ho hr c).2 h
  simp only [defG, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_pos h]

lemma defG_e1 (ho : o = 1 ∨ o = 3) (hr : 16 ≤ r) (h : cleanE1G o r p) : defG o r p = r / 8 := by
  have n1 : ¬ LowCleanO o r (r / 8) p := fun c => (disj_lc ho hr c).1 h
  have n2 : ¬ WC7G o r p := fun c => (disj_c7 ho hr c).1 h
  have n3 : ¬ WC5G o r p := fun c => (disj_c5 ho hr c).1 h
  have n4 : ¬ WBG r p := fun c => (disj_b ho hr c).1 h
  have n5 : ¬ cleanE3G o r p := fun c => disj_e3 ho hr c h
  simp only [defG, if_neg n1, if_neg n2, if_neg n3, if_neg n4, if_neg n5, if_pos h]

end Glue

end CatalanFrames.HybCommon
