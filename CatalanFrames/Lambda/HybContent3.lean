module

public import CatalanFrames.Lambda.HybContent2
public import CatalanFrames.Lambda.HybDefC7Lam

@[expose] public section

/-!
# λ: the content bound with the deficits E, B, C5, C7 and GK: weights

`lamWT3 = max lamWT2 (max eC7 eGK)` adds the C7 dual `2r + 2m - L_p` (window `0.643 r < p < 0.714 r`,
class 1; it is exactly the line `(13 r - 7 p)/4` of the piece `c1T_2`) and the GK dual `2r + m`
(`0.41 r < p < r/2`, below the plateau `17r/8 + 8` of the pieces `c3T_1`, `c1T_1`).  Every piece cover
of `lamWT2` extends to `lamWT3` by an `omega` check.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

/-- The weight including the C7 and GK dual excesses. -/
noncomputable def lamWT3 (r p : ℕ) : ℝ :=
  max (lamWT2 r p) (max ((eC7 r p : ℕ) : ℝ) ((eGK r p : ℕ) : ℝ))

lemma lamWT3_nonneg (r p : ℕ) : 0 ≤ lamWT3 r p := (lamWT2_nonneg r p).trans (le_max_left _ _)

lemma eC7_eq {r p : ℕ} (h : WC7 r p) :
    eC7 r p = 2 * r + 2 * (r / 8) - (p + (3 * p + 1) / 4 - r) := by
  simp only [eC7, if_pos h]

lemma eC7_zero {r p : ℕ} (h : ¬ WC7 r p) : eC7 r p = 0 := by
  simp only [eC7, if_neg h]

lemma eGK_eq {r p : ℕ} (h : LowClean r (r / 8) p) : eGK r p = 2 * r + r / 8 := by
  simp only [eGK, if_pos h]

lemma eGK_zero {r p : ℕ} (h : ¬ LowClean r (r / 8) p) : eGK r p = 0 := by
  simp only [eGK, if_neg h]

/-- Outside `(r/4, r)` both new duals vanish. -/
lemma e7_zero {r p : ℕ} (hr : 16 ≤ r) (h : 4 * p ≤ r ∨ r ≤ p) : eC7 r p = 0 ∧ eGK r p = 0 := by
  constructor
  · refine eC7_zero fun hW => ?_
    obtain ⟨_, _, _, _⟩ := hW
    omega
  · refine eGK_zero fun hL => ?_
    rcases hL with ⟨_, _, _, _, _⟩ | ⟨_, _, _, _, _⟩ <;> omega

lemma covers_T3_of {M : ℕ} (c : ZMod M) {r sn sd tn td : ℕ} {A B E D : ℤ} (hD : 0 < D)
    (hw : Covers c (lamWT2 r) r (mkPiece sn sd tn td A B E D))
    (he : ∀ p, sn * r / sd < p → p ≤ tn * r / td → p.Prime → (p : ZMod M) = c → WC7 r p →
      D * (eC7 r p : ℤ) ≤ A * r + B * p + E)
    (hg : ∀ p, sn * r / sd < p → p ≤ tn * r / td → p.Prime → (p : ZMod M) = c →
      LowClean r (r / 8) p → D * (eGK r p : ℤ) ≤ A * r + B * p + E) :
    Covers c (lamWT3 r) r (mkPiece sn sd tn td A B E D) := by
  classical
  intro p hlo hhi hp hc
  have h1 := hw p hlo hhi hp hc
  have h0 := lamWT2_nonneg r p
  refine max_le h1 (max_le ?_ ?_)
  · by_cases hW : WC7 r p
    · rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
      exact real_of_int_bound D A B E hD (he p hlo hhi hp hc hW)
    · rw [eC7_zero hW]
      simp only [Nat.cast_zero]
      exact h0.trans h1
  · by_cases hL : LowClean r (r / 8) p
    · rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
      exact real_of_int_bound D A B E hD (hg p hlo hhi hp hc hL)
    · rw [eGK_zero hL]
      simp only [Nat.cast_zero]
      exact h0.trans h1

section Class3

variable {r : ℕ} (hr : 16 ≤ r)
include hr

lemma c3T3_1 : Covers (3 : ZMod 4) (lamWT3 r) r (mkPiece 1 4 9 10 17 0 64 8) :=
  covers_T3_of _ (by norm_num) (c3T2_1 hr)
    (fun p hlo hhi hp hc hW => by
      have h4 := cls4_mod3 hc; rw [eC7_eq hW]; obtain ⟨_, _, _, _⟩ := hW; omega)
    (fun p hlo hhi hp hc hL => by
      have h4 := cls4_mod3 hc; rw [eGK_eq hL]
      rcases hL with ⟨_, _, _, _, _⟩ | ⟨_, _, _, _, _⟩ <;> omega)

lemma c3T3_2 : Covers (3 : ZMod 4) (lamWT3 r) r (mkPiece 9 10 1 1 13 (-5) 32 4) :=
  covers_T3_of _ (by norm_num) (c3T2_2 hr)
    (fun p hlo hhi hp hc hW => by
      have h4 := cls4_mod3 hc; rw [eC7_eq hW]; obtain ⟨_, _, _, _⟩ := hW; omega)
    (fun p hlo hhi hp hc hL => by
      have h4 := cls4_mod3 hc; rw [eGK_eq hL]
      rcases hL with ⟨_, _, _, _, _⟩ | ⟨_, _, _, _, _⟩ <;> omega)

lemma c3T3_3 : Covers (3 : ZMod 4) (lamWT3 r) r (mkPiece 1 1 5 4 7 (-3) 32 2) :=
  covers_T3_of _ (by norm_num) (c3T2_3 hr)
    (fun p hlo hhi hp hc hW => by
      have h4 := cls4_mod3 hc; rw [eC7_eq hW]; obtain ⟨_, _, _, _⟩ := hW; omega)
    (fun p hlo hhi hp hc hL => by
      have h4 := cls4_mod3 hc; rw [eGK_eq hL]
      rcases hL with ⟨_, _, _, _, _⟩ | ⟨_, _, _, _, _⟩ <;> omega)

lemma c3T3_4 : Covers (3 : ZMod 4) (lamWT3 r) r (mkPiece 5 4 4 1 9 (-2) 32 4) :=
  covers_T3_of _ (by norm_num) (c3T2_4 hr)
    (fun p hlo hhi hp hc hW => by
      have h4 := cls4_mod3 hc; rw [eC7_eq hW]; obtain ⟨_, _, _, _⟩ := hW; omega)
    (fun p hlo hhi hp hc hL => by
      have h4 := cls4_mod3 hc; rw [eGK_eq hL]
      rcases hL with ⟨_, _, _, _, _⟩ | ⟨_, _, _, _, _⟩ <;> omega)

lemma c3T3_5 : Covers (3 : ZMod 4) (lamWT3 r) r (mkPiece 4 1 5 1 5 (-1) 32 4) :=
  covers_T3_of _ (by norm_num) (c3T2_5 hr)
    (fun p hlo hhi hp hc hW => by
      have h4 := cls4_mod3 hc; rw [eC7_eq hW]; obtain ⟨_, _, _, _⟩ := hW; omega)
    (fun p hlo hhi hp hc hL => by
      have h4 := cls4_mod3 hc; rw [eGK_eq hL]
      rcases hL with ⟨_, _, _, _, _⟩ | ⟨_, _, _, _, _⟩ <;> omega)

end Class3

section Class1

variable {r : ℕ} (hr : 16 ≤ r)
include hr

lemma c1T3_1 : Covers (1 : ZMod 4) (lamWT3 r) r (mkPiece 1 4 9 14 17 0 64 8) :=
  covers_T3_of _ (by norm_num) (c1T2_1 hr)
    (fun p hlo hhi hp hc hW => by
      have h4 := cls4_mod1 hc; rw [eC7_eq hW]; obtain ⟨_, _, _, _⟩ := hW; omega)
    (fun p hlo hhi hp hc hL => by
      have h4 := cls4_mod1 hc; rw [eGK_eq hL]
      rcases hL with ⟨_, _, _, _, _⟩ | ⟨_, _, _, _, _⟩ <;> omega)

lemma c1T3_2 : Covers (1 : ZMod 4) (lamWT3 r) r (mkPiece 9 14 5 7 13 (-7) 32 4) :=
  covers_T3_of _ (by norm_num) (c1T2_2 hr)
    (fun p hlo hhi hp hc hW => by
      have h4 := cls4_mod1 hc; rw [eC7_eq hW]; obtain ⟨_, _, _, _⟩ := hW; omega)
    (fun p hlo hhi hp hc hL => by
      have h4 := cls4_mod1 hc; rw [eGK_eq hL]
      rcases hL with ⟨_, _, _, _, _⟩ | ⟨_, _, _, _, _⟩ <;> omega)

lemma c1T3_3 : Covers (1 : ZMod 4) (lamWT3 r) r (mkPiece 5 7 1 1 9 (-7) 16 2) :=
  covers_T3_of _ (by norm_num) (c1T2_3 hr)
    (fun p hlo hhi hp hc hW => by
      have h4 := cls4_mod1 hc; rw [eC7_eq hW]; obtain ⟨_, _, _, _⟩ := hW; omega)
    (fun p hlo hhi hp hc hL => by
      have h4 := cls4_mod1 hc; rw [eGK_eq hL]
      rcases hL with ⟨_, _, _, _, _⟩ | ⟨_, _, _, _, _⟩ <;> omega)

lemma c1T3_4 : Covers (1 : ZMod 4) (lamWT3 r) r (mkPiece 1 1 5 4 7 (-5) 16 2) :=
  covers_T3_of _ (by norm_num) (c1T2_4 hr)
    (fun p hlo hhi hp hc hW => by
      have h4 := cls4_mod1 hc; rw [eC7_eq hW]; obtain ⟨_, _, _, _⟩ := hW; omega)
    (fun p hlo hhi hp hc hL => by
      have h4 := cls4_mod1 hc; rw [eGK_eq hL]
      rcases hL with ⟨_, _, _, _, _⟩ | ⟨_, _, _, _, _⟩ <;> omega)

lemma c1T3_5 : Covers (1 : ZMod 4) (lamWT3 r) r (mkPiece 5 4 4 3 9 (-6) 32 4) :=
  covers_T3_of _ (by norm_num) (c1T2_5 hr)
    (fun p hlo hhi hp hc hW => by
      have h4 := cls4_mod1 hc; rw [eC7_eq hW]; obtain ⟨_, _, _, _⟩ := hW; omega)
    (fun p hlo hhi hp hc hL => by
      have h4 := cls4_mod1 hc; rw [eGK_eq hL]
      rcases hL with ⟨_, _, _, _, _⟩ | ⟨_, _, _, _, _⟩ <;> omega)

lemma c1T3_6 : Covers (1 : ZMod 4) (lamWT3 r) r (mkPiece 4 3 5 3 5 (-3) 32 4) :=
  covers_T3_of _ (by norm_num) (c1T2_6 hr)
    (fun p hlo hhi hp hc hW => by
      have h4 := cls4_mod1 hc; rw [eC7_eq hW]; obtain ⟨_, _, _, _⟩ := hW; omega)
    (fun p hlo hhi hp hc hL => by
      have h4 := cls4_mod1 hc; rw [eGK_eq hL]
      rcases hL with ⟨_, _, _, _, _⟩ | ⟨_, _, _, _, _⟩ <;> omega)

end Class1

lemma ld1_covers_T3 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) {r : ℕ} (hr : 16 ≤ r) :
    ∀ P ∈ ld1, Covers c (lamWT3 r) r P := by
  intro P hP
  have hw := ld1_covers_T2 c hc2 hr P hP
  intro p hlo hhi hp hc
  have ht := ld1_t_le P hP
  have h1 : (p : ℝ) ≤ P.t * r := by
    have h2 : (p : ℝ) ≤ (⌊P.t * r⌋₊ : ℝ) := by exact_mod_cast hhi
    refine h2.trans (Nat.floor_le ?_)
    have : 0 ≤ P.t := by
      by_contra hneg
      push_neg at hneg
      have : ⌊P.t * r⌋₊ = 0 := Nat.floor_of_nonpos (by nlinarith [(Nat.cast_nonneg r : (0:ℝ) ≤ r)])
      omega
    positivity
  have h4 : 4 * p ≤ r := by
    have : (p : ℝ) ≤ r / 4 := by nlinarith [(Nat.cast_nonneg r : (0:ℝ) ≤ r)]
    have : (4 * p : ℝ) ≤ r := by linarith
    exact_mod_cast this
  obtain ⟨h7, hk⟩ := e7_zero (p := p) hr (Or.inl h4)
  refine max_le (hw p hlo hhi hp hc) (max_le ?_ ?_)
  · rw [h7]; simp only [Nat.cast_zero]; exact (lamWT2_nonneg r p).trans (hw p hlo hhi hp hc)
  · rw [hk]; simp only [Nat.cast_zero]; exact (lamWT2_nonneg r p).trans (hw p hlo hhi hp hc)

lemma prefixT3 {r : ℕ} (hr : 16 ≤ r) (p : ℕ) (hp : p.Prime)
    (hpl : p ≤ ⌊(1 / 68 : ℝ) * r⌋₊) : lamWT3 r p ≤ 9 / 4 * r := by
  have h68 : 68 * p ≤ r := by
    have h1 : (p : ℝ) ≤ (1 / 68 : ℝ) * r := (Nat.cast_le.2 hpl).trans (Nat.floor_le (by positivity))
    have : (68 * p : ℝ) ≤ r := by linarith
    exact_mod_cast this
  obtain ⟨h7, hk⟩ := e7_zero (p := p) hr (Or.inl (by omega))
  have hr0 : (0 : ℝ) ≤ 9 / 4 * r := by positivity
  refine max_le (prefixT2 hr p hp hpl) (max_le ?_ ?_)
  · rw [h7]; simpa using hr0
  · rw [hk]; simpa using hr0

theorem class3_totalT3 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (3 : ZMod 4) (lamWT3 r) 0 (5 * r) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε) := by
  have h := class_total (M := 4) isUnit4_3 (α0 := 9 / 4) (t1 := 1 / 68) (by norm_num)
    (by norm_num) l3x l3x_chain hε
  filter_upwards [h, eventually_ge_atTop 16] with r hr hr16
  have := hr (lamWT3 r) (fun p hpl hp _ => prefixT3 hr16 p hp hpl) (by
    intro P hP
    unfold l3x at hP
    rcases List.mem_append.mp hP with h | h
    · exact ld1_covers_T3 3 (by decide) hr16 P h
    · simp only [l3, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      exacts [c3T3_1 hr16, c3T3_2 hr16, c3T3_3 hr16, c3T3_4 hr16, c3T3_5 hr16])
  rw [l3x_end, floor_frac] at this
  simpa [tot4] using this

theorem class1_totalT3 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (1 : ZMod 4) (lamWT3 r) 0 (5 * r / 3) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε) := by
  have h := class_total (M := 4) isUnit4_1 (α0 := 9 / 4) (t1 := 1 / 68) (by norm_num)
    (by norm_num) l1x l1x_chain hε
  filter_upwards [h, eventually_ge_atTop 16] with r hr hr16
  have := hr (lamWT3 r) (fun p hpl hp _ => prefixT3 hr16 p hp hpl) (by
    intro P hP
    unfold l1x at hP
    rcases List.mem_append.mp hP with h | h
    · exact ld1_covers_T3 1 (by decide) hr16 P h
    · simp only [l1, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [c1T3_1 hr16, c1T3_2 hr16, c1T3_3 hr16, c1T3_4 hr16, c1T3_5 hr16, c1T3_6 hr16])
  rw [l1x_end, floor_frac] at this
  simpa [tot4] using this

end CatalanFrames.Lambda
