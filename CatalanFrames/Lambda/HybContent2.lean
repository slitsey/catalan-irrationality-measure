module

public import CatalanFrames.Lambda.HybContentT5
public import CatalanFrames.Lambda.HybDefC5Lam

@[expose] public section

/-!
# λ: the content bound with the deficits E, B and C5 (`lam_content_deficit2`)

`lamWT2 = max lamWT eC5` adds the C5 dual `2r + 2m - L_p` (window `0.9 r ≲ p < r`, class 3) to the
exponent bound.  Every piece cover of `lamWT` extends to `lamWT2` (an `omega` check: the C5 dual
lies on the piece `c3_2`, `(13 r - 5 p + 32)/4`, and below `c3_1`'s `17r/8 + 8` at its left end).
The log bound and the class totals of `HybContentT4/5` are repeated for `lamWT2`, then the four
deficit families E (class 1), E (class 3), B, C5 are summed with `defSum_ge`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid

namespace CatalanFrames.Lambda

/-- The weight including the C5 dual excess. -/
noncomputable def lamWT2 (r p : ℕ) : ℝ := max (lamWT r p) ((eC5 r p : ℕ) : ℝ)

lemma lamWT2_nonneg (r p : ℕ) : 0 ≤ lamWT2 r p := (lamWT_nonneg r p).trans (le_max_left _ _)

lemma eC5_eq {r p : ℕ} (h : WC5 r p) : eC5 r p = 2 * r + 2 * (r / 8) - (p + (p + 1) / 4 - r) := by
  simp only [eC5, if_pos h]

lemma eC5_zero {r p : ℕ} (h : ¬ WC5 r p) : eC5 r p = 0 := by
  simp only [eC5, if_neg h]

lemma covers_T2_of {M : ℕ} (c : ZMod M) {r sn sd tn td : ℕ} {A B E D : ℤ} (hD : 0 < D)
    (hw : Covers c (lamWT r) r (mkPiece sn sd tn td A B E D))
    (he : ∀ p, sn * r / sd < p → p ≤ tn * r / td → p.Prime → (p : ZMod M) = c → WC5 r p →
      D * (eC5 r p : ℤ) ≤ A * r + B * p + E) :
    Covers c (lamWT2 r) r (mkPiece sn sd tn td A B E D) := by
  classical
  intro p hlo hhi hp hc
  have h1 := hw p hlo hhi hp hc
  refine max_le h1 ?_
  by_cases hW : WC5 r p
  · rw [floor_mk_s] at hlo; rw [floor_mk_t] at hhi
    exact real_of_int_bound D A B E hD (he p hlo hhi hp hc hW)
  · rw [eC5_zero hW]
    simp only [Nat.cast_zero]
    exact (lamWT_nonneg r p).trans h1

section Class3

variable {r : ℕ} (hr : 16 ≤ r)
include hr

lemma c3T2_1 : Covers (3 : ZMod 4) (lamWT2 r) r (mkPiece 1 4 9 10 17 0 64 8) :=
  covers_T2_of _ (by norm_num) (c3T_1 hr) fun p hlo hhi hp hc hW => by
    rw [eC5_eq hW]; obtain ⟨_, _, _, _, _⟩ := hW; omega

lemma c3T2_2 : Covers (3 : ZMod 4) (lamWT2 r) r (mkPiece 9 10 1 1 13 (-5) 32 4) :=
  covers_T2_of _ (by norm_num) (c3T_2 hr) fun p hlo hhi hp hc hW => by
    rw [eC5_eq hW]; obtain ⟨_, _, _, _, _⟩ := hW; omega

lemma c3T2_3 : Covers (3 : ZMod 4) (lamWT2 r) r (mkPiece 1 1 5 4 7 (-3) 32 2) :=
  covers_T2_of _ (by norm_num) (c3T_3 hr) fun p hlo hhi hp hc hW => by
    rw [eC5_eq hW]; obtain ⟨_, _, _, _, _⟩ := hW; omega

lemma c3T2_4 : Covers (3 : ZMod 4) (lamWT2 r) r (mkPiece 5 4 4 1 9 (-2) 32 4) :=
  covers_T2_of _ (by norm_num) (c3T_4 hr) fun p hlo hhi hp hc hW => by
    rw [eC5_eq hW]; obtain ⟨_, _, _, _, _⟩ := hW; omega

lemma c3T2_5 : Covers (3 : ZMod 4) (lamWT2 r) r (mkPiece 4 1 5 1 5 (-1) 32 4) :=
  covers_T2_of _ (by norm_num) (c3T_5 hr) fun p hlo hhi hp hc hW => by
    rw [eC5_eq hW]; obtain ⟨_, _, _, _, _⟩ := hW; omega

end Class3

section Class1

variable {r : ℕ} (hr : 16 ≤ r)
include hr

lemma c1T2_1 : Covers (1 : ZMod 4) (lamWT2 r) r (mkPiece 1 4 9 14 17 0 64 8) :=
  covers_T2_of _ (by norm_num) (c1T_1 hr) fun p hlo hhi hp hc hW => by
    have h4 := cls4_mod1 hc; obtain ⟨_, _, _, _, _⟩ := hW; omega

lemma c1T2_2 : Covers (1 : ZMod 4) (lamWT2 r) r (mkPiece 9 14 5 7 13 (-7) 32 4) :=
  covers_T2_of _ (by norm_num) (c1T_2 hr) fun p hlo hhi hp hc hW => by
    have h4 := cls4_mod1 hc; obtain ⟨_, _, _, _, _⟩ := hW; omega

lemma c1T2_3 : Covers (1 : ZMod 4) (lamWT2 r) r (mkPiece 5 7 1 1 9 (-7) 16 2) :=
  covers_T2_of _ (by norm_num) (c1T_3 hr) fun p hlo hhi hp hc hW => by
    have h4 := cls4_mod1 hc; obtain ⟨_, _, _, _, _⟩ := hW; omega

lemma c1T2_4 : Covers (1 : ZMod 4) (lamWT2 r) r (mkPiece 1 1 5 4 7 (-5) 16 2) :=
  covers_T2_of _ (by norm_num) (c1T_4 hr) fun p hlo hhi hp hc hW => by
    have h4 := cls4_mod1 hc; obtain ⟨_, _, _, _, _⟩ := hW; omega

lemma c1T2_5 : Covers (1 : ZMod 4) (lamWT2 r) r (mkPiece 5 4 4 3 9 (-6) 32 4) :=
  covers_T2_of _ (by norm_num) (c1T_5 hr) fun p hlo hhi hp hc hW => by
    have h4 := cls4_mod1 hc; obtain ⟨_, _, _, _, _⟩ := hW; omega

lemma c1T2_6 : Covers (1 : ZMod 4) (lamWT2 r) r (mkPiece 4 3 5 3 5 (-3) 32 4) :=
  covers_T2_of _ (by norm_num) (c1T_6 hr) fun p hlo hhi hp hc hW => by
    have h4 := cls4_mod1 hc; obtain ⟨_, _, _, _, _⟩ := hW; omega

end Class1

lemma ld1_covers_T2 (c : ZMod 4) (hc2 : (2 : ZMod 4) ≠ c) {r : ℕ} (hr : 16 ≤ r) :
    ∀ P ∈ ld1, Covers c (lamWT2 r) r P := by
  intro P hP
  have hw := ld1_covers_T c hc2 hr P hP
  intro p hlo hhi hp hc
  refine max_le (hw p hlo hhi hp hc) ?_
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
  have h0 : eC5 r p = 0 := by
    refine eC5_zero fun hW => ?_
    obtain ⟨_, _, _, _, _⟩ := hW
    omega
  rw [h0]
  simp only [Nat.cast_zero]
  exact (lamWT_nonneg r p).trans (hw p hlo hhi hp hc)

lemma prefixT2 {r : ℕ} (hr : 16 ≤ r) (p : ℕ) (hp : p.Prime)
    (hpl : p ≤ ⌊(1 / 68 : ℝ) * r⌋₊) : lamWT2 r p ≤ 9 / 4 * r := by
  refine max_le (prefixT hr p hp hpl) ?_
  have h68 : 68 * p ≤ r := by
    have h1 : (p : ℝ) ≤ (1 / 68 : ℝ) * r := (Nat.cast_le.2 hpl).trans (Nat.floor_le (by positivity))
    have : (68 * p : ℝ) ≤ r := by linarith
    exact_mod_cast this
  have h0 : eC5 r p = 0 := by
    refine eC5_zero fun hW => ?_
    obtain ⟨_, _, _, _, _⟩ := hW
    have := hp.two_le
    omega
  rw [h0]; simp

theorem class3_totalT2 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (3 : ZMod 4) (lamWT2 r) 0 (5 * r) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l3x) / 2 + ε) := by
  have h := class_total (M := 4) isUnit4_3 (α0 := 9 / 4) (t1 := 1 / 68) (by norm_num)
    (by norm_num) l3x l3x_chain hε
  filter_upwards [h, eventually_ge_atTop 16] with r hr hr16
  have := hr (lamWT2 r) (fun p hpl hp _ => prefixT2 hr16 p hp hpl) (by
    intro P hP
    unfold l3x at hP
    rcases List.mem_append.mp hP with h | h
    · exact ld1_covers_T2 3 (by decide) hr16 P h
    · simp only [l3, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl
      exacts [c3T2_1 hr16, c3T2_2 hr16, c3T2_3 hr16, c3T2_4 hr16, c3T2_5 hr16])
  rw [l3x_end, floor_frac] at this
  simpa [tot4] using this

theorem class1_totalT2 {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, clsSum 4 (1 : ZMod 4) (lamWT2 r) 0 (5 * r / 3) ≤
      (r : ℝ) ^ 2 * (((9 / 4 : ℝ) * (1 / 68) + listInt l1x) / 2 + ε) := by
  have h := class_total (M := 4) isUnit4_1 (α0 := 9 / 4) (t1 := 1 / 68) (by norm_num)
    (by norm_num) l1x l1x_chain hε
  filter_upwards [h, eventually_ge_atTop 16] with r hr hr16
  have := hr (lamWT2 r) (fun p hpl hp _ => prefixT2 hr16 p hp hpl) (by
    intro P hP
    unfold l1x at hP
    rcases List.mem_append.mp hP with h | h
    · exact ld1_covers_T2 1 (by decide) hr16 P h
    · simp only [l1, List.mem_cons, List.mem_nil_iff, or_false] at h
      rcases h with rfl | rfl | rfl | rfl | rfl | rfl
      exacts [c1T2_1 hr16, c1T2_2 hr16, c1T2_3 hr16, c1T2_4 hr16, c1T2_5 hr16, c1T2_6 hr16])
  rw [l1x_end, floor_frac] at this
  simpa [tot4] using this

end CatalanFrames.Lambda
