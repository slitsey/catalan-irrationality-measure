module

public import Mathlib.Tactic
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

/-!
# Cell tools: sign and floor constancy between the points `n/c`

`NoPt c l r` says that no point `n/c` (`n ∈ ℤ`) lies in the open interval `(l, r)`. On such an
interval every affine sign condition `s t < n` and every floor `⌊s t⌋` is constant, whenever
`NoPt s l r` (`noPt_of_mul` transfers `NoPt` along integer multiples of the slope).
`noPt_of_check` is the rational (decidable) form used by the evaluators.
-/

open Set

namespace CatalanCore.Zeta5.Profile

/-- No point `n / c` lies in `(l, r)`. -/
def NoPt (c l r : ℝ) : Prop := ∀ n : ℤ, ¬ (l < (n : ℝ) / c ∧ (n : ℝ) / c < r)

lemma noPt_of_mul {c s l r : ℝ} {k : ℤ} (hk : k ≠ 0) (hs : s ≠ 0) (hc : c = k * s)
    (h : NoPt c l r) : NoPt s l r := by
  intro n hn
  apply h (k * n)
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have : ((k * n : ℤ) : ℝ) / c = (n : ℝ) / s := by
    rw [hc]; push_cast; field_simp
  rw [this]; exact hn

lemma noPt_mono {c l r l' r' : ℝ} (h : NoPt c l r) (h1 : l ≤ l') (h2 : r' ≤ r) :
    NoPt c l' r' := fun n hn => h n ⟨lt_of_le_of_lt h1 hn.1, lt_of_lt_of_le hn.2 h2⟩

/-- Strict sign constancy of `s t - n` on `(l, r)`. -/
lemma sign_const_lt_aux {s l r : ℝ} (hs : s ≠ 0) (hN : NoPt s l r) {n : ℤ} {t m : ℝ}
    (ht : t ∈ Ioo l r) (hm : m ∈ Ioo l r) (h1 : s * t < n) : s * m < n := by
  by_contra hcon
  push Not at hcon
  have hp : (n : ℝ) / s * s = n := by field_simp
  rcases hcon.eq_or_lt with heq | hlt
  · apply hN n
    have : m = (n : ℝ) / s := by
      field_simp; linarith
    rw [← this]; exact hm
  · -- s t < n < s m : the point n/s lies strictly between t and m
    apply hN n
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · have h1' : (n : ℝ) / s < t := by
        rw [div_lt_iff_of_neg hneg]; linarith
      have h2' : m < (n : ℝ) / s := by
        rw [lt_div_iff_of_neg hneg]; linarith
      exact ⟨by linarith [hm.1], by linarith [ht.2]⟩
    · have h1' : t < (n : ℝ) / s := by
        rw [lt_div_iff₀ hpos]; linarith
      have h2' : (n : ℝ) / s < m := by
        rw [div_lt_iff₀ hpos]; linarith
      exact ⟨by linarith [ht.1], by linarith [hm.2]⟩

lemma sign_const_lt {s l r : ℝ} (hs : s ≠ 0) (hN : NoPt s l r) {n : ℤ} {t m : ℝ}
    (ht : t ∈ Ioo l r) (hm : m ∈ Ioo l r) : s * t < n ↔ s * m < n :=
  ⟨sign_const_lt_aux hs hN ht hm, sign_const_lt_aux hs hN hm ht⟩

lemma ne_of_mem {s l r : ℝ} (hs : s ≠ 0) (hN : NoPt s l r) {n : ℤ} {t : ℝ}
    (ht : t ∈ Ioo l r) : s * t ≠ n := by
  intro h
  apply hN n
  have : t = (n : ℝ) / s := by field_simp; linarith
  rw [← this]; exact ht

/-- Non-strict sign constancy. -/
lemma sign_const_le {s l r : ℝ} (hs : s ≠ 0) (hN : NoPt s l r) {n : ℤ} {t m : ℝ}
    (ht : t ∈ Ioo l r) (hm : m ∈ Ioo l r) : s * t ≤ n ↔ s * m ≤ n := by
  have a1 : s * t ≤ n ↔ s * t < n :=
    ⟨fun h => lt_of_le_of_ne h (ne_of_mem hs hN ht), le_of_lt⟩
  have a2 : s * m ≤ n ↔ s * m < n :=
    ⟨fun h => lt_of_le_of_ne h (ne_of_mem hs hN hm), le_of_lt⟩
  rw [a1, a2]; exact sign_const_lt hs hN ht hm

/-- Floor constancy. -/
lemma floor_const {s l r : ℝ} (hs : s ≠ 0) (hN : NoPt s l r) {t m : ℝ}
    (ht : t ∈ Ioo l r) (hm : m ∈ Ioo l r) : ⌊s * t⌋ = ⌊s * m⌋ := by
  rw [Int.floor_eq_iff]
  constructor
  · by_contra h
    push Not at h
    have := (sign_const_lt hs hN (n := ⌊s * m⌋) ht hm).1 h
    exact absurd (Int.floor_le (s * m)) (not_le.2 this)
  · have := (sign_const_lt hs hN (n := ⌊s * m⌋ + 1) ht hm).2
      (by have := Int.lt_floor_add_one (s * m); push_cast; exact this)
    push_cast at this ⊢; exact this

/-- The decidable form: `r c ≤ ⌊l c⌋ + 1` for rational `0 < c` gives `NoPt`. -/
lemma noPt_of_check {c l r : ℚ} (hc : 0 < c) (h : r * c ≤ ⌊l * c⌋ + 1) :
    NoPt (c : ℝ) (l : ℝ) (r : ℝ) := by
  intro n ⟨h1, h2⟩
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  rw [lt_div_iff₀ hc'] at h1
  rw [div_lt_iff₀ hc'] at h2
  have h1' : ((l * c : ℚ) : ℝ) < n := by push_cast; exact h1
  have h1'' : l * c < (n : ℚ) := by exact_mod_cast h1'
  have h3 : ⌊l * c⌋ < n := Int.floor_lt.2 (by exact_mod_cast h1'')
  have h4 : ⌊l * c⌋ + 1 ≤ n := h3
  have h5 : r * c ≤ (n : ℚ) := by
    have : ((⌊l * c⌋ + 1 : ℤ) : ℚ) ≤ n := by exact_mod_cast h4
    push_cast at this; linarith
  have h6 : ((r * c : ℚ) : ℝ) ≤ n := by exact_mod_cast h5
  push_cast at h6
  linarith

end CatalanCore.Zeta5.Profile
