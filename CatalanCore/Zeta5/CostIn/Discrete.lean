module

public import CatalanCore.Zeta5.Frames.InnerAlloc

@[expose] public section

/-!
# ZC17 (second module): discrete tools for the class sums

* `sum_fin_succ_real`: `∑_{a ≤ m} F a = F 0 + ∑_{c=1}^m F c`.
* `sum_abs_coef_le`: the error constant `5/2 ∑|coef|` of `class_sum_approx` is at most `5/2 · 36 B`
  when `|h a b| ≤ B` on `{0,1,2}²`.
* `card_filter_top`, `sum_top_two`: a set `S` of top-`E` elements (largest `c`, `c ≤ 2`) has
  `∑_{a ∈ S} c a = min(E, n₁) + min(E, n₂)` (layer cake), `n_k = #{a : c a ≥ k}`.
* `card_two`, `card_one_add_two`, `n1_approx`, `n2_approx`: the class counts `n₁ = #{c : a_c ≥ 1}`,
  `n₂ = #{c : a_c = 2}` are within `1/2` of `min(v, p/2)` and `max(0, v - p/2)`.
* `card_filter_fin_erase`: counting over `Fin (m+1) \ {0}` equals counting over `[1, m]`.
-/

open Finset

namespace Apery.CostIn

/-- `∑_{a ≤ m} F a = F 0 + ∑_{c=1}^m F c`. -/
lemma sum_fin_succ_real (m : ℕ) (F : ℕ → ℝ) :
    ∑ a : Fin (m + 1), F a = F 0 + ∑ c ∈ Icc 1 m, F c := by
  rw [Fin.sum_univ_eq_sum_range (fun i => F i) (m + 1), Finset.sum_range_succ', add_comm]
  congr 1
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

/-- The coefficients of `class_sum_approx` are bounded by four values of `h`. -/
lemma sum_abs_coef_le (h : ℕ → ℕ → ℝ) (B : ℝ) (hB : ∀ a b, a ≤ 2 → b ≤ 2 → |h a b| ≤ B) :
    ∑ i, ∑ j, |bcoef (fun a => bcoef (fun b => h a b) j) i| ≤ 36 * B := by
  obtain ⟨l00, u00⟩ := abs_le.1 (hB 0 0 (by norm_num) (by norm_num))
  obtain ⟨l01, u01⟩ := abs_le.1 (hB 0 1 (by norm_num) (by norm_num))
  obtain ⟨l02, u02⟩ := abs_le.1 (hB 0 2 (by norm_num) (by norm_num))
  obtain ⟨l10, u10⟩ := abs_le.1 (hB 1 0 (by norm_num) (by norm_num))
  obtain ⟨l11, u11⟩ := abs_le.1 (hB 1 1 (by norm_num) (by norm_num))
  obtain ⟨l12, u12⟩ := abs_le.1 (hB 1 2 (by norm_num) (by norm_num))
  obtain ⟨l20, u20⟩ := abs_le.1 (hB 2 0 (by norm_num) (by norm_num))
  obtain ⟨l21, u21⟩ := abs_le.1 (hB 2 1 (by norm_num) (by norm_num))
  obtain ⟨l22, u22⟩ := abs_le.1 (hB 2 2 (by norm_num) (by norm_num))
  have each : ∀ i j : Fin 3, |bcoef (fun a => bcoef (fun b => h a b) j) i| ≤ 4 * B := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [bcoef, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
      (rw [abs_le]; constructor <;> linarith)
  calc ∑ i, ∑ j, |bcoef (fun a => bcoef (fun b => h a b) j) i|
      ≤ ∑ i : Fin 3, ∑ j : Fin 3, 4 * B :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => each i j
    _ = 36 * B := by simp; ring


/-! ### Top-`E` selections (layer cake) -/

section top
variable {ι : Type*} [DecidableEq ι]

/-- If `S ⊆ s` consists of elements of largest `c`-value, then the number of elements of `S`
with `c ≥ k` is `min |S| #{a ∈ s : c a ≥ k}`. -/
lemma card_filter_top (s S : Finset ι) (c : ι → ℕ) (k : ℕ) (hS : S ⊆ s)
    (htop : ∀ a ∈ S, ∀ b ∈ s, b ∉ S → c b ≤ c a) :
    (S.filter fun a => k ≤ c a).card = min S.card (s.filter fun a => k ≤ c a).card := by
  by_cases hex : ∃ a ∈ S, ¬ k ≤ c a
  · obtain ⟨a, haS, hak⟩ := hex
    have hB : s.filter (fun a => k ≤ c a) ⊆ S.filter (fun a => k ≤ c a) := by
      intro b hb
      rw [Finset.mem_filter] at hb ⊢
      refine ⟨?_, hb.2⟩
      by_contra hbS
      have := htop a haS b hb.1 hbS
      omega
    have hA : S.filter (fun a => k ≤ c a) ⊆ s.filter (fun a => k ≤ c a) :=
      Finset.filter_subset_filter _ hS
    have e : S.filter (fun a => k ≤ c a) = s.filter (fun a => k ≤ c a) := Finset.Subset.antisymm hA hB
    rw [e]
    have : (s.filter fun a => k ≤ c a).card ≤ S.card := by
      rw [← e]; exact Finset.card_filter_le _ _
    omega
  · push Not at hex
    have e : S.filter (fun a => k ≤ c a) = S := Finset.filter_true_of_mem hex
    rw [e]
    have : S.card ≤ (s.filter fun a => k ≤ c a).card := by
      refine Finset.card_le_card fun a ha => ?_
      rw [Finset.mem_filter]; exact ⟨hS ha, hex a ha⟩
    omega

/-- `∑_{a ∈ S} c a = min |S| n₁ + min |S| n₂` when `c ≤ 2`, `S` the top elements of `s`. -/
lemma sum_top_two (s S : Finset ι) (c : ι → ℕ) (hc : ∀ a ∈ S, c a ≤ 2) (hS : S ⊆ s)
    (htop : ∀ a ∈ S, ∀ b ∈ s, b ∉ S → c b ≤ c a) :
    ∑ a ∈ S, c a = min S.card (s.filter fun a => 1 ≤ c a).card
      + min S.card (s.filter fun a => 2 ≤ c a).card := by
  rw [← card_filter_top s S c 1 hS htop, ← card_filter_top s S c 2 hS htop,
    Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  have := hc a ha
  split_ifs <;> omega

end top


/-! ### Class counts of `a_c = [c ≤ v] + [p - v ≤ c]` -/

section cnt
variable {p m v : ℕ}

lemma aCnt_le_two (p v c : ℕ) : aCnt p v c ≤ 2 := by
  unfold aCnt; split_ifs <;> omega

/-- The number of classes with `a_c = 2`. -/
lemma card_two (hm : 2 * m + 1 = p) (hv : v < p) :
    ((Icc 1 m).filter fun c => 2 ≤ aCnt p v c).card = if m < v then v - m else 0 := by
  have e : (Icc 1 m).filter (fun c => 2 ≤ aCnt p v c) =
      (Icc 1 m).filter (fun c => (0 ≤ c ∧ c ≤ v) ∧ (p - v ≤ c ∧ c ≤ m)) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Icc]
    unfold aCnt
    split_ifs <;> omega
  rw [e, card_two_intervals]
  split_ifs <;> omega

lemma card_one_add_two [Fact p.Prime] (hm : 2 * m + 1 = p) (hv : v < p) :
    ((Icc 1 m).filter fun c => 1 ≤ aCnt p v c).card +
      ((Icc 1 m).filter fun c => 2 ≤ aCnt p v c).card = v := by
  have hs := sum_aCnt hm hv
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) hs
  have := aCnt_le_two p v c
  split_ifs <;> omega

lemma card_filter_fin_erase (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.univ.erase (0 : Fin (m + 1))).filter fun a : Fin (m + 1) => P (a : ℕ)).card =
      ((Icc 1 m).filter P).card := by
  refine Finset.card_bij (fun a _ => (a : ℕ)) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_Icc] at ha ⊢
    refine ⟨⟨?_, Nat.lt_succ_iff.mp a.isLt⟩, ha.2⟩
    rcases Nat.eq_zero_or_pos (a : ℕ) with h | h
    · exact absurd (Fin.ext h) ha.1
    · exact h
  · intro a _ b _ h; exact Fin.ext h
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_Icc] at hc
    refine ⟨⟨c, by omega⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨fun h => by have := congrArg Fin.val h; simp at this; omega, hc.2⟩

/-- `n₁ = #{c : a_c ≥ 1}` is within `1/2` of `min(v, p/2)`. -/
lemma n1_approx [Fact p.Prime] (hm : 2 * m + 1 = p) (hv : v < p) :
    |(((Icc 1 m).filter fun c => 1 ≤ aCnt p v c).card : ℝ) - min (v : ℝ) (p / 2)| ≤ 1 / 2 := by
  have h12 := card_one_add_two hm hv
  have h2 := card_two hm hv
  have hmR : (p : ℝ) = 2 * m + 1 := by exact_mod_cast hm.symm
  by_cases hvm : m < v
  · rw [if_pos hvm] at h2
    have e1 : (((Icc 1 m).filter fun c => 1 ≤ aCnt p v c).card : ℝ) = m := by
      have : ((Icc 1 m).filter fun c => 1 ≤ aCnt p v c).card = m := by omega
      exact_mod_cast this
    have hvR : (m : ℝ) + 1 ≤ v := by exact_mod_cast hvm
    rw [e1, min_eq_right (by linarith), abs_le]; constructor <;> linarith
  · rw [if_neg hvm] at h2
    have e1 : (((Icc 1 m).filter fun c => 1 ≤ aCnt p v c).card : ℝ) = v := by
      have : ((Icc 1 m).filter fun c => 1 ≤ aCnt p v c).card = v := by omega
      exact_mod_cast this
    have hvR : (v : ℝ) ≤ m := by exact_mod_cast not_lt.mp hvm
    rw [e1, min_eq_left (by linarith)]; simp

/-- `n₂ = #{c : a_c = 2}` is within `1/2` of `max(0, v - p/2)`. -/
lemma n2_approx (hm : 2 * m + 1 = p) (hv : v < p) :
    |(((Icc 1 m).filter fun c => 2 ≤ aCnt p v c).card : ℝ) - max 0 ((v : ℝ) - p / 2)| ≤ 1 / 2 := by
  have h2 := card_two hm hv
  have hmR : (p : ℝ) = 2 * m + 1 := by exact_mod_cast hm.symm
  by_cases hvm : m < v
  · rw [if_pos hvm] at h2
    have e2 : (((Icc 1 m).filter fun c => 2 ≤ aCnt p v c).card : ℝ) = (v : ℝ) - m := by
      rw [h2, Nat.cast_sub hvm.le]
    have hvR : (m : ℝ) + 1 ≤ v := by exact_mod_cast hvm
    rw [e2, max_eq_right (by linarith), abs_le]; constructor <;> linarith
  · rw [if_neg hvm] at h2
    have e2 : (((Icc 1 m).filter fun c => 2 ≤ aCnt p v c).card : ℝ) = 0 := by rw [h2]; simp
    have hvR : (v : ℝ) ≤ m := by exact_mod_cast not_lt.mp hvm
    rw [e2, max_eq_left (by linarith)]; simp

end cnt

end Apery.CostIn
