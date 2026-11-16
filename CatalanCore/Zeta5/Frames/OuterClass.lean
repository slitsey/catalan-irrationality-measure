module

public import CatalanCore.Zeta5.Frames.OuterEntryMain
public import CatalanCore.Zeta5.Frames.ClassData
public import CatalanCore.Zeta5.Frames.InnerAlloc

@[expose] public section

/-! Ported from mo271/Zeta5 (Apache-2.0), commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
Apery/Growth/OuterPrime.lean and Apery/Growth/InnerPrime.lean (Moritz Firsching); changes: module
conversion, only the class-count lemmas (`jc_eq_iff`, `card_class`, `card_class_Ioc`, `SX_small`,
`class_data`, `sum_wO_class`, `sum_erase_zero_eq_Icc`) are taken, `sum_erase_zero_eq_Icc` is
generalised to any additive commutative monoid; the rest of this file is new. -/

/-!
# ZC14 (I): the class data of the outer range

For `K/3 < p` (`40 n < 3 p`) and a nonzero class `c`, with `q = ⌊K/p⌋`, `a_c = a_c(K mod p)` and
`δ_c = [c ≤ N]`: the row count of the class is `2q + a_c - δ_c`, the number of rows with a
cancelling high-pole factor is `2q + a_c - 2`, and the pole count is `ℓ_K(c) = 2q + a_c`.
-/

open Finset Polynomial

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime] {m : ℕ}

lemma sum_erase_zero_eq_Icc {m : ℕ} {β : Type*} [AddCommMonoid β] (F : ℕ → β) :
    ∑ c ∈ (univ : Finset (Fin (m + 1))).erase 0, F c = ∑ c ∈ Icc 1 m, F c := by
  refine Finset.sum_nbij (fun c : Fin (m + 1) => (c : ℕ)) ?_ ?_ ?_ ?_
  · intro c hc
    have h1 := (Finset.mem_erase.mp hc).1
    have h2 := c.isLt
    simp only [Finset.mem_Icc]
    refine ⟨?_, by omega⟩
    rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
    · exact absurd (Fin.ext h) h1
    · exact h
  · intro a _ b _ hab; exact Fin.ext hab
  · intro j hj
    have := Finset.mem_Icc.mp hj
    refine ⟨⟨j, by omega⟩, ?_, rfl⟩
    simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Finset.mem_univ, true_and,
      Set.mem_singleton_iff]
    intro h
    have := congrArg Fin.val h
    simp at this; omega
  · intro c _; rfl

lemma jc_eq_iff (hm : 2 * m + 1 = p) (j : ℕ) (c : Fin (m + 1)) :
    jc hm j = c ↔ ((j : ℤ) : ZMod p) = (((c : ℕ) : ℤ) : ZMod p) ∨
      ((j : ℤ) : ZMod p) = -(((c : ℕ) : ℤ) : ZMod p) := by
  unfold jc
  constructor
  · intro h
    rcases ccls_spec hm ((j : ℤ) : ZMod p) with h1 | h1 <;> rw [h] at h1
    · left; exact h1.symm
    · right; rw [h1]; ring
  · intro h
    refine (ccls_unique hm _ c ?_).symm
    rcases h with h | h
    · left; exact h.symm
    · right; rw [h]; ring

lemma neg_ne_self_zmod (hm : 2 * m + 1 = p) {x : ZMod p} (hx : x ≠ 0) : x ≠ -x := by
  intro h
  have h2 : (2 : ZMod p) * x = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact two_ne_zero_zmod hm h3
  · exact hx h3

lemma card_class (hm : 2 * m + 1 = p) {c : Fin (m + 1)} (hc : c ≠ 0) (X : ℕ) :
    ((Icc 1 X).filter fun j => jc hm j = c).card = SX p X (((c : ℕ) : ℤ) : ZMod p) := by
  have hc0 : (((c : ℕ) : ℤ) : ZMod p) ≠ 0 := by
    intro h
    apply hc
    have := (ccls_eq_zero_iff hm _).mpr h
    rw [ccls_self hm c] at this
    exact this
  unfold SX
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_union, jc_eq_iff hm]
    tauto
  · rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [Finset.mem_filter] at h1 h2
    exact neg_ne_self_zmod hm hc0 (h1.2.symm.trans h2.2)

lemma card_class_Ioc (hm : 2 * m + 1 = p) {c : Fin (m + 1)} (hc : c ≠ 0) {X Y : ℕ} (hXY : X ≤ Y) :
    ((Icc (X + 1) Y).filter fun j => jc hm j = c).card =
      SX p Y (((c : ℕ) : ℤ) : ZMod p) - SX p X (((c : ℕ) : ℤ) : ZMod p) := by
  rw [← card_class hm hc, ← card_class hm hc]
  have hsplit : (Icc 1 Y).filter (fun j => jc hm j = c) =
      (Icc 1 X).filter (fun j => jc hm j = c) ∪ (Icc (X + 1) Y).filter (fun j => jc hm j = c) := by
    ext j; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc]; omega
  have hdisj : Disjoint ((Icc 1 X).filter (fun j => jc hm j = c))
      ((Icc (X + 1) Y).filter (fun j => jc hm j = c)) := by
    rw [Finset.disjoint_left]; intro j h1 h2
    simp only [Finset.mem_filter, Finset.mem_Icc] at h1 h2; omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  omega

/-- The per-class outer weight sum `G_q(a, δ)`. -/
noncomputable def GO (q a d : ℕ) : ℚ :=
  ∑ i ∈ range (2 * q + a - 2), min 0 ((i : ℚ) + 3 * d - ((2 * q + a : ℕ) + 4 : ℚ) / 2)

section
variable (hm : 2 * m + 1 = p) {n : ℕ} (hn : 1 ≤ n) (hout : 40 * n < 3 * p)

include hm hn hout in
lemma three_n_le_m : 3 * n ≤ m := by omega

include hm in
lemma SX_small {X : ℕ} (hX : X < p) {c : ℕ} (hc1 : 1 ≤ c) (hcm : c ≤ m) :
    SX p X (((c : ℕ) : ℤ) : ZMod p) = aCnt p X c := by
  rw [SX_class hm hc1 hcm, Nat.div_eq_of_lt hX, Nat.mod_eq_of_lt hX]; ring

include hn hout in
lemma class_data {c : Fin (m + 1)} (hc : c ≠ 0) :
    LoC hm n c = 2 * (40 * n / p) + aCnt p (40 * n % p) c - aCnt p (3 * n) c ∧
      nbC hm n c = 2 * (40 * n / p) + aCnt p (40 * n % p) c - 2 ∧
      ellC hm n c = 2 * (40 * n / p) + aCnt p (40 * n % p) c ∧
      delC n c = aCnt p (3 * n) c := by
  have hc1 : 1 ≤ (c : ℕ) := by
    rcases Nat.eq_zero_or_pos (c : ℕ) with h | h
    · exact absurd (Fin.ext h) hc
    · exact h
  have hcm := Nat.lt_succ_iff.mp c.isLt
  have h3m := three_n_le_m hm hn hout
  have hN : 3 * n < p := by omega
  have hK := SX_class hm hc1 hcm (40 * n)
  have hNs := SX_small hm hN hc1 hcm
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold LoC tailC tailO
    rw [card_class_Ioc hm hc (by omega), hK, hNs]
  · unfold nbC bigC tailC tailO
    rw [Finset.filter_filter]
    rcases le_or_gt p (40 * n) with hpK | hpK
    · have e : (Icc (3 * n + 1) (40 * n)).filter (fun j => jc hm j = c ∧ p < j) =
          (Icc (p + 1) (40 * n)).filter (fun j => jc hm j = c) := by
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [e, card_class_Ioc hm hc hpK, hK, SX_class hm hc1 hcm p, Nat.div_self (by omega),
        Nat.mod_self]
      unfold aCnt; split_ifs <;> omega
    · have e : (Icc (3 * n + 1) (40 * n)).filter (fun j => jc hm j = c ∧ p < j) = ∅ := by
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.notMem_empty, iff_false]; omega
      rw [e, Finset.card_empty, Nat.div_eq_of_lt hpK]
      unfold aCnt; split_ifs <;> omega
  · unfold ellC; rw [card_class hm hc, hK]
  · unfold delC aCnt; split_ifs <;> omega

include hn hout in
lemma sum_wO_class {c : Fin (m + 1)} (hc : c ≠ 0) :
    ∑ i ∈ range (LoC hm n c), wO hm n c i =
      GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) := by
  obtain ⟨hL, hnb, hl, hd⟩ := class_data hm hn hout hc
  have hδ : aCnt p (3 * n) c ≤ 1 := by
    have := three_n_le_m hm hn hout
    have hcm := Nat.lt_succ_iff.mp c.isLt
    unfold aCnt; split_ifs <;> omega
  have hsub : nbC hm n c ≤ LoC hm n c := by rw [hL, hnb]; omega
  rw [← Finset.sum_range_add_sum_Ico _ hsub]
  have h0 : ∑ i ∈ Ico (nbC hm n c) (LoC hm n c), wO hm n c i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    unfold wO; rw [if_neg hc, if_neg (by have := (Finset.mem_Ico.mp hi).1; omega)]
  rw [h0, add_zero, hnb]
  unfold GO
  refine Finset.sum_congr rfl fun i hi => ?_
  unfold wO
  rw [if_neg hc, if_pos (by rw [hnb]; exact Finset.mem_range.mp hi), hl, hd]

end


/-! ### Arithmetic closed forms of the per-class sums -/

/-- The zero-weight rows of a nonzero class, in terms of the class data. -/
def ZOc (q a d : ℕ) : ℕ :=
  ((range (2 * q + a - d)).filter fun i => 2 * q + a - 2 ≤ i ∨ 2 * q + a + 4 ≤ 2 * i + 6 * d).card

lemma GO_closed (q a d : ℕ) (hq : q = 1 ∨ q = 2) (ha : a ≤ 2) (hd : d ≤ 1) :
    2 * GO q a d = -7 * ((2 * q + a - 2 : ℕ) : ℚ) + d * (if q = 1 then 6 * a else 12 + 5 * a) := by
  rcases hq with rfl | rfl <;> interval_cases a <;> interval_cases d <;>
    simp [GO, Finset.sum_range_succ] <;> norm_num

lemma ZOc_closed (q a d : ℕ) (hq : q = 1 ∨ q = 2) (ha : a ≤ 2) (hd : d ≤ 1) :
    ZOc q a d = (if q = 1 then 2 - d + (if a = 2 then d else 0) else 2 + (if a = 2 then d else 0)) := by
  rcases hq with rfl | rfl <;> interval_cases a <;> interval_cases d <;> decide

section
variable (hm : 2 * m + 1 = p) {n : ℕ} (hn : 1 ≤ n) (hout : 40 * n < 3 * p)

include hn hout in
lemma wO_zero_iff {c : Fin (m + 1)} (hc : c ≠ 0) (i : ℕ) :
    wO hm n c i = 0 ↔ (nbC hm n c ≤ i ∨ ellC hm n c + 4 ≤ 2 * i + 6 * delC n c) := by
  unfold wO
  rw [if_neg hc]
  by_cases h : i < nbC hm n c
  · rw [if_pos h]
    have : min 0 ((i : ℚ) + 3 * delC n c - ((ellC hm n c : ℚ) + 4) / 2) = 0 ↔
        0 ≤ (i : ℚ) + 3 * delC n c - ((ellC hm n c : ℚ) + 4) / 2 := min_eq_left_iff
    rw [this]
    constructor
    · intro h0
      right
      have : ((ellC hm n c + 4 : ℕ) : ℚ) ≤ ((2 * i + 6 * delC n c : ℕ) : ℚ) := by
        push_cast; linarith
      exact_mod_cast this
    · rintro (h1 | h1)
      · omega
      · have : ((ellC hm n c + 4 : ℕ) : ℚ) ≤ ((2 * i + 6 * delC n c : ℕ) : ℚ) := by
          exact_mod_cast h1
        push_cast at this
        linarith
  · rw [if_neg h]
    simp only [true_iff]
    left; omega

include hn hout in
lemma zero_count_class {c : Fin (m + 1)} (hc : c ≠ 0) :
    ((range (LoC hm n c)).filter fun i => wO hm n c i = 0).card =
      ZOc (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) := by
  obtain ⟨hL, hnb, hl, hd⟩ := class_data hm hn hout hc
  unfold ZOc
  rw [hL]
  congr 1
  ext i
  simp only [Finset.mem_filter]
  rw [wO_zero_iff hm hn hout hc, hnb, hl, hd]

end


section
variable (hm : 2 * m + 1 = p) {n : ℕ} (hn : 1 ≤ n) (hout : 40 * n < 3 * p)

include hm hn hout in
lemma zero_Lo : LoC hm n 0 = 40 * n / p ∧ nbC hm n 0 = 40 * n / p - 1 := by
  have hN : 3 * n < p := by omega
  have hset : tailC hm n 0 = (Ioc 0 (40 * n)).filter (fun j => p ∣ j) := by
    ext j
    unfold tailC tailO
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc, jc_eq_zero_iff hm,
      Int.natCast_dvd_natCast]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have := Nat.le_of_dvd h1 h3
      exact ⟨⟨by omega, h2⟩, h3⟩
  have hLo : LoC hm n 0 = 40 * n / p := by
    unfold LoC; rw [hset]; exact Nat.Ioc_filter_dvd_card_eq_div _ _
  refine ⟨hLo, ?_⟩
  have hsplit := Finset.card_filter_add_card_filter_not (s := tailC hm n 0) (fun j => p < j)
  have hb : nbC hm n 0 = ((tailC hm n 0).filter fun j => p < j).card := rfl
  by_cases hpK : p ≤ 40 * n
  · have e : (tailC hm n 0).filter (fun j => ¬ p < j) = {p} := by
      ext j
      rw [hset]
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        have := Nat.le_of_dvd h1 h3
        omega
      · rintro rfl
        exact ⟨⟨⟨by omega, hpK⟩, dvd_refl _⟩, by omega⟩
    rw [e, Finset.card_singleton] at hsplit
    have : 1 ≤ 40 * n / p := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    unfold LoC at hLo
    omega
  · have e : (tailC hm n 0).filter (fun j => ¬ p < j) = ∅ := by
      ext j
      rw [hset]
      simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.notMem_empty, iff_false]
      rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
      have := Nat.le_of_dvd h1 h3
      omega
    rw [e, Finset.card_empty] at hsplit
    have : 40 * n / p = 0 := Nat.div_eq_of_lt (by omega)
    unfold LoC at hLo
    omega

include hm hn hout in
lemma zero_sum (hq : 40 * n / p ≤ 2) :
    ∑ i ∈ range (LoC hm n 0), wO hm n 0 i =
      (if 40 * n / p = 1 then -1 / 2 else if 40 * n / p = 2 then -2 else 0) := by
  obtain ⟨hL, hnb⟩ := zero_Lo hm hn hout
  rw [hL]
  generalize hq' : 40 * n / p = q at *
  interval_cases q
  · simp
  · simp [wO, hnb]
  · simp [wO, hnb, Finset.sum_range_succ]

include hm hn hout in
lemma zero_count (hq : 40 * n / p ≤ 2) :
    ((range (LoC hm n 0)).filter fun i => wO hm n 0 i = 0).card =
      (if 40 * n / p = 2 then 1 else 0) := by
  obtain ⟨hL, hnb⟩ := zero_Lo hm hn hout
  rw [hL]
  generalize hq' : 40 * n / p = q at *
  interval_cases q
  · simp
  · simp [wO, hnb]
  · simp [wO, hnb, Finset.sum_range_succ, Finset.filter_insert]
    decide

end


/-! ### The class sums -/

lemma aCnt_le_two (p v c : ℕ) : aCnt p v c ≤ 2 := by unfold aCnt; split_ifs <;> omega

/-- For `N ≤ m` and `c ∈ [1, m]`, `a_c(N) = [c ≤ N]`. -/
lemma aCnt_small {m : ℕ} (hm : 2 * m + 1 = p) {N c : ℕ} (hN : N ≤ m) (hcm : c ≤ m) :
    aCnt p N c = if c ≤ N then 1 else 0 := by
  unfold aCnt; split_ifs <;> omega

lemma sum_aCnt_mul {m : ℕ} (hm : 2 * m + 1 = p) {N v : ℕ} (hN : N ≤ m) (hv : v < p) :
    ∑ c ∈ Icc 1 m, aCnt p N c * aCnt p v c = min N v + (N + v + 1 - p) := by
  have e1 : ∀ c ∈ Icc 1 m, aCnt p N c * aCnt p v c = if c ≤ N then aCnt p v c else 0 := by
    intro c hc
    rw [aCnt_small hm hN (Finset.mem_Icc.mp hc).2]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl e1, ← Finset.sum_filter]
  have e2 : (Icc 1 m).filter (fun c => c ≤ N) = Icc 1 N := by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [e2]
  unfold aCnt
  rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
  have e3 : (Icc 1 N).filter (fun c => c ≤ v) = Icc 1 (min N v) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  have e4 : (Icc 1 N).filter (fun c => p - v ≤ c) = Icc (max (p - v) 1) N := by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [e3, e4, Nat.card_Icc, Nat.card_Icc]
  push_cast
  omega

lemma sum_aCnt_ind {m : ℕ} (hm : 2 * m + 1 = p) {N v : ℕ} (hN : N ≤ m) (hv : v < p) :
    ∑ c ∈ Icc 1 m, aCnt p N c * (if aCnt p v c = 2 then 1 else 0) = N + v + 1 - p := by
  have e1 : ∀ c ∈ Icc 1 m, aCnt p N c * (if aCnt p v c = 2 then 1 else 0) =
      if c ≤ N then (if aCnt p v c = 2 then 1 else 0) else 0 := by
    intro c hc
    rw [aCnt_small hm hN (Finset.mem_Icc.mp hc).2]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl e1, ← Finset.sum_filter, Finset.sum_boole]
  have e2 : (Icc 1 m).filter (fun c => c ≤ N) = Icc 1 N := by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [e2]
  have e3 : (Icc 1 N).filter (fun c => aCnt p v c = 2) = Icc (p - v) (min N v) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_Icc]
    unfold aCnt
    constructor
    · rintro ⟨hc, h⟩
      split_ifs at h <;> omega
    · rintro ⟨h1, h2⟩
      refine ⟨by omega, ?_⟩
      split_ifs <;> omega
  rw [e3, Nat.card_Icc]
  push_cast
  omega

section
variable (hm : 2 * m + 1 = p) {n : ℕ} (hn : 1 ≤ n) (hout : 40 * n < 3 * p)

include hm hn hout in
/-- `W := ∑_c ∑_i w_O(c,i)` splits into the zero class and the nonzero classes. -/
lemma W_split :
    ∑ c : Fin (m + 1), ∑ i ∈ range (LoC hm n c), wO hm n c i =
      ∑ i ∈ range (LoC hm n 0), wO hm n 0 i +
        ∑ c ∈ Icc 1 m, GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1)))]
  congr 1
  rw [Finset.sum_congr rfl fun c hc => sum_wO_class hm hn hout (Finset.mem_erase.mp hc).1]
  exact sum_erase_zero_eq_Icc (fun c => GO (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c))

include hm hn hout in
lemma Z_split :
    zcO hm n = ((range (LoC hm n 0)).filter fun i => wO hm n 0 i = 0).card +
      ∑ c ∈ Icc 1 m, ZOc (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) := by
  unfold zcO
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (m + 1)))]
  congr 1
  rw [Finset.sum_congr rfl fun c hc => zero_count_class hm hn hout (Finset.mem_erase.mp hc).1]
  exact sum_erase_zero_eq_Icc (fun c => ZOc (40 * n / p) (aCnt p (40 * n % p) c) (aCnt p (3 * n) c))

end


section
variable (hm : 2 * m + 1 = p) {n : ℕ} (hn : 1 ≤ n) (hout : 40 * n < 3 * p)

include hm hn hout in
lemma d_le_one {c : ℕ} (hc : c ∈ Icc 1 m) : aCnt p (3 * n) c ≤ 1 := by
  have h3m := three_n_le_m hm hn hout
  rw [aCnt_small hm h3m (Finset.mem_Icc.mp hc).2]
  split_ifs <;> omega

include hm hn hout in
lemma outer_total_q1 (h1 : 40 * n / p = 1) :
    2 * ∑ c : Fin (m + 1), ∑ i ∈ range (LoC hm n c), wO hm n c i =
      -7 * ((40 * n % p : ℕ) : ℚ) +
        6 * ((min (3 * n) (40 * n % p) + (3 * n + 40 * n % p + 1 - p) : ℕ) : ℚ) - 1 ∧
    zcO hm n = 2 * m - 3 * n + (3 * n + 40 * n % p + 1 - p) := by
  have h3m := three_n_le_m hm hn hout
  have hN : 3 * n < p := by omega
  have hv : 40 * n % p < p := Nat.mod_lt _ (by omega)
  constructor
  · rw [W_split hm hn hout, zero_sum hm hn hout (by omega), h1, if_pos rfl, mul_add]
    have e : ∀ c ∈ Icc 1 m, 2 * GO 1 (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) =
        -7 * ((aCnt p (40 * n % p) c : ℕ) : ℚ) +
          6 * ((aCnt p (3 * n) c * aCnt p (40 * n % p) c : ℕ) : ℚ) := by
      intro c hc
      rw [GO_closed 1 _ _ (Or.inl rfl) (aCnt_le_two _ _ _) (d_le_one hm hn hout hc)]
      rw [show 2 * 1 + aCnt p (40 * n % p) c - 2 = aCnt p (40 * n % p) c by omega]
      simp only [if_true]
      push_cast; ring
    rw [Finset.mul_sum, Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum]
    have s1 : ∑ c ∈ Icc 1 m, ((aCnt p (40 * n % p) c : ℕ) : ℚ) = ((40 * n % p : ℕ) : ℚ) := by
      rw [← Nat.cast_sum, sum_aCnt hm hv]
    have s2 : ∑ c ∈ Icc 1 m, ((aCnt p (3 * n) c * aCnt p (40 * n % p) c : ℕ) : ℚ) =
        ((min (3 * n) (40 * n % p) + (3 * n + 40 * n % p + 1 - p) : ℕ) : ℚ) := by
      rw [← Nat.cast_sum, sum_aCnt_mul hm h3m hv]
    rw [s1, s2]; ring
  · rw [Z_split hm hn hout, zero_count hm hn hout (by omega), h1]
    have e : ∀ c ∈ Icc 1 m, ZOc 1 (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) =
        2 - aCnt p (3 * n) c + aCnt p (3 * n) c * (if aCnt p (40 * n % p) c = 2 then 1 else 0) := by
      intro c hc
      rw [ZOc_closed 1 _ _ (Or.inl rfl) (aCnt_le_two _ _ _) (d_le_one hm hn hout hc)]
      simp only [if_true]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib,
      sum_aCnt_ind hm h3m hv]
    have s3 : ∑ c ∈ Icc 1 m, (2 - aCnt p (3 * n) c) + 3 * n = 2 * m := by
      have : ∀ c ∈ Icc 1 m, (2 - aCnt p (3 * n) c) + aCnt p (3 * n) c = 2 := fun c hc => by
        have := d_le_one hm hn hout hc; omega
      have h2 := Finset.sum_congr rfl this
      rw [Finset.sum_add_distrib, sum_aCnt hm hN] at h2
      simpa [Nat.card_Icc, mul_comm] using h2
    simp only [if_neg (by omega : ¬ (1 = 2))]
    omega

end


section
variable (hm : 2 * m + 1 = p) {n : ℕ} (hn : 1 ≤ n) (hout : 40 * n < 3 * p)

include hm hn hout in
lemma outer_total_q2 (h2 : 40 * n / p = 2) :
    2 * ∑ c : Fin (m + 1), ∑ i ∈ range (LoC hm n c), wO hm n c i =
      -7 * ((2 * m + 40 * n % p : ℕ) : ℚ) + 12 * ((3 * n : ℕ) : ℚ) +
        5 * ((min (3 * n) (40 * n % p) + (3 * n + 40 * n % p + 1 - p) : ℕ) : ℚ) - 4 ∧
    zcO hm n = 1 + 2 * m + (3 * n + 40 * n % p + 1 - p) := by
  have h3m := three_n_le_m hm hn hout
  have hN : 3 * n < p := by omega
  have hv : 40 * n % p < p := Nat.mod_lt _ (by omega)
  constructor
  · rw [W_split hm hn hout, zero_sum hm hn hout (by omega), h2, if_neg (by omega), if_pos rfl,
      mul_add]
    have e : ∀ c ∈ Icc 1 m, 2 * GO 2 (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) =
        -7 * (2 + ((aCnt p (40 * n % p) c : ℕ) : ℚ)) +
          12 * ((aCnt p (3 * n) c : ℕ) : ℚ) +
          5 * ((aCnt p (3 * n) c * aCnt p (40 * n % p) c : ℕ) : ℚ) := by
      intro c hc
      rw [GO_closed 2 _ _ (Or.inr rfl) (aCnt_le_two _ _ _) (d_le_one hm hn hout hc)]
      rw [show 2 * 2 + aCnt p (40 * n % p) c - 2 = 2 + aCnt p (40 * n % p) c by omega]
      simp only [if_neg (by omega : ¬ (2 = 1))]
      push_cast; ring
    rw [Finset.mul_sum, Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
    have s1 : ∑ c ∈ Icc 1 m, ((aCnt p (40 * n % p) c : ℕ) : ℚ) = ((40 * n % p : ℕ) : ℚ) := by
      rw [← Nat.cast_sum, sum_aCnt hm hv]
    have s0 : ∑ c ∈ Icc 1 m, ((aCnt p (3 * n) c : ℕ) : ℚ) = ((3 * n : ℕ) : ℚ) := by
      rw [← Nat.cast_sum, sum_aCnt hm hN]
    have s2 : ∑ c ∈ Icc 1 m, ((aCnt p (3 * n) c * aCnt p (40 * n % p) c : ℕ) : ℚ) =
        ((min (3 * n) (40 * n % p) + (3 * n + 40 * n % p + 1 - p) : ℕ) : ℚ) := by
      rw [← Nat.cast_sum, sum_aCnt_mul hm h3m hv]
    rw [s1, s2, s0]
    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    push_cast
    ring
  · rw [Z_split hm hn hout, zero_count hm hn hout (by omega), h2]
    have e : ∀ c ∈ Icc 1 m, ZOc 2 (aCnt p (40 * n % p) c) (aCnt p (3 * n) c) =
        2 + aCnt p (3 * n) c * (if aCnt p (40 * n % p) c = 2 then 1 else 0) := by
      intro c hc
      rw [ZOc_closed 2 _ _ (Or.inr rfl) (aCnt_le_two _ _ _) (d_le_one hm hn hout hc)]
      simp only [if_neg (by omega : ¬ (2 = 1))]
      split_ifs <;> simp
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, sum_aCnt_ind hm h3m hv]
    simp only [if_true, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
    omega

end

end Apery
