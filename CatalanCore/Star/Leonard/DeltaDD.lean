module

public import CatalanCore.Star.Leonard.DeltaBasis
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
# Prop hDelta, step (4): divided differences

Divided differences `dd f s = ∑_{z∈s} f z / ∏_{w∈s\{z}} (z-w)` of a finite node set, the recursion
`dd(a,b,s)(b-a) = dd(b,s) - dd(a,s)`, the Newton expansion (peeling nodes `u_0,u_1,…`), and the value
of the window divided differences `dd (z)_K {s, s+1, …, s+n} = C(K,n) (s+n)_{K-n}`.
-/

@[expose] public section

open Finset

namespace CatalanCore.Star.Leonard

variable {F : Type*} [Field F] [DecidableEq F]

/-- Divided difference over a finite node set. -/
noncomputable def dd (f : F → F) (s : Finset F) : F :=
  ∑ z ∈ s, f z / ∏ w ∈ s.erase z, (z - w)

lemma dd_insert (f : F → F) (a : F) (t : Finset F) (ha : a ∉ t) :
    dd f (insert a t) = f a / ∏ w ∈ t, (a - w) +
      ∑ z ∈ t, (f z / ∏ w ∈ t.erase z, (z - w)) / (z - a) := by
  unfold dd
  rw [Finset.sum_insert ha, Finset.erase_insert ha]
  congr 1
  refine Finset.sum_congr rfl fun z hz => ?_
  have hza : z ≠ a := fun h => ha (h ▸ hz)
  rw [Finset.erase_insert_of_ne (Ne.symm hza), Finset.prod_insert (by simp [ha]), div_div, mul_comm]

/-- The divided-difference recursion. -/
lemma dd_F1 (f : F → F) (a b : F) (s : Finset F) (ha : a ∉ s) (hb : b ∉ s) (hab : a ≠ b) :
    dd f (insert a (insert b s)) * (b - a) = dd f (insert b s) - dd f (insert a s) := by
  have hab' : a ∉ insert b s := by simp [hab, ha]
  rw [dd_insert f a (insert b s) hab', dd_insert f b s hb, dd_insert f a s ha,
    Finset.sum_insert hb, Finset.erase_insert hb, Finset.prod_insert hb]
  have hba : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hab0 : a - b ≠ 0 := sub_ne_zero.2 hab
  have hs : ∀ z ∈ s, (f z / ∏ w ∈ (insert b s).erase z, (z - w)) / (z - a) * (b - a) =
      (f z / ∏ w ∈ s.erase z, (z - w)) / (z - b) - (f z / ∏ w ∈ s.erase z, (z - w)) / (z - a) := by
    intro z hz
    have hzb : z - b ≠ 0 := sub_ne_zero.2 (fun h => hb (h ▸ hz))
    have hza : z - a ≠ 0 := sub_ne_zero.2 (fun h => ha (h ▸ hz))
    have hbz : b ≠ z := fun h => hb (h ▸ hz)
    rw [Finset.erase_insert_of_ne hbz, Finset.prod_insert (by simp [hb])]
    generalize ∏ w ∈ s.erase z, (z - w) = P
    rw [show (z - b) * P = P * (z - b) from mul_comm _ _, ← div_div]
    generalize f z / P = g
    field_simp
    ring
  have hsum : (∑ z ∈ s, (f z / ∏ w ∈ (insert b s).erase z, (z - w)) / (z - a)) * (b - a) =
      ∑ z ∈ s, (f z / ∏ w ∈ s.erase z, (z - w)) / (z - b) -
        ∑ z ∈ s, (f z / ∏ w ∈ s.erase z, (z - w)) / (z - a) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hs
  generalize ∏ w ∈ s, (a - w) = Pa
  generalize ∏ w ∈ s, (b - w) = Pb
  have h1 : f a / ((a - b) * Pa) * (b - a) = -(f a / Pa) := by
    rw [show (a - b) * Pa = Pa * (a - b) from mul_comm _ _, ← div_div]
    generalize f a / Pa = g; field_simp; ring
  have h2 : f b / Pb / (b - a) * (b - a) = f b / Pb := by
    field_simp
  linear_combination hsum + h1 + h2

/-! ### Newton expansion -/

/-- The first `r` nodes `u 0, …, u (r-1)`. -/
def Vs (u : ℕ → F) (r : ℕ) : Finset F := (range r).image u

lemma Vs_zero (u : ℕ → F) : Vs u 0 = ∅ := by simp [Vs]

lemma Vs_succ (u : ℕ → F) (r : ℕ) : Vs u (r + 1) = insert (u r) (Vs u r) := by
  simp [Vs, Finset.range_add_one, Finset.image_insert]

lemma mem_Vs {u : ℕ → F} (hu : Function.Injective u) {r i : ℕ} : u i ∈ Vs u r ↔ i < r := by
  simp only [Vs, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, h⟩; exact (hu h) ▸ hj
  · intro h; exact ⟨i, h, rfl⟩

/-- Newton products `∏_{k<i} (x - u_k)`. -/
def Nn (u : ℕ → F) (x : F) (i : ℕ) : F := ∏ k ∈ range i, (x - u k)

/-- **Newton expansion** of `dd f (T ∪ {u_p})` in the divided differences `dd f (T ∪ {u_0..u_i})`. -/
theorem newton (f : F → F) (u : ℕ → F) (hu : Function.Injective u) (T : Finset F)
    (hT : ∀ z ∈ T, ∀ i, z ≠ u i) (p : ℕ) :
    dd f (insert (u p) T) =
      ∑ i ∈ range (p + 1), Nn u (u p) i * dd f (T ∪ Vs u (i + 1)) := by
  have key : ∀ r, r ≤ p → dd f (insert (u p) T) =
      ∑ i ∈ range r, Nn u (u p) i * dd f (T ∪ Vs u (i + 1)) +
        Nn u (u p) r * dd f (insert (u p) (T ∪ Vs u r)) := by
    intro r
    induction r with
    | zero => intro _; simp [Nn, Vs_zero]
    | succ r ih =>
      intro hr
      have hrp : r < p := hr
      rw [ih (by omega), Finset.sum_range_succ]
      have hs1 : u r ∉ T ∪ Vs u r := by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun h => hT _ h r rfl, fun h => by simpa using (mem_Vs hu).1 h⟩
      have hs2 : u p ∉ T ∪ Vs u r := by
        simp only [Finset.mem_union, not_or]
        exact ⟨fun h => hT _ h p rfl, fun h => by have := (mem_Vs hu).1 h; omega⟩
      have hne : u r ≠ u p := fun h => by have := hu h; omega
      have F1 := dd_F1 f (u r) (u p) (T ∪ Vs u r) hs1 hs2 hne
      have e1 : insert (u r) (T ∪ Vs u r) = T ∪ Vs u (r + 1) := by
        rw [Vs_succ, Finset.union_insert]
      have e2 : insert (u r) (insert (u p) (T ∪ Vs u r)) =
          insert (u p) (T ∪ Vs u (r + 1)) := by
        rw [← e1, Finset.insert_comm]
      rw [e1, e2] at F1
      have : Nn u (u p) (r + 1) = Nn u (u p) r * (u p - u r) := by
        simp [Nn, Finset.prod_range_succ]
      rw [this]
      have h3 : dd f (insert (u p) (T ∪ Vs u r)) =
          dd f (T ∪ Vs u (r + 1)) + dd f (insert (u p) (T ∪ Vs u (r + 1))) * (u p - u r) := by
        linear_combination (-1 : F) * F1
      rw [h3]; ring
  have := key p le_rfl
  rw [this, Finset.sum_range_succ]
  congr 2
  rw [Vs_succ, Finset.union_insert]

/-! ### Windows -/

/-- The window `{s, s+1, …, s+n}`. -/
def Win (s : F) (n : ℕ) : Finset F := (range (n + 1)).image fun t : ℕ => s + (t : F)

/-- Interior `{s+1, …, s+n}`. -/
def Int' (s : F) (n : ℕ) : Finset F := (range n).image fun t : ℕ => s + 1 + (t : F)

variable [CharZero F]

lemma Win_eq_insert (s : F) (n : ℕ) : Win s n = insert s (Int' s n) := by
  ext z
  simp only [Win, Int', Finset.mem_image, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨t, ht, rfl⟩
    cases t with
    | zero => left; simp
    | succ t => right; exact ⟨t, by omega, by push_cast; ring⟩
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨0, by omega, by simp⟩
    · exact ⟨t + 1, by omega, by push_cast; ring⟩

lemma Win_succ_eq_insert (s : F) (n : ℕ) : Win (s + 1) n = insert (s + ((n : F) + 1)) (Int' s n) := by
  ext z
  simp only [Win, Int', Finset.mem_image, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases h : t < n
    · right; exact ⟨t, h, by ring⟩
    · left; have : t = n := by omega
      subst this; ring
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨n, by omega, by ring⟩
    · exact ⟨t, by omega, by ring⟩

lemma Win_next (s : F) (n : ℕ) :
    Win s (n + 1) = insert s (insert (s + ((n : F) + 1)) (Int' s n)) := by
  rw [Win_eq_insert]
  congr 1
  ext z
  simp only [Int', Finset.mem_image, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases h : t < n
    · right; exact ⟨t, h, rfl⟩
    · left; have : t = n := by omega
      subst this; ring
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨n, by omega, by ring⟩
    · exact ⟨t, by omega, rfl⟩

lemma Int'_not_mem_left (s : F) (n : ℕ) : s ∉ Int' s n := by
  simp only [Int', Finset.mem_image, Finset.mem_range, not_exists, not_and]
  intro t _ h
  have : (1 : F) + (t : F) = 0 := by linear_combination h
  have h2 : ((1 + t : ℕ) : F) = 0 := by push_cast; exact this
  exact absurd (Nat.cast_eq_zero.1 h2) (by omega)

lemma Int'_not_mem_right (s : F) (n : ℕ) : s + ((n : F) + 1) ∉ Int' s n := by
  simp only [Int', Finset.mem_image, Finset.mem_range, not_exists, not_and]
  intro t ht h
  have h2 : ((t : ℕ) : F) = (n : F) := by linear_combination h
  have := Nat.cast_injective h2
  omega

lemma Win_zero (s : F) : Win s 0 = {s} := by simp [Win]

/-- window divided difference recursion -/
lemma dd_Win_succ (f : F → F) (s : F) (n : ℕ) :
    dd f (Win s (n + 1)) * ((n : F) + 1) = dd f (Win (s + 1) n) - dd f (Win s n) := by
  rw [Win_next, Win_succ_eq_insert, Win_eq_insert]
  have h := dd_F1 f s (s + ((n : F) + 1)) (Int' s n) (Int'_not_mem_left s n)
    (Int'_not_mem_right s n) (by
      intro h
      have : ((n : F) + 1) = 0 := by linear_combination -h
      have h2 : ((n + 1 : ℕ) : F) = 0 := by push_cast; exact this
      exact absurd (Nat.cast_eq_zero.1 h2) (by omega))
  rw [← h]; congr 1; ring

lemma dd_singleton (f : F → F) (s : F) : dd f {s} = f s := by simp [dd]

/-- value of the window divided differences of `(z)_K` -/
theorem dd_Win_pochr (K : ℕ) : ∀ (n : ℕ) (s : F),
    dd (fun z => pochr z K) (Win s n) = (K.choose n : F) * pochr (s + (n : F)) (K - n) := by
  intro n
  induction n with
  | zero => intro s; simp [Win_zero, dd_singleton, pochr]
  | succ n ih =>
    intro s
    have hn : ((n : F) + 1) ≠ 0 := by
      have : ((n + 1 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      simpa using this
    have h := dd_Win_succ (fun z => pochr z K) s n
    rw [ih (s + 1), ih s] at h
    apply mul_right_cancel₀ hn
    rw [h]
    by_cases hK : n + 1 ≤ K
    · obtain ⟨k, hk⟩ : ∃ k, K - n = k + 1 := ⟨K - n - 1, by omega⟩
      have hk2 : K - (n + 1) = k := by omega
      rw [hk, hk2]
      have f1 : pochr (s + 1 + (n : F)) (k + 1) =
          pochr (s + 1 + (n : F)) k * (s + 1 + (n : F) + (k : F)) := pochr_succ_right _ _
      have f2 : pochr (s + (n : F)) (k + 1) = (s + (n : F)) * pochr (s + 1 + (n : F)) k := by
        rw [pochr_succ_left]; congr 2; ring
      have f3 : pochr (s + ((n + 1 : ℕ) : F)) k = pochr (s + 1 + (n : F)) k := by
        congr 1; push_cast; ring
      have hc : (K.choose (n + 1) : F) * ((n : F) + 1) = (K.choose n : F) * ((k : F) + 1) := by
        have := Nat.choose_succ_right_eq K n
        rw [hk] at this
        exact_mod_cast this
      rw [f1, f2, f3]
      linear_combination (-(pochr (s + 1 + (n : F)) k)) * hc
    · have h1 : K - n = 0 := by omega
      have h2 : K - (n + 1) = 0 := by omega
      have h3 : K.choose (n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [h1, h2, h3]
      simp [pochr]

end CatalanCore.Star.Leonard
