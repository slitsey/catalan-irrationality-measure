module

public import CatalanFrames.P6Hybrid.Level
public import CatalanCore.Arith.Hybrid.Dual
public import CatalanCore.Arith.Hybrid.D1Exact

@[expose] public section

/-!
# The Z dual of the P6 hybrid (primes `p > N/2`)

For a good prime `p` with `r + 2m ≤ 2p` the level-1 tropical exponent is bounded using only the two
zero facts `p6_lev_zero_low`, `p6_lev_zero_win`.  A label `A` is *known zero* (`kz`) when one of them
applies.  The potentials depend on NO level data:

  `u_A = [¬kz A] + [kz A ∧ A + p is a column label]`,   `v_B = [¬kz B] + [kz B ∧ B + p is a row label]`

are feasible for `wt lev p` (a congruent pair `(A, B)`, `A ≠ B`, has `B = A ± p`; one of the two is `kz`
only if it is the lower one, and then its potential carries the `+1`).  The value is
`2r + 2m - Sv r m p` with `Sv` a sum of four interval counts (`zdual_value`).
-/

open Finset CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.P6

namespace CatalanFrames.P6Hybrid

open Classical

lemma kq6_cases (p : ℕ) :
    (p % 6 = 1 ∧ kq6 p = (p + 2) / 3) ∨ (p % 6 ≠ 1 ∧ kq6 p = (p + 1) / 2) := by
  unfold kq6; by_cases h : p % 6 = 1 <;> simp [h]

/-- known-zero labels -/
def kz (r p A : ℕ) : Prop := A < kq6 p ∨ (p % 6 = 1 ∧ (p + 1) / 2 ≤ A ∧ A < p ∧ r ≤ A)

/-- column / row labels of the hybrid matrix -/
def isColP (r m x : ℕ) : Prop := x < r ∨ (x < r + 2 * m ∧ (x - r) % 2 = 1)
def isRowP (r m x : ℕ) : Prop := x < r ∨ (x < r + 2 * m ∧ (x - r) % 2 = 0)

noncomputable def zu (r m p A : ℕ) : ℚ :=
  (if kz r p A then 0 else 1) + (if kz r p A ∧ isColP r m (A + p) then 1 else 0)

noncomputable def zv (r m p B : ℕ) : ℚ :=
  (if kz r p B then 0 else 1) + (if kz r p B ∧ isRowP r m (B + p) then 1 else 0)

lemma zu_nkz {r m p A : ℕ} (h : ¬ kz r p A) : zu r m p A = 1 := by simp [zu, h]
lemma zv_nkz {r m p B : ℕ} (h : ¬ kz r p B) : zv r m p B = 1 := by simp [zv, h]
lemma zu_kz {r m p A : ℕ} (h : kz r p A) (hc : isColP r m (A + p)) : zu r m p A = 1 := by
  simp [zu, h, hc]
lemma zv_kz {r m p B : ℕ} (h : kz r p B) (hc : isRowP r m (B + p)) : zv r m p B = 1 := by
  simp [zv, h, hc]
lemma zu_nonneg (r m p A : ℕ) : 0 ≤ zu r m p A := by unfold zu; split_ifs <;> norm_num
lemma zv_nonneg (r m p B : ℕ) : 0 ≤ zv r m p B := by unfold zv; split_ifs <;> norm_num

lemma kz_lt_p {r p A : ℕ} (h5 : 5 ≤ p) (h : kz r p A) : A < p := by
  rcases h with h | ⟨_, _, h, _⟩
  · rcases kq6_cases p with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  · exact h

lemma kz_lev {r m p A : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hA : A < r + 2 * m) (h : kz r p A) :
    (p6Inst r m).lev p A = 0 := by
  rcases h with h | ⟨h1, h2, h3, h4⟩
  · exact p6_lev_zero_low hp h5 h
  · exact p6_lev_zero_win hp h1 h2 h3 (by simp only [p6dok]; omega)

lemma cong_cases {p A B : ℕ} (hp : 0 < p) (hA : A < p) (hB : B < 2 * p)
    (h : (p : ℤ) ∣ (A : ℤ) - B) : B = A ∨ B = A + p := by
  obtain ⟨k, hk⟩ := h
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hA' : (A : ℤ) < p := by exact_mod_cast hA
  have hB' : (B : ℤ) < 2 * p := by exact_mod_cast hB
  have hk1 : k < 1 := by
    by_contra hc; have hc := not_lt.mp hc; nlinarith [(Nat.cast_nonneg B : (0 : ℤ) ≤ B)]
  have hk2 : -2 < k := by
    by_contra hc; have hc := not_lt.mp hc; nlinarith [(Nat.cast_nonneg A : (0 : ℤ) ≤ A)]
  have : k = 0 ∨ k = -1 := by omega
  rcases this with rfl | rfl
  · left; have : (A : ℤ) - B = 0 := by simpa using hk
    omega
  · right; have : (A : ℤ) - B = -p := by simpa using hk
    omega

lemma cong_cases' {p A B : ℕ} (hp : 0 < p) (hB : B < p) (hA : A < 2 * p)
    (h : (p : ℤ) ∣ (A : ℤ) - B) : A = B ∨ A = B + p := by
  have h' : (p : ℤ) ∣ (B : ℤ) - A := by rw [← dvd_neg]; simpa using h
  rcases cong_cases hp hB hA h' with h | h
  · left; exact h
  · right; exact h

/-- feasibility of the Z potentials on labels -/
lemma zdual_feas {r m p A B : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hN : r + 2 * m ≤ 2 * p)
    (hA : A < r + 2 * m) (hB : B < r + 2 * m) (hAr : isRowP r m A) (hBc : isColP r m B) :
    (wt (p6Inst r m).lev p A B : ℚ) ≤ zu r m p A + zv r m p B := by
  have hl : ∀ X, X < r + 2 * m → kz r p X → (p6Inst r m).lev p X = 0 :=
    fun X hX h => kz_lev hp h5 hX h
  have hp0 : 0 < p := by omega
  by_cases hAB : A = B
  · subst hAB
    by_cases hk : kz r p A
    · have : wt (p6Inst r m).lev p A A = 0 := by rw [wt_diag, hl A hA hk]; simp
      rw [this]; have := zu_nonneg r m p A; have := zv_nonneg r m p A; simpa using add_nonneg ‹_› ‹_›
    · have h2 : (wt (p6Inst r m).lev p A A : ℚ) ≤ 2 := by exact_mod_cast wt_le_two _ _ _ _
      rw [zu_nkz hk, zv_nkz hk]; linarith
  · by_cases hc : (p : ℤ) ∣ (A : ℤ) - B
    · have h2 : (wt (p6Inst r m).lev p A B : ℚ) ≤ 2 := by exact_mod_cast wt_le_two _ _ _ _
      by_cases hkA : kz r p A <;> by_cases hkB : kz r p B
      · exfalso
        have := cong_cases hp0 (kz_lt_p h5 hkA) (by have := kz_lt_p h5 hkB; omega) hc
        have := kz_lt_p h5 hkB
        omega
      · rcases cong_cases hp0 (kz_lt_p h5 hkA) (by omega) hc with e | e
        · exact absurd e.symm hAB
        · have : zu r m p A = 1 := zu_kz hkA (by rw [← e]; exact hBc)
          rw [this, zv_nkz hkB]; linarith
      · rcases cong_cases' hp0 (kz_lt_p h5 hkB) (by omega) hc with e | e
        · exact absurd e hAB
        · have : zv r m p B = 1 := zv_kz hkB (by rw [← e]; exact hAr)
          rw [this, zu_nkz hkA]; linarith
      · rw [zu_nkz hkA, zv_nkz hkB]; linarith
    · have h1 : (wt (p6Inst r m).lev p A B : ℚ) ≤ 1 := by
        exact_mod_cast wt_le_one_of_noncong hAB hc
      by_cases hkA : kz r p A <;> by_cases hkB : kz r p B
      · have : wt (p6Inst r m).lev p A B = 0 :=
          wt_eq_zero_of_blk hAB hc (by rw [hl A hA hkA, hl B hB hkB])
        rw [this]; have := zu_nonneg r m p A; have := zv_nonneg r m p B; simp; linarith
      · rw [zv_nkz hkB]; have := zu_nonneg r m p A; linarith
      · rw [zu_nkz hkA]; have := zv_nonneg r m p B; linarith
      · rw [zu_nkz hkA, zv_nkz hkB]; linarith


/-! ### The value of the potentials -/

lemma sum_ind_core (n lo hi : ℕ) :
    ∑ c ∈ range n, (if lo ≤ c ∧ c < hi then (1 : ℚ) else 0) = ((min hi n - lo : ℕ) : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : lo ≤ n ∧ n < hi
    · rw [if_pos h]
      have e : min hi (n + 1) - lo = min hi n - lo + 1 := by omega
      rw [e]; push_cast; ring
    · rw [if_neg h]
      have e : min hi (n + 1) - lo = min hi n - lo := by omega
      rw [e]; ring

lemma sum_ind_ext (r n lo hi : ℕ) :
    ∑ j ∈ range n, (if lo ≤ r + j ∧ r + j < hi then (1 : ℚ) else 0) =
      ((min hi (r + n) - max lo r : ℕ) : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : lo ≤ r + n ∧ r + n < hi
    · rw [if_pos h]
      have e : min hi (r + (n + 1)) - max lo r = min hi (r + n) - max lo r + 1 := by omega
      rw [e]; push_cast; ring
    · rw [if_neg h]
      have e : min hi (r + (n + 1)) - max lo r = min hi (r + n) - max lo r := by omega
      rw [e]; ring

lemma sum_pair (f : ℕ → ℚ) (m : ℕ) :
    ∑ i ∈ range m, (f (2 * i) + f (2 * i + 1)) = ∑ j ∈ range (2 * m), f j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- the interval-count saving -/
def Sv (r m p : ℕ) : ℕ :=
  (min (kq6 p) r - (r - p)) + (min (kq6 p) r - (r + 2 * m - p)) +
    (min (kq6 p) (r + 2 * m) - max (r + 2 * m - p) r) +
    (if p % 6 = 1 then min p (r + 2 * m) - max (max ((p + 1) / 2) (r + 2 * m - p)) r else 0)

lemma core_pt {r m p c : ℕ} (hc : c < r) (hp2 : p % 2 = 1) :
    zu r m p c + zv r m p c = 2 - (if r - p ≤ c ∧ c < kq6 p then 1 else 0) -
      (if r + 2 * m - p ≤ c ∧ c < kq6 p then 1 else 0) := by
  have hk := kq6_cases p
  unfold zu zv kz isColP isRowP
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

lemma core_sum {r m p : ℕ} (hp2 : p % 2 = 1) :
    ∑ c ∈ range r, (zu r m p c + zv r m p c) =
      2 * r - ((min (kq6 p) r - (r - p) : ℕ) : ℚ) - ((min (kq6 p) r - (r + 2 * m - p) : ℕ) : ℚ) := by
  rw [Finset.sum_congr rfl (fun c hc => core_pt (Finset.mem_range.mp hc) hp2)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_ind_core, sum_ind_core]
  simp; ring

/-- the extras: the pointwise function -/
noncomputable def hx (r m p x : ℕ) : ℚ :=
  1 - (if r + 2 * m - p ≤ x ∧ x < kq6 p then 1 else 0) -
    (if p % 6 = 1 ∧ (max ((p + 1) / 2) (r + 2 * m - p) ≤ x ∧ x < p) then 1 else 0)

lemma ext_pt_u {r m p i : ℕ} (hi : i < m) (hp2 : p % 2 = 1) :
    zu r m p (r + 2 * i) = hx r m p (r + (2 * i)) := by
  have hk := kq6_cases p
  unfold zu hx kz isColP
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

lemma ext_pt_v {r m p i : ℕ} (hi : i < m) (hp2 : p % 2 = 1) :
    zv r m p (r + 2 * i + 1) = hx r m p (r + (2 * i + 1)) := by
  have hk := kq6_cases p
  unfold zv hx kz isRowP
  split_ifs <;> first | (norm_num; done) | (exfalso; omega)

lemma ext_sum {r m p : ℕ} (hp2 : p % 2 = 1) :
    ∑ i ∈ range m, (zu r m p (r + 2 * i) + zv r m p (r + 2 * i + 1)) =
      2 * m - ((min (kq6 p) (r + 2 * m) - max (r + 2 * m - p) r : ℕ) : ℚ) -
        (if p % 6 = 1 then ((min p (r + 2 * m) - max (max ((p + 1) / 2) (r + 2 * m - p)) r : ℕ) : ℚ)
          else 0) := by
  rw [Finset.sum_congr rfl (fun i hi => by
    rw [ext_pt_u (Finset.mem_range.mp hi) hp2, ext_pt_v (Finset.mem_range.mp hi) hp2])]
  rw [sum_pair (fun j => hx r m p (r + j)) m]
  unfold hx
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_ind_ext]
  by_cases h : p % 6 = 1
  · simp only [h, true_and, if_true]
    rw [sum_ind_ext]; simp
  · simp [h]

lemma zdual_value {r m p : ℕ} (hp2 : p % 2 = 1) :
    potVal (zu r m p) (zv r m p) r m = 2 * r + 2 * m - (Sv r m p : ℚ) := by
  unfold potVal
  have h1 := core_sum (r := r) (m := m) hp2
  have h2 := ext_sum (r := r) (m := m) hp2
  unfold Sv
  rw [h1, h2]
  push_cast
  split_ifs <;> ring


/-- **The Z bound** (`2p ≥ N`): `tropVal + Sv ≤ 2r + 2m`. -/
theorem p6_trop_Z {r m p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hc : p % 6 = 1 ∨ p % 6 = 5)
    (hN : r + 2 * m ≤ 2 * p) :
    tropVal (HW (p6Inst r m).lev p r m) + Sv r m p ≤ 2 * r + 2 * m := by
  have hp2 : p % 2 = 1 := by omega
  have h := trop_HW_le (lev := (p6Inst r m).lev) p r m (zu r m p) (zv r m p) (by
    intro a b
    show (wt (p6Inst r m).lev p (Frame.hybRow r m a) (Frame.hybCol r m b) : ℚ) ≤ _
    refine zdual_feas hp h5 hN (Frame_hybRow_lt r m a) (Frame_hybCol_lt r m b) ?_ ?_
    · rcases a with c | i
      · left; simpa [Frame.hybRow] using c.2
      · right; have := i.2; simp [Frame.hybRow]
    · rcases b with c | i
      · left; simpa [Frame.hybCol] using c.2
      · right; have := i.2; simp [Frame.hybCol]; omega)
  rw [zdual_value hp2] at h
  have h' : ((tropVal (HW (p6Inst r m).lev p r m) + Sv r m p : ℕ) : ℚ) ≤ ((2 * r + 2 * m : ℕ) : ℚ) := by
    push_cast; linarith
  exact_mod_cast h'

/-- the H bound (`val_D1x`) in a form without the modulus -/
def Hb (r m p : ℕ) : ℕ := if m < p then 2 * r + 2 * m - min m (p - m) else 2 * r + 2 * m

theorem p6_trop_H {r m p : ℕ} (hp2 : p % 2 = 1) (hp0 : 0 < p) :
    tropVal (HW (p6Inst r m).lev p r m) ≤ Hb r m p := by
  have h := val_D1x (lev := (p6Inst r m).lev) p r hp2 hp0 m
  unfold Hb
  split_ifs with hm
  · rw [Nat.mod_eq_of_lt hm] at h; exact h
  · exact h.trans (Nat.sub_le _ _)

/-- the per-prime weight (natural numbers) -/
def Wn (r m p : ℕ) : ℕ :=
  if p % 6 = 1 then (if 32 * p ≤ 27 * r then Hb r m p else 2 * r + 2 * m - Sv r m p)
  else if p % 6 = 5 then (if 4 * p ≤ 3 * r then Hb r m p else 2 * r + 2 * m - Sv r m p)
  else 2 * r + 2 * m

/-- **`Wn` bounds the level-1 tropical exponent** at every prime. -/
theorem p6_trop_le_Wn {r m p : ℕ} (hp : p.Prime) (hr : 16 ≤ r) (h8 : r ≤ 8 * m)
    (h8' : 8 * m ≤ r + 9) : tropVal (HW (p6Inst r m).lev p r m) ≤ Wn r m p := by
  unfold Wn
  by_cases h1 : p % 6 = 1
  · have hp2 : p % 2 = 1 := by omega
    have hp0 : 0 < p := hp.pos
    rw [if_pos h1]
    split_ifs with hH
    · exact p6_trop_H hp2 hp0
    · have := p6_trop_Z (r := r) (m := m) hp (by omega) (Or.inl h1) (by omega)
      omega
  · by_cases h5 : p % 6 = 5
    · have hp2 : p % 2 = 1 := by omega
      have hp0 : 0 < p := hp.pos
      rw [if_neg h1, if_pos h5]
      split_ifs with hH
      · exact p6_trop_H hp2 hp0
      · have := p6_trop_Z (r := r) (m := m) hp (by omega) (Or.inr h5) (by omega)
        omega
    · rw [if_neg h1, if_neg h5]
      have h := trop_D1 (lev := (p6Inst r m).lev) p r m
      have : (tropVal (HW (p6Inst r m).lev p r m) : ℚ) ≤ ((2 * r + 2 * m : ℕ) : ℚ) := by
        push_cast; linarith
      exact_mod_cast this

end CatalanFrames.P6Hybrid
