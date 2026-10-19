module

public import CatalanCore.Arith.Hybrid.Values

@[expose] public section

/-!
# The exact dual D1 (DW §3): class-count potentials for `q < 2m`

For an odd modulus `q` (`h = (q+1)/2`, `2h = q+1`) the class of a label `A` is
`kap A = h (A + (q-1) r) mod q`; `A ≡ B (q)` implies `kap A = kap B`, and the zone nodes
`r + 2i` (`X'`), `r + 2i + 1` (`Y'`) have classes `i mod q` and `(i + h) mod q`.
With `m = Q q + s0` the potentials
`u = 1 - (P - Q')/2`, `v = 1 + (P - Q')/2` (`P k = [k < s0]`, `Q' k = [(k + q - h) mod q < s0]`)
are feasible for every `s0`, and their value is `2r + 2m - s0 + E`,
`E = (s0 - h) + (s0 + 1 - h)` (truncated).  Hence (`val_D1x`, `q = 2h - 1`):

  `tropVal (HW lev q r m) ≤ 2 r + 2 m - min (m % q) (q - m % q)`.

This is `2(r+m) - (m - M_q)` with `m - M_q = dist (m, qℤ)`.  No hypothesis on `lev`.
-/

open Finset

namespace CatalanCore.Arith.Hybrid

variable {lev : ℕ → ℕ → ℕ}

/-- Periodic sums. -/
lemma sum_range_mod (F : ℕ → ℚ) (q : ℕ) (hq : 0 < q) (m : ℕ) :
    ∑ i ∈ range m, F (i % q) =
      ((m / q : ℕ) : ℚ) * ∑ k ∈ range q, F k + ∑ k ∈ range (m % q), F k := by
  have hA : ∀ Q : ℕ, ∑ i ∈ range (Q * q), F (i % q) = (Q : ℚ) * ∑ k ∈ range q, F k := by
    intro Q
    induction Q with
    | zero => simp
    | succ Q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have : ∀ j ∈ range q, F ((Q * q + j) % q) = F j := by
        intro j hj
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
      rw [Finset.sum_congr rfl this]
      push_cast; ring
  have hm : m = (m / q) * q + m % q := by
    have := Nat.div_add_mod m q; linarith [Nat.mul_comm q (m / q)]
  have hs : m % q < q := Nat.mod_lt _ hq
  conv_lhs => rw [hm]
  rw [Finset.sum_range_add, hA]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.mul_comm, Nat.mul_add_mod]
  congr 1
  exact Nat.mod_eq_of_lt (by have := Finset.mem_range.mp hj; omega)

section D1x

variable (q r : ℕ)

/-- Class of a label modulo `q` (as an index in `[0, q)`). -/
def kap (A : ℕ) : ℕ := ((q + 1) / 2 * (A + (q - 1) * r)) % q

lemma kap_congr (hq : 0 < q) {A B : ℕ} (h : (q : ℤ) ∣ (A : ℤ) - B) : kap q r A = kap q r B := by
  have h1 : (A + (q - 1) * r) ≡ (B + (q - 1) * r) [MOD q] := by
    rw [Nat.modEq_iff_dvd]
    have : ((B + (q - 1) * r : ℕ) : ℤ) - ((A + (q - 1) * r : ℕ) : ℤ) = -((A : ℤ) - B) := by
      push_cast; ring
    rw [this]; exact (dvd_neg).mpr h
  exact (h1.mul_left ((q + 1) / 2))

lemma kap_X (hodd : q % 2 = 1) (hq : 0 < q) (i : ℕ) : kap q r (r + 2 * i) = i % q := by
  unfold kap
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hh : 2 * ((q' + 1 + 1) / 2) = q' + 1 + 1 := by omega
  set h := (q' + 1 + 1) / 2
  have e1 : (r + 2 * i) + (q' + 1 - 1) * r = (q' + 1) * r + 2 * i := by simp; ring
  have e2 : h * ((q' + 1) * r + 2 * i) = (q' + 1) * (h * r + i) + i := by
    have : h * ((q' + 1) * r + 2 * i) = h * (q' + 1) * r + (2 * h) * i := by ring
    rw [this, hh]; ring
  rw [e1, e2, Nat.mul_add_mod]

lemma kap_Y (hodd : q % 2 = 1) (hq : 0 < q) (i : ℕ) :
    kap q r (r + 2 * i + 1) = (i + (q + 1) / 2) % q := by
  unfold kap
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hh : 2 * ((q' + 1 + 1) / 2) = q' + 1 + 1 := by omega
  set h := (q' + 1 + 1) / 2
  have e1 : (r + 2 * i + 1) + (q' + 1 - 1) * r = (q' + 1) * r + 2 * i + 1 := by simp; ring
  have e2 : h * ((q' + 1) * r + 2 * i + 1) = (q' + 1) * (h * r + i) + (i + h) := by
    have : h * ((q' + 1) * r + 2 * i + 1) = h * (q' + 1) * r + (2 * h) * i + h := by ring
    rw [this, hh]; ring
  rw [e1, e2, Nat.mul_add_mod]

/-- The two indicator functions and the potentials. -/
def Pind (s0 k : ℕ) : ℚ := if k < s0 then 1 else 0

def Qind (s0 k : ℕ) : ℚ := if (k + (q - (q + 1) / 2)) % q < s0 then 1 else 0

noncomputable def Fk (s0 k : ℕ) : ℚ := 1 - (Pind s0 k - Qind q s0 k) / 2

noncomputable def Gk (s0 k : ℕ) : ℚ := 1 + (Pind s0 k - Qind q s0 k) / 2

lemma Fk_ge (s0 k : ℕ) : 1 / 2 ≤ Fk q s0 k := by
  unfold Fk Pind Qind; split_ifs <;> norm_num

lemma Gk_ge (s0 k : ℕ) : 1 / 2 ≤ Gk q s0 k := by
  unfold Gk Pind Qind; split_ifs <;> norm_num

lemma FG_sum (s0 k : ℕ) : Fk q s0 k + Gk q s0 k = 2 := by
  unfold Fk Gk; ring

/-- Feasibility: the class potentials are dual feasible for every `s0`. -/
theorem trop_D1x_pot (m s0 : ℕ) (hq : 0 < q) :
    (tropVal (HW lev q r m) : ℚ) ≤
      potVal (fun A => Fk q s0 (kap q r A)) (fun A => Gk q s0 (kap q r A)) r m := by
  apply trop_HW_le
  intro a b
  set A := Frame.hybRow r m a
  set B := Frame.hybCol r m b
  show (wt lev q A B : ℚ) ≤ Fk q s0 (kap q r A) + Gk q s0 (kap q r B)
  by_cases hc : (q : ℤ) ∣ (A : ℤ) - B
  · rw [kap_congr q r hq hc, FG_sum]
    exact wt_le_two' (lev := lev) A B
  · have hne : A ≠ B := by
      intro h; apply hc; rw [h]; simp
    have h1 := wt_le_one' (lev := lev) hne hc
    have := Fk_ge q s0 (kap q r A)
    have := Gk_ge q s0 (kap q r B)
    linarith

end D1x


section D1val

variable (q r : ℕ)

lemma Qind_shift (hq : 0 < q) (hh : (q + 1) / 2 ≤ q) (s0 i : ℕ) :
    Qind q s0 ((i + (q + 1) / 2) % q) = Pind s0 (i % q) := by
  unfold Qind Pind
  have : ((i + (q + 1) / 2) % q + (q - (q + 1) / 2)) % q = i % q := by
    rw [Nat.mod_add_mod]
    have : i + (q + 1) / 2 + (q - (q + 1) / 2) = i + q := by omega
    rw [this, Nat.add_mod_right]
  rw [this]

lemma card_filter_shift (hq : 0 < q) (c s0 : ℕ) :
    ((range q).filter (fun k => (k + c) % q < s0)).card ≤ s0 := by
  have : ((range q).filter (fun k => (k + c) % q < s0)).card ≤ (range s0).card := by
    apply Finset.card_le_card_of_injOn (fun k => (k + c) % q)
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk
      simp only [Finset.coe_range, Set.mem_Iio]
      exact hk.2
    · intro k hk k' hk' hkk
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk hk'
      have h1 : (k + c) ≡ (k' + c) [MOD q] := hkk
      have h2 := Nat.ModEq.add_right_cancel' c h1
      have : k % q = k' % q := h2
      rwa [Nat.mod_eq_of_lt hk.1, Nat.mod_eq_of_lt hk'.1] at this
  simpa using this

lemma sumP_full (s0 : ℕ) (hs : s0 ≤ q) : ∑ k ∈ range q, Pind s0 k = s0 := by
  unfold Pind
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : (range q).filter (fun k => k < s0) = range s0 := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this]; simp

lemma sumP_part (s0 : ℕ) : ∑ k ∈ range s0, Pind s0 k = s0 := by
  unfold Pind
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℚ))]
  · simp
  · intro k hk; rw [if_pos (Finset.mem_range.mp hk)]

lemma sumQ_full (hq : 0 < q) (s0 : ℕ) : ∑ k ∈ range q, Qind q s0 k ≤ s0 := by
  unfold Qind
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast card_filter_shift q hq _ s0

lemma sumP3_full (hq : 0 < q) (s0 : ℕ) :
    ∑ k ∈ range q, Pind s0 ((k + (q + 1) / 2) % q) ≤ s0 := by
  unfold Pind
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast card_filter_shift q hq _ s0

lemma sumQ_part (hodd : q % 2 = 1) (s0 : ℕ) (hs : s0 < q) :
    ∑ k ∈ range s0, Qind q s0 k ≤
      (((s0 - (q + 1) / 2) + (s0 + 1 - (q + 1) / 2) : ℕ) : ℚ) := by
  unfold Qind
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : ((range s0).filter (fun k => (k + (q - (q + 1) / 2)) % q < s0)).card ≤
      (Ico ((q + 1) / 2) s0 ∪ range (s0 + 1 - (q + 1) / 2)).card := by
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_range]
    by_cases hkh : (q + 1) / 2 ≤ k
    · left; exact ⟨hkh, hk.1⟩
    · right
      have hlt : k + (q - (q + 1) / 2) < q := by omega
      have := hk.2
      rw [Nat.mod_eq_of_lt hlt] at this
      omega
  have h2 := this.trans (Finset.card_union_le _ _)
  simp only [Nat.card_Ico, Finset.card_range] at h2
  exact_mod_cast h2

lemma sumP3_part (hodd : q % 2 = 1) (s0 : ℕ) (hs : s0 < q) :
    ∑ k ∈ range s0, Pind s0 ((k + (q + 1) / 2) % q) ≤
      (((s0 - (q + 1) / 2) + (s0 + 1 - (q + 1) / 2) : ℕ) : ℚ) := by
  unfold Pind
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have : ((range s0).filter (fun k => (k + (q + 1) / 2) % q < s0)).card ≤
      (range (s0 - (q + 1) / 2) ∪ Ico ((q + 1) / 2 - 1) s0).card := by
    apply Finset.card_le_card
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_union, Finset.mem_Ico, Finset.mem_range]
    by_cases hkq : k + (q + 1) / 2 < q
    · left
      have := hk.2
      rw [Nat.mod_eq_of_lt hkq] at this
      omega
    · right
      omega
  have h2 := this.trans (Finset.card_union_le _ _)
  simp only [Nat.card_Ico, Finset.card_range] at h2
  have h3 : (((s0 - (q + 1) / 2) + (s0 - ((q + 1) / 2 - 1)) : ℕ) : ℚ) =
      (((s0 - (q + 1) / 2) + (s0 + 1 - (q + 1) / 2) : ℕ) : ℚ) := by
    congr 1; omega
  have h4 : ((((range s0).filter (fun k => (k + (q + 1) / 2) % q < s0)).card : ℕ) : ℚ) ≤
      (((s0 - (q + 1) / 2) + (s0 - ((q + 1) / 2 - 1)) : ℕ) : ℚ) := by exact_mod_cast h2
  linarith

/-- **The exact D1 bound.**  `tropVal (HW q r m) ≤ 2 r + 2 m - dist (m, q ℤ)` for odd `q`. -/
theorem val_D1x (hodd : q % 2 = 1) (hq : 0 < q) (m : ℕ) :
    tropVal (HW lev q r m) ≤ 2 * r + 2 * m - min (m % q) (q - m % q) := by
  set s0 := m % q with hs0
  set Qn := m / q with hQn
  set h := (q + 1) / 2 with hh
  have hs : s0 < q := Nat.mod_lt _ hq
  have hhq : h ≤ q := by omega
  have hpot := trop_D1x_pot (lev := lev) q r m s0 hq
  unfold potVal at hpot
  have hC : ∑ c ∈ range r, (Fk q s0 (kap q r c) + Gk q s0 (kap q r c)) = 2 * r := by
    rw [Finset.sum_congr rfl (g := fun _ => (2 : ℚ))]
    · simp; ring
    · intro c _; exact FG_sum q s0 _
  have hZ : ∑ i ∈ range m, (Fk q s0 (kap q r (r + 2 * i)) + Gk q s0 (kap q r (r + 2 * i + 1))) =
      2 * m - ∑ i ∈ range m, Pind s0 (i % q) + (1 / 2) * ∑ i ∈ range m, Qind q s0 (i % q) +
        (1 / 2) * ∑ i ∈ range m, Pind s0 ((i % q + h) % q) := by
    have : ∀ i ∈ range m, Fk q s0 (kap q r (r + 2 * i)) + Gk q s0 (kap q r (r + 2 * i + 1)) =
        2 - Pind s0 (i % q) + (1 / 2) * Qind q s0 (i % q) +
          (1 / 2) * Pind s0 ((i % q + h) % q) := by
      intro i _
      rw [kap_X q r hodd hq, kap_Y q r hodd hq]
      have e1 : (i + h) % q = (i % q + h) % q := by rw [Nat.mod_add_mod]
      have e2 : Qind q s0 ((i + h) % q) = Pind s0 (i % q) := Qind_shift q hq hhq s0 i
      unfold Fk Gk
      rw [e2, e1]
      ring
    rw [Finset.sum_congr rfl this]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp
    ring
  have hS1 := sum_range_mod (Pind s0) q hq m
  have hS2 := sum_range_mod (Qind q s0) q hq m
  have hS3 := sum_range_mod (fun k => Pind s0 ((k + h) % q)) q hq m
  rw [sumP_full q s0 hs.le, sumP_part] at hS1
  have hQ1 := sumQ_full q hq s0
  have hQ2 := sumQ_part q hodd s0 hs
  have hP1 := sumP3_full q hq s0
  have hP2 := sumP3_part q hodd s0 hs
  have hQn : (0 : ℚ) ≤ Qn := Nat.cast_nonneg _
  set E : ℚ := (((s0 - h) + (s0 + 1 - h) : ℕ) : ℚ) with hE
  have hS2' : ∑ i ∈ range m, Qind q s0 (i % q) ≤ Qn * s0 + E := by
    rw [hS2]; nlinarith
  have hS3' : ∑ i ∈ range m, Pind s0 ((i % q + h) % q) ≤ Qn * s0 + E := by
    rw [hS3]; nlinarith
  have hS1' : ∑ i ∈ range m, Pind s0 (i % q) = Qn * s0 + s0 := hS1
  have hmQ : (m : ℚ) = Qn * q + s0 := by
    have := Nat.div_add_mod m q
    have h2 : (q * (m / q) + m % q : ℕ) = m := this
    have h3 : (((q * (m / q) + m % q : ℕ)) : ℚ) = m := by exact_mod_cast h2
    push_cast at h3
    nlinarith
  have hpot' : (tropVal (HW lev q r m) : ℚ) ≤
      ∑ c ∈ range r, (Fk q s0 (kap q r c) + Gk q s0 (kap q r c)) +
      ∑ i ∈ range m, (Fk q s0 (kap q r (r + 2 * i)) + Gk q s0 (kap q r (r + 2 * i + 1))) := hpot
  rw [hC, hZ] at hpot'
  have hval : (tropVal (HW lev q r m) : ℚ) ≤ 2 * r + 2 * m - s0 + E := by
    rw [hS1'] at hpot'
    linarith
  have hnat : tropVal (HW lev q r m) + s0 ≤ 2 * r + 2 * m + ((s0 - h) + (s0 + 1 - h)) := by
    have : ((tropVal (HW lev q r m) + s0 : ℕ) : ℚ) ≤
        ((2 * r + 2 * m + ((s0 - h) + (s0 + 1 - h)) : ℕ) : ℚ) := by
      push_cast
      have : ((((s0 - h) + (s0 + 1 - h) : ℕ)) : ℚ) = E := rfl
      push_cast at this
      linarith
    exact_mod_cast this
  omega

end D1val

end CatalanCore.Arith.Hybrid
