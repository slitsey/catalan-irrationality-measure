module

public import CatalanCore.Uniform.Content.Sweep.RowE1

@[expose] public section

/-!
# Row `P₁` (lane H, wave H2b; ledger P213, Theorem R★ of `PLANE2-ROW-SIMPLIFICATION`)

For `p ≤ 2m` write `2m = k p + s`, `k = 2k' + e`, `e ∈ {0, 1}`, `0 ≤ s < p`; `E = [r, r + s)` for `e = 0` and
`E = [r + s, r + p)` for `e = 1`.  For every symmetric dual `w` of the cell weight `W₃` on `E` (here a
function of the node, which contains the paper's function of the cell) and every member of the family
(window rows `r + 2 i`, columns `r + 2 i + 1`, retained common nodes `c` below `r`),
`GLE p (3 (r + m) − 3 ‖m‖_p + ∑_{t ∈ E} w t)` of the determinant.

The potential on the label nodes `L = [r, κp) ∪ [N, h*) ∪ [h*, N)` is `ψ ∘ sh`, `sh t = t − 2k'p` for
`t ≥ h* = (κ + 2k') p`, with `ψ = w` on `E` and `ψ = 1` in the period `j₀`, `2` elsewhere.  The pair
inequalities are `Q1` (congruent images), `Q2` (non-congruent images); the sum condition of
`RowNodes.member_gle_P` is an equality, proved on the images by splitting the intervals.
-/

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep.Gen

namespace CatalanCore.Uniform.Content.Sweep

section P1Tools

theorem div_win {p u j : ℕ} (hp : 0 < p) : u / p = j ↔ j * p ≤ u ∧ u < j * p + p := by
  rw [Nat.div_eq_iff hp]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> omega

theorem div_le_win {p n b : ℕ} (hp : 0 < p) (h : n < b * p + p) : n / p ≤ b := by
  have : n / p < b + 1 := (Nat.div_lt_iff_lt_mul hp).2 (by rw [Nat.add_mul, Nat.one_mul]; exact h)
  omega

theorem le_div_win {p n b : ℕ} (hp : 0 < p) (h : b * p ≤ n) : b ≤ n / p :=
  (Nat.le_div_iff_mul_le hp).2 h

theorem sub_mul_div' {p x a : ℕ} : (x - a * p) / p = x / p - a := by
  have := Nat.sub_mul_div x p a
  rwa [Nat.mul_comm p a] at this

theorem sub_mul_mod' {p x a : ℕ} (h : a * p ≤ x) : (x - a * p) % p = x % p := by
  have h' : p * a ≤ x := by rwa [Nat.mul_comm] at h
  have := Nat.sub_mul_mod h'
  rwa [Nat.mul_comm p a] at this

theorem cong_gap {p n n' : ℕ} (hp : 0 < p) (h : n % p = n' % p) (hlt : n < n') :
    ∃ q, n' = n + q * p ∧ 1 ≤ q := by
  have hd : (n' - n) % p = 0 := Nat.sub_mod_eq_zero_of_mod_eq h.symm
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hd
  refine ⟨q, ?_, ?_⟩
  · rw [Nat.mul_comm] at hq; omega
  · rcases Nat.eq_zero_or_pos q with h0 | h0
    · subst h0; simp at hq; omega
    · exact h0

theorem no_mult_between {p a q : ℕ} (hp : 0 < p) (h1 : a * p < q * p) (h2 : q * p < a * p + p) : False := by
  have h3 : a < q := Nat.lt_of_mul_lt_mul_right h1
  have h4 : (a + 1) * p ≤ q * p := Nat.mul_le_mul_right p h3
  rw [Nat.add_mul, Nat.one_mul] at h4
  omega

theorem w3_le_two (c c' : ℕ × ℕ) : w3 c c' ≤ 2 := by unfold w3; split_ifs <;> omega

theorem w3_diff {p t t' : ℕ} (h : t / p ≠ t' / p) : w3 (cell p t) (cell p t') = 2 := by
  unfold w3 cell
  have : (t / p, half p t) ≠ (t' / p, half p t') := fun h' => h (congrArg Prod.fst h')
  rw [if_neg this]
  simp [h]

theorem w3_same {p t t' : ℕ} (h : t / p = t' / p) : w3 (cell p t) (cell p t') ≤ 1 := by
  unfold w3 cell
  simp only [h]
  split_ifs <;> simp

theorem cnt_even (r a n : ℕ) (ha : r ≤ a) :
    ∑ t ∈ Finset.Ico a (a + n), (if (t - r) % 2 = 0 then 1 else 0) =
      if (a - r) % 2 = 0 then (n + 1) / 2 else n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Nat.add_assoc, Finset.sum_Ico_succ_top (by omega), ih]
    split_ifs <;> omega

end P1Tools


section P1Pot

/-- The potential in image coordinates: `w` on `E = [lo, hi)`, else `1` in the period `j₀` and `2` elsewhere;
`fl = true` means `j₀ = κ − 1` (the nodes below `A`), `fl = false` means `j₀ = κ` (the nodes in `[A, A + p)`). -/
def psi (p A lo hi : ℕ) (fl : Bool) (w : ℕ → ℕ) (u : ℕ) : ℕ :=
  if lo ≤ u ∧ u < hi then w u
  else if fl then (if u < A then 1 else 2) else (if A ≤ u ∧ u < A + p then 1 else 2)

theorem psi_true (p A lo hi : ℕ) (w : ℕ → ℕ) (u : ℕ) :
    psi p A lo hi true w u = if lo ≤ u ∧ u < hi then w u else (if u < A then 1 else 2) := rfl

theorem psi_false (p A lo hi : ℕ) (w : ℕ → ℕ) (u : ℕ) :
    psi p A lo hi false w u =
      if lo ≤ u ∧ u < hi then w u else (if A ≤ u ∧ u < A + p then 1 else 2) := rfl

/-- The image coordinates of the labels. -/
def InIm (r A Itop N hs t : ℕ) : Prop := r ≤ t ∧ (t < A ∨ t < Itop ∨ (N ≤ t ∧ t < hs))

/-- Numerical facts of the setting: `2 m = (2 k' + e) p + s`, `A = b0 p + p`, `h* = A + D2`, `N = Itop + D2`. -/
structure Geo (p r s e k' b0 lo hi Itop D2 N : ℕ) : Prop where
  p5 : 5 ≤ p
  odd : p % 2 = 1
  b0le : b0 * p ≤ r
  rlt : r < b0 * p + p
  slt : s < p
  spar : s % 2 = e
  hD2 : D2 = (2 * k') * p
  hk : e = 1 ∨ 2 * p ≤ D2
  hE : (e = 0 ∧ lo = r ∧ hi = r + s ∧ Itop = r + s) ∨
    (e = 1 ∧ lo = r + s ∧ hi = r + p ∧ Itop = r + p + s)
  hN : N = Itop + D2

theorem per_b0 {p b0 x : ℕ} (hp : 0 < p) (h1 : b0 * p ≤ x) (h2 : x < b0 * p + p) : x / p = b0 :=
  (div_win hp).2 ⟨h1, h2⟩

theorem per_b1 {p b0 x : ℕ} (hp : 0 < p) (h1 : b0 * p + p ≤ x) (h2 : x < b0 * p + p + p) :
    x / p = b0 + 1 := by
  have e : (b0 + 1) * p = b0 * p + p := by rw [Nat.add_mul, Nat.one_mul]
  exact (div_win hp).2 ⟨by rw [e]; exact h1, by rw [e]; exact h2⟩

variable {p r s e k' b0 lo hi Itop D2 N : ℕ}

/-- Congruent images: the potentials add up to at least `3`. -/
theorem Q1 (G : Geo p r s e k' b0 lo hi Itop D2 N) (fl : Bool) (w : ℕ → ℕ) {t t' : ℕ}
    (ht : InIm r (b0 * p + p) Itop N (b0 * p + p + D2) t)
    (ht' : InIm r (b0 * p + p) Itop N (b0 * p + p + D2) t')
    (hlt : t < t') (hc : t % p = t' % p) :
    3 ≤ psi p (b0 * p + p) lo hi fl w t + psi p (b0 * p + p) lo hi fl w t' := by
  obtain ⟨hp5, hodd, hb0, hrl, hs, hsp, hD2, hk, hE, hN⟩ := G
  have hp0 : 0 < p := by omega
  obtain ⟨q, hq, hq1⟩ := cong_gap hp0 hc hlt
  have hqp : p ≤ q * p := Nat.le_mul_of_pos_left p hq1
  have hbet : ¬ (D2 < q * p ∧ q * p < D2 + p) := by
    rintro ⟨h1, h2⟩
    rw [hD2] at h1 h2
    exact no_mult_between hp0 h1 h2
  unfold InIm at ht ht'
  cases fl
  · rw [psi_false, psi_false]
    split_ifs <;> omega
  · rw [psi_true, psi_true]
    split_ifs <;> omega

theorem Q2E (G : Geo p r s e k' b0 lo hi Itop D2 N) {fl : Bool} {w : ℕ → ℕ}
    (hfl : fl = true ↔ (lo < b0 * p + p ∧ ∀ t, lo ≤ t → t < hi → b0 * p + p ≤ t → 1 ≤ w t))
    (hdual : ∀ t t', lo ≤ t → t < hi → lo ≤ t' → t' < hi → w3 (cell p t) (cell p t') ≤ w t + w t')
    {t t' : ℕ} (ht : lo ≤ t ∧ t < hi) (ht' : InIm r (b0 * p + p) Itop N (b0 * p + p + D2) t')
    (hn' : ¬ (lo ≤ t' ∧ t' < hi)) :
    w3 (cell p t) (cell p t') ≤ w t + psi p (b0 * p + p) lo hi fl w t' := by
  obtain ⟨hp5, hodd, hb0, hrl, hs, hsp, hD2, hk, hE, hN⟩ := G
  have hp0 : 0 < p := by omega
  have hw3 := w3_le_two (cell p t) (cell p t')
  have htr : r ≤ t ∧ t < r + p := by omega
  have ht'r : r ≤ t' := ht'.1
  cases fl
  · -- `j₀ = κ`
    rw [psi_false, if_neg hn']
    by_cases hJ : b0 * p + p ≤ t' ∧ t' < b0 * p + p + p
    · rw [if_pos (by omega)]
      have e1 : t' / p = b0 + 1 := per_b1 hp0 hJ.1 hJ.2
      by_cases hper : t / p = t' / p
      · have := w3_same (p := p) hper; omega
      · have hlt : t < b0 * p + p := by
          by_contra hge
          apply hper
          rw [e1]; exact per_b1 hp0 (by omega) (by omega)
        have hnf : ¬ (lo < b0 * p + p ∧ ∀ t, lo ≤ t → t < hi → b0 * p + p ≤ t → 1 ≤ w t) := by
          intro h; exact absurd (hfl.2 h) (by simp)
        have hlo : lo < b0 * p + p := by omega
        have hex : ∃ t₁, lo ≤ t₁ ∧ t₁ < hi ∧ b0 * p + p ≤ t₁ ∧ ¬ 1 ≤ w t₁ := by
          by_contra hno
          apply hnf
          refine ⟨hlo, fun t₁ h1 h2 h3 => ?_⟩
          by_contra hh
          exact hno ⟨t₁, h1, h2, h3, hh⟩
        obtain ⟨t₁, h1, h2, h3, h4⟩ := hex
        have hd := hdual t t₁ ht.1 ht.2 h1 h2
        have p1 : t / p = b0 := per_b0 hp0 (by omega) hlt
        have p2 : t₁ / p = b0 + 1 := per_b1 hp0 h3 (by omega)
        have : w3 (cell p t) (cell p t₁) = 2 := w3_diff (by omega)
        omega
    · rw [if_neg hJ]; omega
  · -- `j₀ = κ − 1`
    rw [psi_true, if_neg hn']
    by_cases hJ : t' < b0 * p + p
    · rw [if_pos hJ]
      have e1 : t' / p = b0 := per_b0 hp0 (by omega) hJ
      by_cases hper : t / p = t' / p
      · have := w3_same (p := p) hper; omega
      · have hge : b0 * p + p ≤ t := by
          by_contra hlt
          apply hper
          rw [e1]; exact per_b0 hp0 (by omega) (by omega)
        have := (hfl.1 rfl).2 t ht.1 ht.2 hge
        omega
    · rw [if_neg hJ]; omega

/-- Non-congruent images: the potentials dominate the cell weight. -/
theorem Q2 (G : Geo p r s e k' b0 lo hi Itop D2 N) {fl : Bool} {w : ℕ → ℕ}
    (hfl : fl = true ↔ (lo < b0 * p + p ∧ ∀ t, lo ≤ t → t < hi → b0 * p + p ≤ t → 1 ≤ w t))
    (hdual : ∀ t t', lo ≤ t → t < hi → lo ≤ t' → t' < hi → w3 (cell p t) (cell p t') ≤ w t + w t')
    {t t' : ℕ} (ht : InIm r (b0 * p + p) Itop N (b0 * p + p + D2) t)
    (ht' : InIm r (b0 * p + p) Itop N (b0 * p + p + D2) t') :
    w3 (cell p t) (cell p t') ≤
      psi p (b0 * p + p) lo hi fl w t + psi p (b0 * p + p) lo hi fl w t' := by
  by_cases h1 : lo ≤ t ∧ t < hi
  · have e1 : psi p (b0 * p + p) lo hi fl w t = w t := by unfold psi; rw [if_pos h1]
    by_cases h2 : lo ≤ t' ∧ t' < hi
    · have e2 : psi p (b0 * p + p) lo hi fl w t' = w t' := by unfold psi; rw [if_pos h2]
      rw [e1, e2]; exact hdual t t' h1.1 h1.2 h2.1 h2.2
    · rw [e1]; exact Q2E G hfl hdual h1 ht' h2
  · by_cases h2 : lo ≤ t' ∧ t' < hi
    · have e2 : psi p (b0 * p + p) lo hi fl w t' = w t' := by unfold psi; rw [if_pos h2]
      rw [e2, w3_symm]
      have := Q2E G hfl hdual h2 ht h1
      omega
    · have hw3 := w3_le_two (cell p t) (cell p t')
      cases fl
      · rw [psi_false, psi_false, if_neg h1, if_neg h2]; split_ifs <;> omega
      · rw [psi_true, psi_true, if_neg h1, if_neg h2]; split_ifs <;> omega

end P1Pot

section P1Pair

/-- The shift of the labels beyond `h*` onto the image coordinates. -/
def shn (hs D2 u : ℕ) : ℕ := if hs ≤ u then u - D2 else u

/-- The potential on the label nodes (`3` below `r`). -/
def phin (p A lo hi hs D2 r : ℕ) (fl : Bool) (w : ℕ → ℕ) (u : ℕ) : ℕ :=
  if u < r then 3 else psi p A lo hi fl w (shn hs D2 u)

theorem shn_of_le {hs D2 u : ℕ} (h : hs ≤ u) : shn hs D2 u = u - D2 := by unfold shn; rw [if_pos h]

theorem shn_of_lt {hs D2 u : ℕ} (h : u < hs) : shn hs D2 u = u := by unfold shn; rw [if_neg (by omega)]

theorem w3_congr {p a b a' b' : ℕ} (h1 : half p a = half p a') (h2 : half p b = half p b')
    (h3 : a / p = b / p ↔ a' / p = b' / p) :
    w3 (cell p a) (cell p b) = w3 (cell p a') (cell p b') := by
  unfold w3 cell
  simp only [Prod.mk.injEq, h1, h2, h3]

variable {p r s e k' b0 lo hi Itop D2 N : ℕ}

/-- Period and residue data of one label node under the shift. -/
theorem shift_data (G : Geo p r s e k' b0 lo hi Itop D2 N) {x : ℕ} (hx : r ≤ x) :
    (b0 * p + p + D2 ≤ x → (x - D2) % p = x % p ∧ (x - D2) / p + 2 * k' = x / p ∧
      b0 + 1 + 2 * k' ≤ x / p) ∧
    (x < b0 * p + p + D2 → (x < b0 * p + p → x / p = b0) ∧ (N ≤ x → b0 + 2 ≤ x / p)) := by
  obtain ⟨hp5, hodd, hb0, hrl, hs, hsp, hD2, hk, hE, hN⟩ := G
  have hp0 : 0 < p := by omega
  constructor
  · intro h
    have h1 : (2 * k') * p ≤ x := by rw [← hD2]; omega
    have h3 : b0 + 1 + 2 * k' ≤ x / p := by
      apply le_div_win hp0
      have : (b0 + 1 + 2 * k') * p = b0 * p + p + D2 := by rw [hD2]; ring
      omega
    have h4 := le_div_win hp0 h1
    have h5 : (x - D2) / p = x / p - 2 * k' := by rw [hD2]; exact sub_mul_div'
    have h6 : (x - D2) % p = x % p := by rw [hD2]; exact sub_mul_mod' h1
    exact ⟨h6, by omega, h3⟩
  · intro h
    refine ⟨fun h2 => per_b0 hp0 (by omega) h2, fun h2 => ?_⟩
    apply le_div_win hp0
    have : (b0 + 2) * p = b0 * p + 2 * p := by ring
    omega

theorem kind_eq {A D2 N n n' : ℕ}
    (h : (n < A ∧ n' < A) ∨ (N ≤ n ∧ n < A + D2 ∧ N ≤ n' ∧ n' < A + D2) ∨ (A + D2 ≤ n ∧ A + D2 ≤ n')) :
    (A + D2 ≤ n ↔ A + D2 ≤ n') := by
  constructor <;> intro h' <;> omega

theorem class_eq [hp : Fact p.Prime] (hodd : p % 2 = 1) (b0 r n n' : ℕ) (hnr : r ≤ n) (hnr' : r ≤ n')
    (hpar : (n - r) % 2 ≠ (n' - r) % 2) (hper : n / p = n' / p) :
    oc p (b0 + 1) ((r + 1) % 2) (n % p) = oc p (b0 + 1) (1 - (r + 1) % 2) (n' % p) := by
  rw [ocR_eq hodd (b0 + 1) r n, ocC_eq hodd (b0 + 1) r n']
  split_ifs <;> omega

/-- The aggregate facts of a pair of label nodes under the shift. -/
theorem p1_aux (G : Geo p r s e k' b0 lo hi Itop D2 N) {n n' t t' : ℕ}
    (hn : (r ≤ n ∧ n < b0 * p + p ∧ (n - r) % 2 = 0) ∨ (N ≤ n ∧ n < b0 * p + p + D2 ∧ (n - r) % 2 = 1) ∨
      (b0 * p + p + D2 ≤ n ∧ n < N ∧ (n - r) % 2 = 0))
    (hn' : (r ≤ n' ∧ n' < b0 * p + p ∧ (n' - r) % 2 = 1) ∨ (N ≤ n' ∧ n' < b0 * p + p + D2 ∧ (n' - r) % 2 = 0) ∨
      (b0 * p + p + D2 ≤ n' ∧ n' < N ∧ (n' - r) % 2 = 1))
    (ht : t = shn (b0 * p + p + D2) D2 n) (ht' : t' = shn (b0 * p + p + D2) D2 n') :
    InIm r (b0 * p + p) Itop N (b0 * p + p + D2) t ∧
      InIm r (b0 * p + p) Itop N (b0 * p + p + D2) t' ∧ t % p = n % p ∧ t' % p = n' % p ∧
      (n / p = n' / p ↔ t / p = t' / p) ∧ t ≠ t' ∧
      (n / p = n' / p → ((n < b0 * p + p ∧ n' < b0 * p + p) ∨
        (N ≤ n ∧ n < b0 * p + p + D2 ∧ N ≤ n' ∧ n' < b0 * p + p + D2) ∨
        (b0 * p + p + D2 ≤ n ∧ b0 * p + p + D2 ≤ n'))) := by
  have hnr : r ≤ n := by have := G.hE; have := G.hN; have := G.hk; have := G.b0le; have := G.rlt; omega
  have hnr' : r ≤ n' := by have := G.hE; have := G.hN; have := G.hk; have := G.b0le; have := G.rlt; omega
  have hD2e : D2 % 2 = 0 := by rw [G.hD2, Nat.mul_assoc]; exact Nat.mul_mod_right 2 _
  have hD := shift_data G hnr
  have hD' := shift_data G hnr'
  obtain ⟨hp5, hodd, hb0, hrl, hs, hsp, hD2, hk, hE, hN⟩ := G
  by_cases h1 : b0 * p + p + D2 ≤ n
  · obtain ⟨a1, a2, a3⟩ := hD.1 h1
    have e1 : t = n - D2 := by rw [ht]; exact shn_of_le h1
    clear hD
    subst e1
    by_cases h2 : b0 * p + p + D2 ≤ n'
    · obtain ⟨c1, c2, c3⟩ := hD'.1 h2
      have e2 : t' = n' - D2 := by rw [ht']; exact shn_of_le h2
      clear hD'
      subst e2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try unfold InIm) <;> omega
    · obtain ⟨c1, c2⟩ := hD'.2 (by omega)
      have e2 : t' = n' := by rw [ht']; exact shn_of_lt (by omega)
      clear hD'
      subst e2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try unfold InIm) <;> omega
  · obtain ⟨a1, a2⟩ := hD.2 (by omega)
    have e1 : t = n := by rw [ht]; exact shn_of_lt (by omega)
    clear hD
    subst e1
    by_cases h2 : b0 * p + p + D2 ≤ n'
    · obtain ⟨c1, c2, c3⟩ := hD'.1 h2
      have e2 : t' = n' - D2 := by rw [ht']; exact shn_of_le h2
      clear hD'
      subst e2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try unfold InIm) <;> omega
    · obtain ⟨c1, c2⟩ := hD'.2 (by omega)
      have e2 : t' = n' := by rw [ht']; exact shn_of_lt (by omega)
      clear hD'
      subst e2
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try unfold InIm) <;> omega

/-- **The pair inequality of Theorem R★**: for a row-type label `n` and a column-type label `n'`
(`RowLab`, `ColLab`), `Wlab ≤ φ n + φ n'`. -/
theorem p1_pair [hp : Fact p.Prime] (G : Geo p r s e k' b0 lo hi Itop D2 N) {fl : Bool} {w : ℕ → ℕ}
    (hfl : fl = true ↔ (lo < b0 * p + p ∧ ∀ t, lo ≤ t → t < hi → b0 * p + p ≤ t → 1 ≤ w t))
    (hdual : ∀ t t', lo ≤ t → t < hi → lo ≤ t' → t' < hi → w3 (cell p t) (cell p t') ≤ w t + w t')
    {n n' : ℕ} {kR kC : Bool}
    (hn : (r ≤ n ∧ n < b0 * p + p ∧ (n - r) % 2 = 0) ∨ (N ≤ n ∧ n < b0 * p + p + D2 ∧ (n - r) % 2 = 1) ∨
      (b0 * p + p + D2 ≤ n ∧ n < N ∧ (n - r) % 2 = 0))
    (hn' : (r ≤ n' ∧ n' < b0 * p + p ∧ (n' - r) % 2 = 1) ∨ (N ≤ n' ∧ n' < b0 * p + p + D2 ∧ (n' - r) % 2 = 0) ∨
      (b0 * p + p + D2 ≤ n' ∧ n' < N ∧ (n' - r) % 2 = 1))
    (hkR : kR = true ↔ b0 * p + p + D2 ≤ n) (hkC : kC = true ↔ b0 * p + p + D2 ≤ n') :
    Wlab p kR kC (oc p (b0 + 1) ((r + 1) % 2) (n % p)) (oc p (b0 + 1) (1 - (r + 1) % 2) (n' % p)) n n' ≤
      phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w n +
        phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w n' := by
  have G' := G
  obtain ⟨hp5, hodd, hb0, hrl, hs, hsp, hD2, hk, hE, hN⟩ := G'
  have hnr : r ≤ n := by omega
  have hnr' : r ≤ n' := by omega
  have hphn : phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w n =
      psi p (b0 * p + p) lo hi fl w (shn (b0 * p + p + D2) D2 n) := by
    unfold phin; rw [if_neg (by omega)]
  have hphn' : phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w n' =
      psi p (b0 * p + p) lo hi fl w (shn (b0 * p + p + D2) D2 n') := by
    unfold phin; rw [if_neg (by omega)]
  rw [hphn, hphn']
  obtain ⟨t, ht⟩ : ∃ t, t = shn (b0 * p + p + D2) D2 n := ⟨_, rfl⟩
  obtain ⟨t', ht'⟩ : ∃ t', t' = shn (b0 * p + p + D2) D2 n' := ⟨_, rfl⟩
  rw [← ht, ← ht']
  have aux := p1_aux G hn hn' ht ht'
  obtain ⟨hIm, hIm', htm, htm', hper, hne, hsame⟩ := aux
  have hhalf : half p t = half p n := by unfold half; rw [htm]
  have hhalf' : half p t' = half p n' := by unfold half; rw [htm']
  by_cases hc : n % p = n' % p
  · -- congruent
    unfold Wlab
    rw [if_pos hc]
    have htc : t % p = t' % p := by rw [htm, htm', hc]
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · exact Q1 G fl w hIm hIm' hlt htc
    · have := Q1 G fl w hIm' hIm hlt htc.symm
      omega
  · -- non-congruent
    have hpat : n / p = n' / p → kR = kC ∧ oc p (b0 + 1) ((r + 1) % 2) (n % p) =
        oc p (b0 + 1) (1 - (r + 1) % 2) (n' % p) := by
      intro hpp
      have hs3 := hsame hpp
      refine ⟨?_, ?_⟩
      · have : (b0 * p + p + D2 ≤ n ↔ b0 * p + p + D2 ≤ n') := kind_eq hs3
        exact Bool.eq_iff_iff.2 ((hkR.trans this).trans hkC.symm)
      · exact class_eq hodd b0 r n n' hnr hnr' (by omega) hpp
    refine le_trans (Wlab_le_w3 kR kC _ _ n n' hc hpat) ?_
    rw [w3_congr (a' := t) (b' := t') hhalf.symm hhalf'.symm hper]
    exact Q2 G hfl hdual hIm hIm'

end P1Pair

section P1Sums

variable {p r s e k' b0 lo hi Itop D2 N : ℕ}

/-- Row-type indicator in image coordinates: X parity below `N`, Y parity from `N`. -/
def rt (r N u : ℕ) : ℕ :=
  if u < N then (if (u - r) % 2 = 0 then 1 else 0) else (if (u - r) % 2 = 1 then 1 else 0)

theorem Geo.AN (G : Geo p r s e k' b0 lo hi Itop D2 N) : b0 * p + p ≤ N := by
  have := G.hE; have := G.hN; have := G.hk; have := G.rlt; have := G.b0le; omega

/-- The four label sets as unions of parity classes of intervals. -/
theorem sets_eq (G : Geo p r s e k' b0 lo hi Itop D2 N) {m : ℕ} (hm : r + 2 * m = N) :
    TRs p (b0 + 1) k' r m =
      (Finset.Ico r (b0 * p + p)).filter (fun t => (t - r) % 2 = 0) ∪
        (Finset.Ico N (b0 * p + p + D2)).filter (fun t => ¬ (t - r) % 2 = 0) ∧
    TCs p (b0 + 1) k' r m =
      (Finset.Ico r (b0 * p + p)).filter (fun t => ¬ (t - r) % 2 = 0) ∪
        (Finset.Ico N (b0 * p + p + D2)).filter (fun t => (t - r) % 2 = 0) ∧
    ORs p (b0 + 1) k' r m = (Finset.Ico (b0 * p + p + D2) N).filter (fun t => (t - r) % 2 = 0) ∧
    OCs p (b0 + 1) k' r m = (Finset.Ico (b0 * p + p + D2) N).filter (fun t => ¬ (t - r) % 2 = 0) := by
  have hk1 : (b0 + 1) * p = b0 * p + p := by rw [Nat.add_mul, Nat.one_mul]
  have hk2 : (b0 + 1 + 2 * k') * p = b0 * p + p + D2 := by rw [G.hD2]; ring
  have h1 := G.rlt
  have h2 := G.hN
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext t <;>
    simp only [TRs, TCs, ORs, OCs, Tdel, Finset.mem_filter, Finset.mem_Ico, Finset.mem_union, hk1, hk2, hm] <;>
    omega

theorem ite_pair (I : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (F : ℕ → ℕ) :
    ∑ t ∈ I, (if P t then F t else 0) + ∑ t ∈ I, (if ¬ P t then F t else 0) = ∑ t ∈ I, F t := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun t _ => by split_ifs <;> simp)

theorem row_split (G : Geo p r s e k' b0 lo hi Itop D2 N) {m : ℕ} (hm : r + 2 * m = N) (F : ℕ → ℕ) :
    ∑ t ∈ TRs p (b0 + 1) k' r m, F t + ∑ t ∈ ORs p (b0 + 1) k' r m, F t =
      ∑ t ∈ Finset.Ico r (b0 * p + p), (if (t - r) % 2 = 0 then F t else 0) +
      ∑ t ∈ Finset.Ico N (b0 * p + p + D2), (if ¬ (t - r) % 2 = 0 then F t else 0) +
      ∑ t ∈ Finset.Ico (b0 * p + p + D2) N, (if (t - r) % 2 = 0 then F t else 0) := by
  obtain ⟨hTR, -, hOR, -⟩ := sets_eq G hm
  have hAN := G.AN
  have hd : Disjoint ((Finset.Ico r (b0 * p + p)).filter (fun t => (t - r) % 2 = 0))
      ((Finset.Ico N (b0 * p + p + D2)).filter (fun t => ¬ (t - r) % 2 = 0)) := by
    rw [Finset.disjoint_left]
    intro t h1 h2
    simp only [Finset.mem_filter, Finset.mem_Ico] at h1 h2
    omega
  rw [hTR, hOR, Finset.sum_union hd, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]

theorem col_split (G : Geo p r s e k' b0 lo hi Itop D2 N) {m : ℕ} (hm : r + 2 * m = N) (F : ℕ → ℕ) :
    ∑ t ∈ TCs p (b0 + 1) k' r m, F t + ∑ t ∈ OCs p (b0 + 1) k' r m, F t =
      ∑ t ∈ Finset.Ico r (b0 * p + p), (if ¬ (t - r) % 2 = 0 then F t else 0) +
      ∑ t ∈ Finset.Ico N (b0 * p + p + D2), (if (t - r) % 2 = 0 then F t else 0) +
      ∑ t ∈ Finset.Ico (b0 * p + p + D2) N, (if ¬ (t - r) % 2 = 0 then F t else 0) := by
  obtain ⟨-, hTC, -, hOC⟩ := sets_eq G hm
  have hAN := G.AN
  have hd : Disjoint ((Finset.Ico r (b0 * p + p)).filter (fun t => ¬ (t - r) % 2 = 0))
      ((Finset.Ico N (b0 * p + p + D2)).filter (fun t => (t - r) % 2 = 0)) := by
    rw [Finset.disjoint_left]
    intro t h1 h2
    simp only [Finset.mem_filter, Finset.mem_Ico] at h1 h2
    omega
  rw [hTC, hOC, Finset.sum_union hd, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]

theorem sum_total (G : Geo p r s e k' b0 lo hi Itop D2 N) {m : ℕ} (hm : r + 2 * m = N) (F : ℕ → ℕ) :
    ∑ t ∈ TRs p (b0 + 1) k' r m, F t + ∑ t ∈ ORs p (b0 + 1) k' r m, F t +
      ∑ t ∈ TCs p (b0 + 1) k' r m, F t + ∑ t ∈ OCs p (b0 + 1) k' r m, F t =
    ∑ t ∈ Finset.Ico r (b0 * p + p), F t + ∑ t ∈ Finset.Ico N (b0 * p + p + D2), F t +
      ∑ t ∈ Finset.Ico (b0 * p + p + D2) N, F t := by
  have h1 := row_split G hm F
  have h2 := col_split G hm F
  have e1 := ite_pair (Finset.Ico r (b0 * p + p)) (fun t => (t - r) % 2 = 0) F
  have e2 := ite_pair (Finset.Ico N (b0 * p + p + D2)) (fun t => (t - r) % 2 = 0) F
  have e3 := ite_pair (Finset.Ico (b0 * p + p + D2) N) (fun t => (t - r) % 2 = 0) F
  omega

theorem shiftW (G : Geo p r s e k' b0 lo hi Itop D2 N) (F : ℕ → ℕ) :
    ∑ t ∈ Finset.Ico (b0 * p + p + D2) N, F t = ∑ x ∈ Finset.Ico (b0 * p + p) (N - D2), F (x + D2) := by
  have := Finset.sum_Ico_add' F (b0 * p + p) (N - D2) D2
  have hN := G.hN
  rw [show N - D2 + D2 = N by omega] at this
  exact this.symm

/-- Potential sum in image coordinates. -/
theorem sum_phi (G : Geo p r s e k' b0 lo hi Itop D2 N) {m : ℕ} (hm : r + 2 * m = N) (fl : Bool)
    (w : ℕ → ℕ) :
    ∑ t ∈ TRs p (b0 + 1) k' r m, phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w t +
      ∑ t ∈ ORs p (b0 + 1) k' r m, phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w t +
      ∑ t ∈ TCs p (b0 + 1) k' r m, phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w t +
      ∑ t ∈ OCs p (b0 + 1) k' r m, phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w t =
    ∑ t ∈ Finset.Ico r (b0 * p + p), psi p (b0 * p + p) lo hi fl w t +
      ∑ t ∈ Finset.Ico N (b0 * p + p + D2), psi p (b0 * p + p) lo hi fl w t +
      ∑ t ∈ Finset.Ico (b0 * p + p) (N - D2), psi p (b0 * p + p) lo hi fl w t := by
  rw [sum_total G hm, shiftW G]
  have hAN := G.AN
  have hrl := G.rlt
  have hN := G.hN
  have c1 : ∑ t ∈ Finset.Ico r (b0 * p + p), phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w t =
      ∑ t ∈ Finset.Ico r (b0 * p + p), psi p (b0 * p + p) lo hi fl w t := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.mem_Ico] at ht
    unfold phin; rw [if_neg (by omega), shn_of_lt (by omega)]
  have c2 : ∑ t ∈ Finset.Ico N (b0 * p + p + D2), phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w t =
      ∑ t ∈ Finset.Ico N (b0 * p + p + D2), psi p (b0 * p + p) lo hi fl w t := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.mem_Ico] at ht
    unfold phin; rw [if_neg (by omega), shn_of_lt (by omega)]
  have c3 : ∑ x ∈ Finset.Ico (b0 * p + p) (N - D2), phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w (x + D2) =
      ∑ x ∈ Finset.Ico (b0 * p + p) (N - D2), psi p (b0 * p + p) lo hi fl w x := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.mem_Ico] at ht
    unfold phin; rw [if_neg (by omega), shn_of_le (by omega)]
    congr 1; omega
  rw [c1, c2, c3]

/-- Row-type count in image coordinates. -/
theorem card_rows (G : Geo p r s e k' b0 lo hi Itop D2 N) {m : ℕ} (hm : r + 2 * m = N) :
    (TRs p (b0 + 1) k' r m).card + (ORs p (b0 + 1) k' r m).card =
    ∑ t ∈ Finset.Ico r (b0 * p + p), rt r N t + ∑ t ∈ Finset.Ico N (b0 * p + p + D2), rt r N t +
      ∑ t ∈ Finset.Ico (b0 * p + p) (N - D2), rt r N t := by
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones, row_split G hm (fun _ => 1)]
  have hAN := G.AN
  have hrl := G.rlt
  have hN := G.hN
  have h3 := shiftW G (fun t => if (t - r) % 2 = 0 then 1 else 0)
  have c1 : ∑ t ∈ Finset.Ico r (b0 * p + p), (if (t - r) % 2 = 0 then 1 else 0) =
      ∑ t ∈ Finset.Ico r (b0 * p + p), rt r N t := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.mem_Ico] at ht
    have hlt : t < N := by omega
    unfold rt; rw [if_pos hlt]
  have c2 : ∑ t ∈ Finset.Ico N (b0 * p + p + D2), (if ¬ (t - r) % 2 = 0 then 1 else 0) =
      ∑ t ∈ Finset.Ico N (b0 * p + p + D2), rt r N t := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.mem_Ico] at ht
    have hlt : ¬ t < N := by omega
    unfold rt; rw [if_neg hlt]
    split_ifs <;> omega
  have c3 : ∑ x ∈ Finset.Ico (b0 * p + p) (N - D2), (if (x + D2 - r) % 2 = 0 then 1 else 0) =
      ∑ x ∈ Finset.Ico (b0 * p + p) (N - D2), rt r N x := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.mem_Ico] at ht
    have hlt : t < N := by omega
    unfold rt; rw [if_pos hlt]
    have hD2e : D2 % 2 = 0 := by rw [G.hD2, Nat.mul_assoc]; exact Nat.mul_mod_right 2 _
    split_ifs <;> omega
  omega

end P1Sums

section P1Regions

variable {p r s e k' b0 lo hi Itop D2 N : ℕ}

theorem psi_mem {p A lo hi : ℕ} {fl : Bool} {w : ℕ → ℕ} {u : ℕ} (h : lo ≤ u ∧ u < hi) :
    psi p A lo hi fl w u = w u := by unfold psi; rw [if_pos h]

/-- The pairing `a ↔ a + p` of the case `e = 1`: potentials add to `3`, exactly one is a row-type node. -/
theorem pair_odd (G : Geo p r s e k' b0 lo hi Itop D2 N) {fl : Bool} {w : ℕ → ℕ}
    (hfl : fl = true ↔ (lo < b0 * p + p ∧ ∀ t, lo ≤ t → t < hi → b0 * p + p ≤ t → 1 ≤ w t))
    (he : e = 1) {a : ℕ} (h1 : r ≤ a) (h2 : a < r + s) :
    psi p (b0 * p + p) lo hi fl w a + psi p (b0 * p + p) lo hi fl w (a + p) = 3 ∧
      rt r N a + rt r N (a + p) = 1 := by
  obtain ⟨hp5, hodd, hb0, hrl, hs, hsp, hD2, hk, hE, hN⟩ := G
  have hE' : lo = r + s ∧ hi = r + p ∧ Itop = r + p + s := by omega
  unfold rt
  cases fl
  · rw [psi_false, psi_false]
    refine ⟨?_, ?_⟩ <;> split_ifs <;> omega
  · rw [psi_true, psi_true]
    have hlo := (hfl.1 rfl).1
    refine ⟨?_, ?_⟩ <;> split_ifs <;> omega

/-- The pairing `a ↔ a + 2 k' p` of the case `e = 0`, `h* > N`. -/
theorem pair_even (G : Geo p r s e k' b0 lo hi Itop D2 N) {fl : Bool} {w : ℕ → ℕ}
    (hfl : fl = true ↔ (lo < b0 * p + p ∧ ∀ t, lo ≤ t → t < hi → b0 * p + p ≤ t → 1 ≤ w t))
    (he : e = 0) (hc : r + s < b0 * p + p) {a : ℕ} (h1 : r + s ≤ a) (h2 : a < b0 * p + p) :
    psi p (b0 * p + p) lo hi fl w a + psi p (b0 * p + p) lo hi fl w (a + D2) = 3 ∧
      rt r N a + rt r N (a + D2) = 1 := by
  have G' := G
  obtain ⟨hp5, hodd, hb0, hrl, hs, hsp, hD2, hk, hE, hN⟩ := G'
  have hD2e : D2 % 2 = 0 := by rw [hD2, Nat.mul_assoc]; exact Nat.mul_mod_right 2 _
  have hE' : lo = r ∧ hi = r + s ∧ Itop = r + s := by omega
  have hf : fl = true := hfl.2 ⟨by omega, fun t h1 h2 h3 => by omega⟩
  subst hf
  rw [psi_true, psi_true]
  unfold rt
  refine ⟨?_, ?_⟩ <;> split_ifs <;> omega

/-- The decomposition of the image intervals: `E` and the paired remainder. -/
theorem p1_regions (G : Geo p r s e k' b0 lo hi Itop D2 N) {fl : Bool} {w : ℕ → ℕ}
    (hfl : fl = true ↔ (lo < b0 * p + p ∧ ∀ t, lo ≤ t → t < hi → b0 * p + p ≤ t → 1 ≤ w t)) :
    ∃ a0 c d : ℕ, (∀ F : ℕ → ℕ,
      ∑ t ∈ Finset.Ico r (b0 * p + p), F t + ∑ t ∈ Finset.Ico N (b0 * p + p + D2), F t +
        ∑ t ∈ Finset.Ico (b0 * p + p) (N - D2), F t =
      ∑ t ∈ Finset.Ico lo hi, F t + ∑ a ∈ Finset.Ico a0 (a0 + c), (F a + F (a + d))) ∧
    (∀ a, a0 ≤ a → a < a0 + c →
      psi p (b0 * p + p) lo hi fl w a + psi p (b0 * p + p) lo hi fl w (a + d) = 3 ∧
        rt r N a + rt r N (a + d) = 1) := by
  have G' := G
  obtain ⟨hp5, hodd, hb0, hrl, hs, hsp, hD2, hk, hE, hN⟩ := G'
  rcases hE with ⟨he0, hlo, hhi, hIt⟩ | ⟨he1, hlo, hhi, hIt⟩
  · by_cases hcase : b0 * p + p ≤ r + s
    · refine ⟨0, 0, 0, fun F => ?_, fun a h1 h2 => by omega⟩
      have hV : Finset.Ico N (b0 * p + p + D2) = ∅ := Finset.Ico_eq_empty (by omega)
      rw [hV, Finset.sum_empty, Nat.add_zero, Finset.Ico_self, Finset.sum_empty, Nat.add_zero,
        show N - D2 = r + s by omega, hlo, hhi]
      rw [Finset.sum_Ico_consecutive F (by omega) hcase]
    · refine ⟨r + s, b0 * p + p - (r + s), D2, fun F => ?_, fun a h1 h2 => ?_⟩
      · have hW : Finset.Ico (b0 * p + p) (N - D2) = ∅ := Finset.Ico_eq_empty (by omega)
        rw [hW, Finset.sum_empty, Nat.add_zero, Finset.sum_add_distrib]
        have hsh := Finset.sum_Ico_add' F (r + s) (b0 * p + p) D2
        rw [show N = r + s + D2 by omega, ← hsh, hlo, hhi]
        have hsp2 := Finset.sum_Ico_consecutive F (m := r) (n := r + s) (k := b0 * p + p) (by omega) (by omega)
        rw [show r + s + (b0 * p + p - (r + s)) = b0 * p + p by omega]
        omega
      · exact pair_even G hfl he0 (by omega) h1 (by omega)
  · refine ⟨r, s, p, fun F => ?_, fun a h1 h2 => pair_odd G hfl he1 h1 (by omega)⟩
    have hV : Finset.Ico N (b0 * p + p + D2) = ∅ := Finset.Ico_eq_empty (by omega)
    rw [hV, Finset.sum_empty, Nat.add_zero, Finset.sum_add_distrib, hlo, hhi,
      show N - D2 = r + p + s by omega]
    have hsh := Finset.sum_Ico_add' F r (r + s) p
    have c1 := Finset.sum_Ico_consecutive F (m := r) (n := b0 * p + p) (k := r + p + s) (by omega) (by omega)
    have c2 := Finset.sum_Ico_consecutive F (m := r) (n := r + s) (k := r + p) (by omega) (by omega)
    have c3 := Finset.sum_Ico_consecutive F (m := r) (n := r + p) (k := r + p + s) (by omega) (by omega)
    rw [show r + s + p = r + p + s by omega] at hsh
    omega

end P1Regions

section P1Total

variable {p r s e k' b0 lo hi Itop D2 N : ℕ}

/-- **The sum condition of `RowNodes.member_gle_P`, as an equality.** -/
theorem p1_sum [hp : Fact p.Prime] (G : Geo p r s e k' b0 lo hi Itop D2 N) {m : ℕ} (hm : r + 2 * m = N)
    {fl : Bool} {w : ℕ → ℕ}
    (hfl : fl = true ↔ (lo < b0 * p + p ∧ ∀ t, lo ≤ t → t < hi → b0 * p + p ≤ t → 1 ≤ w t))
    {nm : ℕ} (hnm : (e = 0 ∧ nm = s / 2) ∨ (e = 1 ∧ nm = (p - s) / 2)) :
    (∑ t ∈ TRs p (b0 + 1) k' r m, phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w t +
      ∑ t ∈ ORs p (b0 + 1) k' r m, phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w t +
      ∑ t ∈ TCs p (b0 + 1) k' r m, phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w t +
      ∑ t ∈ OCs p (b0 + 1) k' r m, phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w t) +
      3 * nm ≤ ∑ t ∈ Finset.Ico lo hi, w t +
        3 * ((TRs p (b0 + 1) k' r m).card + (ORs p (b0 + 1) k' r m).card) := by
  have hS := sum_phi G hm fl w
  have hR := card_rows G hm
  obtain ⟨a0, c, d, hreg, hpair⟩ := p1_regions G hfl
  have hSψ := hreg (psi p (b0 * p + p) lo hi fl w)
  have hRrt := hreg (rt r N)
  have hEψ : ∑ t ∈ Finset.Ico lo hi, psi p (b0 * p + p) lo hi fl w t = ∑ t ∈ Finset.Ico lo hi, w t := by
    refine Finset.sum_congr rfl (fun t ht => ?_)
    rw [Finset.mem_Ico] at ht
    exact psi_mem ht
  have hG := G
  obtain ⟨hp5, hodd, hb0, hrl, hs, hsp, hD2, hk, hE, hN⟩ := hG
  have hErt : ∑ t ∈ Finset.Ico lo hi, rt r N t = nm := by
    have h1 : ∑ t ∈ Finset.Ico lo hi, rt r N t =
        ∑ t ∈ Finset.Ico lo (lo + (hi - lo)), (if (t - r) % 2 = 0 then 1 else 0) := by
      rw [show lo + (hi - lo) = hi by omega]
      refine Finset.sum_congr rfl (fun t ht => ?_)
      rw [Finset.mem_Ico] at ht
      have hlt : t < N := by omega
      unfold rt; rw [if_pos hlt]
    rw [h1, cnt_even r lo (hi - lo) (by omega)]
    split_ifs <;> omega
  have hps : ∑ a ∈ Finset.Ico a0 (a0 + c),
      (psi p (b0 * p + p) lo hi fl w a + psi p (b0 * p + p) lo hi fl w (a + d)) = 3 * c := by
    rw [Finset.sum_congr rfl (fun a ha => (hpair a (Finset.mem_Ico.1 ha).1 (Finset.mem_Ico.1 ha).2).1)]
    simp [Finset.sum_const, Nat.mul_comm]
  have hrs : ∑ a ∈ Finset.Ico a0 (a0 + c), (rt r N a + rt r N (a + d)) = c := by
    rw [Finset.sum_congr rfl (fun a ha => (hpair a (Finset.mem_Ico.1 ha).1 (Finset.mem_Ico.1 ha).2).2)]
    simp
  omega

end P1Total

section P1Thm

variable {p : ℕ} [hp : Fact p.Prime]

/-- The window `E` of the row: `[r, r + s)` for `k` even and `[r + s, r + p)` for `k` odd, where
`2 m = k p + s`, `0 ≤ s < p`; its length is `2 ‖m‖_p`. -/
def P1E (p r m : ℕ) : Finset ℕ :=
  Finset.Ico (if (2 * m / p) % 2 = 0 then r else r + 2 * m % p)
    (if (2 * m / p) % 2 = 0 then r + 2 * m % p else r + p)

set_option maxHeartbeats 4000000 in
/-- **Row `P₁`** (`PLANE2-ROW-SIMPLIFICATION` Theorem R★; ledger P213).  For `p ≤ 2 m`, `p ≥ 5`, `p ∤ v`,
`p² > 2 N + 2 p` (`N = r + 2 m`) and every symmetric dual `w` of the cell weight `W₃` on `E` (a function of
the node; in particular any function of the cell), every coefficient of the determinant of every member of
the family (window rows `r + 2 i`, columns `r + 2 i + 1`, retained common nodes `c` below `r`) has
`p`-adic denominator at most `3 (r + m) − 3 ‖m‖_p + ∑_{t ∈ E} w t`, where `‖m‖_p = min (m mod p) (p − m mod p)`.
No (ND) hypothesis and no table. -/
theorem row_P1 (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1)
    (hp5 : 5 ≤ p) {r m : ℕ} (hm : p ≤ 2 * m) (hN : 2 * (r + 2 * m) + 2 * p < p * p)
    {ι : Type} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) (hcinj : Function.Injective c)
    (hcr : ∀ i, c i < r) (w : ℕ → ℕ)
    (hdual : ∀ t ∈ P1E p r m, ∀ t' ∈ P1E p r m, w3 (cell p t) (cell p t') ≤ w t + w t') :
    GLE p (3 * (r + m) - 3 * min (m % p) (p - m % p) + ∑ t ∈ P1E p r m, w t)
      (seqFullN (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e c
        (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1) (X : ℚ[X])).det := by
  classical
  have hp0 : 0 < p := hp.out.pos
  obtain ⟨b0, hb0def⟩ : ∃ b0, b0 = r / p := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k, k = 2 * m / p := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s, s = 2 * m % p := ⟨_, rfl⟩
  have h2m : k * p + s = 2 * m := by
    rw [hkdef, hsdef, Nat.mul_comm]; exact Nat.div_add_mod (2 * m) p
  have hslt : s < p := by rw [hsdef]; exact Nat.mod_lt _ hp0
  have hk1 : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst this
    omega
  obtain ⟨k', e, hke, he⟩ : ∃ k' e, k = 2 * k' + e ∧ e ≤ 1 := ⟨k / 2, k % 2, by omega, by omega⟩
  obtain ⟨D2, hD2⟩ : ∃ D2, D2 = (2 * k') * p := ⟨_, rfl⟩
  have hkp : k * p = D2 + e * p := by rw [hke, Nat.add_mul, hD2]
  have hD2' : D2 = 2 * (k' * p) := by rw [hD2, Nat.mul_assoc]
  have hkpar : (k * p) % 2 = k % 2 := by
    rw [Nat.mul_mod, hodd]; simp
  have hspar : s % 2 = e := by omega
  have hb0le : b0 * p ≤ r := by rw [hb0def]; exact Nat.div_mul_le_self r p
  have hrlt : r < b0 * p + p := by
    rw [hb0def]
    have := Nat.lt_mul_div_succ r hp0
    rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm] at this
    exact this
  obtain ⟨N, hNdef⟩ : ∃ N, N = r + 2 * m := ⟨_, rfl⟩
  obtain ⟨lo, hlo⟩ : ∃ lo, lo = (if e = 0 then r else r + s) := ⟨_, rfl⟩
  obtain ⟨hi, hhi⟩ : ∃ hi, hi = (if e = 0 then r + s else r + p) := ⟨_, rfl⟩
  obtain ⟨Itop, hItop⟩ : ∃ Itop, Itop = r + s + e * p := ⟨_, rfl⟩
  have hP1E : P1E p r m = Finset.Ico lo hi := by
    unfold P1E
    rw [← hkdef, ← hsdef, hlo, hhi]
    have : k % 2 = e := by omega
    rw [this]
  have hGeo : Geo p r s e k' b0 lo hi Itop D2 N := by
    refine ⟨hp5, hodd, hb0le, hrlt, hslt, hspar, hD2, ?_, ?_, ?_⟩
    · rcases (by omega : e = 0 ∨ e = 1) with h | h
      · right
        have h1 : 2 ≤ 2 * k' := by omega
        have := Nat.mul_le_mul_right p h1
        omega
      · left; exact h
    · rcases (by omega : e = 0 ∨ e = 1) with h | h
      · left
        subst h
        simp at hlo hhi hItop
        exact ⟨rfl, hlo, hhi, hItop⟩
      · right
        subst h
        simp at hlo hhi hItop
        exact ⟨rfl, hlo, hhi, by omega⟩
    · rw [hNdef, hItop]; omega
  have hm' : r + 2 * m = N := hNdef.symm
  -- the flag and the dual in image coordinates
  obtain ⟨fl, hfl⟩ : ∃ fl : Bool, (fl = true ↔ (lo < b0 * p + p ∧
      ∀ t, lo ≤ t → t < hi → b0 * p + p ≤ t → 1 ≤ w t)) :=
    ⟨decide (lo < b0 * p + p ∧ ∀ t, lo ≤ t → t < hi → b0 * p + p ≤ t → 1 ≤ w t), by simp⟩
  have hdual' : ∀ t t', lo ≤ t → t < hi → lo ≤ t' → t' < hi →
      w3 (cell p t) (cell p t') ≤ w t + w t' := by
    intro t t' h1 h2 h3 h4
    refine hdual t ?_ t' ?_
    · rw [hP1E]; exact Finset.mem_Ico.2 ⟨h1, h2⟩
    · rw [hP1E]; exact Finset.mem_Ico.2 ⟨h3, h4⟩
  -- the norm
  obtain ⟨nm, hnmdef⟩ : ∃ nm, nm = min (m % p) (p - m % p) := ⟨_, rfl⟩
  have hnm : (e = 0 ∧ nm = s / 2) ∨ (e = 1 ∧ nm = (p - s) / 2) := by
    rcases (by omega : e = 0 ∨ e = 1) with h | h
    · left
      refine ⟨h, ?_⟩
      have hmm : m = s / 2 + k' * p := by
        have : 2 * m = 2 * (k' * p) + s := by
          subst h; omega
        omega
      have : m % p = s / 2 := by
        rw [hmm, Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hnmdef, this]
      omega
    · right
      refine ⟨h, ?_⟩
      have hmm : m = (p + s) / 2 + k' * p := by
        have : 2 * m = 2 * (k' * p) + p + s := by
          subst h; omega
        omega
      have : m % p = (p + s) / 2 := by
        rw [hmm, Nat.add_mul_mod_self_right]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hnmdef, this]
      omega
  have key := p1_sum (p := p) hGeo hm' hfl hnm
  -- the shifted bound `N'`
  obtain ⟨N', hN'⟩ : ∃ N', N' = max ((N / p + 1) * p) (b0 * p + p + D2) := ⟨_, rfl⟩
  have hN'le : N' ≤ N + p := by
    have h1 := Nat.div_mul_le_self N p
    have h2 := hGeo.hN
    have h3 := hGeo.hE
    rw [hN']
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hN2 : 2 * N' < p * p := by omega
  have hk1' : (b0 + 1) * p = b0 * p + p := by rw [Nat.add_mul, Nat.one_mul]
  have hk2' : (b0 + 1 + 2 * k') * p = b0 * p + p + D2 := by rw [hD2]; ring
  have hκr : r < (b0 + 1) * p := by rw [hk1']; exact hrlt
  have hH : (b0 + 1 + 2 * k') * p ≤ N' := by rw [hk2', hN']; exact le_max_right _ _
  have hcompl : ∀ n, n < r + 2 * m → (n / p + 1) * p ≤ N' := by
    intro n hn
    rw [hN']
    refine le_trans ?_ (le_max_left _ _)
    exact Nat.mul_le_mul_right p (Nat.add_le_add_right (Nat.div_le_div_right (by omega)) 1)
  have hφ : ∀ t, t < r → phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w t = 3 ∧
      phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w t = 3 := by
    intro t ht
    unfold phin; rw [if_pos ht]; exact ⟨rfl, rfl⟩
  obtain ⟨hTR, hTC, hOR, hOC⟩ := sets_eq hGeo hm'
  refine member_gle_P (p := p) (k' := k') (κ := b0 + 1) v u hv hu hpv hodd hp5 hN2 hκr hH hcompl c hcinj hcr
    (phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w)
    (phin p (b0 * p + p) lo hi (b0 * p + p + D2) D2 r fl w) hφ ?_ ?_ ?_ ?_
    (3 * (r + m) - 3 * min (m % p) (p - m % p) + ∑ t ∈ P1E p r m, w t) ?_
  · intro n hn n' hn'
    rw [hTR] at hn
    rw [hTC] at hn'
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico] at hn hn'
    exact p1_pair hGeo hfl hdual' (n := n) (n' := n') (kR := false) (kC := false) (by omega) (by omega)
      ⟨fun h => absurd h (by simp), fun h => by omega⟩ ⟨fun h => absurd h (by simp), fun h => by omega⟩
  · intro n hn n' hn'
    rw [hTR] at hn
    rw [hOC] at hn'
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico] at hn hn'
    exact p1_pair hGeo hfl hdual' (n := n) (n' := n') (kR := false) (kC := true) (by omega) (by omega)
      ⟨fun h => absurd h (by simp), fun h => by omega⟩ ⟨fun _ => by omega, fun _ => rfl⟩
  · intro n hn n' hn'
    rw [hOR] at hn
    rw [hTC] at hn'
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico] at hn hn'
    exact p1_pair hGeo hfl hdual' (n := n) (n' := n') (kR := true) (kC := false) (by omega) (by omega)
      ⟨fun _ => by omega, fun _ => rfl⟩ ⟨fun h => absurd h (by simp), fun h => by omega⟩
  · intro n hn n' hn'
    rw [hOR] at hn
    rw [hOC] at hn'
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico] at hn hn'
    exact p1_pair hGeo hfl hdual' (n := n) (n' := n') (kR := true) (kC := true) (by omega) (by omega)
      ⟨fun _ => by omega, fun _ => rfl⟩ ⟨fun _ => by omega, fun _ => rfl⟩
  · rw [hP1E]
    have hmm : min (m % p) (p - m % p) ≤ m := le_trans (min_le_left _ _) (Nat.mod_le m p)
    omega

end P1Thm

#print axioms row_P1
end CatalanCore.Uniform.Content.Sweep
