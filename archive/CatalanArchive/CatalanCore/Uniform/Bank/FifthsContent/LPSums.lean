import CatalanCore.Uniform.Content.Wire.LP
import CatalanCore.Arith.Hybrid.DefC5Entries
import CatalanCore.Arith.Hybrid.LamEntries
set_option Elab.async false

/-! # Closed forms of the LP1 / LP2 full-member prices (lane B, B5c)

For the hybrid labels (rows `i`, `r + 2 i`, columns `i`, `r + 2 i + 1`) the D2 potentials `wC` and
the D4 potentials `uPot` sum to

* `wC`:  `Σ rows + Σ cols = 2 (r - (k - (r - p))) + 2 m + min m ((p+k-r+1)/2) + min m ((p+k-r)/2)`  (`k ≤ r`);
* `uPot`: `Σ rows + Σ cols = 2 (r - k) + 2 m + (m - min m ((p-r+1)/2)) + (m - min m ((p-r)/2))`  (`k ≤ r`).

Hence `lp1Base = 4 r - 2 p - 2 k + 3 m` and `lp2Base = 2 r - 2 k + 3 m` in the LP windows. -/

namespace CatalanCore.Uniform.Bank.FifthsContent
open Finset CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Wire

theorem sum_ite_zero_one (s : Finset ℕ) (c : ℕ → Prop) [DecidablePred c] :
    ∑ i ∈ s, (if c i then 0 else 1) = s.card - (s.filter c).card := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := s) c
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one]
  omega

theorem sum_ite_two_one (s : Finset ℕ) (c : ℕ → Prop) [DecidablePred c] :
    ∑ i ∈ s, (if c i then 2 else 1) = s.card + (s.filter c).card := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card (s := s) c
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, smul_eq_mul, mul_one]
  omega

theorem sum_ite_one_two (s : Finset ℕ) (c : ℕ → Prop) [DecidablePred c] :
    ∑ i ∈ s, (1 + if c i then 1 else 0) = s.card + (s.filter c).card := by
  rw [Finset.sum_add_distrib]
  simp [Finset.card_filter]

theorem card_range_ico (r a b : ℕ) (hb : b ≤ r) :
    ((Finset.range r).filter (fun i => a ≤ i ∧ i < b)).card = b - a := by
  have : (Finset.range r).filter (fun i => a ≤ i ∧ i < b) = Finset.Ico a b := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this]; simp

theorem card_range_lt (m c : ℕ) :
    ((Finset.range m).filter (fun i => i < c)).card = min m c := by
  have : (Finset.range m).filter (fun i => i < c) = Finset.range (min m c) := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [this]; simp

theorem card_range_ge (m c : ℕ) :
    ((Finset.range m).filter (fun i => c ≤ i)).card = m - c := by
  have : (Finset.range m).filter (fun i => c ≤ i) = Finset.Ico c m := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this]; simp

/-- `wC` core sum. -/
theorem wC_core (p r k : ℕ) (hk : k ≤ r) :
    ∑ i : Fin r, wC p r k (i : ℕ) = r - (k - (r - p)) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => wC p r k i) r]
  have : ∀ i ∈ Finset.range r, wC p r k i = if (r - p ≤ i ∧ i < k) then 0 else 1 := by
    intro i hi
    have := Finset.mem_range.1 hi
    simp [wC, this]
  rw [Finset.sum_congr rfl this, sum_ite_zero_one, card_range_ico r _ _ hk]
  simp

theorem wC_row (p r k m : ℕ) (hk : k ≤ r) :
    ∑ a : Fin r ⊕ Fin m, wC p r k (Frame.hybRow r m a) =
      (r - (k - (r - p))) + (m + min m ((p + k - r + 1) / 2)) := by
  rw [Fintype.sum_sum_type]
  have h1 : ∑ i : Fin r, wC p r k (Frame.hybRow r m (Sum.inl i)) = r - (k - (r - p)) :=
    wC_core p r k hk
  have h2 : ∑ i : Fin m, wC p r k (Frame.hybRow r m (Sum.inr i)) =
      m + min m ((p + k - r + 1) / 2) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => wC p r k (r + 2 * i)) m]
    have : ∀ i ∈ Finset.range m, wC p r k (r + 2 * i) = if (i < (p + k - r + 1) / 2) then 2 else 1 := by
      intro i _
      unfold wC
      by_cases h : r + 2 * i < p + k
      · rw [if_neg (by omega), if_pos h, if_pos (by omega)]
      · rw [if_neg (by omega), if_neg h, if_neg (by omega)]
    rw [Finset.sum_congr rfl this, sum_ite_two_one, card_range_lt]
    simp
  rw [h1, h2]

theorem wC_col (p r k m : ℕ) (hk : k ≤ r) :
    ∑ a : Fin r ⊕ Fin m, wC p r k (Frame.hybCol r m a) =
      (r - (k - (r - p))) + (m + min m ((p + k - r) / 2)) := by
  rw [Fintype.sum_sum_type]
  have h1 : ∑ i : Fin r, wC p r k (Frame.hybCol r m (Sum.inl i)) = r - (k - (r - p)) :=
    wC_core p r k hk
  have h2 : ∑ i : Fin m, wC p r k (Frame.hybCol r m (Sum.inr i)) =
      m + min m ((p + k - r) / 2) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => wC p r k (r + 2 * i + 1)) m]
    have : ∀ i ∈ Finset.range m, wC p r k (r + 2 * i + 1) = if (i < (p + k - r) / 2) then 2 else 1 := by
      intro i _
      unfold wC
      by_cases h : r + 2 * i + 1 < p + k
      · rw [if_neg (by omega), if_pos h, if_pos (by omega)]
      · rw [if_neg (by omega), if_neg h, if_neg (by omega)]
    rw [Finset.sum_congr rfl this, sum_ite_two_one, card_range_lt]
    simp
  rw [h1, h2]

/-- The full-member LP1 price in the LP1 window. -/
theorem lp1Base_closed (G : BlockGeom) (kf : ℕ → ℕ → ℕ) (r p : ℕ) (hk : kf r p ≤ r) :
    lp1Base G kf r p =
      2 * (r - (kf r p - (r - p))) + 2 * (G.geometry r).k +
        min (G.geometry r).k ((p + kf r p - r + 1) / 2) +
        min (G.geometry r).k ((p + kf r p - r) / 2) -
        (min (p + kf r p - r) (2 * (G.geometry r).k) - (G.geometry r).k) := by
  unfold lp1Base
  rw [wC_row p r (kf r p) _ hk, wC_col p r (kf r p) _ hk]
  omega

/-- `uPot` core sums. -/
theorem uPot_core (p r k : ℕ) (hk : k ≤ r) :
    ∑ i : Fin r, uPot p r k (i : ℕ) = r - k := by
  rw [Fin.sum_univ_eq_sum_range (fun i => uPot p r k i) r]
  have : ∀ i ∈ Finset.range r, uPot p r k i = if k ≤ i then 1 else 0 := by
    intro i hi
    have := Finset.mem_range.1 hi
    simp [uPot, this]
  rw [Finset.sum_congr rfl this]
  rw [← Finset.card_filter, card_range_ge]

theorem uPot_row (p r k m : ℕ) (hk : k ≤ r) :
    ∑ a : Fin r ⊕ Fin m, uPot p r k (Frame.hybRow r m a) =
      (r - k) + (m + (m - min m ((p - r + 1) / 2))) := by
  rw [Fintype.sum_sum_type]
  have h1 : ∑ i : Fin r, uPot p r k (Frame.hybRow r m (Sum.inl i)) = r - k := uPot_core p r k hk
  have h2 : ∑ i : Fin m, uPot p r k (Frame.hybRow r m (Sum.inr i)) =
      m + (m - min m ((p - r + 1) / 2)) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => uPot p r k (r + 2 * i)) m]
    have : ∀ i ∈ Finset.range m, uPot p r k (r + 2 * i) =
        1 + if ((p - r + 1) / 2 ≤ i) then 1 else 0 := by
      intro i _
      unfold uPot
      rw [if_neg (by omega)]
      by_cases h : p ≤ r + 2 * i
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    rw [Finset.sum_congr rfl this, sum_ite_one_two, card_range_ge]
    simp only [Finset.card_range]
    omega
  rw [h1, h2]

theorem uPot_col (p r k m : ℕ) (hk : k ≤ r) :
    ∑ a : Fin r ⊕ Fin m, uPot p r k (Frame.hybCol r m a) =
      (r - k) + (m + (m - min m ((p - r) / 2))) := by
  rw [Fintype.sum_sum_type]
  have h1 : ∑ i : Fin r, uPot p r k (Frame.hybCol r m (Sum.inl i)) = r - k := uPot_core p r k hk
  have h2 : ∑ i : Fin m, uPot p r k (Frame.hybCol r m (Sum.inr i)) =
      m + (m - min m ((p - r) / 2)) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => uPot p r k (r + 2 * i + 1)) m]
    have : ∀ i ∈ Finset.range m, uPot p r k (r + 2 * i + 1) =
        1 + if ((p - r) / 2 ≤ i) then 1 else 0 := by
      intro i _
      unfold uPot
      rw [if_neg (by omega)]
      by_cases h : p ≤ r + 2 * i + 1
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    rw [Finset.sum_congr rfl this, sum_ite_one_two, card_range_ge]
    simp only [Finset.card_range]
    omega
  rw [h1, h2]

/-- The full-member LP2 price in the LP2 window. -/
theorem lp2Base_closed (G : BlockGeom) (kf : ℕ → ℕ → ℕ) (r p : ℕ) (hk : kf r p ≤ r) :
    lp2Base G kf r p =
      2 * (r - kf r p) + 2 * (G.geometry r).k +
        ((G.geometry r).k - min (G.geometry r).k ((p - r + 1) / 2)) +
        ((G.geometry r).k - min (G.geometry r).k ((p - r) / 2)) -
        ((G.geometry r).k - (p - r)) := by
  unfold lp2Base
  rw [uPot_row p r (kf r p) _ hk, uPot_col p r (kf r p) _ hk]
  omega

#print axioms lp1Base_closed
#print axioms lp2Base_closed
end CatalanCore.Uniform.Bank.FifthsContent
