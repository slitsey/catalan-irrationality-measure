import CatalanCore.Uniform.Content.Wire.LP
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace CatalanCore.Uniform.Content.BankShared
open Finset CatalanCore CatalanCore.Arith.Hybrid

lemma zone_sum_nat (f : ℕ → ℕ) (r m : ℕ) :
    ∑ i ∈ range m, (f (r + 2 * i) + f (r + 2 * i + 1)) = ∑ j ∈ range (2 * m), f (r + j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      Finset.sum_range_succ, Finset.sum_range_succ]
    simp only [add_assoc]

lemma slot_sum_nat (f : ℕ → ℕ) (r m : ℕ) :
    (∑ a : Fin r ⊕ Fin m, f (Frame.hybRow r m a)) +
      (∑ b : Fin r ⊕ Fin m, f (Frame.hybCol r m b)) =
      2 * ∑ c ∈ range r, f c + ∑ j ∈ range (2 * m), f (r + j) := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Frame.hybRow, Frame.hybCol, Sum.elim_inl, Sum.elim_inr]
  simp only [Fin.sum_univ_eq_sum_range]
  have hz := zone_sum_nat f r m
  rw [Finset.sum_add_distrib] at hz
  omega

lemma wC_common_sum (p r k : ℕ) (hkp : k ≤ r) (hlo : r - p ≤ k) :
    ∑ c ∈ range r, wC p r k c = r - (k - (r - p)) := by
  let P : ℕ → Prop := fun c => r - p ≤ c ∧ c < k
  have hfilter : (range r).filter P = Ico (r - p) k := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, P]
    omega
  have hs : (∑ c ∈ range r, wC p r k c) = ((range r).filter (fun c => ¬ P c)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro c hc
    rw [wC, if_pos (Finset.mem_range.1 hc)]
    dsimp only [P]
    split_ifs <;> omega
  rw [hs]
  have hc := Finset.card_filter_add_card_filter_not (s := range r) P
  rw [hfilter, Finset.card_Ico, Finset.card_range] at hc
  omega

lemma wC_zone_sum (p r m k : ℕ) (hr : r ≤ p + k) :
    ∑ j ∈ range (2 * m), wC p r k (r + j) = 2 * m + min (2 * m) (p + k - r) := by
  have hf : (range (2 * m)).filter (fun j => j < p + k - r) = range (min (2 * m) (p + k - r)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  have he : ∀ j ∈ range (2 * m), wC p r k (r + j) = 1 + if j < p + k - r then 1 else 0 := by
    intro j _
    rw [wC, if_neg (by omega)]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, Finset.sum_boole]
  rw [hf, Finset.card_range]

lemma uPot_common_sum (p r k : ℕ) :
    ∑ c ∈ range r, uPot p r k c = r - k := by
  have hf : (range r).filter (fun c => k ≤ c) = Ico k r := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have he : ∀ c ∈ range r, uPot p r k c = if k ≤ c then 1 else 0 := by
    intro c hc
    rw [uPot, if_pos (Finset.mem_range.1 hc)]
  rw [Finset.sum_congr rfl he, Finset.sum_boole, hf, Finset.card_Ico]

lemma uPot_zone_sum (p r m k : ℕ) (hrp : r ≤ p) :
    ∑ j ∈ range (2 * m), uPot p r k (r + j) = 2 * m + (2 * m - (p - r)) := by
  have hf : (range (2 * m)).filter (fun j => p - r ≤ j) = Ico (p - r) (2 * m) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have he : ∀ j ∈ range (2 * m), uPot p r k (r + j) = 1 + if p - r ≤ j then 1 else 0 := by
    intro j _
    rw [uPot, if_neg (by omega)]
    split_ifs <;> omega
  rw [Finset.sum_congr rfl he, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one, Finset.sum_boole]
  rw [hf, Finset.card_Ico]

theorem lp1_slot_bound (p r m k : ℕ) (hkp : k ≤ r) (hlo : r - p ≤ k) (hrk : r ≤ p + k) :
    (∑ a : Fin r ⊕ Fin m, wC p r k (Frame.hybRow r m a)) +
      (∑ b : Fin r ⊕ Fin m, wC p r k (Frame.hybCol r m b)) -
      (min (p + k - r) (2 * m) - m) ≤ 2 * (r - (k - (r - p))) + 3 * m := by
  rw [slot_sum_nat, wC_common_sum p r k hkp hlo, wC_zone_sum p r m k hrk]
  omega

theorem lp2_slot_bound (p r m k : ℕ) (hrp : r ≤ p) :
    (∑ a : Fin r ⊕ Fin m, uPot p r k (Frame.hybRow r m a)) +
      (∑ b : Fin r ⊕ Fin m, uPot p r k (Frame.hybCol r m b)) -
      (m - (p - r)) ≤ 2 * (r - k) + 3 * m := by
  rw [slot_sum_nat, uPot_common_sum, uPot_zone_sum p r m k hrp]
  omega

#print axioms lp1_slot_bound
#print axioms lp2_slot_bound
end CatalanCore.Uniform.Content.BankShared
