module

public import CatalanCore.Uniform.Content.BankShared.TwoTerm.Class
public import CatalanCore.Uniform.Content.BankShared.Reindex
public import CatalanCore.Uniform.Content.Wire.LP
public import CatalanCore.Arith.Hybrid.DefC5Entries
public import CatalanCore.Arith.Hybrid.LamEntries

@[expose] public section
set_option Elab.async false

/-! # LP1 / LP2 for every two-term bank (lane C4, gap C4)

For `TwoTermData Fr q o`, a natural norm `nm` (`Fr.norm = nm`, `p ∤ nm`) and the pole data
`q k = j p + o` of the root class `j`:

* `lp1Hyp_tt`, `lp2Hyp_tt`: the hypotheses `LP1Hyp`, `LP2Hyp` of `Wire/LP.lean` (`5 ≤ p`, `2 q ≤ p`);
* `lp1Valid_tt`, `lp2Valid_tt`: the windows `lp1Valid`, `lp2Valid` on `altGeom c` at even `r`;
* `lp1Base_closed`, `lp2Base_closed`: the full-member prices in closed form (generic in the
  geometry; moved here from the fifths bank);
* `lp1_gle_tt`, `lp2_gle_tt`: the branch statements, a member is cleared by
  `2(r - (k - (r - p))) + 2m + min(2m, p+k-r) - (min(p+k-r, 2m) - m)` (LP1) and
  `2(r - k) + 2m + (2m - (p-r)) - (m - (p-r))` (LP2), plus its deletion count (debit 1). -/

namespace CatalanCore.Uniform.Content.BankShared.TwoTerm
open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Uniform
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared

variable {Fr : Frame} {q o : ℕ}

theorem qN_le_of_two {q p N : ℕ} (hN : N ≤ 2 * p) (hpq : 2 * q ≤ p) : q * N ≤ p * p :=
  calc q * N ≤ q * (2 * p) := Nat.mul_le_mul_left q hN
    _ = (2 * q) * p := by ring
    _ ≤ p * p := Nat.mul_le_mul_right p hpq

/-! ### The hypotheses `LP1Hyp`, `LP2Hyp` -/

theorem lp1Hyp_tt (T : TwoTermData Fr q o) {nm : ℕ} (hnorm : Fr.norm = (nm : ℚ))
    {p r m k j : ℕ} [Fact p.Prime] (hpn : ¬ p ∣ nm) (hp5 : 5 ≤ p) (hpq : 2 * q ≤ p)
    (hk : q * k = j * p + o) (hk0 : 0 < k) (hkp : k < p) (hj0 : 0 < j)
    (hN2 : r + 2 * m ≤ 2 * p) (hrp : p ≤ r) (hUk : r < p + k) : LP1Hyp Fr p q o r m k j := by
  have hn := norm_good hnorm hpn
  have ho := T.o_pos
  have hoq := T.o_lt
  exact ⟨⟨T, ⟨by omega, hk, hk0, hkp, hj0, hN2⟩, not_sq_dvd_of_qN T (qN_le_of_two hN2 hpq),
    hn.1, hn.2⟩, hrp, hUk, hp5⟩

theorem lp2Hyp_tt (T : TwoTermData Fr q o) {nm : ℕ} (hnorm : Fr.norm = (nm : ℚ))
    {p r m k j : ℕ} [Fact p.Prime] (hpn : ¬ p ∣ nm) (hp5 : 5 ≤ p) (hpq : 2 * q ≤ p)
    (hk : q * k = j * p + o) (hk0 : 0 < k) (hkp : k < p) (hj0 : 0 < j)
    (hNk : r + 2 * m ≤ p + k) (hrp : r < p) (hkr : k ≤ r) : LP2Hyp Fr p q o r m k j := by
  have hn := norm_good hnorm hpn
  have ho := T.o_pos
  have hoq := T.o_lt
  exact ⟨⟨T, ⟨by omega, hk, hk0, hkp, hj0, hNk⟩,
    not_sq_dvd_of_qN T (qN_le_of_two (by omega) hpq), hn.1, hn.2⟩, hrp, hkr, hp5⟩

/-! ### The windows on the alternating geometry -/

theorem lp1Valid_tt (c : ℚ) (hc : 0 < c) (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (r p k j : ℕ) (hr : r % 2 = 0) [Fact p.Prime] (hpn : ¬ p ∣ nm)
    (hp5 : 5 ≤ p) (hpq : 2 * q ≤ p)
    (hk : q * k = j * p + o) (hk0 : 0 < k) (hkp : k < p) (hj0 : 0 < j)
    (hN2 : r + 2 * (altGeom c hc).borderSize r ≤ 2 * p) (hrp : p ≤ r) (hUk : r < p + k) :
    lp1Valid (altGeom c hc) Fr q o (fun _ _ => k) (fun _ _ => j) r p := by
  have hgk : ((altGeom c hc).geometry r).k = (altGeom c hc).borderSize r :=
    geometry_k_eq_borderSize _ r
  refine ⟨altGeom_hybShape c hc hr, fun [Fact p.Prime] => ?_⟩
  rw [hgk]
  exact lp1Hyp_tt T hnorm hpn hp5 hpq hk hk0 hkp hj0 hN2 hrp hUk

theorem lp2Valid_tt (c : ℚ) (hc : 0 < c) (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (r p k j : ℕ) (hr : r % 2 = 0) [Fact p.Prime] (hpn : ¬ p ∣ nm)
    (hp5 : 5 ≤ p) (hpq : 2 * q ≤ p)
    (hk : q * k = j * p + o) (hk0 : 0 < k) (hkp : k < p) (hj0 : 0 < j)
    (hNk : r + 2 * (altGeom c hc).borderSize r ≤ p + k) (hrp : r < p) (hkr : k ≤ r)
    (hpm : p < r + (altGeom c hc).borderSize r) :
    lp2Valid (altGeom c hc) Fr q o (fun _ _ => k) (fun _ _ => j) r p := by
  have hgk : ((altGeom c hc).geometry r).k = (altGeom c hc).borderSize r :=
    geometry_k_eq_borderSize _ r
  refine ⟨altGeom_hybShape c hc hr, fun [Fact p.Prime] => ?_⟩
  rw [hgk]
  exact ⟨lp2Hyp_tt T hnorm hpn hp5 hpq hk hk0 hkp hj0 hNk hrp hkr, hpm⟩

/-! ### Closed forms of the full-member prices (generic in the geometry) -/

theorem sum_ite_zero_one (s : Finset ℕ) (c : ℕ → Prop) [DecidablePred c] :
    ∑ i ∈ s, (if c i then 0 else 1) = s.card - (s.filter c).card := by
  have h := Finset.card_filter_add_card_filter_not (s := s) c
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one]
  omega

theorem sum_ite_one_two (s : Finset ℕ) (c : ℕ → Prop) [DecidablePred c] :
    ∑ i ∈ s, (1 + if c i then 1 else 0) = s.card + (s.filter c).card := by
  rw [Finset.sum_add_distrib, Finset.sum_boole]
  simp only [Finset.sum_const, smul_eq_mul, mul_one, Nat.cast_id]

theorem sum_ite_two_one (s : Finset ℕ) (c : ℕ → Prop) [DecidablePred c] :
    ∑ i ∈ s, (if c i then 2 else 1) = s.card + (s.filter c).card := by
  rw [← sum_ite_one_two s c]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

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
    show ∑ i : Fin m, wC p r k (r + 2 * (i : ℕ)) = _
    rw [Fin.sum_univ_eq_sum_range (fun i => wC p r k (r + 2 * i)) m]
    have : ∀ i ∈ Finset.range m, wC p r k (r + 2 * i) =
        if (i < (p + k - r + 1) / 2) then 2 else 1 := by
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
    show ∑ i : Fin m, wC p r k (r + 2 * (i : ℕ) + 1) = _
    rw [Fin.sum_univ_eq_sum_range (fun i => wC p r k (r + 2 * i + 1)) m]
    have : ∀ i ∈ Finset.range m, wC p r k (r + 2 * i + 1) =
        if (i < (p + k - r) / 2) then 2 else 1 := by
      intro i _
      unfold wC
      by_cases h : r + 2 * i + 1 < p + k
      · rw [if_neg (by omega), if_pos h, if_pos (by omega)]
      · rw [if_neg (by omega), if_neg h, if_neg (by omega)]
    rw [Finset.sum_congr rfl this, sum_ite_two_one, card_range_lt]
    simp
  rw [h1, h2]

/-- The full-member LP1 price in closed form (`k ≤ r`). -/
theorem lp1Base_closed (G : BlockGeom) (kf : ℕ → ℕ → ℕ) (r p : ℕ) (hk : kf r p ≤ r) :
    lp1Base G kf r p =
      2 * (r - (kf r p - (r - p))) + 2 * (G.geometry r).k +
        min (2 * (G.geometry r).k) (p + kf r p - r) -
        (min (p + kf r p - r) (2 * (G.geometry r).k) - (G.geometry r).k) := by
  unfold lp1Base
  rw [wC_row p r (kf r p) _ hk, wC_col p r (kf r p) _ hk]
  omega

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
    show ∑ i : Fin m, uPot p r k (r + 2 * (i : ℕ)) = _
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
    show ∑ i : Fin m, uPot p r k (r + 2 * (i : ℕ) + 1) = _
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

/-- The full-member LP2 price in closed form (`k ≤ r`). -/
theorem lp2Base_closed (G : BlockGeom) (kf : ℕ → ℕ → ℕ) (r p : ℕ) (hk : kf r p ≤ r) :
    lp2Base G kf r p =
      2 * (r - kf r p) + 2 * (G.geometry r).k + (2 * (G.geometry r).k - (p - r)) -
        ((G.geometry r).k - (p - r)) := by
  unfold lp2Base
  rw [uPot_row p r (kf r p) _ hk, uPot_col p r (kf r p) _ hk]
  omega

/-! ### Branch statements -/

/-- **LP1 branch** of the root class `j`: on the LP1 window a member is cleared by the closed
LP1 price plus its deletion count. -/
theorem lp1_gle_tt (c : ℚ) (hc : 0 < c) (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth : ℕ) (i : ((altGeom c hc).family Fr depth).ι)
    (hi : ((altGeom c hc).family Fr depth).Adm i) (hr : i.1 % 2 = 0)
    (p k j : ℕ) [Fact p.Prime] (hpn : ¬ p ∣ nm) (hp5 : 5 ≤ p) (hpq : 2 * q ≤ p)
    (hk : q * k = j * p + o) (hk0 : 0 < k) (hkp : k < p) (hj0 : 0 < j)
    (hN2 : i.1 + 2 * (altGeom c hc).borderSize i.1 ≤ 2 * p) (hrp : p ≤ i.1)
    (hUk : i.1 < p + k) :
    GLE p (2 * (i.1 - (k - (i.1 - p))) + 2 * (altGeom c hc).borderSize i.1 +
        min (2 * (altGeom c hc).borderSize i.1) (p + k - i.1) -
        (min (p + k - i.1) (2 * (altGeom c hc).borderSize i.1) - (altGeom c hc).borderSize i.1) +
        delCount (altGeom c hc) i) (((altGeom c hc).family Fr depth).Q i) := by
  have hv := lp1Valid_tt c hc T hnorm i.1 p k j hr hpn hp5 hpq hk hk0 hkp hj0 hN2 hrp hUk
  have hg := (lp1Layer (altGeom c hc) Fr depth q o (fun _ _ => k) (fun _ _ => j)).gle i hi p hv
  refine hg.mono (le_of_eq ?_)
  show lp1Base (altGeom c hc) (fun _ _ => k) i.1 p + 1 * delCount (altGeom c hc) i = _
  rw [lp1Base_closed (altGeom c hc) (fun _ _ => k) i.1 p (show k ≤ i.1 by omega),
    geometry_k_eq_borderSize, one_mul]

/-- **LP2 branch** of the root class `j`: on the LP2 window a member is cleared by the closed
LP2 price plus its deletion count. -/
theorem lp2_gle_tt (c : ℚ) (hc : 0 < c) (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth : ℕ) (i : ((altGeom c hc).family Fr depth).ι)
    (hi : ((altGeom c hc).family Fr depth).Adm i) (hr : i.1 % 2 = 0)
    (p k j : ℕ) [Fact p.Prime] (hpn : ¬ p ∣ nm) (hp5 : 5 ≤ p) (hpq : 2 * q ≤ p)
    (hk : q * k = j * p + o) (hk0 : 0 < k) (hkp : k < p) (hj0 : 0 < j)
    (hNk : i.1 + 2 * (altGeom c hc).borderSize i.1 ≤ p + k) (hrp : i.1 < p) (hkr : k ≤ i.1)
    (hpm : p < i.1 + (altGeom c hc).borderSize i.1) :
    GLE p (2 * (i.1 - k) + 2 * (altGeom c hc).borderSize i.1 +
        (2 * (altGeom c hc).borderSize i.1 - (p - i.1)) -
        ((altGeom c hc).borderSize i.1 - (p - i.1)) +
        delCount (altGeom c hc) i) (((altGeom c hc).family Fr depth).Q i) := by
  have hv := lp2Valid_tt c hc T hnorm i.1 p k j hr hpn hp5 hpq hk hk0 hkp hj0 hNk hrp hkr hpm
  have hg := (lp2Layer (altGeom c hc) Fr depth q o (fun _ _ => k) (fun _ _ => j)).gle i hi p hv
  refine hg.mono (le_of_eq ?_)
  show lp2Base (altGeom c hc) (fun _ _ => k) i.1 p + 1 * delCount (altGeom c hc) i = _
  rw [lp2Base_closed (altGeom c hc) (fun _ _ => k) i.1 p hkr, geometry_k_eq_borderSize, one_mul]

end CatalanCore.Uniform.Content.BankShared.TwoTerm
