import CatalanCore.Arith.Hybrid.PeriodicEntries
import CatalanCore.Arith.Hybrid.Dual
import CatalanCore.Uniform.Content.Member.Entries
import CatalanCore.Rect.CommonMinor
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace CatalanCore.Uniform.Content.BankShared
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic
open scoped Classical
variable {Fr : Frame} {p N : ℕ} [Fact p.Prime]

/-- The physical singular-count levels, used by the existing tropical weight. -/
noncomputable def poleLevels (D : PoleData Fr p N) : ℕ → ℕ → ℕ :=
  fun _ c => ((Icc 1 c).filter (fun k : ℕ => D.singular (k : ℤ))).card

theorem noSing_of_poleLevels_eq (D : PoleData Fr p N) {a b : ℕ}
    (hab : a ≤ b) (heq : poleLevels D p a = poleLevels D p b) :
    ∀ k ∈ Ioc a b, ¬ D.singular (k : ℤ) := by
  let A := (Icc 1 a).filter (fun k : ℕ => D.singular (k : ℤ))
  let B := (Icc 1 b).filter (fun k : ℕ => D.singular (k : ℤ))
  have hsub : A ⊆ B := by
    intro k hk
    obtain ⟨hk, hs⟩ := Finset.mem_filter.1 hk
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2
      ⟨(Finset.mem_Icc.1 hk).1, ((Finset.mem_Icc.1 hk).2.trans hab)⟩, hs⟩
  have hc : A.card = B.card := heq
  have hs : A = B := Finset.eq_of_subset_of_card_le hsub hc.ge
  intro k hk hsing
  have hkb : k ∈ B := Finset.mem_filter.2 ⟨Finset.mem_Icc.2
    ⟨by have := (Finset.mem_Ioc.1 hk).1; omega, (Finset.mem_Ioc.1 hk).2⟩, hsing⟩
  rw [← hs] at hkb
  have hka := (Finset.mem_Icc.1 (Finset.mem_filter.1 hkb).1).2
  have hgt := (Finset.mem_Ioc.1 hk).1
  omega

theorem noSing_of_poleLevels_zero (D : PoleData Fr p N) {a : ℕ}
    (heq : poleLevels D p a = 0) : ∀ k ∈ Icc 1 a, ¬ D.singular (k : ℤ) := by
  have hz : (Icc 1 a).filter (fun k : ℕ => D.singular (k : ℤ)) = ∅ :=
    Finset.card_eq_zero.1 heq
  intro k hk hsing
  have hm := Finset.mem_filter.2 ⟨hk, hsing⟩
  rw [hz] at hm
  exact Finset.not_mem_empty _ hm

theorem zmod_diff_ne_of_not_cong {a b : ℕ}
    (h : ¬ (p : ℤ) ∣ (a : ℤ) - b) : (b : ZMod p) - a ≠ 0 := by
  intro hz
  have hm : b % p = a % p := by
    have hh := congrArg ZMod.val (sub_eq_zero.1 hz)
    simpa only [ZMod.val_natCast] using hh
  exact h (Nat.modEq_iff_dvd.1 hm)

theorem regular_ordered_mem (D : PoleData Fr p N) (hN : N < p * p)
    {a b : ℕ} (hab : a < b) (hb : b < N)
    (hs : ∀ k ∈ Ioc a b, ¬ D.singular (k : ℤ)) :
    (p : ℚ) ^ (if (p : ℤ) ∣ (a : ℤ) - b then 1 else 0) * Fr.Mn a b ∈ S p := by
  have hsum : (∑ k ∈ Ioc a b, Fr.Delta k) ∈ S p := by
    apply (S p).sum_mem
    intro k hk
    exact D.regular_delta k (by have := (Finset.mem_Ioc.1 hk).1; omega)
      (by have := (Finset.mem_Ioc.1 hk).2; omega) (hs k hk)
  have gn := (good_red D.norm_mem).inv D.norm_ne
  have hc : ((b - a : ℕ) : ℚ) = (b : ℚ) - a := Nat.cast_sub hab.le
  by_cases hcong : (p : ℤ) ∣ (a : ℤ) - b
  · simp only [if_pos hcong, pow_one]
    have gd := good_scaled_inverse (p := p) (n := b - a) (by omega) (by omega)
    have g := (gn.mul gd).mul (good_red hsum)
    apply (g.congr' ?_).mem
    rw [Frame.Mn, if_neg hab.ne, min_eq_left hab.le, max_eq_right hab.le, hc]
    simp only [div_eq_mul_inv]
    ring
  · simp only [if_neg hcong, pow_zero, one_mul]
    have gd := ((Good.natCast (ℓ := p) b).sub (Good.natCast a)).inv
      (zmod_diff_ne_of_not_cong hcong)
    have g := (gn.mul gd).mul (good_red hsum)
    apply (g.congr' ?_).mem
    rw [Frame.Mn, if_neg hab.ne, min_eq_left hab.le, max_eq_right hab.le]
    simp only [div_eq_mul_inv]
    ring

theorem pole_entry_ordered_mem (D : PoleData Fr p N) (hN : N < p * p)
    {a b : ℕ} (hab : a < b) (ha : a < N) (hb : b < N) :
    (p : ℚ) ^ wt (poleLevels D) p a b * Fr.Mn a b ∈ S p := by
  by_cases hl : poleLevels D p a = poleLevels D p b
  · have hs := noSing_of_poleLevels_eq D hab.le hl
    simpa only [wt, if_neg hab.ne, hl, ne_eq, not_true_eq_false, if_false, zero_add]
      using regular_ordered_mem D hN hab hb hs
  · by_cases hc : (p : ℤ) ∣ (a : ℤ) - b
    · simpa only [wt, if_neg hab.ne, if_pos hl, if_pos hc, Nat.reduceAdd] using D.square_mem hN ha hb
    · have h := (D.good_cross ha hb (zmod_diff_ne_of_not_cong hc)).mem
      simpa only [wt, if_neg hab.ne, if_pos hl, if_neg hc, add_zero, pow_one] using h

/-- The exact existing HW weight clears every simple-pole entry. -/
theorem pole_entry_mem (D : PoleData Fr p N) (hN : N < p * p)
    (a b : ℕ) (ha : a < N) (hb : b < N) :
    (p : ℚ) ^ wt (poleLevels D) p a b * Fr.Mn a b ∈ S p := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · exact pole_entry_ordered_mem D hN hab ha hb
  · by_cases hl : 0 < poleLevels D p a
    · simpa [wt, hl] using D.square_mem hN ha ha
    · have hz : poleLevels D p a = 0 := by omega
      have hs := noSing_of_poleLevels_zero D hz
      have hsum : (∑ k ∈ Icc 1 a, Fr.Dsq k) ∈ S p := by
        apply (S p).sum_mem
        intro k hk
        exact D.regular_dsq k (Finset.mem_Icc.1 hk).1
          (by have := (Finset.mem_Icc.1 hk).2; omega) (hs k hk)
      have gn := ((good_red D.norm_mem).inv D.norm_ne).neg
      have g := gn.mul (good_red hsum)
      have hmem : Fr.Mn a a ∈ S p := by
        apply (g.congr' ?_).mem
        rw [Frame.Mn, if_pos rfl]
        simp only [div_eq_mul_inv]
        ring
      simpa [wt, hl] using hmem
  · rw [wt_comm, Mn_symm]
    exact pole_entry_ordered_mem D hN hab hb ha

theorem poleLevels_zero_iff (D : PoleData Fr p N) (k : ℕ) (hk : 1 ≤ k)
    (hsing : D.singular (k : ℤ))
    (hfirst : ∀ t : ℕ, 1 ≤ t → t < k → ¬ D.singular (t : ℤ)) (c : ℕ) :
    poleLevels D p c = 0 ↔ c < k := by
  constructor
  · intro hz
    by_contra h
    have hm : k ∈ (Icc 1 c).filter (fun t : ℕ => D.singular (t : ℤ)) :=
      Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hk, by omega⟩, hsing⟩
    have he : (Icc 1 c).filter (fun t : ℕ => D.singular (t : ℤ)) = ∅ := Finset.card_eq_zero.1 hz
    rw [he] at hm
    exact Finset.not_mem_empty _ hm
  · intro hc
    apply Finset.card_eq_zero.2
    apply Finset.eq_empty_iff_forall_notMem.2
    intro t ht
    obtain ⟨ht, hs⟩ := Finset.mem_filter.1 ht
    exact hfirst t (Finset.mem_Icc.1 ht).1 (by have := (Finset.mem_Icc.1 ht).2; omega) hs

/-- The simple-pole table prices the actual common-deletion polynomial. -/
theorem pole_commonMinor_gle (D : PoleData Fr p N) (hN : N < p * p)
    (r m : ℕ) (hsize : r + 2 * m < N) (s : Finset (Fin r)) :
    GLE p (tropVal (HW (poleLevels D) p r m)) (CatalanCore.Rect.commonMinorPoly Fr r m s) := by
  apply CatalanCore.Uniform.Content.Member.member_gle_trop Fr
    (fun c : Fin r => (c : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ))
    (fun j : Fin m => r + 2 * (j : ℕ) + 1) s (HW (poleLevels D) p r m)
  apply CatalanCore.Uniform.Content.Member.fullN_entry_gle
  intro a b
  exact pole_entry_mem D hN _ _
    (lt_of_le_of_lt (hybRow_le r m a) hsize)
    (lt_of_le_of_lt (hybCol_le r m b) hsize)

#print axioms pole_entry_mem
end CatalanCore.Uniform.Content.BankShared
