module

public import CatalanCore.Uniform.Content.Member.Transfer

@[expose] public section

/-!
# A rational `Frame` is a digamma frame (lane H5)

For a `Frame` whose shifts are rational `μ j = u j / q j` (`q j > 0`) the digamma frame
`frameDigamma` with coefficients `c j = w j / norm` has prefixes `f, e` such that
`Fr.Mn a b = if a = b then -e a else (f b - f a) / (b - a)`: the entries of the frame matrix are
exactly the Loewner entries of the digamma frame.  Together with `member_gle_of_loewner` this
lets every H1 theorem about `loewner a b Dg.f Dg.e` apply to the deletion members.
-/

open Finset CatalanCore CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.Member

/-- The digamma presentation of a frame with rational shifts `u / q`. -/
noncomputable def frameDigamma (Fr : Frame) (u q : Fin Fr.d → ℕ) : DigammaFrame (Fin Fr.d) where
  u := u
  q := q
  c := fun j => (Fr.w j : ℚ) / Fr.norm

lemma sum_Ioc_pred {α : Type*} [AddCommGroup α] (g : ℕ → α) {a b : ℕ} (h : a ≤ b) :
    ∑ k ∈ Ioc a b, g (k - 1) = ∑ k ∈ range b, g k - ∑ k ∈ range a, g k := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ih, Finset.sum_range_succ (n := b)]
    simp only [Nat.add_sub_cancel]
    abel

lemma sum_Icc_pred {α : Type*} [AddCommGroup α] (g : ℕ → α) (a : ℕ) :
    ∑ k ∈ Icc 1 a, g (k - 1) = ∑ k ∈ range a, g k := by
  have h := sum_Ioc_pred g (Nat.zero_le a)
  have e : Icc 1 a = Ioc 0 a := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [e]
  simpa using h

variable (Fr : Frame) (u q : Fin Fr.d → ℕ) (hu : ∀ j, Fr.μ j = u j / q j)
  (hq : ∀ j, 0 < q j)

include hu hq

lemma frameDigamma_term (j : Fin Fr.d) (k : ℕ) :
    (frameDigamma Fr u q).c j * (frameDigamma Fr u q).q j /
        (((frameDigamma Fr u q).den j k : ℕ) : ℚ) =
      ((Fr.w j : ℚ) / Fr.norm) / ((k : ℚ) + Fr.μ j) := by
  have hqj : (q j : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (hq j).ne'
  have hμ : 0 < Fr.μ j := (Fr.hμ j).1
  have hx : (k : ℚ) + Fr.μ j ≠ 0 := by positivity
  have h1 : (((frameDigamma Fr u q).den j k : ℕ) : ℚ) = q j * ((k : ℚ) + Fr.μ j) := by
    unfold DigammaFrame.den frameDigamma
    rw [hu j]
    push_cast
    field_simp
  rw [h1]
  simp only [frameDigamma]
  field_simp

lemma frameDigamma_term2 (j : Fin Fr.d) (k : ℕ) :
    (frameDigamma Fr u q).c j * ((frameDigamma Fr u q).q j : ℚ) ^ 2 /
        (((frameDigamma Fr u q).den j k : ℕ) : ℚ) ^ 2 =
      ((Fr.w j : ℚ) / Fr.norm) / ((k : ℚ) + Fr.μ j) ^ 2 := by
  have hqj : (q j : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (hq j).ne'
  have hμ : 0 < Fr.μ j := (Fr.hμ j).1
  have hx : (k : ℚ) + Fr.μ j ≠ 0 := by positivity
  have h1 : (((frameDigamma Fr u q).den j k : ℕ) : ℚ) = q j * ((k : ℚ) + Fr.μ j) := by
    unfold DigammaFrame.den frameDigamma
    rw [hu j]
    push_cast
    field_simp
  rw [h1]
  simp only [frameDigamma]
  field_simp

/-- The prefix `f` is the partial sum of `g k = ∑ j, (w j / norm) / (k + μ j)`. -/
lemma frameDigamma_f (n : ℕ) :
    (frameDigamma Fr u q).f n =
      ∑ k ∈ range n, ∑ j, ((Fr.w j : ℚ) / Fr.norm) / ((k : ℚ) + Fr.μ j) := by
  unfold DigammaFrame.f
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  exact frameDigamma_term Fr u q hu hq j k

lemma frameDigamma_e (n : ℕ) :
    (frameDigamma Fr u q).e n =
      ∑ k ∈ range n, ∑ j, ((Fr.w j : ℚ) / Fr.norm) / ((k : ℚ) + Fr.μ j) ^ 2 := by
  unfold DigammaFrame.e
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  exact frameDigamma_term2 Fr u q hu hq j k

omit hu hq in
lemma delta_eq_g (k : ℕ) (hk : 1 ≤ k) :
    Fr.Delta k = Fr.norm * ∑ j, ((Fr.w j : ℚ) / Fr.norm) / (((k - 1 : ℕ) : ℚ) + Fr.μ j) := by
  unfold Frame.Delta
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hn : Fr.norm ≠ 0 := Fr.hnorm.ne'
  have : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by
    rw [Nat.cast_sub hk]; simp
  rw [this]
  field_simp

omit hu hq in
lemma dsq_eq_g (k : ℕ) (hk : 1 ≤ k) :
    Fr.Dsq k = Fr.norm * ∑ j, ((Fr.w j : ℚ) / Fr.norm) / (((k - 1 : ℕ) : ℚ) + Fr.μ j) ^ 2 := by
  unfold Frame.Dsq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hn : Fr.norm ≠ 0 := Fr.hnorm.ne'
  have : ((k - 1 : ℕ) : ℚ) = (k : ℚ) - 1 := by
    rw [Nat.cast_sub hk]; simp
  rw [this]
  field_simp

lemma sum_delta (a b : ℕ) (h : a ≤ b) :
    ∑ k ∈ Ioc a b, Fr.Delta k =
      Fr.norm * ((frameDigamma Fr u q).f b - (frameDigamma Fr u q).f a) := by
  rw [frameDigamma_f Fr u q hu hq, frameDigamma_f Fr u q hu hq]
  rw [← sum_Ioc_pred (fun k => ∑ j, ((Fr.w j : ℚ) / Fr.norm) / ((k : ℚ) + Fr.μ j)) h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have : 1 ≤ k := by
    have := (Finset.mem_Ioc.1 hk).1; omega
  exact delta_eq_g Fr k this

lemma sum_dsq (a : ℕ) :
    ∑ k ∈ Icc 1 a, Fr.Dsq k = Fr.norm * (frameDigamma Fr u q).e a := by
  rw [frameDigamma_e Fr u q hu hq, ← sum_Icc_pred
    (fun k => ∑ j, ((Fr.w j : ℚ) / Fr.norm) / ((k : ℚ) + Fr.μ j) ^ 2), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have : 1 ≤ k := (Finset.mem_Icc.1 hk).1
  exact dsq_eq_g Fr k this

/-- **The frame is its digamma presentation.** -/
theorem mn_eq_loewner (a b : ℕ) :
    Fr.Mn a b = if a = b then -(frameDigamma Fr u q).e a else
      ((frameDigamma Fr u q).f b - (frameDigamma Fr u q).f a) / ((b : ℚ) - a) := by
  have hn : Fr.norm ≠ 0 := Fr.hnorm.ne'
  unfold Frame.Mn
  by_cases hab : a = b
  · subst hab
    simp only [ite_true]
    rw [sum_dsq Fr u q hu hq]
    field_simp
  · simp only [if_neg hab]
    rcases lt_or_gt_of_ne hab with h | h
    · have hmax : max a b = b := max_eq_right h.le
      have hmin : min a b = a := min_eq_left h.le
      rw [hmax, hmin, sum_delta Fr u q hu hq a b h.le]
      have : ((b : ℚ) - a) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h.ne')
      field_simp
    · have hmax : max a b = a := max_eq_left h.le
      have hmin : min a b = b := min_eq_right h.le
      rw [hmax, hmin, sum_delta Fr u q hu hq b a h.le]
      have h1 : ((a : ℚ) - b) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h.ne')
      have h2 : ((b : ℚ) - a) = -((a : ℚ) - b) := by ring
      rw [h2, div_neg, ← neg_div, neg_sub]
      field_simp

end CatalanCore.Uniform.Content.Member
