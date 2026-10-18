module

public import CatalanCore.Frame.Spec
public import CatalanCore.Decay.Contour

@[expose] public section

/-!
# Atom form of the Loewner matrix of a general frame (WP2b)

For a frame `Fr`, the real matrix `T = const • I + M` has entries `Tent Fr a b`, and

  `norm · Tent a b = ∑' m, atomSum a b m`,    `atomSum a b m = ∑_i w_i / ((a+m+μ_i)(b+m+μ_i))`.

(`norm_mul_Tent`).  For λ this is the legacy `T_eq_atoms` (`16 T = -∑ atomTerm`).

Proof, with no derivatives: the diagonal case is `sum_add_tsum_nat_add` for each family `i`; the
off-diagonal case telescopes `∑_m (g(a+m) - g(b+m)) = ∑_{m ∈ [a,b)} g(m)`, with `g(y) = ∑ w_i/(y+μ_i)`,
because `g → 0`.
-/

open Finset Filter Topology

namespace CatalanCore
namespace Frame

variable (Fr : Frame)

/-- Real entries of `T = const • I + M`. -/
noncomputable def Tent (a b : ℕ) : ℝ := (if a = b then Fr.const else 0) + (Fr.Mn a b : ℝ)

lemma summable_inv_sq_add' (c : ℝ) (hc : 0 < c) :
    Summable fun n : ℕ => 1 / ((n : ℝ) + c) ^ 2 := by
  have hs : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.2 (by norm_num)
  have hs1 : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ 2 := by
    have := (summable_nat_add_iff 1).2 hs
    simpa using this
  set m : ℝ := min 1 c with hm
  have hm0 : 0 < m := lt_min one_pos hc
  refine Summable.of_nonneg_of_le (fun n => by positivity)
    (fun n => ?_) (hs1.mul_left (1 / m ^ 2))
  have h1 : m * ((n : ℝ) + 1) ≤ (n : ℝ) + c := by
    have a1 : m ≤ 1 := min_le_left _ _
    have a2 : m ≤ c := min_le_right _ _
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h2 : 0 < m * ((n : ℝ) + 1) := by positivity
  rw [div_mul_div_comm, one_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  have := pow_le_pow_left₀ h2.le h1 2
  nlinarith [this, mul_pow m ((n : ℝ) + 1) 2]

lemma mu_pos (i : Fin Fr.d) : (0 : ℝ) < (Fr.μ i : ℝ) := by exact_mod_cast (Fr.hμ i).1

/-- Summability of the atoms `m ↦ atomSum a b m`. -/
theorem summable_atomSum (a b : ℕ) : Summable (fun m : ℕ => Fr.atomSum a b m) := by
  unfold atomSum
  refine summable_sum (fun i _ => ?_)
  have hμ := Fr.mu_pos i
  have hs := (summable_inv_sq_add' (Fr.μ i : ℝ) hμ).mul_left |(Fr.w i : ℝ)|
  refine Summable.of_norm_bounded hs (fun m => ?_)
  unfold atomR
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have p1 : 0 < (m : ℝ) + Fr.μ i := by linarith
  have p2 : (m : ℝ) + Fr.μ i ≤ (a : ℝ) + m + Fr.μ i := by linarith
  have p3 : (m : ℝ) + Fr.μ i ≤ (b : ℝ) + m + Fr.μ i := by linarith
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos (lt_of_lt_of_le p1 p2) (lt_of_lt_of_le p1 p3))]
  rw [show |(Fr.w i : ℝ)| * (1 / ((m : ℝ) + Fr.μ i) ^ 2) = |(Fr.w i : ℝ)| / ((m + Fr.μ i) ^ 2) by ring]
  apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
  rw [sq]
  exact mul_le_mul p2 p3 p1.le (by linarith)

lemma atomSum_comm (a b m : ℕ) : Fr.atomSum a b m = Fr.atomSum b a m := by
  unfold atomSum atomR
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm ((a : ℝ) + m + Fr.μ i)]

lemma Mn_comm (a b : ℕ) : Fr.Mn a b = Fr.Mn b a := by
  unfold Mn
  by_cases h : a = b
  · subst h; rfl
  · have h' : b ≠ a := Ne.symm h
    rw [if_neg h, if_neg h', max_comm, min_comm]

/-- `g(y) = ∑_i w_i / (y + μ_i)`. -/
noncomputable def gF (y : ℝ) : ℝ := ∑ i, (Fr.w i : ℝ) / (y + (Fr.μ i : ℝ))

lemma tendsto_gF (a : ℕ) : Tendsto (fun m : ℕ => Fr.gF ((a : ℝ) + m)) atTop (𝓝 0) := by
  unfold gF
  have : Tendsto (fun m : ℕ => ∑ i, (Fr.w i : ℝ) / ((a : ℝ) + m + (Fr.μ i : ℝ))) atTop
      (𝓝 (∑ _i : Fin Fr.d, (0 : ℝ))) := by
    refine tendsto_finsetSum _ (fun i _ => ?_)
    have h1 : Tendsto (fun m : ℕ => (a : ℝ) + m + (Fr.μ i : ℝ)) atTop atTop := by
      have := tendsto_natCast_atTop_atTop (R := ℝ)
      exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_left _ _ this)
    exact tendsto_const_nhds.div_atTop h1
  simpa using this

/-- A telescoping step: `∑_{m<M} (f m - f (m+c)) = ∑_{j<c} f j - ∑_{j<c} f (M+j)`. -/
lemma telescope (f : ℕ → ℝ) (c M : ℕ) :
    ∑ m ∈ range M, (f m - f (m + c)) = ∑ j ∈ range c, f j - ∑ j ∈ range c, f (M + j) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 := Finset.sum_range_succ (fun j => f (M + j)) c
    have h2 := Finset.sum_range_succ' (fun j => f (M + j)) c
    have h3 : ∑ j ∈ range c, f (M + 1 + j) = ∑ j ∈ range c, f (M + (j + 1)) :=
      Finset.sum_congr rfl (fun j _ => by ring_nf)
    rw [h3]
    simp only [add_zero] at h2
    linarith

theorem sum_gF_telescope (a c : ℕ) :
    HasSum (fun m : ℕ => Fr.gF ((a : ℝ) + m) - Fr.gF ((a : ℝ) + m + c))
      (∑ j ∈ range c, Fr.gF ((a : ℝ) + j)) := by
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℝ, f = fun m : ℕ => Fr.gF ((a : ℝ) + m) := ⟨_, rfl⟩
  have hfm : ∀ m : ℕ, f m = Fr.gF ((a : ℝ) + m) := fun m => by rw [hf]
  have hfc : ∀ m : ℕ, f (m + c) = Fr.gF ((a : ℝ) + m + c) := fun m => by
    rw [hfm]; push_cast; ring_nf
  have e : (fun m : ℕ => Fr.gF ((a : ℝ) + m) - Fr.gF ((a : ℝ) + m + c))
      = fun m => f m - f (m + c) := by
    funext m; rw [hfm, hfc]
  rw [e]
  have hsum : Summable (fun m : ℕ => f m - f (m + c)) := by
    by_cases hc : c = 0
    · subst hc; simp
    · have hS := (Fr.summable_atomSum a (a + c)).mul_left (c : ℝ)
      refine hS.congr (fun m => ?_)
      rw [hfm, hfc]
      unfold atomSum atomR gF
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hμ := Fr.mu_pos i
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have hc' : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
      have p1 : (a : ℝ) + m + Fr.μ i ≠ 0 := by positivity
      have p2 : (a : ℝ) + m + c + Fr.μ i ≠ 0 := by positivity
      push_cast
      rw [show (a : ℝ) + c + m + Fr.μ i = (a : ℝ) + m + c + Fr.μ i by ring]
      field_simp
      ring
  have hlim : Tendsto (fun M : ℕ => ∑ m ∈ range M, (f m - f (m + c))) atTop
      (𝓝 (∑ j ∈ range c, f j)) := by
    have e : (fun M : ℕ => ∑ m ∈ range M, (f m - f (m + c)))
        = fun M => ∑ j ∈ range c, f j - ∑ j ∈ range c, f (M + j) := by
      funext M; exact telescope f c M
    rw [e]
    have : Tendsto (fun M : ℕ => ∑ j ∈ range c, f (M + j)) atTop (𝓝 0) := by
      have : Tendsto (fun M : ℕ => ∑ j ∈ range c, f (M + j)) atTop
          (𝓝 (∑ _j ∈ range c, (0 : ℝ))) := by
        refine tendsto_finsetSum _ (fun j _ => ?_)
        have := (Fr.tendsto_gF a).comp (tendsto_add_atTop_nat j)
        refine this.congr (fun M => ?_)
        try simp only [Function.comp_apply, hfm]
        try (push_cast; ring_nf)
      simpa using this
    simpa using tendsto_const_nhds.sub this
  have h2 := hsum.hasSum.tendsto_sum_nat
  have := tendsto_nhds_unique h2 hlim
  have hs : ∑ j ∈ range c, f j = ∑ j ∈ range c, Fr.gF ((a : ℝ) + j) :=
    Finset.sum_congr rfl (fun j _ => hfm j)
  rw [← hs, ← this]
  exact hsum.hasSum

lemma sum_Icc_shift (g : ℕ → ℝ) (a : ℕ) :
    ∑ k ∈ Icc 1 a, g k = ∑ n ∈ range a, g (n + 1) := by
  induction a with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

lemma sum_Ioc_shift (a : ℕ) (g : ℕ → ℚ) (n : ℕ) :
    ∑ k ∈ Ioc a (a + n), g k = ∑ j ∈ range n, g (a + j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← Nat.add_assoc, Finset.sum_Ioc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- **`norm · T = ∑' atoms`** (the atom form of the Loewner matrix). -/
theorem norm_mul_Tent (a b : ℕ) : (Fr.norm : ℝ) * Fr.Tent a b = ∑' m : ℕ, Fr.atomSum a b m := by
  have hn : (Fr.norm : ℝ) ≠ 0 := by exact_mod_cast Fr.hnorm.ne'
  by_cases hab : a = b
  · subst hab
    unfold Tent
    rw [if_pos rfl]
    have hDsq : ∀ k : ℕ, ((Fr.Dsq k : ℚ) : ℝ) = ∑ i, (Fr.w i : ℝ) / (((k : ℝ) - 1) + Fr.μ i) ^ 2 := by
      intro k; unfold Dsq; push_cast; rfl
    have hMn : (Fr.Mn a a : ℝ) = -(1 / (Fr.norm : ℝ)) * ∑ k ∈ Icc 1 a, ∑ i, (Fr.w i : ℝ) / (((k : ℝ) - 1) + Fr.μ i) ^ 2 := by
      unfold Mn; rw [if_pos rfl]; push_cast
      simp only [hDsq]
    rw [hMn]
    have hconst : Fr.const = (∑ i, (Fr.w i : ℝ) * ∑' n : ℕ, 1 / ((n : ℝ) + (Fr.μ i : ℝ)) ^ 2) / (Fr.norm : ℝ) := by
      unfold const hurwitzTail2; rfl
    rw [hconst]
    have hI : ∑ k ∈ Icc 1 a, ∑ i, (Fr.w i : ℝ) / (((k : ℝ) - 1) + Fr.μ i) ^ 2
        = ∑ i, (Fr.w i : ℝ) * ∑ n ∈ range a, 1 / ((n : ℝ) + (Fr.μ i : ℝ)) ^ 2 := by
      rw [sum_Icc_shift (fun k => ∑ i, (Fr.w i : ℝ) / (((k : ℝ) - 1) + Fr.μ i) ^ 2) a,
        Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      push_cast
      rw [show ((n : ℝ) + 1 - 1) = n by ring]
      ring
    rw [hI]
    have hS : ∀ i : Fin Fr.d, Summable (fun m : ℕ => 1 / ((m : ℝ) + ((a : ℝ) + Fr.μ i)) ^ 2) := by
      intro i
      exact summable_inv_sq_add' ((a : ℝ) + Fr.μ i) (by have := Fr.mu_pos i; positivity)
    have hat : ∑' m : ℕ, Fr.atomSum a a m = ∑ i, (Fr.w i : ℝ) * ∑' m : ℕ, 1 / ((m : ℝ) + ((a : ℝ) + Fr.μ i)) ^ 2 := by
      unfold atomSum atomR
      rw [Summable.tsum_finsetSum (fun i _ => by
        have := (hS i).mul_left (Fr.w i : ℝ)
        refine this.congr (fun m => ?_)
        rw [show ((m : ℝ) + ((a : ℝ) + Fr.μ i)) = (a : ℝ) + m + Fr.μ i by ring]
        rw [sq]; ring)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← tsum_mul_left]
      refine tsum_congr (fun m => ?_)
      rw [show ((m : ℝ) + ((a : ℝ) + Fr.μ i)) = (a : ℝ) + m + Fr.μ i by ring]
      rw [sq]; ring
    rw [hat]
    have : ∀ i : Fin Fr.d, ∑' n : ℕ, 1 / ((n : ℝ) + (Fr.μ i : ℝ)) ^ 2
        = ∑ n ∈ range a, 1 / ((n : ℝ) + (Fr.μ i : ℝ)) ^ 2
          + ∑' m : ℕ, 1 / ((m : ℝ) + ((a : ℝ) + Fr.μ i)) ^ 2 := by
      intro i
      have h := (summable_inv_sq_add' (Fr.μ i : ℝ) (Fr.mu_pos i)).sum_add_tsum_nat_add a
      rw [← h]
      congr 1
      refine tsum_congr (fun m => ?_)
      push_cast
      rw [show ((m : ℝ) + a + Fr.μ i) = (m : ℝ) + ((a : ℝ) + Fr.μ i) by ring]
    simp only [this, mul_add, Finset.sum_add_distrib]
    field_simp
    ring
  · -- off-diagonal; reduce to a < b
    wlog hlt : a < b generalizing a b
    · have hba : b < a := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hab)
      have := this b a (Ne.symm hab) hba
      unfold Tent at this ⊢
      rw [if_neg hab, Fr.Mn_comm a b]
      rw [if_neg (Ne.symm hab)] at this
      simp only [atomSum_comm Fr a b] at *
      exact this
    · unfold Tent
      rw [if_neg hab, zero_add]
      obtain ⟨c, hb⟩ : ∃ c : ℕ, b = a + c := ⟨b - a, by omega⟩
      have hcpos : (0 : ℝ) < c := by exact_mod_cast (by omega : 0 < c)
      have hT := sum_gF_telescope Fr a c
      have hat : ∀ m : ℕ, Fr.atomSum a b m
          = (1 / (c : ℝ)) * (Fr.gF ((a : ℝ) + m) - Fr.gF ((a : ℝ) + m + c)) := by
        intro m
        unfold atomSum atomR gF
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have hμ := Fr.mu_pos i
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
        have p1 : (a : ℝ) + m + Fr.μ i ≠ 0 := by positivity
        have p2 : (a : ℝ) + m + c + Fr.μ i ≠ 0 := by positivity
        have e : ((b : ℕ) : ℝ) = a + c := by rw [hb]; push_cast; ring
        rw [e]
        have e2 : (a : ℝ) + c + m + Fr.μ i = (a : ℝ) + m + c + Fr.μ i := by ring
        rw [e2]
        field_simp
        ring
      have hsum := (hT.mul_left (1 / (c : ℝ)))
      have hts : ∑' m : ℕ, Fr.atomSum a b m = (1 / (c : ℝ)) * ∑ j ∈ range c, Fr.gF ((a : ℝ) + j) := by
        rw [show (fun m : ℕ => Fr.atomSum a b m) = fun m : ℕ => (1 / (c : ℝ)) * (Fr.gF ((a : ℝ) + m) - Fr.gF ((a : ℝ) + m + c)) from funext hat]
        exact hsum.tsum_eq
      rw [hts]
      have hmin : min a b = a := min_eq_left hlt.le
      have hmax : max a b = b := max_eq_right hlt.le
      have hMnQ : Fr.Mn a b = (1 / Fr.norm) * (1 / (c : ℚ)) *
          ∑ j ∈ range c, ∑ i, (Fr.w i : ℚ) / (((a : ℚ) + j) + Fr.μ i) := by
        unfold Mn
        rw [if_neg hab, hmin, hmax]
        have hcc : ((b : ℚ) - (a : ℚ)) = (c : ℚ) := by rw [hb]; push_cast; ring
        have hcc' : (((b : ℕ) : ℚ) - ((a : ℕ) : ℚ)) = (c : ℚ) := hcc
        rw [hcc']
        have hI : ∑ k ∈ Ioc a b, Fr.Delta k = ∑ j ∈ range c, ∑ i, (Fr.w i : ℚ) / (((a : ℚ) + j) + Fr.μ i) := by
          rw [hb, sum_Ioc_shift a (fun k => Fr.Delta k) c]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          unfold Delta
          refine Finset.sum_congr rfl (fun i _ => ?_)
          push_cast
          ring_nf
        rw [hI]
      have hMnR := congrArg (Rat.cast : ℚ → ℝ) hMnQ
      push_cast at hMnR
      rw [hMnR]
      unfold gF
      field_simp

/-- **The λ-type head** (left open by WP2a): if every atom `m + μ_i` with `m < N0` has its pole east of
`x*` and every atom with `m ≥ N0` is enclosed, then `atomHead = ∑_{m<N0} atomSum`.  (λ: `xs = 3/8`;
the general head is `Space.atomHead_eq`, a sum over `atomIdx`.) -/
theorem atomHead_eq_sum (N0 a b : ℕ)
    (hlt : ∀ m < N0, ∀ i, ¬ ((N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ i : ℝ)))
    (hge : ∀ m, N0 ≤ m → ∀ i, (N0 : ℝ) + (Fr.xs : ℝ) < (m : ℝ) + (Fr.μ i : ℝ)) :
    Fr.atomHead N0 a b = ∑ m ∈ range N0, Fr.atomSum a b m := by
  unfold atomHead
  have hM : N0 ≤ N0 + ⌈(Fr.xs : ℝ)⌉₊ := Nat.le_add_right _ _
  rw [← Finset.sum_range_add_sum_Ico _ hM]
  have h2 : ∑ m ∈ Ico N0 (N0 + ⌈(Fr.xs : ℝ)⌉₊), Fr.headTerm N0 a b (m : ℝ) = 0 := by
    refine Finset.sum_eq_zero (fun m hm => ?_)
    unfold headTerm
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [if_pos (hge m (Finset.mem_Ico.1 hm).1 i)]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  unfold headTerm atomSum
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [if_neg (hlt m (Finset.mem_range.1 hm) i)]

end Frame
end CatalanCore
