module

public import CatalanCore.Zeta5.Frames.InnerWeights
public import CatalanCore.Zeta5.Frames.ClassData
public import CatalanCore.Zeta5.Local.SmallPrimeTau

@[expose] public section

/-!
# ZC12: the inner CRT allocation `L₀ + ∑ L_a = h`

For a prime `p` with `K/M < p ≤ K/3` (`K = 40 n`, `N = 3 n`, `h = 37 n`), put `m = (p-1)/2` and let
`ℓ_A(a) = #{1 ≤ j ≤ A : j ≡ ±a (p)}` (`SX p A a`). The reserve at the zero class is `L₀`; the other
`m` classes receive `L_a = T - 3 ℓ_N(a) + ε_a` rows, where
`m T + E = h - L₀ + 3 (N - ⌊N/p⌋)`, `0 ≤ E < m`, and `ε_a = 1` on a set of `E` classes of largest
`ℓ_K`.

This file defines the allocation and proves the arithmetic facts used by the weight comparison
`winner_ACI` (`InnerWeights`): `L_a ≥ 0` (no truncation), `L₀ + ∑ L_a = h`, and the two comparison
conditions `(P)` and `(Z)`.
-/

open Finset Polynomial

namespace Apery

/-- A set of `E` elements of `s` of largest `f`-value. -/
lemma exists_top {α : Type*} [DecidableEq α] (f : α → ℕ) (s : Finset α) :
    ∀ E, E ≤ s.card → ∃ S ⊆ s, S.card = E ∧ ∀ a ∈ S, ∀ c ∈ s, c ∉ S → f c ≤ f a := by
  intro E
  induction E with
  | zero => intro _; exact ⟨∅, by simp, by simp, by simp⟩
  | succ E ih =>
    intro hE
    obtain ⟨S, hSs, hSc, hSp⟩ := ih (by omega)
    have hne : (s \ S).Nonempty := by
      rw [← Finset.card_pos]
      have := Finset.card_sdiff_add_card_eq_card hSs
      omega
    obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image (s \ S) f hne
    have hcs : c ∈ s := (Finset.mem_sdiff.mp hc).1
    have hcS : c ∉ S := (Finset.mem_sdiff.mp hc).2
    refine ⟨insert c S, ?_, ?_, ?_⟩
    · exact Finset.insert_subset hcs hSs
    · rw [Finset.card_insert_of_notMem hcS, hSc]
    · intro a ha d hd hdS
      have hdS' : d ∉ S := fun h => hdS (Finset.mem_insert_of_mem h)
      have hdc : d ≠ c := fun h => hdS (h ▸ Finset.mem_insert_self _ _)
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · exact hmax d (Finset.mem_sdiff.mpr ⟨hd, hdS'⟩)
      · exact hSp a ha' d hd hdS'

section
variable {p : ℕ} [hp : Fact p.Prime]

lemma aCnt_consec {m : ℕ} (hm : 2 * m + 1 = p) {v a c : ℕ} (ha1 : 1 ≤ a) (ham : a ≤ m)
    (hc1 : 1 ≤ c) (hcm : c ≤ m) : aCnt p v a ≤ aCnt p v c + 1 := by
  unfold aCnt
  split_ifs <;> omega

/-- `∑_{c=1}^m a_c = v`. -/
lemma sum_aCnt {m : ℕ} (hm : 2 * m + 1 = p) {v : ℕ} (hv : v < p) :
    ∑ c ∈ Icc 1 m, aCnt p v c = v := by
  unfold aCnt
  rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
  have e1 : (Icc 1 m).filter (fun c => c ≤ v) = Icc 1 (min v m) := by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  have e2 : (Icc 1 m).filter (fun c => p - v ≤ c) = Icc (max (p - v) 1) m := by
    ext c; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [e1, e2, Nat.card_Icc, Nat.card_Icc]
  push_cast
  omega

/-- `∑_{a=1}^m ℓ_X(a) = X - ⌊X/p⌋`. -/
lemma sum_SX_class {m : ℕ} (hm : 2 * m + 1 = p) (X : ℕ) :
    ∑ a ∈ Icc 1 m, SX p X (((a : ℕ) : ℤ) : ZMod p) = X - X / p := by
  have h1 : ∀ a ∈ Icc 1 m, SX p X (((a : ℕ) : ℤ) : ZMod p) = 2 * (X / p) + aCnt p (X % p) a :=
    fun a ha => SX_class hm (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2 X
  rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, sum_aCnt hm (Nat.mod_lt X hp.out.pos)]
  simp only [Finset.sum_const, Nat.card_Icc, smul_eq_mul]
  have h0 : p * (X / p) + X % p = X := Nat.div_add_mod X p
  generalize X / p = q at h0 ⊢
  generalize X % p = r at h0 ⊢
  rw [← hm] at h0
  have h3 : X = m * (2 * q) + r + q := by nlinarith [h0]
  rw [show m + 1 - 1 = m by omega]
  omega

end


/-- The hypotheses of the inner range: `M ≥ 40`, `K = 40 n ≥ 200 M²`, `K/M < p ≤ K/3`, and the
zero-class reserve `L₀` (the sources use `4M + 10` and `(κ + s + 2) M + 10 = 13 M + 10`). -/
structure InnerHyp (p n M L0 : ℕ) : Prop where
  prime : p.Prime
  hM : 40 ≤ M
  hK : 200 * M ^ 2 ≤ 40 * n
  hpM : 40 * n < p * M
  hp3 : 3 * p ≤ 40 * n
  hL0a : 2 * M ≤ L0
  hL0b : L0 ≤ 13 * M + 10

namespace InnerHyp
variable {p n M L0 : ℕ} (H : InnerHyp p n M L0)
include H

lemma p200 : 200 * M < p := by
  have h1 : 200 * M * M < p * M := by nlinarith [H.hK, H.hpM]
  exact Nat.lt_of_mul_lt_mul_right h1

lemma p_odd : 2 * (p / 2) + 1 = p := by
  have hp := H.prime
  have := hp.eq_one_or_self_of_dvd 2
  rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
  · have := this ⟨k, by omega⟩
    have := H.p200; have := H.hM; omega
  · omega

lemma p_sq : 200 * (40 * n) < p ^ 2 := by
  have h1 := H.p200
  have h2 := H.hpM
  nlinarith

lemma n_pos : 1 ≤ n := by
  have := H.hK; have := H.hM; nlinarith

lemma mN_lt : 3 * n / p < M := by
  rw [Nat.div_lt_iff_lt_mul H.prime.pos]
  have := H.hpM; nlinarith

lemma mK_lt : 40 * n / p < M := by
  rw [Nat.div_lt_iff_lt_mul H.prime.pos]
  have := H.hpM; nlinarith

end InnerHyp

section alloc
variable (p n L0 : ℕ)

/-- `h - L₀ + 3 (N - ⌊N/p⌋)`. -/
def innerTot : ℕ := 37 * n - L0 + 3 * (3 * n - 3 * n / p)
/-- The base dimension `T`. -/
def innerT : ℕ := innerTot p n L0 / (p / 2)
/-- The number of extras `E`. -/
def innerE : ℕ := innerTot p n L0 % (p / 2)

/-- `ℓ_K(a)`. -/
def lK (a : ℕ) : ℕ := SX p (40 * n) (((a : ℕ) : ℤ) : ZMod p)
/-- `ℓ_N(a)`. -/
def lN (a : ℕ) : ℕ := SX p (3 * n) (((a : ℕ) : ℤ) : ZMod p)

open Classical in
/-- The set of classes receiving an extra row: `E` classes of largest `ℓ_K`. -/
noncomputable def epsSet : Finset (Fin (p / 2 + 1)) :=
  if h : innerE p n L0 ≤ ((Finset.univ : Finset (Fin (p / 2 + 1))).erase 0).card then
    Classical.choose (exists_top (fun a : Fin (p / 2 + 1) => lK p n a) _ _ h)
  else ∅

open Classical in
/-- The class dimensions `L_a`. -/
noncomputable def innerL (a : Fin (p / 2 + 1)) : ℕ :=
  if a = 0 then L0 else innerT p n L0 + (if a ∈ epsSet p n L0 then 1 else 0) - 3 * lN p n a

end alloc


namespace InnerHyp
variable {p n M L0 : ℕ} (H : InnerHyp p n M L0)
include H

lemma m_pos : 1 ≤ p / 2 := by
  have := H.p200; have := H.hM; omega

lemma tot_eq : (p / 2) * innerT p n L0 + innerE p n L0 = innerTot p n L0 := by
  unfold innerT innerE
  have := Nat.div_add_mod (innerTot p n L0) (p / 2)
  linarith

lemma E_lt : innerE p n L0 < p / 2 := Nat.mod_lt _ H.m_pos

lemma tot_le : innerTot p n L0 ≤ 46 * n := by
  unfold innerTot
  generalize 3 * n / p = b
  omega

/-- `p ℓ_N(a) ≤ 2 N + p`. -/
lemma pl_N_le {a : ℕ} (ha1 : 1 ≤ a) (ham : a ≤ p / 2) : p * lN p n a ≤ 2 * (3 * n) + p := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  unfold lN
  rw [SX_class H.p_odd ha1 ham]
  have hv := Nat.mod_lt (3 * n) H.prime.pos
  have h0 : p * (3 * n / p) + 3 * n % p = 3 * n := Nat.div_add_mod _ _
  unfold aCnt
  generalize 3 * n / p = q at *
  generalize 3 * n % p = v at *
  split_ifs <;> first | nlinarith | (have : p ≤ 2 * v := by omega
                                     nlinarith)

lemma mN_pos_bound : 2 * L0 + 6 * (3 * n / p) ≤ 34 * n := by
  have h1 := H.mN_lt
  have h2 := H.hL0b
  have h3 := H.hK
  have h4 := H.hM
  nlinarith

lemma three_lN_le {a : ℕ} (ha1 : 1 ≤ a) (ham : a ≤ p / 2) : 3 * lN p n a ≤ innerT p n L0 := by
  have hm := H.p_odd
  have h1 := H.pl_N_le ha1 ham
  have h2 := H.mN_pos_bound
  have h3 := H.hp3
  have h4 := H.tot_eq
  have h5 := H.E_lt
  -- 2 * tot ≥ 6 N + 3 p
  have h6 : 6 * (3 * n) + 3 * p ≤ 2 * innerTot p n L0 := by
    unfold innerTot
    have : 3 * n / p ≤ 3 * n := Nat.div_le_self _ _
    have : L0 ≤ 37 * n := by nlinarith [H.hL0b, H.hK, H.hM]
    generalize 3 * n / p = b at *
    omega
  by_contra hcon
  push Not at hcon
  -- T + 1 ≤ 3 ℓ
  have h7 : (p / 2) * (innerT p n L0 + 1) ≤ (p / 2) * (3 * lN p n a) :=
    Nat.mul_le_mul_left _ (by omega)
  -- 6 m ℓ ≤ 6 N + 3 p
  have h8 : 6 * ((p / 2) * lN p n a) ≤ 6 * (3 * n) + 3 * p := by
    have : 2 * (p / 2) = p - 1 := by omega
    have h9 : (p - 1) * lN p n a + lN p n a = p * lN p n a := by
      rw [← Nat.succ_mul]; congr 1; omega
    nlinarith
  nlinarith

lemma innerT_le : innerT p n L0 ≤ 3 * M := by
  have hm := H.p_odd
  have h1 := H.tot_eq
  have h2 := H.tot_le
  have h3 := H.hpM
  have h4 := H.p200
  by_contra hcon
  push Not at hcon
  have h5 : (p / 2) * (3 * M) ≤ (p / 2) * innerT p n L0 := Nat.mul_le_mul_left _ (by omega)
  have h6 : 3 * M * (p / 2) ≤ 46 * n := by nlinarith
  have h7 : p * M = 2 * (p / 2 * M) + M := by
    have : p = 2 * (p / 2) + 1 := hm.symm
    nlinarith
  have h8 : 28 * ((p / 2) * M) ≤ 46 * M := by nlinarith
  have h9 : 28 * (p / 2) ≤ 46 := by
    have : (28 * (p / 2)) * M ≤ 46 * M := by nlinarith
    exact Nat.le_of_mul_le_mul_right this (by have := H.hM; omega)
  have := H.m_pos
  have := H.p200; have := H.hM
  omega

end InnerHyp


namespace InnerHyp
variable {p n M L0 : ℕ} (H : InnerHyp p n M L0)
include H

lemma epsSet_spec : epsSet p n L0 ⊆ Finset.univ.erase 0 ∧ (epsSet p n L0).card = innerE p n L0 ∧
    ∀ a ∈ epsSet p n L0, ∀ c ∈ (Finset.univ : Finset (Fin (p / 2 + 1))).erase 0,
      c ∉ epsSet p n L0 → lK p n c ≤ lK p n a := by
  have hcard : ((Finset.univ : Finset (Fin (p / 2 + 1))).erase 0).card = p / 2 := by simp
  have hE : innerE p n L0 ≤ ((Finset.univ : Finset (Fin (p / 2 + 1))).erase 0).card := by
    rw [hcard]; exact H.E_lt.le
  unfold epsSet
  rw [dif_pos hE]
  exact Classical.choose_spec (exists_top (fun a : Fin (p / 2 + 1) => lK p n a) _ _ hE)

lemma innerL_zero : innerL p n L0 0 = L0 := by
  unfold innerL; simp

lemma innerL_spec (a : Fin (p / 2 + 1)) (ha : a ≠ 0) :
    innerL p n L0 a + 3 * lN p n a = innerT p n L0 + (if a ∈ epsSet p n L0 then 1 else 0) := by
  unfold innerL
  rw [if_neg ha]
  have h1 : 1 ≤ (a : ℕ) := by
    rcases Nat.eq_zero_or_pos (a : ℕ) with h | h
    · exact absurd (Fin.ext h) ha
    · exact h
  have h2 : (a : ℕ) ≤ p / 2 := Nat.lt_succ_iff.mp a.isLt
  have := H.three_lN_le h1 h2
  split_ifs <;> omega

lemma lK_consec (a c : Fin (p / 2 + 1)) (ha : a ≠ 0) (hc : c ≠ 0) :
    lK p n a ≤ lK p n c + 1 := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  have h1 : 1 ≤ (a : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => ha (Fin.ext h))
  have h2 : (a : ℕ) ≤ p / 2 := Nat.lt_succ_iff.mp a.isLt
  have h3 : 1 ≤ (c : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => hc (Fin.ext h))
  have h4 : (c : ℕ) ≤ p / 2 := Nat.lt_succ_iff.mp c.isLt
  unfold lK
  rw [SX_class H.p_odd h1 h2, SX_class H.p_odd h3 h4]
  have := aCnt_consec H.p_odd (v := 40 * n % p) h1 h2 h3 h4
  omega

lemma topw_eq (a : Fin (p / 2 + 1)) (ha : a ≠ 0) :
    topw (innerL p n L0) (Bse p (40 * n) (3 * n)) a =
      (innerT p n L0 : ℚ) + (if a ∈ epsSet p n L0 then 1 else 0) - (lK p n a : ℚ) / 2 - 2 := by
  unfold topw Bse
  have hna : (a : ℕ) ≠ 0 := fun h => ha (Fin.ext h)
  rw [if_neg hna]
  have h := H.innerL_spec a ha
  have h' : ((innerL p n L0 a : ℕ) : ℚ) + 3 * (lN p n a : ℚ) =
      (innerT p n L0 : ℚ) + (if a ∈ epsSet p n L0 then 1 else 0) := by
    have h2 := h
    split_ifs at h2 ⊢ <;> exact_mod_cast h2
  unfold lN at h'
  unfold lK
  push_cast at h' ⊢
  linarith

lemma inner_P : ∀ a c : Fin (p / 2 + 1), a ≠ 0 → c ≠ 0 →
    topw (innerL p n L0) (Bse p (40 * n) (3 * n)) a - 1 ≤
      topw (innerL p n L0) (Bse p (40 * n) (3 * n)) c := by
  intro a c ha hc
  rw [H.topw_eq a ha, H.topw_eq c hc]
  obtain ⟨hsub, hcard, hprop⟩ := H.epsSet_spec
  have hc1 := H.lK_consec a c ha hc
  have hc2 := H.lK_consec c a hc ha
  have hc1' : (lK p n a : ℚ) ≤ lK p n c + 1 := by exact_mod_cast hc1
  have hc2' : (lK p n c : ℚ) ≤ lK p n a + 1 := by exact_mod_cast hc2
  by_cases hA : a ∈ epsSet p n L0 <;> by_cases hC : c ∈ epsSet p n L0
  · simp only [if_pos hA, if_pos hC]; linarith
  · simp only [if_pos hA, if_neg hC]
    have := hprop a hA c (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩) hC
    have : (lK p n c : ℚ) ≤ lK p n a := by exact_mod_cast this
    linarith
  · simp only [if_neg hA, if_pos hC]; linarith
  · simp only [if_neg hA, if_neg hC]; linarith

lemma inner_Z : ∀ a : Fin (p / 2 + 1), a ≠ 0 →
    topw (innerL p n L0) (Bse p (40 * n) (3 * n)) a - 1 ≤
      2 * (innerL p n L0 0 : ℚ) + (Bse p (40 * n) (3 * n) 0 - 4) / 2 := by
  intro a ha
  rw [H.topw_eq a ha, H.innerL_zero]
  haveI : Fact p.Prime := ⟨H.prime⟩
  have hB : Bse p (40 * n) (3 * n) 0 = 5 + 6 * ((3 * n / p : ℕ) * 2 : ℕ) - ((40 * n / p : ℕ) * 2 : ℕ) := by
    unfold Bse
    simp only [if_true, Nat.cast_zero, Int.cast_zero, SX_zero]
    push_cast; ring
  rw [hB]
  have hT : (innerT p n L0 : ℚ) ≤ 3 * M := by exact_mod_cast H.innerT_le
  have hmK : ((40 * n / p : ℕ) : ℚ) + 1 ≤ M := by exact_mod_cast H.mK_lt
  have hL : (2 * M : ℚ) ≤ L0 := by exact_mod_cast H.hL0a
  have hmN : (0 : ℚ) ≤ ((3 * n / p : ℕ) : ℚ) := Nat.cast_nonneg _
  have hlK : (0 : ℚ) ≤ lK p n a := Nat.cast_nonneg _
  have hε : (if a ∈ epsSet p n L0 then (1 : ℚ) else 0) ≤ 1 := by split_ifs <;> norm_num
  push_cast
  linarith

end InnerHyp


section sep
variable {p : ℕ} [hp : Fact p.Prime]

/-- Ported from mo271/Zeta5 (Apache-2.0), commit 7fe736760f4b96bfdb4334b68e3b3124ecbe10b0,
`Apery/Norm.lean` `Sep_PlK`. The poles `±j`, `1 ≤ j ≤ K` have pairwise differences `< p²`. -/
lemma Sep_PlK {K : ℕ} (hK : 2 * K < p ^ 2) : Sep p (PlK K) := by
  intro r hr s hs hrs _ hdvd
  obtain ⟨j, hj, ε, hε, rfl⟩ := mem_PlK_iff hr
  obtain ⟨j', hj', ε', hε', rfl⟩ := mem_PlK_iff hs
  have h1 := Finset.mem_Icc.mp hj
  have h2 := Finset.mem_Icc.mp hj'
  have hlt : |ε * (j : ℤ) - ε' * j'| < (p : ℤ) ^ 2 := by
    rcases hε with rfl | rfl <;> rcases hε' with rfl | rfl <;> rw [abs_lt] <;> constructor <;>
      push_cast <;> nlinarith
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  exact hrs (by linarith)

end sep

lemma sum_range_shift (f : ℕ → ℕ) (m : ℕ) : ∑ i ∈ range m, f (i + 1) = ∑ j ∈ Icc 1 m, f j := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega)]

namespace InnerHyp
variable {p n M L0 : ℕ} (H : InnerHyp p n M L0)
include H

lemma sum_innerL : ∑ a : Fin (p / 2 + 1), innerL p n L0 a = 37 * n := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  obtain ⟨hsub, hcard, hprop⟩ := H.epsSet_spec
  rw [Fin.sum_univ_succ, H.innerL_zero]
  have key : ∀ i : Fin (p / 2), innerL p n L0 i.succ + 3 * lN p n ((i.succ : Fin (p / 2 + 1)) : ℕ) =
      innerT p n L0 + (if i.succ ∈ epsSet p n L0 then 1 else 0) :=
    fun i => H.innerL_spec i.succ (Fin.succ_ne_zero i)
  have hsum1 : ∑ i : Fin (p / 2), innerL p n L0 i.succ +
      3 * ∑ i : Fin (p / 2), lN p n ((i.succ : Fin (p / 2 + 1)) : ℕ) =
      (p / 2) * innerT p n L0 + ∑ i : Fin (p / 2), (if i.succ ∈ epsSet p n L0 then 1 else 0) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_congr rfl fun i _ => key i,
      Finset.sum_add_distrib]
    simp
  have hlN : ∑ i : Fin (p / 2), lN p n ((i.succ : Fin (p / 2 + 1)) : ℕ) = 3 * n - 3 * n / p := by
    have e : ∀ i : Fin (p / 2), lN p n ((i.succ : Fin (p / 2 + 1)) : ℕ) = lN p n ((i : ℕ) + 1) := by
      intro i; simp [Fin.val_succ]
    rw [Finset.sum_congr rfl fun i _ => e i,
      Fin.sum_univ_eq_sum_range (fun i => lN p n (i + 1)) (p / 2),
      sum_range_shift (fun j => lN p n j) (p / 2)]
    exact sum_SX_class H.p_odd (3 * n)
  have hε : ∑ i : Fin (p / 2), (if i.succ ∈ epsSet p n L0 then 1 else 0) = innerE p n L0 := by
    have h0 : (0 : Fin (p / 2 + 1)) ∉ epsSet p n L0 := fun h0 =>
      (Finset.mem_erase.mp (hsub h0)).1 rfl
    have h1 : ∑ a : Fin (p / 2 + 1), (if a ∈ epsSet p n L0 then 1 else 0) = innerE p n L0 := by
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
      simpa using hcard
    rw [Fin.sum_univ_succ, if_neg h0, zero_add] at h1
    exact h1
  rw [hlN, hε] at hsum1
  have h4 := H.tot_eq
  unfold innerTot at h4
  have h5 : L0 ≤ 37 * n := by nlinarith [H.hL0b, H.hK, H.hM]
  have h6 : 3 * n / p ≤ 3 * n := Nat.div_le_self _ _
  generalize 3 * n / p = b at *
  omega

/-- **ZC12.** The inner determinant bound `v_p^G(Δ_K) ≥ γ_p^in = 2 ∑ w` for the allocation
`L_a = T - 3 ℓ_N(a) + ε_a` and the weights `winner` of the ledger (`w_{a,i} = i + b_a -
(ℓ_K(a)+4)/2`, `w_{0,i} = min(2i + 6 m_N - m_K + 1/2, min_c [Z_c - (ℓ_K(c)+4)/2])`). -/
theorem zc12_inner [hp : Fact p.Prime] :
    GV p (Δ n) (2 * ∑ s : (Σ a : Fin (p / 2 + 1), Fin (innerL p n L0 a)),
      winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) s) := by
  have hp5 : 5 ≤ p := by have := H.p200; have := H.hM; omega
  have hsq := H.p_sq
  have hn := H.n_pos
  have hp2 : 25 ≤ p ^ 2 := by nlinarith
  refine inner_bound hp5 H.p_odd H.m_pos n (innerL p n L0) H.sum_innerL
    (Sep_PlK (by omega)) (by omega) (by omega) H.inner_P H.inner_Z

end InnerHyp


/-- The class constants `Bse` are integers. -/
lemma Bse_int (p K N a : ℕ) : ∃ k : ℤ, Bse p K N a = k := by
  unfold Bse
  refine ⟨(if a = 0 then 5 else 0) + 6 * (SX p N (((a : ℤ) : ZMod p)) : ℤ) -
    (SX p K (((a : ℤ) : ZMod p)) : ℤ), ?_⟩
  split_ifs <;> push_cast <;> ring

/-- The inner weights are half-integers. -/
lemma winner_half {m : ℕ} (hm : 1 ≤ m) (L : Fin (m + 1) → ℕ) (b : ℕ → ℚ)
    (hb : ∀ a, ∃ k : ℤ, b a = k) (s : Σ a : Fin (m + 1), Fin (L a)) :
    ∃ k : ℤ, winner hm L b s = k / 2 := by
  have htop : ∀ c : Fin (m + 1), ∃ k : ℤ, topw L b c = k / 2 := by
    intro c
    obtain ⟨k, hk⟩ := hb c
    exact ⟨2 * L c + k - 4, by unfold topw; rw [hk]; push_cast; ring⟩
  unfold winner
  split_ifs with h
  · have hne : (Finset.univ.erase (0 : Fin (m + 1))).Nonempty := ⟨⟨1, by omega⟩, by
      simp [Fin.ext_iff]⟩
    obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_inf' hne (topw L b)
    have hmin : ∃ k : ℤ, tmin hm L b = k / 2 := by
      unfold tmin; rw [hc]; exact htop c
    obtain ⟨k0, hk0⟩ := hb 0
    obtain ⟨k1, hk1⟩ := hmin
    rcases min_choice (2 * (s.2 : ℚ) + (b 0 - 4) / 2) (tmin hm L b) with h1 | h1
    · exact ⟨4 * (s.2 : ℕ) + k0 - 4, by rw [h1, hk0]; push_cast; ring⟩
    · exact ⟨k1, by rw [h1, hk1]⟩
  · obtain ⟨k, hk⟩ := hb s.1
    exact ⟨2 * (s.2 : ℕ) + k - 4, by rw [hk]; push_cast; ring⟩

namespace InnerHyp
variable {p n M L0 : ℕ} (H : InnerHyp p n M L0)
include H

/-- `γ_p^in = 2 ∑ w` is an integer. -/
theorem inner_gamma_int :
    ∃ z : ℤ, 2 * ∑ s : (Σ a : Fin (p / 2 + 1), Fin (innerL p n L0 a)),
      winner H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n)) s = z := by
  choose f hf using winner_half H.m_pos (innerL p n L0) (Bse p (40 * n) (3 * n))
    (fun a => Bse_int p (40 * n) (3 * n) a)
  refine ⟨∑ s, f s, ?_⟩
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [hf s]; ring

end InnerHyp

end Apery
