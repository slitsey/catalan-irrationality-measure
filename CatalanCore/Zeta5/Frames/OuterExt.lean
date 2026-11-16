module

public import CatalanCore.Zeta5.Frames.OuterClass

@[expose] public section

/-!
# ZC18: the outer CRT extension (OUTER-CRT-EXTENSION §O1)

For a prime `p ≥ 101` with `K/3 < p ≤ K` (`K = 40 n`, `N = 3 n`, `h = 37 n`, `2 N < p`) put
`m = (p-1)/2`, reserve `L₀ = 8` rows at the zero class, and `m T + E = h - 8 + 3 N = 23 K/20 - 8`,
`0 ≤ E < m`. The `E` extra rows go to the classes of largest `2 ℓ_K(a) + [a ≤ N]` (decreasing `ℓ_K`,
ties to removed classes first). `L_a = T - 3 [a ≤ N] + ε_a`. The weights are the unclipped
`w_{a,i} = i + 3 ℓ_N(a) - (ℓ_K(a)+4)/2` and the zero weights of `winner`.
Result `zc18_ext`: `v_p^G(Δ_K) ≥ 2 ∑ w = γ_p^ext`, together with `2 ≤ T ≤ 6` (`T_ge2`, `T_le6`),
`L_a ≥ 0` (`extL_spec`) and `L₀ + ∑ L_a = h` (`sum_extL`).
-/

open Finset Polynomial

namespace Apery

/-- The hypotheses of the outer extension. -/
structure ExtHyp (p n : ℕ) : Prop where
  prime : p.Prime
  h101 : 101 ≤ p
  hout : 40 * n < 3 * p
  hpK : p ≤ 40 * n

section alloc
variable (p n : ℕ)

/-- `h - 8 + 3 N`. -/
def extTot : ℕ := 37 * n - 8 + 3 * (3 * n)
/-- The base dimension `T`. -/
def extT : ℕ := extTot n / (p / 2)
/-- The number of extras `E`. -/
def extE : ℕ := extTot n % (p / 2)
/-- The ordering key: `ℓ_K` first, removed classes first among ties. -/
def extKey (a : ℕ) : ℕ := 2 * lK p n a + (if a ≤ 3 * n then 1 else 0)

open Classical in
/-- The classes receiving an extra row. -/
noncomputable def extEps : Finset (Fin (p / 2 + 1)) :=
  if h : extE p n ≤ ((Finset.univ : Finset (Fin (p / 2 + 1))).erase 0).card then
    Classical.choose (exists_top (fun a : Fin (p / 2 + 1) => extKey p n a) _ _ h)
  else ∅

open Classical in
/-- The class dimensions. -/
noncomputable def extL (a : Fin (p / 2 + 1)) : ℕ :=
  if a = 0 then 8 else extT p n + (if a ∈ extEps p n then 1 else 0) - 3 * lN p n a

end alloc

namespace ExtHyp
variable {p n : ℕ} (H : ExtHyp p n)
include H

lemma n3 : 3 ≤ n := by have := H.h101; have := H.hpK; omega

lemma p_odd : 2 * (p / 2) + 1 = p := by
  have hp := H.prime
  have := hp.eq_one_or_self_of_dvd 2
  rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
  · have := this ⟨k, by omega⟩
    have := H.h101; omega
  · omega

lemma m_pos : 1 ≤ p / 2 := by have := H.h101; omega

lemma tot_val : extTot n = 46 * n - 8 := by
  have := H.n3; unfold extTot; omega

lemma tot_eq : (p / 2) * extT p n + extE p n = extTot n := by
  unfold extT extE
  have := Nat.div_add_mod (extTot n) (p / 2)
  linarith

lemma E_lt : extE p n < p / 2 := Nat.mod_lt _ H.m_pos

lemma T_ge2 : 2 ≤ extT p n := by
  unfold extT
  rw [Nat.le_div_iff_mul_le H.m_pos, H.tot_val]
  have := H.p_odd; have := H.hpK; have := H.n3
  omega

lemma T_le6 : extT p n ≤ 6 := by
  by_contra hcon
  push Not at hcon
  have h1 := H.tot_eq
  have h2 := H.tot_val
  have h3 := H.p_odd
  have h4 := H.hout
  have h5 : (p / 2) * 7 ≤ (p / 2) * extT p n := Nat.mul_le_mul_left _ (by omega)
  have := H.n3
  omega

lemma eps_spec : extEps p n ⊆ Finset.univ.erase 0 ∧ (extEps p n).card = extE p n ∧
    ∀ a ∈ extEps p n, ∀ c ∈ (Finset.univ : Finset (Fin (p / 2 + 1))).erase 0,
      c ∉ extEps p n → extKey p n c ≤ extKey p n a := by
  have hcard : ((Finset.univ : Finset (Fin (p / 2 + 1))).erase 0).card = p / 2 := by simp
  have hE : extE p n ≤ ((Finset.univ : Finset (Fin (p / 2 + 1))).erase 0).card := by
    rw [hcard]; exact H.E_lt.le
  unfold extEps
  rw [dif_pos hE]
  exact Classical.choose_spec (exists_top (fun a : Fin (p / 2 + 1) => extKey p n a) _ _ hE)

lemma lN_eq {a : ℕ} (ha1 : 1 ≤ a) (ham : a ≤ p / 2) :
    lN p n a = if a ≤ 3 * n then 1 else 0 := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  unfold lN
  have h3m : 3 * n < p := by have := H.hout; omega
  rw [SX_small H.p_odd h3m ha1 ham]
  unfold aCnt
  have := H.hout
  split_ifs <;> omega

lemma lK_eq {a : ℕ} (ha1 : 1 ≤ a) (ham : a ≤ p / 2) :
    lK p n a = 2 * (40 * n / p) + aCnt p (40 * n % p) a := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  unfold lK
  exact SX_class H.p_odd ha1 ham _

/-- If `T = 2` every removed class receives an extra row (the tie priority is essential). -/
lemma removed_mem (hT : extT p n = 2) (a : Fin (p / 2 + 1)) (ha : a ≠ 0)
    (hN : (a : ℕ) ≤ 3 * n) : a ∈ extEps p n := by
  by_contra hna
  obtain ⟨hsub, hcard, hprop⟩ := H.eps_spec
  have h1 : 1 ≤ (a : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => ha (Fin.ext h))
  have h2 : (a : ℕ) ≤ p / 2 := Nat.lt_succ_iff.mp a.isLt
  have htot := H.tot_eq
  have hv := H.tot_val
  rw [hT] at htot
  have hpo := H.p_odd
  have hn3 := H.n3
  have hpK := H.hpK
  have hout := H.hout
  have hE := H.E_lt
  -- K < 2p, so 40n / p = 1 and v = 40n - p
  have hp30 : 92 * n < 3 * p + 13 := by omega
  have hq : 40 * n / p = 1 := by
    apply le_antisymm
    · have : 40 * n / p < 2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
      omega
    · exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hvv : 40 * n % p = 40 * n - p := by
    have := Nat.div_add_mod (40 * n) p
    rw [hq] at this; omega
  -- the elements of S are all `≤ max N v`
  have hmem : ∀ b ∈ extEps p n, (b : ℕ) ≤ 3 * n ∨ (b : ℕ) ≤ 40 * n - p := by
    intro b hb
    have hb0 : b ≠ 0 := fun h => (Finset.mem_erase.mp (hsub hb)).1 h
    have hb1 : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => hb0 (Fin.ext h))
    have hb2 : (b : ℕ) ≤ p / 2 := Nat.lt_succ_iff.mp b.isLt
    have key := hprop b hb a (Finset.mem_erase.mpr ⟨ha, Finset.mem_univ _⟩) hna
    unfold extKey at key
    rw [lK_eq H h1 h2, lK_eq H hb1 hb2, hq, hvv] at key
    by_contra hcon
    push Not at hcon
    unfold aCnt at key
    simp only [if_pos hN] at key
    split_ifs at key <;> omega
  have hinj : (extEps p n).card ≤ ((Icc 1 (max (3 * n) (40 * n - p))).erase (a : ℕ)).card := by
    refine Finset.card_le_card_of_injOn (fun b => (b : ℕ)) (fun b hb => ?_) ?_
    · have hb0 : b ≠ 0 := fun h => (Finset.mem_erase.mp (hsub hb)).1 h
      have hb1 : 1 ≤ (b : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => hb0 (Fin.ext h))
      simp only [Finset.coe_erase, Set.mem_diff, Finset.coe_Icc, Set.mem_Icc,
        Set.mem_singleton_iff, Finset.mem_coe]
      refine ⟨⟨hb1, ?_⟩, ?_⟩
      · rcases hmem b hb with h | h <;> omega
      · intro h
        exact hna (by have : b = a := Fin.ext h; rw [← this]; exact hb)
    · intro x _ y _ hxy; exact Fin.ext hxy
  rw [Finset.card_erase_of_mem (by simp only [Finset.mem_Icc]; omega), Nat.card_Icc] at hinj
  omega

lemma three_lN_le (a : Fin (p / 2 + 1)) (ha : a ≠ 0) :
    3 * lN p n a ≤ extT p n + (if a ∈ extEps p n then 1 else 0) := by
  have h1 : 1 ≤ (a : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => ha (Fin.ext h))
  have h2 : (a : ℕ) ≤ p / 2 := Nat.lt_succ_iff.mp a.isLt
  rw [lN_eq H h1 h2]
  have hT2 := H.T_ge2
  by_cases hN : (a : ℕ) ≤ 3 * n
  · rw [if_pos hN]
    by_cases hT : extT p n = 2
    · rw [if_pos (H.removed_mem hT a ha hN)]; omega
    · split_ifs <;> omega
  · rw [if_neg hN]; omega

lemma extL_zero : extL p n 0 = 8 := by unfold extL; simp

lemma extL_spec (a : Fin (p / 2 + 1)) (ha : a ≠ 0) :
    extL p n a + 3 * lN p n a = extT p n + (if a ∈ extEps p n then 1 else 0) := by
  unfold extL
  rw [if_neg ha]
  have := H.three_lN_le a ha
  split_ifs at this ⊢ <;> omega

lemma lK_consec (a c : Fin (p / 2 + 1)) (ha : a ≠ 0) (hc : c ≠ 0) :
    lK p n a ≤ lK p n c + 1 := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  have h1 : 1 ≤ (a : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => ha (Fin.ext h))
  have h2 : (a : ℕ) ≤ p / 2 := Nat.lt_succ_iff.mp a.isLt
  have h3 : 1 ≤ (c : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => hc (Fin.ext h))
  have h4 : (c : ℕ) ≤ p / 2 := Nat.lt_succ_iff.mp c.isLt
  rw [lK_eq H h1 h2, lK_eq H h3 h4]
  have := aCnt_consec H.p_odd (v := 40 * n % p) h1 h2 h3 h4
  omega

lemma topw_eq (a : Fin (p / 2 + 1)) (ha : a ≠ 0) :
    topw (extL p n) (Bse p (40 * n) (3 * n)) a =
      (extT p n : ℚ) + (if a ∈ extEps p n then 1 else 0) - (lK p n a : ℚ) / 2 - 2 := by
  unfold topw Bse
  have hna : (a : ℕ) ≠ 0 := fun h => ha (Fin.ext h)
  rw [if_neg hna]
  have h := H.extL_spec a ha
  have h' : ((extL p n a : ℕ) : ℚ) + 3 * (lN p n a : ℚ) =
      (extT p n : ℚ) + (if a ∈ extEps p n then 1 else 0) := by
    have h2 := h
    split_ifs at h2 ⊢ <;> exact_mod_cast h2
  unfold lN at h'
  unfold lK
  push_cast at h' ⊢
  linarith

lemma ext_P : ∀ a c : Fin (p / 2 + 1), a ≠ 0 → c ≠ 0 →
    topw (extL p n) (Bse p (40 * n) (3 * n)) a - 1 ≤
      topw (extL p n) (Bse p (40 * n) (3 * n)) c := by
  intro a c ha hc
  rw [H.topw_eq a ha, H.topw_eq c hc]
  obtain ⟨hsub, hcard, hprop⟩ := H.eps_spec
  have hc1 := H.lK_consec a c ha hc
  have hc2 := H.lK_consec c a hc ha
  have hc1' : (lK p n a : ℚ) ≤ lK p n c + 1 := by exact_mod_cast hc1
  have hc2' : (lK p n c : ℚ) ≤ lK p n a + 1 := by exact_mod_cast hc2
  by_cases hA : a ∈ extEps p n <;> by_cases hC : c ∈ extEps p n
  · simp only [if_pos hA, if_pos hC]; linarith
  · simp only [if_pos hA, if_neg hC]
    have key := hprop a hA c (Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩) hC
    unfold extKey at key
    have : lK p n c ≤ lK p n a := by split_ifs at key <;> omega
    have : (lK p n c : ℚ) ≤ lK p n a := by exact_mod_cast this
    linarith
  · simp only [if_neg hA, if_pos hC]; linarith
  · simp only [if_neg hA, if_neg hC]; linarith

lemma ext_Z : ∀ a : Fin (p / 2 + 1), a ≠ 0 →
    topw (extL p n) (Bse p (40 * n) (3 * n)) a - 1 ≤
      2 * (extL p n 0 : ℚ) + (Bse p (40 * n) (3 * n) 0 - 4) / 2 := by
  intro a ha
  rw [H.topw_eq a ha, H.extL_zero]
  haveI : Fact p.Prime := ⟨H.prime⟩
  have hN : 3 * n / p = 0 := Nat.div_eq_of_lt (by have := H.hout; omega)
  have hB : Bse p (40 * n) (3 * n) 0 = 5 + 6 * ((3 * n / p : ℕ) * 2 : ℕ) - ((40 * n / p : ℕ) * 2 : ℕ) := by
    unfold Bse
    simp only [if_true, Nat.cast_zero, Int.cast_zero, SX_zero]
    push_cast; ring
  rw [hB, hN]
  have hq : 40 * n / p ≤ 2 := by
    have : 40 * n / p < 3 := (Nat.div_lt_iff_lt_mul H.prime.pos).mpr (by have := H.hout; omega)
    omega
  have hT : (extT p n : ℚ) ≤ 6 := by exact_mod_cast H.T_le6
  have hq' : ((40 * n / p : ℕ) : ℚ) ≤ 2 := by exact_mod_cast hq
  have hq0 : (0 : ℚ) ≤ ((40 * n / p : ℕ) : ℚ) := Nat.cast_nonneg _
  have hlK : (0 : ℚ) ≤ lK p n a := Nat.cast_nonneg _
  have hε : (if a ∈ extEps p n then (1 : ℚ) else 0) ≤ 1 := by split_ifs <;> norm_num
  push_cast
  linarith

lemma sum_extL : ∑ a : Fin (p / 2 + 1), extL p n a = 37 * n := by
  haveI : Fact p.Prime := ⟨H.prime⟩
  obtain ⟨hsub, hcard, hprop⟩ := H.eps_spec
  rw [Fin.sum_univ_succ, H.extL_zero]
  have key : ∀ i : Fin (p / 2), extL p n i.succ + 3 * lN p n ((i.succ : Fin (p / 2 + 1)) : ℕ) =
      extT p n + (if i.succ ∈ extEps p n then 1 else 0) :=
    fun i => H.extL_spec i.succ (Fin.succ_ne_zero i)
  have hsum1 : ∑ i : Fin (p / 2), extL p n i.succ +
      3 * ∑ i : Fin (p / 2), lN p n ((i.succ : Fin (p / 2 + 1)) : ℕ) =
      (p / 2) * extT p n + ∑ i : Fin (p / 2), (if i.succ ∈ extEps p n then 1 else 0) := by
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
  have hε : ∑ i : Fin (p / 2), (if i.succ ∈ extEps p n then 1 else 0) = extE p n := by
    have h0 : (0 : Fin (p / 2 + 1)) ∉ extEps p n := fun h0 =>
      (Finset.mem_erase.mp (hsub h0)).1 rfl
    have h1 : ∑ a : Fin (p / 2 + 1), (if a ∈ extEps p n then 1 else 0) = extE p n := by
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
      simpa using hcard
    rw [Fin.sum_univ_succ, if_neg h0, zero_add] at h1
    exact h1
  have hN : 3 * n / p = 0 := Nat.div_eq_of_lt (by have := H.hout; omega)
  rw [hlN, hε, hN] at hsum1
  have h4 := H.tot_eq
  rw [H.tot_val] at h4
  have := H.n3
  omega

/-- **ZC18.** The outer extension: `v_p^G(Δ_K) ≥ γ_p^ext = 2 ∑ w` for the unclipped weights. -/
theorem zc18_ext [hp : Fact p.Prime] :
    GV p (Δ n) (2 * ∑ s : (Σ a : Fin (p / 2 + 1), Fin (extL p n a)),
      winner H.m_pos (extL p n) (Bse p (40 * n) (3 * n)) s) := by
  have hp5 : 5 ≤ p := by have := H.h101; omega
  have hn := H.n3
  have hout := H.hout
  have hp2 : 25 ≤ p ^ 2 := by nlinarith
  have hp13 : 13 * n + 1 ≤ p := by omega
  have hsq : 2 * (40 * n) < p ^ 2 := by nlinarith
  have hsq2 : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2 := by
    have e : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 = 104 * n + 6 := by omega
    rw [e]; nlinarith
  refine inner_bound hp5 H.p_odd H.m_pos n (extL p n) H.sum_extL
    (Sep_PlK hsq) (by omega) hsq2 H.ext_P H.ext_Z

/-- `γ_p^ext` is an integer. -/
theorem ext_gamma_int :
    ∃ z : ℤ, 2 * ∑ s : (Σ a : Fin (p / 2 + 1), Fin (extL p n a)),
      winner H.m_pos (extL p n) (Bse p (40 * n) (3 * n)) s = z := by
  choose f hf using winner_half H.m_pos (extL p n) (Bse p (40 * n) (3 * n))
    (fun a => Bse_int p (40 * n) (3 * n) a)
  refine ⟨∑ s, f s, ?_⟩
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [hf s]; ring

end ExtHyp

end Apery
