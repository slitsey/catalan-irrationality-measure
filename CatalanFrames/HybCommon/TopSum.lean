module

public import CatalanFrames.HybCommon.Final
public import CatalanFrames.HybCommon.Numer
public import CatalanFrames.HybCommon.Pieces
public import CatalanFrames.HybCommon.Num
public import CatalanCore.Arith.Hybrid.BorderSum
public import CatalanCore.Rect.PairBridgeTop
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# The border cost is negligible, and `Mem2Content` from `DefBothG` families (generic)

`topC_sum_G`: `∑_{p < Bnd} topC · log p = O(r log r) ≤ ε r²` eventually (`m = mf r ≤ r` arbitrary), for
any hybrid instance with the generic numerology `BadInfo I Lc cm` (`Numer.lean`).  `mem2Content_of_both_G`: the bordering step.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Rect

namespace CatalanFrames.HybCommon

variable {Fr : Frame}

/-- Crude bound for any `(r, m)`: the normalisation exponents of the bad primes cost `2 cm β`. -/
lemma topC_sum_aux_G {Lc cm : ℕ} (I : HybInst Fr) (B : BadInfo I Lc cm) (r m : ℕ) :
    ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime,
        (topC I r m p : ℝ) * Real.log p ≤
      2 * ((cm : ℝ) * badLog I) + (Bnd I r m : ℝ) *
        (4 * Real.log (Elev I r m) + Real.log (Bnd I r m)) := by
  set P := (Finset.range (Bnd I r m)).filter Nat.Prime with hP
  set Bn := Bnd I r m with hB
  set E := Elev I r m with hE
  have hlE : 0 ≤ Real.log E := Real.log_natCast_nonneg E
  have hpt : ∀ p ∈ P, (topC I r m p : ℝ) * Real.log p ≤
      2 * (if p ∈ I.cd.bad then (cm : ℝ) * Real.log p else 0) + (4 * Real.log E + Real.log Bn) := by
    intro p hp
    have hp' := Finset.mem_filter.1 hp
    have hlt : p < Bn := Finset.mem_range.1 hp'.1
    have h1 := topC_log_le I r m hp'.2.one_lt
    have h2 : Real.log p ≤ Real.log Bn :=
      Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast hlt.le)
    have hlp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp'.2.one_lt.le)
    have h3 : (cOf I p : ℝ) * Real.log p ≤ if p ∈ I.cd.bad then (cm : ℝ) * Real.log p else 0 := by
      by_cases h : p ∈ I.cd.bad
      · rw [if_pos h]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast B.cOf_le p) hlp
      · rw [if_neg h, cOf_eq_zero I hp'.2 h]; simp
    linarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum] at hsum
  have hcard : (P.card : ℝ) ≤ Bn := by
    have : P.card ≤ Bn := (Finset.card_le_card (Finset.filter_subset _ _)).trans (Finset.card_range _).le
    exact_mod_cast this
  have hlB : 0 ≤ Real.log Bn := Real.log_natCast_nonneg Bn
  have hbad : ∑ p ∈ P, (if p ∈ I.cd.bad then (cm : ℝ) * Real.log p else 0) ≤
      (cm : ℝ) * badLog I := by
    rw [← Finset.sum_filter]
    unfold badLog
    rw [Finset.mul_sum]
    have hsub : P.filter (fun p => p ∈ I.cd.bad) ⊆ I.cd.bad :=
      fun x hx => (Finset.mem_filter.mp hx).2
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun b hb _ =>
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (I.cd.bad_prime b hb).one_lt.le))
  rw [nsmul_eq_mul] at hsum
  have : (P.card : ℝ) * (4 * Real.log E + Real.log Bn) ≤ Bn * (4 * Real.log E + Real.log Bn) :=
    mul_le_mul_of_nonneg_right hcard (by linarith)
  linarith

/-- Pointwise core of `topC_sum_G`: for one `(r, m)` with `m ≤ r` and `r` large. -/
lemma topC_sum_core {Lc cm : ℕ} {I : HybInst Fr} (B : BadInfo I Lc cm) {ε : ℝ} (hε : 0 < ε)
    (r m : ℕ) (hmr : m ≤ r) (hr : Real.log r ≤ ε / 572 * r) (hr2 : 48 / ε ≤ (r : ℝ) ^ 2)
    (hr18 : 18 ≤ r) :
    ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime,
      (topC I r m p : ℝ) * Real.log p ≤ ε * (r : ℝ) ^ 2 := by
  refine (topC_sum_aux_G I B r m).trans ?_
  have hBd := Bnd_le_G B r m
  have hN : r + 2 * m ≤ 3 * r := by omega
  have hrR : (18 : ℝ) ≤ r := by exact_mod_cast hr18
  have hBr : Bnd I r m ≤ 13 * r := by
    have h4 : Lc * (r + 2 * m) ≤ 4 * (3 * r) :=
      Nat.mul_le_mul B.Lc_le hN
    omega
  have hBr2 : Bnd I r m ≤ r ^ 2 := by nlinarith
  have hEr : Elev I r m ≤ r ^ 5 := by
    have h1 : Elev I r m ≤ 5 * (r + 2 * m) ^ 3 := B.Ebd_le _
    have h2 : 5 * (r + 2 * m) ^ 3 ≤ 5 * (3 * r) ^ 3 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN 3)
    have h3 : 5 * (3 * r) ^ 3 ≤ r ^ 5 := by
      have : 135 * r ^ 3 ≤ r ^ 2 * r ^ 3 := Nat.mul_le_mul_right _ (by nlinarith)
      nlinarith
    omega
  have hBpos : (0 : ℝ) < Bnd I r m := by
    have : 0 < Bnd I r m := by unfold Bnd; omega
    exact_mod_cast this
  have hEpos : (0 : ℝ) < Elev I r m := by
    have : 0 < Elev I r m := by
      unfold Elev
      have : 0 < r + 2 * m := by omega
      omega
    exact_mod_cast this
  have hlogE : Real.log (Elev I r m) ≤ 5 * Real.log r := by
    have hc : (Elev I r m : ℝ) ≤ (r : ℝ) ^ 5 := by exact_mod_cast hEr
    have := Real.log_le_log hEpos hc
    rwa [Real.log_pow] at this
  have hlogB : Real.log (Bnd I r m) ≤ 2 * Real.log r := by
    have hc : (Bnd I r m : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast hBr2
    have := Real.log_le_log hBpos hc
    rwa [Real.log_pow] at this
  have hBR : (Bnd I r m : ℝ) ≤ 13 * r := by exact_mod_cast hBr
  have hlr : 0 ≤ Real.log r := Real.log_natCast_nonneg r
  have hr0 : (0 : ℝ) < r := by linarith
  have hconst : 2 * ((cm : ℝ) * badLog I) ≤ 24 := by
    have hc : (cm : ℝ) ≤ 4 := by exact_mod_cast B.cm_le
    have hb := B.badLog_le
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hbn := badLog_nonneg I
    nlinarith
  have h16 : 24 ≤ ε / 2 * (r : ℝ) ^ 2 := by
    have := (div_le_iff₀ hε).1 hr2
    nlinarith
  have hmain : (Bnd I r m : ℝ) * (4 * Real.log (Elev I r m) + Real.log (Bnd I r m))
      ≤ (13 * r) * (22 * Real.log r) := by
    have a1 := Real.log_natCast_nonneg (Elev I r m)
    have a2 := Real.log_natCast_nonneg (Bnd I r m)
    exact mul_le_mul hBR (by linarith) (by linarith) (by positivity)
  have : (13 * (r : ℝ)) * (22 * Real.log r) ≤ ε / 2 * (r : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ 286 * r by positivity)
    nlinarith
  linarith

/-- **The border cost is negligible for an instance family**: eventually in `r`, uniformly in
`m ≤ r`, with a numerology `BadInfo (I r m) Lc cm` for every member. -/
theorem topC_sum_fam {Lc cm : ℕ} (I : ℕ → ℕ → HybInst Fr) (B : ∀ r m, BadInfo (I r m) Lc cm)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ r : ℕ in Filter.atTop, ∀ m, m ≤ r →
    ∑ p ∈ (Finset.range (Bnd (I r m) r m)).filter Nat.Prime,
      (topC (I r m) r m p : ℝ) * Real.log p ≤ ε * (r : ℝ) ^ 2 := by
  have hl := eventually_log_le (e := ε / 572) (by positivity)
  have hbig : ∀ᶠ r : ℕ in atTop, 48 / ε ≤ (r : ℝ) ^ 2 := by
    have : Tendsto (fun r : ℕ => (r : ℝ) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp tendsto_natCast_atTop_atTop
    exact this.eventually_ge_atTop _
  filter_upwards [hl, hbig, eventually_ge_atTop 18] with r hr hr2 hr18 m hmr
  exact topC_sum_core (B r m) hε r m hmr hr hr2 hr18

/-- **The border cost is negligible**, generic in the numerology and in the hybrid size `m = mf r`
(any `mf r ≤ r`). -/
theorem topC_sum_G {Lc cm : ℕ} (I : HybInst Fr) (B : BadInfo I Lc cm) (mf : ℕ → ℕ)
    (hm : ∀ r, mf r ≤ r) {ε : ℝ} (hε : 0 < ε) : ∀ᶠ r : ℕ in Filter.atTop,
    ∑ p ∈ (Finset.range (Bnd I r (mf r))).filter Nat.Prime,
      (topC I r (mf r) p : ℝ) * Real.log p ≤ ε * (r : ℝ) ^ 2 :=
  (topC_sum_fam (fun _ _ => I) (fun _ _ => B) hε).mono fun r h => h (mf r) (hm r)

/-- The border cost is negligible for any `HybParams`. -/
theorem HybParams.topC_sum {I : HybInst Fr} (P : HybParams I) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in Filter.atTop,
    ∑ p ∈ (Finset.range (Bnd I r (P.mf r))).filter Nat.Prime,
      (topC I r (P.mf r) p : ℝ) * Real.log p ≤ ε * (r : ℝ) ^ 2 :=
  topC_sum_G I P.bad P.mf P.mf_le hε

/-- **Bordering step**: a content bound for a simultaneous member-1/member-2 deficit family gives
`Mem2Content` (the border cost is `O(r log r)`). -/
theorem mem2Content_of_both_G (I : HybInst Fr) [∀ r m, I.DiagOK r m] {Λ0 Λ : ℝ} (hΛ : Λ0 ≤ Λ)
    (hsum : ∀ ε > 0, ∀ᶠ r : ℕ in atTop,
      ∑ p ∈ (Finset.range (Bnd I r (r / 8))).filter Nat.Prime,
        (topC I r (r / 8) p : ℝ) * Real.log p ≤ ε * (r : ℝ) ^ 2)
    (h : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∃ T δ : ℕ → ℕ, DefBothG I r T δ ∧
      Real.log (DhybT I r (r / 8) T δ) ≤ (Λ0 + ε) * (r : ℝ) ^ 2) :
    Mem2Content Fr Λ := by
  refine mem2Content_of_top I ?_
  intro ε hε
  filter_upwards [h (ε / 2) (by positivity), hsum (ε / 2) (by positivity)] with r
    ⟨T, δ, hδ, hlog⟩ hS
  refine ⟨T, δ, hδ.2, ?_⟩
  rw [log_DhybTop I r (r / 8) hδ.1]
  nlinarith [hlog, hS, mul_le_mul_of_nonneg_right hΛ (sq_nonneg (r : ℝ))]

end CatalanFrames.HybCommon

namespace CatalanFrames.HybCommon

/-- **Second member from the first member's content, for an instance family** (`δ = 0`, no deficit
families): if `log Dhyb (I r m) ≤ (Λ + ε) r²` eventually, uniformly over the admissible `m` (`A r m → m ≤ r`),
then `Mem2ContentA Fr A Λ` (`A r m → m ≤ r` eventually); the bordering costs only `topC`, which is `O(r log r)` (`topC_sum_fam`). -/
theorem mem2ContentA_of_member1 {Fr : Frame} {Lc cm : ℕ} (I : ℕ → ℕ → HybInst Fr)
    [∀ r m, (I r m).DiagOK r m] (B : ∀ r m, BadInfo (I r m) Lc cm) {Λ : ℝ} (A : ℕ → ℕ → Prop)
    (hA : ∀ᶠ r : ℕ in atTop, ∀ m, A r m → m ≤ r)
    (h : ∀ ε > 0, ∀ᶠ r : ℕ in atTop, ∀ m, A r m →
      Real.log (Dhyb (I r m) r m) ≤ (Λ + ε) * (r : ℝ) ^ 2) :
    Mem2ContentA Fr A Λ := by
  refine mem2ContentF_of_top I A ?_
  intro ε hε
  filter_upwards [h (ε / 2) (by positivity), topC_sum_fam I B (ε := ε / 2) (by positivity), hA]
    with r h1 h2 h3 m hm
  have hT : DefHypT (I r m) r m (tropExp (I r m) r m) (fun _ => 0) :=
    defHypT_of_local (I := I r m) (r := r) (m := m) _ _ (fun p _ _ => le_rfl) (fun _ => False)
      (fun _ _ => rfl) (fun p _ _ hS => absurd hS id)
  refine ⟨tropExp (I r m) r m, fun _ => 0,
    defHypTop_of_local (I := I r m) (r := r) (m := m) _ _ (fun p _ _ => le_rfl) (fun _ => False)
      (fun _ _ => rfl) (fun p _ _ hS => absurd hS id), ?_⟩
  rw [log_DhybTop (I r m) r m hT, log_DhybT (I r m) r m hT, ← log_Dhyb]
  have := h1 m hm
  have := h2 m (h3 m hm)
  simp only [Nat.cast_zero, zero_mul, Finset.sum_const_zero, sub_zero]
  nlinarith

end CatalanFrames.HybCommon
