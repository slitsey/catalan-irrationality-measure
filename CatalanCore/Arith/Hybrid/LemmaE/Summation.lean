module

public import CatalanCore.Arith.Hybrid.Deficit
public import CatalanCore.Arith.Hybrid.PieceSum

@[expose] public section

/-!
# The deficit sum (generic; reusable by Lemma E, B, C5, C7, GK)

A deficit family `δ` with `δ p = m` on a clean set contributes `m · ∑_{p clean} log p` to the
saving `∑ δ p log p` of `log DhybD δ` (`log_DhybD`).  Two lemmas:

* `clsSum_ge` (lower prime sum): eventually in `r`, `∑_{s r < p ≤ t r, p ≡ c (M)} log p ≥
  ((t-s)/φ(M) - ε) r`.  Only `theta_interval_abs_le` is used.
* `cleanSum_ge` : if `clean` contains every prime of the window and class **except those in a
  finite exception set `Exc`** (e.g. the single band-boundary prime `5p ∈ {4r-1, 4r}` of class 3,
  which is not clean), then
  `∑_{p < Bnd, prime} cleanDef m clean p · log p ≥ m (((t-s)/φ(M) - ε) r - |Exc| log r)`.
  With `|Exc| = O(1)` the exception costs `O(r log r) = o(r²)` after multiplying by `m ≤ r`.
  Several windows/classes add, since `cleanDef` is a function of a single `clean` predicate.
-/

open Finset Filter Topology CatalanCore.NT

namespace CatalanCore.Arith.Hybrid

variable {M : ℕ}

lemma clsSum_ge [NeZero M] {c : ZMod M} (hc : IsUnit c) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop,
      ((t - s) / (M.totient : ℝ) - ε) * r ≤ clsSum M c (fun _ => 1) ⌊s * r⌋₊ ⌊t * r⌋₊ := by
  have h := theta_interval_abs_le hc hs hst hε
  have h2 : ∀ᶠ r : ℕ in atTop, _ := tendsto_natCast_atTop_atTop.eventually h
  filter_upwards [h2] with r hr
  have hle : ⌊s * r⌋₊ ≤ ⌊t * r⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_right hst (Nat.cast_nonneg r))
  have e : clsSum M c (fun _ => 1) ⌊s * r⌋₊ ⌊t * r⌋₊ =
      thetaClass M c (t * r) - thetaClass M c (s * r) := by
    unfold clsSum thetaClass
    rw [thetaClassN_sub M c hle]
    simp
  rw [e]
  have := (abs_le.mp hr).1
  linarith

/-- The sum of `δ p log p` over primes below `Bnd` for `δ = cleanDef m clean`. -/
lemma cleanSum_ge [NeZero M] {c : ZMod M} (hc : IsUnit c) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (ht : t ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ {Fr : Frame} (I : HybInst Fr) (m : ℕ) (clean : ℕ → Prop)
      (Exc : Finset ℕ),
      (∀ p, ⌊s * r⌋₊ < p → p ≤ ⌊t * r⌋₊ → p.Prime → (p : ZMod M) = c → p ∉ Exc → clean p) →
      (m : ℝ) * (((t - s) / (M.totient : ℝ) - ε) * r - Exc.card * Real.log r) ≤
        ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime,
          (cleanDef m clean p : ℝ) * Real.log p := by
  classical
  filter_upwards [clsSum_ge hc hs hst hε, eventually_ge_atTop 1] with r hr hr1 Fr I m clean Exc hcl
  set A := ⌊s * r⌋₊
  set B := ⌊t * r⌋₊
  have hBr : B ≤ r := by
    have : t * r ≤ r := by nlinarith [(Nat.cast_nonneg r : (0:ℝ) ≤ r)]
    exact Nat.floor_le_of_le (by simpa using this)
  have hBnd : r + 3 ≤ Bnd I r m := by
    have := I.cd.hL
    unfold Bnd
    nlinarith
  set S := (Ioc A B).filter (fun p : ℕ => p.Prime ∧ (p : ZMod M) = c) with hS
  set S' := S.filter (fun p => p ∉ Exc) with hS'
  -- the clean primes below Bnd contain S'
  have hsub : S' ⊆ (Finset.range (Bnd I r m)).filter Nat.Prime := by
    intro p hp
    simp only [hS', hS, Finset.mem_filter, Finset.mem_Ioc] at hp
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hp.1.2.1⟩
  have hlog0 : ∀ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, 0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
  have hcl' : ∀ p ∈ S', cleanDef m clean p = m := by
    intro p hp
    simp only [hS', hS, Finset.mem_filter, Finset.mem_Ioc] at hp
    simp [cleanDef, hcl p hp.1.1.1 hp.1.1.2 hp.1.2.1 hp.1.2.2 hp.2]
  have h1 : ∑ p ∈ S', (m : ℝ) * Real.log p ≤
      ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, (cleanDef m clean p : ℝ) * Real.log p := by
    calc ∑ p ∈ S', (m : ℝ) * Real.log p = ∑ p ∈ S', (cleanDef m clean p : ℝ) * Real.log p := by
          refine Finset.sum_congr rfl fun p hp => ?_
          rw [hcl' p hp]
      _ ≤ _ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro p hp _
          exact mul_nonneg (Nat.cast_nonneg _) (hlog0 p hp)
  -- S' loses at most Exc.card logs
  have hS0 : clsSum M c (fun _ => 1) A B = ∑ p ∈ S, Real.log p := by
    unfold clsSum; simp [hS]
  have hsplit : ∑ p ∈ S', Real.log p + ∑ p ∈ S.filter (fun p => p ∈ Exc), Real.log p =
      ∑ p ∈ S, Real.log p :=
    Finset.sum_filter_not_add_sum_filter S (fun p => p ∈ Exc) (fun p => Real.log p)
  have hexc : ∑ p ∈ S.filter (fun p => p ∈ Exc), Real.log p ≤ Exc.card * Real.log r := by
    have hb : ∀ p ∈ S.filter (fun p => p ∈ Exc), Real.log p ≤ Real.log r := by
      intro p hp
      simp only [hS, Finset.mem_filter, Finset.mem_Ioc] at hp
      exact Real.log_le_log (by exact_mod_cast hp.1.2.1.pos) (by exact_mod_cast hp.1.1.2.trans hBr)
    calc _ ≤ (S.filter (fun p => p ∈ Exc)).card • Real.log r := Finset.sum_le_card_nsmul _ _ _ hb
      _ ≤ Exc.card • Real.log r := by
          have := Finset.card_le_card (s := S.filter (fun p => p ∈ Exc)) (t := Exc)
            (fun p hp => (Finset.mem_filter.mp hp).2)
          exact smul_le_smul_of_nonneg_right this
            (Real.log_nonneg (by exact_mod_cast hr1))
      _ = _ := by simp
  rw [hS0] at hr
  have h2 : ((t - s) / (M.totient : ℝ) - ε) * r - Exc.card * Real.log r ≤ ∑ p ∈ S', Real.log p := by
    linarith
  calc (m : ℝ) * (((t - s) / (M.totient : ℝ) - ε) * r - Exc.card * Real.log r)
      ≤ (m : ℝ) * ∑ p ∈ S', Real.log p := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg m)
    _ = ∑ p ∈ S', (m : ℝ) * Real.log p := by rw [Finset.mul_sum]
    _ ≤ _ := h1

/-- `log DhybD δ = log Dhyb - ∑ δ p log p`. -/
theorem log_DhybD_eq_sub {Fr : Frame} (I : HybInst Fr) (r m : ℕ) {δ : ℕ → ℕ}
    (hδ : DefHyp I r m δ) :
    Real.log (DhybD I r m δ) = Real.log (Dhyb I r m) -
      ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, (δ p : ℝ) * Real.log p := by
  rw [log_DhybD I r m hδ, log_Dhyb]

end CatalanCore.Arith.Hybrid
