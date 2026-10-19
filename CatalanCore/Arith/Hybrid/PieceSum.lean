module

public import CatalanCore.NT.Interval
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-!
# Upper Riemann sums for prime sums over a linear piece

`clsSum M c w A B = ∑_{A < p ≤ B, p prime, p ≡ c (M)} w p · log p`.

`piece_sum` : if `w p ≤ α r + β p + C` for the primes of class `c` with `s r < p ≤ t r`, and the
linear function `α + β θ` is `≥ 0` at `s, t`, then eventually in `r`
`clsSum M c w ⌊s r⌋ ⌊t r⌋ ≤ r² (∫_s^t (α + β θ) dθ / φ(M) + ε)`.
Only the two-sided PNT on intervals (`theta_interval_abs_le`) is used; the modulus `M` is a
parameter (λ: `M = 4`; P6: `M = 6`).
-/

open Finset Filter Topology CatalanCore.NT

namespace CatalanCore.Arith.Hybrid

/-- Weighted prime sum over a window and a class mod `M`. -/
noncomputable def clsSum (M : ℕ) (c : ZMod M) (w : ℕ → ℝ) (A B : ℕ) : ℝ :=
  ∑ p ∈ (Ioc A B).filter (fun p : ℕ => p.Prime ∧ (p : ZMod M) = c), w p * Real.log p

variable {M : ℕ}

lemma clsSum_eq (c : ZMod M) (w : ℕ → ℝ) (A B : ℕ) :
    clsSum M c w A B = ∑ p ∈ Ioc A B, if p.Prime ∧ (p : ZMod M) = c then w p * Real.log p else 0 := by
  unfold clsSum; rw [Finset.sum_filter]

lemma clsSum_add (c : ZMod M) (w : ℕ → ℝ) {A B D : ℕ} (h1 : A ≤ B) (h2 : B ≤ D) :
    clsSum M c w A B + clsSum M c w B D = clsSum M c w A D := by
  simp only [clsSum_eq]
  exact Finset.sum_Ioc_consecutive _ h1 h2

lemma clsSum_chain (c : ZMod M) (w : ℕ → ℝ) (A : ℕ → ℕ) (hA : Monotone A) (n : ℕ) :
    clsSum M c w (A 0) (A n) = ∑ i ∈ range n, clsSum M c w (A i) (A (i + 1)) := by
  induction n with
  | zero => simp [clsSum]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, clsSum_add c w (hA (Nat.zero_le k)) (hA (Nat.le_succ k))]

lemma clsSum_le_cell (c : ZMod M) (w : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) {K : ℝ}
    (h : ∀ p, A < p → p ≤ B → p.Prime → (p : ZMod M) = c → w p ≤ K) :
    clsSum M c w A B ≤ K * (thetaClassN M c B - thetaClassN M c A) := by
  rw [thetaClassN_sub M c hAB, Finset.mul_sum]
  unfold clsSum
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hp1, hp2, hp3⟩ := by simpa using hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp2.one_lt.le)
  exact mul_le_mul_of_nonneg_right (h p hp1.1 hp1.2 hp2 hp3) hlog

/-- Midpoint sum of a linear function over a uniform grid. -/
lemma mid_sum (α β s t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ range n, (α + β * (s + ((i : ℝ) + 1 / 2) * ((t - s) / n)) + |β| * ((t - s) / n) / 2) *
        ((t - s) / n) =
      α * (t - s) + β * (t ^ 2 - s ^ 2) / 2 + |β| * (t - s) * ((t - s) / n) / 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have key : ∀ k : ℕ, ∑ i ∈ range k, ((i : ℝ) + 1 / 2) = (k : ℝ) ^ 2 / 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  have e : ∀ i : ℕ, (α + β * (s + ((i : ℝ) + 1 / 2) * ((t - s) / n)) + |β| * ((t - s) / n) / 2) *
        ((t - s) / n) = (α + β * s + |β| * ((t - s) / n) / 2) * ((t - s) / n) +
          β * ((t - s) / n) ^ 2 * ((i : ℝ) + 1 / 2) := by
    intro i; ring
  simp_rw [e]
  have h2 : ∑ x ∈ range n, β * ((t - s) / n) ^ 2 * ((x : ℝ) + 1 / 2) =
      β * ((t - s) / n) ^ 2 * ((n : ℝ) ^ 2 / 2) := by
    rw [← Finset.mul_sum, key]
  rw [Finset.sum_add_distrib, h2]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring


/-- Grid points. -/
noncomputable def gridPt (s t : ℝ) (n i : ℕ) : ℝ := s + (i : ℝ) * ((t - s) / n)

/-- Cell constants (midpoint value plus slope error). -/
noncomputable def cellC (α β s t : ℝ) (n i : ℕ) : ℝ :=
  α + β * (s + ((i : ℝ) + 1 / 2) * ((t - s) / n)) + |β| * ((t - s) / n) / 2

lemma cellC_nonneg {α β s t : ℝ} (hlt : s ≤ t) (h0 : 0 ≤ α + β * s) (h1 : 0 ≤ α + β * t)
    {n : ℕ} (hn : 1 ≤ n) {i : ℕ} (hi : i < n) : 0 ≤ cellC α β s t n i := by
  unfold cellC
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : 0 ≤ (t - s) / n := div_nonneg (by linarith) hn0.le
  have hi' : ((i : ℝ) + 1) ≤ n := by exact_mod_cast hi
  have hm1 : s ≤ s + ((i : ℝ) + 1 / 2) * ((t - s) / n) := by
    have : 0 ≤ ((i : ℝ) + 1 / 2) * ((t - s) / n) := by positivity
    linarith
  have hm2 : s + ((i : ℝ) + 1 / 2) * ((t - s) / n) ≤ t := by
    have : ((i : ℝ) + 1 / 2) * ((t - s) / n) ≤ (n : ℝ) * ((t - s) / n) :=
      mul_le_mul_of_nonneg_right (by linarith) hh
    have e : (n : ℝ) * ((t - s) / n) = t - s := by field_simp
    linarith
  have habs : 0 ≤ |β| * ((t - s) / n) / 2 := by positivity
  rcases le_total 0 β with hb | hb
  · nlinarith
  · nlinarith

/-- Pointwise bound inside cell `i`. -/
lemma cell_pt_bound {α β s t C : ℝ} {n : ℕ} {i : ℕ} {x y : ℝ}
    (hx : gridPt s t n i * x < y) (hy : y ≤ gridPt s t n (i + 1) * x) (hx0 : 0 ≤ x) :
    α * x + β * y + C ≤ x * cellC α β s t n i + C := by
  unfold gridPt at hx hy
  unfold cellC
  have hm : y - (s + ((i : ℝ) + 1 / 2) * ((t - s) / n)) * x ≤ x * ((t - s) / n) / 2 := by
    push_cast at hy; nlinarith
  have hm' : -(x * ((t - s) / n) / 2) ≤ y - (s + ((i : ℝ) + 1 / 2) * ((t - s) / n)) * x := by
    nlinarith
  have habs : |y - (s + ((i : ℝ) + 1 / 2) * ((t - s) / n)) * x| ≤ x * ((t - s) / n) / 2 :=
    abs_le.mpr ⟨hm', hm⟩
  have : β * (y - (s + ((i : ℝ) + 1 / 2) * ((t - s) / n)) * x) ≤
      |β| * (x * ((t - s) / n) / 2) := by
    calc _ ≤ |β * (y - (s + ((i : ℝ) + 1 / 2) * ((t - s) / n)) * x)| := le_abs_self _
      _ = |β| * |y - (s + ((i : ℝ) + 1 / 2) * ((t - s) / n)) * x| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  nlinarith


lemma gridPt_mono {s t : ℝ} (hlt : s ≤ t) (n : ℕ) : Monotone (gridPt s t n) := by
  intro i j hij
  unfold gridPt
  have : 0 ≤ (t - s) / n := div_nonneg (by linarith) (Nat.cast_nonneg n)
  have : (i : ℝ) ≤ j := by exact_mod_cast hij
  nlinarith

lemma gridPt_zero (s t : ℝ) (n : ℕ) : gridPt s t n 0 = s := by simp [gridPt]

lemma gridPt_last (s t : ℝ) {n : ℕ} (hn : 1 ≤ n) : gridPt s t n n = t := by
  unfold gridPt
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma gridPt_nonneg {s t : ℝ} (hs : 0 < s) (hlt : s ≤ t) (n i : ℕ) : 0 ≤ gridPt s t n i := by
  have := gridPt_mono hlt n (Nat.zero_le i)
  rw [gridPt_zero] at this
  linarith

lemma piece_core (c : ZMod M) (w : ℕ → ℝ) {s t α β C : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hs : 0 < s) (hlt : s ≤ t) (h0 : 0 ≤ α + β * s) (h1 : 0 ≤ α + β * t) (hC : 0 ≤ C) {r : ℕ}
    (hw : ∀ p, ⌊s * r⌋₊ < p → p ≤ ⌊t * r⌋₊ → p.Prime → (p : ZMod M) = c →
      w p ≤ α * r + β * p + C)
    {D : ℝ}
    (hθ : ∀ i < n, thetaClassN M c ⌊gridPt s t n (i + 1) * r⌋₊ -
        thetaClassN M c ⌊gridPt s t n i * r⌋₊ ≤ D) :
    clsSum M c w ⌊s * r⌋₊ ⌊t * r⌋₊ ≤ ∑ i ∈ range n, ((r : ℝ) * cellC α β s t n i + C) * D := by
  set A : ℕ → ℕ := fun i => ⌊gridPt s t n i * r⌋₊ with hA
  have hAmono : Monotone A := fun i j hij =>
    Nat.floor_le_floor (mul_le_mul_of_nonneg_right (gridPt_mono hlt n hij) (Nat.cast_nonneg r))
  have hA0 : A 0 = ⌊s * r⌋₊ := by simp [hA, gridPt_zero]
  have hAn : A n = ⌊t * r⌋₊ := by simp [hA, gridPt_last s t hn]
  rw [← hA0, ← hAn, clsSum_chain c w A hAmono n]
  apply Finset.sum_le_sum
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hK : 0 ≤ (r : ℝ) * cellC α β s t n i + C :=
    add_nonneg (mul_nonneg hr (cellC_nonneg hlt h0 h1 hn hi')) hC
  refine (clsSum_le_cell c w (hAmono (Nat.le_succ i)) (K := (r : ℝ) * cellC α β s t n i + C)
    ?_).trans (mul_le_mul_of_nonneg_left (hθ i hi') hK)
  intro p hp1 hp2 hpp hpc
  have hlo : ⌊s * r⌋₊ < p := lt_of_le_of_lt (hA0 ▸ hAmono (Nat.zero_le i)) hp1
  have hhi : p ≤ ⌊t * r⌋₊ := le_trans hp2 (hAn ▸ hAmono (Nat.succ_le_of_lt hi'))
  have hb := hw p hlo hhi hpp hpc
  have g0 := gridPt_nonneg hs hlt n i
  have g1 := gridPt_nonneg hs hlt n (i + 1)
  have hx : gridPt s t n i * r < p := (Nat.floor_lt (mul_nonneg g0 hr)).mp hp1
  have hy : (p : ℝ) ≤ gridPt s t n (i + 1) * r := (Nat.le_floor_iff (mul_nonneg g1 hr)).mp hp2
  exact hb.trans (cell_pt_bound hx hy hr)


lemma cellC_le {α β s t : ℝ} (hs : 0 < s) (hlt : s ≤ t) {n : ℕ} (hn : 1 ≤ n) {i : ℕ} (hi : i < n) :
    cellC α β s t n i ≤ |α| + |β| * t + |β| * (t - s) := by
  unfold cellC
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : 0 ≤ (t - s) / n := div_nonneg (by linarith) hn0.le
  have hi' : ((i : ℝ) + 1) ≤ n := by exact_mod_cast hi
  have hm1 : 0 ≤ s + ((i : ℝ) + 1 / 2) * ((t - s) / n) := by
    have : 0 ≤ ((i : ℝ) + 1 / 2) * ((t - s) / n) := by positivity
    linarith
  have hm2 : s + ((i : ℝ) + 1 / 2) * ((t - s) / n) ≤ t := by
    have : ((i : ℝ) + 1 / 2) * ((t - s) / n) ≤ (n : ℝ) * ((t - s) / n) :=
      mul_le_mul_of_nonneg_right (by linarith) hh
    have e : (n : ℝ) * ((t - s) / n) = t - s := by field_simp
    linarith
  have hh2 : (t - s) / n ≤ t - s := by
    rw [div_le_iff₀ hn0]
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [show 0 ≤ t - s by linarith]
  have h1 : β * (s + ((i : ℝ) + 1 / 2) * ((t - s) / n)) ≤ |β| * t := by
    calc _ ≤ |β * (s + ((i : ℝ) + 1 / 2) * ((t - s) / n))| := le_abs_self _
      _ = |β| * (s + ((i : ℝ) + 1 / 2) * ((t - s) / n)) := by
        rw [abs_mul, abs_of_nonneg hm1]
      _ ≤ |β| * t := mul_le_mul_of_nonneg_left hm2 (abs_nonneg _)
  have h2 : |β| * ((t - s) / n) / 2 ≤ |β| * (t - s) := by
    have : |β| * ((t - s) / n) ≤ |β| * (t - s) := mul_le_mul_of_nonneg_left hh2 (abs_nonneg _)
    have := abs_nonneg β
    nlinarith [mul_nonneg this hh]
  have := le_abs_self α
  linarith

theorem piece_sum {M : ℕ} [NeZero M] {c : ZMod M} (hc : IsUnit c) {s t α β C : ℝ}
    (hs : 0 < s) (hst : s ≤ t) (hC : 0 ≤ C) (h0 : 0 ≤ α + β * s) (h1 : 0 ≤ α + β * t)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ w : ℕ → ℝ,
      (∀ p, ⌊s * r⌋₊ < p → p ≤ ⌊t * r⌋₊ → p.Prime → (p : ZMod M) = c →
        w p ≤ α * r + β * p + C) →
      clsSum M c w ⌊s * r⌋₊ ⌊t * r⌋₊ ≤
        (r : ℝ) ^ 2 * ((α * (t - s) + β * (t ^ 2 - s ^ 2) / 2) / (M.totient : ℝ) + ε) := by
  have hφ : (0 : ℝ) < (M.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  set φ : ℝ := (M.totient : ℝ) with hφdef
  rcases eq_or_lt_of_le hst with hEq | hlt
  · subst hEq
    filter_upwards [eventually_ge_atTop 0] with r _ w _
    have : clsSum M c w ⌊s * r⌋₊ ⌊s * r⌋₊ = 0 := by simp [clsSum]
    rw [this]
    have : 0 ≤ (r : ℝ) ^ 2 * ((α * (s - s) + β * (s ^ 2 - s ^ 2) / 2) / φ + ε) := by
      simp only [sub_self, mul_zero, zero_div, zero_add]
      positivity
    exact this
  · obtain ⟨n0, hn0⟩ := exists_nat_gt (2 * |β| * (t - s) ^ 2 / (φ * ε))
    set n : ℕ := n0 + 1 with hndef
    have hn1 : 1 ≤ n := Nat.le_add_left 1 n0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnX : 2 * |β| * (t - s) ^ 2 / (φ * ε) < n := by
      have : (n0 : ℝ) ≤ n := by simp [hndef]
      linarith
    set h : ℝ := (t - s) / n with hh
    have hhpos : 0 < h := div_pos (by linarith) hnpos
    set K0 : ℝ := |α| + |β| * t + |β| * (t - s) with hK0
    have hK0nn : 0 ≤ K0 := add_nonneg (add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (by linarith))) (mul_nonneg (abs_nonneg _) (by linarith))
    set ε' : ℝ := ε / (4 * (n * K0 + 1)) with hε'
    have hε'pos : 0 < ε' := by positivity
    -- PNT on each cell, uniformly
    have hall : ∀ i ∈ Finset.range n, ∀ᶠ N : ℝ in atTop,
        |thetaClass M c (gridPt s t n (i + 1) * N) - thetaClass M c (gridPt s t n i * N) -
          (gridPt s t n (i + 1) - gridPt s t n i) / φ * N| ≤ ε' * N := by
      intro i hi
      have ha : 0 < gridPt s t n i := by
        have := gridPt_mono hst n (Nat.zero_le i)
        rw [gridPt_zero] at this; linarith
      exact theta_interval_abs_le hc ha (gridPt_mono hst n (Nat.le_succ i)) hε'pos
    have hall' := (Filter.eventually_all_finset (Finset.range n)).2 hall
    have hallr := tendsto_natCast_atTop_atTop.eventually hall'
    have hcb : ∀ᶠ r : ℕ in atTop, (n : ℝ) * C * (h / φ + ε') * r ≤ ε / 4 * (r : ℝ) ^ 2 := by
      obtain ⟨R, hR⟩ := exists_nat_ge (4 * (n * C * (h / φ + ε')) / ε)
      filter_upwards [eventually_ge_atTop R, eventually_ge_atTop 1] with r hr hr1
      have hr' : (R : ℝ) ≤ r := by exact_mod_cast hr
      have hr1' : (1 : ℝ) ≤ r := by exact_mod_cast hr1
      have hpos : 0 ≤ (n : ℝ) * C * (h / φ + ε') := by positivity
      have : 4 * ((n : ℝ) * C * (h / φ + ε')) / ε ≤ r := hR.trans hr'
      rw [div_le_iff₀ hε] at this
      nlinarith
    filter_upwards [hallr, hcb] with r hr hcbr w hw
    have hθ : ∀ i < n, thetaClassN M c ⌊gridPt s t n (i + 1) * r⌋₊ -
        thetaClassN M c ⌊gridPt s t n i * r⌋₊ ≤ (h / φ + ε') * r := by
      intro i hi
      have := hr i (Finset.mem_range.mpr hi)
      have hd : gridPt s t n (i + 1) - gridPt s t n i = h := by
        unfold gridPt; push_cast; rw [hh]; ring
      rw [hd] at this
      have := (abs_le.mp this).2
      show thetaClass M c _ - thetaClass M c _ ≤ _
      linarith
    have hcore := piece_core c w hn1 hs hst h0 h1 hC hw hθ
    refine hcore.trans ?_
    -- algebra
    have hsum : ∑ i ∈ range n, cellC α β s t n i * h =
        α * (t - s) + β * (t ^ 2 - s ^ 2) / 2 + |β| * (t - s) * h / 2 := by
      have := mid_sum α β s t n hn1
      simpa [cellC, hh] using this
    have hsumc : ∑ i ∈ range n, cellC α β s t n i =
        (α * (t - s) + β * (t ^ 2 - s ^ 2) / 2 + |β| * (t - s) * h / 2) / h := by
      rw [eq_div_iff hhpos.ne', ← hsum, Finset.sum_mul]
    have hcle : ∑ i ∈ range n, cellC α β s t n i ≤ n * K0 := by
      calc _ ≤ ∑ _i ∈ range n, K0 := Finset.sum_le_sum fun i hi =>
            cellC_le hs hst hn1 (Finset.mem_range.mp hi)
        _ = n * K0 := by simp
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have e1 : ∑ i ∈ range n, ((r : ℝ) * cellC α β s t n i + C) * ((h / φ + ε') * r) =
        (r : ℝ) ^ 2 * (h / φ + ε') * ∑ i ∈ range n, cellC α β s t n i +
          n * C * (h / φ + ε') * r := by
      rw [← Finset.sum_mul] at *
      simp only [add_mul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    rw [e1]
    -- bound the pieces
    have hJ : (r : ℝ) ^ 2 * (h / φ) * ∑ i ∈ range n, cellC α β s t n i =
        (r : ℝ) ^ 2 * ((α * (t - s) + β * (t ^ 2 - s ^ 2) / 2 + |β| * (t - s) * h / 2) / φ) := by
      rw [hsumc]; field_simp
    have herr : |β| * (t - s) * h / 2 / φ ≤ ε / 4 := by
      rw [div_le_iff₀ hφ, hh]
      have hX : 2 * |β| * (t - s) ^ 2 / (φ * ε) < n := hnX
      rw [div_lt_iff₀ (by positivity)] at hX
      have : |β| * (t - s) * ((t - s) / n) / 2 = |β| * (t - s) ^ 2 / (2 * n) := by
        field_simp
      rw [this, div_le_iff₀ (by positivity)]
      nlinarith
    have hε1 : (r : ℝ) ^ 2 * ε' * ∑ i ∈ range n, cellC α β s t n i ≤ (r : ℝ) ^ 2 * (ε / 4) := by
      have hl : ε' * ∑ i ∈ range n, cellC α β s t n i ≤ ε / 4 := by
        calc _ ≤ ε' * (n * K0) := mul_le_mul_of_nonneg_left hcle hε'pos.le
          _ = ε * (n * K0) / (4 * (n * K0 + 1)) := by rw [hε']; ring
          _ ≤ ε / 4 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [mul_nonneg hnpos.le hK0nn]
      calc _ = (r : ℝ) ^ 2 * (ε' * ∑ i ∈ range n, cellC α β s t n i) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
    have hsplit : (r : ℝ) ^ 2 * (h / φ + ε') * ∑ i ∈ range n, cellC α β s t n i =
        (r : ℝ) ^ 2 * (h / φ) * ∑ i ∈ range n, cellC α β s t n i +
          (r : ℝ) ^ 2 * ε' * ∑ i ∈ range n, cellC α β s t n i := by ring
    rw [hsplit, hJ]
    have hfin : (r : ℝ) ^ 2 * ((α * (t - s) + β * (t ^ 2 - s ^ 2) / 2 + |β| * (t - s) * h / 2) / φ)
        = (r : ℝ) ^ 2 * ((α * (t - s) + β * (t ^ 2 - s ^ 2) / 2) / φ) +
          (r : ℝ) ^ 2 * (|β| * (t - s) * h / 2 / φ) := by
      ring
    rw [hfin]
    have h2 : (r : ℝ) ^ 2 * (|β| * (t - s) * h / 2 / φ) ≤ (r : ℝ) ^ 2 * (ε / 4) :=
      mul_le_mul_of_nonneg_left herr (by positivity)
    have hrε : 0 ≤ (r : ℝ) ^ 2 * ε := by positivity
    linarith [hcbr, hε1, h2, hrε]

end CatalanCore.Arith.Hybrid
