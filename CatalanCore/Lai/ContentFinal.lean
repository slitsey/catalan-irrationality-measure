module

public import CatalanCore.Lai.ContentL12
public import CatalanCore.Lai.ClassCount
public import CatalanCore.Lai.ContentPrimes
public import CatalanCore.Lai.Family
public import CatalanCore.Lai.ContentTables
public import CatalanCore.Uniform.Measure.NV0
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# `CatalanCore.Lai.ContentFinal`: the content limit of Lai's `J_n` (rows LC30 and LC40)

Paper: `N9-LAI-CONTENT-EXACT-2026-11-16.md` (Assembly, Theorem C01R); Lai, arXiv 2610.06838 (Lemma 5.1,
Lemma 5.4, Proposition 5.5).

**Signed normaliser (mismatch M10).**  The constant `28.68723663` is the constant of the signed rational
normaliser `m_n = ∏_{p ≤ 6n} p^{-w(n,p)}` (`signedDen`), where `w(n,p)` is the best proved lower bound of
`v_p(J_n)` (`laiW`); Lai's bound is positive on `(5.4n, 6n]`, which a natural-number denominator cannot use.
As for ζ(5) (`Zeta5/Criterion/Signed.lean`) the family is rescaled to `Q n = m n * J_n` (`scaleFam`): then
`den = 1`, `Λ' = 0` and the decay constant becomes `D - Λ`.

* `laiW`, `laiW_valid` : `GV p (laiW n p) (laiJ n)` for every prime `p` and `n ≥ 10`, from Theorem L2
  (`L2Stmt`), Theorem O (`thmO`, `3n < p ≤ 7n/2`), Lai Lemma 4.4 for `7n/2 < p ≤ 6n` (`Band7Stmt`),
  Lemma 4.1 (`lai_vp_lower`, `lai_vp_nonneg`);
* `window_le`, `band_main`, `band_O`, `band_7a/7b/7c`, `band_small` : Lai Lemma 5.1 (`weighted_prime_sum_approx_le`)
  on the windows: the 22 pieces of Theorem C01 on `(1/M, 3]` (`kset`, `c01_tiling`, `window_char`), the Theorem O
  band, the three bands of Lai's Lemma 5.4, and the primes `p ≤ n/M`;
* `sum_Icl` : the window integrals sum to `2263/280 + S_M` (`c01_cells_sum`, `c01_nodeF_eq`);
* `c01_partial_le` (LC27): `S_M ≤ 3573565641/700000000` from the prefix datum `S₁₀₀₀ ≤ Ŝ` and one rational
  comparison; the 12 positivity checks and the moment signs are proved here, not data;
  `partialS_le_of_grid` is the generic grid lemma for the prefix datum;
* `sum_signed_le`, `lai_content` (**LC30**): for every `ε > 0` and large `n`, `m_n J_n` is integral at every
  prime and `log m_n ≤ (28.68723663 + ε) n²`;
* `hasScaledContent_scale`, `hasScaledDecay_scale`, `lai_plane_hasScaledContent`, `lai_ratio_hasScaledContent`,
  `lai_plane_decay_scaled`, `lai_ratio_decay_scaled` (**LC40**).

Hypotheses (named, discharged in `CatalanCore.Lai.ContentCert`): `L2Stmt` (`lai_L2`, built), `Band7Stmt`
(Lai Lemma 4.4 at `q₆ = 1`), `BridgeStmt` (integer law versus the 22 affine pieces, `Lai.ContentBridge`), and the
W2 datum `(Ŝ, hS, hR)`.
-/


set_option linter.deprecated false

open Finset MvPolynomial CatalanCore.Basic CatalanCore.Content
open scoped Nat

namespace CatalanCore.Lai

section SignedDen

/-- the primes `p ≤ 6n`. -/
noncomputable def primes6 (n : ℕ) : Finset ℕ := (Finset.Ioc 0 (6 * n)).filter Nat.Prime

/-- the signed normaliser `∏_{p ≤ 6n} p^{-w n p}` (a positive rational). -/
noncomputable def signedDen (n : ℕ) (w : ℕ → ℕ → ℤ) : ℚ := ∏ p ∈ primes6 n, (p : ℚ) ^ (-(w n p))

lemma mem_primes6 {n p : ℕ} : p ∈ primes6 n ↔ p.Prime ∧ p ≤ 6 * n := by
  unfold primes6
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨_, h⟩, h2⟩; exact ⟨h2, h⟩
  · rintro ⟨h2, h⟩; exact ⟨⟨h2.pos, h⟩, h2⟩

theorem signedDen_pos (n : ℕ) (w : ℕ → ℕ → ℤ) : 0 < signedDen n w :=
  Finset.prod_pos fun p hp => zpow_pos (by exact_mod_cast (mem_primes6.1 hp).1.pos) _

lemma zpow_mem_loc {q p : ℕ} [Fact q.Prime] (hp : p.Prime) (hne : p ≠ q) (k : ℤ) :
    (p : ℚ) ^ k ∈ LocRing q := by
  have hn : ¬ q ∣ p := fun h => hne ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) hp).1 h).symm
  rcases k with k | k
  · have : ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ k := by push_cast; rfl
    simp only [Int.ofNat_eq_natCast, zpow_natCast]
    exact_mod_cast int_mem_locRing (ℓ := q) ((p : ℤ) ^ k)
  · have h1 : (p : ℚ) ^ (Int.negSucc k) = (((p ^ (k + 1) : ℕ) : ℚ))⁻¹ := by
      rw [zpow_negSucc]; push_cast; rfl
    rw [h1]
    exact inv_natCast_mem_locRing (fun h => hn ((Nat.Prime.dvd_of_dvd_pow (Fact.out : q.Prime) h)))

lemma prod_zpow_mem_loc {q : ℕ} [Fact q.Prime] (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ q)
    (k : ℕ → ℤ) : (∏ p ∈ S, (p : ℚ) ^ (k p)) ∈ LocRing q :=
  Subring.prod_mem _ fun p hp => zpow_mem_loc (hS p hp).1 (hS p hp).2 _

/-- `C (signedDen) * laiJ n` has Gauss valuation `≥ 0` at every prime, from the lower bounds `w`. -/
theorem GV_signedDen_mul (n : ℕ) (w : ℕ → ℕ → ℤ)
    (hw : ∀ p : ℕ, ∀ [Fact p.Prime], p ≤ 6 * n → GV p (w n p) (laiJ n))
    (q : ℕ) [Fact q.Prime] : GV q 0 (C (signedDen n w) * laiJ n) := by
  by_cases hq : q ≤ 6 * n
  · have hmem : q ∈ primes6 n := mem_primes6.2 ⟨Fact.out, hq⟩
    have hsplit : signedDen n w = (q : ℚ) ^ (-(w n q)) *
        ∏ p ∈ (primes6 n).erase q, (p : ℚ) ^ (-(w n p)) := by
      unfold signedDen
      exact (Finset.mul_prod_erase _ (fun p : ℕ => (p : ℚ) ^ (-(w n p))) hmem).symm
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    have h1 : GV q (-(w n q)) (C ((q : ℚ) ^ (-(w n q))) : MvPolynomial (Fin 3) ℚ) := by
      refine GV.const ?_
      rw [neg_neg, ← zpow_add₀ hq0]
      simp
    have h2 : GV q 0 (C (∏ p ∈ (primes6 n).erase q, (p : ℚ) ^ (-(w n p))) : MvPolynomial (Fin 3) ℚ) := by
      refine GV.const_loc (prod_zpow_mem_loc _ (fun p hp => ?_) _)
      have := Finset.mem_erase.1 hp
      exact ⟨(mem_primes6.1 this.2).1, this.1⟩
    have := (h1.mul h2).mul (hw q hq)
    have key := this.mono (show (0 : ℤ) ≤ -(w n q) + 0 + w n q by omega)
    rw [hsplit, map_mul]
    exact key
  · push_neg at hq
    have h2 : GV q 0 (C (signedDen n w) : MvPolynomial (Fin 3) ℚ) := by
      refine GV.const_loc (prod_zpow_mem_loc _ (fun p hp => ?_) _)
      have := (mem_primes6.1 hp)
      exact ⟨this.1, by omega⟩
    have := h2.mul (lai_vp_nonneg (n := n) hq)
    simpa using this

theorem signedDen_int (n : ℕ) (w : ℕ → ℕ → ℤ)
    (hw : ∀ p : ℕ, ∀ [Fact p.Prime], p ≤ 6 * n → GV p (w n p) (laiJ n))
    (v : Fin 3 → ℤ) :
    ∃ z : ℤ, signedDen n w * MvPolynomial.eval (fun i => (v i : ℚ)) (laiJ n) = z := by
  have := int_eval_of_forall_GV (f := C (signedDen n w) * laiJ n)
    (fun q _ => GV_signedDen_mul n w hw q) v
  simpa using this

theorem log_signedDen (n : ℕ) (w : ℕ → ℕ → ℤ) :
    Real.log ((signedDen n w : ℚ) : ℝ) = -∑ p ∈ primes6 n, (w n p : ℝ) * Real.log (p : ℝ) := by
  unfold signedDen
  push_cast
  rw [Real.log_prod]
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Real.log_zpow]; push_cast; ring
  · intro p hp
    exact (zpow_pos (by exact_mod_cast (mem_primes6.1 hp).1.pos) _).ne'

end SignedDen


section Exponents

/-- the law's lower bound `Σ pot2 - ν_p + x₁ + x₂` (Theorems L1, L2). -/
noncomputable def Wlaw (n p : ℕ) : ℤ :=
  ∑ x, pot2 n p x - (nuP n p : ℤ) + xone n p + xtwo n p

/-- crude bound of Lemma 4.1 (1). -/
noncomputable def crudeW (n p : ℕ) : ℤ := -((12 * n * Nat.log p (8 * n) : ℕ) : ℤ)

/-- Lai's Lemma 4.4 bound for `7n/2 < p ≤ 6n` (Lai Lemma 5.4, Cases 2-4). -/
def w7 (n p : ℕ) : ℤ :=
  if p ≤ 4 * n then -(2 * (n : ℤ) + 2 * p)
  else if 2 * p ≤ 9 * n then -(18 * (n : ℤ)) + 2 * p - 2
  else -(54 * (n : ℤ)) + 10 * p - 10

open Classical in
/-- the signed exponent: the best proved lower bound of `v_p(J_n)`. -/
noncomputable def laiW (n p : ℕ) : ℤ :=
  if 6 * n < p then 0
  else if 7 * n < 2 * p then w7 n p
  else if 3 * n < p then -6 * ((p : ℤ) - 2 * n)
  else if Rng n p then max (Wlaw n p) (crudeW n p) else crudeW n p

/-- Theorem L2 (LC21), the statement J-main posts. -/
def L2Stmt : Prop := ∀ (n p : ℕ) [Fact p.Prime], Rng n p → GV p (Wlaw n p) (laiJ n)

/-- Lai Lemma 4.4 at `7n/2 < p ≤ 6n` (Lai Lemma 5.4 Cases 2-4). -/
def Band7Stmt : Prop :=
  ∀ (n p : ℕ) [Fact p.Prime], 10 ≤ n → 7 * n < 2 * p → p ≤ 6 * n → GV p (w7 n p) (laiJ n)

theorem laiW_ge_crude {n p : ℕ} (h : p ≤ 3 * n) : crudeW n p ≤ laiW n p := by
  classical
  unfold laiW
  by_cases h1 : 6 * n < p
  · omega
  by_cases h2 : 7 * n < 2 * p
  · omega
  by_cases h3 : 3 * n < p
  · omega
  rw [if_neg h1, if_neg h2, if_neg h3]
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

theorem laiW_ge_W {n p : ℕ} (hR : Rng n p) : Wlaw n p ≤ laiW n p := by
  classical
  have h3 := hR.h3
  unfold laiW
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hR]
  exact le_max_left _ _

theorem laiW_valid (hL2 : L2Stmt) (hB7 : Band7Stmt) {n p : ℕ} [hp : Fact p.Prime] (hn : 10 ≤ n) :
    GV p (laiW n p) (laiJ n) := by
  classical
  unfold laiW
  by_cases h1 : 6 * n < p
  · rw [if_pos h1]; exact lai_vp_nonneg h1
  rw [if_neg h1]
  by_cases h2 : 7 * n < 2 * p
  · rw [if_pos h2]; exact hB7 n p hn h2 (by omega)
  rw [if_neg h2]
  by_cases h3 : 3 * n < p
  · rw [if_pos h3]
    have := thmO (n := n) (p := p) (by omega) h3 (by omega)
    have e : (((p - 2 * n : ℕ)) : ℤ) = (p : ℤ) - 2 * n := by omega
    rw [e] at this
    exact this
  rw [if_neg h3]
  by_cases hR : Rng n p
  · rw [if_pos hR]
    rcases max_choice (Wlaw n p) (crudeW n p) with h | h
    · rw [h]; exact hL2 n p hR
    · rw [h]; exact lai_vp_lower n
  · rw [if_neg hR]; exact lai_vp_lower n

end Exponents

section Windows

open Filter Topology CatalanCore.NT.WeightedPrimeSum CatalanCore.Zeta5.Sum

theorem pc_affine {A B α β : ℝ} (h : α < β) :
    PiecewiseCont (fun y => A * y + B) (fun i => if i = 0 then α else β) 1 := by
  refine ⟨?_, ?_⟩
  · intro i hi
    have : i = 0 := by omega
    subst this
    simpa using h
  · intro i hi
    exact ⟨fun y => A * y + B, by fun_prop, fun x _ => rfl⟩

/-- One window, one-sided Lai Lemma 5.1 with an affine integrand, for large `n` only. -/
theorem window_le {α β A B E : ℝ} (hα : 0 < α) (hαβ : α < β) (hE : 0 ≤ E) (N0 : ℕ)
    (w : ℕ → ℕ → ℝ)
    (hw : ∀ n, N0 ≤ n → ∀ p ∈ primeWin α β n, w n p ≤ n * (A * ((p : ℝ) / n) + B) + E)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∑ p ∈ primeWin α β n, w n p * Real.log (p : ℝ) ≤
      ((∫ y in α..β, (A * y + B)) + ε) * (n : ℝ) ^ 2 := by
  classical
  let w' : ℕ → ℕ → ℝ := fun n p => if N0 ≤ n then w n p else n * (A * ((p : ℝ) / n) + B)
  have hE' : Tendsto (fun n : ℕ => E / (n : ℝ)) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat E
  have key := weighted_prime_sum_approx_le (F := fun y => A * y + B)
    (c := fun i => if i = 0 then α else β) (N := 1) (by simpa using hα) (pc_affine hαβ) w'
    (fun _ => E) (fun _ => hE) hE' (fun n p hp => by
      by_cases hn : N0 ≤ n
      · simp only [w', hn, if_true]
        exact hw n hn p (by simpa using hp)
      · simp only [w', hn, if_false]; linarith) hε
  filter_upwards [key, eventually_ge_atTop N0, eventually_gt_atTop 0] with n hn hN hpos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos
  simp only [Nat.zero_ne_one, if_true, if_false, one_ne_zero] at hn
  have e : ∑ p ∈ primeWin α β n, w' n p * Real.log (p : ℝ) = ∑ p ∈ primeWin α β n, w n p * Real.log (p : ℝ) :=
    Finset.sum_congr rfl fun p _ => by simp [w', hN]
  rw [e, div_le_iff₀ (by positivity)] at hn
  exact hn

theorem sum_primes6_split (δ : ℝ) (hδ : 0 < δ) (hδ3 : δ ≤ 3) (f : ℕ → ℝ) (n : ℕ) :
    ∑ p ∈ primes6 n, f p = ∑ p ∈ smallPrimes δ n, f p + ∑ p ∈ primeWin δ 3 n, f p +
      ∑ p ∈ primeWin 3 (7 / 2) n, f p + ∑ p ∈ primeWin (7 / 2) 4 n, f p +
      ∑ p ∈ primeWin 4 (9 / 2) n, f p + ∑ p ∈ primeWin (9 / 2) 6 n, f p := by
  classical
  have h6 : ⌊(6 : ℝ) * n⌋₊ = 6 * n := by
    rw [show (6 : ℝ) * n = ((6 * n : ℕ) : ℝ) by push_cast; ring]; exact Nat.floor_natCast _
  have hmono : ∀ x y : ℝ, 0 ≤ x → x ≤ y → ⌊x * n⌋₊ ≤ ⌊y * n⌋₊ := fun x y hx hxy =>
    Nat.floor_le_floor (mul_le_mul_of_nonneg_right hxy (Nat.cast_nonneg _))
  have a1 : ⌊δ * n⌋₊ ≤ ⌊(3 : ℝ) * n⌋₊ := hmono _ _ hδ.le hδ3
  have a2 : ⌊(3 : ℝ) * n⌋₊ ≤ ⌊(7 / 2 : ℝ) * n⌋₊ := hmono _ _ (by norm_num) (by norm_num)
  have a3 : ⌊(7 / 2 : ℝ) * n⌋₊ ≤ ⌊(4 : ℝ) * n⌋₊ := hmono _ _ (by norm_num) (by norm_num)
  have a4 : ⌊(4 : ℝ) * n⌋₊ ≤ ⌊(9 / 2 : ℝ) * n⌋₊ := hmono _ _ (by norm_num) (by norm_num)
  have a5 : ⌊(9 / 2 : ℝ) * n⌋₊ ≤ ⌊(6 : ℝ) * n⌋₊ := hmono _ _ (by norm_num) (by norm_num)
  have z0 : 0 ≤ ⌊δ * n⌋₊ := Nat.zero_le _
  unfold primes6 smallPrimes primeWin
  simp only [Finset.sum_filter, h6]
  rw [← Finset.sum_Ioc_consecutive _ z0 (a1.trans (a2.trans (a3.trans (a4.trans (a5.trans_eq h6))))),
    ← Finset.sum_Ioc_consecutive _ a1 (a2.trans (a3.trans (a4.trans (a5.trans_eq h6)))),
    ← Finset.sum_Ioc_consecutive _ a2 (a3.trans (a4.trans (a5.trans_eq h6))),
    ← Finset.sum_Ioc_consecutive _ a3 (a4.trans (a5.trans_eq h6)),
    ← Finset.sum_Ioc_consecutive _ a4 (a5.trans_eq h6)]
  ring


theorem integral_affine (A B a b : ℝ) :
    ∫ y in a..b, (A * y + B) = A * (b ^ 2 - a ^ 2) / 2 + B * (b - a) := by
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const_mul, integral_id]
  simp
  ring

theorem laiW_O {n p : ℕ} (h1 : 3 * n < p) (h2 : 2 * p ≤ 7 * n) :
    laiW n p = -6 * ((p : ℤ) - 2 * n) := by
  classical
  unfold laiW
  rw [if_neg (by omega), if_neg (by omega), if_pos h1]

theorem laiW_7 {n p : ℕ} (h1 : 7 * n < 2 * p) (h2 : p ≤ 6 * n) : laiW n p = w7 n p := by
  classical
  unfold laiW
  rw [if_neg (by omega), if_pos h1]

/-- the band `(3n, 7n/2]` (Theorem O): `(3, 7/2]` contributes `15/4`. -/
theorem band_O {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∑ p ∈ primeWin 3 (7 / 2) n, (-(laiW n p : ℝ)) * Real.log (p : ℝ) ≤
      (15 / 4 + ε) * (n : ℝ) ^ 2 := by
  have := window_le (α := 3) (β := 7 / 2) (A := 6) (B := -12) (E := 0) (by norm_num) (by norm_num)
    le_rfl 10 (fun n p => -(laiW n p : ℝ)) (fun n hn p hp => by
      have hm := (mem_primeWin (α := 3) (β := 7 / 2) (by norm_num) (by norm_num)).1 hp
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have h1 : 3 * n < p := by exact_mod_cast hm.1
      have h2 : 2 * p ≤ 7 * n := by
        have := hm.2.1; exact_mod_cast (by linarith : (2 * p : ℝ) ≤ 7 * n)
      rw [laiW_O h1 h2]
      push_cast
      field_simp
      ring_nf
      rfl) hε
  filter_upwards [this] with n hn
  convert hn using 2
  rw [integral_affine]; norm_num

theorem band_7a {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∑ p ∈ primeWin (7 / 2) 4 n, (-(laiW n p : ℝ)) * Real.log (p : ℝ) ≤
      (19 / 4 + ε) * (n : ℝ) ^ 2 := by
  have := window_le (α := 7 / 2) (β := 4) (A := 2) (B := 2) (E := 0) (by norm_num) (by norm_num)
    le_rfl 10 (fun n p => -(laiW n p : ℝ)) (fun n hn p hp => by
      have hm := (mem_primeWin (α := 7 / 2) (β := 4) (by norm_num) (by norm_num)).1 hp
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have h1 : 7 * n < 2 * p := by
        have := hm.1; exact_mod_cast (by linarith : (7 * n : ℝ) < 2 * p)
      have h2 : p ≤ 4 * n := by exact_mod_cast (by linarith [hm.2.1] : (p : ℝ) ≤ 4 * n)
      rw [laiW_7 h1 (by omega)]
      unfold w7
      rw [if_pos h2]
      push_cast
      field_simp
      ring_nf
      rfl) hε
  filter_upwards [this] with n hn
  convert hn using 2
  rw [integral_affine]; norm_num

theorem band_7b {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∑ p ∈ primeWin 4 (9 / 2) n, (-(laiW n p : ℝ)) * Real.log (p : ℝ) ≤
      (19 / 4 + ε) * (n : ℝ) ^ 2 := by
  have := window_le (α := 4) (β := 9 / 2) (A := -2) (B := 18) (E := 2) (by norm_num) (by norm_num)
    (by norm_num) 10 (fun n p => -(laiW n p : ℝ)) (fun n hn p hp => by
      have hm := (mem_primeWin (α := 4) (β := 9 / 2) (by norm_num) (by norm_num)).1 hp
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have h1 : 4 * n < p := by exact_mod_cast hm.1
      have h2 : 2 * p ≤ 9 * n := by
        have := hm.2.1; exact_mod_cast (by linarith : (2 * p : ℝ) ≤ 9 * n)
      rw [laiW_7 (by omega) (by omega)]
      unfold w7
      rw [if_neg (by omega), if_pos h2]
      push_cast
      field_simp
      ring_nf
      rfl) hε
  filter_upwards [this] with n hn
  convert hn using 2
  rw [integral_affine]; norm_num

theorem band_7c {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∑ p ∈ primeWin (9 / 2) 6 n, (-(laiW n p : ℝ)) * Real.log (p : ℝ) ≤
      (9 / 4 + ε) * (n : ℝ) ^ 2 := by
  have := window_le (α := 9 / 2) (β := 6) (A := -10) (B := 54) (E := 10) (by norm_num) (by norm_num)
    (by norm_num) 10 (fun n p => -(laiW n p : ℝ)) (fun n hn p hp => by
      have hm := (mem_primeWin (α := 9 / 2) (β := 6) (by norm_num) (by norm_num)).1 hp
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have h1 : 9 * n < 2 * p := by
        have := hm.1; exact_mod_cast (by linarith : (9 * n : ℝ) < 2 * p)
      have h2 : p ≤ 6 * n := by exact_mod_cast (by linarith [hm.2.1] : (p : ℝ) ≤ 6 * n)
      rw [laiW_7 (by omega) h2]
      unfold w7
      rw [if_neg (by omega), if_neg (by omega)]
      push_cast
      field_simp
      ring_nf
      rfl) hε
  filter_upwards [this] with n hn
  convert hn using 2
  rw [integral_affine]; norm_num

/-- the small primes `p ≤ δ n` (Lemma 4.1 (1)): at most `12 δ n²`. -/
theorem band_small {δ : ℝ} (hδ : 0 < δ) (hδ3 : δ ≤ 3) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∑ p ∈ smallPrimes δ n, (-(laiW n p : ℝ)) * Real.log (p : ℝ) ≤
      (12 * δ + ε) * (n : ℝ) ^ 2 := by
  refine small_primes_cost hδ (fun n p => -(laiW n p : ℝ)) (fun n p hp hpd => ?_) hε
  have h3 : p ≤ 3 * n := by
    have : (p : ℝ) ≤ 3 * n := hpd.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
    exact_mod_cast this
  have := laiW_ge_crude h3
  unfold crudeW at this
  have h' : ((-(12 * n * Nat.log p (8 * n) : ℕ) : ℤ) : ℝ) ≤ (laiW n p : ℝ) := by exact_mod_cast this
  push_cast at h'
  linarith


section Tiling

theorem c01_tiling (r : ℕ) (hr : r < 6) (t : ℝ) (h0 : 0 ≤ t) (h1 : t < 1) :
    ∃ j, j < 22 ∧ (c01Piece j).r = r ∧ (c01Piece j).lo ≤ t ∧ t < (c01Piece j).hi := by
  interval_cases r
  · by_cases a : t < 3 / 4
    · exact ⟨0, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    by_cases b : t < 6 / 7
    · exact ⟨1, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    · exact ⟨2, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
  · by_cases a : t < 1 / 2
    · exact ⟨3, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    by_cases b : t < 5 / 7
    · exact ⟨4, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    · exact ⟨5, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
  · by_cases a : t < 1 / 4
    · exact ⟨6, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    by_cases b : t < 2 / 5
    · exact ⟨7, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    by_cases c : t < 4 / 7
    · exact ⟨8, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    by_cases d : t < 2 / 3
    · exact ⟨9, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    · exact ⟨10, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
  · by_cases a : t < 1 / 3
    · exact ⟨11, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    by_cases b : t < 3 / 7
    · exact ⟨12, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    by_cases c : t < 3 / 5
    · exact ⟨13, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    by_cases d : t < 3 / 4
    · exact ⟨14, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    · exact ⟨15, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
  · by_cases a : t < 2 / 7
    · exact ⟨16, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    by_cases b : t < 1 / 2
    · exact ⟨17, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    · exact ⟨18, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
  · by_cases a : t < 1 / 7
    · exact ⟨19, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    by_cases b : t < 1 / 4
    · exact ⟨20, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩
    · exact ⟨21, by norm_num, by simp [c01Piece], by simp [c01Piece]; linarith, by simp [c01Piece]; linarith⟩

/-- first piece index of the residue `r`. -/
def rstart : ℕ → ℕ
  | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 11 | 4 => 16 | 5 => 19 | _ => 22

theorem c01_rstart {j : ℕ} (hj : j < 22) :
    rstart (c01Piece j).r ≤ j ∧ j < rstart ((c01Piece j).r + 1) := by
  interval_cases j <;> simp [c01Piece, rstart]

theorem c01_tiling_unique {j j' : ℕ} (hj : j < 22) (hj' : j' < 22)
    (hr : (c01Piece j).r = (c01Piece j').r) {t : ℝ}
    (h1 : (c01Piece j).lo ≤ t) (h2 : t < (c01Piece j).hi)
    (h1' : (c01Piece j').lo ≤ t) (h2' : t < (c01Piece j').hi) : j = j' := by
  have hr6 := (c01_piece_bounds j hj).2.2.2
  obtain ⟨hs, hs'⟩ := c01_rstart hj
  obtain ⟨hs2, hs2'⟩ := c01_rstart hj'
  rw [← hr] at hs2 hs2'
  have hcases : (c01Piece j).r = 0 ∨ (c01Piece j).r = 1 ∨ (c01Piece j).r = 2 ∨
      (c01Piece j).r = 3 ∨ (c01Piece j).r = 4 ∨ (c01Piece j).r = 5 := by omega
  rcases hcases with h | h | h | h | h | h <;> rw [h] at hs hs' hs2 hs2' <;>
    simp only [rstart] at hs hs' hs2 hs2' <;>
    interval_cases j <;> interval_cases j' <;> simp only [c01Piece] at h1 h2 h1' h2' ⊢ <;>
      first | rfl | (exfalso; linarith)

theorem c01_r_ge2 {j : ℕ} (hj : j < 22) (h6 : 6 ≤ j) : 2 ≤ (c01Piece j).r := by
  interval_cases j <;> simp [c01Piece]

theorem c01_j_ge6 {j : ℕ} (hj : j < 22) (h2 : 2 ≤ (c01Piece j).r) : 6 ≤ j := by
  interval_cases j <;> simp [c01Piece] at h2 ⊢

end Tiling

section KSet

theorem window_char {n p q : ℕ} {lo hi : ℝ} (hlo : 0 ≤ lo) (hlh : lo < hi) (hhi : hi ≤ 1)
    (hq : 0 < q) (hp : 0 < p) :
    p ∈ primeWin (6 / ((q : ℝ) + hi)) (6 / ((q : ℝ) + lo)) n ↔
      p.Prime ∧ q6 n p = q ∧ lo * (p : ℝ) ≤ (r6 n p : ℝ) ∧ (r6 n p : ℝ) < hi * (p : ℝ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hA : 0 < (q : ℝ) + lo := by linarith
  have hB : 0 < (q : ℝ) + hi := by linarith
  have hαβ : 6 / ((q : ℝ) + hi) ≤ 6 / ((q : ℝ) + lo) :=
    div_le_div_of_nonneg_left (by norm_num) hA (by linarith)
  rw [mem_primeWin (div_nonneg (by norm_num) hB.le) hαβ]
  have e1 : 6 / ((q : ℝ) + hi) * (n : ℝ) < p ↔ 6 * (n : ℝ) < (p : ℝ) * ((q : ℝ) + hi) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hB]
  have e2 : (p : ℝ) ≤ 6 / ((q : ℝ) + lo) * (n : ℝ) ↔ (p : ℝ) * ((q : ℝ) + lo) ≤ 6 * (n : ℝ) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hA]
  rw [e1, e2]
  have hqr := qr6 n p hp
  have hcast : (6 : ℝ) * n = (q6 n p : ℝ) * p + (r6 n p : ℝ) := by exact_mod_cast hqr
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hA' : q * p ≤ 6 * n := by
      have : (q : ℝ) * p ≤ 6 * n := by nlinarith [mul_nonneg hlo hp0.le]
      exact_mod_cast this
    have hB' : 6 * n < (q + 1) * p := by
      have : (6 : ℝ) * n < ((q : ℝ) + 1) * p := by nlinarith [mul_nonneg (sub_nonneg.2 hhi) hp0.le]
      exact_mod_cast this
    have hdiv : q6 n p = q := Nat.div_eq_of_lt_le hA' hB'
    refine ⟨h3, hdiv, ?_, ?_⟩
    · rw [hdiv] at hcast; nlinarith
    · rw [hdiv] at hcast; nlinarith
  · rintro ⟨h3, hdiv, h1, h2⟩
    rw [hdiv] at hcast
    exact ⟨by nlinarith, by nlinarith, h3⟩


/-- the index set of the windows of `(1/M, 3]`: cells `q = 6m + r` with `m ≥ 1`, and `q = 2, …, 5`. -/
def kset (M : ℕ) : Finset (ℕ × ℕ) :=
  ({0} ×ˢ Finset.Ico 6 22) ∪ (Finset.Ico 1 M ×ˢ Finset.range 22)

noncomputable def qk (κ : ℕ × ℕ) : ℕ := 6 * κ.1 + (c01Piece κ.2).r

noncomputable def alk (κ : ℕ × ℕ) : ℝ := 6 / ((qk κ : ℝ) + (c01Piece κ.2).hi)
noncomputable def bek (κ : ℕ × ℕ) : ℝ := 6 / ((qk κ : ℝ) + (c01Piece κ.2).lo)
/-- the integrand of the window `κ` is `winA κ * y + winB κ = -(c₀ y + c₁)`. -/
noncomputable def winA (κ : ℕ × ℕ) : ℝ :=
  -((c01Piece κ.2).a + (c01Piece κ.2).b * (qk κ : ℝ) + (qk κ : ℝ) ^ 2 / 2)
noncomputable def winB (κ : ℕ × ℕ) : ℝ := -((c01Piece κ.2).g - 3 * (qk κ : ℝ))
noncomputable def Icl (κ : ℕ × ℕ) : ℝ := winA κ * (bek κ ^ 2 - alk κ ^ 2) / 2 + winB κ * (bek κ - alk κ)

theorem mem_kset {M : ℕ} {κ : ℕ × ℕ} :
    κ ∈ kset M ↔ (κ.1 = 0 ∧ 6 ≤ κ.2 ∧ κ.2 < 22) ∨ (1 ≤ κ.1 ∧ κ.1 < M ∧ κ.2 < 22) := by
  obtain ⟨m, j⟩ := κ
  simp only [kset, Finset.mem_union, Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico,
    Finset.mem_range]
  omega

theorem kset_props {M : ℕ} (hM : 1 ≤ M) {κ : ℕ × ℕ} (hκ : κ ∈ kset M) :
    κ.2 < 22 ∧ 0 ≤ (c01Piece κ.2).lo ∧ (c01Piece κ.2).lo < (c01Piece κ.2).hi ∧ (c01Piece κ.2).hi ≤ 1 ∧
      2 ≤ qk κ ∧ (qk κ : ℝ) + (c01Piece κ.2).hi ≤ 6 * M := by
  obtain ⟨m, j⟩ := κ
  have hr := (mem_kset.1 hκ)
  simp only at hr
  have hj : j < 22 := by omega
  obtain ⟨h0, h1, h2, h3⟩ := c01_piece_bounds j hj
  refine ⟨hj, h0, h1, h2, ?_, ?_⟩
  · rcases hr with ⟨hm, hj6, _⟩ | ⟨hm, _, _⟩
    · have := c01_r_ge2 hj hj6; simp only [qk, hm]; omega
    · simp only [qk]; omega
  · have hq : qk (m, j) + 1 ≤ 6 * M := by
      rcases hr with ⟨hm, _, _⟩ | ⟨hm, hmM, _⟩
      · simp only [qk, hm]; omega
      · simp only [qk]; omega
    have : ((qk (m, j) + 1 : ℕ) : ℝ) ≤ ((6 * M : ℕ) : ℝ) := by exact_mod_cast hq
    push_cast at this
    linarith

theorem alk_ge {M : ℕ} (hM : 1 ≤ M) {κ : ℕ × ℕ} (hκ : κ ∈ kset M) : 1 / (M : ℝ) ≤ alk κ := by
  obtain ⟨hj, h0, h1, h2, hq, hq6⟩ := kset_props hM hκ
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hq0 : (0 : ℝ) < (qk κ : ℝ) + (c01Piece κ.2).hi := by
    have : (2 : ℝ) ≤ qk κ := by exact_mod_cast hq
    linarith
  unfold alk
  rw [div_le_div_iff₀ hM0 hq0]
  nlinarith

theorem bek_le {M : ℕ} (hM : 1 ≤ M) {κ : ℕ × ℕ} (hκ : κ ∈ kset M) : bek κ ≤ 3 := by
  obtain ⟨hj, h0, h1, h2, hq, hq6⟩ := kset_props hM hκ
  have hq2 : (2 : ℝ) ≤ qk κ := by exact_mod_cast hq
  unfold bek
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem alk_lt_bek {M : ℕ} (hM : 1 ≤ M) {κ : ℕ × ℕ} (hκ : κ ∈ kset M) : alk κ < bek κ := by
  obtain ⟨hj, h0, h1, h2, hq, hq6⟩ := kset_props hM hκ
  have hq2 : (2 : ℝ) ≤ qk κ := by exact_mod_cast hq
  unfold alk bek
  exact div_lt_div_of_pos_left (by norm_num) (by linarith) (by linarith)

theorem alk_pos {M : ℕ} (hM : 1 ≤ M) {κ : ℕ × ℕ} (hκ : κ ∈ kset M) : 0 < alk κ := by
  obtain ⟨hj, h0, h1, h2, hq, hq6⟩ := kset_props hM hκ
  have hq2 : (2 : ℝ) ≤ qk κ := by exact_mod_cast hq
  unfold alk
  exact div_pos (by norm_num) (by linarith)

/-- every window of `kset M` lies in `(1/M, 3]`, and conversely every prime there is in one. -/
theorem primeWin_eq_biUnion {M : ℕ} (hM : 1 ≤ M) (n : ℕ) :
    primeWin (1 / (M : ℝ)) 3 n = (kset M).biUnion (fun κ => primeWin (alk κ) (bek κ) n) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hδ0 : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
  have hδ3 : 1 / (M : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hM0]
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  ext p
  rw [Finset.mem_biUnion]
  constructor
  · intro hp
    have hp' := (mem_primeWin hδ0 hδ3).1 hp
    obtain ⟨h1, h2, hpr⟩ := hp'
    have hp0 : 0 < p := hpr.pos
    have hpn3 : p ≤ 3 * n := by exact_mod_cast (by linarith : (p : ℝ) ≤ 3 * n)
    have hnM : n < M * p := by
      have : (n : ℝ) < M * p := by
        have := h1
        rw [div_mul_eq_mul_div, div_lt_iff₀ hM0] at this
        linarith
      exact_mod_cast this
    have hqr := qr6 n p hp0
    have hrlt := r6_lt n p hp0
    set q := q6 n p with hq
    have hq2 : 2 ≤ q := by
      rw [hq]; unfold q6
      rw [Nat.le_div_iff_mul_le hp0]; omega
    have hq6 : q < 6 * M := by
      rw [hq]; unfold q6
      rw [Nat.div_lt_iff_lt_mul hp0]; nlinarith
    have ht0 : (0 : ℝ) ≤ (r6 n p : ℝ) / p := by positivity
    have ht1 : (r6 n p : ℝ) / p < 1 := by
      rw [div_lt_one (by exact_mod_cast hp0)]; exact_mod_cast hrlt
    obtain ⟨j, hj, hrj, hlo, hhi⟩ := c01_tiling (q % 6) (Nat.mod_lt _ (by norm_num)) _ ht0 ht1
    obtain ⟨b0, b1, b2, b3⟩ := c01_piece_bounds j hj
    have hκ : ((q / 6, j) : ℕ × ℕ) ∈ kset M := by
      rw [mem_kset]
      by_cases hm : q / 6 = 0
      · left
        have hr2 : 2 ≤ (c01Piece j).r := by rw [hrj]; omega
        exact ⟨hm, c01_j_ge6 hj hr2, hj⟩
      · right
        exact ⟨by omega, by omega, hj⟩
    have hqk : qk (q / 6, j) = q := by simp only [qk, hrj]; omega
    refine ⟨(q / 6, j), hκ, ?_⟩
    have hq0 : 0 < qk (q / 6, j) := by omega
    unfold alk bek
    rw [window_char b0 b1 b2 hq0 hp0]
    refine ⟨hpr, by rw [hqk], ?_, ?_⟩
    · have := (le_div_iff₀ (by exact_mod_cast hp0 : (0 : ℝ) < p)).1 hlo
      exact this
    · have := (div_lt_iff₀ (by exact_mod_cast hp0 : (0 : ℝ) < p)).1 hhi
      exact this
  · rintro ⟨κ, hκ, hp⟩
    obtain ⟨hj, h0, h1, h2, hq, hq6⟩ := kset_props hM hκ
    have hα := alk_pos hM hκ
    have hαβ := (alk_lt_bek hM hκ).le
    have hm := (mem_primeWin hα.le hαβ).1 hp
    obtain ⟨m1, m2, m3⟩ := hm
    refine (mem_primeWin hδ0 hδ3).2 ⟨?_, ?_, m3⟩
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (alk_ge hM hκ) (Nat.cast_nonneg _)) m1
    · exact m2.trans (mul_le_mul_of_nonneg_right (bek_le hM hκ) (Nat.cast_nonneg _))

theorem windows_disjoint {M : ℕ} (hM : 1 ≤ M) (n : ℕ) :
    (↑(kset M) : Set (ℕ × ℕ)).PairwiseDisjoint (fun κ => primeWin (alk κ) (bek κ) n) := by
  intro κ hκ κ' hκ' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro p hp hp'
  obtain ⟨hj, h0, h1, h2, hq, hq6⟩ := kset_props hM hκ
  obtain ⟨hj', h0', h1', h2', hq', hq6'⟩ := kset_props hM hκ'
  have hpr := prime_of_mem_primeWin hp
  have hp0 := hpr.pos
  have e1 := (window_char (n := n) (p := p) (q := qk κ) h0 h1 h2 (by omega) hp0).1 (by unfold alk bek at hp; exact hp)
  have e2 := (window_char (n := n) (p := p) (q := qk κ') h0' h1' h2' (by omega) hp0).1 (by unfold alk bek at hp'; exact hp')
  obtain ⟨_, d1, l1, u1⟩ := e1
  obtain ⟨_, d2, l2, u2⟩ := e2
  have hpr0 : (0 : ℝ) < p := by exact_mod_cast hp0
  have hrj : (c01Piece κ.2).r = (c01Piece κ'.2).r := by
    have a1 := (c01_piece_bounds κ.2 hj).2.2.2
    have a2 := (c01_piece_bounds κ'.2 hj').2.2.2
    simp only [qk] at d1 d2
    omega
  have hjj := c01_tiling_unique hj hj' hrj (t := (r6 n p : ℝ) / p)
    ((le_div_iff₀ hpr0).2 l1) ((div_lt_iff₀ hpr0).2 u1) ((le_div_iff₀ hpr0).2 l2) ((div_lt_iff₀ hpr0).2 u2)
  apply hne
  have : κ.1 = κ'.1 := by
    simp only [qk] at d1 d2
    rw [hjj] at d1
    omega
  exact Prod.ext this hjj


/-- The bridge `Wlaw ≥ p c₀ + n c₁ − 1000 (q² + 1)` on the 22 pieces (to be proved in `Lai.ContentBridge`). -/
def BridgeStmt : Prop :=
  ∀ (n p j : ℕ), p.Prime → 10 ≤ n → Rng n p → j < 22 → q6 n p % 6 = (c01Piece j).r →
    (c01Piece j).lo * (p : ℝ) ≤ (r6 n p : ℝ) → (r6 n p : ℝ) < (c01Piece j).hi * (p : ℝ) →
    (p : ℝ) * ((c01Piece j).a + (c01Piece j).b * (q6 n p : ℝ) + (q6 n p : ℝ) ^ 2 / 2) +
      (n : ℝ) * ((c01Piece j).g - 3 * (q6 n p : ℝ)) - 1000 * ((q6 n p : ℝ) ^ 2 + 1) ≤ (Wlaw n p : ℝ)

theorem Icl_alg (a b g lo hi r m : ℝ) (hm : 1 ≤ m) (hr : 0 ≤ r) (hlo : 0 ≤ lo) (hhi : 0 ≤ hi) :
    -(a + b * (6 * m + r) + (6 * m + r) ^ 2 / 2) *
        ((6 / (6 * m + r + lo)) ^ 2 - (6 / (6 * m + r + hi)) ^ 2) / 2 +
      -(g - 3 * (6 * m + r)) * (6 / (6 * m + r + lo) - 6 / (6 * m + r + hi)) =
    -((9 - (3 * b + g) / (m + (r + hi) / 6) - (a - b * hi + hi ^ 2 / 2) / (2 * (m + (r + hi) / 6) ^ 2)) -
      (9 - (3 * b + g) / (m + (r + lo) / 6) - (a - b * lo + lo ^ 2 / 2) / (2 * (m + (r + lo) / 6) ^ 2))) := by
  have e1 : (6 * m + r + hi) ≠ 0 := by linarith
  have e2 : (6 * m + r + lo) ≠ 0 := by linarith
  have e3 : (m + (r + hi) / 6) ≠ 0 := by linarith
  have e4 : (m + (r + lo) / 6) ≠ 0 := by linarith
  field_simp
  ring

theorem Icl_eq (m j : ℕ) (hm : 1 ≤ m) (hj : j < 22) : Icl (m, j) = -c01CellInt m j := by
  obtain ⟨h0, h1, h2, h3⟩ := c01_piece_bounds j hj
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hr0 : (0 : ℝ) ≤ (c01Piece j).r := Nat.cast_nonneg _
  rw [c01_cell_eval m j hm hj]
  unfold Icl winA winB alk bek qk c01End
  simp only
  push_cast
  exact Icl_alg _ _ _ _ _ _ _ hm1 hr0 h0 (by linarith)

set_option maxRecDepth 100000 in
theorem sum_Icl_zero : ∑ j ∈ Finset.Ico 6 22, Icl (0, j) = 2263 / 280 := by
  simp only [Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_zero, Icl, winA,
    winB, alk, bek, qk, c01Piece]
  norm_num

theorem sum_Icl (M : ℕ) (hM : 1 ≤ M) :
    ∑ κ ∈ kset M, Icl κ = 2263 / 280 +
      ((CatalanCore.Content.PartialSums.partialS (fun i : Fin 23 => c01Eq i)
        (fun i : Fin 23 => c01Dq i) M : ℚ) : ℝ) := by
  unfold kset
  rw [Finset.sum_union (by
    rw [Finset.disjoint_left]
    intro κ h1 h2
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_Ico] at h1 h2
    omega)]
  rw [Finset.sum_product, Finset.sum_product]
  simp only [Finset.sum_singleton]
  rw [sum_Icl_zero]
  congr 1
  unfold CatalanCore.Content.PartialSums.partialS
  push_cast
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 := (Finset.mem_Ico.1 hm).1
  rw [CatalanCore.Lai.c01_nodeF_eq m hm1]
  push_cast
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j hj => Icl_eq m j hm1 (Finset.mem_range.1 hj)

/-- the bridging for one window. -/
theorem win_bound (hBr : BridgeStmt) {M : ℕ} (hM : 1 ≤ M) {κ : ℕ × ℕ} (hκ : κ ∈ kset M) {n : ℕ}
    (hn : max 10 (8 * M ^ 2) ≤ n) {p : ℕ} (hp : p ∈ primeWin (alk κ) (bek κ) n) :
    -(laiW n p : ℝ) ≤ (n : ℝ) * (winA κ * ((p : ℝ) / n) + winB κ) + 1000 * ((qk κ : ℝ) ^ 2 + 1) := by
  obtain ⟨hj, h0, h1, h2, hq, hq6⟩ := kset_props hM hκ
  have hn10 : 10 ≤ n := le_trans (le_max_left _ _) hn
  have hn8 : 8 * M ^ 2 ≤ n := le_trans (le_max_right _ _) hn
  have hpr := prime_of_mem_primeWin hp
  have hp0 := hpr.pos
  have hmem := (mem_primeWin (alk_pos hM hκ).le (alk_lt_bek hM hκ).le).1 hp
  obtain ⟨m1, m2, m3⟩ := hmem
  have hch := (window_char (n := n) (p := p) (q := qk κ) h0 h1 h2 (by omega) hp0).1
    (by unfold alk bek at hp; exact hp)
  obtain ⟨_, hqq, hl, hu⟩ := hch
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hp3 : p ≤ 3 * n := by
    have : (p : ℝ) ≤ 3 * n := m2.trans (mul_le_mul_of_nonneg_right (bek_le hM hκ) hn0.le)
    exact_mod_cast this
  have hp3' : p < 3 * n := by
    rcases Nat.lt_or_ge p (3 * n) with h | h
    · exact h
    · have heq : p = 3 * n := le_antisymm hp3 h
      have h3 : 3 ∣ p := ⟨n, heq⟩
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpr).1 h3
      omega
  have hnM : (n : ℝ) < M * p := by
    have h := lt_of_le_of_lt (mul_le_mul_of_nonneg_right (alk_ge hM hκ) hn0.le) m1
    rw [div_mul_eq_mul_div, div_lt_iff₀ hM0] at h
    linarith
  have h8 : 8 * n < p ^ 2 := by
    have hn8' : (8 : ℝ) * M ^ 2 ≤ n := by exact_mod_cast hn8
    have : (8 : ℝ) * n < p ^ 2 := by
      have hsq : (n : ℝ) ^ 2 < (M * p) ^ 2 := by
        apply pow_lt_pow_left₀ hnM hn0.le (by norm_num)
      have : (M : ℝ) ^ 2 * (8 * n) < (M : ℝ) ^ 2 * p ^ 2 := by nlinarith
      exact lt_of_mul_lt_mul_left this (by positivity)
    exact_mod_cast this
  have hR : Rng n p := ⟨h8, hp3'⟩
  have hres : q6 n p % 6 = (c01Piece κ.2).r := by
    rw [hqq]; simp only [qk]
    have := (c01_piece_bounds κ.2 hj).2.2.2
    omega
  have hb := hBr n p κ.2 hpr hn10 hR hj hres hl hu
  have hW : (Wlaw n p : ℝ) ≤ (laiW n p : ℝ) := by exact_mod_cast laiW_ge_W hR
  rw [hqq] at hb
  unfold winA winB
  have e : (n : ℝ) * (-((c01Piece κ.2).a + (c01Piece κ.2).b * (qk κ : ℝ) + (qk κ : ℝ) ^ 2 / 2) *
      ((p : ℝ) / n) + -((c01Piece κ.2).g - 3 * (qk κ : ℝ))) =
      -((p : ℝ) * ((c01Piece κ.2).a + (c01Piece κ.2).b * (qk κ : ℝ) + (qk κ : ℝ) ^ 2 / 2)) -
        (n : ℝ) * ((c01Piece κ.2).g - 3 * (qk κ : ℝ)) := by
    field_simp
    ring
  rw [e]
  linarith

theorem band_main (hBr : BridgeStmt) {M : ℕ} (hM : 1 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∑ p ∈ primeWin (1 / (M : ℝ)) 3 n, (-(laiW n p : ℝ)) * Real.log (p : ℝ) ≤
        ((∑ κ ∈ kset M, Icl κ) + ε) * (n : ℝ) ^ 2 := by
  classical
  have hmem06 : ((0, 6) : ℕ × ℕ) ∈ kset M := by rw [mem_kset]; left; norm_num
  have hcard : (0 : ℝ) < ((kset M).card : ℝ) := by exact_mod_cast Finset.card_pos.2 ⟨_, hmem06⟩
  set ε' : ℝ := ε / (kset M).card with hε'
  have hε'0 : 0 < ε' := div_pos hε hcard
  have hall : ∀ κ ∈ kset M, ∀ᶠ n : ℕ in atTop,
      ∑ p ∈ primeWin (alk κ) (bek κ) n, (-(laiW n p : ℝ)) * Real.log (p : ℝ) ≤
        (Icl κ + ε') * (n : ℝ) ^ 2 := by
    intro κ hκ
    have := window_le (α := alk κ) (β := bek κ) (A := winA κ) (B := winB κ) (E := 1000 * ((qk κ : ℝ) ^ 2 + 1))
      (alk_pos hM hκ) (alk_lt_bek hM hκ) (by positivity) (max 10 (8 * M ^ 2))
      (fun n p => -(laiW n p : ℝ)) (fun n hn p hp => win_bound hBr hM hκ hn hp) hε'0
    filter_upwards [this] with n hn
    rw [integral_affine] at hn
    unfold Icl
    exact hn
  filter_upwards [(Filter.eventually_all_finset (kset M)).2 hall] with n hn
  rw [primeWin_eq_biUnion hM n, Finset.sum_biUnion (windows_disjoint hM n)]
  calc _ ≤ ∑ κ ∈ kset M, (Icl κ + ε') * (n : ℝ) ^ 2 := Finset.sum_le_sum fun κ hκ => hn κ hκ
    _ = ((∑ κ ∈ kset M, Icl κ) + ε) * (n : ℝ) ^ 2 := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hε']
      congr 2
      field_simp


/-- `R_C = 28.68723663 - 6603/280`. -/
theorem RC_eq : (6603 / 280 : ℚ) + 3573565641 / 700000000 = 2868723663 / 10 ^ 8 := by norm_num

/-- **The signed sum**: the primes `p ≤ 6n` cost at most `(6603/280 + R + ε) n²`, given the bridge and
`S_M ≤ R` for all `M`. -/
theorem sum_signed_le (hBr : BridgeStmt) {R : ℝ}
    (hS : ∀ M : ℕ, 1 ≤ M → ((CatalanCore.Content.PartialSums.partialS (fun i : Fin 23 => c01Eq i)
        (fun i : Fin 23 => c01Dq i) M : ℚ) : ℝ) ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∑ p ∈ primes6 n, (-(laiW n p : ℝ)) * Real.log (p : ℝ) ≤ (6603 / 280 + R + ε) * (n : ℝ) ^ 2 := by
  obtain ⟨M, hM1, hM⟩ : ∃ M : ℕ, 1 ≤ M ∧ 48 / ε ≤ (M : ℝ) :=
    ⟨⌈48 / ε⌉₊ + 1, by omega, by have := Nat.le_ceil (48 / ε); push_cast; linarith⟩
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hδ : 0 < 1 / (M : ℝ) := by positivity
  have hδ3 : 1 / (M : ℝ) ≤ 3 := by
    rw [div_le_iff₀ hM0]
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    linarith
  have h12 : 12 * (1 / (M : ℝ)) ≤ ε / 4 := by
    have : 48 / ε ≤ M := hM
    rw [div_le_iff₀ hε] at this
    rw [show 12 * (1 / (M : ℝ)) = 12 / M by ring, div_le_iff₀ hM0]
    nlinarith
  have e0 := band_small hδ hδ3 (ε := ε / 8) (by positivity)
  have e1 := band_main hBr hM1 (ε := ε / 8) (by positivity)
  have e2 := band_O (ε := ε / 8) (by positivity)
  have e3 := band_7a (ε := ε / 8) (by positivity)
  have e4 := band_7b (ε := ε / 8) (by positivity)
  have e5 := band_7c (ε := ε / 8) (by positivity)
  have hSM := hS M hM1
  have hI := sum_Icl M hM1
  filter_upwards [e0, e1, e2, e3, e4, e5] with n h0 h1 h2 h3 h4 h5
  rw [sum_primes6_split (1 / (M : ℝ)) hδ hδ3]
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have hsum : ∑ κ ∈ kset M, Icl κ ≤ 2263 / 280 + R := by rw [hI]; linarith
  have hb : (12 * (1 / (M : ℝ)) + ε / 8) * (n : ℝ) ^ 2 + ((∑ κ ∈ kset M, Icl κ) + ε / 8) * (n : ℝ) ^ 2 +
      (15 / 4 + ε / 8) * (n : ℝ) ^ 2 + (19 / 4 + ε / 8) * (n : ℝ) ^ 2 + (19 / 4 + ε / 8) * (n : ℝ) ^ 2 +
      (9 / 4 + ε / 8) * (n : ℝ) ^ 2 ≤ (6603 / 280 + R + ε) * (n : ℝ) ^ 2 := by
    have : (12 * (1 / (M : ℝ)) + ε / 8) + ((∑ κ ∈ kset M, Icl κ) + ε / 8) + (15 / 4 + ε / 8) +
        (19 / 4 + ε / 8) + (19 / 4 + ε / 8) + (9 / 4 + ε / 8) ≤ 6603 / 280 + R + ε := by linarith
    nlinarith
  linarith

end KSet

end Windows

section C01Data

open CatalanCore.Content.PartialSums

/-- the node table of Theorem C01 as functions on `Fin 23`. -/
noncomputable abbrev e23 : Fin 23 → ℚ := fun i => c01Eq i
noncomputable abbrev d23 : Fin 23 → ℚ := fun i => c01Dq i

theorem d23_sum : ∑ i, d23 i = 0 := by
  have := c01Dq_sum
  rw [Finset.sum_range] at this
  exact this

theorem e23_nonneg : ∀ i, 0 ≤ e23 i := by
  intro i; fin_cases i <;> simp [e23, c01Eq] <;> norm_num

theorem e23_le_one : ∀ i, e23 i ≤ 1 := by
  intro i; fin_cases i <;> simp [e23, c01Eq] <;> norm_num

set_option maxRecDepth 100000 in
theorem c01_signs :
    0 ≤ a2 e23 d23 ∧ a3 e23 d23 ≤ 0 ∧ 0 ≤ a4 e23 d23 ∧ a5 e23 d23 ≤ 0 ∧ 0 ≤ a6 e23 d23 ∧
      -a3 e23 d23 / 2 - a5 e23 d23 / 4 ≤ a2 e23 d23 := by
  simp only [a2, a3, a4, a5, a6, mom, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp [e23, d23, c01Eq, c01Dq]
  norm_num

theorem nodeF_range (m : ℕ) :
    nodeF e23 d23 m = -∑ i ∈ Finset.range 23, c01Dq i / ((m : ℚ) + c01Eq i) := by
  unfold nodeF
  simp only [e23, d23]
  rw [Finset.sum_range (fun i => c01Dq i / ((m : ℚ) + c01Eq i))]

theorem mom_range (j : ℕ) : mom e23 d23 j = ∑ i ∈ Finset.range 23, c01Dq i * c01Eq i ^ j := by
  unfold mom
  simp only [e23, d23]
  rw [Finset.sum_range (fun i => c01Dq i * c01Eq i ^ j)]

theorem absmom_range (j : ℕ) :
    absmom e23 d23 j = ∑ i ∈ Finset.range 23, |c01Dq i| * c01Eq i ^ j := by
  unfold absmom
  simp only [e23, d23]
  rw [Finset.sum_range (fun i => |c01Dq i| * c01Eq i ^ j)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem c01_nodeF_nonneg : ∀ m : ℕ, 1 ≤ m → 0 ≤ nodeF e23 d23 m := by
  refine nodeF_nonneg d23_sum e23_nonneg 13 (fun m hm1 hm13 => ?_) ?_ ?_
  · rw [nodeF_range]
    interval_cases m <;> (simp only [Finset.sum_range_succ, Finset.sum_range_zero, c01Dq, c01Eq]; norm_num)
  · rw [absmom_range, mom_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, c01Dq, c01Eq]
    norm_num
  · rw [mom_range]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, c01Dq, c01Eq]
    norm_num

/-- the grid lemma (the only theorem-side step of the prefix certificate): if every term
`-d_i/(m+e_i)` is bounded by `-d_i Q(m,i)/2^80` then `S₁₀₀₀` is bounded by the grid sum. -/
theorem partialS_le_of_grid (Q : ℕ → Fin 23 → ℤ)
    (hterm : ∀ m : ℕ, 1 ≤ m → m < 1000 → ∀ i : Fin 23,
      -(d23 i) / ((m : ℚ) + e23 i) ≤ -(d23 i) * (Q m i : ℚ) / 2 ^ 80) :
    partialS e23 d23 1000 ≤ ∑ m ∈ Finset.Ico 1 1000, ∑ i : Fin 23, -(d23 i) * (Q m i : ℚ) / 2 ^ 80 := by
  unfold partialS nodeF
  refine Finset.sum_le_sum fun m hm => ?_
  have hm' := Finset.mem_Ico.1 hm
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have := hterm m hm'.1 hm'.2 i
  rw [neg_div] at this
  exact this

/-- **LC27 (theorem side).**  Given the prefix bound `S₁₀₀₀ ≤ Ŝ` (the 22,977-term grid certificate,
W2 data) and the single rational comparison `Ŝ + Φ(1000) ≤ R_C`, every partial sum is `≤ R_C`. -/
theorem c01_partial_le (Shat : ℚ) (hS : partialS e23 d23 1000 ≤ Shat)
    (hR : Shat + Phi e23 d23 ((1000 : ℕ) : ℚ) ≤ 3573565641 / 700000000) :
    ∀ M : ℕ, 1 ≤ M → partialS e23 d23 M ≤ 3573565641 / 700000000 := by
  obtain ⟨h2, h3, h4, h5, h6, hΦ⟩ := c01_signs
  exact partial_sum_le d23_sum e23_nonneg e23_le_one h2 h3 h4 h5 h6 hΦ c01_nodeF_nonneg 1000
    (by norm_num) Shat _ hS hR

end C01Data

section Final

open Filter Topology

/-- **LC30, `lai_content`.**  With the signed normaliser `m_n = ∏_{p ≤ 6n} p^{-w(n,p)}` (a positive rational),
for every `ε > 0` and all large `n`: `m_n · J_n ∈ ℤ_(q)[a, b, X]` at every prime `q` (so `m_n J_n(a, b, X)`
is an integer at every integer point) and `log m_n ≤ (28.68723663 + ε) n²`.  Inputs: Theorem L2
(`L2Stmt`), Lai Lemma 4.4 for `7n/2 < p ≤ 6n` (`Band7Stmt`), the bridge on the 22 pieces
(`BridgeStmt`), and the C01 prefix data `(Ŝ, hS, hR)`. -/
theorem lai_content (hL2 : L2Stmt) (hB7 : Band7Stmt) (hBr : BridgeStmt) (Shat : ℚ)
    (hS : CatalanCore.Content.PartialSums.partialS e23 d23 1000 ≤ Shat)
    (hR : Shat + CatalanCore.Content.PartialSums.Phi e23 d23 ((1000 : ℕ) : ℚ) ≤ 3573565641 / 700000000)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ n : ℕ, R₀ ≤ n →
      0 < signedDen n laiW ∧
      (∀ q : ℕ, ∀ [Fact q.Prime], GV q 0 (C (signedDen n laiW) * laiJ n)) ∧
      Real.log ((signedDen n laiW : ℚ) : ℝ) ≤ (2868723663 / 10 ^ 8 + ε) * (n : ℝ) ^ 2 := by
  have hS' : ∀ M : ℕ, 1 ≤ M → ((CatalanCore.Content.PartialSums.partialS (fun i : Fin 23 => c01Eq i)
      (fun i : Fin 23 => c01Dq i) M : ℚ) : ℝ) ≤ ((3573565641 / 700000000 : ℚ) : ℝ) := fun M hM => by
    exact_mod_cast c01_partial_le Shat hS hR M hM
  have key := sum_signed_le hBr hS' hε
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 (key.and (eventually_ge_atTop 10))
  refine ⟨R₀, fun n hn => ?_⟩
  obtain ⟨hk, h10⟩ := hR₀ n hn
  refine ⟨signedDen_pos n laiW, fun q _ => ?_, ?_⟩
  · exact GV_signedDen_mul n laiW (fun p _ _ => laiW_valid hL2 hB7 h10) q
  · rw [log_signedDen, ← Finset.sum_neg_distrib]
    have e : ((6603 / 280 : ℝ) + ((3573565641 / 700000000 : ℚ) : ℝ)) = 2868723663 / 10 ^ 8 := by
      push_cast; norm_num
    rw [e] at hk
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => by ring)) hk

end Final

section Scaled

open CatalanCore CatalanCore.Uniform Filter Topology

/-- A family rescaled by a positive rational normaliser (the signed form, as `Zeta5.signedFamily`):
`Q n = m n · Fam.Q n`, admissible where `Fam` is and `P n` holds. -/
noncomputable def scaleFam (Fam : PolyFamily) (P : Fam.ι → Prop) (m : Fam.ι → ℚ) : PolyFamily where
  const := Fam.const
  ι := Fam.ι
  deg := Fam.deg
  Adm := fun n => Fam.Adm n ∧ P n
  Q := fun n => Polynomial.C (m n) * Fam.Q n

theorem scaleFam_evalQ (Fam : PolyFamily) (P : Fam.ι → Prop) (m : Fam.ι → ℚ) (n : Fam.ι) (x : ℚ) :
    (scaleFam Fam P m).evalQ n x = m n * Fam.evalQ n x := by
  simp [PolyFamily.evalQ, scaleFam]

theorem scaleFam_evalR (Fam : PolyFamily) (P : Fam.ι → Prop) (m : Fam.ι → ℚ) (n : Fam.ι) (x : ℝ) :
    (scaleFam Fam P m).evalR n x = (m n : ℝ) * Fam.evalR n x := by
  simp [PolyFamily.evalR, scaleFam]

/-- **LC40, generic.**  Integrality of `q^deg · m n · Q_n(p/q)` gives `HasScaledContent` of the rescaled
family with `Λ = 0` (`den = 1`). -/
theorem hasScaledContent_scale (Fam : PolyFamily) (P : Fam.ι → Prop) (m : Fam.ι → ℚ)
    (scale : Fam.ι → ℕ)
    (hint : ∀ n, Fam.Adm n → P n → ∀ p q : ℤ, 0 < q →
      ∃ z : ℤ, (q : ℚ) ^ Fam.deg n * m n * Fam.evalQ n ((p : ℚ) / q) = z) :
    HasScaledContent (scaleFam Fam P m) scale 0 := by
  refine ⟨fun _ => 1, fun _ => Nat.one_pos, ?_, ?_⟩
  · intro n hn p q hq
    obtain ⟨z, hz⟩ := hint n hn.1 hn.2 p q hq
    refine ⟨z, ?_⟩
    show (q : ℚ) ^ Fam.deg n * ((1 : ℕ) : ℚ) * (scaleFam Fam P m).evalQ n ((p : ℚ) / q) = z
    have e : (scaleFam Fam P m).evalQ n ((p : ℚ) / q) = m n * Fam.evalQ n ((p : ℚ) / q) :=
      scaleFam_evalQ Fam P m n _
    rw [e, ← hz]
    push_cast
    ring
  · intro ε hε
    refine ⟨0, fun n _ _ => ?_⟩
    simp only [Nat.cast_one, Real.log_one, zero_add]
    positivity

/-- **Decay of the rescaled family:** `D' = D - Λ`, same window constant. -/
theorem hasScaledDecay_scale (Fam : PolyFamily) (P : Fam.ι → Prop) (m : Fam.ι → ℚ)
    (scale : Fam.ι → ℕ) {D c Λ : ℝ} (hD : HasScaledDecay Fam scale D c)
    (hpos : ∀ n, Fam.Adm n → P n → 0 < m n)
    (hlog : ∀ ε > 0, ∃ R : ℕ, ∀ n, Fam.Adm n → P n → R ≤ scale n →
      Real.log ((m n : ℚ) : ℝ) ≤ (Λ + ε) * (scale n : ℝ) ^ 2) :
    HasScaledDecay (scaleFam Fam P m) scale (D - Λ) c := by
  intro ε hε
  obtain ⟨R1, h1⟩ := hD (ε / 2) (by linarith)
  obtain ⟨R2, h2⟩ := hlog (ε / 2) (by linarith)
  refine ⟨max R1 R2, fun n hn hr t ht => ?_⟩
  have hsc : (0 : ℝ) ≤ (scale n : ℝ) := Nat.cast_nonneg _
  have hw : |t| ≤ Real.exp (-(c + ε / 2) * (scale n : ℝ)) :=
    ht.trans (Real.exp_le_exp.mpr (by nlinarith))
  have e1 := h1 n hn.1 (le_trans (le_max_left _ _) hr) t hw
  have e2 := h2 n hn.1 hn.2 (le_trans (le_max_right _ _) hr)
  have hm : (0 : ℝ) < (m n : ℝ) := by exact_mod_cast hpos n hn.1 hn.2
  have hmle : (m n : ℝ) ≤ Real.exp ((Λ + ε / 2) * (scale n : ℝ) ^ 2) := by
    calc (m n : ℝ) = Real.exp (Real.log (m n : ℝ)) := (Real.exp_log hm).symm
      _ ≤ _ := Real.exp_le_exp.mpr e2
  have hev : (scaleFam Fam P m).evalR n ((scaleFam Fam P m).const + t) =
      (m n : ℝ) * Fam.evalR n (Fam.const + t) := scaleFam_evalR Fam P m n _
  rw [hev, abs_mul, abs_of_pos hm]
  calc (m n : ℝ) * |Fam.evalR n (Fam.const + t)|
      ≤ Real.exp ((Λ + ε / 2) * (scale n : ℝ) ^ 2) *
          Real.exp (-(D - ε / 2) * (scale n : ℝ) ^ 2) :=
        mul_le_mul hmle e1 (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (-((D - Λ) - ε) * (scale n : ℝ) ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring

end Scaled


section LaiInstances

open CatalanCore CatalanCore.Uniform Filter Topology

/-- the signed Lai normaliser. -/
noncomputable def laiM (n : ℕ) : ℚ := signedDen n laiW

/-- plane: `q^{3n} · m_n · Q_n(p/q) ∈ ℤ` for `n ≥ 10` (LA08 + Gauss content at every prime). -/
theorem lai_plane_int (hL2 : L2Stmt) (hB7 : Band7Stmt) (a b : ℤ) {n : ℕ} (hn : 10 ≤ n) (p q : ℤ)
    (hq : 0 < q) :
    ∃ z : ℤ, (q : ℚ) ^ (laiPlaneFam a b).deg n * laiM n * (laiPlaneFam a b).evalQ n ((p : ℚ) / q) = z := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  obtain ⟨z, hz⟩ := signedDen_int n laiW (fun p _ _ => laiW_valid hL2 hB7 hn) ![q * a, q * b, p]
  refine ⟨z, ?_⟩
  have h := plane_scaled a b n p q hq0
  have hv : (fun i => (((![q * a, q * b, p] : Fin 3 → ℤ) i : ℤ) : ℚ)) =
      ![(q : ℚ) * a, (q : ℚ) * b, (p : ℚ)] := by
    funext i; fin_cases i <;> simp
  rw [hv] at hz
  show (q : ℚ) ^ (3 * n) * signedDen n laiW * (laiPlaneFam a b).evalQ n ((p : ℚ) / q) = z
  rw [← hz, ← h]
  ring

/-- ratio: `q^{3n} · m_n · Q_n(p/q) ∈ ℤ` for `n ≥ 10`. -/
theorem lai_ratio_int (hL2 : L2Stmt) (hB7 : Band7Stmt) {n : ℕ} (hn : 10 ≤ n) (p q : ℤ)
    (hq : 0 < q) :
    ∃ z : ℤ, (q : ℚ) ^ laiRatioFam.deg n * laiM n * laiRatioFam.evalQ n ((p : ℚ) / q) = z := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  obtain ⟨z, hz⟩ := signedDen_int n laiW (fun p _ _ => laiW_valid hL2 hB7 hn) ![q, -p, 0]
  refine ⟨z, ?_⟩
  have h := ratio_scaled n p q hq0
  have hv : (fun i => (((![q, -p, 0] : Fin 3 → ℤ) i : ℤ) : ℚ)) = ![(q : ℚ), -(p : ℚ), 0] := by
    funext i; fin_cases i <;> simp
  rw [hv] at hz
  show (q : ℚ) ^ (3 * n) * signedDen n laiW * laiRatioFam.evalQ n ((p : ℚ) / q) = z
  rw [← hz, ← h]
  ring

/-- the rescaled plane and ratio families (`Q n = m_n · J_n(a, b, X)`, admissible for `n ≥ 10`). -/
noncomputable abbrev laiPlaneFamS (a b : ℤ) : PolyFamily :=
  scaleFam (laiPlaneFam a b) (fun n : ℕ => 10 ≤ n) laiM

noncomputable abbrev laiRatioFamS : PolyFamily :=
  scaleFam laiRatioFam (fun n : ℕ => 10 ≤ n) laiM

/-- **LC40 (plane).** -/
theorem lai_plane_hasScaledContent (hL2 : L2Stmt) (hB7 : Band7Stmt) (a b : ℤ) :
    HasScaledContent (laiPlaneFamS a b) id 0 :=
  hasScaledContent_scale _ _ _ _ (fun n _ hn p q hq => lai_plane_int hL2 hB7 a b hn p q hq)

/-- **LC40 (ratio).** -/
theorem lai_ratio_hasScaledContent (hL2 : L2Stmt) (hB7 : Band7Stmt) :
    HasScaledContent laiRatioFamS id 0 :=
  hasScaledContent_scale _ _ _ _ (fun n _ hn p q hq => lai_ratio_int hL2 hB7 hn p q hq)

theorem laiM_pos (n : ℕ) : 0 < laiM n := signedDen_pos n laiW

/-- the log bound in the form `hasScaledDecay_scale` consumes. -/
theorem lai_laiM_log (hL2 : L2Stmt) (hB7 : Band7Stmt) (hBr : BridgeStmt) (Shat : ℚ)
    (hS : CatalanCore.Content.PartialSums.partialS e23 d23 1000 ≤ Shat)
    (hR : Shat + CatalanCore.Content.PartialSums.Phi e23 d23 ((1000 : ℕ) : ℚ) ≤ 3573565641 / 700000000) :
    ∀ ε > 0, ∃ R : ℕ, ∀ n : ℕ, 10 ≤ n → R ≤ n →
      Real.log ((laiM n : ℚ) : ℝ) ≤ (2868723663 / 10 ^ 8 + ε) * (n : ℝ) ^ 2 := by
  intro ε hε
  obtain ⟨R₀, h⟩ := lai_content hL2 hB7 hBr Shat hS hR hε
  exact ⟨R₀, fun n _ hn => (h n hn).2.2⟩

/-- **Decay of the rescaled plane family:** `D' = D - 28.68723663`, window constant unchanged. -/
theorem lai_plane_decay_scaled (hL2 : L2Stmt) (hB7 : Band7Stmt) (hBr : BridgeStmt) (Shat : ℚ)
    (hS : CatalanCore.Content.PartialSums.partialS e23 d23 1000 ≤ Shat)
    (hR : Shat + CatalanCore.Content.PartialSums.Phi e23 d23 ((1000 : ℕ) : ℚ) ≤ 3573565641 / 700000000)
    (a b : ℤ) {D c : ℝ} (hD : HasScaledDecay (laiPlaneFam a b) id D c) :
    HasScaledDecay (laiPlaneFamS a b) id (D - 2868723663 / 10 ^ 8) c :=
  hasScaledDecay_scale _ _ _ _ hD (fun n _ _ => laiM_pos n) (fun ε hε => by
    obtain ⟨R, h⟩ := lai_laiM_log hL2 hB7 hBr Shat hS hR ε hε
    exact ⟨R, fun n _ hn hr => h n hn hr⟩)

/-- **Decay of the rescaled ratio family.** -/
theorem lai_ratio_decay_scaled (hL2 : L2Stmt) (hB7 : Band7Stmt) (hBr : BridgeStmt) (Shat : ℚ)
    (hS : CatalanCore.Content.PartialSums.partialS e23 d23 1000 ≤ Shat)
    (hR : Shat + CatalanCore.Content.PartialSums.Phi e23 d23 ((1000 : ℕ) : ℚ) ≤ 3573565641 / 700000000)
    {D c : ℝ} (hD : HasScaledDecay laiRatioFam id D c) :
    HasScaledDecay laiRatioFamS id (D - 2868723663 / 10 ^ 8) c :=
  hasScaledDecay_scale _ _ _ _ hD (fun n _ _ => laiM_pos n) (fun ε hε => by
    obtain ⟨R, h⟩ := lai_laiM_log hL2 hB7 hBr Shat hS hR ε hε
    exact ⟨R, fun n _ hn hr => h n hn hr⟩)

end LaiInstances


end CatalanCore.Lai

#print axioms CatalanCore.Lai.laiW_valid
#print axioms CatalanCore.Lai.band_main
#print axioms CatalanCore.Lai.sum_signed_le
#print axioms CatalanCore.Lai.c01_partial_le
#print axioms CatalanCore.Lai.partialS_le_of_grid
#print axioms CatalanCore.Lai.lai_content
#print axioms CatalanCore.Lai.hasScaledContent_scale
#print axioms CatalanCore.Lai.hasScaledDecay_scale
#print axioms CatalanCore.Lai.lai_plane_hasScaledContent
#print axioms CatalanCore.Lai.lai_ratio_hasScaledContent
#print axioms CatalanCore.Lai.lai_plane_decay_scaled
#print axioms CatalanCore.Lai.lai_ratio_decay_scaled
