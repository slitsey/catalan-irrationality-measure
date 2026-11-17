module

public import CatalanCore.Arith.Hybrid.LemmaE.Harmonic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# The harmonic shift lemma modulo `p` (content note, Lemma SH)

For `p` prime, `H_m = ∑_{j=1}^m 1/j ∈ 𝔽_p` and a polynomial `G` of degree `≤ p - 4`, put
`∫G := ∑_{m<p} G(m) H_m` (`harmSum`).  Then the Volkenborn shift

  `∫G(x - 1) = ∫G - G'(-1)`            (`harmSum_shift_one`).

No Bernoulli number is used: the proof is summation by parts and the power sums
`∑_{j<p} j^i = 0` for `0 < i < p - 1` (reused from `LemmaE.Harmonic`).
-/

open Finset Polynomial CatalanCore.Arith.Hybrid.LemmaE

namespace CatalanCore.Content

variable {p : ℕ} [hp : Fact p.Prime]

/-- The harmonic number `H_m ∈ 𝔽_p`. -/
def harm (p : ℕ) [Fact p.Prime] (m : ℕ) : ZMod p := Gs p (fun x => x⁻¹) m

lemma harm_succ (m : ℕ) : harm p (m + 1) = harm p m + (((m + 1 : ℕ) : ZMod p))⁻¹ := by
  unfold harm Gs
  rw [Finset.sum_range_succ]

lemma harm_zero : harm p 0 = 0 := by simp [harm, Gs]

lemma harm_top (h3 : 3 ≤ p) : harm p (p - 1) = 0 := Gs_inv_top p h3

/-- The power sums `T_k = ∑_{j=1}^{p-1} j^k j^{-1}` for `k ≤ p - 4`. -/
lemma T_sum (k : ℕ) (hk : k ≤ p - 4) (h5 : 5 ≤ p) :
    ∑ u ∈ range (p - 1), (((u + 1 : ℕ) : ZMod p)) ^ k * (((u + 1 : ℕ) : ZMod p))⁻¹ =
      if k = 0 then 0 else if k = 1 then -1 else 0 := by
  have hne : ∀ u ∈ range (p - 1), (((u + 1 : ℕ) : ZMod p)) ≠ 0 := fun u hu =>
    cast_succ_ne_zero p (by have := Finset.mem_range.1 hu; omega)
  by_cases h0 : k = 0
  · subst h0
    simp only [pow_zero, one_mul, if_true]
    have := Gs_inv_top p (by omega)
    simpa [Gs] using this
  by_cases h1 : k = 1
  · subst h1
    simp only [pow_one, one_ne_zero, if_false, if_true]
    rw [Finset.sum_congr rfl (fun u hu => mul_inv_cancel₀ (hne u hu))]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have h1p : 1 ≤ p := by omega
    rw [Nat.cast_sub h1p, ZMod.natCast_self]; simp
  · simp only [h0, h1, if_false]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : 1 ≤ j := by omega
    have e : ∀ u ∈ range (p - 1), (((u + 1 : ℕ) : ZMod p)) ^ (j + 1) * (((u + 1 : ℕ) : ZMod p))⁻¹ =
        (((u + 1 : ℕ) : ZMod p)) ^ j := by
      intro u hu
      rw [pow_succ, mul_assoc, mul_inv_cancel₀ (hne u hu), mul_one]
    rw [Finset.sum_congr rfl e]
    have h := sum_range_pow p j (by omega)
    rw [sum_shift p (fun m => ((m : ℕ) : ZMod p) ^ j) (by simp [show j ≠ 0 by omega]) (by omega)] at h
    exact h

/-- `∑_{u<p-1} u^n (u+1)^{-1} = -n (-1)^{n-1}`. -/
lemma mono_C (n : ℕ) (hn : n ≤ p - 4) (h5 : 5 ≤ p) :
    ∑ u ∈ range (p - 1), ((u : ℕ) : ZMod p) ^ n * (((u + 1 : ℕ) : ZMod p))⁻¹ =
      -(n : ZMod p) * (-1) ^ (n - 1) := by
  have e1 : ∀ u ∈ range (p - 1), ((u : ℕ) : ZMod p) ^ n * (((u + 1 : ℕ) : ZMod p))⁻¹ =
      ∑ k ∈ range (n + 1), ((-1) ^ (n - k) * (n.choose k : ZMod p)) *
        ((((u + 1 : ℕ) : ZMod p)) ^ k * (((u + 1 : ℕ) : ZMod p))⁻¹) := by
    intro u _
    have : ((u : ℕ) : ZMod p) = (((u + 1 : ℕ) : ZMod p)) + (-1) := by push_cast; ring
    rw [this, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hT : ∀ k ∈ range (n + 1), ((-1 : ZMod p) ^ (n - k) * (n.choose k : ZMod p)) *
      ∑ u ∈ range (p - 1), (((u + 1 : ℕ) : ZMod p)) ^ k * (((u + 1 : ℕ) : ZMod p))⁻¹ =
      if k = 1 then -((-1 : ZMod p) ^ (n - 1) * (n : ZMod p)) else 0 := by
    intro k hk
    have hkn : k ≤ n := by have := Finset.mem_range.1 hk; omega
    rw [T_sum k (by omega) h5]
    by_cases h0 : k = 0
    · simp [h0]
    by_cases h1 : k = 1
    · subst h1; simp [Nat.choose_one_right]
    · simp [h0, h1]
  rw [Finset.sum_congr rfl hT]
  by_cases hn0 : n = 0
  · subst hn0; simp
  · rw [Finset.sum_ite_eq' (range (n + 1)) 1, if_pos (Finset.mem_range.2 (by omega))]
    ring

lemma sum_range_p_succ' (h : 1 ≤ p) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ m ∈ range p, f m = ∑ u ∈ range (p - 1), f (u + 1) + f 0 := by
  rw [show range p = range (p - 1 + 1) by rw [Nat.sub_add_cancel h], Finset.sum_range_succ']

lemma sum_range_p_succ (h : 1 ≤ p) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ m ∈ range p, f m = ∑ u ∈ range (p - 1), f u + f (p - 1) := by
  rw [show range p = range (p - 1 + 1) by rw [Nat.sub_add_cancel h], Finset.sum_range_succ]

/-- The shift identity on monomials. -/
lemma mono_shift (n : ℕ) (hn : n ≤ p - 4) (h5 : 5 ≤ p) :
    ∑ m ∈ range p, (((m : ℕ) : ZMod p) - 1) ^ n * harm p m =
      ∑ m ∈ range p, ((m : ℕ) : ZMod p) ^ n * harm p m - (n : ZMod p) * (-1) ^ (n - 1) := by
  have hp1 : 1 ≤ p := by omega
  have hL : ∑ m ∈ range p, (((m : ℕ) : ZMod p) - 1) ^ n * harm p m =
      ∑ u ∈ range (p - 1), ((u : ℕ) : ZMod p) ^ n * harm p u +
        ∑ u ∈ range (p - 1), ((u : ℕ) : ZMod p) ^ n * (((u + 1 : ℕ) : ZMod p))⁻¹ := by
    rw [sum_range_p_succ' hp1]
    simp only [harm_zero, mul_zero, add_zero, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [harm_succ, show (((u + 1 : ℕ) : ZMod p)) - 1 = ((u : ℕ) : ZMod p) by push_cast; ring]
    ring
  have hR : ∑ m ∈ range p, ((m : ℕ) : ZMod p) ^ n * harm p m =
      ∑ u ∈ range (p - 1), ((u : ℕ) : ZMod p) ^ n * harm p u := by
    rw [sum_range_p_succ hp1, harm_top (by omega), mul_zero, add_zero]
  rw [hL, hR, mono_C n hn h5]
  ring


/-! ### Polynomials over a ring of characteristic `p` -/

section Poly

variable {K : Type*} [CommRing K] [CharP K p]

/-- `∫G = ∑_{m<p} G(m) H_m`. -/
def harmSum (p : ℕ) [Fact p.Prime] {K : Type*} [CommRing K] [CharP K p] (G : K[X]) : K :=
  ∑ m ∈ range p, G.eval ((m : ℕ) : K) * ZMod.castHom (dvd_refl p) K (harm p m)

lemma eval_range (G : K[X]) (N : ℕ) (hN : G.natDegree < N) (x : K) :
    G.eval x = ∑ n ∈ range N, G.coeff n * x ^ n := eval_eq_sum_range' hN x

lemma deriv_eval_range (G : K[X]) (N : ℕ) (hN : G.natDegree < N) (x : K) :
    G.derivative.eval x = ∑ n ∈ range N, G.coeff n * (n : K) * x ^ (n - 1) := by
  rw [derivative_eval, sum_over_range' _ (by intro n; simp) N hN]

/-- **Volkenborn shift.**  `∫G(x - 1) = ∫G - G'(-1)` for `deg G ≤ p - 4`. -/
theorem harmSum_shift_one (G : K[X]) (hdeg : G.natDegree ≤ p - 4) (h5 : 5 ≤ p) :
    harmSum p (G.comp (X - 1)) = harmSum p G - G.derivative.eval (-1) := by
  have hN : G.natDegree < p - 3 := by omega
  set φ : ZMod p →+* K := ZMod.castHom (dvd_refl p) K with hφ
  have hcomp : ∀ x : K, (G.comp (X - 1)).eval x = G.eval (x - 1) := by
    intro x; simp
  have e1 : harmSum p (G.comp (X - 1)) =
      ∑ n ∈ range (p - 3), G.coeff n * φ (∑ m ∈ range p, (((m : ℕ) : ZMod p) - 1) ^ n * harm p m) := by
    unfold harmSum
    have step : ∀ m ∈ range p, (G.comp (X - 1)).eval ((m : ℕ) : K) * φ (harm p m) =
        ∑ n ∈ range (p - 3), G.coeff n * φ ((((m : ℕ) : ZMod p) - 1) ^ n * harm p m) := by
      intro m _
      rw [hcomp, eval_range G (p - 3) hN, Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_mul, map_pow, map_sub, map_one, map_natCast]; ring
    rw [Finset.sum_congr rfl step, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_sum, Finset.mul_sum]
  have e2 : harmSum p G =
      ∑ n ∈ range (p - 3), G.coeff n * φ (∑ m ∈ range p, ((m : ℕ) : ZMod p) ^ n * harm p m) := by
    unfold harmSum
    have step : ∀ m ∈ range p, G.eval ((m : ℕ) : K) * φ (harm p m) =
        ∑ n ∈ range (p - 3), G.coeff n * φ (((m : ℕ) : ZMod p) ^ n * harm p m) := by
      intro m _
      rw [eval_range G (p - 3) hN, Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_mul, map_pow, map_natCast]; ring
    rw [Finset.sum_congr rfl step, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_sum, Finset.mul_sum]
  rw [e1, e2, deriv_eval_range G (p - 3) hN, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn' : n ≤ p - 4 := by have := Finset.mem_range.1 hn; omega
  rw [mono_shift n hn' h5, map_sub, map_mul, map_natCast, map_pow, map_neg, map_one]
  ring

lemma natDegree_comp_X_sub_le (G : K[X]) (a : K) : (G.comp (X - C a)).natDegree ≤ G.natDegree := by
  calc (G.comp (X - C a)).natDegree ≤ G.natDegree * (X - C a).natDegree := natDegree_comp_le
    _ ≤ G.natDegree * 1 := Nat.mul_le_mul_left _ (natDegree_X_sub_C_le a)
    _ = G.natDegree := mul_one _

/-- **Iterated Volkenborn shift.**  `∫G(x - α) = ∫G - ∑_{j=1}^{α} G'(-j)`. -/
theorem harmSum_shift_nat (G : K[X]) (hdeg : G.natDegree ≤ p - 4) (h5 : 5 ≤ p) (α : ℕ) :
    harmSum p (G.comp (X - C (α : K))) =
      harmSum p G - ∑ j ∈ range α, G.derivative.eval (-(((j + 1 : ℕ)) : K)) := by
  induction α with
  | zero => simp
  | succ α ih =>
    have hc : G.comp (X - C (((α + 1 : ℕ)) : K)) = (G.comp (X - C (α : K))).comp (X - 1) := by
      rw [comp_assoc]
      congr 1
      simp only [sub_comp, X_comp, C_comp, Nat.cast_add, Nat.cast_one, map_add, map_one]
      ring
    have hd : (G.comp (X - C (α : K))).natDegree ≤ p - 4 := (natDegree_comp_X_sub_le G _).trans hdeg
    rw [hc, harmSum_shift_one _ hd h5, ih, derivative_comp, eval_mul, eval_comp]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, eval_one, one_mul, eval_sub,
      eval_X, eval_C, Finset.sum_range_succ]
    have : (-1 : K) - (α : K) = -(((α + 1 : ℕ)) : K) := by push_cast; ring
    rw [this]
    ring

/-- **Lemma SH.**  Let `W ⊆ [0, p - α)` be a set of residues, and suppose `G` and `G'` vanish at
every residue in `[0, p)` outside `W`.  Then `∑_{s ∈ W} G(s) H_{s+α} = ∫G`. -/
theorem harmSum_window (G : K[X]) (hdeg : G.natDegree ≤ p - 4) (h5 : 5 ≤ p) (W : Finset ℕ)
    (α : ℕ) (hα : α < p) (hW : ∀ s ∈ W, s + α < p)
    (hG : ∀ m, m < p → m ∉ W → G.eval ((m : ℕ) : K) = 0)
    (hG' : ∀ m, m < p → m ∉ W → G.derivative.eval ((m : ℕ) : K) = 0) :
    ∑ s ∈ W, G.eval ((s : ℕ) : K) * ZMod.castHom (dvd_refl p) K (harm p (s + α)) = harmSum p G := by
  have hpK : ((p : ℕ) : K) = 0 := CharP.cast_eq_zero K p
  -- the vanishing at the shifted residues
  have hshift : ∀ m ∈ range p, m ∉ W.image (· + α) →
      (G.comp (X - C (α : K))).eval ((m : ℕ) : K) = 0 := by
    intro m hm hmW
    have hm' : m < p := Finset.mem_range.1 hm
    simp only [eval_comp, eval_sub, eval_X, eval_C]
    by_cases hmα : α ≤ m
    · have hr : m - α ∉ W := by
        intro h; exact hmW (Finset.mem_image.2 ⟨m - α, h, by omega⟩)
      have := hG (m - α) (by omega) hr
      rwa [Nat.cast_sub hmα] at this
    · have hr : p + m - α ∉ W := by
        intro h; have := hW _ h; omega
      have := hG (p + m - α) (by omega) hr
      rwa [Nat.cast_sub (by omega), Nat.cast_add, hpK, zero_add] at this
  have hA : ∑ s ∈ W, G.eval ((s : ℕ) : K) * ZMod.castHom (dvd_refl p) K (harm p (s + α)) =
      harmSum p (G.comp (X - C (α : K))) := by
    unfold harmSum
    have hinj : Set.InjOn (· + α) (W : Set ℕ) := fun a _ b _ h => by simpa using h
    rw [← Finset.sum_subset (s₁ := W.image (· + α)) (s₂ := range p)
      (fun m hm => by
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hm
        exact Finset.mem_range.2 (hW s hs))
      (fun m hm hmW => by rw [hshift m hm hmW, zero_mul]), Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [eval_comp, eval_sub, eval_X, eval_C, Nat.cast_add]
    congr 2
    ring
  rw [hA, harmSum_shift_nat G hdeg h5 α]
  have hz : ∑ j ∈ range α, G.derivative.eval (-(((j + 1 : ℕ)) : K)) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' : j < α := Finset.mem_range.1 hj
    have hr : p - (j + 1) ∉ W := by
      intro h; have := hW _ h; omega
    have := hG' (p - (j + 1)) (by omega) hr
    rwa [Nat.cast_sub (by omega), hpK, zero_sub] at this
  rw [hz, sub_zero]

/-- The reverse shift: `∫G(x + 1) = ∫G + G'(0)`. -/
theorem harmSum_shift_one_neg (G : K[X]) (hdeg : G.natDegree ≤ p - 4) (h5 : 5 ≤ p) :
    harmSum p (G.comp (X + 1)) = harmSum p G + G.derivative.eval 0 := by
  haveI : Nontrivial K := CharP.nontrivial_of_char_ne_one hp.out.ne_one
  have hd : (G.comp (X + 1)).natDegree ≤ p - 4 := by
    calc (G.comp (X + 1)).natDegree ≤ G.natDegree * (X + 1 : K[X]).natDegree := natDegree_comp_le
      _ ≤ G.natDegree * 1 := Nat.mul_le_mul_left _ (by simpa using (natDegree_X_add_C (1 : K)).le)
      _ ≤ p - 4 := by simpa using hdeg
  have h := harmSum_shift_one (G.comp (X + 1)) hd h5
  have e : (G.comp (X + 1)).comp (X - 1) = G := by
    rw [comp_assoc]; simp
  rw [e] at h
  have e2 : (G.comp (X + 1)).derivative.eval (-1) = G.derivative.eval 0 := by
    rw [derivative_comp, eval_mul, eval_comp]; simp
  rw [e2] at h
  linear_combination -h

/-- **Iterated reverse shift.** -/
theorem harmSum_shift_nat_neg (G : K[X]) (hdeg : G.natDegree ≤ p - 4) (h5 : 5 ≤ p) (α : ℕ) :
    harmSum p (G.comp (X + C (α : K))) =
      harmSum p G + ∑ j ∈ range α, G.derivative.eval ((j : ℕ) : K) := by
  induction α with
  | zero => simp
  | succ α ih =>
    have hc : G.comp (X + C (((α + 1 : ℕ)) : K)) = (G.comp (X + C (α : K))).comp (X + 1) := by
      rw [comp_assoc]
      congr 1
      simp only [add_comp, X_comp, C_comp, Nat.cast_add, Nat.cast_one, map_add, map_one]
      ring
    have hd : (G.comp (X + C (α : K))).natDegree ≤ p - 4 := by
      have := natDegree_comp_X_sub_le G (-(α : K))
      simpa [sub_eq_add_neg] using this.trans hdeg
    rw [hc, harmSum_shift_one_neg _ hd h5, ih, derivative_comp, eval_mul, eval_comp]
    simp only [derivative_add, derivative_X, derivative_C, add_zero, eval_one, one_mul, eval_add,
      eval_X, eval_C, Finset.sum_range_succ, zero_add]
    ring

/-- Lemma SH, reflected form: `x(s) = c - s`. -/
theorem harmSum_window_refl (G : K[X]) (hdeg : G.natDegree ≤ p - 4) (h5 : 5 ≤ p) (W : Finset ℕ)
    (c : ℕ) (hc : c < p) (hW : ∀ s ∈ W, s ≤ c)
    (hG : ∀ m, m < p → m ∉ W → G.eval ((m : ℕ) : K) = 0)
    (hG' : ∀ m, m < p → m ∉ W → G.derivative.eval ((m : ℕ) : K) = 0) :
    ∑ s ∈ W, G.eval ((s : ℕ) : K) * ZMod.castHom (dvd_refl p) K (harm p (c - s)) = harmSum p G := by
  rw [← harmSum_window G hdeg h5 W (p - 1 - c) (by omega) (fun s hs => by have := hW s hs; omega) hG hG']
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs' := hW s hs
  have : harm p (c - s) = harm p (s + (p - 1 - c)) := by
    have h := H_refl p (by omega) (n := c - s) (by omega)
    have e : p - 1 - (c - s) = s + (p - 1 - c) := by omega
    rw [e] at h
    exact h.symm
  rw [this]

/-- Lemma SH, `x(s) = s - α'` (`α' ≤ s`). -/
theorem harmSum_window_neg (G : K[X]) (hdeg : G.natDegree ≤ p - 4) (h5 : 5 ≤ p) (W : Finset ℕ)
    (α : ℕ) (hα : α < p) (hW : ∀ s ∈ W, α ≤ s ∧ s < p)
    (hG : ∀ m, m < p → m ∉ W → G.eval ((m : ℕ) : K) = 0)
    (hG' : ∀ m, m < p → m ∉ W → G.derivative.eval ((m : ℕ) : K) = 0) :
    ∑ s ∈ W, G.eval ((s : ℕ) : K) * ZMod.castHom (dvd_refl p) K (harm p (s - α)) = harmSum p G := by
  have hpK : ((p : ℕ) : K) = 0 := CharP.cast_eq_zero K p
  have hshift : ∀ m ∈ range p, m ∉ W.image (· - α) →
      (G.comp (X + C (α : K))).eval ((m : ℕ) : K) = 0 := by
    intro m hm hmW
    have hm' : m < p := Finset.mem_range.1 hm
    simp only [eval_comp, eval_add, eval_X, eval_C]
    by_cases hmα : m + α < p
    · have hr : m + α ∉ W := by
        intro h; exact hmW (Finset.mem_image.2 ⟨m + α, h, by omega⟩)
      have := hG (m + α) hmα hr
      rwa [Nat.cast_add] at this
    · have hr : m + α - p ∉ W := by
        intro h; have := hW _ h; omega
      have := hG (m + α - p) (by omega) hr
      rwa [Nat.cast_sub (by omega), Nat.cast_add, hpK, sub_zero] at this
  have hA : ∑ s ∈ W, G.eval ((s : ℕ) : K) * ZMod.castHom (dvd_refl p) K (harm p (s - α)) =
      harmSum p (G.comp (X + C (α : K))) := by
    unfold harmSum
    have hinj : Set.InjOn (· - α) (W : Set ℕ) := fun a ha b hb h => by
      have := hW a ha; have := hW b hb; simp only at h; omega
    rw [← Finset.sum_subset (s₁ := W.image (· - α)) (s₂ := range p)
      (fun m hm => by
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hm
        exact Finset.mem_range.2 (by have := hW s hs; omega))
      (fun m hm hmW => by rw [hshift m hm hmW, zero_mul]), Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun s hs => ?_
    have := hW s hs
    simp only [eval_comp, eval_add, eval_X, eval_C]
    congr 2
    rw [Nat.cast_sub this.1]; ring
  rw [hA, harmSum_shift_nat_neg G hdeg h5 α]
  have hz : ∑ j ∈ range α, G.derivative.eval ((j : ℕ) : K) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' : j < α := Finset.mem_range.1 hj
    have hr : j ∉ W := by
      intro h; have := hW _ h; omega
    exact hG' j (by omega) hr
  rw [hz, add_zero]

end Poly

end CatalanCore.Content
