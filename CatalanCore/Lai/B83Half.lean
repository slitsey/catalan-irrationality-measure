module

public import CatalanCore.NT.Wolstenholme
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Lemma G3 in the finite form (ledger LB07)

Note `N9-LAI-G3-FIN-2026-11-20.md`.  For a prime `p ≥ 5` and `n` with `8n < 3p`, `p + 1 < 3n`
(`a = p - 2n`, `A = 6n - 2p`, `K = 3n - 1 - p`), `ph ∈ ℤ_(p)[t]` of degree `≤ 2K - 2` and `ψ(x) = ph(-x)`:

  `L(Π² ph) ≡ 15 K₀ p³ λ(D_a³ ψ)  (mod p⁴)`.

All sums are finite; Faulhaber and von Staudt replace Euler–Maclaurin (`NT/Wolstenholme.lean`).
-/

set_option autoImplicit false

namespace CatalanCore.Lai.B83Half

open Polynomial Finset CatalanCore.Basic CatalanCore.NT
open scoped Nat

/-- The band hypotheses: `a = p - 2n`, `A = 6n - 2p`, `A < a` (that is `8n < 3p`), `p + 1 < 3n`. -/
structure Band (p n a A : ℕ) : Prop where
  p5 : 5 ≤ p
  ha : p = 2 * n + a
  hA : 6 * n = 2 * p + A
  hAa : A < a
  hn : p + 1 < 3 * n

theorem Band.of_range {p n : ℕ} (h5 : 5 ≤ p) (h1 : 8 * n < 3 * p) (h2 : p + 1 < 3 * n) :
    Band p n (p - 2 * n) (6 * n - 2 * p) :=
  ⟨h5, by omega, by omega, by omega, h2⟩

/-! ## Definitions -/

/-- `c_k = C(6n,k)² C(2n+k,k)³`. -/
def cc (n k : ℕ) : ℚ := (((6 * n).choose k : ℕ) : ℚ) ^ 2 * (((2 * n + k).choose k : ℕ) : ℚ) ^ 3

/-- `d_k = 5H_k - 3H_{2n+k} - 2H_{6n-k}`. -/
def dd (n k : ℕ) : ℚ := 5 * harm 1 k - 3 * harm 1 (2 * n + k) - 2 * harm 1 (6 * n - k)

/-- `U_k = -2 c_k H^{(3)}_k`. -/
def UU (n k : ℕ) : ℚ := -2 * cc n k * harm 3 k

/-- `E_k = U_k d_k - 6 c_k H^{(4)}_k`. -/
def EE (n k : ℕ) : ℚ := UU n k * dd n k - 6 * cc n k * harm 4 k

/-- The functional `L(f) = ∑_{k ≤ 6n} [E_k f(-k) + U_k f'(-k)]` (the `b`-component of Lai's
moment functional at `(a, b, X) = (0, 1, 0)`). -/
noncomputable def Lf (n : ℕ) (f : ℚ[X]) : ℚ :=
  ∑ k ∈ range (6 * n + 1), (EE n k * f.eval (-(k : ℚ)) + UU n k * (derivative f).eval (-(k : ℚ)))

/-- `∏_{r<a} (X + r)`. -/
noncomputable def Dplus (a : ℕ) : ℚ[X] := ∏ r ∈ range a, (X + C (r : ℚ))

/-- `D_a(x) = x (x-1) ⋯ (x-a+1)`. -/
noncomputable def Dfall (a : ℕ) : ℚ[X] := ∏ r ∈ range a, (X - C (r : ℚ))

/-- `Π(t) = ∏_{r<a} (t + r)^{μ_r}`, `μ_r = 4` for `r ≤ A` and `3` otherwise. -/
noncomputable def PiA (a A : ℕ) : ℚ[X] := ∏ r ∈ range a, (X + C (r : ℚ)) ^ (if r ≤ A then 4 else 3)

/-- `K₀ = 32 (p-1)!³ A!² / (2n)!³`. -/
def K0 (p n A : ℕ) : ℚ := 32 * (((p - 1) ! : ℕ) : ℚ) ^ 3 * ((A ! : ℕ) : ℚ) ^ 2 / (((2 * n) ! : ℕ) : ℚ) ^ 3

theorem PiA_eq {a A : ℕ} (h : A < a) : PiA a A = Dplus a ^ 3 * Dplus (A + 1) := by
  obtain ⟨b, rfl⟩ : ∃ b, a = (A + 1) + b := ⟨a - (A + 1), by omega⟩
  unfold PiA Dplus
  have e : ∀ r ∈ range ((A + 1) + b), (X + C (r : ℚ)) ^ (if r ≤ A then 4 else 3) =
      (X + C (r : ℚ)) ^ 3 * (if r ≤ A then (X + C (r : ℚ)) else 1) := by
    intro r _
    split_ifs with h1
    · rw [← pow_succ]
    · simp
  rw [prod_congr rfl e, prod_mul_distrib, prod_pow]
  have h1 : ∏ r ∈ range (A + 1), (if r ≤ A then (X + C (r : ℚ)) else 1) =
      ∏ r ∈ range (A + 1), (X + C (r : ℚ)) :=
    prod_congr rfl fun r hr => by rw [if_pos (by have := mem_range.1 hr; omega)]
  have h2 : ∏ r ∈ range b, (if A + 1 + r ≤ A then (X + C ((A + 1 + r : ℕ) : ℚ)) else 1) = 1 :=
    prod_eq_one fun r _ => by rw [if_neg (by omega)]
  congr 1
  rw [prod_range_add (fun r : ℕ => if r ≤ A then (X + C (r : ℚ)) else 1) (A + 1) b, h1, h2, mul_one]

/-! ## Factorial identities -/

theorem fact_add (N x : ℕ) : (((N + x) ! : ℕ) : ℚ) = ((N ! : ℕ) : ℚ) * ∏ y ∈ range x, ((N : ℚ) + y + 1) := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [show N + (x + 1) = (N + x) + 1 from rfl, Nat.factorial_succ, prod_range_succ]
    push_cast
    rw [ih]; ring

variable {p : ℕ} [hp : Fact p.Prime]

theorem prod_shift (j x : ℕ) :
    ∏ y ∈ range x, (((j * p : ℕ) : ℚ) + y + 1) = ((x ! : ℕ) : ℚ) * Pj p (j : ℤ) x := by
  induction x with
  | zero => simp [Pj]
  | succ x ih =>
    rw [prod_range_succ, ih]
    unfold Pj at *
    rw [prod_range_succ, Nat.factorial_succ]
    have : ((x : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

theorem fact_jp_add (j x : ℕ) :
    (((j * p + x) ! : ℕ) : ℚ) = (((j * p) ! : ℕ) : ℚ) * ((x ! : ℕ) : ℚ) * Pj p (j : ℤ) x := by
  rw [fact_add, prod_shift]; ring

theorem fact_p_mul (j : ℕ) :
    ((((j + 1) * p) ! : ℕ) : ℚ) = (((j * p) ! : ℕ) : ℚ) * (((j + 1) * p : ℕ) : ℚ) *
      (((p - 1) ! : ℕ) : ℚ) * Pj p (j : ℤ) (p - 1) := by
  have h1 : (j + 1) * p = j * p + p := by ring
  rw [h1, fact_add]
  have hp1 : p - 1 + 1 = p := by have := hp.out.pos; omega
  have := prod_range_succ (fun y : ℕ => ((j * p : ℕ) : ℚ) + y + 1) (p - 1)
  rw [hp1] at this
  rw [this, prod_shift]
  push_cast
  have e : ((j : ℚ) * p + ((p - 1 : ℕ) : ℚ) + 1) = ((j : ℚ) + 1) * p := by
    rw [Nat.cast_sub hp.out.one_le]; push_cast; ring
  rw [e]; ring

theorem fact_p_add (x : ℕ) :
    (((p + x) ! : ℕ) : ℚ) = (p : ℚ) * (((p - 1) ! : ℕ) : ℚ) * ((x ! : ℕ) : ℚ) * Pj p 1 x := by
  have := fact_jp_add (p := p) 1 x
  rw [one_mul] at this
  rw [this]
  have h2 : ((p ! : ℕ) : ℚ) = (p : ℚ) * (((p - 1) ! : ℕ) : ℚ) := by
    rw [← Nat.mul_factorial_pred hp.out.ne_zero]; push_cast; ring
  rw [h2]; simp

theorem fact_2p_add (x : ℕ) :
    (((2 * p + x) ! : ℕ) : ℚ) = 2 * (p : ℚ) ^ 2 * (((p - 1) ! : ℕ) : ℚ) ^ 2 * Pj p 1 (p - 1) *
      ((x ! : ℕ) : ℚ) * Pj p 2 x := by
  have h := fact_jp_add (p := p) 2 x
  have h2 := fact_p_mul (p := p) 1
  have h3 : ((1 * p) ! : ℕ) = p ! := by rw [one_mul]
  rw [h3] at h2
  have h4 : ((p ! : ℕ) : ℚ) = (p : ℚ) * (((p - 1) ! : ℕ) : ℚ) := by
    rw [← Nat.mul_factorial_pred hp.out.ne_zero]; push_cast; ring
  push_cast at h h2
  rw [show (2 : ℕ) * p = (1 + 1) * p from rfl] at h ⊢
  rw [h, h2, h4]
  push_cast
  ring

theorem fact_reflect (m : ℕ) (hm : m ≤ p - 1) :
    (((p - 1) ! : ℕ) : ℚ) = (((p - 1 - m) ! : ℕ) : ℚ) * (-1) ^ m * ((m ! : ℕ) : ℚ) * Pj p (-1) m := by
  induction m with
  | zero => simp [Pj]
  | succ m ih =>
    have ih' := ih (by omega)
    have e1 : (p - 1 - m) = (p - 1 - (m + 1)) + 1 := by omega
    have e2 : (((p - 1 - m) ! : ℕ) : ℚ) = ((p : ℚ) - m - 1) * (((p - 1 - (m + 1)) ! : ℕ) : ℚ) := by
      rw [e1, Nat.factorial_succ]
      push_cast
      have : ((p - 1 - (m + 1) : ℕ) : ℚ) = (p : ℚ) - m - 2 := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; ring
    have e3 : Pj p (-1) (m + 1) = Pj p (-1) m * (1 + ((-1 : ℤ) : ℚ) * p * (((m : ℚ) + 1))⁻¹) := by
      unfold Pj; rw [prod_range_succ]
    rw [e3, Nat.factorial_succ]
    rw [ih', e2]
    have : ((m : ℚ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

/-! ## Lemma A: `c_{p+s} Π(-p-s)²` -/

theorem prod_sub_range (N c : ℕ) (hc : c ≤ N) :
    ∏ r ∈ range c, ((N : ℚ) - r) = ((N ! : ℕ) : ℚ) / (((N - c) ! : ℕ) : ℚ) := by
  have h := Nat.factorial_mul_descFactorial hc
  rw [Nat.descFactorial_eq_prod_range] at h
  have hne : (((N - c) ! : ℕ) : ℚ) ≠ 0 := by positivity
  rw [eq_div_iff hne, mul_comm]
  have h' := congrArg (fun x : ℕ => (x : ℚ)) h
  simp only [Nat.cast_mul, Nat.cast_prod] at h'
  rw [← h']
  congr 1
  refine prod_congr rfl fun r hr => ?_
  have := mem_range.1 hr
  rw [Nat.cast_sub (by omega)]

theorem dplus_eval_sq (a k : ℕ) (hk : a ≤ k) :
    ((Dplus a).eval (-(k : ℚ))) ^ 2 = ((((k !) : ℕ) : ℚ) / (((k - a) ! : ℕ) : ℚ)) ^ 2 := by
  have h : (Dplus a).eval (-(k : ℚ)) = (-1) ^ a * ∏ r ∈ range a, ((k : ℚ) - r) := by
    unfold Dplus
    rw [eval_prod]
    simp only [eval_add, eval_X, eval_C]
    have : ∀ r ∈ range a, (-(k : ℚ) + r) = (-1) * ((k : ℚ) - r) := fun r _ => by ring
    rw [prod_congr rfl this, prod_mul_distrib, prod_const, card_range]
  rw [h, mul_pow, ← pow_mul, mul_comm a 2, pow_mul, neg_one_sq, one_pow, one_mul,
    prod_sub_range k a hk]

theorem PiA_sq {a A : ℕ} (hAa : A < a) (k : ℕ) (hk : a ≤ k) :
    ((PiA a A).eval (-(k : ℚ))) ^ 2 =
      ((((k !) : ℕ) : ℚ) / (((k - a) ! : ℕ) : ℚ)) ^ 6 *
        ((((k !) : ℕ) : ℚ) / (((k - (A + 1)) ! : ℕ) : ℚ)) ^ 2 := by
  have h1 := dplus_eval_sq a k hk
  have h2 := dplus_eval_sq (A + 1) k (by omega)
  rw [PiA_eq hAa, eval_mul, eval_pow, mul_pow, ← pow_mul, mul_comm 3 2, pow_mul, h1, h2]
  ring

/-- The unit factor of `c_{p+s} Π(-p-s)²`. -/
noncomputable def ThetaA (p A a s u m : ℕ) : ℚ :=
  Pj p 1 (p - 1) ^ 5 * Pj p 2 A ^ 2 * Pj p 2 u ^ 3 * Pj p 1 s ^ 3 * Pj p (-1) m ^ 2 *
    Pj p (-1) (a - 1) ^ 3 * (Pj p 1 u ^ 6 * Pj p 1 m ^ 2)⁻¹

theorem Band.a_odd {n a A : ℕ} (hB : Band p n a A) : Odd a := by
  have h := hp.out.eq_two_or_odd'
  rcases h with h | ⟨k, hk⟩
  · have := hB.p5; omega
  · exact ⟨k - n, by have := hB.ha; omega⟩

theorem lemmaA {n a A s u m : ℕ} (hB : Band p n a A) (hs2 : s < p) (hu : s = u + a)
    (hm : s = m + A + 1) :
    cc n (p + s) * ((PiA a A).eval (-((p + s : ℕ) : ℚ))) ^ 2 =
      (p : ℚ) ^ 5 * (32 * (((A !) : ℕ) : ℚ) ^ 2 * ((((a - 1) !) : ℕ) : ℚ) ^ 3) *
        (((((s !) : ℕ) : ℚ) / (((u !) : ℕ) : ℚ)) ^ 3) * ThetaA p A a s u m := by
  have hAa := hB.hAa
  have hha := hB.ha
  have hhA := hB.hA
  have hhn := hB.hn
  have hhp5 := hB.p5
  have hk : a ≤ p + s := by omega
  rw [PiA_sq hAa (p + s) hk]
  have e1 : p + s - a = p + u := by omega
  have e2 : p + s - (A + 1) = p + m := by omega
  rw [e1, e2]
  unfold cc
  have c1 := Nat.cast_choose ℚ (show p + s ≤ 6 * n by omega)
  rw [show 6 * n - (p + s) = p - 1 - m by omega, show 6 * n = 2 * p + A from hB.hA] at c1
  have c2 := Nat.cast_choose ℚ (show p + s ≤ 2 * n + (p + s) by omega)
  rw [show 2 * n + (p + s) - (p + s) = p - a by omega,
    show 2 * n + (p + s) = 2 * p + u by omega] at c2
  rw [show 6 * n = 2 * p + A from hB.hA, show 2 * n + (p + s) = 2 * p + u by omega, c1, c2]
  -- factorial expansions
  have fA := fact_2p_add (p := p) A
  have fu := fact_2p_add (p := p) u
  have fs := fact_p_add (p := p) s
  have fpu := fact_p_add (p := p) u
  have fpm := fact_p_add (p := p) m
  have rm := fact_reflect (p := p) m (by omega)
  have ra := fact_reflect (p := p) (a - 1) (by omega)
  rw [show p - 1 - (a - 1) = p - a by omega] at ra
  have hsig : (-1 : ℚ) ^ (a - 1) = 1 := Even.neg_one_pow (by
    obtain ⟨k, hk⟩ := hB.a_odd; exact ⟨k, by omega⟩)
  rw [hsig, mul_one] at ra
  have hsm : ((-1 : ℚ) ^ m) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  -- positivity facts
  have pF1 : (((p - 1) ! : ℕ) : ℚ) ≠ 0 := by positivity
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hpos : ∀ x : ℕ, ((x ! : ℕ) : ℚ) ≠ 0 := fun x => by positivity
  have hq1 : Pj p 1 (p - 1) ≠ 0 := (EJ_pj_ne hB.p5 1 (p - 1) (by omega))
  have hq2 : Pj p 2 A ≠ 0 := (EJ_pj_ne hB.p5 2 A (by omega))
  have hq3 : Pj p 2 u ≠ 0 := (EJ_pj_ne hB.p5 2 u (by omega))
  have hq4 : Pj p 1 s ≠ 0 := (EJ_pj_ne hB.p5 1 s (by omega))
  have hq5 : Pj p (-1) m ≠ 0 := (EJ_pj_ne hB.p5 (-1) m (by omega))
  have hq6 : Pj p (-1) (a - 1) ≠ 0 := (EJ_pj_ne hB.p5 (-1) (a - 1) (by omega))
  have hq7 : Pj p 1 u ≠ 0 := (EJ_pj_ne hB.p5 1 u (by omega))
  have hq8 : Pj p 1 m ≠ 0 := (EJ_pj_ne hB.p5 1 m (by omega))
  have hfm : (((p - 1 - m) ! : ℕ) : ℚ) ^ 2 * (((m ! : ℕ) : ℚ) ^ 2 * Pj p (-1) m ^ 2) =
      (((p - 1) ! : ℕ) : ℚ) ^ 2 := by
    linear_combination (-((((p - 1) ! : ℕ) : ℚ) + (((p - 1 - m) ! : ℕ) : ℚ) * (-1) ^ m * ((m ! : ℕ) : ℚ) *
      Pj p (-1) m)) * rm + (-((((p - 1 - m) ! : ℕ) : ℚ) ^ 2 * (((m ! : ℕ) : ℚ) ^ 2 * Pj p (-1) m ^ 2))) * hsm
  have hfa : (((p - a) ! : ℕ) : ℚ) = (((p - 1) ! : ℕ) : ℚ) / ((((a - 1) !) : ℕ) * Pj p (-1) (a - 1)) := by
    rw [eq_div_iff (mul_ne_zero (hpos _) hq6)]; rw [ra]; ring
  have hfm' : (((p - 1 - m) ! : ℕ) : ℚ) ^ 2 =
      (((p - 1) ! : ℕ) : ℚ) ^ 2 / (((m ! : ℕ) : ℚ) ^ 2 * Pj p (-1) m ^ 2) := by
    rw [eq_div_iff (mul_ne_zero (pow_ne_zero _ (hpos _)) (pow_ne_zero _ hq5))]; exact hfm
  rw [div_pow (((2 * p + A) ! : ℕ) : ℚ), div_pow (((2 * p + u) ! : ℕ) : ℚ), mul_pow, hfm', hfa, fA, fu]
  unfold ThetaA
  rw [show ((p + s) ! : ℕ) = (p + s) ! from rfl, fs, fpu, fpm]
  field_simp
  ring

theorem EJ_Q (hp5 : 5 ≤ p) : EJ p (Pj p 1 (p - 1)) 0 0 := by
  have h := EJ_Pj hp5 1 (p - 1) (by have := hp.out.pos; omega)
  refine h.congr hp5 zero_mem' zero_mem' ?_ ?_
  · simpa using wolstenholme_one hp5
  · have h2 : (-(1 / 2) : ℚ) ∈ LocRing p := by
      have := (LocRing p).neg_mem (two_inv_mem (p := p) (by omega))
      convert this using 1; norm_num
    have := PDv.mul_left h2 (wolstenholme_two hp5)
    convert this using 1; push_cast; ring

theorem thetaA_EJ {n a A s u m : ℕ} (hB : Band p n a A) (hs2 : s < p) (hu : s = u + a)
    (hm : s = m + A + 1) :
    EJ p (ThetaA p A a s u m)
      (4 * harm 1 A - 3 * harm 1 (a - 1) + 3 * harm 1 s - 4 * harm 1 m)
      (-4 * harm 2 A - (3 / 2) * harm 2 (a - 1) - 3 * harm 2 u - (3 / 2) * harm 2 s) := by
  have hAa := hB.hAa
  have hha := hB.ha
  have hp5 := hB.p5
  have hQ := (EJ_Q hp5).pow hp5 5
  have hP2A := (EJ_Pj hp5 2 A (by omega)).pow hp5 2
  have hP2u := (EJ_Pj hp5 2 u (by omega)).pow hp5 3
  have hP1s := (EJ_Pj hp5 1 s (by omega)).pow hp5 3
  have hPm := (EJ_Pj hp5 (-1) m (by omega)).pow hp5 2
  have hPa := (EJ_Pj hp5 (-1) (a - 1) (by omega)).pow hp5 3
  have hD := ((EJ_Pj hp5 1 u (by omega)).pow hp5 6).mul hp5 ((EJ_Pj hp5 1 m (by omega)).pow hp5 2)
  have h := (((((hQ.mul hp5 hP2A).mul hp5 hP2u).mul hp5 hP1s).mul hp5 hPm).mul hp5 hPa).mul hp5
    (hD.inv hp5)
  unfold ThetaA
  convert h using 1
  · push_cast; ring
  · push_cast; ring

/-! ## `p`-adic expansions of harmonic numbers beyond `p` -/

theorem harm_add (r x y : ℕ) :
    harm r (x + y) = harm r x + ∑ i ∈ range y, ((((x + i : ℕ) : ℚ) + 1) ^ r)⁻¹ := by
  unfold harm
  rw [sum_range_add]

theorem term_exp (c : ℤ) {i : ℕ} (h0 : 0 < i) (hi : i < p) :
    PDv p 2 (((i : ℚ) + c * p)⁻¹ - ((i : ℚ)⁻¹ - c * p * ((i : ℚ)⁻¹) ^ 2)) := by
  obtain ⟨w, hw, e⟩ := inv_expand c h0 hi
  exact ⟨w, hw, by rw [e]; ring⟩

theorem term_exp3 (c : ℤ) {i : ℕ} (h0 : 0 < i) (hi : i < p) :
    PDv p 3 ((p : ℚ) * ((i : ℚ) + c * p)⁻¹ - ((p : ℚ) * (i : ℚ)⁻¹ - c * p ^ 2 * ((i : ℚ)⁻¹) ^ 2)) := by
  obtain ⟨w, hw, e⟩ := inv_expand c h0 hi
  exact ⟨w, hw, by rw [e]; ring⟩

/-- `p H_{jp + x}` for `j = 1, 2`: the tail sum. -/
theorem sum_tail (j : ℤ) (x : ℕ) (hx : x < p) :
    PDv p 3 (∑ i ∈ range x, (p : ℚ) * ((((i + 1 : ℕ) : ℚ)) + j * p)⁻¹ -
      ((p : ℚ) * harm 1 x - j * p ^ 2 * harm 2 x)) := by
  have h := PDv.sum (p := p) (range x) (fun i => (p : ℚ) * ((((i + 1 : ℕ) : ℚ)) + j * p)⁻¹ -
      ((p : ℚ) * (((i + 1 : ℕ) : ℚ))⁻¹ - j * p ^ 2 * ((((i + 1 : ℕ) : ℚ))⁻¹) ^ 2)) (fun i hi =>
    term_exp3 j (Nat.succ_pos i) (by have := mem_range.1 hi; omega))
  convert h using 1
  rw [sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
  unfold harm
  have e1 : ∀ i ∈ range x, ((((i + 1 : ℕ) : ℚ))⁻¹) = (((i : ℚ) + 1) ^ 1)⁻¹ := fun i _ => by simp
  have e2 : ∀ i ∈ range x, (((((i + 1 : ℕ) : ℚ))⁻¹) ^ 2) = (((i : ℚ) + 1) ^ 2)⁻¹ := fun i _ => by
    simp [inv_pow]
  rw [sum_congr rfl e1, sum_congr rfl e2]

theorem pH_p_add (x : ℕ) (hx : x < p) (hp5 : 5 ≤ p) :
    PDv p 3 ((p : ℚ) * harm 1 (p + x) - (1 + p * harm 1 x - p ^ 2 * harm 2 x)) := by
  have hp1 : p - 1 + 1 = p := by have := hp.out.pos; omega
  have e : harm 1 p = harm 1 (p - 1) + (p : ℚ)⁻¹ := by
    have := harm_succ 1 (p - 1)
    rw [hp1] at this
    rw [this]
    have : ((p - 1 : ℕ) : ℚ) + 1 = p := by rw [Nat.cast_sub hp.out.one_le]; ring
    rw [this]; simp
  have e2 : (p : ℚ) * harm 1 (p + x) = (p : ℚ) * harm 1 (p - 1) + 1 +
      ∑ i ∈ range x, (p : ℚ) * ((((i + 1 : ℕ) : ℚ)) + (1 : ℤ) * p)⁻¹ := by
    rw [harm_add, e, mul_add, mul_add, mul_sum]
    have hpq : (p : ℚ) ≠ 0 := p_ne_zero
    rw [mul_inv_cancel₀ hpq]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    push_cast; ring_nf
  rw [e2]
  have h1 := sum_tail (p := p) 1 x hx
  have h2 : PDv p 3 ((p : ℚ) * harm 1 (p - 1)) := by
    have := PDv.mul (j := 1) (k := 2) pPDv_one (wolstenholme_one hp5)
    simpa using this
  have := h2.add h1
  convert this using 1
  push_cast; ring

theorem pH_2p_add (x : ℕ) (hx : x < p) (hp5 : 5 ≤ p) :
    PDv p 3 ((p : ℚ) * harm 1 (2 * p + x) - (3 / 2 + p * harm 1 x - 2 * p ^ 2 * harm 2 x)) := by
  have hp1 : p - 1 + 1 = p := by have := hp.out.pos; omega
  have hpq : (p : ℚ) ≠ 0 := p_ne_zero
  have e0 : harm 1 p = harm 1 (p - 1) + (p : ℚ)⁻¹ := by
    have := harm_succ 1 (p - 1)
    rw [hp1] at this
    rw [this]
    have : ((p - 1 : ℕ) : ℚ) + 1 = p := by rw [Nat.cast_sub hp.out.one_le]; ring
    rw [this]; simp
  have e1 : harm 1 (2 * p) = harm 1 p + ∑ i ∈ range (p - 1), ((((p + i : ℕ) : ℚ) + 1) ^ 1)⁻¹ +
      ((2 : ℚ) * p)⁻¹ := by
    rw [show 2 * p = p + p by ring, harm_add]
    have hs := sum_range_succ (fun i : ℕ => ((((p + i : ℕ) : ℚ) + 1) ^ 1)⁻¹) (p - 1)
    rw [hp1] at hs
    have hL : ((((p + (p - 1) : ℕ) : ℚ) + 1) ^ 1)⁻¹ = ((2 : ℚ) * p)⁻¹ := by
      rw [pow_one]; congr 1
      rw [Nat.cast_add, Nat.cast_sub hp.out.one_le]; push_cast; ring
    rw [hs, hL]; ring
  have e2 : harm 1 (2 * p + x) = harm 1 (2 * p) + ∑ i ∈ range x, ((((2 * p + i : ℕ) : ℚ) + 1) ^ 1)⁻¹ :=
    harm_add 1 (2 * p) x
  have t1 := sum_tail (p := p) 1 (p - 1) (by omega)
  have t2 := sum_tail (p := p) 2 x hx
  have hw := wolstenholme_one hp5
  have hw2 := wolstenholme_two hp5
  have h1 : PDv p 3 ((p : ℚ) * harm 1 (p - 1)) := by
    have := PDv.mul (j := 1) (k := 2) pPDv_one hw; simpa using this
  have h2 : PDv p 3 ((p : ℚ) ^ 2 * harm 2 (p - 1)) := by
    have := PDv.mul (j := 2) (k := 1) (⟨1, one_mem', by simp⟩ : PDv p 2 ((p : ℚ) ^ 2)) hw2
    simpa using this
  have S1 : ∑ i ∈ range (p - 1), (p : ℚ) * ((((i + 1 : ℕ) : ℚ)) + (1 : ℤ) * p)⁻¹ =
      ∑ i ∈ range (p - 1), (p : ℚ) * ((((p + i : ℕ) : ℚ) + 1) ^ 1)⁻¹ := by
    refine sum_congr rfl fun i _ => ?_
    push_cast; ring_nf
  have S2 : ∑ i ∈ range x, (p : ℚ) * ((((i + 1 : ℕ) : ℚ)) + (2 : ℤ) * p)⁻¹ =
      ∑ i ∈ range x, (p : ℚ) * ((((2 * p + i : ℕ) : ℚ) + 1) ^ 1)⁻¹ := by
    refine sum_congr rfl fun i _ => ?_
    push_cast; ring_nf
  rw [S1] at t1; rw [S2] at t2
  have key : (p : ℚ) * harm 1 (2 * p + x) = (p : ℚ) * harm 1 (p - 1) + 1 +
      ∑ i ∈ range (p - 1), (p : ℚ) * ((((p + i : ℕ) : ℚ) + 1) ^ 1)⁻¹ + 1 / 2 +
      ∑ i ∈ range x, (p : ℚ) * ((((2 * p + i : ℕ) : ℚ) + 1) ^ 1)⁻¹ := by
    rw [e2, e1, e0]
    simp only [mul_add, ← mul_sum]
    field_simp
  rw [key]
  convert (PDv.sub (PDv.add (PDv.add (PDv.add h1 h1) t1) t2) h2) using 1
  push_cast
  ring

theorem pH_pm1 (x : ℕ) (hx : x ≤ p - 1) (hp5 : 5 ≤ p) :
    PDv p 3 ((p : ℚ) * harm 1 (p - 1 - x) - (p * harm 1 x + p ^ 2 * harm 2 x)) := by
  have hp1 : p - 1 - x + x = p - 1 := by omega
  have h0 := harm_add 1 (p - 1 - x) x
  rw [hp1] at h0
  have hrefl := sum_range_reflect (fun i : ℕ => ((((p - 1 - x + i : ℕ) : ℚ) + 1) ^ 1)⁻¹) x
  have hterm : ∀ i ∈ range x, ((((p - 1 - x + (x - 1 - i) : ℕ) : ℚ) + 1) ^ 1)⁻¹ =
      -((((i + 1 : ℕ) : ℚ)) + ((-1 : ℤ) : ℚ) * p)⁻¹ := by
    intro i hi
    have hi' := mem_range.1 hi
    have e : (p - 1 - x + (x - 1 - i) : ℕ) = p - 2 - i := by omega
    have e2 : (((p - 2 - i : ℕ) : ℚ) + 1) = (p : ℚ) - (((i + 1 : ℕ) : ℚ)) := by
      have : ((p - 2 - i : ℕ) : ℚ) = (p : ℚ) - 2 - i := by
        rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; push_cast; ring
    rw [e, e2, pow_one]
    have : (((i + 1 : ℕ) : ℚ)) + ((-1 : ℤ) : ℚ) * p = -((p : ℚ) - (((i + 1 : ℕ) : ℚ))) := by push_cast; ring
    rw [this, ← inv_neg, neg_neg]
  have hsum : ∑ i ∈ range x, ((((p - 1 - x + i : ℕ) : ℚ) + 1) ^ 1)⁻¹ =
      -∑ i ∈ range x, ((((i + 1 : ℕ) : ℚ)) + ((-1 : ℤ) : ℚ) * p)⁻¹ := by
    rw [← hrefl, sum_congr rfl hterm, sum_neg_distrib]
  have e : harm 1 (p - 1 - x) = harm 1 (p - 1) + ∑ i ∈ range x, ((((i + 1 : ℕ) : ℚ)) + ((-1 : ℤ) : ℚ) * p)⁻¹ := by
    have : harm 1 (p - 1) = harm 1 (p - 1 - x) - ∑ i ∈ range x, ((((i + 1 : ℕ) : ℚ)) + ((-1 : ℤ) : ℚ) * p)⁻¹ := by
      rw [h0, hsum]; ring
    linarith
  have t := sum_tail (p := p) (-1) x (by omega)
  have hw : PDv p 3 ((p : ℚ) * harm 1 (p - 1)) := by
    have := PDv.mul (j := 1) (k := 2) pPDv_one (wolstenholme_one hp5); simpa using this
  rw [e, mul_add, mul_sum]
  convert hw.add t using 1
  push_cast; ring

theorem harm_split (r N : ℕ) : ∀ c, c ≤ N →
    harm r N = harm r (N - c) + ∑ i ∈ range c, ((((N : ℚ) - i)) ^ r)⁻¹ := by
  intro c
  induction c with
  | zero => intro _; simp
  | succ c ih =>
    intro hc
    have h1 := ih (by omega)
    have h2 : N - c = (N - (c + 1)) + 1 := by omega
    have h3 := harm_succ r (N - (c + 1))
    rw [← h2] at h3
    have h4 : ((N - (c + 1) : ℕ) : ℚ) + 1 = (N : ℚ) - c := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [h4] at h3
    rw [h1, h3, sum_range_succ]; ring

/-- `H^{(r)}_{p+x} = p^{-r} + (integral)`. -/
theorem harm_p_add (r x : ℕ) (hr : 1 ≤ r) (hx : x < p) :
    ∃ h : ℚ, h ∈ LocRing p ∧ harm r (p + x) = ((p : ℚ) ^ r)⁻¹ + h := by
  have hp1 : p - 1 + 1 = p := by have := hp.out.pos; omega
  have e : harm r p = harm r (p - 1) + ((p : ℚ) ^ r)⁻¹ := by
    have := harm_succ r (p - 1)
    rw [hp1] at this
    rw [this]
    have : ((p - 1 : ℕ) : ℚ) + 1 = p := by rw [Nat.cast_sub hp.out.one_le]; ring
    rw [this]
  refine ⟨harm r (p - 1) + ∑ i ∈ range x, ((((p + i : ℕ) : ℚ) + 1) ^ r)⁻¹, ?_, ?_⟩
  · refine (LocRing p).add_mem (harm_mem (by omega)) ((LocRing p).sum_mem fun i hi => ?_)
    have hi' := mem_range.1 hi
    have : ((((p + i : ℕ) : ℚ) + 1)) = ((p + i + 1 : ℕ) : ℚ) := by push_cast; ring
    rw [this, ← inv_pow]
    refine (LocRing p).pow_mem (inv_natCast_mem_locRing ?_) r
    intro hd
    have : p ∣ i + 1 := (Nat.dvd_add_right (dvd_refl p)).1 (by rwa [show p + (i + 1) = p + i + 1 by ring])
    exact absurd (Nat.le_of_dvd (Nat.succ_pos i) this) (by omega)
  · rw [harm_add, e]; ring

/-! ## The data at the nodes `k = p + s`, `s ∈ [a, p)` -/

/-- `∑_{i<c} (s - i)^{-r}`. -/
noncomputable def dsum (c r s : ℕ) : ℚ := ∑ i ∈ range c, ((((s : ℚ) - i)) ^ r)⁻¹

theorem dsum_mem {c r s : ℕ} (hc : c ≤ s) (hs : s < p) : dsum c r s ∈ LocRing p := by
  unfold dsum
  refine (LocRing p).sum_mem fun i hi => ?_
  have hi' := mem_range.1 hi
  have : ((s : ℚ) - i) = ((s - i : ℕ) : ℚ) := by rw [Nat.cast_sub (by omega)]
  rw [this, ← inv_pow]
  exact (LocRing p).pow_mem (inv_mem_of_lt (by omega) (by omega)) r

theorem dsum_expand {c s : ℕ} (hc : c ≤ s) (hs : s < p) :
    PDv p 2 (dsum c 1 (p + s) - (dsum c 1 s - p * dsum c 2 s)) := by
  have h := PDv.sum (p := p) (range c) (fun i => ((((s - i : ℕ) : ℚ)) + ((1 : ℤ) : ℚ) * p)⁻¹ -
      ((((s - i : ℕ) : ℚ))⁻¹ - ((1 : ℤ) : ℚ) * p * ((((s - i : ℕ) : ℚ))⁻¹) ^ 2)) (fun i hi =>
    term_exp 1 (by have := mem_range.1 hi; omega) (by omega))
  convert h using 1
  unfold dsum
  rw [mul_sum, ← sum_sub_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hi' := mem_range.1 hi
  have e1 : ((((p + s : ℕ) : ℚ)) - i) = (((s - i : ℕ) : ℚ)) + ((1 : ℤ) : ℚ) * p := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : ((s : ℚ) - i) = (((s - i : ℕ) : ℚ)) := by rw [Nat.cast_sub (by omega)]
  rw [e1, e2]
  simp only [pow_one, inv_pow]
  push_cast; ring

section NodeB

variable {n a A s u m : ℕ}

theorem harm_m_eq (hs2 : s < p) (hu : s = u + a) (hm : s = m + A + 1) (hAa : A < a) :
    harm 1 u = harm 1 s - dsum a 1 s ∧ harm 1 m = harm 1 s - dsum (A + 1) 1 s ∧
    harm 2 u = harm 2 s - dsum a 2 s ∧ harm 2 m = harm 2 s - dsum (A + 1) 2 s := by
  have h1 := harm_split 1 s a (by omega)
  have h2 := harm_split 1 s (A + 1) (by omega)
  have h3 := harm_split 2 s a (by omega)
  have h4 := harm_split 2 s (A + 1) (by omega)
  rw [show s - a = u by omega] at h1 h3
  rw [show s - (A + 1) = m by omega] at h2 h4
  unfold dsum
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- `p d_{p+s} ≡ 1/2 + p λ₀ + p² δ₁ (mod p³)`, in the atoms `dsum`. -/
theorem D_expand (hB : Band p n a A) (hs2 : s < p) (hu : s = u + a) (hm : s = m + A + 1) :
    PDv p 3 ((p : ℚ) * dd n (p + s) -
      (1 / 2 + p * (3 * dsum a 1 s + 2 * dsum (A + 1) 1 s) +
        p ^ 2 * (-harm 2 s - 6 * dsum a 2 s + 2 * dsum (A + 1) 2 s))) := by
  have hha := hB.ha
  have hhA := hB.hA
  have hAa := hB.hAa
  have hp5 := hB.p5
  obtain ⟨hq1, hq2, hq3, hq4⟩ := harm_m_eq (p := p) hs2 hu hm hAa
  unfold dd
  rw [show 2 * n + (p + s) = 2 * p + u by omega, show 6 * n - (p + s) = p - 1 - m by omega]
  have t1 := pH_p_add (p := p) s hs2 hp5
  have t2 := pH_2p_add (p := p) u (by omega) hp5
  have t3 := pH_pm1 (p := p) m (by omega) hp5
  have n5 : ((5 : ℕ) : ℚ) ∈ LocRing p := natCast_mem 5
  have n3 : ((3 : ℕ) : ℚ) ∈ LocRing p := natCast_mem 3
  have n2 : ((2 : ℕ) : ℚ) ∈ LocRing p := natCast_mem 2
  have := ((PDv.mul_left n5 t1).sub (PDv.mul_left n3 t2)).sub (PDv.mul_left n2 t3)
  convert this using 1
  rw [hq1, hq2, hq3, hq4]
  push_cast
  ring

theorem p4V_expand (hB : Band p n a A) (hs1 : a ≤ s) (hs2 : s < p) (hu : s = u + a)
    (hm : s = m + A + 1) :
    ∃ h3 r : ℚ, h3 ∈ LocRing p ∧ r ∈ LocRing p ∧
      (p : ℚ) ^ 4 * harm 3 (p + s) = p + p ^ 4 * h3 ∧
      (p : ℚ) ^ 4 * (-2 * harm 3 (p + s) * dd n (p + s) - 6 * harm 4 (p + s)) =
        -7 - 2 * p * (3 * dsum a 1 s + 2 * dsum (A + 1) 1 s) -
          2 * p ^ 2 * (-harm 2 s - 6 * dsum a 2 s + 2 * dsum (A + 1) 2 s) + p ^ 3 * r := by
  have hAa := hB.hAa
  have hp5 := hB.p5
  have hpq : (p : ℚ) ≠ 0 := p_ne_zero
  obtain ⟨h3, hh3, e3⟩ := harm_p_add (p := p) 3 s (by norm_num) hs2
  obtain ⟨h4, hh4, e4⟩ := harm_p_add (p := p) 4 s (by norm_num) hs2
  obtain ⟨w, hw, ew⟩ := D_expand hB hs2 hu hm
  have hs' : harm 2 s ∈ LocRing p := harm_mem hs2
  have hd1 := dsum_mem (p := p) (c := a) (r := 1) hs1 hs2
  have hd2 := dsum_mem (p := p) (c := a) (r := 2) hs1 hs2
  have hd3 := dsum_mem (p := p) (c := A + 1) (r := 1) (by omega) hs2
  have hd4 := dsum_mem (p := p) (c := A + 1) (r := 2) (by omega) hs2
  have h2i : (2 : ℚ)⁻¹ ∈ LocRing p := two_inv_mem (by omega)
  have hpm : (p : ℚ) ∈ LocRing p := p_mem
  have hM : (1 / 2 + p * (3 * dsum a 1 s + 2 * dsum (A + 1) 1 s) +
        p ^ 2 * (-harm 2 s - 6 * dsum a 2 s + 2 * dsum (A + 1) 2 s)) ∈ LocRing p := by
    have : (1 / 2 : ℚ) = 2⁻¹ := by norm_num
    rw [this]; rmem
  generalize hMd : (1 / 2 + p * (3 * dsum a 1 s + 2 * dsum (A + 1) 1 s) +
        p ^ 2 * (-harm 2 s - 6 * dsum a 2 s + 2 * dsum (A + 1) 2 s) : ℚ) = M at ew hM
  refine ⟨h3, -2 * w - 2 * h3 * M - 2 * p ^ 3 * h3 * w - 6 * p * h4, hh3, by rmem, ?_, ?_⟩
  · rw [e3]; field_simp
  · have e4' : (p : ℚ) ^ 4 * harm 4 (p + s) = 1 + p ^ 4 * h4 := by rw [e4]; field_simp
    have e3' : (p : ℚ) ^ 4 * harm 3 (p + s) = p + p ^ 4 * h3 := by rw [e3]; field_simp
    have key : (p : ℚ) ^ 4 * (-2 * harm 3 (p + s) * dd n (p + s) - 6 * harm 4 (p + s)) =
        -2 * (p ^ 4 * harm 3 (p + s)) * dd n (p + s) - 6 * (p ^ 4 * harm 4 (p + s)) := by ring
    rw [key, e3', e4']
    linear_combination (-2 * (1 + p ^ 3 * h3)) * ew + 2 * hMd

end NodeB

section NodeB2

variable {n a A s u m : ℕ}

/-- `B_{p+s} = p⁴ [(V + 4 H³ Λ) ψ(k) + 2 H³ ψ'(k)]`, grouped as in the proof. -/
noncomputable def Bk (n a A s : ℕ) (ψ : ℚ[X]) : ℚ :=
  ((p : ℚ) ^ 4 * (-2 * harm 3 (p + s) * dd n (p + s) - 6 * harm 4 (p + s))) * ψ.eval ((p + s : ℕ) : ℚ) +
    4 * ((p : ℚ) ^ 4 * harm 3 (p + s)) * (3 * dsum a 1 (p + s) + dsum (A + 1) 1 (p + s)) *
      ψ.eval ((p + s : ℕ) : ℚ) +
    2 * ((p : ℚ) ^ 4 * harm 3 (p + s)) * (derivative ψ).eval ((p + s : ℕ) : ℚ)

/-- The truncation `b₀ + p b₁ + p² b₂`. -/
noncomputable def bTrunc (a A s : ℕ) (ψ : ℚ[X]) : ℚ :=
  -7 * ψ.eval (s : ℚ) +
    p * (-5 * (derivative ψ).eval (s : ℚ) + 6 * dsum a 1 s * ψ.eval (s : ℚ)) +
    p ^ 2 * (-(3 / 2) * (derivative (derivative ψ)).eval (s : ℚ) +
      6 * dsum a 1 s * (derivative ψ).eval (s : ℚ) +
      (2 * harm 2 s - 8 * dsum (A + 1) 2 s) * ψ.eval (s : ℚ))

theorem B_expand (hB : Band p n a A) (hs1 : a ≤ s) (hs2 : s < p) (hu : s = u + a)
    (hm : s = m + A + 1) {ψ : ℚ[X]} (hψ : PInt p ψ) :
    PDv p 3 (Bk (p := p) n a A s ψ - bTrunc (p := p) a A s ψ) := by
  have hAa := hB.hAa
  have hp5 := hB.p5
  obtain ⟨h3, r, hh3, hr, e3, e4V⟩ := p4V_expand hB hs1 hs2 hu hm
  obtain ⟨c1, hc1, ec1⟩ := dsum_expand (p := p) (c := a) hs1 hs2
  obtain ⟨c2, hc2, ec2⟩ := dsum_expand (p := p) (c := A + 1) (by omega) hs2
  obtain ⟨z, hz, ez⟩ := taylor_pdv hψ (natCast_mem (p := p) s)
  obtain ⟨z', hz', ez'⟩ := taylor_pdv hψ.derivative (natCast_mem (p := p) s)
  have h2i : (2 : ℚ)⁻¹ ∈ LocRing p := two_inv_mem (by omega)
  have hpm : (p : ℚ) ∈ LocRing p := p_mem
  have hd1 := dsum_mem (p := p) (c := a) (r := 1) hs1 hs2
  have hd2 := dsum_mem (p := p) (c := a) (r := 2) hs1 hs2
  have hd3 := dsum_mem (p := p) (c := A + 1) (r := 1) (by omega) hs2
  have hd4 := dsum_mem (p := p) (c := A + 1) (r := 2) (by omega) hs2
  have hH2 : harm 2 s ∈ LocRing p := harm_mem hs2
  have hps0 := hψ.eval_nat (p := p) s
  have hps1 := hψ.derivative.eval_nat (p := p) s
  have hps2 := hψ.derivative.derivative.eval_nat (p := p) s
  have hps3 := hψ.derivative.derivative.derivative.eval_nat (p := p) s
  unfold Bk bTrunc
  have hk : ((p + s : ℕ) : ℚ) = (s : ℚ) + p := by push_cast; ring
  rw [e4V, e3, hk, ez, ez']
  have hL : 3 * dsum a 1 (p + s) + dsum (A + 1) 1 (p + s) =
      (3 * dsum a 1 s + dsum (A + 1) 1 s) - p * (3 * dsum a 2 s + dsum (A + 1) 2 s) +
        p ^ 2 * (3 * c1 + c2) := by linear_combination 3 * ec1 + ec2
  rw [hL]
  set ps0 := ψ.eval (s : ℚ)
  set ps1 := (derivative ψ).eval (s : ℚ)
  set ps2 := (derivative (derivative ψ)).eval (s : ℚ)
  set ps3 := (derivative (derivative (derivative ψ))).eval (s : ℚ)
  refine ⟨2 * (ps3 * 2⁻¹ + p * z') + (-7) * z + 4 * ps0 * (3 * c1 + c2) + 1 * ps0 * r + (-8) * (dsum (A + 1) 2 s) * ps1 + 3 * (dsum a 1 s) * ps2 + 2 * (harm 2 s) * ps1 + 4 * (p : ℚ) * ps1 * (3 * c1 + c2) + 2 * (p : ℚ) * ps1 * h3 + 1 * (p : ℚ) * ps1 * r + (-4) * (p : ℚ) * (dsum (A + 1) 2 s) * ps2 + 4 * (p : ℚ) * (dsum (A + 1) 1 s) * ps0 * h3 + 6 * (p : ℚ) * (dsum a 1 s) * z + 12 * (p : ℚ) * (dsum a 1 s) * ps0 * h3 + 1 * (p : ℚ) * (harm 2 s) * ps2 + 2 * (p : ℚ)^2 * ps2 * (3 * c1 + c2) + 2 * (p : ℚ)^2 * ps2 * h3 + (1 * 2⁻¹) * (p : ℚ)^2 * ps2 * r + (-8) * (p : ℚ)^2 * (dsum (A + 1) 2 s) * z + (-4) * (p : ℚ)^2 * (dsum (A + 1) 2 s) * ps0 * h3 + (-12) * (p : ℚ)^2 * (dsum a 2 s) * ps0 * h3 + 4 * (p : ℚ)^2 * (dsum (A + 1) 1 s) * ps1 * h3 + 12 * (p : ℚ)^2 * (dsum a 1 s) * ps1 * h3 + 2 * (p : ℚ)^2 * (harm 2 s) * z + 4 * (p : ℚ)^3 * (3 * c1 + c2) * z + 2 * (p : ℚ)^3 * h3 * (ps3 * 2⁻¹ + p * z') + 1 * (p : ℚ)^3 * r * z + 4 * (p : ℚ)^3 * ps0 * h3 * (3 * c1 + c2) + (-4) * (p : ℚ)^3 * (dsum (A + 1) 2 s) * ps1 * h3 + (-12) * (p : ℚ)^3 * (dsum a 2 s) * ps1 * h3 + 2 * (p : ℚ)^3 * (dsum (A + 1) 1 s) * ps2 * h3 + 6 * (p : ℚ)^3 * (dsum a 1 s) * ps2 * h3 + 4 * (p : ℚ)^4 * ps1 * h3 * (3 * c1 + c2) + (-2) * (p : ℚ)^4 * (dsum (A + 1) 2 s) * ps2 * h3 + (-6) * (p : ℚ)^4 * (dsum a 2 s) * ps2 * h3 + 4 * (p : ℚ)^4 * (dsum (A + 1) 1 s) * h3 * z + 12 * (p : ℚ)^4 * (dsum a 1 s) * h3 * z + 2 * (p : ℚ)^5 * ps2 * h3 * (3 * c1 + c2) + (-4) * (p : ℚ)^5 * (dsum (A + 1) 2 s) * h3 * z + (-12) * (p : ℚ)^5 * (dsum a 2 s) * h3 * z + 4 * (p : ℚ)^6 * h3 * (3 * c1 + c2) * z, ?_, ?_⟩
  · rmem
  · ring

end NodeB2

/-! ## The node term `E_k f(-k) + U_k f'(-k)` for `f = Π² ph` -/

theorem dplus_logder (c : ℕ) (x : ℚ) (hx : ∀ r < c, x + r ≠ 0) :
    (derivative (Dplus c)).eval x = (Dplus c).eval x * ∑ r ∈ range c, (x + r)⁻¹ := by
  induction c with
  | zero => simp [Dplus]
  | succ c ih =>
    have h1 := ih (fun r hr => hx r (by omega))
    have hne : x + c ≠ 0 := hx c (by omega)
    have e : Dplus (c + 1) = Dplus c * (X + C (c : ℚ)) := by
      unfold Dplus; rw [prod_range_succ]
    rw [e]
    simp only [derivative_mul, derivative_add, derivative_X, derivative_C, add_zero, eval_add, eval_mul,
      eval_one, eval_X, eval_C]
    rw [h1, sum_range_succ]
    field_simp

theorem PiA_logder {a A : ℕ} (hAa : A < a) (x : ℚ) (hx : ∀ r < a, x + r ≠ 0) :
    (derivative (PiA a A)).eval x = (PiA a A).eval x *
      (3 * ∑ r ∈ range a, (x + r)⁻¹ + ∑ r ∈ range (A + 1), (x + r)⁻¹) := by
  rw [PiA_eq hAa, derivative_mul, derivative_pow, eval_add, eval_mul, eval_mul, eval_mul, eval_mul, eval_pow,
    eval_pow, dplus_logder a x hx, dplus_logder (A + 1) x (fun r hr => hx r (by omega))]
  simp only [eval_mul, eval_pow, eval_C, eval_natCast]
  push_cast
  ring

theorem dfall_eval (a s : ℕ) (hs : a ≤ s) :
    (Dfall a).eval (s : ℚ) = ((s ! : ℕ) : ℚ) / (((s - a) ! : ℕ) : ℚ) := by
  unfold Dfall
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  exact prod_sub_range s a hs

theorem PInt.dfall (a : ℕ) : PInt p (Dfall a) := by
  unfold Dfall
  exact PInt.prod _ _ fun r _ => PInt.X_sub_C (by exact_mod_cast int_mem_locRing (ℓ := p) (r : ℤ))

theorem PInt.dplus (a : ℕ) : PInt p (Dplus a) := by
  unfold Dplus
  exact PInt.prod _ _ fun r _ => PInt.X_add_C (by exact_mod_cast int_mem_locRing (ℓ := p) (r : ℤ))

theorem PInt.piA {a A : ℕ} (h : A < a) : PInt p (PiA a A) := by
  rw [PiA_eq h]
  exact ((PInt.dplus a).pow 3).mul (PInt.dplus (A + 1))

theorem PInt.comp_neg {g : ℚ[X]} (hg : PInt p g) : PInt p (g.comp (-X)) := fun i => by
  rw [coeff_comp_neg_X]
  exact (LocRing p).mul_mem (by rcases neg_one_pow_eq_or ℚ i with h | h <;> rw [h] <;> rmem) (hg i)

/-- `τ_k := E_k f(-k) + U_k f'(-k)` for `f = Π² ph`. -/
noncomputable def tauK (n a A : ℕ) (ph : ℚ[X]) (k : ℕ) : ℚ :=
  EE n k * ((PiA a A ^ 2) * ph).eval (-(k : ℚ)) +
    UU n k * (derivative ((PiA a A ^ 2) * ph)).eval (-(k : ℚ))

theorem tau_formula {a A : ℕ} (n : ℕ) (hAa : A < a) (k : ℕ) (hk : a ≤ k) (ph : ℚ[X]) :
    tauK n a A ph k = cc n k * ((PiA a A).eval (-(k : ℚ))) ^ 2 *
      (((-2 * harm 3 k * dd n k - 6 * harm 4 k) +
          4 * harm 3 k * (3 * dsum a 1 k + dsum (A + 1) 1 k)) * (ph.comp (-X)).eval (k : ℚ) +
        2 * harm 3 k * (derivative (ph.comp (-X))).eval (k : ℚ)) := by
  have hne : ∀ r < a, -(k : ℚ) + r ≠ 0 := fun r hr => by
    have : (r : ℚ) < k := by exact_mod_cast (by omega : r < k)
    linarith
  have hl := PiA_logder hAa (-(k : ℚ)) hne
  have hs1 : ∑ r ∈ range a, (-(k : ℚ) + r)⁻¹ = -dsum a 1 k := by
    unfold dsum
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [pow_one, ← inv_neg]; congr 1; ring
  have hs2 : ∑ r ∈ range (A + 1), (-(k : ℚ) + r)⁻¹ = -dsum (A + 1) 1 k := by
    unfold dsum
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun r _ => ?_
    rw [pow_one, ← inv_neg]; congr 1; ring
  rw [hs1, hs2] at hl
  have hψ : (ph.comp (-X)).eval (k : ℚ) = ph.eval (-(k : ℚ)) := by simp [eval_comp]
  have hψ' : (derivative (ph.comp (-X))).eval (k : ℚ) = -(derivative ph).eval (-(k : ℚ)) := by
    rw [derivative_comp]; simp [eval_comp]
  rw [hψ, hψ']
  unfold tauK EE UU
  rw [derivative_mul, derivative_pow]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_natCast, derivative_X, derivative_C]
  rw [hl]
  push_cast
  ring


/-! ## The node term mod `p⁴` -/

/-- The 17-coefficient table of Lemma G3 (G = Ω ψ, W₁ = Ω ψ', W₂ = Ω ψ''). -/
noncomputable def TabF (p H1 H2 dN1 dA1 dN2 dA2 Om ps0 ps1 ps2 : ℚ) : ℚ :=
  -7 * (Om * ps0) +
    p * (-5 * (Om * ps1) + 7 * (Om * ps0) * H1 - 28 * (Om * ps0) * dA1 + 6 * (Om * ps0) * dN1) +
    p ^ 2 * (-(3 * 2⁻¹) * (Om * ps2) - (7 * 2⁻¹) * (Om * ps0) * H1 ^ 2 + (67 * 2⁻¹) * (Om * ps0) * H2 -
      56 * (Om * ps0) * dA1 ^ 2 - 8 * (Om * ps0) * dA2 - 21 * (Om * ps0) * dN2 + 5 * H1 * (Om * ps1) -
      20 * (Om * ps1) * dA1 + 6 * (Om * ps1) * dN1 + 28 * (Om * ps0) * H1 * dA1 -
      6 * (Om * ps0) * H1 * dN1 + 24 * (Om * ps0) * dA1 * dN1)

/-- `E(α, β) = 1 + pα + p²(β + α²/2)`. -/
noncomputable def Ejet (p α β : ℚ) : ℚ := 1 + p * α + p ^ 2 * (β + α ^ 2 * 2⁻¹)

theorem Ejet_EJ (hp5 : 5 ≤ p) {α β : ℚ} (ha : α ∈ LocRing p) (hb : β ∈ LocRing p) :
    EJ p (Ejet p α β) α β := by
  have h2 : (2 : ℚ)⁻¹ ∈ LocRing p := two_inv_mem (by omega)
  have hpm : (p : ℚ) ∈ LocRing p := p_mem
  refine ⟨?_, ha, hb, ?_⟩
  · unfold Ejet; rmem
  · have : Ejet p α β - (1 + p * α + p ^ 2 * (β + α ^ 2 / 2)) = 0 := by unfold Ejet; ring
    rw [this]; exact PDv.zero 3

theorem EJ_unique {x y α β : ℚ} (hx : EJ p x α β) (hy : EJ p y α β) : PDv p 3 (x - y) := by
  have := hx.2.2.2.sub hy.2.2.2
  convert this using 1; ring

section NodeT

variable {n a A s u m : ℕ}

set_option maxHeartbeats 4000000 in
theorem node_term (hB : Band p n a A) (hs1 : a ≤ s) (hs2 : s < p) (hu : s = u + a)
    (hm : s = m + A + 1) {ph : ℚ[X]} (hph : PInt p ph) :
    PDv p 4 (tauK n a A ph (p + s) -
      (p : ℚ) * (32 * (((A !) : ℕ) : ℚ) ^ 2 * ((((a - 1) !) : ℕ) : ℚ) ^ 3) *
        Ejet p (4 * harm 1 A - 3 * harm 1 (a - 1)) (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) *
        TabF p (harm 1 s) (harm 2 s) (dsum a 1 s) (dsum (A + 1) 1 s) (dsum a 2 s) (dsum (A + 1) 2 s)
          (((Dfall a).eval (s : ℚ)) ^ 3) ((ph.comp (-X)).eval (s : ℚ))
          ((derivative (ph.comp (-X))).eval (s : ℚ))
          ((derivative (derivative (ph.comp (-X)))).eval (s : ℚ))) := by
  have hAa := hB.hAa
  have hp5 := hB.p5
  have hha := hB.ha
  have hψ : PInt p (ph.comp (-X)) := PInt.comp_neg hph
  set ψ := ph.comp (-X) with hψdef
  have h2i : (2 : ℚ)⁻¹ ∈ LocRing p := two_inv_mem (by omega)
  have hpm : (p : ℚ) ∈ LocRing p := p_mem
  obtain ⟨hq1, hq2, hq3, hq4⟩ := harm_m_eq (p := p) hs2 hu hm hAa
  have hk : a ≤ p + s := by omega
  have hτ := tau_formula (a := a) (A := A) n hAa (p + s) hk ph
  have hA' := lemmaA (n := n) (a := a) (A := A) (s := s) (u := u) (m := m) hB hs2 hu hm
  have hBk := B_expand hB hs1 hs2 hu hm hψ
  have hΘ := thetaA_EJ hB hs2 hu hm
  rw [hq2, hq3] at hΘ
  have hH1 : harm 1 s ∈ LocRing p := harm_mem hs2
  have hH2 : harm 2 s ∈ LocRing p := harm_mem hs2
  have hHA1 : harm 1 A ∈ LocRing p := harm_mem (by omega)
  have hHA2 : harm 2 A ∈ LocRing p := harm_mem (by omega)
  have hHa1 : harm 1 (a - 1) ∈ LocRing p := harm_mem (by omega)
  have hHa2 : harm 2 (a - 1) ∈ LocRing p := harm_mem (by omega)
  have hd1 := dsum_mem (p := p) (c := a) (r := 1) hs1 hs2
  have hd2 := dsum_mem (p := p) (c := a) (r := 2) hs1 hs2
  have hd3 := dsum_mem (p := p) (c := A + 1) (r := 1) (by omega) hs2
  have hd4 := dsum_mem (p := p) (c := A + 1) (r := 2) (by omega) hs2
  have hps0 := hψ.eval_nat (p := p) s
  have hps1 := hψ.derivative.eval_nat (p := p) s
  have hps2 := hψ.derivative.derivative.eval_nat (p := p) s
  have hOm : ((Dfall a).eval (s : ℚ)) ^ 3 ∈ LocRing p :=
    (LocRing p).pow_mem ((PInt.dfall a).eval_nat s) 3
  have hK1 : (4 * harm 1 A - 3 * harm 1 (a - 1)) ∈ LocRing p := by rmem
  have hK2 : (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) ∈ LocRing p := by rmem
  have hE1a : (-harm 1 s + 4 * dsum (A + 1) 1 s) ∈ LocRing p := by rmem
  have hE1b : (-(9 * 2⁻¹) * harm 2 s + 3 * dsum a 2 s) ∈ LocRing p := by rmem
  have hT0 := Ejet_EJ hp5 hK1 hK2
  have hE1 := Ejet_EJ hp5 hE1a hE1b
  have hprod := EJ.mul hp5 hT0 hE1
  have hΘ' : EJ p (ThetaA p A a s u m)
      (4 * harm 1 A - 3 * harm 1 (a - 1) + (-harm 1 s + 4 * dsum (A + 1) 1 s))
      (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1) + (-(9 * 2⁻¹) * harm 2 s + 3 * dsum a 2 s)) := by
    convert hΘ using 1 <;> ring
  have hΘΘ := EJ_unique hΘ' hprod
  have hbT : bTrunc (p := p) a A s ψ ∈ LocRing p := by
    unfold bTrunc
    have : (3 / 2 : ℚ) = 3 * 2⁻¹ := by norm_num
    rw [this]; rmem
  obtain ⟨w, hw, ew⟩ := hBk
  have hBmem : Bk (p := p) n a A s ψ ∈ LocRing p := by
    have : Bk (p := p) n a A s ψ = bTrunc (p := p) a A s ψ + p ^ 3 * w := by linear_combination ew
    rw [this]; rmem
  have hcore : tauK n a A ph (p + s) =
      (p : ℚ) * (32 * (((A !) : ℕ) : ℚ) ^ 2 * ((((a - 1) !) : ℕ) : ℚ) ^ 3) *
        ((((Dfall a).eval (s : ℚ)) ^ 3) * (ThetaA p A a s u m * Bk (p := p) n a A s ψ)) := by
    rw [hτ]
    have hdf := dfall_eval a s hs1
    rw [show s - a = u by omega] at hdf
    have hpq : (p : ℚ) ≠ 0 := p_ne_zero
    have hBk' : Bk (p := p) n a A s ψ = (p : ℚ) ^ 4 *
        (((-2 * harm 3 (p + s) * dd n (p + s) - 6 * harm 4 (p + s)) +
          4 * harm 3 (p + s) * (3 * dsum a 1 (p + s) + dsum (A + 1) 1 (p + s))) *
            ψ.eval ((p + s : ℕ) : ℚ) + 2 * harm 3 (p + s) * (derivative ψ).eval ((p + s : ℕ) : ℚ)) := by
      unfold Bk; ring
    rw [hBk']
    have hu' : (((Dfall a).eval (s : ℚ)) ^ 3) = ((((s !) : ℕ) : ℚ) / (((u !) : ℕ) : ℚ)) ^ 3 := by rw [hdf]
    rw [hu']
    generalize hX : (((-2 * harm 3 (p + s) * dd n (p + s) - 6 * harm 4 (p + s)) +
          4 * harm 3 (p + s) * (3 * dsum a 1 (p + s) + dsum (A + 1) 1 (p + s))) *
            ψ.eval ((p + s : ℕ) : ℚ) + 2 * harm 3 (p + s) * (derivative ψ).eval ((p + s : ℕ) : ℚ)) = X
    have := hA'
    calc cc n (p + s) * ((PiA a A).eval (-((p + s : ℕ) : ℚ))) ^ 2 * X
        = (cc n (p + s) * ((PiA a A).eval (-((p + s : ℕ) : ℚ))) ^ 2) * X := by ring
      _ = _ := by rw [hA']; field_simp
  rw [hcore]
  have hEmem : Ejet p (4 * harm 1 A - 3 * harm 1 (a - 1)) (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) ∈
      LocRing p := hT0.1
  have hE1mem : Ejet p (-harm 1 s + 4 * dsum (A + 1) 1 s) (-(9 * 2⁻¹) * harm 2 s + 3 * dsum a 2 s) ∈
      LocRing p := hE1.1
  have htab : PDv p 3 (((Dfall a).eval (s : ℚ) ^ 3) *
      Ejet p (-harm 1 s + 4 * dsum (A + 1) 1 s) (-(9 * 2⁻¹) * harm 2 s + 3 * dsum a 2 s) *
        bTrunc (p := p) a A s ψ -
      TabF p (harm 1 s) (harm 2 s) (dsum a 1 s) (dsum (A + 1) 1 s) (dsum a 2 s) (dsum (A + 1) 2 s)
          (((Dfall a).eval (s : ℚ)) ^ 3) (ψ.eval (s : ℚ)) ((derivative ψ).eval (s : ℚ))
          ((derivative (derivative ψ)).eval (s : ℚ))) := by
    unfold Ejet TabF bTrunc
    have h32 : (3 / 2 : ℚ) = 3 * 2⁻¹ := by norm_num
    rw [h32]
    set ps0 := ψ.eval (s : ℚ)
    set ps1 := (derivative ψ).eval (s : ℚ)
    set ps2 := (derivative (derivative ψ)).eval (s : ℚ)
    set Om := ((Dfall a).eval (s : ℚ)) ^ 3
    set H1 := harm 1 s
    set H2 := harm 2 s
    set dN1 := dsum a 1 s
    set dA1 := dsum (A + 1) 1 s
    set dN2 := dsum a 2 s
    set dA2 := dsum (A + 1) 2 s
    refine ⟨(-15) * dN2 * Om * ps1 + (-6) * dA1 * Om * ps2 + (-32) * dA1 * dA2 * Om * ps0 + (-40) * dA1^2 * Om * ps1 + 18 * dN1 * dN2 * Om * ps0 + 24 * dN1 * dA1 * Om * ps1 + 48 * dN1 * dA1^2 * Om * ps0 + (45 * 2⁻¹) * H2 * Om * ps1 + 8 * H2 * dA1 * Om * ps0 + (-27) * H2 * dN1 * Om * ps0 + (3 * 2⁻¹) * H1 * Om * ps2 + 8 * H1 * dA2 * Om * ps0 + 20 * H1 * dA1 * Om * ps1 + (-6) * H1 * dN1 * Om * ps1 + (-24) * H1 * dN1 * dA1 * Om * ps0 + (-2) * H1 * H2 * Om * ps0 + (-5 * 2⁻¹) * H1^2 * Om * ps1 + 3 * H1^2 * dN1 * Om * ps0 + (-9 * 2⁻¹) * (p : ℚ) * dN2 * Om * ps2 + (-24) * (p : ℚ) * dN2 * dA2 * Om * ps0 + (-12) * (p : ℚ) * dA1^2 * Om * ps2 + (-64) * (p : ℚ) * dA1^2 * dA2 * Om * ps0 + 18 * (p : ℚ) * dN1 * dN2 * Om * ps1 + 48 * (p : ℚ) * dN1 * dA1^2 * Om * ps1 + (27 * 2⁻¹ * 2⁻¹) * (p : ℚ) * H2 * Om * ps2 + 36 * (p : ℚ) * H2 * dA2 * Om * ps0 + 6 * (p : ℚ) * H2 * dN2 * Om * ps0 + 16 * (p : ℚ) * H2 * dA1^2 * Om * ps0 + (-27) * (p : ℚ) * H2 * dN1 * Om * ps1 + (-9) * (p : ℚ) * H2^2 * Om * ps0 + 6 * (p : ℚ) * H1 * dA1 * Om * ps2 + 32 * (p : ℚ) * H1 * dA1 * dA2 * Om * ps0 + (-24) * (p : ℚ) * H1 * dN1 * dA1 * Om * ps1 + (-8) * (p : ℚ) * H1 * H2 * dA1 * Om * ps0 + (-3 * 2⁻¹ * 2⁻¹) * (p : ℚ) * H1^2 * Om * ps2 + (-4) * (p : ℚ) * H1^2 * dA2 * Om * ps0 + 3 * (p : ℚ) * H1^2 * dN1 * Om * ps1 + 1 * (p : ℚ) * H1^2 * H2 * Om * ps0, ?_, ?_⟩
    · rmem
    · ring
  have h1 : PDv p 3 (ThetaA p A a s u m * Bk (p := p) n a A s ψ -
      Ejet p (4 * harm 1 A - 3 * harm 1 (a - 1)) (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) *
        (Ejet p (-harm 1 s + 4 * dsum (A + 1) 1 s) (-(9 * 2⁻¹) * harm 2 s + 3 * dsum a 2 s) *
          bTrunc (p := p) a A s ψ)) := by
    have e : ThetaA p A a s u m * Bk (p := p) n a A s ψ -
        Ejet p (4 * harm 1 A - 3 * harm 1 (a - 1)) (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) *
          (Ejet p (-harm 1 s + 4 * dsum (A + 1) 1 s) (-(9 * 2⁻¹) * harm 2 s + 3 * dsum a 2 s) *
            bTrunc (p := p) a A s ψ) =
        (ThetaA p A a s u m - Ejet p (4 * harm 1 A - 3 * harm 1 (a - 1)) (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) *
          Ejet p (-harm 1 s + 4 * dsum (A + 1) 1 s) (-(9 * 2⁻¹) * harm 2 s + 3 * dsum a 2 s)) *
            Bk (p := p) n a A s ψ +
        (Ejet p (4 * harm 1 A - 3 * harm 1 (a - 1)) (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) *
          Ejet p (-harm 1 s + 4 * dsum (A + 1) 1 s) (-(9 * 2⁻¹) * harm 2 s + 3 * dsum a 2 s)) *
            (Bk (p := p) n a A s ψ - bTrunc (p := p) a A s ψ) := by ring
    rw [e]
    refine PDv.add (PDv.mul_right hΘΘ hBmem) (PDv.mul_left ((LocRing p).mul_mem hEmem hE1mem) ?_)
    exact ⟨w, hw, ew⟩
  have h2 : PDv p 3 (((Dfall a).eval (s : ℚ) ^ 3) * (ThetaA p A a s u m * Bk (p := p) n a A s ψ) -
      Ejet p (4 * harm 1 A - 3 * harm 1 (a - 1)) (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) *
        TabF p (harm 1 s) (harm 2 s) (dsum a 1 s) (dsum (A + 1) 1 s) (dsum a 2 s) (dsum (A + 1) 2 s)
          (((Dfall a).eval (s : ℚ)) ^ 3) (ψ.eval (s : ℚ)) ((derivative ψ).eval (s : ℚ))
          ((derivative (derivative ψ)).eval (s : ℚ))) := by
    have e : ((Dfall a).eval (s : ℚ) ^ 3) * (ThetaA p A a s u m * Bk (p := p) n a A s ψ) -
      Ejet p (4 * harm 1 A - 3 * harm 1 (a - 1)) (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) *
        TabF p (harm 1 s) (harm 2 s) (dsum a 1 s) (dsum (A + 1) 1 s) (dsum a 2 s) (dsum (A + 1) 2 s)
          (((Dfall a).eval (s : ℚ)) ^ 3) (ψ.eval (s : ℚ)) ((derivative ψ).eval (s : ℚ))
          ((derivative (derivative ψ)).eval (s : ℚ)) =
        ((Dfall a).eval (s : ℚ) ^ 3) * (ThetaA p A a s u m * Bk (p := p) n a A s ψ -
          Ejet p (4 * harm 1 A - 3 * harm 1 (a - 1)) (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) *
            (Ejet p (-harm 1 s + 4 * dsum (A + 1) 1 s) (-(9 * 2⁻¹) * harm 2 s + 3 * dsum a 2 s) *
              bTrunc (p := p) a A s ψ)) +
        Ejet p (4 * harm 1 A - 3 * harm 1 (a - 1)) (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) *
          (((Dfall a).eval (s : ℚ) ^ 3) *
            Ejet p (-harm 1 s + 4 * dsum (A + 1) 1 s) (-(9 * 2⁻¹) * harm 2 s + 3 * dsum a 2 s) *
              bTrunc (p := p) a A s ψ -
            TabF p (harm 1 s) (harm 2 s) (dsum a 1 s) (dsum (A + 1) 1 s) (dsum a 2 s) (dsum (A + 1) 2 s)
              (((Dfall a).eval (s : ℚ)) ^ 3) (ψ.eval (s : ℚ)) ((derivative ψ).eval (s : ℚ))
              ((derivative (derivative ψ)).eval (s : ℚ))) := by ring
    rw [e]
    exact PDv.add (PDv.mul_left hOm h1) (PDv.mul_left hEmem htab)
  have h3 := PDv.mul (j := 1) (k := 3) pPDv_one h2
  have h4 := PDv.mul_left (show (32 * (((A !) : ℕ) : ℚ) ^ 2 * ((((a - 1) !) : ℕ) : ℚ) ^ 3) ∈ LocRing p by
    have := natCast_mem (p := p) (A !); have := natCast_mem (p := p) ((a - 1) !); rmem) h3
  convert h4 using 1
  ring

end NodeT


/-! ## The other nodes contribute `0 (mod p⁴)` (Lemma N) -/

theorem lucas_dvd {N k : ℕ} (h : N % p < k % p) : p ∣ N.choose k := by
  have := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := N) (k := k)
  rw [Nat.choose_eq_zero_of_lt h, zero_mul] at this
  exact (Nat.modEq_zero_iff_dvd).1 this

theorem pow_inv_mem (r : ℕ) {t : ℕ} (h0 : 0 < t) (ht : t < p ^ 2) :
    (p : ℚ) ^ r * ((t : ℚ) ^ r)⁻¹ ∈ LocRing p := by
  by_cases hd : p ∣ t
  · obtain ⟨q, rfl⟩ := hd
    have hq0 : 0 < q := Nat.pos_of_mul_pos_left h0
    have hq : q < p := by
      by_contra hcon
      have : p * p ≤ p * q := Nat.mul_le_mul_left p (not_lt.1 hcon)
      nlinarith
    have : (p : ℚ) ^ r * (((p * q : ℕ) : ℚ) ^ r)⁻¹ = (((q : ℚ)) ^ r)⁻¹ := by
      have hp0 : (p : ℚ) ≠ 0 := p_ne_zero
      push_cast; rw [mul_pow]; field_simp
    rw [this, ← inv_pow]
    exact (LocRing p).pow_mem (inv_mem_of_lt hq0 hq) r
  · refine (LocRing p).mul_mem ((LocRing p).pow_mem p_mem r) ?_
    rw [← inv_pow]
    exact (LocRing p).pow_mem (inv_natCast_mem_locRing hd) r

theorem p_harm_mem (r x : ℕ) (hx : x < p ^ 2) : (p : ℚ) ^ r * harm r x ∈ LocRing p := by
  unfold harm
  rw [mul_sum]
  refine (LocRing p).sum_mem fun i hi => ?_
  have hi' := mem_range.1 hi
  have := pow_inv_mem (p := p) r (t := i + 1) (Nat.succ_pos i) (by omega)
  convert this using 3
  push_cast; ring

section LemmaN

variable {n a A : ℕ}

theorem ccN_eq (n k : ℕ) : cc n k = (((6 * n).choose k ^ 2 * (2 * n + k).choose k ^ 3 : ℕ) : ℚ) := by
  unfold cc; push_cast; ring

/-- `E_k`, `U_k` in terms of `c_k`. -/
theorem tau_pdv {n k : ℕ} (hk : k < p ^ 2) (hk2 : 2 * n + k < p ^ 2) (hk3 : 6 * n - k < p ^ 2)
    {cN v e e' : ℕ} (hc : cc n k = (p : ℚ) ^ v * (cN : ℚ)) (hv8 : 8 ≤ v + e) (hv7 : 7 ≤ v + e')
    {F0 F1 : ℚ} (hF0 : F0 ∈ LocRing p) (hF1 : F1 ∈ LocRing p) (f : ℚ[X])
    (hf0 : f.eval (-(k : ℚ)) = (p : ℚ) ^ e * F0)
    (hf1 : (derivative f).eval (-(k : ℚ)) = (p : ℚ) ^ e' * F1) :
    PDv p 4 (EE n k * f.eval (-(k : ℚ)) + UU n k * (derivative f).eval (-(k : ℚ))) := by
  have hp0 : (p : ℚ) ≠ 0 := p_ne_zero
  have q3 := p_harm_mem (p := p) 3 k hk
  have q4 := p_harm_mem (p := p) 4 k hk
  have q1a := p_harm_mem (p := p) 1 k hk
  have q1b := p_harm_mem (p := p) 1 (2 * n + k) hk2
  have q1c := p_harm_mem (p := p) 1 (6 * n - k) hk3
  have hq4 : (p : ℚ) ^ 4 * (-2 * harm 3 k * dd n k - 6 * harm 4 k) ∈ LocRing p := by
    have : (p : ℚ) ^ 4 * (-2 * harm 3 k * dd n k - 6 * harm 4 k) =
        -2 * ((p : ℚ) ^ 3 * harm 3 k) * ((p : ℚ) * dd n k) - 6 * ((p : ℚ) ^ 4 * harm 4 k) := by ring
    rw [this]
    have hdd : (p : ℚ) * dd n k ∈ LocRing p := by
      unfold dd
      have : (p : ℚ) * (5 * harm 1 k - 3 * harm 1 (2 * n + k) - 2 * harm 1 (6 * n - k)) =
          5 * ((p : ℚ) ^ 1 * harm 1 k) - 3 * ((p : ℚ) ^ 1 * harm 1 (2 * n + k)) -
            2 * ((p : ℚ) ^ 1 * harm 1 (6 * n - k)) := by ring
      rw [this]; rmem
    rmem
  obtain ⟨d, hd⟩ : ∃ d, v + e = 8 + d := ⟨v + e - 8, by omega⟩
  obtain ⟨d', hd'⟩ : ∃ d', v + e' = 7 + d' := ⟨v + e' - 7, by omega⟩
  have hpe : (p : ℚ) ^ v * (p : ℚ) ^ e = (p : ℚ) ^ 4 * (p : ℚ) ^ 4 * (p : ℚ) ^ d := by
    rw [← pow_add, hd, pow_add]; ring
  have hpe' : (p : ℚ) ^ v * (p : ℚ) ^ e' = (p : ℚ) ^ 4 * (p : ℚ) ^ 3 * (p : ℚ) ^ d' := by
    rw [← pow_add, hd', pow_add]; ring
  refine ⟨(cN : ℚ) * (p : ℚ) ^ d * ((p : ℚ) ^ 4 * (-2 * harm 3 k * dd n k - 6 * harm 4 k)) * F0 -
      2 * (cN : ℚ) * (p : ℚ) ^ d' * ((p : ℚ) ^ 3 * harm 3 k) * F1, ?_, ?_⟩
  · have hcn : (cN : ℚ) ∈ LocRing p := natCast_mem cN
    have hpd : ∀ t : ℕ, (p : ℚ) ^ t ∈ LocRing p := fun t => (LocRing p).pow_mem p_mem t
    have := hpd d; have := hpd d'
    rmem
  · unfold EE UU
    rw [hf0, hf1, hc]
    linear_combination ((cN : ℚ) * F0 * (-2 * harm 3 k * dd n k - 6 * harm 4 k)) * hpe +
      (-2 * (cN : ℚ) * F1 * harm 3 k) * hpe'

end LemmaN


section LemmaN2

variable {n a A : ℕ}

theorem tau_pdv_small {n k : ℕ} (hk : k < p) (hk2 : 2 * n + k < p ^ 2) (hk3 : 6 * n - k < p ^ 2)
    {cN : ℕ} (hc : cc n k = (p : ℚ) ^ 5 * (cN : ℚ)) {F0 F1 : ℚ} (hF0 : F0 ∈ LocRing p)
    (hF1 : F1 ∈ LocRing p) (f : ℚ[X]) (hf0 : f.eval (-(k : ℚ)) = F0)
    (hf1 : (derivative f).eval (-(k : ℚ)) = F1) :
    PDv p 4 (EE n k * f.eval (-(k : ℚ)) + UU n k * (derivative f).eval (-(k : ℚ))) := by
  have hp0 : (p : ℚ) ≠ 0 := p_ne_zero
  have h3 : harm 3 k ∈ LocRing p := harm_mem hk
  have h4 : harm 4 k ∈ LocRing p := harm_mem hk
  have q1a := p_harm_mem (p := p) 1 k (by nlinarith [hp.out.two_le])
  have q1b := p_harm_mem (p := p) 1 (2 * n + k) hk2
  have q1c := p_harm_mem (p := p) 1 (6 * n - k) hk3
  have hdd : (p : ℚ) * dd n k ∈ LocRing p := by
    unfold dd
    have : (p : ℚ) * (5 * harm 1 k - 3 * harm 1 (2 * n + k) - 2 * harm 1 (6 * n - k)) =
        5 * ((p : ℚ) ^ 1 * harm 1 k) - 3 * ((p : ℚ) ^ 1 * harm 1 (2 * n + k)) -
          2 * ((p : ℚ) ^ 1 * harm 1 (6 * n - k)) := by ring
    rw [this]; rmem
  have hpm := p_mem (p := p)
  have hcn : (cN : ℚ) ∈ LocRing p := natCast_mem cN
  have hpV : (p : ℚ) * (-2 * harm 3 k * dd n k - 6 * harm 4 k) ∈ LocRing p := by
    have : (p : ℚ) * (-2 * harm 3 k * dd n k - 6 * harm 4 k) =
        -2 * harm 3 k * ((p : ℚ) * dd n k) - 6 * (p : ℚ) * harm 4 k := by ring
    rw [this]; rmem
  refine ⟨(cN : ℚ) * ((p : ℚ) * (-2 * harm 3 k * dd n k - 6 * harm 4 k) * F0 -
      2 * (p : ℚ) * harm 3 k * F1), ?_, ?_⟩
  · rmem
  · unfold EE UU
    rw [hf0, hf1, hc]
    ring

theorem f_factor (hAa : A < a) {s : ℕ} (hs : s < a) (ph : ℚ[X]) (hph : PInt p ph) :
    ∃ fs : ℚ[X], PInt p fs ∧ PiA a A ^ 2 * ph =
      (X + C (s : ℚ)) ^ (2 * (if s ≤ A then 4 else 3)) * fs := by
  have hmem : s ∈ range a := mem_range.2 hs
  refine ⟨(∏ r ∈ (range a).erase s, (X + C (r : ℚ)) ^ (if r ≤ A then 4 else 3)) ^ 2 * ph, ?_, ?_⟩
  · refine PInt.mul (PInt.pow (PInt.prod _ _ fun r _ => PInt.pow (PInt.X_add_C ?_) _) 2) hph
    exact_mod_cast int_mem_locRing (ℓ := p) (r : ℤ)
  · unfold PiA
    rw [← mul_prod_erase (range a) (fun r => (X + C (r : ℚ)) ^ (if r ≤ A then 4 else 3)) hmem]
    ring

omit hp in
theorem f_eval_aux (N : ℕ) (hN : 2 ≤ N) (x s : ℚ) (fs : ℚ[X]) :
    (derivative ((X + C s) ^ N * fs)).eval x =
      (N : ℚ) * (x + s) ^ (N - 1) * fs.eval x + (x + s) ^ N * (derivative fs).eval x := by
  rw [derivative_mul, derivative_pow]
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X, derivative_add, derivative_X, derivative_C,
    add_zero, mul_one, eval_natCast, eval_one]

/-- Vanishing orders of `f = Π² φ` at the node `-(j p + s)`, `s < a`. -/
theorem f_vals (hB : Band p n a A) {s : ℕ} (hs : s < a) {ph : ℚ[X]} (hph : PInt p ph) (j : ℕ) :
    ∃ F0 F1 : ℚ, F0 ∈ LocRing p ∧ F1 ∈ LocRing p ∧
      ((PiA a A ^ 2 * ph).eval (-((j * p + s : ℕ) : ℚ)) =
        (p : ℚ) ^ (2 * (if s ≤ A then 4 else 3)) * F0) ∧
      ((derivative (PiA a A ^ 2 * ph)).eval (-((j * p + s : ℕ) : ℚ)) =
        (p : ℚ) ^ (2 * (if s ≤ A then 4 else 3) - 1) * F1) := by
  obtain ⟨fs, hfs, hf⟩ := f_factor hB.hAa hs ph hph
  set μ := (if s ≤ A then 4 else 3) with hμ
  have hμ3 : 3 ≤ μ := by rw [hμ]; split_ifs <;> omega
  have hx : -((j * p + s : ℕ) : ℚ) + s = -((j : ℚ) * p) := by push_cast; ring
  have hxm : -((j * p + s : ℕ) : ℚ) ∈ LocRing p := by
    have := natCast_mem (p := p) (j * p + s); rmem
  have hfs0 : fs.eval (-((j * p + s : ℕ) : ℚ)) ∈ LocRing p := hfs.eval_mem hxm
  have hfs1 : (derivative fs).eval (-((j * p + s : ℕ) : ℚ)) ∈ LocRing p := hfs.derivative.eval_mem hxm
  have hjm : (j : ℚ) ∈ LocRing p := natCast_mem j
  have hpm := p_mem (p := p)
  refine ⟨(j : ℚ) ^ (2 * μ) * fs.eval (-((j * p + s : ℕ) : ℚ)),
    -(2 * μ : ℚ) * (j : ℚ) ^ (2 * μ - 1) * fs.eval (-((j * p + s : ℕ) : ℚ)) +
      p * (j : ℚ) ^ (2 * μ) * (derivative fs).eval (-((j * p + s : ℕ) : ℚ)), ?_, ?_, ?_, ?_⟩
  · have := natCast_mem (p := p) μ; rmem
  · have := natCast_mem (p := p) μ; rmem
  · rw [hf, eval_mul, eval_pow, eval_add, eval_X, eval_C, hx, neg_pow, Even.neg_pow (by exact ⟨μ, by ring⟩)]
    rw [mul_pow]; ring
  · rw [hf, f_eval_aux (2 * μ) (by omega), hx]
    have h1 : (-((j : ℚ) * p)) ^ (2 * μ - 1) = -(((j : ℚ) * p) ^ (2 * μ - 1)) :=
      Odd.neg_pow ⟨μ - 1, by omega⟩ _
    have h2 : (-((j : ℚ) * p)) ^ (2 * μ) = ((j : ℚ) * p) ^ (2 * μ) :=
      Even.neg_pow ⟨μ, by ring⟩ _
    rw [h1, h2, mul_pow, mul_pow]
    obtain ⟨t, ht⟩ : ∃ t, 2 * μ = (2 * μ - 1) + 1 := ⟨0, by omega⟩
    have hpow : (p : ℚ) ^ (2 * μ) = (p : ℚ) ^ (2 * μ - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [hpow]
    push_cast
    ring

end LemmaN2


section LemmaN3

variable {n a A : ℕ}

theorem hpp3 (hp5 : 5 ≤ p) : 3 * p ≤ p ^ 2 := by nlinarith

theorem lucas_C1 (hB : Band p n a A) {k : ℕ} (hk : k % p > A) : p ∣ (6 * n).choose k := by
  have hhA := hB.hA
  have hp5 := hB.p5
  have hAa := hB.hAa
  have hha := hB.ha
  apply lucas_dvd
  have : (6 * n) % p = A := by
    rw [show 6 * n = A + p * 2 by omega, Nat.add_mul_mod_self_left]; exact Nat.mod_eq_of_lt (by omega)
  omega

theorem cc_nat (n k : ℕ) : cc n k = (((6 * n).choose k : ℕ) : ℚ) ^ 2 * (((2 * n + k).choose k : ℕ) : ℚ) ^ 3 := rfl

theorem others_AC (hB : Band p n a A) {ph : ℚ[X]} (hph : PInt p ph) {j s : ℕ} (hs : s < a) (hj : j ≤ 2)
    (hk : j * p + s ≤ 6 * n) (hjs : j = 2 → s ≤ A) :
    PDv p 4 (tauK n a A ph (j * p + s)) := by
  have hhA := hB.hA
  have hAa := hB.hAa
  have hha := hB.ha
  have hp5 := hB.p5
  have hpp := hpp3 (p := p) hp5
  obtain ⟨F0, F1, hF0, hF1, e0, e1⟩ := f_vals hB hs hph j
  unfold tauK
  have hsp : s < p := by omega
  have hmod : (j * p + s) % p = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]; exact Nat.mod_eq_of_lt hsp
  by_cases hsA : s ≤ A
  · rw [if_pos hsA] at e0 e1
    refine tau_pdv (n := n) (k := j * p + s) (by omega) (by omega) (by omega) (cN := (((6 * n).choose (j * p + s) ^ 2 *
      (2 * n + (j * p + s)).choose (j * p + s) ^ 3 : ℕ))) (v := 0) (e := 2 * 4) (e' := 2 * 4 - 1)
      ?_ (by omega) (by omega) hF0 hF1 _ e0 e1
    rw [cc_nat]; push_cast; ring
  · rw [if_neg hsA] at e0 e1
    have hj1 : j ≠ 2 := fun h => hsA (hjs h)
    have hdv := lucas_C1 hB (k := j * p + s) (by rw [hmod]; omega)
    obtain ⟨q, hq⟩ := hdv
    refine tau_pdv (n := n) (k := j * p + s) (by omega) (by omega) (by omega)
      (cN := q ^ 2 * (2 * n + (j * p + s)).choose (j * p + s) ^ 3) (v := 2) (e := 2 * 3) (e' := 2 * 3 - 1)
      ?_ (by omega) (by omega) hF0 hF1 _ e0 e1
    rw [cc_nat, hq]; push_cast; ring

theorem others_small (hB : Band p n a A) {ph : ℚ[X]} (hph : PInt p ph) {k : ℕ} (hka : a ≤ k) (hkp : k < p) :
    PDv p 4 (tauK n a A ph k) := by
  have hhA := hB.hA
  have hAa := hB.hAa
  have hha := hB.ha
  have hp5 := hB.p5
  have hpp := hpp3 (p := p) hp5
  have hd1 := lucas_C1 hB (k := k) (by rw [Nat.mod_eq_of_lt hkp]; omega)
  have hd2 : p ∣ (2 * n + k).choose k := by
    apply lucas_dvd
    have h1 : (2 * n + k) % p = 2 * n + k - p := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [h1, Nat.mod_eq_of_lt hkp]; omega
  obtain ⟨q1, hq1⟩ := hd1
  obtain ⟨q2, hq2⟩ := hd2
  have hm : PInt p (PiA a A ^ 2 * ph) := (PInt.piA hAa).pow 2 |>.mul hph
  have hxm : -(k : ℚ) ∈ LocRing p := by have := natCast_mem (p := p) k; rmem
  unfold tauK
  refine tau_pdv_small (n := n) (k := k) hkp (by omega) (by omega)
    (cN := q1 ^ 2 * q2 ^ 3 * p ^ 0) ?_ (hm.eval_mem hxm) (hm.derivative.eval_mem hxm) _ rfl rfl
  rw [cc_nat, hq1, hq2]; push_cast; ring

theorem others_pdv (hB : Band p n a A) {ph : ℚ[X]} (hph : PInt p ph) {k : ℕ} (hk : k < 6 * n + 1)
    (hnot : ¬ (p ≤ k ∧ k < 2 * p ∧ a ≤ k - p)) : PDv p 4 (tauK n a A ph k) := by
  have hhA := hB.hA
  have hAa := hB.hAa
  have hha := hB.ha
  rcases lt_or_ge k a with hka | hka
  · have := others_AC hB hph (j := 0) (s := k) hka (by omega) (by omega) (by omega)
    simpa using this
  · rcases lt_or_ge k p with hkp | hkp
    · exact others_small hB hph hka hkp
    · rcases lt_or_ge k (2 * p) with hk2 | hk2
      · have := others_AC hB hph (j := 1) (s := k - p) (by omega) (by omega) (by omega) (by omega)
        rwa [show 1 * p + (k - p) = k by omega] at this
      · have := others_AC hB hph (j := 2) (s := k - 2 * p) (by omega) (by omega) (by omega) (by omega)
        rwa [show 2 * p + (k - 2 * p) = k by omega] at this

theorem Lf_main (hB : Band p n a A) {ph : ℚ[X]} (hph : PInt p ph) :
    PDv p 4 (Lf n (PiA a A ^ 2 * ph) - ∑ s ∈ Ico a p, tauK n a A ph (p + s)) := by
  have hhA := hB.hA
  have hAa := hB.hAa
  have hha := hB.ha
  have hL : Lf n (PiA a A ^ 2 * ph) = ∑ k ∈ range (6 * n + 1), tauK n a A ph k := rfl
  set M : Finset ℕ := (Ico a p).image (fun s => p + s) with hM
  have hsub : M ⊆ range (6 * n + 1) := by
    intro k hk
    rw [hM, mem_image] at hk
    obtain ⟨s, hs, rfl⟩ := hk
    rw [mem_Ico] at hs; rw [mem_range]; omega
  have hsum := sum_sdiff hsub (f := fun k => tauK n a A ph k)
  have hMsum : ∑ k ∈ M, tauK n a A ph k = ∑ s ∈ Ico a p, tauK n a A ph (p + s) := by
    rw [hM, sum_image]
    intro x _ y _ h; simpa using h
  rw [hL, ← hsum, hMsum]
  have : ∑ k ∈ range (6 * n + 1) \ M, tauK n a A ph k +
      ∑ s ∈ Ico a p, tauK n a A ph (p + s) - ∑ s ∈ Ico a p, tauK n a A ph (p + s) =
      ∑ k ∈ range (6 * n + 1) \ M, tauK n a A ph k := by ring
  rw [this]
  refine PDv.sum _ _ fun k hk => ?_
  rw [mem_sdiff, mem_range] at hk
  refine others_pdv hB hph hk.1 ?_
  rintro ⟨h1, h2, h3⟩
  apply hk.2
  rw [hM, mem_image]
  exact ⟨k - p, by rw [mem_Ico]; omega, by omega⟩

end LemmaN3


section Weights

variable {n a A : ℕ}

/-! ## The weight polynomials: `Ω ψ`, `Ω ψ'`, `Ω ψ''`, `Ω δ ψ`, … -/

/-- `∏_{i ∈ S} (X - i)`. -/
noncomputable def DgS (S : Finset ℕ) : ℚ[X] := ∏ i ∈ S, (X - C (i : ℚ))

omit hp in
theorem DgS_logder (S : Finset ℕ) (s : ℚ) (hs : ∀ i ∈ S, s - i ≠ 0) :
    (derivative (DgS S)).eval s = (DgS S).eval s * ∑ i ∈ S, (s - i)⁻¹ ∧
    (derivative (derivative (DgS S))).eval s =
      (DgS S).eval s * ((∑ i ∈ S, (s - i)⁻¹) ^ 2 - ∑ i ∈ S, ((s - i) ^ 2)⁻¹) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [DgS]
  | insert i S hi ih =>
    obtain ⟨h1, h2⟩ := ih (fun j hj => hs j (mem_insert_of_mem hj))
    have ht : s - i ≠ 0 := hs i (mem_insert_self _ _)
    have e : DgS (insert i S) = (X - C (i : ℚ)) * DgS S := by unfold DgS; rw [prod_insert hi]
    rw [e, sum_insert hi, sum_insert hi]
    have d1 : derivative ((X - C (i : ℚ)) * DgS S) = DgS S + (X - C (i : ℚ)) * derivative (DgS S) := by
      simp [derivative_mul]
    have d2 : derivative (derivative ((X - C (i : ℚ)) * DgS S)) =
        2 * derivative (DgS S) + (X - C (i : ℚ)) * derivative (derivative (DgS S)) := by
      rw [d1]; simp [derivative_add, derivative_mul]; ring
    constructor
    · rw [d1]
      simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, h1]
      field_simp
    · rw [d2]
      simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, h1, h2, eval_ofNat]
      field_simp
      ring

theorem DgS_pint (S : Finset ℕ) : PInt p (DgS S) := by
  unfold DgS
  exact PInt.prod _ _ fun r _ => PInt.X_sub_C (by exact_mod_cast int_mem_locRing (ℓ := p) (r : ℤ))

omit hp in
theorem DgS_natDegree (S : Finset ℕ) : (DgS S).natDegree ≤ S.card := by
  unfold DgS
  refine (natDegree_prod_le S (fun i : ℕ => (X - C (i : ℚ)))).trans ?_
  have h : ∀ i ∈ S, (X - C (i : ℚ)).natDegree ≤ 1 := fun i _ => (natDegree_X_sub_C (i : ℚ)).le
  exact (sum_le_sum h).trans (by simp)

/-- The factors `U = ∏_{i ≤ A} (X - i)` and `V = ∏_{A < i < a} (X - i)` of `D_a = U V`. -/
noncomputable def Uw (A : ℕ) : ℚ[X] := DgS (range (A + 1))
noncomputable def Vw (a A : ℕ) : ℚ[X] := DgS (Ico (A + 1) a)

omit hp in
theorem Dfall_eq (a A : ℕ) (h : A < a) : Dfall a = Uw A * Vw a A := by
  unfold Dfall Uw Vw DgS
  rw [prod_range_mul_prod_Ico _ (by omega)]

noncomputable def wG (a A : ℕ) (ψ : ℚ[X]) : ℚ[X] := Uw A ^ 3 * Vw a A ^ 3 * ψ
noncomputable def wW1 (a A : ℕ) (ψ : ℚ[X]) : ℚ[X] := Uw A ^ 3 * Vw a A ^ 3 * derivative ψ
noncomputable def wW2 (a A : ℕ) (ψ : ℚ[X]) : ℚ[X] := Uw A ^ 3 * Vw a A ^ 3 * derivative (derivative ψ)
noncomputable def wGA (a A : ℕ) (ψ : ℚ[X]) : ℚ[X] := Uw A ^ 2 * Vw a A ^ 3 * derivative (Uw A) * ψ
noncomputable def wGN (a A : ℕ) (ψ : ℚ[X]) : ℚ[X] :=
  (Uw A ^ 2 * Vw a A ^ 3 * derivative (Uw A) + Uw A ^ 3 * Vw a A ^ 2 * derivative (Vw a A)) * ψ
noncomputable def wGAA (a A : ℕ) (ψ : ℚ[X]) : ℚ[X] := Uw A * Vw a A ^ 3 * derivative (Uw A) ^ 2 * ψ
noncomputable def wGA2 (a A : ℕ) (ψ : ℚ[X]) : ℚ[X] :=
  Uw A * Vw a A ^ 3 * (derivative (Uw A) ^ 2 - Uw A * derivative (derivative (Uw A))) * ψ
noncomputable def wGN2 (a A : ℕ) (ψ : ℚ[X]) : ℚ[X] :=
  (Uw A * Vw a A ^ 3 * (derivative (Uw A) ^ 2 - Uw A * derivative (derivative (Uw A))) +
    Uw A ^ 3 * Vw a A * (derivative (Vw a A) ^ 2 - Vw a A * derivative (derivative (Vw a A)))) * ψ
noncomputable def wGAN (a A : ℕ) (ψ : ℚ[X]) : ℚ[X] :=
  (Uw A * Vw a A ^ 3 * derivative (Uw A) ^ 2 +
    Uw A ^ 2 * Vw a A ^ 2 * derivative (Uw A) * derivative (Vw a A)) * ψ
noncomputable def wW1A (a A : ℕ) (ψ : ℚ[X]) : ℚ[X] := Uw A ^ 2 * Vw a A ^ 3 * derivative (Uw A) * derivative ψ
noncomputable def wW1N (a A : ℕ) (ψ : ℚ[X]) : ℚ[X] :=
  (Uw A ^ 2 * Vw a A ^ 3 * derivative (Uw A) + Uw A ^ 3 * Vw a A ^ 2 * derivative (Vw a A)) * derivative ψ

/-- Evaluation of all weights at a natural `s ≥ a`. -/
theorem weights_eval (hAa : A < a) {s : ℕ} (hs : a ≤ s) (ψ : ℚ[X]) :
    (wG a A ψ).eval (s : ℚ) = (((Dfall a).eval (s : ℚ)) ^ 3) * ψ.eval (s : ℚ) ∧
    (wW1 a A ψ).eval (s : ℚ) = (((Dfall a).eval (s : ℚ)) ^ 3) * (derivative ψ).eval (s : ℚ) ∧
    (wW2 a A ψ).eval (s : ℚ) = (((Dfall a).eval (s : ℚ)) ^ 3) * (derivative (derivative ψ)).eval (s : ℚ) ∧
    (wGA a A ψ).eval (s : ℚ) = (((Dfall a).eval (s : ℚ)) ^ 3) * ψ.eval (s : ℚ) * dsum (A + 1) 1 s ∧
    (wGN a A ψ).eval (s : ℚ) = (((Dfall a).eval (s : ℚ)) ^ 3) * ψ.eval (s : ℚ) * dsum a 1 s ∧
    (wGAA a A ψ).eval (s : ℚ) = (((Dfall a).eval (s : ℚ)) ^ 3) * ψ.eval (s : ℚ) * dsum (A + 1) 1 s ^ 2 ∧
    (wGA2 a A ψ).eval (s : ℚ) = (((Dfall a).eval (s : ℚ)) ^ 3) * ψ.eval (s : ℚ) * dsum (A + 1) 2 s ∧
    (wGN2 a A ψ).eval (s : ℚ) = (((Dfall a).eval (s : ℚ)) ^ 3) * ψ.eval (s : ℚ) * dsum a 2 s ∧
    (wGAN a A ψ).eval (s : ℚ) = (((Dfall a).eval (s : ℚ)) ^ 3) * ψ.eval (s : ℚ) * dsum (A + 1) 1 s * dsum a 1 s ∧
    (wW1A a A ψ).eval (s : ℚ) = (((Dfall a).eval (s : ℚ)) ^ 3) * (derivative ψ).eval (s : ℚ) * dsum (A + 1) 1 s ∧
    (wW1N a A ψ).eval (s : ℚ) = (((Dfall a).eval (s : ℚ)) ^ 3) * (derivative ψ).eval (s : ℚ) * dsum a 1 s := by
  have hne : ∀ i ∈ range a, (s : ℚ) - i ≠ 0 := fun i hi => by
    have := mem_range.1 hi
    have : (i : ℚ) < s := by exact_mod_cast (by omega : i < s)
    linarith
  have hU := DgS_logder (range (A + 1)) (s : ℚ) (fun i hi => hne i (mem_range.2 (by have := mem_range.1 hi; omega)))
  have hV := DgS_logder (Ico (A + 1) a) (s : ℚ) (fun i hi => hne i (by
    have := mem_Ico.1 hi; exact mem_range.2 this.2))
  have hsplit1 : dsum a 1 s = dsum (A + 1) 1 s + ∑ i ∈ Ico (A + 1) a, (((s : ℚ) - i) ^ 1)⁻¹ := by
    unfold dsum
    rw [← sum_range_add_sum_Ico _ (show A + 1 ≤ a by omega)]
  have hsplit2 : dsum a 2 s = dsum (A + 1) 2 s + ∑ i ∈ Ico (A + 1) a, (((s : ℚ) - i) ^ 2)⁻¹ := by
    unfold dsum
    rw [← sum_range_add_sum_Ico _ (show A + 1 ≤ a by omega)]
  have hU1 : (derivative (Uw A)).eval (s : ℚ) = (Uw A).eval (s : ℚ) * dsum (A + 1) 1 s := by
    have := hU.1; unfold Uw dsum; simpa [pow_one] using this
  have hU2 : (derivative (derivative (Uw A))).eval (s : ℚ) =
      (Uw A).eval (s : ℚ) * (dsum (A + 1) 1 s ^ 2 - dsum (A + 1) 2 s) := by
    have := hU.2; unfold Uw dsum; simpa [pow_one] using this
  have hV1 : (derivative (Vw a A)).eval (s : ℚ) = (Vw a A).eval (s : ℚ) *
      ∑ i ∈ Ico (A + 1) a, (((s : ℚ) - i) ^ 1)⁻¹ := by
    have := hV.1; unfold Vw; simpa [pow_one] using this
  have hV2 : (derivative (derivative (Vw a A))).eval (s : ℚ) = (Vw a A).eval (s : ℚ) *
      ((∑ i ∈ Ico (A + 1) a, (((s : ℚ) - i) ^ 1)⁻¹) ^ 2 - ∑ i ∈ Ico (A + 1) a, (((s : ℚ) - i) ^ 2)⁻¹) := by
    have := hV.2; unfold Vw; simpa [pow_one] using this
  have hOm : (((Dfall a).eval (s : ℚ)) ^ 3) = ((Uw A).eval (s : ℚ) * (Vw a A).eval (s : ℚ)) ^ 3 := by
    rw [Dfall_eq a A hAa, eval_mul]
  generalize (∑ i ∈ Ico (A + 1) a, (((s : ℚ) - i) ^ 1)⁻¹) = dV1 at *
  generalize (∑ i ∈ Ico (A + 1) a, (((s : ℚ) - i) ^ 2)⁻¹) = dV2 at *
  rw [hsplit1, hsplit2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [wG, wW1, wW2, wGA, wGN, wGAA, wGA2, wGN2, wGAN, wW1A, wW1N, eval_mul, eval_pow, eval_add,
      eval_sub, hU1, hU2, hV1, hV2, hOm] <;> ring

omit hp in
theorem Dfall_eval_zero {a s : ℕ} (hs : s < a) : (Dfall a).eval (s : ℚ) = 0 := by
  unfold Dfall
  rw [eval_prod]
  exact prod_eq_zero (mem_range.2 hs) (by simp)

/-- Every weight is divisible by `D_a`, hence vanishes at `0, …, a-1`. -/
theorem weights_zero (hAa : A < a) {s : ℕ} (hs : s < a) (ψ : ℚ[X]) :
    (wG a A ψ).eval (s : ℚ) = 0 ∧ (wW1 a A ψ).eval (s : ℚ) = 0 ∧ (wW2 a A ψ).eval (s : ℚ) = 0 ∧
    (wGA a A ψ).eval (s : ℚ) = 0 ∧ (wGN a A ψ).eval (s : ℚ) = 0 ∧ (wGAA a A ψ).eval (s : ℚ) = 0 ∧
    (wGA2 a A ψ).eval (s : ℚ) = 0 ∧ (wGN2 a A ψ).eval (s : ℚ) = 0 ∧ (wGAN a A ψ).eval (s : ℚ) = 0 ∧
    (wW1A a A ψ).eval (s : ℚ) = 0 ∧ (wW1N a A ψ).eval (s : ℚ) = 0 := by
  have h0 := Dfall_eval_zero (a := a) hs
  rw [Dfall_eq a A hAa, eval_mul, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [wG, wW1, wW2, wGA, wGN, wGAA, wGA2, wGN2, wGAN, wW1A, wW1N, eval_mul, eval_pow, eval_add,
        eval_sub, h0] <;> ring
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [wG, wW1, wW2, wGA, wGN, wGAA, wGA2, wGN2, wGAN, wW1A, wW1N, eval_mul, eval_pow, eval_add,
        eval_sub, h0] <;> ring

/-! ## The weights are admissible, and the summation lemmas apply -/

omit hp in
theorem ND.mul {f g : ℚ[X]} {a b : ℕ} (hf : f.natDegree ≤ a) (hg : g.natDegree ≤ b) :
    (f * g).natDegree ≤ a + b := natDegree_mul_le.trans (Nat.add_le_add hf hg)

omit hp in
theorem ND.pow {f : ℚ[X]} {a : ℕ} (hf : f.natDegree ≤ a) (k : ℕ) : (f ^ k).natDegree ≤ k * a :=
  natDegree_pow_le.trans (Nat.mul_le_mul_left k hf)

omit hp in
theorem ND.deriv {f : ℚ[X]} {a : ℕ} (hf : f.natDegree ≤ a) : (derivative f).natDegree ≤ a :=
  (natDegree_derivative_le f).trans ((Nat.sub_le _ _).trans hf)

omit hp in
theorem ND.add {f g : ℚ[X]} {a : ℕ} (hf : f.natDegree ≤ a) (hg : g.natDegree ≤ a) :
    (f + g).natDegree ≤ a := natDegree_add_le_of_degree_le hf hg

omit hp in
theorem ND.sub {f g : ℚ[X]} {a b c : ℕ} (hf : f.natDegree ≤ a) (hg : g.natDegree ≤ b) (h1 : a ≤ c)
    (h2 : b ≤ c) : (f - g).natDegree ≤ c :=
  (natDegree_sub_le_of_le (hf.trans h1) (hg.trans h2)).trans (by simp)

omit hp in
theorem ND.mono {f : ℚ[X]} {a b : ℕ} (hf : f.natDegree ≤ a) (h : a ≤ b) : f.natDegree ≤ b :=
  hf.trans h

omit hp in
theorem Uw_deg : (Uw A).natDegree ≤ A + 1 := by
  have := DgS_natDegree (range (A + 1)); unfold Uw; simpa using this

omit hp in
theorem Vw_deg : (Vw a A).natDegree ≤ a - (A + 1) := by
  have := DgS_natDegree (Ico (A + 1) a); unfold Vw; simpa using this

/-- All eleven weights are admissible for the summation lemmas. -/
theorem weights_adm (hB : Band p n a A) {ψ : ℚ[X]} (hψ : PInt p ψ) {d : ℕ} (hd : ψ.natDegree ≤ d)
    (hda : 3 * a + d ≤ p - 3) :
    Adm p (wG a A ψ) ∧ Adm p (wW1 a A ψ) ∧ Adm p (wW2 a A ψ) ∧ Adm p (wGA a A ψ) ∧
    Adm p (wGN a A ψ) ∧ Adm p (wGAA a A ψ) ∧ Adm p (wGA2 a A ψ) ∧ Adm p (wGN2 a A ψ) ∧
    Adm p (wGAN a A ψ) ∧ Adm p (wW1A a A ψ) ∧ Adm p (wW1N a A ψ) := by
  have hAa := hB.hAa
  have pU : PInt p (Uw A) := DgS_pint _
  have pV : PInt p (Vw a A) := DgS_pint _
  have pU1 := pU.derivative
  have pU2 := pU1.derivative
  have pV1 := pV.derivative
  have pV2 := pV1.derivative
  have pψ1 := hψ.derivative
  have pψ2 := pψ1.derivative
  have dU : (Uw A).natDegree ≤ A + 1 := Uw_deg
  have dV : (Vw a A).natDegree ≤ a - (A + 1) := Vw_deg
  have dU1 := ND.deriv dU
  have dU2 := ND.deriv dU1
  have dV1 := ND.deriv dV
  have dV2 := ND.deriv dV1
  have dψ1 := ND.deriv hd
  have dψ2 := ND.deriv dψ1
  have e3 : 3 * (A + 1) + 3 * (a - (A + 1)) + d ≤ p - 3 := by omega
  have hUV3 : PInt p (Uw A ^ 3 * Vw a A ^ 3) := (pU.pow 3).mul (pV.pow 3)
  have pwGA : PInt p (Uw A ^ 2 * Vw a A ^ 3 * derivative (Uw A)) := ((pU.pow 2).mul (pV.pow 3)).mul pU1
  have pwGV : PInt p (Uw A ^ 3 * Vw a A ^ 2 * derivative (Vw a A)) := ((pU.pow 3).mul (pV.pow 2)).mul pV1
  have pq1 : PInt p (Uw A * Vw a A ^ 3 * (derivative (Uw A) ^ 2 - Uw A * derivative (derivative (Uw A)))) :=
    (pU.mul (pV.pow 3)).mul ((pU1.pow 2).sub (pU.mul pU2))
  have pq2 : PInt p (Uw A ^ 3 * Vw a A * (derivative (Vw a A) ^ 2 - Vw a A * derivative (derivative (Vw a A)))) :=
    ((pU.pow 3).mul pV).mul ((pV1.pow 2).sub (pV.mul pV2))
  have pq3 : PInt p (Uw A * Vw a A ^ 3 * derivative (Uw A) ^ 2) := (pU.mul (pV.pow 3)).mul (pU1.pow 2)
  have pq4 : PInt p (Uw A ^ 2 * Vw a A ^ 2 * derivative (Uw A) * derivative (Vw a A)) :=
    (((pU.pow 2).mul (pV.pow 2)).mul pU1).mul pV1
  have dwGA : (Uw A ^ 2 * Vw a A ^ 3 * derivative (Uw A)).natDegree ≤ 3 * (A + 1) + 3 * (a - (A + 1)) :=
    ND.mono (ND.mul (ND.mul (ND.pow dU 2) (ND.pow dV 3)) dU1) (by omega)
  have dwGV : (Uw A ^ 3 * Vw a A ^ 2 * derivative (Vw a A)).natDegree ≤ 3 * (A + 1) + 3 * (a - (A + 1)) :=
    ND.mono (ND.mul (ND.mul (ND.pow dU 3) (ND.pow dV 2)) dV1) (by omega)
  have dq1 : (Uw A * Vw a A ^ 3 * (derivative (Uw A) ^ 2 - Uw A * derivative (derivative (Uw A)))).natDegree ≤
      3 * (A + 1) + 3 * (a - (A + 1)) :=
    ND.mono (ND.mul (ND.mul dU (ND.pow dV 3)) (ND.sub (ND.pow dU1 2) (ND.mul dU dU2)
      (c := 2 * (A + 1)) (by omega) (by omega))) (by omega)
  have dq2 : (Uw A ^ 3 * Vw a A * (derivative (Vw a A) ^ 2 - Vw a A * derivative (derivative (Vw a A)))).natDegree ≤
      3 * (A + 1) + 3 * (a - (A + 1)) :=
    ND.mono (ND.mul (ND.mul (ND.pow dU 3) dV) (ND.sub (ND.pow dV1 2) (ND.mul dV dV2)
      (c := 2 * (a - (A + 1))) (by omega) (by omega))) (by omega)
  have dq3 : (Uw A * Vw a A ^ 3 * derivative (Uw A) ^ 2).natDegree ≤ 3 * (A + 1) + 3 * (a - (A + 1)) :=
    ND.mono (ND.mul (ND.mul dU (ND.pow dV 3)) (ND.pow dU1 2)) (by omega)
  have dq4 : (Uw A ^ 2 * Vw a A ^ 2 * derivative (Uw A) * derivative (Vw a A)).natDegree ≤
      3 * (A + 1) + 3 * (a - (A + 1)) :=
    ND.mono (ND.mul (ND.mul (ND.mul (ND.pow dU 2) (ND.pow dV 2)) dU1) dV1) (by omega)
  have dUV3 : (Uw A ^ 3 * Vw a A ^ 3).natDegree ≤ 3 * (A + 1) + 3 * (a - (A + 1)) :=
    ND.mono (ND.mul (ND.pow dU 3) (ND.pow dV 3)) (by omega)
  refine ⟨⟨hUV3.mul hψ, ?_⟩, ⟨hUV3.mul pψ1, ?_⟩, ⟨hUV3.mul pψ2, ?_⟩, ⟨pwGA.mul hψ, ?_⟩,
    ⟨(pwGA.add pwGV).mul hψ, ?_⟩, ⟨pq3.mul hψ, ?_⟩, ⟨pq1.mul hψ, ?_⟩, ⟨(pq1.add pq2).mul hψ, ?_⟩,
    ⟨(pq3.add pq4).mul hψ, ?_⟩, ⟨pwGA.mul pψ1, ?_⟩, ⟨(pwGA.add pwGV).mul pψ1, ?_⟩⟩
  · exact (ND.mul dUV3 hd).trans (by omega)
  · exact (ND.mul dUV3 dψ1).trans (by omega)
  · exact (ND.mul dUV3 dψ2).trans (by omega)
  · exact (ND.mul dwGA hd).trans (by omega)
  · exact (ND.mul (ND.add dwGA dwGV) hd).trans (by omega)
  · exact (ND.mul dq3 hd).trans (by omega)
  · exact (ND.mul dq1 hd).trans (by omega)
  · exact (ND.mul (ND.add dq1 dq2) hd).trans (by omega)
  · exact (ND.mul (ND.add dq3 dq4) hd).trans (by omega)
  · exact (ND.mul dwGA dψ1).trans (by omega)
  · exact (ND.mul (ND.add dwGA dwGV) dψ1).trans (by omega)

/-! ## The summation and the cancellation -/

theorem sum_harm_one_modp (hp5 : 5 ≤ p) {g : ℚ[X]} (hg : Adm p g) :
    PDv p 1 (∑ u ∈ range p, g.eval (u : ℚ) * harm 1 u - bI g) := by
  have h := sum_harm_one hp5 hg
  have hmu : bMu g ∈ LocRing p := (hg.faul_divX hp5).bI_mem hp5
  have h2 : PDv p 1 ((p : ℚ) * bMu g) := ⟨bMu g, hmu, by ring⟩
  have := (PDv.mono (j := 1) (by norm_num) h).sub h2
  convert this using 1; ring

/-- The table as a linear combination of the weight evaluations. -/
noncomputable def TabP (a A : ℕ) (ψ : ℚ[X]) (s : ℕ) : ℚ :=
  (-7) * (wG a A ψ).eval (s : ℚ) +
  ((p : ℚ) * (-5)) * (wW1 a A ψ).eval (s : ℚ) +
  ((p : ℚ) * 7) * ((wG a A ψ).eval (s : ℚ) * harm 1 s) +
  ((p : ℚ) * (-28)) * (wGA a A ψ).eval (s : ℚ) +
  ((p : ℚ) * 6) * (wGN a A ψ).eval (s : ℚ) +
  ((p : ℚ) ^ 2 * (-(3 * 2⁻¹))) * (wW2 a A ψ).eval (s : ℚ) +
  ((p : ℚ) ^ 2 * (-(7 * 2⁻¹))) * ((wG a A ψ).eval (s : ℚ) * harm 1 s ^ 2) +
  ((p : ℚ) ^ 2 * (67 * 2⁻¹)) * ((wG a A ψ).eval (s : ℚ) * harm 2 s) +
  ((p : ℚ) ^ 2 * (-56)) * (wGAA a A ψ).eval (s : ℚ) +
  ((p : ℚ) ^ 2 * (-8)) * (wGA2 a A ψ).eval (s : ℚ) +
  ((p : ℚ) ^ 2 * (-21)) * (wGN2 a A ψ).eval (s : ℚ) +
  ((p : ℚ) ^ 2 * 5) * ((wW1 a A ψ).eval (s : ℚ) * harm 1 s) +
  ((p : ℚ) ^ 2 * (-20)) * (wW1A a A ψ).eval (s : ℚ) +
  ((p : ℚ) ^ 2 * 6) * (wW1N a A ψ).eval (s : ℚ) +
  ((p : ℚ) ^ 2 * 28) * ((wGA a A ψ).eval (s : ℚ) * harm 1 s) +
  ((p : ℚ) ^ 2 * (-6)) * ((wGN a A ψ).eval (s : ℚ) * harm 1 s) +
  ((p : ℚ) ^ 2 * 24) * (wGAN a A ψ).eval (s : ℚ)

theorem TabF_eq_TabP (hAa : A < a) {s : ℕ} (hs : a ≤ s) (ψ : ℚ[X]) :
    TabF p (harm 1 s) (harm 2 s) (dsum a 1 s) (dsum (A + 1) 1 s) (dsum a 2 s) (dsum (A + 1) 2 s)
        (((Dfall a).eval (s : ℚ)) ^ 3) (ψ.eval (s : ℚ)) ((derivative ψ).eval (s : ℚ))
        ((derivative (derivative ψ)).eval (s : ℚ)) = TabP (p := p) a A ψ s := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := weights_eval hAa hs ψ
  unfold TabF TabP
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  ring

theorem TabP_zero (hAa : A < a) {s : ℕ} (hs : s < a) (ψ : ℚ[X]) : TabP (p := p) a A ψ s = 0 := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := weights_zero hAa hs ψ
  unfold TabP
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  ring

theorem pdv_pt {m k : ℕ} (hmk : m + k = 3) {c x : ℚ} (hc : c ∈ LocRing p) (hx : PDv p k x) :
    PDv p 3 ((p : ℚ) ^ m * c * x) := by
  have h := PDv.mul (j := m) (k := k) (⟨c, hc, rfl⟩ : PDv p m ((p : ℚ) ^ m * c)) hx
  rwa [hmk] at h

theorem tab_sum (hB : Band p n a A) {ψ : ℚ[X]} (hψ : PInt p ψ) {d : ℕ} (hd : ψ.natDegree ≤ d)
    (hda : 3 * a + d ≤ p - 3) :
    PDv p 3 (∑ s ∈ range p, TabP (p := p) a A ψ s - 15 * (p : ℚ) ^ 2 * bL (wG a A ψ)) := by
  have hp5 := hB.p5
  obtain ⟨hG, hW1, hW2, hGA, hGN, hGAA, hGA2, hGN2, hGAN, hW1A, hW1N⟩ := weights_adm hB hψ hd hda
  have h2 : (2 : ℚ)⁻¹ ∈ LocRing p := two_inv_mem (by omega)
  -- the sums
  have hsum : ∑ s ∈ range p, TabP (p := p) a A ψ s =
      (-7) * ∑ s ∈ range p, (wG a A ψ).eval (s : ℚ) +
      ((p : ℚ) * (-5)) * ∑ s ∈ range p, (wW1 a A ψ).eval (s : ℚ) +
      ((p : ℚ) * 7) * ∑ s ∈ range p, ((wG a A ψ).eval (s : ℚ) * harm 1 s) +
      ((p : ℚ) * (-28)) * ∑ s ∈ range p, (wGA a A ψ).eval (s : ℚ) +
      ((p : ℚ) * 6) * ∑ s ∈ range p, (wGN a A ψ).eval (s : ℚ) +
      ((p : ℚ) ^ 2 * (-(3 * 2⁻¹))) * ∑ s ∈ range p, (wW2 a A ψ).eval (s : ℚ) +
      ((p : ℚ) ^ 2 * (-(7 * 2⁻¹))) * ∑ s ∈ range p, ((wG a A ψ).eval (s : ℚ) * harm 1 s ^ 2) +
      ((p : ℚ) ^ 2 * (67 * 2⁻¹)) * ∑ s ∈ range p, ((wG a A ψ).eval (s : ℚ) * harm 2 s) +
      ((p : ℚ) ^ 2 * (-56)) * ∑ s ∈ range p, (wGAA a A ψ).eval (s : ℚ) +
      ((p : ℚ) ^ 2 * (-8)) * ∑ s ∈ range p, (wGA2 a A ψ).eval (s : ℚ) +
      ((p : ℚ) ^ 2 * (-21)) * ∑ s ∈ range p, (wGN2 a A ψ).eval (s : ℚ) +
      ((p : ℚ) ^ 2 * 5) * ∑ s ∈ range p, ((wW1 a A ψ).eval (s : ℚ) * harm 1 s) +
      ((p : ℚ) ^ 2 * (-20)) * ∑ s ∈ range p, (wW1A a A ψ).eval (s : ℚ) +
      ((p : ℚ) ^ 2 * 6) * ∑ s ∈ range p, (wW1N a A ψ).eval (s : ℚ) +
      ((p : ℚ) ^ 2 * 28) * ∑ s ∈ range p, ((wGA a A ψ).eval (s : ℚ) * harm 1 s) +
      ((p : ℚ) ^ 2 * (-6)) * ∑ s ∈ range p, ((wGN a A ψ).eval (s : ℚ) * harm 1 s) +
      ((p : ℚ) ^ 2 * 24) * ∑ s ∈ range p, (wGAN a A ψ).eval (s : ℚ) := by
    unfold TabP
    simp only [sum_add_distrib, ← mul_sum]
  -- the congruences
  obtain ⟨t0, ht0, e0⟩ := sum_poly_eq hp5 hG
  have A_G : PDv p 3 (∑ s ∈ range p, (wG a A ψ).eval (s : ℚ) - ((p : ℚ) * bI (wG a A ψ) + (p : ℚ) ^ 2 * (bL (wG a A ψ) / 2))) :=
    ⟨t0, ht0, by rw [e0]; ring⟩
  have A_W1 := sum_poly_pdv2 hp5 hW1
  have A_GH := sum_harm_one hp5 hG
  have A_GA := sum_poly_pdv2 hp5 hGA
  have A_GN := sum_poly_pdv2 hp5 hGN
  have A_W2 := sum_poly_pdv hp5 hW2
  have A_GHH := sum_harm_sq hp5 hG
  have A_GH2 := sum_harm_two hp5 hG
  have A_GAA := sum_poly_pdv hp5 hGAA
  have A_GA2 := sum_poly_pdv hp5 hGA2
  have A_GN2 := sum_poly_pdv hp5 hGN2
  have A_W1H := sum_harm_one_modp hp5 hW1
  have A_W1A := sum_poly_pdv hp5 hW1A
  have A_W1N := sum_poly_pdv hp5 hW1N
  have A_GAH := sum_harm_one_modp hp5 hGA
  have A_GNH := sum_harm_one_modp hp5 hGN
  have A_GAN := sum_poly_pdv hp5 hGAN
  have c : ∀ (q : ℚ), q ∈ LocRing p → q ∈ LocRing p := fun q h => h
  have T0 := pdv_pt (p := p) (m := 0) (k := 3) (by norm_num) (c := -7) (by rmem) A_G
  have T1 := pdv_pt (p := p) (m := 1) (k := 2) (by norm_num) (c := -5) (by rmem) A_W1
  have T2 := pdv_pt (p := p) (m := 1) (k := 2) (by norm_num) (c := 7) (by rmem) A_GH
  have T3 := pdv_pt (p := p) (m := 1) (k := 2) (by norm_num) (c := -28) (by rmem) A_GA
  have T4 := pdv_pt (p := p) (m := 1) (k := 2) (by norm_num) (c := 6) (by rmem) A_GN
  have T5 := pdv_pt (p := p) (m := 2) (k := 1) (by norm_num) (c := -(3 * 2⁻¹)) (by rmem) A_W2
  have T6 := pdv_pt (p := p) (m := 2) (k := 1) (by norm_num) (c := -(7 * 2⁻¹)) (by rmem) A_GHH
  have T7 := pdv_pt (p := p) (m := 2) (k := 1) (by norm_num) (c := 67 * 2⁻¹) (by rmem) A_GH2
  have T8 := pdv_pt (p := p) (m := 2) (k := 1) (by norm_num) (c := -56) (by rmem) A_GAA
  have T9 := pdv_pt (p := p) (m := 2) (k := 1) (by norm_num) (c := -8) (by rmem) A_GA2
  have T10 := pdv_pt (p := p) (m := 2) (k := 1) (by norm_num) (c := -21) (by rmem) A_GN2
  have T11 := pdv_pt (p := p) (m := 2) (k := 1) (by norm_num) (c := 5) (by rmem) A_W1H
  have T12 := pdv_pt (p := p) (m := 2) (k := 1) (by norm_num) (c := -20) (by rmem) A_W1A
  have T13 := pdv_pt (p := p) (m := 2) (k := 1) (by norm_num) (c := 6) (by rmem) A_W1N
  have T14 := pdv_pt (p := p) (m := 2) (k := 1) (by norm_num) (c := 28) (by rmem) A_GAH
  have T15 := pdv_pt (p := p) (m := 2) (k := 1) (by norm_num) (c := -6) (by rmem) A_GNH
  have T16 := pdv_pt (p := p) (m := 2) (k := 1) (by norm_num) (c := 24) (by rmem) A_GAN
  have U1 := T0.add T1
  have U2 := U1.add T2
  have U3 := U2.add T3
  have U4 := U3.add T4
  have U5 := U4.add T5
  have U6 := U5.add T6
  have U7 := U6.add T7
  have U8 := U7.add T8
  have U9 := U8.add T9
  have U10 := U9.add T10
  have U11 := U10.add T11
  have U12 := U11.add T12
  have U13 := U12.add T13
  have U14 := U13.add T14
  have U15 := U14.add T15
  have this := U15.add T16
  convert this using 1
  rw [hsum]
  ring

theorem K0_sub (hB : Band p n a A) :
    PDv p 1 (K0 p n A - 32 * (((A !) : ℕ) : ℚ) ^ 2 * ((((a - 1) !) : ℕ) : ℚ) ^ 3) := by
  have hhA := hB.hA
  have hha := hB.ha
  have hAa := hB.hAa
  have hp5 := hB.p5
  have rm := fact_reflect (p := p) (a - 1) (by omega)
  rw [show p - 1 - (a - 1) = 2 * n by omega] at rm
  have hsig : (-1 : ℚ) ^ (a - 1) = 1 := Even.neg_one_pow (by
    obtain ⟨k, hk⟩ := hB.a_odd; exact ⟨k, by omega⟩)
  rw [hsig, mul_one] at rm
  have hEJ := EJ_Pj hp5 (-1) (a - 1) (by omega)
  have h1 : PDv p 1 (Pj p (-1) (a - 1) - 1) := by
    have h3 := PDv.mono (j := 1) (by norm_num) hEJ.2.2.2
    have h4 : PDv p 1 ((p : ℚ) * (((-1 : ℤ) : ℚ) * harm 1 (a - 1)) +
        (p : ℚ) ^ 2 * (-(((-1 : ℤ) : ℚ) ^ 2 / 2) * harm 2 (a - 1) +
          (((-1 : ℤ) : ℚ) * harm 1 (a - 1)) ^ 2 / 2)) := by
      have h2i : (2 : ℚ)⁻¹ ∈ LocRing p := two_inv_mem (by omega)
      refine ⟨((-1 : ℤ) : ℚ) * harm 1 (a - 1) + (p : ℚ) * (-(((-1 : ℤ) : ℚ) ^ 2 * 2⁻¹) * harm 2 (a - 1) +
          (((-1 : ℤ) : ℚ) * harm 1 (a - 1)) ^ 2 * 2⁻¹), ?_, by ring⟩
      have h1 : harm 1 (a - 1) ∈ LocRing p := harm_mem (by omega)
      have h2 : harm 2 (a - 1) ∈ LocRing p := harm_mem (by omega)
      have hm1 : ((-1 : ℤ) : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (-1)
      have := p_mem (p := p)
      rmem
    have := h3.add h4
    convert this using 1; ring
  have hPm : Pj p (-1) (a - 1) ∈ LocRing p := hEJ.1
  have hF : (((p - 1) ! : ℕ) : ℚ) = (((2 * n) ! : ℕ) : ℚ) * ((((a - 1) !) : ℕ) : ℚ) * Pj p (-1) (a - 1) := by
    rw [rm]
  have hne : (((2 * n) ! : ℕ) : ℚ) ≠ 0 := by positivity
  have e : K0 p n A - 32 * (((A !) : ℕ) : ℚ) ^ 2 * ((((a - 1) !) : ℕ) : ℚ) ^ 3 =
      (32 * (((A !) : ℕ) : ℚ) ^ 2 * ((((a - 1) !) : ℕ) : ℚ) ^ 3) *
        ((Pj p (-1) (a - 1) - 1) * (Pj p (-1) (a - 1) ^ 2 + Pj p (-1) (a - 1) + 1)) := by
    unfold K0
    rw [hF]
    field_simp
    ring
  rw [e]
  have h32 : (32 * (((A !) : ℕ) : ℚ) ^ 2 * ((((a - 1) !) : ℕ) : ℚ) ^ 3) ∈ LocRing p := by
    have := natCast_mem (p := p) (A !); have := natCast_mem (p := p) ((a - 1) !); rmem
  exact PDv.mul_left h32 (PDv.mul_right h1 (by rmem))

omit hp in
theorem wG_eq (hAa : A < a) (ψ : ℚ[X]) : wG a A ψ = Dfall a ^ 3 * ψ := by
  unfold wG; rw [Dfall_eq a A hAa]; ring

theorem natDegree_comp_neg_le (g : ℚ[X]) : (g.comp (-X)).natDegree ≤ g.natDegree := by
  refine natDegree_le_iff_coeff_eq_zero.2 fun N hN => ?_
  rw [coeff_comp_neg_X, coeff_eq_zero_of_natDegree_lt hN, mul_zero]

/-- **Lemma G3 (finite form).**  Let `p ≥ 5` be prime, `8n < 3p`, `p + 1 < 3n`, `a = p - 2n`,
`A = 6n - 2p`, `K = 3n - 1 - p`, and `φ ∈ ℤ_(p)[t]` of degree `≤ 2K - 2`.  Then
`L(Π² φ) ≡ 15 K₀ p³ λ(D_a³ · φ(-x)) (mod p⁴)`, i.e. `p⁻³ L(Π² φ) ≡ 15 K₀ λ(D_a³ φ(-x)) (mod p)`. -/
theorem lemma_G3 (hB : Band p n a A) {ph : ℚ[X]} (hph : PInt p ph)
    (hdeg : ph.natDegree + 2 ≤ 2 * (3 * n - 1 - p)) :
    PDv p 4 (Lf n (PiA a A ^ 2 * ph) -
      15 * K0 p n A * (p : ℚ) ^ 3 * bL (Dfall a ^ 3 * ph.comp (-X))) := by
  have hAa := hB.hAa
  have hha := hB.ha
  have hhA := hB.hA
  have hhn := hB.hn
  have hp5 := hB.p5
  have h2i : (2 : ℚ)⁻¹ ∈ LocRing p := two_inv_mem (by omega)
  have hpm : (p : ℚ) ∈ LocRing p := p_mem
  have hψ : PInt p (ph.comp (-X)) := PInt.comp_neg hph
  set ψ := ph.comp (-X) with hψdef
  have hd : ψ.natDegree ≤ ph.natDegree := natDegree_comp_neg_le ph
  have hda : 3 * a + ph.natDegree ≤ p - 3 := by omega
  have hL := Lf_main hB hph
  have hnode : ∀ s ∈ Ico a p, PDv p 4 (tauK n a A ph (p + s) -
      (p : ℚ) * (32 * (((A !) : ℕ) : ℚ) ^ 2 * ((((a - 1) !) : ℕ) : ℚ) ^ 3) *
        Ejet p (4 * harm 1 A - 3 * harm 1 (a - 1)) (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) *
        TabP (p := p) a A ψ s) := by
    intro s hs
    rw [mem_Ico] at hs
    have h := node_term (n := n) (u := s - a) (m := s - A - 1) hB hs.1 hs.2 (by omega) (by omega) hph
    rw [← hψdef] at h
    rw [← TabF_eq_TabP hAa hs.1 ψ]
    exact h
  have hS := PDv.sum (Ico a p) _ hnode
  rw [sum_sub_distrib, ← mul_sum] at hS
  have hsplit : ∑ s ∈ range p, TabP (p := p) a A ψ s = ∑ s ∈ Ico a p, TabP (p := p) a A ψ s := by
    rw [← sum_range_add_sum_Ico _ (show a ≤ p by omega),
      sum_eq_zero (fun s hs => TabP_zero hAa (mem_range.1 hs) ψ), zero_add]
  have htab := tab_sum hB hψ hd hda
  rw [hsplit] at htab
  have hG : Adm p (wG a A ψ) := (weights_adm hB hψ hd hda).1
  have hlam : bL (wG a A ψ) ∈ LocRing p := hG.bL_mem hp5
  have hK' : (32 * (((A !) : ℕ) : ℚ) ^ 2 * ((((a - 1) !) : ℕ) : ℚ) ^ 3) ∈ LocRing p := by
    have := natCast_mem (p := p) (A !); have := natCast_mem (p := p) ((a - 1) !); rmem
  have hHA1 : harm 1 A ∈ LocRing p := harm_mem (by omega)
  have hHA2 : harm 2 A ∈ LocRing p := harm_mem (by omega)
  have hHa1 : harm 1 (a - 1) ∈ LocRing p := harm_mem (by omega)
  have hHa2 : harm 2 (a - 1) ∈ LocRing p := harm_mem (by omega)
  have hT0m : Ejet p (4 * harm 1 A - 3 * harm 1 (a - 1)) (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) ∈
      LocRing p := by unfold Ejet; rmem
  have hT0one : PDv p 1 (Ejet p (4 * harm 1 A - 3 * harm 1 (a - 1)) (-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) - 1) := by
    refine ⟨(4 * harm 1 A - 3 * harm 1 (a - 1)) + p * ((-4 * harm 2 A - (3 * 2⁻¹) * harm 2 (a - 1)) +
      (4 * harm 1 A - 3 * harm 1 (a - 1)) ^ 2 * 2⁻¹), by rmem, ?_⟩
    unfold Ejet; ring
  have hK0 := K0_sub hB
  have c3 := PDv.mul (j := 1) (k := 3) pPDv_one
    (PDv.mul_left ((LocRing p).mul_mem hK' hT0m) htab)
  have c4 := PDv.mul (j := 3) (k := 1)
    (⟨15 * bL (wG a A ψ) * (32 * (((A !) : ℕ) : ℚ) ^ 2 * ((((a - 1) !) : ℕ) : ℚ) ^ 3), by rmem, by ring⟩ :
      PDv p 3 ((p : ℚ) ^ 3 * (15 * bL (wG a A ψ) * (32 * (((A !) : ℕ) : ℚ) ^ 2 * ((((a - 1) !) : ℕ) : ℚ) ^ 3))))
    hT0one
  have c5 := PDv.mul (j := 3) (k := 1)
    (⟨15 * bL (wG a A ψ), by rmem, by ring⟩ : PDv p 3 ((p : ℚ) ^ 3 * (15 * bL (wG a A ψ)))) hK0
  have hsum := ((hL.add hS).add c3).add (c4.add c5.neg)
  rw [wG_eq hAa ψ] at hsum
  convert hsum using 1
  ring

omit hp in
theorem bL_eq_range (g : ℚ[X]) {N : ℕ} (hN : g.natDegree < N) :
    bL g = ∑ e ∈ range N, g.coeff e * (e : ℚ) * bernoulli (e - 1) := by
  unfold bL
  refine sum_subset (range_subset_range.2 (by omega)) fun e _ he => ?_
  have : g.coeff e = 0 := coeff_eq_zero_of_natDegree_lt (by
    have := mem_range.not.1 he; omega)
  rw [this]; ring

omit hp in
theorem bL_C_mul (c : ℚ) (g : ℚ[X]) : bL (C c * g) = c * bL g := by
  have h1 : (C c * g).natDegree < g.natDegree + 1 := lt_of_le_of_lt (natDegree_C_mul_le c g) (Nat.lt_succ_self _)
  rw [bL_eq_range (C c * g) h1]
  unfold bL
  rw [mul_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [coeff_C_mul]; ring

/-- **The form consumed by the half block (LB09).**  For `0 ≤ e ≤ 2K - 2`:
`p⁻³ L(Π² t^e) ≡ 15 K₀ (-1)^e λ(D_a³ t^e) (mod p)`. -/
theorem lemma_G3_monomial (hB : Band p n a A) {e : ℕ} (he : e + 2 ≤ 2 * (3 * n - 1 - p)) :
    PDv p 4 (Lf n (PiA a A ^ 2 * X ^ e) -
      15 * K0 p n A * (p : ℚ) ^ 3 * ((-1) ^ e * bL (Dfall a ^ 3 * X ^ e))) := by
  have hX : PInt p ((X : ℚ[X]) ^ e) := PInt.pow PInt.ofX e
  have h := lemma_G3 hB hX (by rw [natDegree_X_pow]; exact he)
  have e1 : ((X : ℚ[X]) ^ e).comp (-X) = C ((-1 : ℚ) ^ e) * X ^ e := by
    rw [pow_comp, X_comp, neg_pow]; simp [C_pow]
  rw [e1, show Dfall a ^ 3 * (C ((-1 : ℚ) ^ e) * X ^ e) = C ((-1 : ℚ) ^ e) * (Dfall a ^ 3 * X ^ e) by ring,
    bL_C_mul] at h
  exact h

end Weights

end CatalanCore.Lai.B83Half
