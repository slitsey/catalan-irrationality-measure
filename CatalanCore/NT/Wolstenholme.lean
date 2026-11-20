module

public import CatalanCore.Basic.PrimePower
public import CatalanCore.Basic.ZModGood
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Wolstenholme's congruences and `p`-adic bookkeeping for harmonic sums (ledger LB07a)

Generic over a prime `p`.  `harm r k = ∑_{i=1}^k i^{-r}`.

* `wolstenholme_one`: `H_{p-1} ≡ 0 (mod p²)`, `wolstenholme_two`: `H^{(2)}_{p-1} ≡ 0 (mod p)` (`p ≥ 5`);
* `PDv p k x`: `x ∈ p^k ℤ_(p)`, with its calculus.
-/

namespace CatalanCore.NT

open Finset CatalanCore.Basic

/-- `H^{(r)}_k = ∑_{i=1}^{k} i^{-r}`. -/
def harm (r k : ℕ) : ℚ := ∑ i ∈ range k, (((i : ℚ) + 1) ^ r)⁻¹

theorem harm_zero (r : ℕ) : harm r 0 = 0 := by simp [harm]

theorem harm_succ (r k : ℕ) : harm r (k + 1) = harm r k + (((k : ℚ) + 1) ^ r)⁻¹ := by
  simp [harm, sum_range_succ]

section PDv

variable (p : ℕ) [hp : Fact p.Prime]

/-- `x ∈ p^k ℤ_(p)`. -/
def PDv (k : ℕ) (x : ℚ) : Prop := ∃ z : ℚ, z ∈ LocRing p ∧ x = (p : ℚ) ^ k * z

variable {p}

theorem PDv.zero (k : ℕ) : PDv p k 0 := ⟨0, (LocRing p).zero_mem, by simp⟩

theorem PDv.add {k : ℕ} {x y : ℚ} (hx : PDv p k x) (hy : PDv p k y) : PDv p k (x + y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a + b, (LocRing p).add_mem ha hb, by ring⟩

theorem PDv.neg {k : ℕ} {x : ℚ} (hx : PDv p k x) : PDv p k (-x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨-a, (LocRing p).neg_mem ha, by ring⟩

theorem PDv.sub {k : ℕ} {x y : ℚ} (hx : PDv p k x) (hy : PDv p k y) : PDv p k (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

theorem PDv.mul_left {k : ℕ} {x y : ℚ} (hx : x ∈ LocRing p) (hy : PDv p k y) : PDv p k (x * y) := by
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨x * b, (LocRing p).mul_mem hx hb, by ring⟩

theorem PDv.mul_right {k : ℕ} {x y : ℚ} (hx : PDv p k x) (hy : y ∈ LocRing p) : PDv p k (x * y) := by
  rw [mul_comm]; exact PDv.mul_left hy hx

theorem PDv.mul {j k : ℕ} {x y : ℚ} (hx : PDv p j x) (hy : PDv p k y) : PDv p (j + k) (x * y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a * b, (LocRing p).mul_mem ha hb, by ring⟩

theorem PDv.mono {j k : ℕ} (h : j ≤ k) {x : ℚ} (hx : PDv p k x) : PDv p j x := by
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨(p : ℚ) ^ (k - j) * a, (LocRing p).mul_mem ((LocRing p).pow_mem
    (by exact_mod_cast int_mem_locRing (ℓ := p) (p : ℤ)) _) ha, ?_⟩
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

theorem PDv.of_mem {x : ℚ} (hx : x ∈ LocRing p) : PDv p 0 x := ⟨x, hx, by simp⟩

theorem PDv.mem {x : ℚ} (hx : PDv p 0 x) : x ∈ LocRing p := by
  obtain ⟨a, ha, rfl⟩ := hx; simpa using ha

theorem PDv.zero_pow_mem {k : ℕ} {x : ℚ} (hx : PDv p k x) : x ∈ LocRing p :=
  (PDv.mono (Nat.zero_le k) hx).mem

theorem PDv.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) {k : ℕ} (h : ∀ i ∈ s, PDv p k (f i)) :
    PDv p k (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PDv.zero k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem pPDv_one : PDv p 1 (p : ℚ) := ⟨1, (LocRing p).one_mem, by simp⟩

theorem natCast_mem (n : ℕ) : (n : ℚ) ∈ LocRing p := by
  exact_mod_cast int_mem_locRing (ℓ := p) (n : ℤ)

theorem p_mem : (p : ℚ) ∈ LocRing p := natCast_mem p

theorem p_ne_zero : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero

theorem PDv.of_mul_pow {k : ℕ} {x : ℚ} (hx : x ∈ LocRing p) : PDv p k ((p : ℚ) ^ k * x) :=
  ⟨x, hx, rfl⟩

/-- `1 / i ∈ ℤ_(p)` for `0 < i < p`. -/
theorem inv_mem_of_lt {i : ℕ} (h0 : 0 < i) (h : i < p) : ((i : ℚ))⁻¹ ∈ LocRing p :=
  inv_natCast_mem_locRing (fun hd => absurd (Nat.le_of_dvd h0 hd) (by omega))

theorem inv_succ_mem_of_lt {i : ℕ} (h : i + 1 < p) : (((i : ℚ) + 1))⁻¹ ∈ LocRing p := by
  have := inv_mem_of_lt (p := p) (Nat.succ_pos i) h
  simpa using this

theorem two_inv_mem (hp5 : 3 ≤ p) : ((2 : ℚ))⁻¹ ∈ LocRing p := by
  have := inv_mem_of_lt (p := p) (i := 2) (by norm_num) (by omega)
  simpa using this

/-- Divisibility by `p` of a `p`-integral rational that reduces to `0` in `𝔽_p`. -/
theorem pdv_one_of_red_zero {x : ℚ} (hx : x ∈ LocRing p) (h : (x : ZMod p) = 0) : PDv p 1 x := by
  rw [Rat.cast_def] at h
  have hd : ((x.den : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hx
  have hn : (x.num : ZMod p) = 0 := by
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h hd
  obtain ⟨t, ht⟩ : (p : ℤ) ∣ x.num := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hn
  have hy : ((t : ℚ) / (x.den : ℚ)) ∈ LocRing p := by
    rw [mem_locRing]
    have e : ((t : ℚ) / (x.den : ℚ)) = Rat.divInt t (x.den : ℤ) := by
      rw [Rat.divInt_eq_div]; push_cast; rfl
    rw [e]
    intro hdv
    have h1 := Rat.den_dvd t (x.den : ℤ)
    have h2 : (p : ℤ) ∣ (x.den : ℤ) := (Int.natCast_dvd_natCast.2 hdv).trans h1
    exact hx (Int.natCast_dvd_natCast.1 h2)
  refine ⟨(t : ℚ) / (x.den : ℚ), hy, ?_⟩
  have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hnum : x = (x.num : ℚ) / (x.den : ℚ) := (Rat.num_div_den _).symm
  have hnum' : (x.num : ℚ) = (p : ℚ) * t := by exact_mod_cast ht
  calc x = (x.num : ℚ) / (x.den : ℚ) := hnum
    _ = _ := by rw [hnum']; ring

end PDv

section Wolstenholme

variable {p : ℕ} [hp : Fact p.Prime]

/-- The sum over a residue system: `∑_{i<p} F(i mod p) = ∑_{x : ZMod p} F x`. -/
theorem sum_range_eq_sum_zmod (F : ZMod p → ZMod p) :
    ∑ i ∈ range p, F (i : ZMod p) = ∑ x : ZMod p, F x := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hsurj : (range p).image (fun i : ℕ => (i : ZMod p)) = Finset.univ := by
    ext x
    simp only [mem_image, mem_range, Finset.mem_univ, iff_true]
    exact ⟨x.val, ZMod.val_lt x, ZMod.natCast_zmod_val x⟩
  rw [← hsurj, Finset.sum_image]
  intro a ha b hb hab
  simp only [coe_range, Set.mem_Iio] at ha hb
  have := (ZMod.natCast_eq_natCast_iff' a b p).1 hab
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- `H^{(2)}_{p-1} ≡ 0 (mod p)` for `p ≥ 5`. -/
theorem wolstenholme_two (hp5 : 5 ≤ p) : PDv p 1 (harm 2 (p - 1)) := by
  have hmem : ∀ i ∈ range (p - 1), (((((i : ℚ) + 1)) ^ 2)⁻¹) ∈ LocRing p := by
    intro i hi
    have hi' : i + 1 < p := by have := mem_range.1 hi; omega
    have := (LocRing p).pow_mem (inv_succ_mem_of_lt (p := p) hi') 2
    simpa [inv_pow] using this
  have hmem' : harm 2 (p - 1) ∈ LocRing p := (LocRing p).sum_mem hmem
  refine pdv_one_of_red_zero hmem' ?_
  -- reduction mod p
  have hgood : ∀ i ∈ range (p - 1),
      CatalanCore.Good p (((((i : ℚ) + 1)) ^ 2)⁻¹) ((((i : ZMod p) + 1)) ^ 2)⁻¹ := by
    intro i hi
    have hi' : i + 1 < p := by have := mem_range.1 hi; omega
    have hne : (((i : ZMod p) + 1)) ^ 2 ≠ 0 := by
      have : ((i + 1 : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]; exact fun hd => absurd (Nat.le_of_dvd (Nat.succ_pos i) hd) (by omega)
      push_cast at this
      exact pow_ne_zero 2 this
    have h1 : CatalanCore.Good p (((i : ℚ) + 1)) (((i : ZMod p) + 1)) := by
      have := CatalanCore.Good.natCast (ℓ := p) (i + 1)
      simpa using this
    exact (h1.pow' 2).inv hne
  have hG := CatalanCore.Good.sum (ℓ := p) (range (p - 1)) _ _ hgood
  have hred : ((harm 2 (p - 1) : ℚ) : ZMod p) = ∑ i ∈ range (p - 1), ((((i : ZMod p) + 1)) ^ 2)⁻¹ := by
    have := hG.2
    simpa [harm, CatalanCore.red] using this
  rw [hred]
  -- ∑_{i=1}^{p-1} (i⁻¹)² = ∑_{x} (x⁻¹)² = ∑_x x² = 0
  have h1 : ∑ i ∈ range (p - 1), ((((i : ZMod p) + 1)) ^ 2)⁻¹ =
      ∑ i ∈ range p, (((i : ZMod p)⁻¹) ^ 2) := by
    have e : ∀ m : ℕ, ∑ i ∈ range (m + 1), (((i : ZMod p)⁻¹) ^ 2) =
        ∑ i ∈ range m, ((((i : ZMod p) + 1)) ^ 2)⁻¹ := by
      intro m
      rw [sum_range_succ']
      simp [inv_pow]
    have hp1 : p - 1 + 1 = p := by have := hp.out.pos; omega
    have := e (p - 1)
    rw [hp1] at this
    exact this.symm
  have h2 : ∑ i ∈ range p, (((i : ZMod p)⁻¹) ^ 2) = ∑ x : ZMod p, (x⁻¹) ^ 2 :=
    sum_range_eq_sum_zmod (fun x => (x⁻¹) ^ 2)
  have h3 : ∑ x : ZMod p, (x⁻¹) ^ 2 = ∑ x : ZMod p, x ^ 2 :=
    Equiv.sum_comp (Function.Involutive.toPerm (fun x : ZMod p => x⁻¹) inv_inv) (fun x => x ^ 2)
  have h4 : ∑ x : ZMod p, x ^ 2 = 0 :=
    FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) 2 (by rw [ZMod.card]; omega)
  rw [h1, h2, h3, h4]

/-- `H_{p-1} ≡ 0 (mod p²)` for `p ≥ 5` (Wolstenholme). -/
theorem wolstenholme_one (hp5 : 5 ≤ p) : PDv p 2 (harm 1 (p - 1)) := by
  obtain ⟨z, hz, hz'⟩ := wolstenholme_two hp5
  have hpos : ∀ i ∈ range (p - 1), (0 < p - (i + 1)) ∧ (p - (i + 1) < p) := by
    intro i hi; have := mem_range.1 hi; omega
  have hcast : ∀ i ∈ range (p - 1), ((p : ℚ) - ((i : ℚ) + 1)) = ((p - (i + 1) : ℕ) : ℚ) := by
    intro i hi
    have := mem_range.1 hi
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hne : ∀ i ∈ range (p - 1), ((p : ℚ) - ((i : ℚ) + 1)) ≠ 0 := by
    intro i hi
    rw [hcast i hi]
    exact_mod_cast (hpos i hi).1.ne'
  have hne1 : ∀ i : ℕ, ((i : ℚ) + 1) ≠ 0 := fun i => by positivity
  set W : ℚ := ∑ i ∈ range (p - 1), (((i : ℚ) + 1) ^ 2 * ((p : ℚ) - ((i : ℚ) + 1)))⁻¹ with hW
  have hWmem : W ∈ LocRing p := by
    refine (LocRing p).sum_mem fun i hi => ?_
    have h1 : (((i : ℚ) + 1))⁻¹ ∈ LocRing p := inv_succ_mem_of_lt (by have := mem_range.1 hi; omega)
    have h2 : ((p : ℚ) - ((i : ℚ) + 1))⁻¹ ∈ LocRing p := by
      rw [hcast i hi]; exact inv_mem_of_lt (hpos i hi).1 (hpos i hi).2
    have := (LocRing p).mul_mem ((LocRing p).pow_mem h1 2) h2
    convert this using 1
    rw [mul_inv, inv_pow]
  have h1 : harm 1 (p - 1) = ∑ i ∈ range (p - 1), (((p : ℚ) - ((i : ℚ) + 1)))⁻¹ := by
    unfold harm
    rw [← Finset.sum_range_reflect (fun j : ℕ => ((((j : ℚ) + 1)) ^ 1)⁻¹) (p - 1)]
    refine sum_congr rfl fun j hj => ?_
    have hj' := mem_range.1 hj
    have : ((p - 1 - 1 - j + 1 : ℕ) : ℚ) = ((p - (j + 1) : ℕ) : ℚ) := by congr 1; omega
    rw [pow_one, hcast j hj, ← this]
    push_cast
    rfl
  have key : 2 * harm 1 (p - 1) = -(p : ℚ) * harm 2 (p - 1) + (p : ℚ) ^ 2 * W := by
    have e1 : 2 * harm 1 (p - 1) = harm 1 (p - 1) + harm 1 (p - 1) := by ring
    rw [e1]
    nth_rewrite 2 [h1]
    unfold harm
    rw [hW, Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i hi => ?_
    have a1 := hne1 i
    have a2 := hne i hi
    simp only [pow_one]
    field_simp
    ring
  have : harm 1 (p - 1) = (p : ℚ) ^ 2 * ((-z + W) / 2) := by
    have h2 : (2 : ℚ) ≠ 0 := two_ne_zero
    have : 2 * harm 1 (p - 1) = (p : ℚ) ^ 2 * (-z + W) := by
      rw [key, hz']; ring
    field_simp
    linarith
  refine ⟨(-z + W) / 2, ?_, this⟩
  have hp3 : 3 ≤ p := by omega
  rw [div_eq_mul_inv]
  exact (LocRing p).mul_mem ((LocRing p).add_mem ((LocRing p).neg_mem hz) hWmem) (two_inv_mem hp3)

end Wolstenholme

section Bernoulli

variable {p : ℕ} [hp : Fact p.Prime]

theorem neg_half_mem (hp3 : 3 ≤ p) : (-1 / 2 : ℚ) ∈ LocRing p := by
  have := (LocRing p).neg_mem (two_inv_mem (p := p) hp3)
  convert this using 1; norm_num

/-- `B_n ∈ ℤ_(p)` for `n + 1 < p` (von Staudt–Clausen), `p ≥ 5`. -/
theorem bernoulli_mem (hp5 : 5 ≤ p) {n : ℕ} (hn : n + 1 < p) : bernoulli n ∈ LocRing p := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ho
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have : n = 0 := by omega
      subst this; simp [bernoulli_zero]
    · have hk2 : n = 2 * k := by omega
      subst hk2
      obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k
      have e : bernoulli (2 * k) = (z : ℚ) -
          ∑ q ∈ range (2 * k + 2) with q.Prime ∧ (q - 1) ∣ 2 * k, (1 : ℚ) / q := by
        rw [hz]; ring
      rw [e]
      refine (LocRing p).sub_mem (int_mem_locRing z) ((LocRing p).sum_mem fun q hq => ?_)
      rw [Finset.mem_filter] at hq
      have hpq : ¬ p ∣ q := by
        intro hd
        have h1 : p = q := (Nat.prime_dvd_prime_iff_eq hp.out hq.2.1).1 hd
        subst h1
        have := Nat.le_of_dvd (by omega) hq.2.2
        omega
      rw [one_div]; exact inv_natCast_mem_locRing hpq
  · rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by obtain ⟨m, hm⟩ := ho; omega
      subst this; rw [bernoulli_one]; exact neg_half_mem (by omega)
    · rw [bernoulli_eq_zero_of_odd ho (by omega)]; exact (LocRing p).zero_mem

end Bernoulli

/-! ### Faulhaber polynomials and the Bernoulli functionals -/

section Faulhaber

open Polynomial

/-- The Bernoulli functional `I(g) = ∑ g_e B_e` (`= ∫_{ℤ_p} g`). -/
noncomputable def bI (g : ℚ[X]) : ℚ := ∑ e ∈ range (g.natDegree + 1), g.coeff e * bernoulli e

/-- `λ(g) = I(g') = ∑ e g_e B_{e-1}`. -/
noncomputable def bL (g : ℚ[X]) : ℚ :=
  ∑ e ∈ range (g.natDegree + 1), g.coeff e * (e : ℚ) * bernoulli (e - 1)

/-- `x^e ↦ ∑_{i ≤ e} B_i C(e+1, i) x^{e+1-i} / (e+1)`: Faulhaber's polynomial of `∑_{k<x} k^e`. -/
noncomputable def faulE (e : ℕ) : ℚ[X] :=
  ∑ i ∈ range (e + 1), C (bernoulli i * (((e + 1).choose i : ℕ) : ℚ) / ((e : ℚ) + 1)) * X ^ (e + 1 - i)

/-- The coefficient of `x^j` in `faulE e`. -/
noncomputable def faulCoef (e j : ℕ) : ℚ :=
  if j = 0 then 0 else bernoulli (e + 1 - j) * (((e + 1).choose j : ℕ) : ℚ) / ((e : ℚ) + 1)

theorem faulE_eval (e n : ℕ) : (faulE e).eval (n : ℚ) = ∑ k ∈ range n, (k : ℚ) ^ e := by
  rw [sum_range_pow]
  simp only [faulE, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  refine sum_congr rfl fun i hi => ?_
  push_cast
  ring

theorem faulE_coeff (e j : ℕ) : (faulE e).coeff j = faulCoef e j := by
  unfold faulE faulCoef
  rw [finset_sum_coeff]
  simp only [coeff_C_mul_X_pow]
  by_cases hj0 : j = 0
  · subst hj0
    simp only [if_true]
    refine sum_eq_zero fun i hi => ?_
    have := mem_range.1 hi
    rw [if_neg]; omega
  · rw [if_neg hj0]
    by_cases hj : j ≤ e + 1
    · rw [sum_eq_single (e + 1 - j)]
      · rw [if_pos (by omega), Nat.choose_symm hj]
      · intro i hi hne
        rw [if_neg]; have := mem_range.1 hi; omega
      · intro h; exfalso; apply h; rw [mem_range]; omega
    · have hc : (e + 1).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hc]
      simp only [Nat.cast_zero, mul_zero, zero_div]
      refine sum_eq_zero fun i hi => ?_
      have := mem_range.1 hi
      rw [if_neg]; omega

/-- Faulhaber polynomial of `g`: `faul g (N) = ∑_{u<N} g(u)`. -/
noncomputable def faul (g : ℚ[X]) : ℚ[X] :=
  ∑ e ∈ range (g.natDegree + 1), C (g.coeff e) * faulE e

theorem faul_eval (g : ℚ[X]) (n : ℕ) : (faul g).eval (n : ℚ) = ∑ u ∈ range n, g.eval (u : ℚ) := by
  unfold faul
  simp only [eval_finset_sum, eval_mul, eval_C, faulE_eval]
  simp only [eval_eq_sum_range (p := g)]
  rw [sum_comm]
  refine sum_congr rfl fun e he => ?_
  rw [mul_sum]

theorem faul_coeff (g : ℚ[X]) (j : ℕ) :
    (faul g).coeff j = ∑ e ∈ range (g.natDegree + 1), g.coeff e * faulCoef e j := by
  unfold faul
  rw [finset_sum_coeff]
  refine sum_congr rfl fun e he => ?_
  rw [coeff_C_mul, faulE_coeff]

theorem faul_coeff_zero (g : ℚ[X]) : (faul g).coeff 0 = 0 := by
  rw [faul_coeff]; simp [faulCoef]

theorem faul_coeff_one (g : ℚ[X]) : (faul g).coeff 1 = bI g := by
  rw [faul_coeff]
  unfold bI
  refine sum_congr rfl fun e he => ?_
  have : ((e : ℚ) + 1) ≠ 0 := by positivity
  simp only [faulCoef, if_neg one_ne_zero, Nat.add_sub_cancel, Nat.choose_one_right]
  push_cast
  field_simp

theorem faul_coeff_two (g : ℚ[X]) : (faul g).coeff 2 = bL g / 2 := by
  rw [faul_coeff]
  unfold bL
  rw [sum_div]
  refine sum_congr rfl fun e he => ?_
  have hne : ((e : ℚ) + 1) ≠ 0 := by positivity
  rcases e with _ | e
  · simp [faulCoef]
  · have hc : (((e + 1 + 1).choose 2 : ℕ) : ℚ) = ((e : ℚ) + 2) * ((e : ℚ) + 1) / 2 := by
      rw [Nat.cast_choose_two]; push_cast; ring
    have h2 : e + 1 + 1 - 2 = e := by omega
    simp only [faulCoef, if_neg (two_ne_zero), h2, hc]
    have h3 : ((e : ℚ) + 1 + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

theorem faul_coeff_eq_zero (g : ℚ[X]) {j : ℕ} (hj : g.natDegree + 1 < j) : (faul g).coeff j = 0 := by
  rw [faul_coeff]
  refine sum_eq_zero fun e he => ?_
  have := mem_range.1 he
  have hc : (e + 1).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
  simp [faulCoef, hc]

theorem natDegree_faul_le (g : ℚ[X]) : (faul g).natDegree ≤ g.natDegree + 1 :=
  natDegree_le_iff_coeff_eq_zero.2 fun _ hN => faul_coeff_eq_zero g hN

/-- Integral polynomial. -/
def PInt (p : ℕ) [Fact p.Prime] (g : ℚ[X]) : Prop := ∀ i, g.coeff i ∈ LocRing p

variable {p : ℕ} [hp : Fact p.Prime]

theorem PInt.eval_mem {g : ℚ[X]} (hg : PInt p g) {x : ℚ} (hx : x ∈ LocRing p) :
    g.eval x ∈ LocRing p := by
  rw [eval_eq_sum_range]
  exact (LocRing p).sum_mem fun i _ => (LocRing p).mul_mem (hg i) ((LocRing p).pow_mem hx i)

theorem PInt.eval_nat {g : ℚ[X]} (hg : PInt p g) (n : ℕ) : g.eval (n : ℚ) ∈ LocRing p :=
  hg.eval_mem (natCast_mem n)

theorem PInt.divX {g : ℚ[X]} (hg : PInt p g) : PInt p g.divX := fun i => by
  rw [coeff_divX]; exact hg _

/-- Admissible polynomials for the summation lemmas: integral, degree at most `p - 3`. -/
def Adm (p : ℕ) [Fact p.Prime] (g : ℚ[X]) : Prop := PInt p g ∧ g.natDegree ≤ p - 3

theorem Adm.divX {g : ℚ[X]} (hg : Adm p g) : Adm p g.divX :=
  ⟨hg.1.divX, natDegree_divX_le.trans hg.2⟩

theorem faulCoef_mem (hp5 : 5 ≤ p) {e : ℕ} (he : e ≤ p - 3) (j : ℕ) : faulCoef e j ∈ LocRing p := by
  unfold faulCoef
  split_ifs with hj0
  · exact (LocRing p).zero_mem
  · by_cases hj : j ≤ e + 1
    · have hB : bernoulli (e + 1 - j) ∈ LocRing p := bernoulli_mem hp5 (by omega)
      have hinv : (((e : ℚ) + 1))⁻¹ ∈ LocRing p := inv_succ_mem_of_lt (by omega)
      have := (LocRing p).mul_mem ((LocRing p).mul_mem hB (natCast_mem ((e + 1).choose j))) hinv
      convert this using 1
      ring
    · have hc : (e + 1).choose j = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hc]; simp

theorem Adm.faul_coeff_mem (hp5 : 5 ≤ p) {g : ℚ[X]} (hg : Adm p g) (j : ℕ) :
    (faul g).coeff j ∈ LocRing p := by
  rw [faul_coeff]
  refine (LocRing p).sum_mem fun e he => (LocRing p).mul_mem (hg.1 e) (faulCoef_mem hp5 ?_ j)
  have := mem_range.1 he
  have := hg.2
  omega

theorem Adm.faul_divX (hp5 : 5 ≤ p) {g : ℚ[X]} (hg : Adm p g) : Adm p (faul g).divX := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [coeff_divX]; exact hg.faul_coeff_mem hp5 _
  · have h1 := natDegree_faul_le g
    have h2 := hg.2
    rw [natDegree_divX_eq_natDegree_tsub_one]
    omega

theorem Adm.bI_mem (hp5 : 5 ≤ p) {g : ℚ[X]} (hg : Adm p g) : bI g ∈ LocRing p := by
  unfold bI
  refine (LocRing p).sum_mem fun e he => (LocRing p).mul_mem (hg.1 e) (bernoulli_mem hp5 ?_)
  have := mem_range.1 he
  have := hg.2
  omega

theorem Adm.bL_mem (hp5 : 5 ≤ p) {g : ℚ[X]} (hg : Adm p g) : bL g ∈ LocRing p := by
  unfold bL
  refine (LocRing p).sum_mem fun e he => (LocRing p).mul_mem
    ((LocRing p).mul_mem (hg.1 e) (natCast_mem e)) (bernoulli_mem hp5 ?_)
  have := mem_range.1 he
  have := hg.2
  omega

/-- `μ(g) = I(𝒢/x)`, the second Bernoulli functional of the Faulhaber antiderivative. -/
noncomputable def bMu (g : ℚ[X]) : ℚ := bI (faul g).divX

end Faulhaber

/-! ### The summation lemmas L0-L3 over `range p` -/

section Sums

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

theorem harm_mem {r u : ℕ} (hu : u < p) : harm r u ∈ LocRing p := by
  refine (LocRing p).sum_mem fun i hi => ?_
  have h := inv_succ_mem_of_lt (p := p) (i := i) (by have := mem_range.1 hi; omega)
  have := (LocRing p).pow_mem h r
  simpa [inv_pow] using this

theorem eval_peel (f : ℚ[X]) (x : ℚ) : f.eval x = f.coeff 0 + x * f.divX.eval x := by
  conv_lhs => rw [← divX_mul_X_add f]
  simp only [eval_add, eval_mul, eval_C, eval_X]
  ring

/-- Abel summation for a double sum. -/
theorem abel_sum (g c : ℕ → ℚ) (N : ℕ) :
    ∑ u ∈ range (N + 1), g u * (∑ i ∈ range u, c i) =
      ∑ i ∈ range N, c i * (∑ u ∈ range (N + 1), g u - ∑ u ∈ range (i + 1), g u) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ (fun u => g u * ∑ i ∈ range u, c i) (N + 1), ih]
    rw [sum_range_succ (fun i => c i * (∑ u ∈ range (N + 1 + 1), g u - ∑ u ∈ range (i + 1), g u)) N]
    have h2 : ∑ u ∈ range (N + 1 + 1), g u = ∑ u ∈ range (N + 1), g u + g (N + 1) :=
      sum_range_succ _ _
    have h3 : ∀ i ∈ range N, c i * (∑ u ∈ range (N + 1 + 1), g u - ∑ u ∈ range (i + 1), g u) =
        c i * (∑ u ∈ range (N + 1), g u - ∑ u ∈ range (i + 1), g u) + c i * g (N + 1) := by
      intro i _; rw [h2]; ring
    rw [sum_congr rfl h3, sum_add_distrib, ← sum_mul, sum_range_succ c N, h2]
    ring

theorem harm_sq (u : ℕ) :
    (harm 1 u) ^ 2 = harm 2 u + 2 * ∑ i ∈ range u, harm 1 i * (((i : ℚ) + 1) ^ 1)⁻¹ := by
  induction u with
  | zero => simp [harm_zero]
  | succ u ih =>
    rw [harm_succ, harm_succ, sum_range_succ]
    have : ((u : ℚ) + 1) ≠ 0 := by positivity
    have e : (harm 1 u + (((u : ℚ) + 1) ^ 1)⁻¹) ^ 2 =
        (harm 1 u) ^ 2 + 2 * (harm 1 u * (((u : ℚ) + 1) ^ 1)⁻¹) + (((u : ℚ) + 1) ^ 2)⁻¹ := by
      field_simp
      ring
    rw [e, ih]; ring

/-- `F(x) = x q(x)` for the Faulhaber polynomial `F = faul g`, `q = F/x`. -/
theorem faul_eval_eq (g : ℚ[X]) (x : ℚ) : (faul g).eval x = x * (faul g).divX.eval x := by
  rw [eval_peel (faul g) x, faul_coeff_zero, zero_add]

/-- Shared set-up for L2 and L3: `c_i q(i+1) = q₀ c_i + r(i+1)`. -/
theorem q_succ_eq (q : ℚ[X]) (i : ℕ) :
    (((i : ℚ) + 1) ^ 1)⁻¹ * q.eval ((i : ℚ) + 1) =
      q.coeff 0 * (((i : ℚ) + 1) ^ 1)⁻¹ + q.divX.eval ((i : ℚ) + 1) := by
  have : ((i : ℚ) + 1) ≠ 0 := by positivity
  rw [eval_peel q ((i : ℚ) + 1)]
  field_simp

variable (hp5 : 5 ≤ p)
include hp5

/-- **L0.**  `∑_{u<p} g(u) = p I(g) + (p²/2) λ(g) + p³ t`, `t ∈ ℤ_(p)`. -/
theorem sum_poly_eq {g : ℚ[X]} (hg : Adm p g) :
    ∃ t : ℚ, t ∈ LocRing p ∧
      ∑ u ∈ range p, g.eval (u : ℚ) = p * bI g + p ^ 2 * (bL g / 2) + p ^ 3 * t := by
  set f := faul g with hf
  have hf0 : f.coeff 0 = 0 := faul_coeff_zero g
  have h1 : f.divX.coeff 0 = bI g := by rw [coeff_divX]; exact faul_coeff_one g
  have h2 : f.divX.divX.coeff 0 = bL g / 2 := by
    rw [coeff_divX, coeff_divX]; exact faul_coeff_two g
  refine ⟨f.divX.divX.divX.eval (p : ℚ), ?_, ?_⟩
  · have : PInt p f.divX.divX.divX := fun i => by
      rw [coeff_divX, coeff_divX, coeff_divX]; exact hg.faul_coeff_mem hp5 _
    exact this.eval_nat p
  · rw [← faul_eval, ← hf, eval_peel f, hf0, eval_peel f.divX, h1, eval_peel f.divX.divX, h2]
    ring

theorem sum_poly_pdv {g : ℚ[X]} (hg : Adm p g) :
    PDv p 1 (∑ u ∈ range p, g.eval (u : ℚ)) := by
  obtain ⟨t, ht, e⟩ := sum_poly_eq hp5 hg
  have hI := hg.bI_mem hp5
  have hL := hg.bL_mem hp5
  have h2 : (2 : ℚ)⁻¹ ∈ LocRing p := two_inv_mem (by omega)
  refine ⟨bI g + p * (bL g / 2) + p ^ 2 * t, ?_, by rw [e]; ring⟩
  exact (LocRing p).add_mem ((LocRing p).add_mem hI
    ((LocRing p).mul_mem p_mem (by rw [div_eq_mul_inv]; exact (LocRing p).mul_mem hL h2)))
    ((LocRing p).mul_mem ((LocRing p).pow_mem p_mem 2) ht)

theorem sum_poly_pdv2 {g : ℚ[X]} (hg : Adm p g) :
    PDv p 2 (∑ u ∈ range p, g.eval (u : ℚ) - p * bI g) := by
  obtain ⟨t, ht, e⟩ := sum_poly_eq hp5 hg
  have hL := hg.bL_mem hp5
  have h2 : (2 : ℚ)⁻¹ ∈ LocRing p := two_inv_mem (by omega)
  have : ∑ u ∈ range p, g.eval (u : ℚ) - p * bI g = (p : ℚ) ^ 2 * (bL g / 2 + p * t) := by
    rw [e]; ring
  rw [this]
  refine ⟨bL g / 2 + p * t, ?_, rfl⟩
  exact (LocRing p).add_mem (by rw [div_eq_mul_inv]; exact (LocRing p).mul_mem hL h2)
    ((LocRing p).mul_mem p_mem ht)

theorem faul_pdv {g : ℚ[X]} (hg : Adm p g) : PDv p 1 ((faul g).eval (p : ℚ)) := by
  have hq := hg.faul_divX hp5
  refine ⟨(faul g).divX.eval (p : ℚ), hq.1.eval_nat p, ?_⟩
  rw [faul_eval_eq]; ring

/-- **L1.** `∑_{u<p} g(u) H_u ≡ I(g) - p μ(g) (mod p²)`. -/
theorem sum_harm_one {g : ℚ[X]} (hg : Adm p g) :
    PDv p 2 (∑ u ∈ range p, g.eval (u : ℚ) * harm 1 u - (bI g - p * bMu g)) := by
  have hq := hg.faul_divX hp5
  set f := faul g with hf
  set q := f.divX with hqdef
  have hp1 : p - 1 + 1 = p := by have := hp.out.pos; omega
  have hab := abel_sum (fun u => g.eval (u : ℚ)) (fun i => (((i : ℚ) + 1) ^ 1)⁻¹) (p - 1)
  rw [hp1] at hab
  have hH : ∀ u, harm 1 u = ∑ i ∈ range u, (((i : ℚ) + 1) ^ 1)⁻¹ := fun u => rfl
  simp only [← hH] at hab
  have hFu : ∀ n : ℕ, ∑ u ∈ range n, g.eval (u : ℚ) = f.eval (n : ℚ) := fun n => (faul_eval g n).symm
  simp only [hFu] at hab
  -- c_i F(i+1) = q(i+1)
  have hterm : ∀ i ∈ range (p - 1), (((i : ℚ) + 1) ^ 1)⁻¹ * (f.eval ((p : ℕ) : ℚ) - f.eval (((i + 1 : ℕ)) : ℚ))
      = (((i : ℚ) + 1) ^ 1)⁻¹ * f.eval ((p : ℕ) : ℚ) - q.eval ((i : ℚ) + 1) := by
    intro i _
    have : ((i : ℚ) + 1) ≠ 0 := by positivity
    rw [show (((i + 1 : ℕ)) : ℚ) = (i : ℚ) + 1 by push_cast; ring, hf, faul_eval_eq g ((i : ℚ) + 1)]
    field_simp
    rfl
  rw [sum_congr rfl hterm, sum_sub_distrib, ← sum_mul, ← hH] at hab
  -- ∑_{i<p-1} q(i+1) = ∑_{i<p} q(i) - q(0)
  have hshift : ∑ i ∈ range (p - 1), q.eval ((i : ℚ) + 1) = ∑ i ∈ range p, q.eval (i : ℚ) - q.eval 0 := by
    have := sum_range_succ' (fun i : ℕ => q.eval (i : ℚ)) (p - 1)
    rw [hp1] at this
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at this
    rw [this]; ring
  have hq0 : q.eval 0 = bI g := by
    rw [← coeff_zero_eq_eval_zero, hqdef, coeff_divX]; exact faul_coeff_one g
  rw [hshift, hq0] at hab
  rw [hab]
  have e1 : f.eval ((p : ℕ) : ℚ) * harm 1 (p - 1) = (f.eval ((p : ℕ) : ℚ)) * harm 1 (p - 1) := rfl
  have hA : PDv p 2 (f.eval ((p : ℕ) : ℚ) * harm 1 (p - 1)) := by
    have := PDv.mono (j := 2) (by norm_num) (PDv.mul (faul_pdv hp5 hg) (wolstenholme_one hp5))
    exact this
  have hB := sum_poly_pdv2 hp5 hq
  have hcalc : harm 1 (p - 1) * f.eval ((p : ℕ) : ℚ) -
        (∑ i ∈ range p, q.eval (i : ℚ) - bI g) - (bI g - p * bMu g) =
      f.eval ((p : ℕ) : ℚ) * harm 1 (p - 1) - (∑ i ∈ range p, q.eval (i : ℚ) - p * bI q) := by
    unfold bMu; rw [← hqdef]; ring
  rw [hcalc]
  exact hA.sub hB

/-- **L2.** `∑_{u<p} g(u) H^{(2)}_u ≡ λ(g)/2 (mod p)`. -/
theorem sum_harm_two {g : ℚ[X]} (hg : Adm p g) :
    PDv p 1 (∑ u ∈ range p, g.eval (u : ℚ) * harm 2 u - bL g / 2) := by
  have hq := hg.faul_divX hp5
  have hr := hq.divX
  set f := faul g with hf
  set q := f.divX with hqdef
  set r := q.divX with hrdef
  have hp1 : p - 1 + 1 = p := by have := hp.out.pos; omega
  have hab := abel_sum (fun u => g.eval (u : ℚ)) (fun i => (((i : ℚ) + 1) ^ 2)⁻¹) (p - 1)
  rw [hp1] at hab
  have hH : ∀ u, harm 2 u = ∑ i ∈ range u, (((i : ℚ) + 1) ^ 2)⁻¹ := fun u => rfl
  simp only [← hH] at hab
  have hFu : ∀ n : ℕ, ∑ u ∈ range n, g.eval (u : ℚ) = f.eval (n : ℚ) := fun n => (faul_eval g n).symm
  simp only [hFu] at hab
  have hterm : ∀ i ∈ range (p - 1), (((i : ℚ) + 1) ^ 2)⁻¹ * (f.eval ((p : ℕ) : ℚ) - f.eval (((i + 1 : ℕ)) : ℚ))
      = (((i : ℚ) + 1) ^ 2)⁻¹ * f.eval ((p : ℕ) : ℚ) -
        (q.coeff 0 * (((i : ℚ) + 1) ^ 1)⁻¹ + r.eval ((i : ℚ) + 1)) := by
    intro i _
    have h0 : ((i : ℚ) + 1) ≠ 0 := by positivity
    rw [show (((i + 1 : ℕ)) : ℚ) = (i : ℚ) + 1 by push_cast; ring, hf, faul_eval_eq g ((i : ℚ) + 1)]
    have := q_succ_eq q i
    have e2 : (((i : ℚ) + 1) ^ 2)⁻¹ * (((i : ℚ) + 1) * q.eval ((i : ℚ) + 1)) =
        (((i : ℚ) + 1) ^ 1)⁻¹ * q.eval ((i : ℚ) + 1) := by field_simp
    rw [mul_sub, e2, this]
  rw [sum_congr rfl hterm, sum_sub_distrib, ← sum_mul, ← hH, sum_add_distrib, ← mul_sum] at hab
  have hshift : ∑ i ∈ range (p - 1), r.eval ((i : ℚ) + 1) = ∑ i ∈ range p, r.eval (i : ℚ) - r.eval 0 := by
    have := sum_range_succ' (fun i : ℕ => r.eval (i : ℚ)) (p - 1)
    rw [hp1] at this
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at this
    rw [this]; ring
  have hr0 : r.eval 0 = bL g / 2 := by
    rw [← coeff_zero_eq_eval_zero, hrdef, coeff_divX, hqdef, coeff_divX]; exact faul_coeff_two g
  have hH1 : ∑ i ∈ range (p - 1), (((i : ℚ) + 1) ^ 1)⁻¹ = harm 1 (p - 1) := rfl
  rw [hshift, hr0, hH1] at hab
  rw [hab]
  have hA : PDv p 1 (harm 2 (p - 1) * f.eval ((p : ℕ) : ℚ)) := by
    have := PDv.mono (j := 1) (by norm_num) (PDv.mul (wolstenholme_two hp5) (faul_pdv hp5 hg))
    simpa [mul_comm] using this
  have hq0 : q.coeff 0 ∈ LocRing p := hq.1 0
  have hB : PDv p 1 (q.coeff 0 * harm 1 (p - 1)) :=
    PDv.mono (by norm_num) (PDv.mul_left hq0 (wolstenholme_one hp5))
  have hC := sum_poly_pdv hp5 hr
  have hcalc : harm 2 (p - 1) * f.eval ((p : ℕ) : ℚ) -
        (q.coeff 0 * harm 1 (p - 1) + (∑ i ∈ range p, r.eval (i : ℚ) - bL g / 2)) - bL g / 2 =
      harm 2 (p - 1) * f.eval ((p : ℕ) : ℚ) - q.coeff 0 * harm 1 (p - 1) -
        ∑ i ∈ range p, r.eval (i : ℚ) := by ring
  rw [hcalc]
  exact (hA.sub hB).sub hC

/-- **L3.** `∑_{u<p} g(u) H_u² ≡ -2 μ(g) - λ(g)/2 (mod p)`. -/
theorem sum_harm_sq {g : ℚ[X]} (hg : Adm p g) :
    PDv p 1 (∑ u ∈ range p, g.eval (u : ℚ) * (harm 1 u) ^ 2 - (-2 * bMu g - bL g / 2)) := by
  have hq := hg.faul_divX hp5
  have hr := hq.divX
  have hq2 := hq.faul_divX hp5
  set f := faul g with hf
  set q := f.divX with hqdef
  set r := q.divX with hrdef
  have hp1 : p - 1 + 1 = p := by have := hp.out.pos; omega
  -- split H² = H2 + 2 ∑ dd
  have hsplit : ∑ u ∈ range p, g.eval (u : ℚ) * (harm 1 u) ^ 2 =
      ∑ u ∈ range p, g.eval (u : ℚ) * harm 2 u +
        2 * ∑ u ∈ range p, g.eval (u : ℚ) * ∑ i ∈ range u, harm 1 i * (((i : ℚ) + 1) ^ 1)⁻¹ := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    rw [harm_sq u]; ring
  have hab := abel_sum (fun u => g.eval (u : ℚ)) (fun i => harm 1 i * (((i : ℚ) + 1) ^ 1)⁻¹) (p - 1)
  rw [hp1] at hab
  have hFu : ∀ n : ℕ, ∑ u ∈ range n, g.eval (u : ℚ) = f.eval (n : ℚ) := fun n => (faul_eval g n).symm
  simp only [hFu] at hab
  have hterm : ∀ i ∈ range (p - 1), harm 1 i * (((i : ℚ) + 1) ^ 1)⁻¹ *
        (f.eval ((p : ℕ) : ℚ) - f.eval (((i + 1 : ℕ)) : ℚ))
      = harm 1 i * (((i : ℚ) + 1) ^ 1)⁻¹ * f.eval ((p : ℕ) : ℚ) -
        (harm 1 (i + 1) * q.eval ((i : ℚ) + 1) -
          (q.coeff 0 * (((i : ℚ) + 1) ^ 1)⁻¹ + r.eval ((i : ℚ) + 1))) := by
    intro i _
    have h0 : ((i : ℚ) + 1) ≠ 0 := by positivity
    rw [show (((i + 1 : ℕ)) : ℚ) = (i : ℚ) + 1 by push_cast; ring, hf, faul_eval_eq g ((i : ℚ) + 1),
      harm_succ]
    have := q_succ_eq q i
    have e3 : harm 1 i * (((i : ℚ) + 1) ^ 1)⁻¹ * (((i : ℚ) + 1) * q.eval ((i : ℚ) + 1)) =
        harm 1 i * q.eval ((i : ℚ) + 1) := by field_simp
    rw [mul_sub, e3]
    have e4 : (harm 1 i + (((i : ℚ) + 1) ^ 1)⁻¹) * q.eval ((i : ℚ) + 1) =
        harm 1 i * q.eval ((i : ℚ) + 1) + (((i : ℚ) + 1) ^ 1)⁻¹ * q.eval ((i : ℚ) + 1) := by ring
    rw [e4, this]
    ring
  rw [sum_congr rfl hterm, sum_sub_distrib, ← sum_mul, sum_sub_distrib, sum_add_distrib] at hab
  -- the three shifted sums
  have hshift1 : ∑ i ∈ range (p - 1), harm 1 (i + 1) * q.eval ((i : ℚ) + 1) =
      ∑ i ∈ range p, q.eval (i : ℚ) * harm 1 i := by
    have := sum_range_succ' (fun i : ℕ => q.eval (i : ℚ) * harm 1 i) (p - 1)
    rw [hp1] at this
    simp only [Nat.cast_add, Nat.cast_one, harm_zero, mul_zero, add_zero] at this
    rw [this]
    exact sum_congr rfl fun i _ => by ring
  have hshift2 : ∑ i ∈ range (p - 1), r.eval ((i : ℚ) + 1) = ∑ i ∈ range p, r.eval (i : ℚ) - r.eval 0 := by
    have := sum_range_succ' (fun i : ℕ => r.eval (i : ℚ)) (p - 1)
    rw [hp1] at this
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at this
    rw [this]; ring
  have hr0 : r.eval 0 = bL g / 2 := by
    rw [← coeff_zero_eq_eval_zero, hrdef, coeff_divX, hqdef, coeff_divX]; exact faul_coeff_two g
  have hH1 : ∑ i ∈ range (p - 1), (((i : ℚ) + 1) ^ 1)⁻¹ = harm 1 (p - 1) := rfl
  rw [← mul_sum, hH1, hshift1, hshift2, hr0] at hab
  -- the main identity
  have hL2 := sum_harm_two hp5 hg
  have hL1q := sum_harm_one hp5 hq
  have hMu : bMu q ∈ LocRing p := hq2.bI_mem hp5
  have hq0 : q.coeff 0 ∈ LocRing p := hq.1 0
  have hdd : ∑ i ∈ range (p - 1), harm 1 i * (((i : ℚ) + 1) ^ 1)⁻¹ ∈ LocRing p := by
    refine (LocRing p).sum_mem fun i hi => (LocRing p).mul_mem
      (harm_mem (by have := mem_range.1 hi; omega)) ?_
    have := inv_succ_mem_of_lt (p := p) (i := i) (by have := mem_range.1 hi; omega)
    simpa using this
  have hA : PDv p 1 ((∑ i ∈ range (p - 1), harm 1 i * (((i : ℚ) + 1) ^ 1)⁻¹) * f.eval ((p : ℕ) : ℚ)) :=
    PDv.mul_left hdd (faul_pdv hp5 hg)
  have hB : PDv p 1 (∑ i ∈ range p, q.eval (i : ℚ) * harm 1 i - bI q) := by
    have h2 : PDv p 1 (p * bMu q) := ⟨bMu q, hMu, by ring⟩
    have h1 := PDv.mono (j := 1) (by norm_num) hL1q
    have := h1.sub h2
    convert this using 1
    ring
  have hC : PDv p 1 (q.coeff 0 * harm 1 (p - 1)) :=
    PDv.mono (by norm_num) (PDv.mul_left hq0 (wolstenholme_one hp5))
  have hD := sum_poly_pdv hp5 hr
  rw [hsplit, hab]
  have hcalc : ∑ u ∈ range p, g.eval (u : ℚ) * harm 2 u + 2 * ((∑ i ∈ range (p - 1), harm 1 i * (((i : ℚ) + 1) ^ 1)⁻¹) * f.eval ((p : ℕ) : ℚ) -
        (∑ i ∈ range p, q.eval (i : ℚ) * harm 1 i -
          (q.coeff 0 * harm 1 (p - 1) + (∑ i ∈ range p, r.eval (i : ℚ) - bL g / 2)))) -
        (-2 * bMu g - bL g / 2) =
      (∑ u ∈ range p, g.eval (u : ℚ) * harm 2 u - bL g / 2) +
        2 * ((∑ i ∈ range (p - 1), harm 1 i * (((i : ℚ) + 1) ^ 1)⁻¹) * f.eval ((p : ℕ) : ℚ)) -
        2 * (∑ i ∈ range p, q.eval (i : ℚ) * harm 1 i - bI q) +
        2 * (q.coeff 0 * harm 1 (p - 1)) + 2 * ∑ i ∈ range p, r.eval (i : ℚ) := by
    have hmu : bMu g = bI q := rfl
    rw [hmu]; ring
  rw [hcalc]
  have two : ∀ {x : ℚ}, PDv p 1 x → PDv p 1 (2 * x) := fun hx =>
    PDv.mul_left (by simpa using natCast_mem (p := p) 2) hx
  exact (((hL2.add (two hA)).sub (two hB)).add (two hC)).add (two hD)

end Sums

/-! ### Toolkit: membership automation, `p`-adic jets `E(α, β) = 1 + pα + p²(β + α²/2)` mod `p³` -/

section Jets

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

theorem ofNat_mem (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : ℚ) ∈ LocRing p := by
  have := natCast_mem (p := p) n
  simpa using this

theorem one_mem' : (1 : ℚ) ∈ LocRing p := (LocRing p).one_mem
theorem zero_mem' : (0 : ℚ) ∈ LocRing p := (LocRing p).zero_mem

/-- Closure of `ℤ_(p)` under the ring operations, as a `simp`-free tactic. -/
macro "rmem" : tactic =>
  `(tactic| repeat' first
    | assumption
    | apply Subring.add_mem
    | apply Subring.mul_mem
    | apply Subring.sub_mem
    | apply Subring.neg_mem
    | apply Subring.pow_mem
    | apply Subring.sum_mem
    | apply Subring.prod_mem
    | apply natCast_mem
    | apply ofNat_mem
    | apply one_mem'
    | apply zero_mem')

/-- Jet of order 2: `x ≡ 1 + pα + p²(β + α²/2) (mod p³)`. -/
def EJ (p : ℕ) [Fact p.Prime] (x α β : ℚ) : Prop :=
  x ∈ LocRing p ∧ α ∈ LocRing p ∧ β ∈ LocRing p ∧ PDv p 3 (x - (1 + p * α + p ^ 2 * (β + α ^ 2 / 2)))

theorem inv_intCast_mem (z : ℤ) (h : ¬ (p : ℤ) ∣ z) : ((z : ℚ))⁻¹ ∈ LocRing p := by
  have hz : z ≠ 0 := fun h0 => h (by simp [h0])
  rw [mem_locRing, Rat.inv_intCast_den]
  simp only [hz, if_false]
  intro hd
  exact h (Int.natCast_dvd.2 hd)

theorem inv_one_add_mem {w : ℚ} (hw : w ∈ LocRing p) : (1 + p * w)⁻¹ ∈ LocRing p := by
  have h1 : CatalanCore.Good p w (CatalanCore.red p w) := CatalanCore.good_red hw
  have h2 : CatalanCore.Good p (1 + (p : ℚ) * w) (1 + 0) :=
    (CatalanCore.Good.one (ℓ := p)).add (CatalanCore.Good.ell_mul h1)
  have h3 := CatalanCore.Good.inv h2 (by simp)
  exact h3.1

theorem one_add_ne_zero {w : ℚ} (hw : w ∈ LocRing p) : (1 + (p : ℚ) * w) ≠ 0 := by
  intro h0
  have h1 : CatalanCore.Good p w (CatalanCore.red p w) := CatalanCore.good_red hw
  have h2 : CatalanCore.Good p (1 + (p : ℚ) * w) (1 + 0) :=
    (CatalanCore.Good.one (ℓ := p)).add (CatalanCore.Good.ell_mul h1)
  have := h2.2
  rw [h0] at this
  simp [CatalanCore.red] at this

variable (hp5 : 5 ≤ p)
include hp5

theorem EJ.mul {x y α β α' β' : ℚ} (hx : EJ p x α β) (hy : EJ p y α' β') :
    EJ p (x * y) (α + α') (β + β') := by
  obtain ⟨hxm, ham, hbm, hxe⟩ := hx
  obtain ⟨hym, ham', hbm', hye⟩ := hy
  have h2 : (2 : ℚ)⁻¹ ∈ LocRing p := two_inv_mem (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rmem
  · rmem
  · rmem
  · have hX : (1 + p * α + p ^ 2 * (β + α ^ 2 / 2)) ∈ LocRing p := by
      have : (1 + p * α + p ^ 2 * (β + α ^ 2 / 2)) = 1 + p * α + p ^ 2 * (β + α ^ 2 * 2⁻¹) := by ring
      rw [this]; rmem
    have e : x * y - (1 + p * (α + α') + p ^ 2 * ((β + β') + (α + α') ^ 2 / 2)) =
        (x - (1 + p * α + p ^ 2 * (β + α ^ 2 / 2))) * y +
          (1 + p * α + p ^ 2 * (β + α ^ 2 / 2)) * (y - (1 + p * α' + p ^ 2 * (β' + α' ^ 2 / 2))) +
          p ^ 3 * (α * (β' + α' ^ 2 / 2) + α' * (β + α ^ 2 / 2) +
            p * ((β + α ^ 2 / 2) * (β' + α' ^ 2 / 2))) := by ring
    rw [e]
    refine (PDv.add (PDv.mul_right hxe hym) (PDv.mul_left hX hye)).add ?_
    refine ⟨α * (β' + α' ^ 2 / 2) + α' * (β + α ^ 2 / 2) + p * ((β + α ^ 2 / 2) * (β' + α' ^ 2 / 2)), ?_, rfl⟩
    have h2' : α' ^ 2 / 2 = α' ^ 2 * 2⁻¹ := by ring
    have h2'' : α ^ 2 / 2 = α ^ 2 * 2⁻¹ := by ring
    rw [h2', h2'']; rmem

omit hp5 in
theorem EJ.one : EJ p 1 0 0 := by
  refine ⟨one_mem', zero_mem', zero_mem', ?_⟩
  simpa using PDv.zero 3

theorem EJ.pow {x α β : ℚ} (hx : EJ p x α β) (N : ℕ) : EJ p (x ^ N) (N * α) (N * β) := by
  induction N with
  | zero => simpa using EJ.one (p := p)
  | succ N ih =>
    have := EJ.mul hp5 ih hx
    rw [pow_succ]
    convert this using 2 <;> push_cast <;> ring

theorem EJ.ne_zero {x α β : ℚ} (hx : EJ p x α β) : x ≠ 0 := by
  obtain ⟨hxm, ham, hbm, hxe⟩ := hx
  have h2 : (2 : ℚ)⁻¹ ∈ LocRing p := two_inv_mem (by omega)
  obtain ⟨z, hz, hzx⟩ := hxe
  have hw : (α + p * (β + α ^ 2 / 2) + p ^ 2 * z) ∈ LocRing p := by
    have : (α + p * (β + α ^ 2 / 2) + p ^ 2 * z) = α + p * (β + α ^ 2 * 2⁻¹) + p ^ 2 * z := by ring
    rw [this]; rmem
  have hxw : x = 1 + p * (α + p * (β + α ^ 2 / 2) + p ^ 2 * z) := by linear_combination hzx
  rw [hxw]; exact one_add_ne_zero hw

theorem EJ.inv {x α β : ℚ} (hx : EJ p x α β) : EJ p x⁻¹ (-α) (-β) := by
  obtain ⟨hxm, ham, hbm, hxe⟩ := hx
  have h2 : (2 : ℚ)⁻¹ ∈ LocRing p := two_inv_mem (by omega)
  obtain ⟨z, hz, hzx⟩ := hxe
  -- x = 1 + p w
  have hw : (α + p * (β + α ^ 2 / 2) + p ^ 2 * z) ∈ LocRing p := by
    have : (α + p * (β + α ^ 2 / 2) + p ^ 2 * z) = α + p * (β + α ^ 2 * 2⁻¹) + p ^ 2 * z := by ring
    rw [this]; rmem
  have hxw : x = 1 + p * (α + p * (β + α ^ 2 / 2) + p ^ 2 * z) := by linear_combination hzx
  have hinv : x⁻¹ ∈ LocRing p := by rw [hxw]; exact inv_one_add_mem hw
  have hne : x ≠ 0 := by rw [hxw]; exact one_add_ne_zero hw
  have hxy : x * x⁻¹ = 1 := mul_inv_cancel₀ hne
  refine ⟨hinv, by rmem, by rmem, ?_⟩
  have hX : (1 + p * α + p ^ 2 * (β + α ^ 2 / 2)) ∈ LocRing p := by
    have : (1 + p * α + p ^ 2 * (β + α ^ 2 / 2)) = 1 + p * α + p ^ 2 * (β + α ^ 2 * 2⁻¹) := by ring
    rw [this]; rmem
  have hZ : (1 + p * (-α) + p ^ 2 * ((-β) + (-α) ^ 2 / 2)) ∈ LocRing p := by
    have : (1 + p * (-α) + p ^ 2 * ((-β) + (-α) ^ 2 / 2)) =
        1 + p * (-α) + p ^ 2 * ((-β) + (-α) ^ 2 * 2⁻¹) := by ring
    rw [this]; rmem
  -- x⁻¹ - Z = x⁻¹ (1 - x Z)
  have e : x⁻¹ - (1 + p * (-α) + p ^ 2 * ((-β) + (-α) ^ 2 / 2)) =
      x⁻¹ * (-(p ^ 3 * (-2 * α * β + p * ((β + α ^ 2 / 2) * (-β + α ^ 2 / 2)))) -
        (x - (1 + p * α + p ^ 2 * (β + α ^ 2 / 2))) *
          (1 + p * (-α) + p ^ 2 * ((-β) + (-α) ^ 2 / 2))) := by
    field_simp
    ring
  rw [e]
  refine PDv.mul_left hinv (PDv.sub ?_ (PDv.mul_right ⟨z, hz, hzx⟩ hZ))
  refine ⟨-(-2 * α * β + p * ((β + α ^ 2 / 2) * (-β + α ^ 2 / 2))), ?_, by ring⟩
  have h2'' : α ^ 2 / 2 = α ^ 2 * 2⁻¹ := by ring
  rw [h2'']; rmem

theorem EJ.congr {x α β α' β' : ℚ} (hx : EJ p x α β) (ha' : α' ∈ LocRing p) (hb' : β' ∈ LocRing p)
    (h1 : PDv p 2 (α - α')) (h2 : PDv p 1 (β - β')) : EJ p x α' β' := by
  obtain ⟨hxm, ham, hbm, hxe⟩ := hx
  have h2i : (2 : ℚ)⁻¹ ∈ LocRing p := two_inv_mem (by omega)
  refine ⟨hxm, ha', hb', ?_⟩
  have e : x - (1 + p * α' + p ^ 2 * (β' + α' ^ 2 / 2)) =
      (x - (1 + p * α + p ^ 2 * (β + α ^ 2 / 2))) + p * (α - α') + p ^ 2 * (β - β') +
        p ^ 2 * ((α - α') * ((α + α') / 2)) := by ring
  rw [e]
  refine (((hxe.add ?_).add ?_).add ?_)
  · have := PDv.mul (j := 1) (k := 2) pPDv_one h1
    simpa using this
  · have := PDv.mul (j := 2) (k := 1) (⟨1, one_mem', by simp⟩ : PDv p 2 ((p : ℚ) ^ 2)) h2
    simpa using this
  · have h3 : ((α + α') / 2) ∈ LocRing p := by
      have : (α + α') / 2 = (α + α') * 2⁻¹ := by ring
      rw [this]; rmem
    have := PDv.mul (j := 2) (k := 2) (⟨1, one_mem', by simp⟩ : PDv p 2 ((p : ℚ) ^ 2))
      (PDv.mul_right h1 h3)
    exact PDv.mono (j := 3) (k := 2 + 2) (by norm_num) (by simpa [mul_assoc] using this)

/-- A factor `1 + p z` is the jet `(z, -z²/2)`. -/
theorem EJ.one_add {z : ℚ} (hz : z ∈ LocRing p) : EJ p (1 + p * z) z (-(z ^ 2 / 2)) := by
  have h2 : (2 : ℚ)⁻¹ ∈ LocRing p := two_inv_mem (by omega)
  refine ⟨by rmem, hz, ?_, ?_⟩
  · have : -(z ^ 2 / 2) = -(z ^ 2 * 2⁻¹) := by ring
    rw [this]; rmem
  · have : 1 + (p : ℚ) * z - (1 + p * z + p ^ 2 * (-(z ^ 2 / 2) + z ^ 2 / 2)) = 0 := by ring
    rw [this]; exact PDv.zero 3

omit hp5 in
theorem EJ.of_pdv {x : ℚ} (hx : x ∈ LocRing p) (hz : PDv p 3 (x - 1)) : EJ p x 0 0 := by
  refine ⟨hx, zero_mem', zero_mem', ?_⟩
  simpa using hz

/-- The factor product `P_j(x) = ∏_{y=1}^{x} (1 + j p / y)`. -/
def Pj (p : ℕ) (j : ℤ) (x : ℕ) : ℚ := ∏ y ∈ range x, (1 + (j : ℚ) * p * (((y : ℚ) + 1))⁻¹)

theorem EJ_Pj (j : ℤ) : ∀ x : ℕ, x < p → EJ p (Pj p j x) (j * harm 1 x) (-((j : ℚ) ^ 2 / 2) * harm 2 x) := by
  intro x
  induction x with
  | zero =>
    intro _
    simpa [Pj, harm_zero] using EJ.one (p := p)
  | succ x ih =>
    intro hx
    have hz : ((j : ℚ) * (((x : ℚ) + 1))⁻¹) ∈ LocRing p :=
      (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) j) (inv_succ_mem_of_lt hx)
    have h1 := EJ.one_add hp5 hz
    have h2 := EJ.mul hp5 (ih (by omega)) h1
    have e : Pj p j (x + 1) = Pj p j x * (1 + (p : ℚ) * ((j : ℚ) * (((x : ℚ) + 1))⁻¹)) := by
      unfold Pj; rw [prod_range_succ]; congr 1; ring
    rw [e]
    have hx0 : ((x : ℚ) + 1) ≠ 0 := by positivity
    convert h2 using 1
    · rw [harm_succ]; ring
    · rw [harm_succ]; field_simp; ring

theorem EJ_pj_ne (j : ℤ) (x : ℕ) (hx : x < p) : Pj p j x ≠ 0 :=
  (EJ_Pj hp5 j x hx).ne_zero hp5

omit hp5 in
/-- `1/(i + c p) = 1/i - c p / i² + p² w`, `w ∈ ℤ_(p)`, for `0 < i < p`. -/
theorem inv_expand (c : ℤ) {i : ℕ} (h0 : 0 < i) (hi : i < p) :
    ∃ w : ℚ, w ∈ LocRing p ∧
      ((i : ℚ) + c * p)⁻¹ = (i : ℚ)⁻¹ - c * p * ((i : ℚ)⁻¹) ^ 2 + (p : ℚ) ^ 2 * w := by
  have hi0 : (i : ℚ) ≠ 0 := by exact_mod_cast h0.ne'
  have hnd : ¬ (p : ℤ) ∣ ((i : ℤ) + c * p) := by
    intro hd
    have h1 : (p : ℤ) ∣ (i : ℤ) := by
      have := dvd_sub hd (dvd_mul_left (p : ℤ) c)
      simpa using this
    have := Int.natCast_dvd_natCast.1 h1
    exact absurd (Nat.le_of_dvd h0 this) (by omega)
  have hinv := inv_intCast_mem ((i : ℤ) + c * p) hnd
  have hne : ((i : ℚ) + c * p) ≠ 0 := by
    intro h0'
    apply hnd
    have : (((i : ℤ) + c * p : ℤ) : ℚ) = 0 := by push_cast; exact h0'
    have h00 : ((i : ℤ) + c * p) = 0 := by exact_mod_cast this
    rw [h00]; exact dvd_zero _
  refine ⟨(c : ℚ) ^ 2 * ((i : ℚ)⁻¹) ^ 2 * ((i : ℚ) + c * p)⁻¹, ?_, ?_⟩
  · have hc : ((c : ℤ) : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) c
    have hiv : (i : ℚ)⁻¹ ∈ LocRing p := inv_mem_of_lt h0 hi
    have hinv' : ((i : ℚ) + c * p)⁻¹ ∈ LocRing p := by
      have : (((i : ℤ) + c * p : ℤ) : ℚ) = (i : ℚ) + c * p := by push_cast; ring
      rw [← this]; exact hinv
    rmem
  · field_simp
    ring

omit hp5 in
theorem PInt.add {g h : ℚ[X]} (hg : PInt p g) (hh : PInt p h) : PInt p (g + h) := fun i => by
  rw [coeff_add]; exact (LocRing p).add_mem (hg i) (hh i)

omit hp5 in
theorem PInt.sub {g h : ℚ[X]} (hg : PInt p g) (hh : PInt p h) : PInt p (g - h) := fun i => by
  rw [coeff_sub]; exact (LocRing p).sub_mem (hg i) (hh i)

omit hp5 in
theorem PInt.mul {g h : ℚ[X]} (hg : PInt p g) (hh : PInt p h) : PInt p (g * h) := fun i => by
  rw [coeff_mul]
  exact (LocRing p).sum_mem fun x _ => (LocRing p).mul_mem (hg _) (hh _)

omit hp5 in
theorem PInt.one : PInt p (1 : ℚ[X]) := fun i => by
  rw [coeff_one]; split_ifs
  · exact (LocRing p).one_mem
  · exact (LocRing p).zero_mem

omit hp5 in
theorem PInt.pow {g : ℚ[X]} (hg : PInt p g) (n : ℕ) : PInt p (g ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact PInt.one
  | succ n ih => rw [pow_succ]; exact ih.mul hg

omit hp5 in
theorem PInt.ofC {c : ℚ} (hc : c ∈ LocRing p) : PInt p (C c) := fun i => by
  rw [coeff_C]; split_ifs
  · exact hc
  · exact (LocRing p).zero_mem

omit hp5 in
theorem PInt.ofX : PInt p (X : ℚ[X]) := fun i => by
  rw [coeff_X]; split_ifs
  · exact (LocRing p).one_mem
  · exact (LocRing p).zero_mem

omit hp5 in
theorem PInt.X_add_C {c : ℚ} (hc : c ∈ LocRing p) : PInt p (X + C c : ℚ[X]) :=
  PInt.ofX.add (PInt.ofC hc)

omit hp5 in
theorem PInt.X_sub_C {c : ℚ} (hc : c ∈ LocRing p) : PInt p (X - C c : ℚ[X]) :=
  PInt.ofX.sub (PInt.ofC hc)

omit hp5 in
theorem PInt.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (h : ∀ i ∈ s, PInt p (f i)) :
    PInt p (∑ i ∈ s, f i) := fun n => by
  rw [finsetSum_coeff]; exact (LocRing p).sum_mem fun i hi => h i hi n

omit hp5 in
theorem PInt.prod {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) (h : ∀ i ∈ s, PInt p (f i)) :
    PInt p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (PInt.one (p := p))
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact (h a (mem_insert_self _ _)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

omit hp5 in
theorem PInt.derivative {g : ℚ[X]} (hg : PInt p g) : PInt p (derivative g) := fun i => by
  rw [coeff_derivative]; exact (LocRing p).mul_mem (hg _) (by rmem)

omit hp5 in
theorem PInt.smul_nat {g : ℚ[X]} (hg : PInt p g) (n : ℕ) : PInt p ((n : ℚ[X]) * g) := fun i => by
  rw [← C_eq_natCast, coeff_C_mul]; exact (LocRing p).mul_mem (by rmem) (hg i)

omit hp5 in
theorem PInt.hasseDeriv {g : ℚ[X]} (hg : PInt p g) (k : ℕ) : PInt p (hasseDeriv k g) := fun i => by
  rw [hasseDeriv_coeff]; exact (LocRing p).mul_mem (by rmem) (hg _)

omit hp5 in
theorem coeff_comp_neg_X (g : ℚ[X]) (n : ℕ) : (g.comp (-X)).coeff n = (-1) ^ n * g.coeff n := by
  induction g using Polynomial.induction_on' with
  | add g h hg hh => simp [add_comp, hg, hh, mul_add]
  | monomial e c =>
    have h1 : (-X : ℚ[X]) ^ e = C ((-1 : ℚ) ^ e) * X ^ e := by
      rw [neg_pow]; simp [C_pow]
    rw [monomial_comp, h1, ← mul_assoc, ← C_mul, coeff_C_mul_X_pow, coeff_monomial]
    by_cases h : n = e
    · subst h; simp; ring
    · simp [h]
      intro h'; exact absurd h'.symm h

omit hp5 in
/-- Taylor expansion to order 2 with `p`-integral remainder. -/
theorem taylor_pdv {g : ℚ[X]} (hg : PInt p g) {x : ℚ} (hx : x ∈ LocRing p) :
    ∃ z : ℚ, z ∈ LocRing p ∧
      g.eval (x + p) = g.eval x + p * (derivative g).eval x +
        (p : ℚ) ^ 2 / 2 * (derivative (derivative g)).eval x + (p : ℚ) ^ 3 * z := by
  set T := taylor x g with hT
  have hc : ∀ j, T.coeff j ∈ LocRing p := fun j => by
    rw [hT, taylor_coeff]; exact (hg.hasseDeriv j).eval_mem hx
  have h2 : 2 * T.coeff 2 = (derivative (derivative g)).eval x := by
    have hd : derivative (derivative g) = C (2 : ℚ) * hasseDeriv 2 g := by
      ext n
      rw [coeff_derivative, coeff_derivative, coeff_C_mul, hasseDeriv_coeff, Nat.cast_choose_two]
      push_cast
      ring
    rw [hd, hT, taylor_coeff, eval_mul, eval_C]
  have hev : g.eval (x + p) = T.eval (p : ℚ) := by rw [hT, taylor_eval, add_comm]
  refine ⟨∑ i ∈ range T.natDegree, T.coeff (i + 3) * (p : ℚ) ^ i, ?_, ?_⟩
  · exact (LocRing p).sum_mem fun i _ => (LocRing p).mul_mem (hc _) ((LocRing p).pow_mem p_mem _)
  · rw [hev, eval_eq_sum_range' (n := T.natDegree + 3) (by omega)]
    rw [show T.natDegree + 3 = (T.natDegree + 1 + 1) + 1 from rfl, sum_range_succ', sum_range_succ',
      sum_range_succ']
    have e0 : T.coeff 0 = g.eval x := by rw [hT, taylor_coeff_zero]
    have e1 : T.coeff 1 = (derivative g).eval x := by rw [hT, taylor_coeff_one]
    rw [← h2, e0, e1]
    have : ∑ i ∈ range T.natDegree, T.coeff (i + 1 + 1 + 1) * (p : ℚ) ^ (i + 1 + 1 + 1) =
        (p : ℚ) ^ 3 * ∑ i ∈ range T.natDegree, T.coeff (i + 3) * (p : ℚ) ^ i := by
      rw [mul_sum]
      refine sum_congr rfl fun i _ => ?_
      rw [show i + 1 + 1 + 1 = i + 3 from rfl]; ring
    rw [this]
    simp only [zero_add, pow_zero, pow_one]
    ring

end Jets

end CatalanCore.NT
