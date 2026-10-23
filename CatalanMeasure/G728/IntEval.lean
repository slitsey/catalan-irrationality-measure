module

public import CatalanMeasure.Cert.FieldEval

@[expose] public section

/-!
# Integer evaluation of the finite Chebyshev / power sums

For a coefficient list `cs` (length `n`) and a rational point `c = a / D` (`a = c.num`, `D = c.den`),
the finite sums
`Σ_{k<n} (cs_k / 2^40) T_{k+1}(c) / (k+1)` and `Σ_{k<n} (cs_k / 2^40) c^{k+1} / (k+1)`
are computed with big-INTEGER arithmetic only (no `ℚ` gcd per step): with `L = n!`, `N_k = D^k T_k(c)`
satisfies `N_{k+2} = 2 a N_{k+1} - D² N_k`, and a Horner scheme in `D` gives
`Acc = D^n Σ_k cs_k (L/(k+1)) T_{k+1}(c)`.  The value is `Acc / (2^40 · L · D^n)`; `encDiv` rounds it
to a dyadic enclosure of width `2^-128`.
-/

open Polynomial

namespace CatalanMeasure.G728
open CatalanMeasure.Cert

/-- `N_n = D^n T_n(a/D)`. -/
def chebN (a D : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => a
  | n + 2 => 2 * a * chebN a D (n + 1) - D * D * chebN a D n

theorem chebN_cast (a D : ℤ) (x : ℝ) (hx : (a : ℝ) = x * D) (n : ℕ) :
    (chebN a D n : ℝ) = (D : ℝ) ^ n * (Chebyshev.T ℝ (n : ℤ)).eval x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [chebN, Chebyshev.T_zero]
  | one => simp [chebN, Chebyshev.T_one, hx]; ring
  | more n h1 h2 =>
    have h := Chebyshev.T_add_two ℝ (n : ℤ)
    have e : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
    rw [e, h]
    simp only [chebN]
    push_cast at h1 h2 ⊢
    rw [h1, h2, hx]
    simp only [eval_sub, eval_mul, eval_X, eval_ofNat]
    ring

/-- The Horner/Clenshaw-free loop for `Σ cs_k (L/(k+1)) T_{k+1}`; state: remaining coefficients,
index `k`, `N_{k+1}`, `N_{k+2}`, accumulator. -/
def chebLoop (L : ℕ) (a D : ℤ) : List ℤ → ℕ → ℤ → ℤ → ℤ → ℤ
  | [], _, _, _, acc => acc
  | m :: ms, k, n1, n2, acc =>
    chebLoop L a D ms (k + 1) n2 (2 * a * n2 - D * D * n1)
      (acc * D + m * ((L / (k + 1) : ℕ) : ℤ) * n1)

theorem chebLoop_cast (L : ℕ) (a D : ℤ) (x : ℝ) (hx : (a : ℝ) = x * D) (hD : (D : ℝ) ≠ 0) :
    ∀ (ms : List ℤ) (k : ℕ) (acc : ℤ),
      (chebLoop L a D ms k (chebN a D (k + 1)) (chebN a D (k + 2)) acc : ℝ) =
        (acc : ℝ) * (D : ℝ) ^ ms.length + (D : ℝ) ^ (k + ms.length) *
          ∑ j ∈ Finset.range ms.length, (ms.getD j 0 : ℝ) * ((L / (k + j + 1) : ℕ) : ℝ) *
            (Chebyshev.T ℝ ((k + j + 1 : ℕ) : ℤ)).eval x := by
  intro ms
  induction ms with
  | nil => intro k acc; simp [chebLoop]
  | cons m ms ih =>
    intro k acc
    have e : chebN a D (k + 3) = 2 * a * chebN a D (k + 2) - D * D * chebN a D (k + 1) := rfl
    simp only [chebLoop]
    have := ih (k + 1) (acc * D + m * ((L / (k + 1) : ℕ) : ℤ) * chebN a D (k + 1))
    rw [show k + 1 + 1 = k + 2 from rfl, show k + 1 + 2 = k + 3 from rfl, e] at this
    rw [this, List.length_cons, Finset.sum_range_succ']
    have hN := chebN_cast a D x hx (k + 1)
    simp only [List.getD_cons_zero, List.getD_cons_succ, Int.cast_add, Int.cast_mul,
      Int.cast_natCast]
    rw [hN]
    have e1 : ∀ j, k + 1 + j + 1 = k + (j + 1) + 1 := fun j => by omega
    have e2 : k + 1 + ms.length = k + (ms.length + 1) := by omega
    simp only [e1, e2, add_zero, pow_succ]
    ring

/-- Loop for `Σ cs_k (L/(k+1)) a^(k+1) D^...`; `p = a^(k+1)`. -/
def powLoop (L : ℕ) (a D : ℤ) : List ℤ → ℕ → ℤ → ℤ → ℤ
  | [], _, _, acc => acc
  | m :: ms, k, p, acc =>
    powLoop L a D ms (k + 1) (a * p) (acc * D + m * ((L / (k + 1) : ℕ) : ℤ) * p)

theorem powLoop_cast (L : ℕ) (a D : ℤ) (x : ℝ) (hx : (a : ℝ) = x * D) :
    ∀ (ms : List ℤ) (k : ℕ) (acc : ℤ),
      (powLoop L a D ms k (a ^ (k + 1)) acc : ℝ) =
        (acc : ℝ) * (D : ℝ) ^ ms.length + (D : ℝ) ^ (k + ms.length) *
          ∑ j ∈ Finset.range ms.length, (ms.getD j 0 : ℝ) * ((L / (k + j + 1) : ℕ) : ℝ) *
            x ^ (k + j + 1) := by
  intro ms
  induction ms with
  | nil => intro k acc; simp [powLoop]
  | cons m ms ih =>
    intro k acc
    simp only [powLoop]
    have := ih (k + 1) (acc * D + m * ((L / (k + 1) : ℕ) : ℤ) * a ^ (k + 1))
    rw [show a * a ^ (k + 1) = a ^ (k + 1 + 1) by ring] at *
    rw [this, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, Int.cast_add, Int.cast_mul,
      Int.cast_natCast, Int.cast_pow, hx]
    have e1 : ∀ j, k + 1 + j + 1 = k + (j + 1) + 1 := fun j => by omega
    have e2 : k + 1 + ms.length = k + (ms.length + 1) := by omega
    simp only [e1, e2, add_zero, pow_succ, mul_pow]
    ring

/-! ### Accumulators and values -/

def chebAcc (cs : List ℤ) (c : ℚ) : ℤ :=
  chebLoop (Nat.factorial cs.length) c.num (c.den : ℤ) cs 0 c.num (2 * c.num * c.num - (c.den : ℤ) * (c.den : ℤ)) 0

def powAcc (cs : List ℤ) (c : ℚ) : ℤ :=
  powLoop (Nat.factorial cs.length) c.num (c.den : ℤ) cs 0 c.num 0

/-- common denominator `2^40 · n! · D^n` -/
def evalDen (cs : List ℤ) (c : ℚ) : ℕ := 1099511627776 * (Nat.factorial cs.length) * c.den ^ cs.length

theorem evalDen_pos (cs : List ℤ) (c : ℚ) : 0 < evalDen cs c := by
  unfold evalDen
  have := c.den_pos
  positivity

theorem cast_div_fact (n j : ℕ) (hj : j < n) :
    (((Nat.factorial n) / (j + 1) : ℕ) : ℝ) = ((Nat.factorial n : ℕ) : ℝ) / ((j + 1 : ℕ) : ℝ) := by
  rw [Nat.cast_div (Nat.dvd_factorial (by omega) (by omega)) (by positivity)]

theorem rat_num_eq (c : ℚ) : ((c.num : ℤ) : ℝ) = (c : ℝ) * (c.den : ℝ) := by
  have h := Rat.num_div_den c
  have hd : (c.den : ℝ) ≠ 0 := by exact_mod_cast c.den_nz
  have : (c : ℝ) = (c.num : ℝ) / (c.den : ℝ) := by
    conv_lhs => rw [← h]
    push_cast; rfl
  rw [this]; field_simp

theorem finT_value (cs : List ℤ) (c : ℚ) :
    ((chebAcc cs c : ℤ) : ℝ) / (evalDen cs c : ℝ) =
      ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (c : ℝ) / ((k + 1 : ℕ) : ℝ) := by
  have hD : ((c.den : ℤ) : ℝ) ≠ 0 := by exact_mod_cast c.den_nz
  have hx : ((c.num : ℤ) : ℝ) = (c : ℝ) * ((c.den : ℤ) : ℝ) := by
    simpa using rat_num_eq c
  have h := chebLoop_cast (Nat.factorial cs.length) c.num (c.den : ℤ) (c : ℝ) hx hD cs 0 0
  have e2 : chebN c.num (c.den : ℤ) 2 = 2 * c.num * c.num - (c.den : ℤ) * (c.den : ℤ) := by
    simp [chebN]
  have e1 : chebN c.num (c.den : ℤ) 1 = c.num := rfl
  rw [show (0 + 1 : ℕ) = 1 from rfl, show (0 + 2 : ℕ) = 2 from rfl, e1, e2] at h
  unfold chebAcc evalDen
  rw [h]
  have hLpos : (0 : ℝ) < ((Nat.factorial cs.length) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hDpos : (0 : ℝ) < (c.den : ℝ) := by exact_mod_cast c.den_pos
  push_cast
  simp only [zero_mul, zero_add, Int.cast_zero, zero_add]
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  rw [cast_div_fact _ _ hj']
  have hk : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_add, Nat.cast_one] at hk ⊢
  field_simp

theorem finS_value (cs : List ℤ) (c : ℚ) :
    ((powAcc cs c : ℤ) : ℝ) / (evalDen cs c : ℝ) =
      ∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
        (c : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ) := by
  have hx : ((c.num : ℤ) : ℝ) = (c : ℝ) * ((c.den : ℤ) : ℝ) := by
    simpa using rat_num_eq c
  have h := powLoop_cast (Nat.factorial cs.length) c.num (c.den : ℤ) (c : ℝ) hx cs 0 0
  simp only [zero_add, pow_one] at h
  unfold powAcc evalDen
  rw [h]
  have hLpos : (0 : ℝ) < ((Nat.factorial cs.length : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hDpos : (0 : ℝ) < (c.den : ℝ) := by exact_mod_cast c.den_pos
  push_cast
  simp only [zero_mul, zero_add, Int.cast_zero]
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hj' := Finset.mem_range.mp hj
  rw [cast_div_fact _ _ hj']
  have hk : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_add, Nat.cast_one] at hk ⊢
  field_simp

/-! ### Dyadic enclosure of a quotient -/

/-- `2^128` -/
def twoPow128 : ℤ := 340282366920938463463374607431768211456

theorem twoPow128_eq : twoPow128 = 2 ^ 128 := by unfold twoPow128; norm_num

/-- enclosure `(v, e)` of `A / den`: `v = ⌊A 2^128 / den⌋ / 2^128`, `e = 2^-128`. -/
def encDiv (A : ℤ) (den : ℕ) : ℚ × ℚ :=
  (((A * twoPow128 / (den : ℤ) : ℤ) : ℚ) / (twoPow128 : ℚ), 1 / (twoPow128 : ℚ))

theorem encDiv_aux (A k : ℝ) (d S : ℝ) (hd : 0 < d) (hS : 0 < S) (h1 : d * k ≤ A * S)
    (h2 : A * S < d * (k + 1)) : |A / d - k / S| ≤ 1 / S := by
  have key : A / d - k / S = (A * S - d * k) / (d * S) := by field_simp
  rw [key, abs_le]
  have hdS : 0 < d * S := mul_pos hd hS
  constructor
  · have : 0 ≤ (A * S - d * k) / (d * S) := div_nonneg (by linarith) hdS.le
    have h0 : 0 ≤ 1 / S := by positivity
    linarith
  · rw [div_le_iff₀ hdS]
    have : 1 / S * (d * S) = d := by field_simp
    rw [this]
    linarith

theorem encDiv_spec (A : ℤ) {den : ℕ} (hden : 0 < den) :
    |(A : ℝ) / (den : ℝ) - ((encDiv A den).1 : ℝ)| ≤ ((encDiv A den).2 : ℝ) := by
  have hbpos : 0 < (den : ℤ) := by exact_mod_cast hden
  have h1 : (den : ℤ) * (A * twoPow128 / (den : ℤ)) ≤ A * twoPow128 :=
    Int.mul_ediv_self_le hbpos.ne'
  have h2 : A * twoPow128 < (den : ℤ) * (A * twoPow128 / (den : ℤ) + 1) := by
    have := Int.emod_lt_of_pos (A * twoPow128) hbpos
    have h3 := Int.mul_ediv_add_emod (A * twoPow128) (den : ℤ)
    nlinarith [this]
  have hS : (0 : ℝ) < (twoPow128 : ℝ) := by unfold twoPow128; norm_num
  have hbR : (0 : ℝ) < (den : ℝ) := by exact_mod_cast hden
  have h1R : (den : ℝ) * ((A * twoPow128 / (den : ℤ) : ℤ) : ℝ) ≤ (A : ℝ) * (twoPow128 : ℝ) := by
    exact_mod_cast h1
  have h2R : (A : ℝ) * (twoPow128 : ℝ) <
      (den : ℝ) * (((A * twoPow128 / (den : ℤ) : ℤ) : ℝ) + 1) := by exact_mod_cast h2
  have := encDiv_aux (A : ℝ) ((A * twoPow128 / (den : ℤ) : ℤ) : ℝ) (den : ℝ) (twoPow128 : ℝ)
    hbR hS h1R h2R
  unfold encDiv
  push_cast
  exact this

def finTEnc (cs : List ℤ) (c : ℚ) : ℚ × ℚ := encDiv (chebAcc cs c) (evalDen cs c)
def finSEnc (cs : List ℤ) (c : ℚ) : ℚ × ℚ := encDiv (powAcc cs c) (evalDen cs c)

theorem finTEnc_spec (cs : List ℤ) (c : ℚ) :
    |(∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
        (Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (c : ℝ) / ((k + 1 : ℕ) : ℝ)) -
      ((finTEnc cs c).1 : ℝ)| ≤ ((finTEnc cs c).2 : ℝ) := by
  rw [← finT_value]
  exact encDiv_spec _ (evalDen_pos cs c)

theorem finSEnc_spec (cs : List ℤ) (c : ℚ) :
    |(∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 1099511627776) *
        (c : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) - ((finSEnc cs c).1 : ℝ)| ≤
      ((finSEnc cs c).2 : ℝ) := by
  rw [← finS_value]
  exact encDiv_spec _ (evalDen_pos cs c)

end CatalanMeasure.G728
