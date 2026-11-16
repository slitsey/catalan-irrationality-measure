module

public import CatalanCore.Zeta5.Frames.Normalizer

@[expose] public section

/-!
# ZC20, integer part: the discrete outer cost `w(K,p)` against a closed integer expression

`K = 40 n`, `N = 3 n`, `h = 37 n`. For a prime `K/3 < p ≤ 2h` the signed outer exponent is
`w(K,p) = -v_p(S_K) - γ_p^out` (`γ_p^out = gammaOut` for `p ≤ K`, `0` for `p > K`).

* `vSK_outer` : `v_p(S_K)` in the outer range, by Legendre's first power and a floor sum
  (`floor_sum_outer`: `∑_{i<h} ⌊2i/p⌋ = ∑_{j=1}^{5} (h - ⌈jp/2⌉)`).
* `pExZ n p` : the integer `p · Ex(K/p)` (the closed form of `K T₀(p/K)`), written with `min`, `max`
  and the four `(q, 2v < p)` cases of the class-count weights (tables `Sq`, `Nq` of `Sum.OuterDefs`).
* `outer_int_bound` : `-10 ≤ w(K,p) - pExZ n p ≤ 2` for odd `p` with `K/3 < p ≤ 2h`.

The identification `p · Ex(K/p) = pExZ n p` is in `CostOut.OuterCost`.
-/

open Finset

namespace CatalanCore.Zeta5.CostOut

open Apery

/-- `∑_{i=1}^{h-1} ⌊2i/p⌋ = ∑_{j=1}^{5} (h - ⌈jp/2⌉)` for `K < 3p`. -/
lemma floor_sum_outer {n p : ℕ} (hn : 1 ≤ n) (hp : 40 * n < 3 * p) :
    ∑ i ∈ Icc 1 (37 * n - 1), (2 * i) / p
      = (37 * n - (p + 1) / 2) + (37 * n - (2 * p + 1) / 2) + (37 * n - (3 * p + 1) / 2)
        + (37 * n - (4 * p + 1) / 2) + (37 * n - (5 * p + 1) / 2) := by
  have hp0 : 0 < p := by omega
  have key : ∀ i ∈ Icc 1 (37 * n - 1),
      (2 * i) / p = ∑ j ∈ Icc 1 5, if j * p ≤ 2 * i then 1 else 0 := by
    intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have hq : 2 * i / p ≤ 5 := by
      have h6 : 2 * i < 6 * p := by omega
      have := (Nat.div_lt_iff_lt_mul hp0).mpr (show 2 * i < 6 * p from h6)
      omega
    have h1 : ∀ j, j * p ≤ 2 * i ↔ j ≤ 2 * i / p := fun j => (Nat.le_div_iff_mul_le hp0).symm
    simp only [h1]
    generalize 2 * i / p = q at hq ⊢
    interval_cases q <;> decide
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  have hj : ∀ j ∈ Icc 1 5,
      ∑ i ∈ Icc 1 (37 * n - 1), (if j * p ≤ 2 * i then 1 else 0) = 37 * n - (j * p + 1) / 2 := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have hjp : 1 ≤ j * p := Nat.mul_pos (by omega) hp0
    rw [Finset.sum_boole]
    have hf : (Icc 1 (37 * n - 1)).filter (fun i => j * p ≤ 2 * i)
        = Icc ((j * p + 1) / 2) (37 * n - 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hf, Nat.card_Icc]
    norm_num only [Nat.cast_id]
    omega
  rw [Finset.sum_congr rfl hj]
  have hI : Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) := by decide
  rw [hI]
  simp [Finset.sum_insert]
  omega

/-- The closed `v_p(S_K)` of the outer range. -/
def vSz (n p : ℕ) : ℤ :=
  74 * (n : ℤ) * ((40 * n / p : ℕ) : ℤ)
    - 2 * (((37 * n - (p + 1) / 2 : ℕ) : ℤ) + ((37 * n - (2 * p + 1) / 2 : ℕ) : ℤ)
      + ((37 * n - (3 * p + 1) / 2 : ℕ) : ℤ) + ((37 * n - (4 * p + 1) / 2 : ℕ) : ℤ)
      + ((37 * n - (5 * p + 1) / 2 : ℕ) : ℤ))

/-- **`v_p(S_K)` for `K/3 < p`** (so `⌊N/p⌋ = 0`, `p² > 2K`, `p` odd). -/
theorem vSK_outer {n p : ℕ} [hp : Fact p.Prime] (hn : 1 ≤ n) (h : 40 * n < 3 * p) :
    vSK n p = vSz n p := by
  have hp14 : 14 ≤ p := by omega
  have h2 : 2 * (40 * n) < p ^ 2 := by nlinarith
  unfold vSK
  rw [vS_eq_firstPower (by omega) hp.out h2]
  have h4 : padicValNat p 4 = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun hd => by
      have := Nat.le_of_dvd (by norm_num) hd
      omega)
  have h3 : (3 * n) / p = 0 := Nat.div_eq_of_lt (by omega)
  rw [h4, h3, ← Nat.cast_sum, floor_sum_outer hn h]
  unfold vSz
  push_cast
  ring

/-- The scalar (Legendre) part of `p · Ex(K/p)`:
`-2h q + ∑_{j=1}^5 (2h - j p)₊`. -/
def scalarPart (n P Q : ℤ) : ℤ :=
  -(74 * n * Q) + max 0 (74 * n - P) + max 0 (74 * n - 2 * P) + max 0 (74 * n - 3 * P)
    + max 0 (74 * n - 4 * P) + max 0 (74 * n - 5 * P)

/-- `p · r(1/x)`: `min(37 n, (52 n - 2 p)₊)`. -/
def rPart (n P : ℤ) : ℤ := min (37 * n) (max 0 (52 * n - 2 * P))

/-- `-p · G(1/x) + p · min(r, Z)` for `K/3 < p < K` (`q = ⌊K/p⌋ ∈ {1,2}`, `v = K mod p`):
with `t = min(v, p - v)`, `a = N`, the four class-count regions. -/
def inPart (n P Q V : ℤ) : ℤ :=
  let t := min V (P - V)
  let a := 3 * n
  let mn := min t a
  let d1 := max 0 (t - a)
  let d2 := max 0 (a - t)
  let mx := max t a
  if Q = 1 then
    if 2 * V < P then
      (mn + 7 * d1) + min (rPart n P) (mn + 2 * d1 + d2 + P - 2 * mx)
    else
      (mn + 7 * d1 + 2 * d2 + 7 * P - 14 * mx) + min (rPart n P) (mn + 2 * d1 + 2 * d2 + P - 2 * mx)
  else
    if 2 * V < P then
      (4 * mn + 21 * d1 + 2 * d2 + 7 * P - 14 * mx)
        + min (rPart n P) (2 * mn + 2 * d1 + 2 * d2 + P - 2 * mx)
    else
      (4 * mn + 21 * d1 + 6 * d2 + 14 * P - 28 * mx)
        + min (rPart n P) (2 * mn + 2 * d1 + 3 * d2 + P - 2 * mx)

/-- The integer `p · Ex(K/p)`. -/
def pExZ (n p : ℕ) : ℤ :=
  if 40 * n ≤ p then
    min (37 * (n : ℤ)) (rPart n p) + scalarPart n p ((40 * n / p : ℕ) : ℤ)
  else
    inPart n p ((40 * n / p : ℕ) : ℤ) ((40 * n % p : ℕ) : ℤ) + scalarPart n p ((40 * n / p : ℕ) : ℤ)

/-- The signed outer exponent `w(K,p) = -v_p(S_K) - γ_p^out` (`γ_p^out = 0` for `p > K`). -/
def wOutZ (n p : ℕ) : ℤ := -vSz n p - (if p ≤ 40 * n then gammaOut n p else 0)

/-- The Legendre/scalar parts agree up to the ceilings: `-3 ≤ -v_p(S_K) - scalar ≤ 0`. -/
lemma scalar_bound (n p Q : ℕ) (hodd : p % 2 = 1) (hQ : 40 * n / p = Q) :
    -3 ≤ -vSz n p - scalarPart n p (Q : ℤ) ∧ -vSz n p - scalarPart n p (Q : ℤ) ≤ 0 := by
  subst hQ
  unfold vSz scalarPart
  omega

set_option maxHeartbeats 4000000 in
/-- Inner part, `K/3 < p < K`: `-7 ≤ -γ_p^out - inPart ≤ 3`. -/
lemma in_bound {n p : ℕ} (hn : 1 ≤ n) (hodd : p % 2 = 1) (h1 : 40 * n < 3 * p)
    (h3 : p < 40 * n) :
    -7 ≤ -gammaOut n p - inPart n p ((40 * n / p : ℕ) : ℤ) ((40 * n % p : ℕ) : ℤ) ∧
      -gammaOut n p - inPart n p ((40 * n / p : ℕ) : ℤ) ((40 * n % p : ℕ) : ℤ) ≤ 3 := by
  have hp0 : 0 < p := by omega
  have hd := Nat.div_add_mod (40 * n) p
  have hv := Nat.mod_lt (40 * n) hp0
  unfold gammaOut
  generalize 40 * n / p = q at hd ⊢
  generalize 40 * n % p = v at hd hv ⊢
  have hq : q = 1 ∨ q = 2 := by
    have h1' : 1 ≤ q := by
      by_contra hc
      have : q = 0 := by omega
      subst this
      omega
    have h2' : q < 3 := by
      by_contra hc
      have : 3 ≤ q := by omega
      have : p * 3 ≤ p * q := Nat.mul_le_mul_left p this
      omega
    omega
  rcases hq with rfl | rfl
  · unfold inPart rPart
    simp only [show 40 * n < 2 * p from by omega, Nat.cast_one, ite_true]
    omega
  · unfold inPart rPart
    simp only [show ¬ 40 * n < 2 * p from by omega, Nat.cast_ofNat, ite_false, show (2:ℤ) ≠ 1 from by norm_num]
    omega

/-- **ZC20, integer form.** For odd `p`, `K/3 < p ≤ 2h`: `-10 ≤ w(K,p) - pExZ ≤ 3`. -/
theorem outer_int_bound {n p : ℕ} (hn : 1 ≤ n) (hodd : p % 2 = 1) (h1 : 40 * n < 3 * p)
    (h2 : p ≤ 74 * n) :
    -10 ≤ wOutZ n p - pExZ n p ∧ wOutZ n p - pExZ n p ≤ 3 := by
  have hs := scalar_bound n p _ hodd rfl
  have hne : p ≠ 40 * n := by omega
  unfold wOutZ pExZ
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have hi := in_bound hn hodd h1 hlt
    simp only [show p ≤ 40 * n by omega, show ¬ 40 * n ≤ p by omega, ite_true, ite_false]
    omega
  · simp only [show ¬ p ≤ 40 * n by omega, show 40 * n ≤ p by omega, ite_true, ite_false]
    unfold rPart
    omega

end CatalanCore.Zeta5.CostOut
