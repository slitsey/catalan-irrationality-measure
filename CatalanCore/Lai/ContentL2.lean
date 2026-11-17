module

public import CatalanCore.Lai.ContentLaw
public import Mathlib.Data.ZMod.Basic
public import CatalanCore.Content.ShiftLemma
public import CatalanCore.Content.WeightedDet
public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# `CatalanCore.Lai.ContentL2`: Lemma G (generic node constants) and window sums for Theorem L2

Content note `N9-LAI-CONTENT-EXACT-2026-11-16.md`, Lemma G, Lemma SH and Theorem L2 step 5.

* `PartG1` (digit form of Lemma G): `choose_digits_mod` (two-digit binomial, unit part modulo `p^2`),
  `coef_digits_mod`, `laiCoef_mod_p2`: for `k = ℓ p + s`, `c_k = p^{σ(s)} u` and in `ZMod (p^2)`
  `u = Kc(ℓ) · ĉ_s · (1 + p E_ℓ(s))` with the harmonic correction `E_ℓ(s)` of the paper.
* `PartSO`: `sum_window_poly_zero` (content note Lemma 2.4 restricted to a residue window) and
  `second_order_sum` (second-order window sum: only the total weight of the harmonic terms survives,
  Lemma SH + Lemma 2.4).
* `PartDR`: `divisor_rigidity`, the rational-function part of Lemma R (translation-invariant divisor vanishing on the window is zero).
* `PartOP`: `orth_poly_scaled`, the Cramer form of the orthogonal polynomial of Lemma H (no division by the Hankel determinant).
* `PartG2`: the generic functional `L_T` (`laiLT`), its specialisation (`specT_laiLT`), the valuation
  transfer from `det L_T(t^{i+j})` to `det L_n(t^{i+j})` (`GV_det_transfer`), the integer lifts of the unit
  part (`laiCoef_cl_kappa`), and the leading term of a modified node (`node_lead_T`).
-/

section PartG1

open Finset CatalanCore.Content
open scoped Nat

namespace CatalanCore.Lai

section G1

variable {p : ℕ} [hp : Fact p.Prime]

/-- Unit part of `(c p + e)!` modulo `p²`: `c! ((p-1)!)^c e! (1 + c p H_e)`. -/
def Wz (p c e : ℕ) : ZMod (p ^ 2) :=
  (c.factorial : ZMod (p ^ 2)) * ((p - 1).factorial : ZMod (p ^ 2)) ^ c * (e.factorial : ZMod (p ^ 2)) *
    (1 + (c : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * Hz p e)

lemma isUnit_fact_p2 (m : ℕ) (hm : m < p) : IsUnit ((m.factorial : ℕ) : ZMod (p ^ 2)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, Nat.cast_mul]
    exact (isUnit_cast_p2 (p := p) (i := m + 1) (by omega) hm).mul (ih (by omega))

lemma isUnit_one_add_p (x : ZMod (p ^ 2)) :
    IsUnit (1 + (p : ZMod (p ^ 2)) * x) := by
  refine IsUnit.of_mul_eq_one (1 - (p : ZMod (p ^ 2)) * x) ?_
  have hs := pp_sq (p := p)
  linear_combination (-(x * x)) * hs

lemma isUnit_Wz (c e : ℕ) (hc : c < p) (he : e < p) : IsUnit (Wz p c e) := by
  unfold Wz
  have h1 := isUnit_fact_p2 (p := p) c hc
  have h2 := isUnit_fact_p2 (p := p) (p - 1) (by have := hp.out.pos; omega)
  have h3 := isUnit_fact_p2 (p := p) e he
  have h4 : IsUnit (1 + (c : ZMod (p ^ 2)) * (p : ZMod (p ^ 2)) * Hz p e) := by
    have := isUnit_one_add_p (p := p) ((c : ZMod (p ^ 2)) * Hz p e)
    convert this using 2; ring
  exact ((h1.mul (h2.pow c)).mul h3).mul h4

/-- Two-digit binomial coefficient: Kummer's exponent and the unit part modulo `p²`. -/
theorem choose_digits_mod (h3 : 3 ≤ p) (c e c1 e1 c2 e2 : ℕ) (hc : c < p) (he : e < p) (he1 : e1 < p)
    (he2 : e2 < p) (hsum : c * p + e = (c1 * p + e1) + (c2 * p + e2)) :
    ∃ u : ℕ, (c * p + e).choose (c1 * p + e1) = p ^ (c - c1 - c2) * u ∧ c1 + c2 ≤ c ∧
      (u : ZMod (p ^ 2)) * Wz p c1 e1 * Wz p c2 e2 = Wz p c e := by
  have hpp := hp.out.pos
  have hle : c1 + c2 ≤ c := by
    by_contra hcon
    push_neg at hcon
    have : (c + 1) * p ≤ (c1 + c2) * p := Nat.mul_le_mul_right p (by omega)
    nlinarith
  have hc1 : c1 < p := by omega
  have hc2 : c2 < p := by omega
  obtain ⟨wa, ha, hac⟩ := fact_digits_mod (p := p) h3 c e he
  obtain ⟨w1, h1', h1c⟩ := fact_digits_mod (p := p) h3 c1 e1 he1
  obtain ⟨w2, h2', h2c⟩ := fact_digits_mod (p := p) h3 c2 e2 he2
  have hk : c1 * p + e1 ≤ c * p + e := by omega
  have hsub : c * p + e - (c1 * p + e1) = c2 * p + e2 := by omega
  have hrel : (c * p + e).factorial = (c * p + e).choose (c1 * p + e1) * (c1 * p + e1).factorial *
      (c2 * p + e2).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial hk
    rw [hsub] at h
    exact h.symm
  rw [ha, h1', h2'] at hrel
  have hpos : 0 < p ^ (c1 + c2) := pow_pos hpp _
  have hexp : p ^ c = p ^ (c1 + c2) * p ^ (c - c1 - c2) := by
    rw [← pow_add]; congr 1; omega
  have hrel2 : wa * p ^ (c - c1 - c2) = (c * p + e).choose (c1 * p + e1) * (w1 * w2) := by
    have h := hrel
    rw [hexp] at h
    have h' : p ^ (c1 + c2) * (wa * p ^ (c - c1 - c2)) =
        p ^ (c1 + c2) * ((c * p + e).choose (c1 * p + e1) * (w1 * w2)) := by
      calc _ = p ^ (c1 + c2) * p ^ (c - c1 - c2) * wa := by ring
        _ = _ := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h'
  have hu1 : IsUnit (Wz p c1 e1) := isUnit_Wz c1 e1 hc1 he1
  have hu2 : IsUnit (Wz p c2 e2) := isUnit_Wz c2 e2 hc2 he2
  have hw1 : Nat.Coprime p w1 := by
    have : IsUnit ((w1 : ℕ) : ZMod (p ^ 2)) := by rw [h1c]; exact hu1
    rw [ZMod.isUnit_iff_coprime] at this
    exact (Nat.Coprime.coprime_dvd_right (dvd_pow_self p two_ne_zero) this).symm
  have hw2 : Nat.Coprime p w2 := by
    have : IsUnit ((w2 : ℕ) : ZMod (p ^ 2)) := by rw [h2c]; exact hu2
    rw [ZMod.isUnit_iff_coprime] at this
    exact (Nat.Coprime.coprime_dvd_right (dvd_pow_self p two_ne_zero) this).symm
  have hcop : Nat.Coprime (p ^ (c - c1 - c2)) (w1 * w2) :=
    Nat.Coprime.pow_left _ (Nat.Coprime.mul_right hw1 hw2)
  have hdvd : p ^ (c - c1 - c2) ∣ (c * p + e).choose (c1 * p + e1) := by
    have : p ^ (c - c1 - c2) ∣ (c * p + e).choose (c1 * p + e1) * (w1 * w2) :=
      ⟨wa, by rw [← hrel2]; ring⟩
    exact hcop.dvd_of_dvd_mul_right this
  obtain ⟨u, hu⟩ := hdvd
  refine ⟨u, hu, hle, ?_⟩
  have hpv : 0 < p ^ (c - c1 - c2) := pow_pos hpp _
  have hfin : wa = u * (w1 * w2) := by
    have : p ^ (c - c1 - c2) * wa = p ^ (c - c1 - c2) * (u * (w1 * w2)) := by
      calc _ = wa * p ^ (c - c1 - c2) := by ring
        _ = (c * p + e).choose (c1 * p + e1) * (w1 * w2) := hrel2
        _ = _ := by rw [hu]; ring
    exact Nat.eq_of_mul_eq_mul_left hpv this
  have := congrArg (fun z : ℕ => (z : ZMod (p ^ 2))) hfin
  simp only [Nat.cast_mul] at this
  rw [hac, h1c, h2c] at this
  unfold Wz
  linear_combination -this


/-- Jet cancellation in a commutative ring where `π² = 0`. -/
lemma jet_ratio {R : Type*} [CommRing R] (π : R) (hπ : π * π = 0) {u c1 c2 c3 a b x1 x2 x3 : R}
    (h : u * (c1 * (1 + π * x1)) * (c2 * (1 + π * x2)) = c3 * (1 + π * x3))
    (ha : c1 * a = 1) (hb : c2 * b = 1) :
    u = c3 * a * b * (1 + π * (x3 - x1 - x2)) := by
  have e1 : (1 + π * x1) * (1 - π * x1) = 1 := by linear_combination (-(x1 * x1)) * hπ
  have e2 : (1 + π * x2) * (1 - π * x2) = 1 := by linear_combination (-(x2 * x2)) * hπ
  calc u = u * (c1 * a) * (c2 * b) * (((1 + π * x1) * (1 - π * x1)) * ((1 + π * x2) * (1 - π * x2))) := by
        rw [ha, hb, e1, e2]; ring
    _ = (u * (c1 * (1 + π * x1)) * (c2 * (1 + π * x2))) * (a * b * (1 - π * x1) * (1 - π * x2)) := by ring
    _ = c3 * (1 + π * x3) * (a * b * (1 - π * x1) * (1 - π * x2)) := by rw [h]
    _ = c3 * a * b * (1 + π * (x3 - x1 - x2)) := by
        linear_combination (c3 * a * b * (x1 * x2 - x3 * (x1 + x2) + π * x1 * x2 * x3)) * hπ

lemma jet_mul {R : Type*} [CommRing R] (π : R) (hπ : π * π = 0) (c d x y : R) :
    (c * (1 + π * x)) * (d * (1 + π * y)) = (c * d) * (1 + π * (x + y)) := by
  linear_combination (c * d * x * y) * hπ

lemma jet_pow2 {R : Type*} [CommRing R] (π : R) (hπ : π * π = 0) (c x : R) :
    (c * (1 + π * x)) ^ 2 = c ^ 2 * (1 + π * (2 * x)) := by
  linear_combination (c ^ 2 * x * x) * hπ

lemma jet_pow3 {R : Type*} [CommRing R] (π : R) (hπ : π * π = 0) (c x : R) :
    (c * (1 + π * x)) ^ 3 = c ^ 3 * (1 + π * (3 * x)) := by
  linear_combination (c ^ 3 * (3 * x * x + π * x * x * x)) * hπ


/-- `A(c) = c! ((p-1)!)^c`, the high-digit part of a factorial unit. -/
def Aw (p c : ℕ) : ZMod (p ^ 2) := (c.factorial : ZMod (p ^ 2)) * ((p - 1).factorial : ZMod (p ^ 2)) ^ c

/-- Inverse of `Aw` (as an explicit product of inverses of units). -/
def Awi (p c : ℕ) : ZMod (p ^ 2) :=
  ((c.factorial : ZMod (p ^ 2)))⁻¹ * (((p - 1).factorial : ZMod (p ^ 2)))⁻¹ ^ c

/-- `B(e) = e!`, the low-digit part. -/
def Bw (p e : ℕ) : ZMod (p ^ 2) := (e.factorial : ZMod (p ^ 2))

def Bwi (p e : ℕ) : ZMod (p ^ 2) := ((e.factorial : ZMod (p ^ 2)))⁻¹

lemma Wz_eq (c e : ℕ) :
    Wz p c e = (Aw p c * Bw p e) * (1 + (p : ZMod (p ^ 2)) * ((c : ZMod (p ^ 2)) * Hz p e)) := by
  unfold Wz Aw Bw; ring

lemma Aw_mul_Awi (c : ℕ) (hc : c < p) : Aw p c * Awi p c = 1 := by
  have h1 := ZMod.mul_inv_of_unit _ (isUnit_fact_p2 (p := p) c hc)
  have h2 := ZMod.mul_inv_of_unit _ (isUnit_fact_p2 (p := p) (p - 1) (by have := hp.out.pos; omega))
  unfold Aw Awi
  calc _ = ((c.factorial : ZMod (p ^ 2)) * ((c.factorial : ZMod (p ^ 2)))⁻¹) *
        (((p - 1).factorial : ZMod (p ^ 2)) * (((p - 1).factorial : ZMod (p ^ 2)))⁻¹) ^ c := by ring
    _ = 1 := by rw [h1, h2]; simp

lemma Bw_mul_Bwi (e : ℕ) (he : e < p) : Bw p e * Bwi p e = 1 :=
  ZMod.mul_inv_of_unit _ (isUnit_fact_p2 (p := p) e he)

/-- The `s`-independent part of the unit coefficient (Lemma G), depending on the class flags and `ℓ`. -/
def Kc (p q6 r6 q2 r2 b ε ℓ : ℕ) : ZMod (p ^ 2) :=
  (Aw p q6 * Awi p ℓ * Awi p (q6 - ℓ - b)) ^ 2 * (Aw p (q2 + ℓ + ε) * Awi p ℓ * Awi p q2) ^ 3 *
    (1 + (p : ZMod (p ^ 2)) * (2 * (q6 : ZMod (p ^ 2)) * Hz p r6 - 3 * (q2 : ZMod (p ^ 2)) * Hz p r2))

/-- The low-digit factorial ratio `ĉ_s`, lifted to `ZMod (p²)`. -/
def Cs (p r6 r2 b ε s : ℕ) : ZMod (p ^ 2) :=
  (Bw p r6 * Bwi p s * Bwi p (r6 + b * p - s)) ^ 2 * (Bw p (r2 + s - ε * p) * Bwi p s * Bwi p r2) ^ 3

/-- The `s`-dependent first-order correction `E_ℓ(s)` of Lemma G. -/
def Es (p q6 r6 q2 r2 b ε ℓ s : ℕ) : ZMod (p ^ 2) :=
  -5 * (ℓ : ZMod (p ^ 2)) * Hz p s - 2 * ((q6 - ℓ - b : ℕ) : ZMod (p ^ 2)) * Hz p (r6 + b * p - s) +
    3 * ((q2 + ℓ + ε : ℕ) : ZMod (p ^ 2)) * Hz p (r2 + s - ε * p)


/-- **Lemma G, digit form (unit part of Lai's coefficient modulo `p²`).**
For `6n = q6 p + r6`, `2n = q2 p + r2`, `k = ℓ p + s` the coefficient
`C(6n,k)² C(2n+k,k)³ = p^{2b+3ε} u` has `u ≡ Kc · ĉ_s · (1 + p E_ℓ(s))` in `ZMod (p²)`. -/
theorem coef_digits_mod (h3 : 3 ≤ p) (q6 r6 q2 r2 ℓ s b ε : ℕ)
    (hq6 : q6 < p) (hr6 : r6 < p) (hq2 : q2 + ℓ + ε < p) (hr2 : r2 < p) (hs : s < p)
    (hℓ : ℓ + b ≤ q6)
    (hb : (b = 0 ∧ s ≤ r6) ∨ (b = 1 ∧ r6 < s))
    (hε : (ε = 0 ∧ r2 + s < p) ∨ (ε = 1 ∧ p ≤ r2 + s)) :
    ∃ u1 u2 : ℕ,
      (q6 * p + r6).choose (ℓ * p + s) = p ^ b * u1 ∧
      ((q2 + ℓ + ε) * p + (r2 + s - ε * p)).choose (ℓ * p + s) = p ^ ε * u2 ∧
      ((u1 ^ 2 * u2 ^ 3 : ℕ) : ZMod (p ^ 2)) =
        Kc p q6 r6 q2 r2 b ε ℓ * Cs p r6 r2 b ε s * (1 + (p : ZMod (p ^ 2)) * Es p q6 r6 q2 r2 b ε ℓ s) := by
  have hpp := hp.out.pos
  set t : ℕ := q6 - ℓ - b with ht
  have hbp : b * p ≤ p := by rcases hb with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
  have he2 : r6 + b * p - s < p := by rcases hb with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp <;> omega
  have hq6' : q6 = ℓ + b + t := by omega
  have hsum1 : q6 * p + r6 = (ℓ * p + s) + (t * p + (r6 + b * p - s)) := by
    rw [hq6']
    rcases hb with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      simp only [zero_mul, add_zero, Nat.add_sub_cancel_left]; ring
    · have : r6 + 1 * p - s + s = r6 + p := by omega
      nlinarith
  have he3 : r2 + s - ε * p < p := by rcases hε with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> simp <;> omega
  have hsum2 : (q2 + ℓ + ε) * p + (r2 + s - ε * p) = (ℓ * p + s) + (q2 * p + r2) := by
    rcases hε with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · simp only [add_zero, zero_mul, Nat.sub_zero]; ring
    · have : r2 + s - 1 * p + p = r2 + s := by omega
      nlinarith
  obtain ⟨u1, hu1, hle1, hU1⟩ := choose_digits_mod (p := p) h3 q6 r6 ℓ s t (r6 + b * p - s) hq6 hr6 hs
    he2 hsum1
  obtain ⟨u2, hu2, hle2, hU2⟩ := choose_digits_mod (p := p) h3 (q2 + ℓ + ε) (r2 + s - ε * p) ℓ s q2 r2
    hq2 he3 hs hr2 hsum2
  have ex1 : q6 - ℓ - t = b := by omega
  have ex2 : q2 + ℓ + ε - ℓ - q2 = ε := by omega
  rw [ex1] at hu1
  rw [ex2] at hu2
  refine ⟨u1, u2, hu1, hu2, ?_⟩
  have hπ := pp_sq (p := p)
  set P : ZMod (p ^ 2) := (p : ZMod (p ^ 2)) with hP
  have hlt : ℓ < p := by omega
  have ht' : t < p := by omega
  have hq2' : q2 < p := by omega
  -- the two jet relations
  rw [Wz_eq, Wz_eq, Wz_eq] at hU1 hU2
  have hAB : ∀ c e : ℕ, c < p → e < p → (Aw p c * Bw p e) * (Awi p c * Bwi p e) = 1 := by
    intro c e hc he
    calc (Aw p c * Bw p e) * (Awi p c * Bwi p e) = (Aw p c * Awi p c) * (Bw p e * Bwi p e) := by ring
      _ = 1 := by rw [Aw_mul_Awi c hc, Bw_mul_Bwi e he]; ring
  have j1 := jet_ratio P hπ hU1 (hAB ℓ s hlt hs) (hAB t (r6 + b * p - s) ht' he2)
  have j2 := jet_ratio P hπ hU2 (hAB ℓ s hlt hs) (hAB q2 r2 hq2' hr2)
  push_cast
  rw [j1, j2, jet_pow2 P hπ, jet_pow3 P hπ]
  have hkey : ∀ y1 y2 c0 E : ZMod (p ^ 2), 2 * y1 + 3 * y2 = c0 + E →
      (1 + P * (2 * y1)) * (1 + P * (3 * y2)) = (1 + P * c0) * (1 + P * E) := by
    intro y1 y2 c0 E h
    linear_combination (6 * y1 * y2 - c0 * E) * hπ + P * h
  have gen : ∀ (U1 U2 K0 C0 y1 y2 c0 E : ZMod (p ^ 2)), U1 ^ 2 * U2 ^ 3 = K0 * C0 →
      2 * y1 + 3 * y2 = c0 + E →
      (U1 ^ 2 * (1 + P * (2 * y1))) * (U2 ^ 3 * (1 + P * (3 * y2))) =
        K0 * (1 + P * c0) * C0 * (1 + P * E) := by
    intro U1 U2 K0 C0 y1 y2 c0 E hU hy
    calc (U1 ^ 2 * (1 + P * (2 * y1))) * (U2 ^ 3 * (1 + P * (3 * y2)))
        = (U1 ^ 2 * U2 ^ 3) * ((1 + P * (2 * y1)) * (1 + P * (3 * y2))) := by ring
      _ = (K0 * C0) * ((1 + P * c0) * (1 + P * E)) := by rw [hU, hkey y1 y2 c0 E hy]
      _ = _ := by ring
  refine Eq.trans (gen _ _
    ((Aw p q6 * Awi p ℓ * Awi p t) ^ 2 * (Aw p (q2 + ℓ + ε) * Awi p ℓ * Awi p q2) ^ 3)
    ((Bw p r6 * Bwi p s * Bwi p (r6 + b * p - s)) ^ 2 * (Bw p (r2 + s - ε * p) * Bwi p s * Bwi p r2) ^ 3)
    _ _ (2 * (q6 : ZMod (p ^ 2)) * Hz p r6 - 3 * (q2 : ZMod (p ^ 2)) * Hz p r2)
    (Es p q6 r6 q2 r2 b ε ℓ s) ?_ ?_) ?_
  · ring
  · unfold Es; ring
  · unfold Kc Cs; ring


/-- **Lemma G, node coefficient modulo `p²`** for Lai's `c_k = C(6n,k)² C(2n+k,k)³`:
`c_k = p^{σ(s)} u` with `u ≡ Kc(class, ℓ) · ĉ_s · (1 + p E_ℓ(s))` in `ZMod (p²)`. -/
theorem laiCoef_mod_p2 {n : ℕ} (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (k : ℕ) (hk : k ≤ 6 * n) :
    ∃ u : ℕ, laiCoef n k = p ^ sig n p (k % p) * u ∧
      (u : ZMod (p ^ 2)) =
        Kc p (q6 n p) (r6 n p) (q2 n p) (r2 n p) (bflag n p (k % p)) (eflag n p (k % p)) (k / p) *
        Cs p (r6 n p) (r2 n p) (bflag n p (k % p)) (eflag n p (k % p)) (k % p) *
        (1 + (p : ZMod (p ^ 2)) *
          Es p (q6 n p) (r6 n p) (q2 n p) (r2 n p) (bflag n p (k % p)) (eflag n p (k % p)) (k / p) (k % p)) := by
  have hpp := hp.out.pos
  obtain ⟨hsd1, hsd2, hsd3⟩ := sub_div_mod p (6 * n) k hpp hk
  obtain ⟨had1, had2⟩ := add_div_mod p k (2 * n) hpp
  have hpk := Nat.mod_lt k hpp
  have hp6 := Nat.mod_lt (6 * n) hpp
  have hp2 := Nat.mod_lt (2 * n) hpp
  have hb : bflag n p (k % p) = if 6 * n % p < k % p then 1 else 0 := rfl
  have he : eflag n p (k % p) = if p - 2 * n % p ≤ k % p then 1 else 0 := rfl
  have hr6e : r6 n p = 6 * n % p := rfl
  have hr2e : r2 n p = 2 * n % p := rfl
  have hq6e : q6 n p = 6 * n / p := rfl
  have hq2e : q2 n p = 2 * n / p := rfl
  have d3 : (k + 2 * n) / p = q2 n p + k / p + eflag n p (k % p) := by
    rw [had1, he]; unfold q2; split_ifs with h1 h2 h2 <;> omega
  have d4 : (k + 2 * n) % p = r2 n p + k % p - eflag n p (k % p) * p := by
    rw [had2, he]; unfold r2; split_ifs with h1 h2 h2 <;> omega
  have hlt6 : 6 * n < p ^ 2 := by omega
  have hq6p : q6 n p < p := by
    rw [hq6e, Nat.div_lt_iff_lt_mul hpp]; simpa [pow_two] using hlt6
  have hq2p : q2 n p + k / p + eflag n p (k % p) < p := by
    rw [← d3, Nat.div_lt_iff_lt_mul hpp]; simpa [pow_two] using (show k + 2 * n < p ^ 2 by omega)
  have hbf : (bflag n p (k % p) = 0 ∧ k % p ≤ r6 n p) ∨ (bflag n p (k % p) = 1 ∧ r6 n p < k % p) := by
    rw [hb, hr6e]; split_ifs with h <;> omega
  have hef : (eflag n p (k % p) = 0 ∧ r2 n p + k % p < p) ∨ (eflag n p (k % p) = 1 ∧ p ≤ r2 n p + k % p) := by
    rw [he, hr2e]; split_ifs with h <;> omega
  have hℓb : k / p + bflag n p (k % p) ≤ q6 n p := by
    rw [hb, hq6e]; exact hsd1
  obtain ⟨u1, u2, hu1, hu2, hU⟩ := coef_digits_mod (p := p) h3 (q6 n p) (r6 n p) (q2 n p) (r2 n p) (k / p) (k % p)
    (bflag n p (k % p)) (eflag n p (k % p)) hq6p (r6_lt n p hpp) hq2p (r2_lt n p hpp) hpk hℓb hbf hef
  have e6 : q6 n p * p + r6 n p = 6 * n := (qr6 n p hpp).symm
  have ek : k / p * p + k % p = k := Nat.div_add_mod' k p
  have e2 : (q2 n p + k / p + eflag n p (k % p)) * p + (r2 n p + k % p - eflag n p (k % p) * p) =
      2 * n + k := by
    have h5 : (k + 2 * n) / p * p + (k + 2 * n) % p = k + 2 * n := Nat.div_add_mod' _ p
    rw [d3, d4] at h5; omega
  rw [e6, ek] at hu1
  rw [e2, ek] at hu2
  refine ⟨u1 ^ 2 * u2 ^ 3, ?_, hU⟩
  unfold laiCoef
  rw [hu1, hu2, sig_eq_flags]; ring

end G1

end CatalanCore.Lai

end PartG1

section PartSO

open Finset Polynomial CatalanCore.Content

namespace CatalanCore.Lai

section SO

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*} [CommRing K] [CharP K p]

/-- The sum over the residues `m < p` equals the sum over `ZMod p` (evaluating at `val`). -/
lemma sum_range_eq_sum_zmod (f : ℕ → K) :
    ∑ m ∈ range p, f m = ∑ s : ZMod p, f s.val := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  symm
  refine Finset.sum_bij (fun s _ => s.val) (fun s _ => Finset.mem_range.2 (ZMod.val_lt s))
    (fun a _ b _ h => ZMod.val_injective p h) (fun m hm => ?_) (fun s _ => rfl)
  exact ⟨(m : ZMod p), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.1 hm)⟩

/-- A polynomial of degree `≤ p - 2` vanishing at all residues outside `W` has zero sum over `W`
(content note Lemma 2.4 restricted to a window). -/
theorem sum_window_poly_zero (H : K[X]) (hH : H.natDegree ≤ p - 2) (W : Finset ℕ)
    (hW : ∀ s ∈ W, s < p) (hvan : ∀ m, m < p → m ∉ W → H.eval ((m : ℕ) : K) = 0) :
    ∑ s ∈ W, H.eval ((s : ℕ) : K) = 0 := by
  have h1 := sum_zmod_eval_eq_zero (p := p) H hH
  have h2 : ∑ s : ZMod p, H.eval (ZMod.castHom (dvd_refl p) K s) =
      ∑ m ∈ range p, H.eval ((m : ℕ) : K) := by
    rw [sum_range_eq_sum_zmod (fun m => H.eval ((m : ℕ) : K))]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [h2] at h1
  rw [← h1]
  refine Finset.sum_subset (fun s hs => Finset.mem_range.2 (hW s hs)) (fun m hm hmW => ?_)
  exact hvan m (Finset.mem_range.1 hm) hmW


/-- **Second-order window sum (only the total weight of the harmonic terms survives).**
For `G` of degree `≤ p - 4` vanishing together with `G'` at every residue outside the window `W`,
a constant `c`, a rational part `ρ` with `G ρ = H` on `W` for a polynomial `H` of degree `≤ p - 2`
vanishing outside `W`, and harmonic terms `H_{s+α}`, `H_{c-s}`, `H_{s-α'}`:
`∑_W G (c + ∑ w H_{s+α} + ∑ v H_{c'-s} + ∑ x H_{s-α'} + ρ) = (∑ w + ∑ v + ∑ x) ∫G`. -/
theorem second_order_sum (G H : K[X]) (hdeg : G.natDegree ≤ p - 4) (h5 : 5 ≤ p)
    (hH : H.natDegree ≤ p - 2) (W : Finset ℕ) (hW : ∀ s ∈ W, s < p)
    (hG : ∀ m, m < p → m ∉ W → G.eval ((m : ℕ) : K) = 0)
    (hG' : ∀ m, m < p → m ∉ W → G.derivative.eval ((m : ℕ) : K) = 0)
    (hHv : ∀ m, m < p → m ∉ W → H.eval ((m : ℕ) : K) = 0)
    (ρ : ℕ → K) (hρ : ∀ s ∈ W, G.eval ((s : ℕ) : K) * ρ s = H.eval ((s : ℕ) : K)) (c : K)
    {ι₁ ι₂ ι₃ : Type*} (S₁ : Finset ι₁) (S₂ : Finset ι₂) (S₃ : Finset ι₃)
    (w : ι₁ → K) (α : ι₁ → ℕ) (hα : ∀ i ∈ S₁, α i < p ∧ ∀ s ∈ W, s + α i < p)
    (v : ι₂ → K) (cc : ι₂ → ℕ) (hcc : ∀ i ∈ S₂, cc i < p ∧ ∀ s ∈ W, s ≤ cc i)
    (x : ι₃ → K) (α' : ι₃ → ℕ) (hα' : ∀ i ∈ S₃, α' i < p ∧ ∀ s ∈ W, α' i ≤ s) :
    ∑ s ∈ W, G.eval ((s : ℕ) : K) *
        (c + ∑ i ∈ S₁, w i * ZMod.castHom (dvd_refl p) K (harm p (s + α i)) +
          ∑ i ∈ S₂, v i * ZMod.castHom (dvd_refl p) K (harm p (cc i - s)) +
          ∑ i ∈ S₃, x i * ZMod.castHom (dvd_refl p) K (harm p (s - α' i)) + ρ s) =
      ((∑ i ∈ S₁, w i) + (∑ i ∈ S₂, v i) + ∑ i ∈ S₃, x i) * harmSum p G := by
  have hc : ∑ s ∈ W, G.eval ((s : ℕ) : K) * c = 0 := by
    rw [← Finset.sum_mul, sum_window_poly_zero G (by omega) W hW hG, zero_mul]
  have hr : ∑ s ∈ W, G.eval ((s : ℕ) : K) * ρ s = 0 := by
    rw [Finset.sum_congr rfl hρ]
    exact sum_window_poly_zero H hH W hW hHv
  have h1 : ∑ s ∈ W, G.eval ((s : ℕ) : K) * (∑ i ∈ S₁, w i * ZMod.castHom (dvd_refl p) K (harm p (s + α i))) =
      (∑ i ∈ S₁, w i) * harmSum p G := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨h1, h2⟩ := hα i hi
    rw [← harmSum_window G hdeg h5 W (α i) h1 h2 hG hG', Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have h2 : ∑ s ∈ W, G.eval ((s : ℕ) : K) * (∑ i ∈ S₂, v i * ZMod.castHom (dvd_refl p) K (harm p (cc i - s))) =
      (∑ i ∈ S₂, v i) * harmSum p G := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨h1, h2⟩ := hcc i hi
    rw [← harmSum_window_refl G hdeg h5 W (cc i) h1 h2 hG hG', Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have h3 : ∑ s ∈ W, G.eval ((s : ℕ) : K) * (∑ i ∈ S₃, x i * ZMod.castHom (dvd_refl p) K (harm p (s - α' i))) =
      (∑ i ∈ S₃, x i) * harmSum p G := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    obtain ⟨h1, h2⟩ := hα' i hi
    rw [← harmSum_window_neg G hdeg h5 W (α' i) h1 (fun s hs => ⟨h2 s hs, hW s hs⟩) hG hG',
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hc, h1, h2, h3, hr]
  ring

end SO

end CatalanCore.Lai

end PartSO

section PartG2

open Finset MvPolynomial Polynomial CatalanCore.Basic CatalanCore.Content

namespace CatalanCore.Lai

section G2

variable {p : ℕ} [hp : Fact p.Prime]

/-- Variables of the generic functional: `a, b, X` and the node constants `T^u_ℓ`
(`(ℓ, false)`), `T^v_ℓ` (`(ℓ, true)`). -/
abbrev TVar : Type := Fin 3 ⊕ (ℕ × Bool)

/-- Polynomials in `a, b, X` and the generic node constants. -/
abbrev MPT : Type := MvPolynomial TVar ℚ

/-- Embedding of `ℚ[a, b, X]` into `ℚ[a, b, X, T]`. -/
noncomputable def ren : MP →ₐ[ℚ] MPT := MvPolynomial.bind₁ (fun i => MvPolynomial.X (Sum.inl i))

noncomputable def Tu (l : ℕ) : MPT := MvPolynomial.X (Sum.inr (l, false))
noncomputable def Tv (l : ℕ) : MPT := MvPolynomial.X (Sum.inr (l, true))
noncomputable def bT : MPT := MvPolynomial.X (Sum.inl 1)

/-- The modification added at the node `k = s + ℓ p` of `L_n` (Lemma G):
`b p^{σ-3} ĉ (T^u_ℓ - τ^u_ℓ) F'(-k) + b p^{σ-4} ĉ (T^v_ℓ - τ^v_ℓ) F(-k)`. -/
noncomputable def modNd (p : ℕ) (σ : ℤ) (cl τu τv : ℚ) (l k : ℕ) (F : ℚ[X]) : MPT :=
  bT * (MvPolynomial.C ((p : ℚ) ^ (σ - 3) * cl) * (Tu l - MvPolynomial.C τu) *
        MvPolynomial.C (F.derivative.eval (-(k : ℚ))) +
      MvPolynomial.C ((p : ℚ) ^ (σ - 4) * cl) * (Tv l - MvPolynomial.C τv) *
        MvPolynomial.C (F.eval (-(k : ℚ))))

/-- The generic functional `L_T`: `L_n` plus the modifications at the nodes of the set `K`
(the `ℓ ≥ 1` nodes of the class `W`), with node data `σ k`, `ĉ_k`, `τ^u_ℓ`, `τ^v_ℓ`. -/
noncomputable def laiLT (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl : ℕ → ℚ) (τu τv : ℕ → ℚ) (F : ℚ[X]) : MPT :=
  ren (laiL n F) +
    ∑ k ∈ K, modNd p (σ k) (cl k) (τu (k / p)) (τv (k / p)) (k / p) k F

/-- The specialisation `T = τ`. -/
noncomputable def specT (τu τv : ℕ → ℚ) : TVar → MP
  | Sum.inl i => MvPolynomial.X i
  | Sum.inr (l, false) => MvPolynomial.C (τu l)
  | Sum.inr (l, true) => MvPolynomial.C (τv l)

lemma specT_ren (τu τv : ℕ → ℚ) (f : MP) :
    MvPolynomial.bind₁ (specT τu τv) (ren f) = f := by
  unfold ren
  rw [MvPolynomial.bind₁_bind₁]
  simp [specT, MvPolynomial.bind₁_X_right, MvPolynomial.bind₁_X_left]

lemma specT_modNd (τu τv : ℕ → ℚ) (σ : ℤ) (cl : ℚ) (l k : ℕ) (F : ℚ[X]) :
    MvPolynomial.bind₁ (specT τu τv) (modNd p σ cl (τu l) (τv l) l k F) = 0 := by
  simp [modNd, Tu, Tv, bT, specT, MvPolynomial.bind₁_X_right]

/-- At `T = τ` the generic functional is `L_n`. -/
theorem specT_laiLT (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl : ℕ → ℚ) (τu τv : ℕ → ℚ) (F : ℚ[X]) :
    MvPolynomial.bind₁ (specT τu τv) (laiLT (p := p) n K σ cl τu τv F) = laiL n F := by
  unfold laiLT
  rw [map_add, specT_ren, map_sum]
  simp [specT_modNd]

/-- **Lemma G, transfer.**  A valuation bound for the Hankel determinant of the generic functional
`L_T` (in the Gauss valuation over `a, b, X, T`) gives the same bound for `det L_n(t^{i+j})`,
provided the node constants `τ` are `p`-integral. -/
theorem GV_det_transfer (n : ℕ) (K : Finset ℕ) (σ : ℕ → ℤ) (cl : ℕ → ℚ) (τu τv : ℕ → ℚ)
    (hτu : ∀ l, τu l ∈ LocRing p) (hτv : ∀ l, τv l ∈ LocRing p) (e : ℤ)
    (h : GV p e (Matrix.of fun i j : Fin (3 * n) =>
        laiLT (p := p) n K σ cl τu τv (Polynomial.X ^ ((i : ℕ) + j))).det) :
    GV p e (laiMat n).det := by
  have hg : ∀ v : TVar, GV p 0 (specT τu τv v) := by
    rintro (i | ⟨l, _ | _⟩)
    · exact GV.var i
    · exact GV.const_loc (hτu l)
    · exact GV.const_loc (hτv l)
  have := GV.subst h (specT τu τv) hg
  have hmat : (Matrix.of fun i j : Fin (3 * n) =>
        laiLT (p := p) n K σ cl τu τv (Polynomial.X ^ ((i : ℕ) + j))).map
        (MvPolynomial.bind₁ (specT τu τv)) = laiMat n := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.of_apply, laiMat]
    exact specT_laiLT (p := p) n K σ cl τu τv _
  have hdet := RingHom.map_det (MvPolynomial.bind₁ (specT τu τv) : MPT →ₐ[ℚ] MP).toRingHom
    (Matrix.of fun i j : Fin (3 * n) =>
        laiLT (p := p) n K σ cl τu τv (Polynomial.X ^ ((i : ℕ) + j)))
  rw [← hmat]
  simpa [RingHom.mapMatrix_apply] using (hdet.symm ▸ this)


/-- Product of a constant and a generator of valuation `0` has the valuation of the constant. -/
lemma GV_C_mul_gen {e : ℤ} (x : ℚ) (hx : (p : ℚ) ^ (-e) * x ∈ LocRing p) (g : MPT) (hg : GV p 0 g) :
    GV p e (MvPolynomial.C x * g : MPT) := by
  have := GV.const_mul (p := p) (e := e) (e' := 0) hx hg
  simpa using this

/-- **Lemma G, leading term of a modified node.**  For `k = s + ℓ p` (`ℓ ≥ 1`), `F = (t+s)^m R`,
and node constants with `u ≡ ĉ κ (mod p)` (`c_k = p^σ u`), the `ℓ`-node of `L_T` equals
`b p^{σ+m-4} ĉ R(-s) (m(-ℓ)^{m-1} T^u_ℓ + (-ℓ)^m T^v_ℓ)` up to valuation `σ - 3 + m`.  The
node constants are `τ^u = κ u_ℓ`, `τ^v = κ v_ℓ`. -/
theorem node_lead_T (n k : ℕ) (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (hk : k ≤ 6 * n) (hl : 1 ≤ k / p)
    (u : ℕ) (hu : (laiCoef n k : ℚ) = (p : ℚ) ^ (sig n p (k % p)) * u)
    (cl κ : ℤ) (hcl : (p : ℤ) ∣ (u : ℤ) - cl * κ)
    (m : ℕ) (R : ℚ[X]) (hR : IntPoly p R) :
    GV p ((sig n p (k % p) : ℤ) - 3 + m)
      (ren (laiNd n k ((Polynomial.X + Polynomial.C ((k % p : ℕ) : ℚ)) ^ m * R)) +
        modNd p (sig n p (k % p) : ℤ) (cl : ℚ) ((κ : ℚ) * uL (k / p)) ((κ : ℚ) * vL n p k (k / p)) (k / p) k
          ((Polynomial.X + Polynomial.C ((k % p : ℕ) : ℚ)) ^ m * R) -
       MvPolynomial.C ((p : ℚ) ^ (sig n p (k % p)) * (p : ℚ) ^ m * ((p : ℚ) ^ 4)⁻¹ * cl *
          R.eval (-((k % p : ℕ) : ℚ))) * bT *
        (MvPolynomial.C ((m : ℚ) * (-((k / p : ℕ) : ℚ)) ^ (m - 1)) * Tu (k / p) +
          MvPolynomial.C ((-((k / p : ℕ) : ℚ)) ^ m) * Tv (k / p))) := by
  have hp0 := p_ne_zero' (p := p)
  have hnl := node_lead (p := p) n k h8 h3 hk hl u hu m R hR
  have hren := GV.subst hnl (fun i : Fin 3 => (MvPolynomial.X (Sum.inl i) : MPT)) (fun i => GV.var _)
  set s := k % p with hs
  set l := k / p with hlk
  set σ := sig n p s with hσ
  have hkl : k = p * l + s := (Nat.div_add_mod k p).symm
  have hkp : l < p := by
    rw [hlk, Nat.div_lt_iff_lt_mul hp.out.pos]; simpa [pow_two] using (show k < p ^ 2 by omega)
  have hkq : (k : ℚ) = p * l + s := by exact_mod_cast hkl
  set F : ℚ[X] := (Polynomial.X + Polynomial.C (s : ℚ)) ^ m * R with hF
  have hFe : F.eval (-(k : ℚ)) = (-((l : ℚ) * p)) ^ m * R.eval (-(k : ℚ)) := by
    rw [hF, Polynomial.eval_mul, Polynomial.eval_pow]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    congr 2; rw [hkq]; ring
  have hFd : F.derivative.eval (-(k : ℚ)) = (m : ℚ) * (-((l : ℚ) * p)) ^ (m - 1) * R.eval (-(k : ℚ)) +
      (-((l : ℚ) * p)) ^ m * (Polynomial.derivative R).eval (-(k : ℚ)) := by
    rw [hF, Polynomial.derivative_mul, Polynomial.derivative_pow]
    simp only [Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C, add_zero,
      mul_one, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_natCast]
    have : -(k : ℚ) + s = -((l : ℚ) * p) := by rw [hkq]; ring
    rw [this]
  have hρ' : (Polynomial.derivative R).eval (-(k : ℚ)) ∈ LocRing p :=
    hR.derivative.eval_mem ((LocRing p).neg_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (k : ℤ)))
  obtain ⟨e1, he1, hRk⟩ : ∃ e1 ∈ LocRing p, R.eval (-(k : ℚ)) = R.eval (-(s : ℚ)) + (p : ℚ) * e1 := by
    have := hR.eval_sub (-(k : ℤ)) (-(s : ℤ)) (by
      have : (-(k : ℤ)) - (-(s : ℤ)) = -((p : ℤ) * l) := by omega
      rw [this]; exact (dvd_neg.2 (dvd_mul_right _ _)))
    refine ⟨_, this, ?_⟩
    push_cast at this ⊢
    field_simp
    ring
  have hρ : R.eval (-(s : ℚ)) ∈ LocRing p :=
    hR.eval_mem ((LocRing p).neg_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (s : ℤ)))
  set ρ := R.eval (-(s : ℚ)) with hρdef
  set ρ' := (Polynomial.derivative R).eval (-(k : ℚ)) with hρ'def
  have huq : (u : ℚ) ∈ LocRing p := natq_mem u
  have hlq : (l : ℚ) ∈ LocRing p := natq_mem l
  have huL := uL_mem (p := p) l hkp
  have hvL := vL_mem (p := p) n k l h8 hk hkp
  set A := F.derivative.eval (-(k : ℚ)) with hA
  set B := F.eval (-(k : ℚ)) with hB
  set c1 : ℚ := (m : ℚ) * (-(l : ℚ)) ^ (m - 1) with hc1
  set c2 : ℚ := (-(l : ℚ)) ^ m with hc2
  set yA : ℚ := c1 * R.eval (-(k : ℚ)) + (p : ℚ) * c2 * ρ' with hyA
  set yB : ℚ := c2 * R.eval (-(k : ℚ)) with hyB
  have hAy : (p : ℚ) * A = (p : ℚ) ^ m * yA := by
    rw [hFd, hyA, hc1, hc2]
    rcases m with _ | m
    · simp
    · simp only [Nat.add_sub_cancel]; rw [neg_mul_eq_neg_mul]; ring
  have hBy : B = (p : ℚ) ^ m * yB := by
    rw [hFe, hyB, hc2]; ring
  -- the polynomial identity
  set Cd : ℚ := (p : ℚ) ^ σ * (p : ℚ) ^ m * ((p : ℚ) ^ 4)⁻¹ with hCd
  have hlead : leadF m l (uL l) (vL n p k l) = c1 * uL l + c2 * vL n p k l := by
    unfold leadF; rw [hc1, hc2]
  have hren' : GV p ((σ : ℤ) - 3 + m)
      (ren (laiNd n k F) - MvPolynomial.C (Cd * u * ρ * (c1 * uL l + c2 * vL n p k l)) * bT) := by
    have := hren
    rw [map_sub, map_mul, MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_X_right, hlead] at this
    exact this
  -- the three coefficients
  set a1 : ℚ := (p : ℚ) ^ ((σ : ℤ) - 3) * cl * A - Cd * cl * ρ * c1 with ha1
  set a2 : ℚ := (p : ℚ) ^ ((σ : ℤ) - 4) * cl * B - Cd * cl * ρ * c2 with ha2
  set a0 : ℚ := Cd * u * ρ * (c1 * uL l + c2 * vL n p k l) -
      (p : ℚ) ^ ((σ : ℤ) - 3) * cl * ((κ : ℚ) * uL l) * A -
      (p : ℚ) ^ ((σ : ℤ) - 4) * cl * ((κ : ℚ) * vL n p k l) * B with ha0
  have hid : ren (laiNd n k F) +
        modNd p (σ : ℤ) (cl : ℚ) ((κ : ℚ) * uL l) ((κ : ℚ) * vL n p k l) l k F -
        MvPolynomial.C (Cd * cl * ρ) * bT *
          (MvPolynomial.C c1 * Tu l + MvPolynomial.C c2 * Tv l) =
      (ren (laiNd n k F) - MvPolynomial.C (Cd * u * ρ * (c1 * uL l + c2 * vL n p k l)) * bT) +
        bT * (MvPolynomial.C a1 * Tu l + MvPolynomial.C a2 * Tv l + MvPolynomial.C a0) := by
    unfold modNd
    rw [ha1, ha2, ha0]
    simp only [map_sub, map_mul, map_add]
    ring
  -- valuations of the coefficients
  have hz3 : (p : ℚ) ^ ((σ : ℤ) - 3) = (p : ℚ) ^ σ * ((p : ℚ) ^ 3)⁻¹ := by
    rw [zpow_sub₀ hp0]; simp [div_eq_mul_inv]
  have hz4 : (p : ℚ) ^ ((σ : ℤ) - 4) = (p : ℚ) ^ σ * ((p : ℚ) ^ 4)⁻¹ := by
    rw [zpow_sub₀ hp0]; simp [div_eq_mul_inv]
  have hze : (p : ℚ) ^ ((σ : ℤ) - 3 + m) = (p : ℚ) ^ σ * (p : ℚ) ^ m * ((p : ℚ) ^ 3)⁻¹ := by
    rw [zpow_add₀ hp0, zpow_sub₀ hp0]; simp [div_eq_mul_inv]; ring
  have hzp1 : (p : ℚ) ^ (-((σ : ℤ) - 3 + m)) * (Cd * p) = 1 := by
    rw [zpow_neg, hze, hCd]
    field_simp
  have hA' : A = (p : ℚ) ^ m * yA / p := by
    rw [eq_div_iff hp0]; linarith [hAy]
  have hRkm : R.eval (-(k : ℚ)) ∈ LocRing p := by
    rw [hRk]; exact (LocRing p).add_mem hρ ((LocRing p).mul_mem lp he1)
  have hn : (-(l : ℚ)) ∈ LocRing p := (LocRing p).neg_mem hlq
  have hc1m : c1 ∈ LocRing p := (LocRing p).mul_mem (natq_mem m) ((LocRing p).pow_mem hn _)
  have hc2m : c2 ∈ LocRing p := (LocRing p).pow_mem hn _
  have hclm : (cl : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) cl
  have hκm : (κ : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) κ
  obtain ⟨w, hw⟩ := hcl
  have hwq : (u : ℚ) - cl * κ = p * w := by
    have := congrArg (fun z : ℤ => (z : ℚ)) hw
    simpa using this
  have hwm : (w : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) w
  have ha1' : a1 = (Cd * p) * (cl * (c1 * e1 + c2 * ρ')) := by
    rw [ha1, hz3, hA', hyA, hRk]; rw [hCd]; field_simp; ring
  have ha2' : a2 = (Cd * p) * (cl * (c2 * e1)) := by
    rw [ha2, hz4, hBy, hyB, hRk]; rw [hCd]; field_simp; ring
  have ha0' : a0 = (Cd * p) * (ρ * w * (c1 * uL l + c2 * vL n p k l) -
      cl * κ * (uL l * (c1 * e1 + c2 * ρ') + vL n p k l * (c2 * e1))) := by
    rw [ha0, hz3, hz4, hA', hBy, hyA, hyB, hRk]
    have hu' : (u : ℚ) = cl * κ + p * w := by linarith
    rw [hu', hCd]; field_simp; ring
  have hy1 : (cl : ℚ) * (c1 * e1 + c2 * ρ') ∈ LocRing p :=
    (LocRing p).mul_mem hclm ((LocRing p).add_mem ((LocRing p).mul_mem hc1m he1) ((LocRing p).mul_mem hc2m hρ'))
  have hy2 : (cl : ℚ) * (c2 * e1) ∈ LocRing p := (LocRing p).mul_mem hclm ((LocRing p).mul_mem hc2m he1)
  have hLm : c1 * uL l + c2 * vL n p k l ∈ LocRing p :=
    (LocRing p).add_mem ((LocRing p).mul_mem hc1m huL) ((LocRing p).mul_mem hc2m hvL)
  have hy0 : ρ * w * (c1 * uL l + c2 * vL n p k l) -
      cl * κ * (uL l * (c1 * e1 + c2 * ρ') + vL n p k l * (c2 * e1)) ∈ LocRing p :=
    (LocRing p).sub_mem ((LocRing p).mul_mem ((LocRing p).mul_mem hρ hwm) hLm)
      ((LocRing p).mul_mem ((LocRing p).mul_mem hclm hκm)
        ((LocRing p).add_mem
          ((LocRing p).mul_mem huL ((LocRing p).add_mem ((LocRing p).mul_mem hc1m he1) ((LocRing p).mul_mem hc2m hρ')))
          ((LocRing p).mul_mem hvL ((LocRing p).mul_mem hc2m he1))))
  have hmem : ∀ y ∈ LocRing p, (p : ℚ) ^ (-((σ : ℤ) - 3 + m)) * ((Cd * p) * y) ∈ LocRing p := by
    intro y hy; rw [← mul_assoc, hzp1, one_mul]; exact hy
  have g1 : GV p ((σ : ℤ) - 3 + m) (MvPolynomial.C a1 * Tu l : MPT) :=
    GV_C_mul_gen a1 (by rw [ha1']; exact hmem _ hy1) _ (GV.var _)
  have g2 : GV p ((σ : ℤ) - 3 + m) (MvPolynomial.C a2 * Tv l : MPT) :=
    GV_C_mul_gen a2 (by rw [ha2']; exact hmem _ hy2) _ (GV.var _)
  have g0 : GV p ((σ : ℤ) - 3 + m) (MvPolynomial.C a0 : MPT) :=
    GV.const (by rw [ha0']; exact hmem _ hy0)
  have gT : GV p ((σ : ℤ) - 3 + m) (bT * (MvPolynomial.C a1 * Tu l + MvPolynomial.C a2 * Tv l + MvPolynomial.C a0) : MPT) := by
    have := (GV.var (p := p) (Sum.inl (1 : Fin 3) : TVar)).mul ((g1.add g2).add g0)
    simpa [bT] using this
  have hfin := hren'.add gT
  rw [← hid] at hfin
  exact hfin


/-- The integer lift `ĉ_s (1 + p E_ℓ(s))` of the `s`-dependent part of the unit coefficient. -/
def clZ (n p ℓ s : ℕ) : ℤ :=
  ((Cs p (r6 n p) (r2 n p) (bflag n p s) (eflag n p s) s *
    (1 + (p : ZMod (p ^ 2)) *
      Es p (q6 n p) (r6 n p) (q2 n p) (r2 n p) (bflag n p s) (eflag n p s) ℓ s)).val : ℤ)

/-- The integer lift of the class constant `Kc(ℓ)` (depends on the class flags `b, ε` and `ℓ` only). -/
def kapZ (n p b ε ℓ : ℕ) : ℤ :=
  ((Kc p (q6 n p) (r6 n p) (q2 n p) (r2 n p) b ε ℓ).val : ℤ)

/-- **Lemma G, unit part:** `c_k = p^σ u` with `u ≡ ĉ_s (1 + pE_ℓ(s)) · κ_ℓ (mod p)` for explicit integer
lifts, the first factor depending on `(ℓ, s)` and the second on the class flags and `ℓ` only. -/
theorem laiCoef_cl_kappa {n : ℕ} (h8 : 8 * n < p ^ 2) (h3 : 3 ≤ p) (k : ℕ) (hk : k ≤ 6 * n) :
    ∃ u : ℕ, laiCoef n k = p ^ sig n p (k % p) * u ∧
      (p : ℤ) ∣ (u : ℤ) - clZ n p (k / p) (k % p) *
        kapZ n p (bflag n p (k % p)) (eflag n p (k % p)) (k / p) := by
  obtain ⟨u, hu, hU⟩ := laiCoef_mod_p2 (p := p) h8 h3 k hk
  refine ⟨u, hu, ?_⟩
  have hcast : ∀ x : ZMod (p ^ 2), ((x.val : ℕ) : ZMod p) =
      ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) x := by
    intro x
    have h := congrArg (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) (ZMod.natCast_zmod_val x)
    rw [map_natCast] at h
    exact h
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  unfold clZ kapZ
  push_cast
  rw [hcast, hcast]
  have h2 := congrArg (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) hU
  rw [map_natCast, map_mul, map_mul] at h2
  rw [h2]
  simp only [map_mul, map_add, map_one]
  ring

/-- `δ` depends on `k` only through `ℓ` and the class flags. -/
lemma laiDelta_digits {n k : ℕ} (hk : k ≤ 6 * n) :
    laiDelta n p k = 5 * Hq 1 (k / p) - 3 * Hq 1 (q2 n p + k / p + eflag n p (k % p)) -
      2 * Hq 1 (q6 n p - k / p - bflag n p (k % p)) := by
  have hpp := hp.out.pos
  obtain ⟨hsd1, hsd2, hsd3⟩ := sub_div_mod p (6 * n) k hpp hk
  obtain ⟨had1, had2⟩ := add_div_mod p k (2 * n) hpp
  have hb : bflag n p (k % p) = if 6 * n % p < k % p then 1 else 0 := rfl
  have he : eflag n p (k % p) = if p - 2 * n % p ≤ k % p then 1 else 0 := rfl
  have d3 : (2 * n + k) / p = q2 n p + k / p + eflag n p (k % p) := by
    rw [add_comm, had1, he]; unfold q2; split_ifs with h1 h2 h2 <;> omega
  have d1 : (6 * n - k) / p = q6 n p - k / p - bflag n p (k % p) := by
    rw [hsd2, hb]; rfl
  unfold laiDelta
  rw [d3, d1]

end G2

end CatalanCore.Lai

end PartG2

section PartDR

namespace CatalanCore.Lai

section DivisorRigidity

/-- **Lemma R, rational-function part (divisor rigidity).**
Let `N : ℤ → ℤ` be the exponent function of a product `∏_x (s + x)^{N(x)}` with `s` in the window
`[W0, W1] ⊂ [0, p)`, supported on `1 - W0 ≤ x` and `x + W1 < p` (so `1 ≤ s + x ≤ p - 1` on the window),
and let `m : ℕ → ℤ` be the multiplicities of a second product `∏_β (s - β)^{m β}` with no root in the
window.  The divisor of `Rat(s) = ∏_x (s+x)^{N x}` at the residue `β` is
`D β = N(-β) + N(p-β)`.  If the divisors of the two shifted ratios agree
(`D (β+1) - D β = m (β+1) - m β`, the factor-by-factor identification of Lemma U), then
`D β = m β` for every residue `β < p`: the function `Rat / Q̂` has translation-invariant divisor on
`𝔽_p`, vanishing on the window, hence zero (the paper's `h = c (s^p - s)^k` with `k = 0`). -/
theorem divisor_rigidity (p : ℕ) (N : ℤ → ℤ) (m : ℕ → ℤ) (W0 W1 : ℕ) (hW : W0 ≤ W1) (hW1 : W1 < p)
    (hsupp : ∀ x : ℤ, N x ≠ 0 → 1 - (W0 : ℤ) ≤ x ∧ x + W1 < p)
    (hmW : ∀ β, W0 ≤ β → β ≤ W1 → m β = 0)
    (hinv : ∀ β : ℕ, β + 1 < p →
      (N (-((β + 1 : ℕ) : ℤ)) + N ((p : ℤ) - ((β + 1 : ℕ) : ℤ))) - (N (-(β : ℤ)) + N ((p : ℤ) - β)) =
        m (β + 1) - m β) :
    ∀ β : ℕ, β < p → N (-(β : ℤ)) + N ((p : ℤ) - β) = m β := by
  set g : ℕ → ℤ := fun β => N (-(β : ℤ)) + N ((p : ℤ) - β) - m β with hg
  have hconst : ∀ β, β < p → g β = g 0 := by
    intro β
    induction β with
    | zero => intro _; rfl
    | succ β ih =>
      intro hb
      have h1 := hinv β hb
      have h2 := ih (by omega)
      simp only [hg] at h2 ⊢
      linarith
  have hW0 : g W0 = 0 := by
    simp only [hg]
    have h1 : N (-(W0 : ℤ)) = 0 := by
      by_contra h
      have := (hsupp _ h).1
      omega
    have h2 : N ((p : ℤ) - W0) = 0 := by
      by_contra h
      have := (hsupp _ h).2
      omega
    rw [h1, h2, hmW W0 le_rfl hW]; simp
  intro β hβ
  have := hconst β hβ
  have h0 := hconst W0 (by omega)
  have : g β = 0 := by rw [hconst β hβ, ← h0, hW0]
  simp only [hg] at this
  linarith

end DivisorRigidity

end CatalanCore.Lai

end PartDR

section PartOP

open Finset

namespace CatalanCore.Lai

section OrthPoly

variable {R : Type*} [CommRing R]

/-- **Scaled orthogonal polynomial (Cramer form of Lemma H's consequence).**
For a linear functional `𝓛` on `R[y]` with moments `c k = 𝓛(y^k)` and `Δ = det (c (i+j))_{i,j<μ}`,
the polynomial `Δ y^μ + ∑_j a_j y^j` is `𝓛`-orthogonal to `y^i`, `i < μ`, with coefficients `a_j`
polynomial in the moments (no division by `Δ`).  When `Δ` is a unit (a Gauss unit in the
`T`-polynomial ring) this is `Δ` times the monic orthogonal polynomial of degree `μ`. -/
theorem orth_poly_scaled (c : ℕ → R) (μ : ℕ) :
    ∃ a : Fin μ → R, ∀ i : Fin μ,
      (Matrix.of fun i j : Fin μ => c ((i : ℕ) + j)).det * c ((i : ℕ) + μ) +
        ∑ j : Fin μ, a j * c ((i : ℕ) + j) = 0 := by
  set H : Matrix (Fin μ) (Fin μ) R := Matrix.of fun i j => c ((i : ℕ) + j) with hH
  set v : Fin μ → R := fun i => c ((i : ℕ) + μ) with hv
  refine ⟨-(H.adjugate.mulVec v), fun i => ?_⟩
  have h1 : H.mulVec (H.adjugate.mulVec v) = H.det • v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 := congrFun h1 i
  have key : ∑ j : Fin μ, (-(H.adjugate.mulVec v)) j * c ((i : ℕ) + j) =
      -(H.mulVec (H.adjugate.mulVec v)) i := by
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hH, Matrix.of_apply]
    ring
  rw [key, h2]
  simp only [Pi.smul_apply, smul_eq_mul, hv, hH]
  ring

end OrthPoly

end CatalanCore.Lai

end PartOP
#print axioms CatalanCore.Lai.orth_poly_scaled
#print axioms CatalanCore.Lai.choose_digits_mod
#print axioms CatalanCore.Lai.laiCoef_mod_p2
#print axioms CatalanCore.Lai.laiCoef_cl_kappa
#print axioms CatalanCore.Lai.sum_window_poly_zero
#print axioms CatalanCore.Lai.second_order_sum
#print axioms CatalanCore.Lai.specT_laiLT
#print axioms CatalanCore.Lai.GV_det_transfer
#print axioms CatalanCore.Lai.node_lead_T
#print axioms CatalanCore.Lai.divisor_rigidity
