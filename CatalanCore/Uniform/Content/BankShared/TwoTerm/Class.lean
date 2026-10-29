import CatalanCore.Uniform.Content.Smith.TwoTerm2
import CatalanCore.Uniform.Content.Shape.Alt
set_option Elab.async false

/-! # Two-term banks: root class, pole index, norm and border (lane C4, gap C3)

A two-term bank is the frame `ψ(z+1) - ψ(z+a/q)` (`TwoTermData Fr q o`, `o = q - a`) on the
alternating geometry `altGeom c` (slope `c = 2α`) at even scales.  Every layer lemma of
`BankShared.TwoTerm` is stated for the pole data `(q, o, j, k)` with `q k = j p + o`.

* `rootClass q a p = a p⁻¹ mod q` and `poleIndex q a p = (j p + o)/q` (**the class map**):
  `rootClass_spec` (`q k = j p + o`, `0 < j < q`, `0 < k < p`), `rootClass_unique` (they are the only
  such pair), `rootClass_of_class` (`j` depends only on the class of `p` modulo any `M` with `q ∣ M`),
  `poleIndex_offset` (the 0-based index `k0 = k - 1` is `(j/q) p - a/q`: offset `-a/q`).
* `norm_good`: a natural norm `nm` is a `p`-unit when `p ∤ nm`.
* `altGeom_border`: `c r - 1 ≤ 2 m < c r + 1` at every even scale.
-/

namespace CatalanCore.Uniform.Content.BankShared.TwoTerm
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.Shape

/-! ### The class map -/

/-- The root class `j = a p⁻¹ mod q` of the member `a` at the prime `p`. -/
def rootClass (q a p : ℕ) : ℕ := ((a : ZMod q) * ((p : ZMod q))⁻¹).val

/-- The root class read from a residue class `c` modulo `M` (`q ∣ M`). -/
def rootClassOf (M q a : ℕ) (c : ZMod M) : ℕ := ((a : ZMod q) * ((ZMod.cast c : ZMod q))⁻¹).val

/-- The (1-based) pole index `k` with `q k = j p + (q - a)`. -/
def poleIndex (q a p : ℕ) : ℕ := (rootClass q a p * p + (q - a)) / q

theorem coprime_of_lt {p q : ℕ} (hp : p.Prime) (hq : 0 < q) (hqp : q < p) : Nat.Coprime p q :=
  Nat.coprime_of_lt_prime (by omega) hqp hp

/-- `j p ≡ a (mod q)` in `ZMod q`. -/
theorem rootClass_mul {q a p : ℕ} (hp : p.Prime) (hq : 0 < q) (hqp : q < p) :
    ((rootClass q a p : ℕ) : ZMod q) * (p : ZMod q) = (a : ZMod q) := by
  haveI : NeZero q := ⟨by omega⟩
  unfold rootClass
  rw [ZMod.natCast_zmod_val, mul_assoc, mul_comm ((p : ZMod q))⁻¹ (p : ZMod q),
    ZMod.coe_mul_inv_eq_one p (coprime_of_lt hp hq hqp), mul_one]

/-- **The class map.**  For `0 < a < q < p`, `p` prime: `q k = j p + (q - a)` with `0 < j < q`,
`0 < k < p`, where `j = rootClass q a p`, `k = poleIndex q a p`. -/
theorem rootClass_spec {q a p : ℕ} (hp : p.Prime) (ha0 : 0 < a) (haq : a < q) (hqp : q < p) :
    q * poleIndex q a p = rootClass q a p * p + (q - a) ∧ 0 < rootClass q a p ∧
      rootClass q a p < q ∧ 0 < poleIndex q a p ∧ poleIndex q a p < p := by
  have hq : 0 < q := by omega
  haveI : NeZero q := ⟨by omega⟩
  have hjq : rootClass q a p < q := ZMod.val_lt _
  have hdvd : q ∣ rootClass q a p * p + (q - a) := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_add, Nat.cast_mul, Nat.cast_sub haq.le,
      ZMod.natCast_self, rootClass_mul hp hq hqp]
    ring
  have hk : q * poleIndex q a p = rootClass q a p * p + (q - a) := Nat.mul_div_cancel' hdvd
  have hj0 : 0 < rootClass q a p := by
    rcases Nat.eq_zero_or_pos (rootClass q a p) with h0 | h0
    · exfalso
      rw [h0, zero_mul, zero_add] at hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    · exact h0
  refine ⟨hk, hj0, hjq, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (poleIndex q a p) with h0 | h0
    · rw [h0, mul_zero] at hk; omega
    · exact h0
  · by_contra hge
    push Not at hge
    have h1 : q * p ≤ q * poleIndex q a p := Nat.mul_le_mul_left q hge
    have h2 : (rootClass q a p + 1) * p ≤ q * p := Nat.mul_le_mul_right p hjq
    rw [add_one_mul] at h2
    omega

/-- **Uniqueness**: `(rootClass, poleIndex)` is the only pair `(j, k)` with `j < q` and
`q k = j p + (q - a)`. -/
theorem rootClass_unique {q a p j k : ℕ} (hp : p.Prime) (ha0 : 0 < a) (haq : a < q) (hqp : q < p)
    (hjq : j < q) (hk : q * k = j * p + (q - a)) : j = rootClass q a p ∧ k = poleIndex q a p := by
  have hq : 0 < q := by omega
  haveI : NeZero q := ⟨by omega⟩
  have hcop := coprime_of_lt hp hq hqp
  have hz : ((j : ℕ) : ZMod q) * (p : ZMod q) = (a : ZMod q) := by
    have h1 : ((q * k : ℕ) : ZMod q) = ((j * p + (q - a) : ℕ) : ZMod q) := by rw [hk]
    rw [Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub haq.le, ZMod.natCast_self] at h1
    linear_combination -h1
  have hjz : ((j : ℕ) : ZMod q) = (a : ZMod q) * ((p : ZMod q))⁻¹ := by
    rw [← hz, mul_assoc, ZMod.coe_mul_inv_eq_one p hcop, mul_one]
  have hjr : j = rootClass q a p := by
    unfold rootClass
    rw [← hjz, ZMod.val_natCast_of_lt hjq]
  refine ⟨hjr, ?_⟩
  unfold poleIndex
  rw [← hjr, ← hk, Nat.mul_div_cancel_left k hq]

/-- The root class depends only on the class of `p` modulo `q`. -/
theorem rootClass_congr {q a p p' : ℕ} (h : (p : ZMod q) = (p' : ZMod q)) :
    rootClass q a p = rootClass q a p' := by
  unfold rootClass; rw [h]

/-- The root class depends only on the class `c` of `p` modulo any `M` with `q ∣ M`. -/
theorem rootClass_of_class {M q a p : ℕ} (hqM : q ∣ M) {c : ZMod M} (hpc : (p : ZMod M) = c) :
    rootClass q a p = rootClassOf M q a c := by
  unfold rootClass rootClassOf
  rw [← hpc, ZMod.cast_natCast hqM]

/-- **The offset of the pole cut.**  With the 0-based index `k0 = k - 1`: `q k0 + a = j p`, i.e.
`k0 = (j/q) p - a/q`, and `0 < k - (j/q) p < 1`. -/
theorem poleIndex_offset {q a p : ℕ} (hp : p.Prime) (ha0 : 0 < a) (haq : a < q) (hqp : q < p) :
    q * (poleIndex q a p - 1) + a = rootClass q a p * p ∧
      ((poleIndex q a p : ℚ) - 1) = (rootClass q a p : ℚ) / q * p - (a : ℚ) / q ∧
      rootClass q a p * p < q * poleIndex q a p ∧ q * poleIndex q a p < rootClass q a p * p + q := by
  obtain ⟨hk, -, -, hk0, -⟩ := rootClass_spec hp ha0 haq hqp
  have hq : 0 < q := by omega
  have e1 : q * (poleIndex q a p - 1) + a = rootClass q a p * p := by
    have : q * (poleIndex q a p - 1) = q * poleIndex q a p - q := Nat.mul_sub_one _ _
    have : q ≤ q * poleIndex q a p := Nat.le_mul_of_pos_right q hk0
    omega
  refine ⟨e1, ?_, by omega, by omega⟩
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have e2 : (q : ℚ) * ((poleIndex q a p : ℚ) - 1) + a = (rootClass q a p : ℚ) * p := by
    have := congrArg (fun x : ℕ => (x : ℚ)) e1
    push_cast [Nat.cast_sub (show 1 ≤ poleIndex q a p by omega)] at this
    linarith
  have e3 : (poleIndex q a p : ℚ) - 1 = ((rootClass q a p : ℚ) * p - a) / q := by
    rw [eq_div_iff hqQ]
    linear_combination e2
  rw [e3]
  ring

/-- The 1-based pole index in the form used by the layer lemmas: `q k = j p + o` with `o = q - a`. -/
theorem poleIndex_eq {q o p : ℕ} (hp : p.Prime) (ho0 : 0 < o) (hoq : o < q) (hqp : q < p) :
    q * poleIndex q (q - o) p = rootClass q (q - o) p * p + o := by
  have h := (rootClass_spec hp (a := q - o) (by omega) (by omega) hqp).1
  rwa [show q - (q - o) = o by omega] at h

/-! ### Norm -/

/-- A natural norm `nm` is a `p`-unit when `p ∤ nm`. -/
theorem norm_good {Fr : Frame} {nm p : ℕ} [Fact p.Prime] (hnorm : Fr.norm = (nm : ℚ))
    (hpn : ¬ p ∣ nm) : Fr.norm ∈ CatalanCore.S p ∧ red p Fr.norm ≠ 0 := by
  rw [hnorm]
  refine ⟨(Good.natCast (ℓ := p) nm).1, ?_⟩
  have h : ((nm : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpn
  simpa [red] using h

/-- `p ∤ q ^ e` for a prime `p > q > 0`. -/
theorem not_dvd_pow_of_lt {p q : ℕ} (hp : p.Prime) (hq : 0 < q) (hqp : q < p) (e : ℕ) :
    ¬ p ∣ q ^ e := by
  intro h
  have := Nat.le_of_dvd hq (hp.dvd_of_dvd_pow h)
  omega

/-- `p ∤ q q` for a prime `p > q > 0` (the norm `q²` of the banks). -/
theorem not_dvd_sq_of_lt {p q : ℕ} (hp : p.Prime) (hq : 0 < q) (hqp : q < p) : ¬ p ∣ q * q := by
  intro h
  rcases hp.dvd_mul.1 h with h1 | h1 <;> exact absurd (Nat.le_of_dvd hq h1) (by omega)

/-! ### Pole regularity -/

/-- `p² ∤ q t - o` for `1 ≤ t < N` once `q N ≤ p²`. -/
theorem not_sq_dvd_of_qN {Fr : Frame} {q o : ℕ} (T : TwoTermData Fr q o) {p N : ℕ}
    (hqN : q * N ≤ p * p) : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o := by
  intro t ht htN hd
  have h0 := T.pos ht
  have h1 := Nat.le_of_dvd h0 hd
  have hq : 0 < q := by have := T.o_lt; omega
  have h2 : q * t < q * N := Nat.mul_lt_mul_of_pos_left htN hq
  rw [pow_two] at h1
  omega

/-! ### Border -/

/-- The border size `m` of `altGeom c` at an even scale: `c r - 1 ≤ 2 m < c r + 1`. -/
theorem altGeom_border (c : ℚ) (hc : 0 < c) {r : ℕ} (hr : r % 2 = 0) :
    c * r - 1 ≤ 2 * ((altGeom c hc).borderSize r : ℚ) ∧
      2 * ((altGeom c hc).borderSize r : ℚ) < c * r + 1 := by
  have hb := altGeom_borderSize c hc hr
  have hcc : ⌈(c * r - 1) / 2⌉₊ ≤ ⌈c * r / 2⌉₊ := Nat.ceil_le_ceil (by linarith)
  rw [min_eq_right hcc] at hb
  rw [hb]
  set x : ℚ := (c * r - 1) / 2 with hx
  have hr0 : (0 : ℚ) ≤ r := Nat.cast_nonneg r
  by_cases h0 : 0 ≤ x
  · have h1 := Nat.le_ceil x
    have h2 := Nat.ceil_lt_add_one h0
    constructor <;> linarith
  · have hz : ⌈x⌉₊ = 0 := Nat.ceil_eq_zero.2 (lt_of_not_ge h0).le
    rw [hz]
    push_cast
    constructor
    · linarith [lt_of_not_ge h0]
    · nlinarith

/-- The border bounds in integers for a slope `c = cn / cd`:
`cn r ≤ cd (2 m) + cd` and `cd (2 m) < cn r + cd`. -/
theorem altGeom_border_nat (c : ℚ) (hc : 0 < c) (cn cd : ℕ) (hcd : 0 < cd)
    (hcq : c = (cn : ℚ) / cd) {r : ℕ} (hr : r % 2 = 0) :
    cn * r ≤ cd * (2 * (altGeom c hc).borderSize r) + cd ∧
      cd * (2 * (altGeom c hc).borderSize r) < cn * r + cd := by
  obtain ⟨h1, h2⟩ := altGeom_border c hc hr
  have hcdQ : (0 : ℚ) < cd := by exact_mod_cast hcd
  have hne : (cd : ℚ) ≠ 0 := hcdQ.ne'
  have e : (cd : ℚ) * c = cn := by rw [hcq, ← mul_div_assoc, mul_div_cancel_left₀ _ hne]
  have k1 : (cd : ℚ) * (c * r - 1) = cn * r - cd := by rw [mul_sub, ← mul_assoc, e, mul_one]
  have k2 : (cd : ℚ) * (c * r + 1) = cn * r + cd := by rw [mul_add, ← mul_assoc, e, mul_one]
  have h1' : (cn : ℚ) * r ≤ cd * (2 * ((altGeom c hc).borderSize r : ℚ)) + cd := by
    have := mul_le_mul_of_nonneg_left h1 hcdQ.le
    rw [k1] at this
    linarith
  have h2' : (cd : ℚ) * (2 * ((altGeom c hc).borderSize r : ℚ)) < cn * r + cd := by
    have := mul_lt_mul_of_pos_left h2 hcdQ
    rw [k2] at this
    exact this
  constructor
  · exact_mod_cast h1'
  · exact_mod_cast h2'

end CatalanCore.Uniform.Content.BankShared.TwoTerm
