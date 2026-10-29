import CatalanCore.Uniform.Content.BankShared.Check.Affine
set_option Elab.async false

/-! # Validity conditions and exact endpoints (lane C1L; C1/PAPER.md §2.2, Lemma 2)

A condition is `L ≥ 0` or `L > 0` with `L = cr r + cp p + cm m + ck k + c1` an integer linear form.  With
`e_m = m - α r ∈ [-1/2, 1/2)` (the rounding of `altGeom`) and `e_k = k - κ p ∈ [1/q, 1 - 1/q]` (the pole
offset `o/q` of every member), `L = ℓ₀ r + ℓ₁ p + η` with `ℓ₀ = cr + cm α`, `ℓ₁ = cp + ck κ` and
`η = cm e_m + ck e_k + c1 ≥ etaLo` (strictly when the lower end is open).

**Lemma 2.**
* `holds_large`: `ℓ₀ r + ℓ₁ p ≥ 1 - etaLo` (off a rounding strip, or away from the zero);
* `holds_left`: an `exactL` condition holds wherever `ℓ₀ r + ℓ₁ p > 0`;
* `holds_right`: an `exactR` condition holds wherever `ℓ₀ r + ℓ₁ p ≥ 0`.
`exactL`/`exactR` are `layers.endpoint_exact` of C1 (sides `+1`/`-1`), with the parity flag computed from the
coefficients (`L` odd for every odd `p`). -/

namespace CatalanCore.Uniform.Content.BankShared.Check

/-- A validity condition `L ≥ 0` (`strict = false`) or `L > 0`. -/
structure Cond where
  cr : ℤ
  cp : ℤ
  cm : ℤ
  ck : ℤ
  c1 : ℤ
  strict : Bool

namespace Cond

/-- The integer form. -/
def L (c : Cond) (r p m k : ℕ) : ℤ := c.cr * r + c.cp * p + c.cm * m + c.ck * k + c.c1

/-- The condition at `(r, p, m, k)`. -/
def Holds (c : Cond) (r p m k : ℕ) : Prop := if c.strict then 0 < c.L r p m k else 0 ≤ c.L r p m k

/-- Homogenisation `ℓ(θ) = ell0 + ell1 θ`. -/
def ell0 (α : ℚ) (c : Cond) : ℚ := c.cr + c.cm * α
def ell1 (κ : ℚ) (c : Cond) : ℚ := c.cp + c.ck * κ

/-- The lower end of `η = cm e_m + ck e_k + c1`. -/
def etaLo (q : ℕ) (c : Cond) : ℚ :=
  c.cm * (if 0 ≤ c.cm then -1 / 2 else 1 / 2) + c.ck * (if 0 ≤ c.ck then 1 / (q : ℚ) else 1 - 1 / (q : ℚ)) +
    c.c1

/-- The lower end is attained (closed) iff `cm ≥ 0` (`e_m < 1/2` is the only open end). -/
def closed (c : Cond) : Bool := decide (0 ≤ c.cm)

/-- `L` is odd for every odd `p`. -/
def odd (c : Cond) : Bool :=
  c.cr % 2 == 0 && c.cm % 2 == 0 && c.ck % 2 == 0 && (c.cp + c.c1) % 2 == 1

/-- Lemma 2 (i): the left endpoint (region `ℓ > 0`, `ℓ` increasing) is exact. -/
def exactL (q : ℕ) (c : Cond) : Bool :=
  if c.strict then decide (0 ≤ c.etaLo q) || (decide (-1 ≤ c.etaLo q) && c.odd)
  else decide (-1 ≤ c.etaLo q)

/-- Lemma 2 (ii): the right endpoint (region `ℓ ≥ 0`, `ℓ` decreasing) is exact. -/
def exactR (q : ℕ) (c : Cond) : Bool :=
  if c.strict then
    (decide (0 < c.etaLo q) || (decide (c.etaLo q = 0) && !c.closed)) ||
      ((decide (-1 < c.etaLo q) || (decide (c.etaLo q = -1) && !c.closed)) && c.odd)
  else decide (-1 < c.etaLo q) || (decide (c.etaLo q = -1) && !c.closed)

/-! ### Soundness -/

theorem L_eq (c : Cond) (α κ : ℚ) (r p m k : ℕ) :
    (c.L r p m k : ℝ) = (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p +
      ((c.cm : ℝ) * ((m : ℝ) - α * r) + (c.ck : ℝ) * ((k : ℝ) - κ * p) + c.c1) := by
  unfold L ell0 ell1; push_cast; ring

theorem etaLo_le (c : Cond) {q : ℕ} {em ek : ℝ} (hm1 : -1 / 2 ≤ em) (hm2 : em < 1 / 2)
    (hk1 : 1 / (q : ℝ) ≤ ek) (hk2 : ek ≤ 1 - 1 / (q : ℝ)) :
    ((c.etaLo q : ℚ) : ℝ) ≤ c.cm * em + c.ck * ek + c.c1 ∧
      (c.closed = false → ((c.etaLo q : ℚ) : ℝ) < c.cm * em + c.ck * ek + c.c1) := by
  unfold etaLo closed
  have hm : (0 : ℤ) ≤ c.cm ∨ c.cm < 0 := le_or_gt 0 c.cm
  have hk : (0 : ℤ) ≤ c.ck ∨ c.ck < 0 := le_or_gt 0 c.ck
  rcases hm with hm | hm <;> rcases hk with hk | hk
  · have hm' : (0 : ℝ) ≤ c.cm := by exact_mod_cast hm
    have hk' : (0 : ℝ) ≤ c.ck := by exact_mod_cast hk
    simp only [hm, hk, if_true, decide_true, reduceCtorEq, false_implies, and_true]
    push_cast
    nlinarith
  · have hm' : (0 : ℝ) ≤ c.cm := by exact_mod_cast hm
    have hk' : (c.ck : ℝ) < 0 := by exact_mod_cast hk
    simp only [hm, not_le.2 hk, if_true, if_false, decide_true, reduceCtorEq, false_implies, and_true]
    push_cast
    nlinarith
  · have hm' : (c.cm : ℝ) < 0 := by exact_mod_cast hm
    have hk' : (0 : ℝ) ≤ c.ck := by exact_mod_cast hk
    simp only [not_le.2 hm, hk, if_true, if_false, decide_false]
    push_cast
    constructor
    · nlinarith
    · intro _; nlinarith
  · have hm' : (c.cm : ℝ) < 0 := by exact_mod_cast hm
    have hk' : (c.ck : ℝ) < 0 := by exact_mod_cast hk
    simp only [not_le.2 hm, not_le.2 hk, if_false, decide_false]
    push_cast
    constructor
    · nlinarith
    · intro _; nlinarith

theorem L_ne_zero_of_odd (c : Cond) {r p m k : ℕ} (ho : c.odd = true) (hp : p % 2 = 1) :
    c.L r p m k ≠ 0 := by
  simp only [odd, Bool.and_eq_true, beq_iff_eq] at ho
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := ho
  obtain ⟨a, ha⟩ : ∃ a, c.cr = 2 * a := ⟨c.cr / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, c.cm = 2 * b := ⟨c.cm / 2, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, c.ck = 2 * d := ⟨c.ck / 2, by omega⟩
  obtain ⟨s, hs⟩ : ∃ s, c.cp + c.c1 = 2 * s + 1 := ⟨(c.cp + c.c1) / 2, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t : ℕ, p = 2 * t + 1 := ⟨p / 2, by omega⟩
  have e : c.L r p m k = 2 * (a * r + c.cp * t + b * m + d * k + s) + 1 := by
    unfold L; rw [ha, hb, hd, ht]; push_cast; linear_combination hs
  omega

section
variable {q r p m k : ℕ} {α κ : ℚ}

/-- The rounding hypotheses of Lemma 2. -/
structure Round (q r p m k : ℕ) (α κ : ℚ) : Prop where
  m_lo : -1 / 2 ≤ (m : ℝ) - α * r
  m_hi : (m : ℝ) - α * r < 1 / 2
  k_lo : 1 / (q : ℝ) ≤ (k : ℝ) - κ * p
  k_hi : (k : ℝ) - κ * p ≤ 1 - 1 / (q : ℝ)

theorem L_ge (c : Cond) (h : Round q r p m k α κ) :
    (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p + ((c.etaLo q : ℚ) : ℝ) ≤ c.L r p m k ∧
      (c.closed = false →
        (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p + ((c.etaLo q : ℚ) : ℝ) < c.L r p m k) := by
  have he := etaLo_le c h.m_lo h.m_hi h.k_lo h.k_hi
  rw [L_eq c α κ]
  exact ⟨by linarith [he.1], fun hc => by linarith [he.2 hc]⟩

/-- **Lemma 2 (iii).** -/
theorem holds_large (c : Cond) (h : Round q r p m k α κ)
    (hl : 1 - ((c.etaLo q : ℚ) : ℝ) ≤ (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p) : c.Holds r p m k := by
  have h1 := (L_ge c h).1
  have h2 : ((1 : ℤ) : ℝ) ≤ (c.L r p m k : ℝ) := by push_cast; linarith
  have h3 : (1 : ℤ) ≤ c.L r p m k := by exact_mod_cast h2
  unfold Holds; split_ifs <;> omega

/-- **Lemma 2 (i).** -/
theorem holds_left (c : Cond) (h : Round q r p m k α κ) (hp : p % 2 = 1) (hx : c.exactL q = true)
    (hl : 0 < (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p) : c.Holds r p m k := by
  have h1 := (L_ge c h).1
  have hne := fun ho => L_ne_zero_of_odd c (r := r) (m := m) (k := k) ho hp
  unfold exactL at hx
  unfold Holds
  cases hs : c.strict
  · simp only [hs, if_false, decide_eq_true_eq, Bool.false_eq_true] at hx ⊢
    have h2 : ((-1 : ℤ) : ℝ) < (c.L r p m k : ℝ) := by
      have : ((-1 : ℚ) : ℝ) ≤ ((c.etaLo q : ℚ) : ℝ) := by exact_mod_cast hx
      push_cast at this ⊢; linarith
    have h3 : (-1 : ℤ) < c.L r p m k := by exact_mod_cast h2
    omega
  · simp only [hs, if_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
    rcases hx with hx | ⟨hx, ho⟩
    · have h2 : ((0 : ℤ) : ℝ) < (c.L r p m k : ℝ) := by
        have : ((0 : ℚ) : ℝ) ≤ ((c.etaLo q : ℚ) : ℝ) := by exact_mod_cast hx
        push_cast at this ⊢; linarith
      exact_mod_cast h2
    · have h2 : ((-1 : ℤ) : ℝ) < (c.L r p m k : ℝ) := by
        have : ((-1 : ℚ) : ℝ) ≤ ((c.etaLo q : ℚ) : ℝ) := by exact_mod_cast hx
        push_cast at this ⊢; linarith
      have h3 : (-1 : ℤ) < c.L r p m k := by exact_mod_cast h2
      have h4 := hne ho
      omega

/-- `η > -1` (resp. `η > 0`) from the `exactR` tests. -/
theorem gt_of_test (c : Cond) (h : Round q r p m k α κ) {x : ℚ} (hl : 0 ≤ (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p)
    (hx : x < c.etaLo q ∨ (c.etaLo q = x ∧ c.closed = false)) : (x : ℝ) < c.L r p m k := by
  have h1 := L_ge c h
  rcases hx with hx | ⟨hx, hc⟩
  · have : (x : ℝ) < ((c.etaLo q : ℚ) : ℝ) := by exact_mod_cast hx
    linarith [h1.1]
  · have := h1.2 hc
    rw [hx] at this
    linarith

/-- **Lemma 2 (ii).** -/
theorem holds_right (c : Cond) (h : Round q r p m k α κ) (hp : p % 2 = 1) (hx : c.exactR q = true)
    (hl : 0 ≤ (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p) : c.Holds r p m k := by
  have hne := fun ho => L_ne_zero_of_odd c (r := r) (m := m) (k := k) ho hp
  unfold exactR at hx
  unfold Holds
  have key : ∀ x : ℤ, ((x : ℚ) < c.etaLo q ∨ (c.etaLo q = (x : ℚ) ∧ c.closed = false)) →
      x < c.L r p m k := by
    intro x hx'
    have := gt_of_test c h hl hx'
    push_cast at this
    exact_mod_cast this
  cases hs : c.strict
  · simp only [hs, Bool.false_eq_true, ite_false, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true'] at hx ⊢
    have := key (-1) (by push_cast; exact hx)
    omega
  · simp only [hs, ite_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      at hx ⊢
    rcases hx with hx | ⟨hx, ho⟩
    · have := key 0 (by push_cast; exact hx)
      exact this
    · have := key (-1) (by push_cast; exact hx)
      have h4 := hne ho
      omega

end

end Cond

end CatalanCore.Uniform.Content.BankShared.Check
