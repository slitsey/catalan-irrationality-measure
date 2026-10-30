module

public import CatalanCore.Uniform.Content.BankShared.Check.Cond
public import Mathlib.Data.Nat.Log

@[expose] public section
set_option Elab.async false

/-! # Certificates for template pieces and the finite covering criterion (lane C1L; C1/PAPER.md §3)

A **branch** is an expression `τ` of class `𝔈`, a list of validity conditions and a debit.  A certificate for a
piece `(s, t; a + b θ; C)` names a branch of the catalogue, the breakpoints of its profile inside `(s, t)`, a strip
branch at each inexact binding endpoint, and the threshold scale `R`.  `pieceOK` is the conjunction (K0)-(K4):

* (K0) `0 < s < t`, `a + b s ≥ 0`, `a + b t ≥ 0`, `C ≥ 0`;
* (K1) every condition is `≥ 0` at `s` and `t`, and a condition vanishing at an end has nonzero slope;
* (K2) on every subinterval `(u, v]` of the subdivision the profile is affine (`affineOn`) and below the line at
  `u` and at `v`;
* (K3) for each condition vanishing at `s` (`t`) whose endpoint is inexact (Lemma 2), a strip branch whose conditions
  are positive at the endpoint and whose one-sided line there is below the piece line;
* (K4) `R` is at least every threshold, `C ≥ E_b + d_b·depth`, `C ≥` every strip constant and
  `C ≥ K_crude(R) = 2⌈R⌉(3⌊log₂ 14⌈R⌉⌋ + c_Fr)`.

**Theorem B** (`piece_sound`): for one member and one prime, given the branch theorems of the catalogue as a
hypothesis, acceptance gives some `n` with `Good n` and `n ≤ a r + b p + C` for `s r < p ≤ t r`. -/

namespace CatalanCore.Uniform.Content.BankShared.Check

/-- A branch: price expression, validity conditions, debit per deleted node. -/
structure Branch where
  τ : Expr
  conds : List Cond
  debit : ℕ

/-- A template piece with rational data: line `a + b θ` on `(s, t]`, slack `C`. -/
structure QPiece where
  s : ℚ
  t : ℚ
  a : ℚ
  b : ℚ
  C : ℚ

/-- A strip certificate at the left (`left = true`, `e = s`) or right end of a piece. -/
structure Strip where
  left : Bool
  yi : ℕ
  w : ℚ
  V : ℚ

/-- A piece certificate. -/
structure Cert where
  bi : ℕ
  cuts : List ℚ
  strips : List Strip
  R : ℚ

/-- Structural list lookup. -/
def nth {α : Type} : List α → ℕ → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: l, n + 1 => nth l n

theorem nth_mem {α : Type} : ∀ (l : List α) (n : ℕ) {x : α}, nth l n = some x → x ∈ l
  | [], _, _, h => by simp [nth] at h
  | y :: l, 0, x, h => by
    simp only [nth, Option.some.injEq] at h; subst h; exact List.mem_cons_self
  | _ :: l, n + 1, _, h => List.mem_cons_of_mem _ (nth_mem l n h)

/-- `ℓ(x)` of a condition. -/
def Cond.lv (α κ x : ℚ) (c : Cond) : ℚ := c.ell0 α + c.ell1 κ * x

/-- (K2) on one subinterval. -/
def lineOK (α κ a b : ℚ) (τ : Expr) (u v : ℚ) : Bool :=
  match affineOn α κ u v τ with
  | some l => decide (lval l u ≤ a + b * u) && decide (lval l v ≤ a + b * v)
  | none => false

/-- (K2) over the subdivision `u < x₁ < … < t`. -/
def k2 (α κ a b : ℚ) (τ : Expr) : ℚ → List ℚ → ℚ → Bool
  | u, [], t => decide (u < t) && lineOK α κ a b τ u t
  | u, x :: xs, t => decide (u < x) && lineOK α κ a b τ u x && k2 α κ a b τ x xs t

/-- (K1) for one condition. -/
def condK1 (α κ s t : ℚ) (c : Cond) : Bool :=
  decide (0 ≤ c.lv α κ s) && decide (0 ≤ c.lv α κ t) &&
    (decide (c.lv α κ s ≠ 0 ∧ c.lv α κ t ≠ 0) || decide (c.ell1 κ ≠ 0))

/-- (K4) threshold of a non-binding condition. -/
def condRok (q : ℕ) (α κ s t R : ℚ) (c : Cond) : Bool :=
  decide (c.lv α κ s = 0 ∨ c.lv α κ t = 0) ||
    decide ((1 - c.etaLo q) / min (c.lv α κ s) (c.lv α κ t) ≤ R)

/-- A strip is needed at `s` (resp. `t`). -/
def needL (q : ℕ) (α κ s : ℚ) (c : Cond) : Bool := decide (c.lv α κ s = 0) && !c.exactL q
def needR (q : ℕ) (α κ t : ℚ) (c : Cond) : Bool := decide (c.lv α κ t = 0) && !c.exactR q

/-- The one-sided line of a strip branch at `e`. -/
def stripLine (α κ e : ℚ) (left : Bool) (w : ℚ) (τ : Expr) : Option (ℚ × ℚ) :=
  if left then affineOn α κ e (e + w) τ else affineOn α κ (e - w) e τ

/-- (K3)-(K4) for one strip. -/
def stripOK (cat : List Branch) (q : ℕ) (α κ : ℚ) (depth : ℕ) (P : QPiece) (br : Branch) (R e : ℚ)
    (st : Strip) : Bool :=
  match nth cat st.yi with
  | none => false
  | some y =>
    decide (0 < st.w) && (st.left || decide (st.w < e)) &&
    br.conds.all (fun c => decide (c.lv α κ e ≠ 0) || decide ((1 - c.etaLo q) / |c.ell1 κ| ≤ st.V)) &&
    y.conds.all (fun c => decide (0 < c.lv α κ e) && decide (2 * (1 - c.etaLo q) / c.lv α κ e ≤ R) &&
      decide (2 * st.V * |c.ell1 κ| / c.lv α κ e ≤ R)) &&
    decide (st.V / st.w ≤ R) &&
    (match stripLine α κ e st.left st.w y.τ with
     | some l => decide (lval l e ≤ P.a + P.b * e) &&
         decide (y.τ.err (1 - 1 / (q : ℚ)) + y.debit * depth + (|P.b| + |l.2|) * st.V ≤ P.C)
     | none => false)

/-- Halvings: `lgF f n = ⌊log₂ n⌋` for `n < 2^(f+1)` (only the check `14 R < 2^(L+1)` is used). -/
def lgF : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => if n < 2 then 0 else lgF f (n / 2) + 1

/-- `max(⌈R⌉, 2)`. -/
def crudeN (R : ℚ) : ℕ := max R.ceil.toNat 2

/-- (K4) for the crude exponent at the scales `r < R`. -/
def crudeOK (R : ℚ) (cF : ℕ) (C : ℚ) : Bool :=
  decide (14 * crudeN R < 2 ^ (lgF 64 (14 * crudeN R) + 1)) &&
    decide (((2 * crudeN R * (3 * lgF 64 (14 * crudeN R) + cF) : ℕ) : ℚ) ≤ C)

/-- **The piece check (K0)-(K4).** -/
def pieceOK (cat : List Branch) (q : ℕ) (α κ : ℚ) (depth cF Pbad : ℕ) (P : QPiece) (c : Cert) : Bool :=
  match nth cat c.bi with
  | none => false
  | some br =>
    decide (0 < P.s) && decide (P.s < P.t) && decide (0 ≤ P.a + P.b * P.s) &&
    decide (0 ≤ P.a + P.b * P.t) && decide (0 ≤ P.C) &&
    br.conds.all (condK1 α κ P.s P.t) &&
    k2 α κ P.a P.b br.τ P.s c.cuts P.t &&
    decide ((q : ℚ) * (2 + 2 * α) / (P.s * P.s) ≤ c.R) && decide ((Pbad : ℚ) / P.s ≤ c.R) &&
    decide (1 ≤ c.R) &&
    br.conds.all (condRok q α κ P.s P.t c.R) &&
    (!(br.conds.any (needL q α κ P.s)) ||
      c.strips.any (fun st => st.left && stripOK cat q α κ depth P br c.R P.s st)) &&
    (!(br.conds.any (needR q α κ P.t)) ||
      c.strips.any (fun st => !st.left && stripOK cat q α κ depth P br c.R P.t st)) &&
    decide (br.τ.err (1 - 1 / (q : ℚ)) + br.debit * depth ≤ P.C) &&
    crudeOK c.R cF P.C

/-! ### Soundness -/

theorem lineOK_sound {α κ a b u v : ℚ} {τ : Expr} (h : lineOK α κ a b τ u v = true) (hu : 0 < u)
    {θ : ℝ} (h1 : (u : ℝ) < θ) (h2 : θ ≤ v) : prof α κ θ τ ≤ a + b * θ := by
  unfold lineOK at h
  rcases hl : affineOn α κ u v τ with _ | l <;> simp only [hl, Bool.and_eq_true, decide_eq_true_eq,
    reduceCtorEq, Bool.false_eq_true] at h
  rw [affineOn_sound α κ u v hu τ l hl θ h1 h2]
  have := lval_nonneg (d := (a - l.1, b - l.2)) h1.le h2 (by unfold lval at h ⊢; simp only; linarith [h.1])
    (by unfold lval at h ⊢; simp only; linarith [h.2])
  push_cast at this
  linarith

theorem k2_sound (α κ a b : ℚ) (τ : Expr) :
    ∀ (cuts : List ℚ) (u t : ℚ), 0 < u → k2 α κ a b τ u cuts t = true →
      ∀ θ : ℝ, (u : ℝ) < θ → θ ≤ t → prof α κ θ τ ≤ a + b * θ
  | [], u, t, hu, h, θ, h1, h2 => by
    simp only [k2, Bool.and_eq_true, decide_eq_true_eq] at h
    exact lineOK_sound h.2 hu h1 h2
  | x :: xs, u, t, hu, h, θ, h1, h2 => by
    simp only [k2, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hux, hl⟩, hr⟩ := h
    by_cases hθ : θ ≤ x
    · exact lineOK_sound hl hu h1 hθ
    · exact k2_sound α κ a b τ xs x t (lt_trans hu hux) hr θ (lt_of_not_ge hθ) h2

theorem lv_real (α κ x : ℚ) (c : Cond) :
    ((c.lv α κ x : ℚ) : ℝ) = (c.ell0 α : ℝ) + (c.ell1 κ : ℝ) * x := by
  unfold Cond.lv; push_cast; ring

theorem log_le_lgF {R : ℚ} (h : 14 * crudeN R < 2 ^ (lgF 64 (14 * crudeN R) + 1)) :
    Nat.log 2 (14 * crudeN R) ≤ lgF 64 (14 * crudeN R) := by
  have := Nat.log_lt_of_lt_pow (by unfold crudeN; omega) h
  omega

/-- The crude exponent at scales `r < R` is at most `K_crude(R)`. -/
theorem crude_le {R : ℚ} {cF r p : ℕ} (hp : 2 ≤ p) (hr : (r : ℚ) < R)
    (h : 14 * crudeN R < 2 ^ (lgF 64 (14 * crudeN R) + 1)) :
    2 * r * (3 * Nat.log p (14 * r) + cF) ≤ 2 * crudeN R * (3 * lgF 64 (14 * crudeN R) + cF) := by
  have hrN : r ≤ crudeN R := by
    have h1 : ((r : ℤ) : ℚ) < R := by exact_mod_cast hr
    have h2 : (r : ℤ) < R.ceil := Rat.lt_ceil_iff.2 h1
    unfold crudeN; omega
  have h1 : Nat.log p (14 * r) ≤ Nat.log 2 (14 * r) := Nat.log_anti_left (by norm_num) hp
  have h2 : Nat.log 2 (14 * r) ≤ Nat.log 2 (14 * crudeN R) := Nat.log_mono_right (by omega)
  have h3 := log_le_lgF h
  have h4 : 3 * Nat.log p (14 * r) + cF ≤ 3 * lgF 64 (14 * crudeN R) + cF := by omega
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 2 hrN) h4

/-- A line nonnegative at `s` and `t` is nonnegative at `p` with `s r < p ≤ t r` (scaled by `r`). -/
theorem line_nonneg_scaled {a b s t : ℚ} {r p : ℝ} (hr : 0 < r) (hs : (s : ℝ) * r < p) (ht : p ≤ t * r)
    (h0 : 0 ≤ a + b * s) (h1 : 0 ≤ a + b * t) : 0 ≤ (a : ℝ) * r + b * p := by
  have h0' : (0 : ℝ) ≤ a + b * s := by exact_mod_cast h0
  have h1' : (0 : ℝ) ≤ a + b * t := by exact_mod_cast h1
  rcases le_total 0 (b : ℝ) with hb | hb
  · nlinarith
  · nlinarith

/-- The value of a condition at `(r, p)` is at least `r · min(ℓ(s), ℓ(t))` on `s r ≤ p ≤ t r`. -/
theorem lin_ge_min (α κ s t : ℚ) (c : Cond) {r p : ℝ} (hr : 0 < r) (hs : (s : ℝ) * r ≤ p)
    (ht : p ≤ t * r) :
    r * (min (c.lv α κ s) (c.lv α κ t) : ℚ) ≤ (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p := by
  push_cast
  rw [lv_real, lv_real]
  rcases le_total 0 (c.ell1 κ : ℝ) with hb | hb
  · have : r * min ((c.ell0 α : ℝ) + c.ell1 κ * s) ((c.ell0 α : ℝ) + c.ell1 κ * t) ≤
        r * ((c.ell0 α : ℝ) + c.ell1 κ * s) := mul_le_mul_of_nonneg_left (min_le_left _ _) hr.le
    nlinarith
  · have : r * min ((c.ell0 α : ℝ) + c.ell1 κ * s) ((c.ell0 α : ℝ) + c.ell1 κ * t) ≤
        r * ((c.ell0 α : ℝ) + c.ell1 κ * t) := mul_le_mul_of_nonneg_left (min_le_right _ _) hr.le
    nlinarith

section Sound

variable {cat : List Branch} {q : ℕ} {α κ : ℚ} {depth cF Pbad : ℕ}

/-- The branch hypothesis of Theorem B at one member and one prime. -/
def BranchesValid (cat : List Branch) (Pbad q r p m k del : ℕ) (Good : ℕ → Prop) : Prop :=
  ∀ b ∈ cat, Pbad < p → q * (r + 2 * m) < p * p →
    (∀ c ∈ b.conds, c.Holds r p m k) → ∃ n, Good n ∧ n ≤ b.τ.evalN r p m k + b.debit * del

/-- The integer price of a branch is below `r` times its profile plus `E + d·depth`. -/
theorem branch_bound {b : Branch} {r p m k del : ℕ} (hq : 1 ≤ q) (hr : 0 < r) (hp : 0 < p)
    (hrd : Cond.Round q r p m k α κ) (hdel : del ≤ depth) {n : ℕ}
    (hn : n ≤ b.τ.evalN r p m k + b.debit * del) :
    (n : ℝ) ≤ r * prof α κ ((p : ℝ) / r) b.τ + ((b.τ.err (1 - 1 / (q : ℚ)) + b.debit * depth : ℚ) : ℝ) := by
  have hm : |(m : ℝ) - α * r| ≤ 1 / 2 := abs_le.2 ⟨by linarith [hrd.m_lo], by linarith [hrd.m_hi]⟩
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
  have hk : |(k : ℝ) - κ * p| ≤ ((1 - 1 / (q : ℚ) : ℚ) : ℝ) := by
    push_cast
    exact abs_le.2 ⟨by linarith [hrd.k_lo], hrd.k_hi⟩
  have h1 := evalN_le_prof (1 - 1 / (q : ℚ)) α κ hr hp hm hk b.τ
  have h2 : (n : ℝ) ≤ (b.τ.evalN r p m k : ℝ) + b.debit * del := by exact_mod_cast hn
  have h3 : (b.debit : ℝ) * del ≤ b.debit * depth := by
    have : (del : ℝ) ≤ depth := by exact_mod_cast hdel
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  push_cast
  linarith

set_option maxHeartbeats 1000000 in
/-- **Theorem B** (one member, one prime). -/
theorem piece_sound (P : QPiece) (cert : Cert) (hok : pieceOK cat q α κ depth cF Pbad P cert = true)
    (hq : 1 ≤ q) (hα : 0 ≤ α) {r p m k del : ℕ} (Good : ℕ → Prop)
    (hrd : Cond.Round q r p m k α κ) (hodd : Pbad < p → p % 2 = 1) (hpge : 2 ≤ p)
    (hdel : del ≤ depth)
    (crude : Good (2 * r * (3 * Nat.log p (14 * r) + cF)))
    (hbr : BranchesValid cat Pbad q r p m k del Good)
    (hs : (P.s : ℝ) * r < p) (ht : (p : ℝ) ≤ P.t * r) :
    ∃ n, Good n ∧ (n : ℝ) ≤ P.a * r + P.b * p + P.C := by
  unfold pieceOK at hok
  rcases hb : nth cat cert.bi with _ | br <;> simp only [hb, reduceCtorEq, Bool.false_eq_true] at hok
  have hbm := nth_mem cat cert.bi hb
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', List.any_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs0, hst⟩, ha0⟩, ha1⟩, hC0⟩, hK1⟩, hK2⟩, hR1⟩, hR2⟩, hR3⟩, hR4⟩, hL⟩, hRt⟩,
    hE⟩, hcr⟩ := hok
  simp only [crudeOK, Bool.and_eq_true, decide_eq_true_eq] at hcr
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hsR : (0 : ℝ) < P.s := by exact_mod_cast hs0
  -- r > 0
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; simp at ht; linarith
    · exact h0
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr0
  have hlin0 := line_nonneg_scaled hrR hs ht ha0 ha1
  by_cases hsmall : (r : ℚ) < cert.R
  · -- small scales: the crude exponent
    refine ⟨_, crude, ?_⟩
    have h1 := crude_le (cF := cF) hpge hsmall hcr.1
    have h2 : ((2 * r * (3 * Nat.log p (14 * r) + cF) : ℕ) : ℝ) ≤
        ((2 * crudeN cert.R * (3 * lgF 64 (14 * crudeN cert.R) + cF) : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : (((2 * crudeN cert.R * (3 * lgF 64 (14 * crudeN cert.R) + cF) : ℕ) : ℚ) : ℝ) ≤ (P.C : ℝ) := by
      exact_mod_cast hcr.2
    push_cast at h2 h3 ⊢
    linarith
  · -- large scales
    have hRr : cert.R ≤ (r : ℚ) := le_of_not_gt hsmall
    have hRr' : (cert.R : ℝ) ≤ r := by exact_mod_cast hRr
    -- frame conditions
    have hPb : Pbad < p := by
      have h1 : ((Pbad : ℚ) / P.s : ℝ) ≤ r := by
        have := (Rat.cast_le (K := ℝ)).2 hR2; push_cast at this ⊢; linarith
      have h2 : (Pbad : ℝ) ≤ P.s * r := by
        push_cast at h1; rw [div_le_iff₀ hsR] at h1; linarith
      have : (Pbad : ℝ) < p := by linarith
      exact_mod_cast this
    have hqN : q * (r + 2 * m) < p * p := by
      have h1 : ((q : ℚ) * (2 + 2 * α) / (P.s * P.s) : ℝ) ≤ r := by
        have := (Rat.cast_le (K := ℝ)).2 hR1; push_cast at this ⊢; linarith
      push_cast at h1
      rw [div_le_iff₀ (mul_pos hsR hsR)] at h1
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr0
      have hα' : (0 : ℝ) ≤ α := by exact_mod_cast hα
      have hm2 : (m : ℝ) < α * r + 1 / 2 := by linarith [hrd.m_hi]
      have e1 : (q : ℝ) * (r + 2 * m) < q * ((1 + 2 * α) * r + 1) :=
        mul_lt_mul_of_pos_left (by linarith) hq0
      have e2 : (q : ℝ) * ((1 + 2 * α) * r + 1) ≤ q * (2 + 2 * α) * r := by
        have := mul_le_mul_of_nonneg_left hr1 hq0.le
        linarith
      have e3 : (q : ℝ) * (2 + 2 * α) * r ≤ (P.s * r) * (P.s * r) := by
        have := mul_le_mul_of_nonneg_right h1 hrR.le
        linarith
      have hsr : (0 : ℝ) ≤ P.s * r := mul_nonneg hsR.le hrR.le
      have e4 : ((P.s : ℝ) * r) * (P.s * r) < p * p := mul_self_lt_mul_self hsr hs
      have : ((q * (r + 2 * m) : ℕ) : ℝ) < ((p * p : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hbv := fun b hb hc => hbr b hb hPb hqN hc
    have hp2 := hodd hPb
    -- the main branch bound, given its conditions
    have main : (∀ c ∈ br.conds, c.Holds r p m k) → ∃ n, Good n ∧ (n : ℝ) ≤ P.a * r + P.b * p + P.C := by
      intro hc
      obtain ⟨n, hn, hnb⟩ := hbv br hbm hc
      refine ⟨n, hn, ?_⟩
      have h1 := branch_bound hq hr0 hp0 hrd hdel hnb (b := br)
      have hθ1 : (P.s : ℝ) < (p : ℝ) / r := by rw [lt_div_iff₀ hrR]; exact hs
      have hθ2 : (p : ℝ) / r ≤ P.t := by rw [div_le_iff₀ hrR]; exact ht
      have h2 := k2_sound α κ P.a P.b br.τ cert.cuts P.s P.t hs0 hK2 ((p : ℝ) / r) hθ1 hθ2
      have h3 : (r : ℝ) * prof α κ ((p : ℝ) / r) br.τ ≤ P.a * r + P.b * p := by
        have := mul_le_mul_of_nonneg_left h2 hrR.le
        have e : (r : ℝ) * ((P.a : ℝ) + P.b * ((p : ℝ) / r)) = P.a * r + P.b * p := by
          field_simp
        linarith
      have h4 : ((br.τ.err (1 - 1 / (q : ℚ)) + br.debit * depth : ℚ) : ℝ) ≤ P.C := by exact_mod_cast hE
      linarith
    -- a strip branch at an end `e` with `|p - e r| ≤ V`
    have strip : ∀ (st : Strip) (e : ℚ), 0 < e → stripOK cat q α κ depth P br cert.R e st = true →
        (st.left = true → (e : ℝ) * r < p ∧ (p : ℝ) ≤ e * r + st.V) →
        (st.left = false → (e : ℝ) * r - st.V < p ∧ (p : ℝ) ≤ e * r) →
        ∃ n, Good n ∧ (n : ℝ) ≤ P.a * r + P.b * p + P.C := by
      intro st e he0 hst hLs hRs
      unfold stripOK at hst
      rcases hy : nth cat st.yi with _ | y <;> simp only [hy, reduceCtorEq, Bool.false_eq_true] at hst
      have hym := nth_mem cat st.yi hy
      rcases hl : stripLine α κ e st.left st.w y.τ with _ | l <;>
        simp only [hl, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
          reduceCtorEq, Bool.false_eq_true, and_false] at hst
      obtain ⟨⟨⟨⟨⟨hw0, hwe⟩, -⟩, hyc⟩, hVw⟩, hle, hCs⟩ := hst
      have hwR : (0 : ℝ) < st.w := by exact_mod_cast hw0
      -- |p - e r| ≤ V and V ≤ w r
      have hVwr : (st.V : ℝ) ≤ st.w * r := by
        have h1 : ((st.V / st.w : ℚ) : ℝ) ≤ r := by
          have := (Rat.cast_le (K := ℝ)).2 hVw; push_cast at this ⊢; linarith
        push_cast at h1; rw [div_le_iff₀ hwR] at h1; linarith
      have hdist : |(p : ℝ) - e * r| ≤ st.V := by
        cases hlft : st.left
        · obtain ⟨h1, h2⟩ := hRs hlft; rw [abs_le]; constructor <;> linarith
        · obtain ⟨h1, h2⟩ := hLs hlft; rw [abs_le]; constructor <;> linarith
      have hV0 : (0 : ℝ) ≤ st.V := le_trans (abs_nonneg _) hdist
      -- conditions of the strip branch
      have hcy : ∀ c ∈ y.conds, c.Holds r p m k := by
        intro c hc
        obtain ⟨⟨hpos, hR5⟩, hR6⟩ := hyc c hc
        have hpos' : (0 : ℝ) < (c.lv α κ e : ℚ) := by exact_mod_cast hpos
        have h5 : ((2 * (1 - c.etaLo q) / c.lv α κ e : ℚ) : ℝ) ≤ r := by
          have := (Rat.cast_le (K := ℝ)).2 hR5; linarith
        have h6 : ((2 * st.V * |c.ell1 κ| / c.lv α κ e : ℚ) : ℝ) ≤ r := by
          have := (Rat.cast_le (K := ℝ)).2 hR6; linarith
        push_cast at h5 h6
        rw [div_le_iff₀ hpos'] at h5 h6
        apply Cond.holds_large c hrd
        have e1 : (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p =
            r * ((c.lv α κ e : ℚ) : ℝ) + (c.ell1 κ : ℝ) * ((p : ℝ) - e * r) := by rw [lv_real]; ring
        have e2 : |(c.ell1 κ : ℝ) * ((p : ℝ) - e * r)| ≤ |(c.ell1 κ : ℝ)| * st.V := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdist (abs_nonneg _)
        rw [e1]
        have e3 := (abs_le.1 e2).1
        linarith
      obtain ⟨n, hn, hnb⟩ := hbv y hym hcy
      refine ⟨n, hn, ?_⟩
      have h1 := branch_bound hq hr0 hp0 hrd hdel hnb (b := y)
      -- the strip line at θ = p / r
      have hθ : prof α κ ((p : ℝ) / r) y.τ = (l.1 : ℝ) + l.2 * ((p : ℝ) / r) := by
        unfold stripLine at hl
        cases hlft : st.left <;> simp only [hlft, if_true, if_false, Bool.false_eq_true] at hl
        · obtain ⟨h1, h2⟩ := hRs hlft
          have hwe' : (st.w : ℝ) < e := by
            simp only [hlft, Bool.false_eq_true, false_or] at hwe; exact_mod_cast hwe
          have hu : (0 : ℚ) < e - st.w := by
            have : (0 : ℝ) < e - st.w := by linarith
            exact_mod_cast this
          refine affineOn_sound α κ (e - st.w) e hu y.τ l hl _ ?_ ?_
          · push_cast; rw [lt_div_iff₀ hrR]; linarith
          · rw [div_le_iff₀ hrR]; exact h2
        · obtain ⟨h1, h2⟩ := hLs hlft
          refine affineOn_sound α κ e (e + st.w) he0 y.τ l hl _ ?_ ?_
          · rw [lt_div_iff₀ hrR]; exact h1
          · push_cast; rw [div_le_iff₀ hrR]; linarith
      have hle' : (l.1 : ℝ) + l.2 * e ≤ P.a + P.b * e := by
        have := (Rat.cast_le (K := ℝ)).2 hle; unfold lval at this; push_cast at this; exact this
      have hCs' : ((y.τ.err (1 - 1 / (q : ℚ)) + y.debit * depth : ℚ) : ℝ) + (|(P.b : ℝ)| + |(l.2 : ℝ)|) * st.V ≤
          P.C := by
        have := (Rat.cast_le (K := ℝ)).2 hCs; push_cast at this ⊢; linarith
      -- r · line(p/r) ≤ a r + b p + (|b| + |l₂|) V
      have hrl : (r : ℝ) * ((l.1 : ℝ) + l.2 * ((p : ℝ) / r)) ≤ P.a * r + P.b * p + (|(P.b : ℝ)| + |(l.2 : ℝ)|) * st.V := by
        have e1 : (r : ℝ) * ((l.1 : ℝ) + l.2 * ((p : ℝ) / r)) = r * ((l.1 : ℝ) + l.2 * e) + l.2 * ((p : ℝ) - e * r) := by
          field_simp; ring
        have e2 : (P.a : ℝ) * r + P.b * p = r * ((P.a : ℝ) + P.b * e) + P.b * ((p : ℝ) - e * r) := by ring
        have e3 : |(l.2 : ℝ) * ((p : ℝ) - e * r)| ≤ |(l.2 : ℝ)| * st.V := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdist (abs_nonneg _)
        have e4 : |(P.b : ℝ) * ((p : ℝ) - e * r)| ≤ |(P.b : ℝ)| * st.V := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdist (abs_nonneg _)
        have e5 : (r : ℝ) * ((l.1 : ℝ) + l.2 * e) ≤ r * ((P.a : ℝ) + P.b * e) :=
          mul_le_mul_of_nonneg_left hle' hrR.le
        rw [e1, e2]
        have := (abs_le.1 e3).2
        have := (abs_le.1 e4).1
        linarith
      rw [hθ] at h1
      linarith
    -- the case analysis on the strips
    by_cases hsl : ∃ st ∈ cert.strips, st.left = true ∧ stripOK cat q α κ depth P br cert.R P.s st = true ∧
        (p : ℝ) ≤ P.s * r + st.V
    · obtain ⟨st, -, hl, hok, hpV⟩ := hsl
      exact strip st P.s hs0 hok (fun _ => ⟨hs, hpV⟩) (fun h => by rw [hl] at h; exact absurd h (by decide))
    by_cases hsr : ∃ st ∈ cert.strips, st.left = false ∧ stripOK cat q α κ depth P br cert.R P.t st = true ∧
        (P.t : ℝ) * r - st.V < p
    · obtain ⟨st, -, hl, hok, hpV⟩ := hsr
      exact strip st P.t (lt_trans hs0 hst) hok (fun h => by rw [hl] at h; exact absurd h (by decide)) (fun _ => ⟨hpV, ht⟩)
    -- off the strips: every condition of the main branch holds
    apply main
    intro c hc
    have hk1 := hK1 c hc
    simp only [condK1, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at hk1
    obtain ⟨⟨hls, hlt⟩, hne⟩ := hk1
    have hlin_s : (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p =
        r * ((c.lv α κ P.s : ℚ) : ℝ) + (c.ell1 κ : ℝ) * ((p : ℝ) - P.s * r) := by rw [lv_real]; ring
    have hlin_t : (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p =
        r * ((c.lv α κ P.t : ℚ) : ℝ) + (c.ell1 κ : ℝ) * ((p : ℝ) - P.t * r) := by rw [lv_real]; ring
    have hst' : (P.s : ℝ) < P.t := by exact_mod_cast hst
    by_cases h0s : c.lv α κ P.s = 0
    · -- binding at s: ℓ₁ > 0
      have hne' : c.ell1 κ ≠ 0 := by
        rcases hne with h | h
        · exact absurd h0s h.1
        · exact h
      have hl1 : (0 : ℝ) < c.ell1 κ := by
        have h1 : (c.lv α κ P.t : ℝ) - (c.lv α κ P.s : ℝ) = (c.ell1 κ : ℝ) * (P.t - P.s) := by
          rw [lv_real, lv_real]; ring
        have h2 : (0 : ℝ) ≤ (c.lv α κ P.t : ℚ) := by exact_mod_cast hlt
        rw [h0s] at h1; push_cast at h1
        have h3 : (0 : ℝ) ≤ (c.ell1 κ : ℝ) * (P.t - P.s) := by linarith
        have h4 : (0 : ℝ) ≤ c.ell1 κ := by
          by_contra hc; push_neg at hc; have := mul_neg_of_neg_of_pos hc (sub_pos.2 hst'); linarith
        have h5 : (c.ell1 κ : ℝ) ≠ 0 := by exact_mod_cast hne'
        exact lt_of_le_of_ne h4 (Ne.symm h5)
      rw [h0s] at hlin_s; push_cast at hlin_s
      have hlin_pos : 0 < (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p := by
        rw [hlin_s]; have : (0 : ℝ) < p - P.s * r := by linarith
        have := mul_pos hl1 this; linarith
      cases hx : c.exactL q
      · -- inexact: off the left strip
        have hneed : ∃ x ∈ br.conds, needL q α κ P.s x = true :=
          ⟨c, hc, by simp [needL, h0s, hx]⟩
        rcases hL with hL | hL
        · exact absurd (List.any_eq_true.2 hneed) (by rw [hL]; decide)
        obtain ⟨st, hstm, hstl, hstok⟩ := hL
        have hoff : P.s * r + st.V < (p : ℝ) := by
          by_contra hcon; push_neg at hcon
          exact hsl ⟨st, hstm, hstl, hstok, hcon⟩
        -- V ≥ (1 - η⁻)/ℓ₁
        have hV : ((1 - c.etaLo q) / |c.ell1 κ| : ℚ) ≤ st.V := by
          unfold stripOK at hstok
          rcases hy : nth cat st.yi with _ | y <;> simp only [hy, reduceCtorEq, Bool.false_eq_true] at hstok
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at hstok
          have := hstok.1.1.1.2 c hc
          rcases this with h | h
          · exact absurd h0s h
          · exact h
        have hV' : (1 - ((c.etaLo q : ℚ) : ℝ)) / (c.ell1 κ : ℝ) ≤ st.V := by
          have := (Rat.cast_le (K := ℝ)).2 hV
          push_cast at this
          rwa [abs_of_pos hl1] at this
        rw [div_le_iff₀ hl1] at hV'
        apply Cond.holds_large c hrd
        rw [hlin_s]
        have := mul_pos hl1 (show (0 : ℝ) < p - P.s * r - st.V by linarith); linarith
      · exact Cond.holds_left c hrd hp2 hx hlin_pos
    by_cases h0t : c.lv α κ P.t = 0
    · -- binding at t: ℓ₁ < 0
      have hne' : c.ell1 κ ≠ 0 := by
        rcases hne with h | h
        · exact absurd h0t h.2
        · exact h
      have hl1 : (c.ell1 κ : ℝ) < 0 := by
        have h1 : (c.lv α κ P.t : ℝ) - (c.lv α κ P.s : ℝ) = (c.ell1 κ : ℝ) * (P.t - P.s) := by
          rw [lv_real, lv_real]; ring
        have h2 : (0 : ℝ) ≤ (c.lv α κ P.s : ℚ) := by exact_mod_cast hls
        rw [h0t] at h1; push_cast at h1
        have h3 : (c.ell1 κ : ℝ) * (P.t - P.s) ≤ 0 := by linarith
        have h4 : (c.ell1 κ : ℝ) ≤ 0 := by
          by_contra hc; push_neg at hc; have := mul_pos hc (sub_pos.2 hst'); linarith
        have h5 : (c.ell1 κ : ℝ) ≠ 0 := by exact_mod_cast hne'
        exact lt_of_le_of_ne h4 h5
      rw [h0t] at hlin_t; push_cast at hlin_t
      have hlin_nn : 0 ≤ (c.ell0 α : ℝ) * r + (c.ell1 κ : ℝ) * p := by
        rw [hlin_t]; have : (p : ℝ) - P.t * r ≤ 0 := by linarith
        have := mul_nonneg (show (0 : ℝ) ≤ -(c.ell1 κ : ℝ) by linarith) (show (0 : ℝ) ≤ -((p : ℝ) - P.t * r) by linarith); linarith
      cases hx : c.exactR q
      · have hneed : ∃ x ∈ br.conds, needR q α κ P.t x = true :=
          ⟨c, hc, by simp [needR, h0t, hx]⟩
        rcases hRt with hRt | hRt
        · exact absurd (List.any_eq_true.2 hneed) (by rw [hRt]; decide)
        obtain ⟨st, hstm, hstl, hstok⟩ := hRt
        have hstl' : st.left = false := by simpa using hstl
        have hoff : (p : ℝ) ≤ P.t * r - st.V := by
          by_contra hcon; push_neg at hcon
          exact hsr ⟨st, hstm, hstl', hstok, hcon⟩
        have hV : ((1 - c.etaLo q) / |c.ell1 κ| : ℚ) ≤ st.V := by
          unfold stripOK at hstok
          rcases hy : nth cat st.yi with _ | y <;> simp only [hy, reduceCtorEq, Bool.false_eq_true] at hstok
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at hstok
          have := hstok.1.1.1.2 c hc
          rcases this with h | h
          · exact absurd h0t h
          · exact h
        have hV' : (1 - ((c.etaLo q : ℚ) : ℝ)) / (-(c.ell1 κ : ℝ)) ≤ st.V := by
          have := (Rat.cast_le (K := ℝ)).2 hV
          push_cast at this
          rwa [abs_of_neg hl1] at this
        rw [div_le_iff₀ (by linarith)] at hV'
        apply Cond.holds_large c hrd
        rw [hlin_t]
        have := mul_nonneg (show (0 : ℝ) ≤ -(c.ell1 κ : ℝ) by linarith) (show (0 : ℝ) ≤ P.t * r - st.V - p by linarith); linarith
      · exact Cond.holds_right c hrd hp2 hx hlin_nn
    -- non-binding
    have hR := hR4 c hc
    simp only [condRok, Bool.or_eq_true, decide_eq_true_eq] at hR
    rcases hR with hR | hR
    · rcases hR with h | h
      · exact absurd h h0s
      · exact absurd h h0t
    have hmin : (0 : ℚ) < min (c.lv α κ P.s) (c.lv α κ P.t) :=
      lt_min (lt_of_le_of_ne hls (Ne.symm h0s)) (lt_of_le_of_ne hlt (Ne.symm h0t))
    have hmin' : (0 : ℝ) < (min (c.lv α κ P.s) (c.lv α κ P.t) : ℚ) := by exact_mod_cast hmin
    have h1 : (((1 - c.etaLo q) / min (c.lv α κ P.s) (c.lv α κ P.t) : ℚ) : ℝ) ≤ r := by
      have := (Rat.cast_le (K := ℝ)).2 hR; linarith
    rw [Rat.cast_div, div_le_iff₀ hmin'] at h1
    have h2 := lin_ge_min α κ P.s P.t c hrR hs.le ht
    rw [Rat.cast_sub, Rat.cast_one] at h1
    apply Cond.holds_large c hrd
    linarith

end Sound

end CatalanCore.Uniform.Content.BankShared.Check
