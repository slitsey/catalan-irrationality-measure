module

public import CatalanCore.Uniform.Bank.Plane2.Zeta3Rows
public import CatalanCore.Uniform.Support.Producer
public import CatalanCore.Uniform.Content.BankShared.Check.Content

@[expose] public section
set_option Elab.async false

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid

/-!
# ζ(3) content side: the direct route (lane H, wave Z2; ledger Z03, Z04)

`Check.Content.altContent_of_bounds` with `M = 1` and ONE template: the prefix `(0, t1]` at the constant
`α0 ≈ 3 (1 + α)`, then a chain of linear pieces `α_P + β_P θ` (`θ = p / r`), no catalogue, no classes.

* `ZP`: a piece with integer data (`s = sn/sd`, `t = tn/td`, `α = A/D`, `β = B/D`, `C = E/D`);
  `zChain`, `zEnd`, `zMass`: the rational chain check, end and mass (kernel `decide`).
* `ZCov`: the covering statement of one piece, over the integer data: for every even scale `r ≥ 10^10`, every
  retained set and every prime `p` with `s r < p`, `p ≤ t r`, some exponent `n` with `GLE p n (member)` and
  `D n ≤ A r + B p + E`.  The wrappers `zc_S`, `zc_B2`, `zc_B4`, `zc_E1`, `zc_P1e0`, `zc_P1e1` prove `ZCov` from the
  sweep rows of `Zeta3Rows` and ONE linear implication over the integers (closed by `omega` in the data modules).
* `zeta3_content_of`: the chain, the piece covers and the mass bound give `HasScaledContent` of the even-scale
  restriction of the Löwner family of the datum.
-/

namespace CatalanCore.Uniform.Bank.Plane2

open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Bank.Halves
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.SmallPrimes

/-! ### Integer pieces and the chain check -/

/-- A piece with integer data: `s = sn/sd`, `t = tn/td`, `α = A/D`, `β = B/D`, `C = E/D`. -/
structure ZP where
  sn : ℕ
  sd : ℕ
  tn : ℕ
  td : ℕ
  D : ℕ
  A : ℤ
  B : ℤ
  E : ℕ

def ZP.s (x : ZP) : ℚ := (x.sn : ℚ) / x.sd
def ZP.t (x : ZP) : ℚ := (x.tn : ℚ) / x.td
def ZP.a (x : ZP) : ℚ := (x.A : ℚ) / x.D
def ZP.b (x : ZP) : ℚ := (x.B : ℚ) / x.D
def ZP.C (x : ZP) : ℚ := (x.E : ℚ) / x.D

/-- The integral of the piece. -/
def ZP.mass (x : ZP) : ℚ := x.a * (x.t - x.s) + x.b * (x.t * x.t - x.s * x.s) / 2

noncomputable def ZP.toPiece (x : ZP) : Piece := ⟨(x.s : ℝ), (x.t : ℝ), (x.a : ℝ), (x.b : ℝ), (x.C : ℝ)⟩

/-- Contiguity and the sign conditions of a chain. -/
def zChain : ℚ → List ZP → Bool
  | _, [] => true
  | s0, x :: l => decide (x.s = s0) && decide (0 < x.s) && decide (x.s ≤ x.t) &&
      decide (0 ≤ x.a + x.b * x.s) && decide (0 ≤ x.a + x.b * x.t) && decide (0 < x.sd) && decide (0 < x.td) &&
      decide (0 < x.D) && zChain x.t l

def zEnd : ℚ → List ZP → ℚ
  | s0, [] => s0
  | _, x :: l => zEnd x.t l

def zMass (l : List ZP) : ℚ := (l.map ZP.mass).sum

theorem zChain_append (s0 : ℚ) (l1 l2 : List ZP) :
    zChain s0 (l1 ++ l2) = (zChain s0 l1 && zChain (zEnd s0 l1) l2) := by
  induction l1 generalizing s0 with
  | nil => simp [zChain, zEnd]
  | cons x l ih =>
    simp only [List.cons_append, zChain, zEnd, ih, Bool.and_assoc]

theorem zEnd_append (s0 : ℚ) (l1 l2 : List ZP) : zEnd s0 (l1 ++ l2) = zEnd (zEnd s0 l1) l2 := by
  induction l1 generalizing s0 with
  | nil => rfl
  | cons x l ih => exact ih _

theorem zMass_append (l1 l2 : List ZP) : zMass (l1 ++ l2) = zMass l1 + zMass l2 := by
  simp [zMass, List.map_append, List.sum_append]

theorem zChain_real : ∀ (l : List ZP) (s0 : ℚ), zChain s0 l = true → Chain (s0 : ℝ) (l.map ZP.toPiece)
  | [], _, _ => trivial
  | x :: l, s0, h => by
    simp only [zChain, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, -⟩, -⟩, -⟩, h6⟩ := h
    have hC : (0 : ℝ) ≤ (x.C : ℝ) := by
      have : (0 : ℚ) ≤ x.C := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      exact_mod_cast this
    refine ⟨?_, ?_, ?_, hC, ?_, ?_, ?_⟩
    · simp [ZP.toPiece, h1]
    · show (0 : ℝ) < (x.s : ℝ); exact_mod_cast h2
    · show (x.s : ℝ) ≤ x.t; exact_mod_cast h3
    · show (0 : ℝ) ≤ (x.a : ℝ) + x.b * x.s; exact_mod_cast h4
    · show (0 : ℝ) ≤ (x.a : ℝ) + x.b * x.t; exact_mod_cast h5
    · exact zChain_real l x.t h6

theorem zEnd_real : ∀ (l : List ZP) (s0 : ℚ),
    lastEnd (s0 : ℝ) (l.map ZP.toPiece) = (zEnd s0 l : ℝ)
  | [], _ => rfl
  | x :: l, _ => by simp only [List.map_cons, lastEnd, zEnd]; exact zEnd_real l x.t

theorem zInt_real : ∀ (l : List ZP), listInt (l.map ZP.toPiece) = ((zMass l : ℚ) : ℝ)
  | [] => by simp [listInt, zMass]
  | x :: l => by
    have ih := zInt_real l
    simp only [List.map_cons, listInt, zMass, List.sum_cons] at ih ⊢
    rw [ih]
    simp only [Piece.int, ZP.toPiece, ZP.mass]
    push_cast; ring

/-! ### The covering statement of a piece -/

/-- The scale threshold of the cover. -/
abbrev ZR0 : ℕ := 10000000000

/-- The integer facts of a point of a piece (the cell and the rounding of `m`). -/
def ZH (sn sd tn td r p m : ℕ) : Prop :=
  sn * r < sd * p ∧ td * p ≤ tn * r ∧ 3 * r ≤ 20 * m + 10 ∧ 20 * m < 3 * r + 10 ∧ ZR0 ≤ r

/-- **The covering statement of one piece.** -/
def ZCov (sn sd tn td D : ℕ) (A B : ℤ) (E : ℕ) : Prop :=
  ∀ (r : ℕ), r % 2 = 0 → ZR0 ≤ r → ∀ (S : Finset (FH.geometry r).C) (p : ℕ) [Fact p.Prime],
    sn * r < sd * p → td * p ≤ tn * r →
    ∃ n : ℕ, GLE p n (zQ r S) ∧ (D : ℤ) * n ≤ A * r + B * p + E

def ZCovP (x : ZP) : Prop := ZCov x.sn x.sd x.tn x.td x.D x.A x.B x.E

def ZAllCov : List ZP → Prop
  | [] => True
  | x :: l => ZCovP x ∧ ZAllCov l

theorem ZAllCov.mem : ∀ {l : List ZP}, ZAllCov l → ∀ x ∈ l, ZCovP x
  | [], _, x, hx => absurd hx (List.not_mem_nil)
  | y :: l, h, x, hx => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact ZAllCov.mem h.2 x hx

theorem ZAllCov.append {l1 l2 : List ZP} (h1 : ZAllCov l1) (h2 : ZAllCov l2) : ZAllCov (l1 ++ l2) := by
  induction l1 with
  | nil => exact h2
  | cons x l ih => exact ⟨h1.1, ih h1.2⟩

/-- The rounding of the border size: `3 r ≤ 20 m + 10` and `20 m < 3 r + 10`. -/
theorem zk_bounds (r : ℕ) (hr : r % 2 = 0) :
    3 * r ≤ 20 * (FH.geometry r).k + 10 ∧ 20 * (FH.geometry r).k < 3 * r + 10 := by
  have h := TwoTerm.altGeom_border (3 / 10) three_tenths_pos hr
  rw [geometry_k_eq_borderSize]
  obtain ⟨h1, h2⟩ := h
  set b := (altGeom (3 / 10) three_tenths_pos).borderSize r with hb
  have h1' : (3 * r : ℚ) ≤ 20 * b + 10 := by linarith
  have h2' : (20 * b : ℚ) < 3 * r + 10 := by linarith
  exact ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩

theorem zr_le {sn sd r p : ℕ} (hsn : 0 < sn) (hsd : sd ≤ 200 * sn) (h : sn * r < sd * p) : r ≤ 200 * p := by
  have h1 : sn * r < sn * (200 * p) := by
    calc sn * r < sd * p := h
      _ ≤ (200 * sn) * p := Nat.mul_le_mul_right p hsd
      _ = sn * (200 * p) := by ring
  exact (Nat.lt_of_mul_lt_mul_left h1).le

theorem zguard {r p m : ℕ} (h200 : r ≤ 200 * p) (hR : ZR0 ≤ r) (hm : 20 * m < 3 * r + 10) :
    5 ≤ p ∧ 2 * (r + 2 * m) + 2 * p < p * p := by
  have hp : 50000000 ≤ p := by unfold ZR0 at hR; omega
  refine ⟨by omega, ?_⟩
  have h1 : 2 * (r + 2 * m) + 2 * p ≤ 602 * p := by unfold ZR0 at hR; omega
  have h2 : 602 * p < p * p := by nlinarith
  omega

/-- The distance of `m` to the multiples of `p` dominates the branch minimum for every integer part `n`. -/
theorem zdist_ge (m p n : ℕ) (hp : 0 < p) :
    min ((m : ℤ) - n * p) (((n : ℤ) + 1) * p - m) ≤ ((min (m % p) (p - m % p) : ℕ) : ℤ) := by
  have hdm : (p : ℤ) * ((m / p : ℕ) : ℤ) + ((m % p : ℕ) : ℤ) = m := by exact_mod_cast Nat.div_add_mod m p
  have hρ : ((m % p : ℕ) : ℤ) < p := by exact_mod_cast Nat.mod_lt m hp
  have hR0 : (0 : ℤ) ≤ ((m % p : ℕ) : ℤ) := Nat.cast_nonneg _
  have hd : ((min (m % p) (p - m % p) : ℕ) : ℤ) = min ((m % p : ℕ) : ℤ) ((p : ℤ) - ((m % p : ℕ) : ℤ)) := by
    rw [Nat.cast_min, Nat.cast_sub (Nat.mod_lt m hp).le]
  rw [hd]
  have hP : (0 : ℤ) < p := by exact_mod_cast hp
  generalize ((m / p : ℕ) : ℤ) = Q at hdm
  generalize ((m % p : ℕ) : ℤ) = R at hdm hρ hR0 ⊢
  generalize (n : ℤ) = N
  rw [← hdm]
  rcases lt_trichotomy Q N with h | h | h
  · have h1 : Q + 1 ≤ N := h
    have : (p : ℤ) * (Q + 1) ≤ p * N := mul_le_mul_of_nonneg_left h1 hP.le
    refine (min_le_left _ _).trans ?_
    refine le_trans ?_ (le_min hR0 (by linarith))
    nlinarith
  · subst h
    refine le_of_eq ?_
    congr 1 <;> ring
  · have h1 : N + 1 ≤ Q := h
    have : (p : ℤ) * (N + 1) ≤ p * Q := mul_le_mul_of_nonneg_left h1 hP.le
    refine (min_le_right _ _).trans ?_
    refine le_trans ?_ (le_min hR0 (by linarith))
    nlinarith

/-! ### Wrappers: one row and one linear implication prove a piece -/

section Wrappers

variable {sn sd tn td D : ℕ} {A B : ℤ} {E : ℕ}

theorem zc_S (hsn : 0 < sn) (hsd : sd ≤ 200 * sn) (n : ℕ)
    (hmain : ∀ r p m d : ℕ, ZH sn sd tn td r p m →
      min ((m : ℤ) - n * p) (((n : ℤ) + 1) * p - m) ≤ d → d ≤ m →
      (D : ℤ) * ((3 * (r + m) - d : ℕ) : ℤ) ≤ A * r + B * p + E) : ZCov sn sd tn td D A B E := by
  intro r hr hR S p _ hc1 hc2
  obtain ⟨hm1, hm2⟩ := zk_bounds r hr
  obtain ⟨hp5, hN⟩ := zguard (zr_le hsn hsd hc1) hR hm2
  have hH : ZH sn sd tn td r p (FH.geometry r).k := ⟨hc1, hc2, hm1, hm2, hR⟩
  refine ⟨_, zrow_B1 hr S rfl hp5 (by omega), hmain r p _ _ hH ?_ ?_⟩
  · exact zdist_ge _ p n (by omega)
  · exact (min_le_left _ _).trans (Nat.mod_le _ _)

theorem zc_B2 (hsn : 0 < sn) (hsd : sd ≤ 200 * sn)
    (hfacts : ∀ r p m : ℕ, ZH sn sd tn td r p m → p ≤ r)
    (hmain : ∀ r p m : ℕ, ZH sn sd tn td r p m → p ≤ r →
      (D : ℤ) * ((6 * (r + m - p) : ℕ) : ℤ) ≤ A * r + B * p + E) : ZCov sn sd tn td D A B E := by
  intro r hr hR S p _ hc1 hc2
  obtain ⟨hm1, hm2⟩ := zk_bounds r hr
  obtain ⟨hp5, hN⟩ := zguard (zr_le hsn hsd hc1) hR hm2
  have hH : ZH sn sd tn td r p (FH.geometry r).k := ⟨hc1, hc2, hm1, hm2, hR⟩
  have hpr := hfacts r p _ hH
  exact ⟨_, zrow_B2 hr S rfl hp5 (by omega) hpr, hmain r p _ hH hpr⟩

theorem zc_B4 (hsn : 0 < sn) (hsd : sd ≤ 200 * sn)
    (hfacts : ∀ r p m : ℕ, ZH sn sd tn td r p m → r ≤ p)
    (hmain : ∀ r p m : ℕ, ZH sn sd tn td r p m → r ≤ p →
      (D : ℤ) * ((3 * (r + 2 * m - p) : ℕ) : ℤ) ≤ A * r + B * p + E) : ZCov sn sd tn td D A B E := by
  intro r hr hR S p _ hc1 hc2
  obtain ⟨hm1, hm2⟩ := zk_bounds r hr
  obtain ⟨hp5, hN⟩ := zguard (zr_le hsn hsd hc1) hR hm2
  have hH : ZH sn sd tn td r p (FH.geometry r).k := ⟨hc1, hc2, hm1, hm2, hR⟩
  have hpr := hfacts r p _ hH
  exact ⟨_, zrow_B4 hr S rfl hp5 (by omega) hpr, hmain r p _ hH hpr⟩

theorem zc_E1 (hsn : 0 < sn) (hsd : sd ≤ 200 * sn) (b U1 V1 U2 V2 : ℕ) (h1 : 2 ≤ U1 + V2) (h2 : 2 ≤ U2 + V1)
    (hfacts : ∀ r p m : ℕ, ZH sn sd tn td r p m → b * p ≤ r ∧ r < b * p + p ∧ 2 * m < p)
    (hmain : ∀ r p m : ℕ, ZH sn sd tn td r p m → b * p ≤ r → r < b * p + p → 2 * m < p →
      (D : ℤ) * ((3 * r + (U1 * min m ((b * p + p - r + 1) / 2) + U2 * (m - min m ((b * p + p - r + 1) / 2))) +
        (V1 * min m ((b * p + p - r) / 2) + V2 * (m - min m ((b * p + p - r) / 2))) : ℕ) : ℤ) ≤
        A * r + B * p + E) : ZCov sn sd tn td D A B E := by
  intro r hr hR S p _ hc1 hc2
  obtain ⟨hm1, hm2⟩ := zk_bounds r hr
  obtain ⟨hp5, hN⟩ := zguard (zr_le hsn hsd hc1) hR hm2
  have hH : ZH sn sd tn td r p (FH.geometry r).k := ⟨hc1, hc2, hm1, hm2, hR⟩
  obtain ⟨hb1, hb2, h2m⟩ := hfacts r p _ hH
  exact ⟨_, zrow_E1 hr S rfl hp5 h2m hN hb1 hb2 U1 V1 U2 V2 h1 h2, hmain r p _ hH hb1 hb2 h2m⟩

theorem zc_P1e0 (hsn : 0 < sn) (hsd : sd ≤ 200 * sn) (b k2 W1 W2 : ℕ) (hk0 : 1 ≤ k2) (hW : 2 ≤ W1 + W2)
    (hfacts : ∀ r p m : ℕ, ZH sn sd tn td r p m →
      b * p ≤ r ∧ r < b * p + p ∧ 2 * (k2 * p) ≤ 2 * m ∧ 2 * m < 2 * (k2 * p) + p)
    (hmain : ∀ r p m : ℕ, ZH sn sd tn td r p m → b * p ≤ r → r < b * p + p →
      2 * (k2 * p) ≤ 2 * m → 2 * m < 2 * (k2 * p) + p →
      (D : ℤ) * ((3 * (r + m) - 3 * (m - k2 * p) +
        (W1 * (min (r + (2 * m - 2 * (k2 * p))) (b * p + p) - r) +
          W2 * (r + (2 * m - 2 * (k2 * p)) - max r (b * p + p))) : ℕ) : ℤ) ≤ A * r + B * p + E) :
    ZCov sn sd tn td D A B E := by
  intro r hr hR S p _ hc1 hc2
  obtain ⟨hm1, hm2⟩ := zk_bounds r hr
  obtain ⟨hp5, hN⟩ := zguard (zr_le hsn hsd hc1) hR hm2
  have hH : ZH sn sd tn td r p (FH.geometry r).k := ⟨hc1, hc2, hm1, hm2, hR⟩
  obtain ⟨hb1, hb2, hk1, hk2⟩ := hfacts r p _ hH
  exact ⟨_, zrow_P1e0 hr S rfl hp5 hN hb1 hb2 hk0 hk1 hk2 W1 W2 hW, hmain r p _ hH hb1 hb2 hk1 hk2⟩

theorem zc_P1e1 (hsn : 0 < sn) (hsd : sd ≤ 200 * sn) (b k2 W1 W2 : ℕ) (hW : 2 ≤ W1 + W2)
    (hfacts : ∀ r p m : ℕ, ZH sn sd tn td r p m →
      b * p ≤ r ∧ r < b * p + p ∧ 2 * (k2 * p) + p ≤ 2 * m ∧ 2 * m < 2 * (k2 * p) + 2 * p)
    (hmain : ∀ r p m : ℕ, ZH sn sd tn td r p m → b * p ≤ r → r < b * p + p →
      2 * (k2 * p) + p ≤ 2 * m → 2 * m < 2 * (k2 * p) + 2 * p →
      (D : ℤ) * ((3 * (r + m) - 3 * (k2 * p + p - m) +
        (W1 * (min (r + p) (b * p + p) - (r + (2 * m - (2 * (k2 * p) + p)))) +
          W2 * (r + p - max (r + (2 * m - (2 * (k2 * p) + p))) (b * p + p)))  : ℕ) : ℤ) ≤
        A * r + B * p + E) : ZCov sn sd tn td D A B E := by
  intro r hr hR S p _ hc1 hc2
  obtain ⟨hm1, hm2⟩ := zk_bounds r hr
  obtain ⟨hp5, hN⟩ := zguard (zr_le hsn hsd hc1) hR hm2
  have hH : ZH sn sd tn td r p (FH.geometry r).k := ⟨hc1, hc2, hm1, hm2, hR⟩
  obtain ⟨hb1, hb2, hk1, hk2⟩ := hfacts r p _ hH
  exact ⟨_, zrow_P1e1 hr S rfl hp5 hN hb1 hb2 hk1 hk2 W1 W2 hW, hmain r p _ hH hb1 hb2 hk1 hk2⟩

end Wrappers

theorem zChain_pos : ∀ (l : List ZP) (s0 : ℚ), zChain s0 l = true →
    ∀ x ∈ l, 0 < x.sd ∧ 0 < x.td ∧ 0 < x.D
  | [], _, _, x, hx => absurd hx List.not_mem_nil
  | y :: l, s0, h, x, hx => by
    simp only [zChain, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨h7, h8, h9⟩
    · exact zChain_pos l y.t h10 x hx

/-! ### From the integer cover to the real cover -/

theorem zcov_real (x : ZP) (hx : ZCovP x) (hsd : 0 < x.sd) (htd : 0 < x.td) (hD : 0 < x.D)
    (r : ℕ) (hr : r % 2 = 0) (hR : ZR0 ≤ r) (S : Finset (FH.geometry r).C) (p : ℕ) [Fact p.Prime]
    (h1 : ⌊(x.s : ℝ) * r⌋₊ < p) (h2 : p ≤ ⌊(x.t : ℝ) * r⌋₊) :
    ∃ n : ℕ, GLE p n (zQ r S) ∧ (n : ℝ) ≤ (x.a : ℝ) * r + (x.b : ℝ) * p + (x.C : ℝ) := by
  have hs0 : (0 : ℝ) ≤ (x.s : ℝ) := by
    have : (0 : ℚ) ≤ x.s := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact_mod_cast this
  have ht0 : (0 : ℝ) ≤ (x.t : ℝ) := by
    have : (0 : ℚ) ≤ x.t := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact_mod_cast this
  have hsdR : (0 : ℝ) < x.sd := by exact_mod_cast hsd
  have htdR : (0 : ℝ) < x.td := by exact_mod_cast htd
  have hDR : (0 : ℝ) < x.D := by exact_mod_cast hD
  have h1' : (x.s : ℝ) * r < p := (Nat.floor_lt (mul_nonneg hs0 (Nat.cast_nonneg _))).1 h1
  have h2' : (p : ℝ) ≤ (x.t : ℝ) * r := (Nat.le_floor_iff (mul_nonneg ht0 (Nat.cast_nonneg _))).1 h2
  have c1 : x.sn * r < x.sd * p := by
    have e : (x.s : ℝ) = (x.sn : ℝ) / x.sd := by simp [ZP.s]
    rw [e, div_mul_eq_mul_div, div_lt_iff₀ hsdR] at h1'
    have : (x.sn : ℝ) * r < x.sd * p := by linarith
    exact_mod_cast this
  have c2 : x.td * p ≤ x.tn * r := by
    have e : (x.t : ℝ) = (x.tn : ℝ) / x.td := by simp [ZP.t]
    rw [e, div_mul_eq_mul_div, le_div_iff₀ htdR] at h2'
    have : (x.td : ℝ) * p ≤ x.tn * r := by linarith
    exact_mod_cast this
  obtain ⟨n, hn, hineq⟩ := hx r hr hR S p c1 c2
  refine ⟨n, hn, ?_⟩
  have key : (x.D : ℝ) * n ≤ x.A * r + x.B * p + x.E := by exact_mod_cast hineq
  have e : (x.a : ℝ) * r + (x.b : ℝ) * p + (x.C : ℝ) = ((x.A : ℝ) * r + x.B * p + x.E) / x.D := by
    simp only [ZP.a, ZP.b, ZP.C]; push_cast; field_simp
  rw [e, le_div_iff₀ hDR]
  linarith

/-! ### Prefix, tail, mass -/

/-- The small-prime budget of the cover. -/
noncomputable def zBudget : SmallBudget := SmallBudget.sqrtLog 3 (30 + 2 * (3 * zeta3Datum.Dc))

theorem zpre (r : ℕ) (hr : r % 2 = 0) (hR : ZR0 ≤ r) (S : Finset (FH.geometry r).C) (p : ℕ) [Fact p.Prime]
    (hpr : p ≤ r) (α0 : ℚ) (hα0 : (69 : ℚ) / 20 + 1 / 10 ^ 9 ≤ α0) :
    ∃ n : ℕ, GLE p n (zQ r S) ∧ (n : ℝ) ≤ (α0 : ℝ) * r + zBudget.X r p := by
  have hQ := datum_altQ zeta3Datum (3 / 10) three_tenths_pos (by norm_num)
  have hα0' : (0 : ℝ) ≤ (α0 : ℝ) := by
    have : (0 : ℚ) ≤ α0 := by linarith
    exact_mod_cast this
  have hR' : (10000000000 : ℝ) ≤ r := by exact_mod_cast hR
  have hp2 := (Fact.out : p.Prime).two_le
  by_cases hsq : p * p ≤ 3 * r
  · refine ⟨Ecrude (3 * zeta3Datum.Dc) r p, hQ.crude ⟨r, S⟩ hr p, ?_⟩
    have h1 := Ecrude_le_budget (3 * zeta3Datum.Dc) (30 + 2 * (3 * zeta3Datum.Dc)) r p le_rfl
      (by unfold ZR0 at hR; omega) hp2
    have h2 : (Ecrude (3 * zeta3Datum.Dc) r p : ℝ) ≤ ((30 + 2 * (3 * zeta3Datum.Dc) : ℕ) : ℝ) * r * ((Nat.log 2 r : ℝ) + 1) := by
      exact_mod_cast h1
    have h3 := SmallBudget.sqrtLog_X_of 3 (30 + 2 * (3 * zeta3Datum.Dc)) r p hsq
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    unfold zBudget
    rw [h3]
    nlinarith [mul_nonneg hα0' hr0]
  · push Not at hsq
    obtain ⟨hm1, hm2⟩ := zk_bounds r hr
    have hp5 : 5 ≤ p := by
      by_contra hc
      push Not at hc
      have : p * p ≤ 16 := by nlinarith
      unfold ZR0 at hR; omega
    refine ⟨3 * (r + (FH.geometry r).k) - min ((FH.geometry r).k % p) (p - (FH.geometry r).k % p),
      zrow_B1 hr S rfl hp5 (by unfold ZR0 at hR; omega), ?_⟩
    have h1 : 3 * (r + (FH.geometry r).k) - min ((FH.geometry r).k % p) (p - (FH.geometry r).k % p) ≤
        3 * (r + (FH.geometry r).k) := Nat.sub_le _ _
    have h2 : ((3 * (r + (FH.geometry r).k) - min ((FH.geometry r).k % p) (p - (FH.geometry r).k % p) : ℕ) : ℝ) ≤
        ((3 * (r + (FH.geometry r).k) : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : (20 : ℝ) * (FH.geometry r).k < 3 * r + 10 := by exact_mod_cast hm2
    have h4 := zBudget.nonneg r p
    have hα : (69 : ℝ) / 20 + 1 / 10 ^ 9 ≤ (α0 : ℝ) := by
      have : (((69 : ℚ) / 20 + 1 / 10 ^ 9 : ℚ) : ℝ) ≤ (α0 : ℝ) := by exact_mod_cast hα0
      simpa using this
    push_cast at h2
    have h5 : ((69 : ℝ) / 20 + 1 / 10 ^ 9) * r ≤ (α0 : ℝ) * r := mul_le_mul_of_nonneg_right hα (Nat.cast_nonneg _)
    linarith

theorem ztail (r : ℕ) (hr : r % 2 = 0) (hR : ZR0 ≤ r) (S : Finset (FH.geometry r).C) (p : ℕ) [Fact p.Prime]
    (hp : ((13 : ℝ) / 10 + 1 / 10 ^ 9) * r < p) : GLE p 0 (zQ r S) := by
  obtain ⟨hm1, hm2⟩ := zk_bounds r hr
  have hR' : (10000000000 : ℝ) ≤ r := by exact_mod_cast hR
  have h1 : (13 : ℝ) / 10 * r + 10 ≤ p := by linarith
  have h2 : 13 * r + 100 ≤ 10 * p := by
    have : (13 : ℝ) * r + 100 ≤ 10 * p := by linarith
    exact_mod_cast this
  have h200 : r ≤ 200 * p := by unfold ZR0 at hR; omega
  obtain ⟨hp5, hN⟩ := zguard h200 hR hm2
  have := zrow_B4 hr S rfl hp5 (by omega) (by omega : r ≤ p)
  have e : 3 * (r + 2 * (FH.geometry r).k - p) = 0 := by omega
  rw [e] at this
  exact this

theorem zcontent_one (T : Template) : contentConstant 1 (fun _ => T) ≤ T.mass := by
  unfold contentConstant
  rw [Finset.sum_const, Nat.totient_one]
  have hc := card_unitClasses_le 1
  have hm := T.mass_nonneg
  simp only [nsmul_eq_mul, Nat.cast_one, div_one]
  have : ((unitClasses 1).card : ℝ) ≤ 1 := by exact_mod_cast hc
  nlinarith

set_option maxHeartbeats 1600000 in
/-- **The content of the ζ(3) family from a chain of certified pieces** (`altContent_of_bounds`, `M = 1`). -/
theorem zeta3_content_alt (depth : ℕ) (L : List ZP) (t1 α0 Lam : ℚ)
    (ht1 : 0 < t1) (ht1le : t1 ≤ 1) (hα0 : (69 : ℚ) / 20 + 1 / 10 ^ 9 ≤ α0)
    (hchain : zChain t1 L = true) (hend : (13 : ℚ) / 10 + 1 / 10 ^ 9 ≤ zEnd t1 L)
    (hcov : ZAllCov L) (hmass : α0 * t1 + zMass L ≤ Lam) :
    HasScaledContent (AltEvenFam (3 / 10) three_tenths_pos zeta3Datum.xi depth
      (SeqFamily.poly zeta3Datum.f zeta3Datum.e (altGeom (3 / 10) three_tenths_pos).geometry))
      (altGeom (3 / 10) three_tenths_pos).scale (Lam : ℝ) := by
  classical
  have hQ := datum_altQ zeta3Datum (3 / 10) three_tenths_pos (by norm_num)
  have hα0R : (0 : ℝ) ≤ (α0 : ℝ) := by
    have : (0 : ℚ) ≤ α0 := by
      have : (0 : ℚ) ≤ 69 / 20 + 1 / 10 ^ 9 := by norm_num
      linarith
    exact_mod_cast this
  have ht1R : (0 : ℝ) < (t1 : ℝ) := by exact_mod_cast ht1
  let T : Template := ⟨(α0 : ℝ), (t1 : ℝ), L.map ZP.toPiece, hα0R, ht1R, zChain_real L t1 hchain⟩
  have hTend : T.tend = (zEnd t1 L : ℝ) := zEnd_real L t1
  have hTmass : T.mass = ((α0 * t1 + zMass L : ℚ) : ℝ) := by
    unfold Template.mass
    show (α0 : ℝ) * (t1 : ℝ) + listInt (L.map ZP.toPiece) = _
    rw [zInt_real]; push_cast; ring
  refine hasScaledContent_lift (AltEvenFam (3 / 10) three_tenths_pos zeta3Datum.xi depth
      (SeqFamily.poly zeta3Datum.f zeta3Datum.e (altGeom (3 / 10) three_tenths_pos).geometry))
    (altGeom (3 / 10) three_tenths_pos).scale (Lam : ℝ) ZR0 (fun i => hQ.deg i) ?_
  refine altContent_of_bounds (3 / 10) three_tenths_pos (3 * zeta3Datum.Dc) zeta3Datum.xi depth ZR0 _ hQ 1
    (Lam : ℝ) zBudget (fun _ _ => T) T.tend ?_ (fun _ _ _ _ => le_rfl) ?_ ?_ ?_
  · intro ε hε
    have h1 := zcontent_one T
    rw [hTmass] at h1
    have h2 : ((α0 * t1 + zMass L : ℚ) : ℝ) ≤ (Lam : ℝ) := by exact_mod_cast hmass
    show contentConstant 1 (fun _ => T) ≤ _
    linarith
  · -- tail
    rintro ε hε ⟨r, S⟩ hi c' hc' p hp hpc hlt _
    have hr : r % 2 = 0 := hi.1.2
    have hR : ZR0 ≤ r := hi.2
    have hlt' : T.tend * r < p := (Nat.floor_lt (mul_nonneg T.tend_pos.le (Nat.cast_nonneg _))).1 hlt
    rw [hTend] at hlt'
    have hend' : (13 : ℝ) / 10 + 1 / 10 ^ 9 ≤ (zEnd t1 L : ℝ) := by
      have : (((13 : ℚ) / 10 + 1 / 10 ^ 9 : ℚ) : ℝ) ≤ (zEnd t1 L : ℝ) := by exact_mod_cast hend
      simpa using this
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_right hend' hr0
    exact ztail r hr hR S p (by linarith)
  · -- prefix
    rintro ε hε ⟨r, S⟩ hi c' hc' p hp1 hp hpc _
    have hr : r % 2 = 0 := hi.1.2
    have hR : ZR0 ≤ r := hi.2
    have hpr : p ≤ r := by
      refine hp1.trans (Nat.floor_le_of_le ?_)
      have : (t1 : ℝ) ≤ 1 := by exact_mod_cast ht1le
      have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
      show (t1 : ℝ) * r ≤ r
      nlinarith
    exact zpre r hr hR S p hpr α0 hα0
  · -- cover
    rintro ε hε ⟨r, S⟩ hi c' hc' P hP p h1 h2 hp hpc _
    have hr : r % 2 = 0 := hi.1.2
    have hR : ZR0 ≤ r := hi.2
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hP
    obtain ⟨hsd, htd, hD⟩ := zChain_pos L t1 hchain x hx
    exact zcov_real x (hcov.mem x hx) hsd htd hD r hr hR S p h1 h2

theorem zeta3_content_of (depth : ℕ) (L : List ZP) (t1 α0 Lam : ℚ)
    (ht1 : 0 < t1) (ht1le : t1 ≤ 1) (hα0 : (69 : ℚ) / 20 + 1 / 10 ^ 9 ≤ α0)
    (hchain : zChain t1 L = true) (hend : (13 : ℚ) / 10 + 1 / 10 ^ 9 ≤ zEnd t1 L)
    (hcov : ZAllCov L) (hmass : α0 * t1 + zMass L ≤ Lam) :
    HasScaledContent ((FH.seqFamily zeta3Datum.f zeta3Datum.e zeta3Datum.xi depth).restrictAdm
      (fun n => SeqFamily.scale FH.geometry n % 2 = 0)) (SeqFamily.scale FH.geometry) (Lam : ℝ) :=
  zeta3_content_alt depth L t1 α0 Lam ht1 ht1le hα0 hchain hend hcov hmass

end CatalanCore.Uniform.Bank.Plane2

#print axioms CatalanCore.Uniform.Bank.Plane2.zeta3_content_of
