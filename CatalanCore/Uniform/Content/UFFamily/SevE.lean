module

public import CatalanCore.Uniform.Content.UFFamily.Empty
public import CatalanCore.Uniform.Content.Shape.Alt

@[expose] public section

/-!
# UF families, sevenths `a = 2`, class `p ≡ 5 (mod 7)`, border before `p` (lane H10)

`q = 7`, `o = 5`, `c = 1/6` (`α = 1/12`), `r = 12 m`, so the border is `[12m, 14m)` and `N = 14 m`.
For `p ≡ 5 (mod 7)` the unique singular index below `p` is `k₀ = (6p + 5)/7` (`7 k₀ - 5 = 6 p`).
When `14 m + 2 ≤ p` and `6p + 5 ≤ 98 m` every border node is `< p` (so every core fiber is EMPTY)
and `12 m < k₀ ≤ 14 m`: the border splits at `k₀` into the types
`L = 0` (before `k₀`) and `L = -7/6` (from `k₀`), and the wedge of the two types is `42 ≠ 0`.

This file: arithmetic of the family and the kill certificates for the nodes `v ≥ k₀` against a
representative `t₀ = r` (a type with `L = 0`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFFamily.SevE

/-- The singular index of the class. -/
def k0 (p : ℕ) : ℕ := (6 * p + 5) / 7

/-- Validity window of the family. -/
structure Valid (r p : ℕ) : Prop where
  hr12 : r % 12 = 0
  hr0 : 0 < r
  hp7 : p % 7 = 5
  hlo : 14 * (r / 12) + 2 ≤ p
  hhi : 6 * p + 5 ≤ 98 * (r / 12)

variable {N : ℕ} {Fr : Frame}

theorem Valid.k0_spec {r p : ℕ} (h : Valid r p) : 7 * k0 p = 6 * p + 5 := by
  have := h.hp7; unfold k0; omega

theorem Valid.k0_lo {r p : ℕ} (h : Valid r p) : r + 2 ≤ k0 p := by
  have := h.hlo; have := h.hr12; have := h.hr0; unfold k0; omega

theorem Valid.k0_hi {r p : ℕ} (h : Valid r p) : k0 p ≤ 14 * (r / 12) := by
  have := h.hhi; unfold k0; omega

theorem cval_lo : ∀ a ≤ 5, Cval 1 7 5 5 0 a = 0 := by
  intro a ha
  interval_cases a <;> decide +kernel

theorem cval_hi : Cval 1 7 5 5 0 6 = -7 / 6 := by decide +kernel

/-- No singular index in `[1, k₀)`. -/
theorem not_sing {T : TwoTermData Fr 7 5} {r p : ℕ} [Fact p.Prime] (h : Valid r p) {k : ℕ} (h1 : 1 ≤ k)
    (h2 : k < k0 p) : ¬ ttSing p 7 5 (k : ℤ) := by
  rw [ttSing_nat T h1]
  have hk := h.k0_spec
  have hp7 := h.hp7
  have hkp : k < p := by have := h.hlo; have := h.k0_hi; omega
  push Not
  refine ⟨Nat.not_dvd_of_pos_of_lt (by omega) hkp, fun hd => ?_⟩
  obtain ⟨j, hj⟩ := hd
  have hj6 : j < 6 := by
    by_contra hc
    push Not at hc
    have : p * 6 ≤ p * j := Nat.mul_le_mul_left p hc
    omega
  interval_cases j <;> omega

theorem noSing {T : TwoTermData Fr 7 5} {r p : ℕ} [Fact p.Prime] (h : Valid r p) (D : PoleData Fr p N)
    (hD : D.singular = ttSing p 7 5) (a Δ : ℕ) (ha : a + Δ < k0 p) : NoSingWin D a Δ := by
  intro k h1 h2
  rw [hD]
  exact not_sing (T := T) h (by omega) (by omega)

theorem intOK_empty (q o r : ℕ) (nrm : ℚ) (u0 : ℤ) (zn : ℕ × ℕ) (Dn : ℤ) :
    IntOK q o r nrm u0 ⟨[], zn⟩ Dn ↔ ((Dn : ℚ) * Lq q o r zn).den = 1 := by
  simp [IntOK, entZ]

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Kill certificate** of a border node `v ≥ k₀` against the representative `t₀ = r`. -/
noncomputable def killE (T : TwoTermData Fr 7 5) {r p N : ℕ} [Fact p.Prime] (h : Valid r p)
    (hNp : N < p * p) (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ 7 * t - 5) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (hN : N = 14 * (r / 12)) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (hcinj : Function.Injective c)
    (hcr : ∀ a, c a < r) (v : ℕ) (hv1 : k0 p ≤ v) (hv2 : v < N) :
    KillCert (twoTermPoleData T hNp.le hsq hnorm hnorm0) hNp c xs ys hc hx hy r v := by
  have hp7 := h.hp7
  have hk := h.k0_spec
  have hlo := h.hlo
  have hlo2 := h.k0_lo
  have hhi := h.hhi
  have hr12 := h.hr12
  have hrp : r < p := by omega
  have hvp : v < p := by omega
  have haJ : (7 * r - 5) / p ≤ 5 := by
    have : (7 * r - 5) / p < 6 := Nat.div_lt_of_lt_mul (by omega)
    omega
  have haK : (7 * v - 5) / p = 6 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hqp : 7 < p := by omega
  refine KillCert.ofTypes T hqp hNp hsq hnorm hnorm0 c xs ys hc hx hy hcinj r v v (by omega)
    (by omega) (shiftData_refl _ c v) 1 ⟨[], (0, (7 * r - 5) / p)⟩ ⟨[], (0, (7 * v - 5) / p)⟩ 6 6
    (fiberList_empty c hcr le_rfl hrp) (fiberList_empty c hcr (by omega) hvp) ?_ ?_ ?_
  · rw [intOK_empty, Lq, hp7, cval_lo _ haJ]; simp
  · rw [intOK_empty, Lq, hp7, haK, cval_hi]
    norm_num
  · change ((crossZ 0 0 6 6 (mkFib 7 5 (p % 7) Fr.norm 1 ⟨[], (0, (7 * r - 5) / p)⟩ 6)
      (mkFib 7 5 (p % 7) Fr.norm 1 ⟨[], (0, (7 * v - 5) / p)⟩ 6) : ℤ) : ZMod p) ≠ 0
    rw [crossZ_empty]
    have hzJ : (mkFib 7 5 (p % 7) Fr.norm 1 ⟨[], (0, (7 * r - 5) / p)⟩ 6).z = 0 := by
      simp [mkFib, entZ, Lq, hp7, cval_lo _ haJ]
    have hzK : (mkFib 7 5 (p % 7) Fr.norm 1 ⟨[], (0, (7 * v - 5) / p)⟩ 6).z = -7 := by
      simp [mkFib, entZ, Lq, hp7, haK, cval_hi]
      norm_num
    rw [hzJ, hzK]
    refine cast_ne_of_not_dvd (c := 6 * (-7) - 0 * 6) ?_
    intro hd
    have h42 : (p : ℤ) ∣ 42 := by
      have : (6 * (-7) - 0 * 6 : ℤ) = -42 := by norm_num
      rw [this] at hd
      exact (dvd_neg).1 hd
    have h42' : p ∣ 42 := Int.natCast_dvd_natCast.1 (by exact_mod_cast h42)
    have : p ≤ 42 := Nat.le_of_dvd (by norm_num) h42'
    interval_cases p <;> omega

end CatalanCore.Uniform.Content.UFFamily.SevE
