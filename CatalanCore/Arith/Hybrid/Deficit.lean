module

public import CatalanCore.Arith.Hybrid.Generic

@[expose] public section

/-!
# Additive per-prime deficits

A *deficit family* is a function `δ : ℕ → ℕ` together with, at every prime `p < 4N + 3`
(`N = r + 2m`), the hypothesis `δ p ≤ tropExp r m p` and
`GLE p (tropExp r m p - δ p) (Fr.fullPoly r m)` ("`v_p(den) ≤ τ_p - δ_p`").
`DhybD δ` is the corresponding denominator and

  `log DhybD δ = ∑_p tropExp · log p - ∑_p δ p · log p`   (`log_DhybD`),

so deficits from different sources add up in the constant.  Lemma E is the instance
`δ p = m` at clean band primes (`LemmaEDef`); a future rank-aware saving is another instance,
and two families with disjoint supports combine by `DefHyp.add`.
-/

open Finset CatalanCore.Basic Classical

namespace CatalanCore.Arith.Hybrid

section Def

variable {Fr : Frame} (r m : ℕ) {δ : ℕ → ℕ}

/-- The hypothesis of a deficit family. -/
def DefHyp (Fr : Frame) (r m : ℕ) (δ : ℕ → ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p < 4 * (r + 2 * m) + 3 →
    δ p ≤ tropExp r m p ∧ ∀ [Fact p.Prime], GLE p (tropExp r m p - δ p) (Fr.fullPoly r m)

/-- The denominator with deficits. -/
noncomputable def DhybD (r m : ℕ) (δ : ℕ → ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (4 * (r + 2 * m) + 3)).filter Nat.Prime, p ^ (tropExp r m p - δ p)

lemma DhybD_pos (r m : ℕ) (δ : ℕ → ℕ) : 0 < DhybD r m δ := by
  unfold DhybD
  exact Finset.prod_pos fun p hp => pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2) _

/-- Integrality of the deficit denominator. -/
theorem DhybD_integral (hF : LamLike Fr) (hδ : DefHyp Fr r m δ) (i : ℕ) :
    ∃ z : ℤ, (DhybD r m δ : ℚ) * (Fr.fullPoly r m).coeff i = z := by
  apply int_of_forall_locRing
  intro p hp
  by_cases hb : p < 4 * (r + 2 * m) + 3
  · have hmem : p ∈ (Finset.range (4 * (r + 2 * m) + 3)).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, hp.out⟩
    have hgle := (hδ p hp.out hb).2 i
    have hD : (DhybD r m δ : ℚ) = (p : ℚ) ^ (tropExp r m p - δ p) *
        ((∏ q ∈ ((Finset.range (4 * (r + 2 * m) + 3)).filter Nat.Prime).erase p,
          q ^ (tropExp r m q - δ q) : ℕ) : ℚ) := by
      unfold DhybD
      rw [← Nat.cast_pow, ← Nat.cast_mul,
        Finset.mul_prod_erase _ (fun q => q ^ (tropExp r m q - δ q)) hmem]
    rw [hD]
    have hR := int_mem_locRing (ℓ := p)
      ((∏ q ∈ ((Finset.range (4 * (r + 2 * m) + 3)).filter Nat.Prime).erase p,
          q ^ (tropExp r m q - δ q) : ℕ) : ℤ)
    have := (LocRing p).mul_mem hgle (by simpa using hR)
    convert this using 1; push_cast; ring
  · have h0 := tropExp_eq_zero r m p hp.out (by omega)
    have hgle := fullPoly_gle hF p r m i
    rw [h0] at hgle
    simp only [pow_zero, one_mul] at hgle
    rw [mul_comm]
    exact (LocRing p).mul_mem hgle (by exact_mod_cast int_mem_locRing (ℓ := p) (DhybD r m δ : ℤ))

lemma log_DhybD (hδ : DefHyp Fr r m δ) :
    Real.log (DhybD r m δ) =
      ∑ p ∈ (Finset.range (4 * (r + 2 * m) + 3)).filter Nat.Prime, (tropExp r m p : ℝ) * Real.log p -
      ∑ p ∈ (Finset.range (4 * (r + 2 * m) + 3)).filter Nat.Prime, (δ p : ℝ) * Real.log p := by
  unfold DhybD
  rw [Nat.cast_prod, Real.log_prod, ← Finset.sum_sub_distrib]
  · apply Finset.sum_congr rfl
    intro p hp
    have hh := hδ p (Finset.mem_filter.mp hp).2 (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_sub hh.1]; ring
  · intro p hp
    have := (Finset.mem_filter.mp hp).2.pos
    positivity

/-- The trivial deficit family. -/
lemma defHyp_zero (hF : LamLike Fr) (r m : ℕ) : DefHyp Fr r m (fun _ => 0) := by
  intro p hp _
  refine ⟨Nat.zero_le _, fun [Fact p.Prime] => ?_⟩
  simpa using fullPoly_gle hF p r m

/-- Deficits at disjoint prime sets add. -/
lemma DefHyp.add {δ₁ δ₂ : ℕ → ℕ} (h1 : DefHyp Fr r m δ₁) (h2 : DefHyp Fr r m δ₂)
    (hdisj : ∀ p, p.Prime → p < 4 * (r + 2 * m) + 3 → δ₁ p = 0 ∨ δ₂ p = 0) :
    DefHyp Fr r m (fun p => δ₁ p + δ₂ p) := by
  intro p hp hb
  rcases hdisj p hp hb with h | h
  · simp only [h, zero_add]; exact h2 p hp hb
  · simp only [h, add_zero]; exact h1 p hp hb

/-! ### Lemma E as a deficit family -/

/-- Clean band primes of DQ/DV (corrected conditions): `p ≡ 3 (4)`, `5r < 8p`, `5p + 1 < 4r`,
`p ≠ 139`; or `p ≡ 1 (4)`, `5r ≤ 7p + 1`, `p < r`. -/
def CleanBand (r p : ℕ) : Prop :=
  (p % 4 = 3 ∧ 5 * r < 8 * p ∧ 5 * p + 1 < 4 * r ∧ p ≠ 139) ∨
  (p % 4 = 1 ∧ 5 * r ≤ 7 * p + 1 ∧ p < r)

/-- **Lemma E (hypothesis form)**: at every clean band prime, in the Gauss valuation,
`v_p(den) ≤ τ_p - m`.  This is DQ Theorems 2.2/3.2 + DN Lemma 2.1, stated for `r`, `m`. -/
def LemmaEHyp (Fr : Frame) (r m : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → CleanBand r p → m ≤ tropExp r m p ∧
    ∀ [Fact p.Prime], GLE p (tropExp r m p - m) (Fr.fullPoly r m)

/-- Lemma E as a deficit family `δ p = m · 1[clean]`. -/
noncomputable def lemmaEDef (r m : ℕ) : ℕ → ℕ := fun p => if CleanBand r p then m else 0

lemma defHyp_lemmaE (hF : LamLike Fr) (hE : LemmaEHyp Fr r m) : DefHyp Fr r m (lemmaEDef r m) := by
  intro p hp hb
  by_cases hc : CleanBand r p
  · have := hE p hp hc
    simp only [lemmaEDef, if_pos hc]
    exact this
  · simp only [lemmaEDef, if_neg hc]
    refine ⟨Nat.zero_le _, fun [Fact p.Prime] => ?_⟩
    simpa using fullPoly_gle hF p r m

end Def

end CatalanCore.Arith.Hybrid
