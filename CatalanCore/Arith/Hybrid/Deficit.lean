module

public import CatalanCore.Arith.Hybrid.Majorant

@[expose] public section

/-!
# Additive per-prime deficits

A *deficit family* is a function `δ : ℕ → ℕ` together with, at every prime `p < Bnd`, the
hypothesis `δ p ≤ tropExp p` and `GLE p (tropExp p - δ p) (Fr.fullPoly r m)`
("`v_p(den) ≤ τ_p - δ_p`").  `DhybD δ` is the corresponding denominator and

  `log DhybD δ = ∑_p tropExp · log p - ∑_p δ p · log p`   (`log_DhybD`),

so deficits from different sources add up in the constant.  Lemma E is the instance
`δ p = m` at clean band primes (`lemmaEDef`); a future rank-aware saving is another instance, and
two families with disjoint supports combine by `DefHyp.add`.  The deficit is optional: with
`δ = 0` (`defHyp_zero`) one recovers `Dhyb`.  The notion of clean band prime is a PARAMETER
(`clean : ℕ → Prop`), since it depends on the frame (kernel shape, jump table, low residues).
-/

open Finset CatalanCore.Basic Classical

namespace CatalanCore.Arith.Hybrid

section Def

variable {Fr : Frame} (I : HybInst Fr) (r m : ℕ) {δ : ℕ → ℕ}

/-- The hypothesis of a deficit family. -/
def DefHyp (δ : ℕ → ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p < Bnd I r m →
    δ p ≤ tropExp I r m p ∧ ∀ [Fact p.Prime], GLE p (tropExp I r m p - δ p) (Fr.fullPoly r m)

/-- The denominator with deficits. -/
noncomputable def DhybD (δ : ℕ → ℕ) : ℕ :=
  ∏ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, p ^ (tropExp I r m p - δ p)

lemma DhybD_pos (δ : ℕ → ℕ) : 0 < DhybD I r m δ := by
  unfold DhybD
  exact Finset.prod_pos fun p hp => pow_pos (Nat.Prime.pos (Finset.mem_filter.mp hp).2) _

/-- Integrality of the deficit denominator. -/
theorem DhybD_integral [I.DiagOK r m] (hδ : DefHyp I r m δ) (i : ℕ) :
    ∃ z : ℤ, (DhybD I r m δ : ℚ) * (Fr.fullPoly r m).coeff i = z := by
  apply int_of_forall_locRing
  intro p hp
  by_cases hb : p < Bnd I r m
  · have hmem : p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, hp.out⟩
    have hgle := (hδ p hp.out hb).2 i
    have hD : (DhybD I r m δ : ℚ) = (p : ℚ) ^ (tropExp I r m p - δ p) *
        ((∏ q ∈ ((Finset.range (Bnd I r m)).filter Nat.Prime).erase p,
          q ^ (tropExp I r m q - δ q) : ℕ) : ℚ) := by
      unfold DhybD
      rw [← Nat.cast_pow, ← Nat.cast_mul,
        Finset.mul_prod_erase _ (fun q => q ^ (tropExp I r m q - δ q)) hmem]
    rw [hD]
    have hR := int_mem_locRing (ℓ := p)
      ((∏ q ∈ ((Finset.range (Bnd I r m)).filter Nat.Prime).erase p,
          q ^ (tropExp I r m q - δ q) : ℕ) : ℤ)
    have := (LocRing p).mul_mem hgle (by simpa using hR)
    convert this using 1; push_cast; ring
  · have h0 := tropExp_eq_zero I r m p hp.out (by omega)
    have hgle := fullPoly_gle I p r m i
    rw [h0] at hgle
    simp only [pow_zero, one_mul] at hgle
    rw [mul_comm]
    exact (LocRing p).mul_mem hgle (by exact_mod_cast int_mem_locRing (ℓ := p) (DhybD I r m δ : ℤ))

lemma log_DhybD (hδ : DefHyp I r m δ) :
    Real.log (DhybD I r m δ) =
      ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, (tropExp I r m p : ℝ) * Real.log p -
      ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, (δ p : ℝ) * Real.log p := by
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
lemma defHyp_zero [I.DiagOK r m] : DefHyp I r m (fun _ => 0) := by
  intro p hp _
  refine ⟨Nat.zero_le _, fun [Fact p.Prime] => ?_⟩
  simpa using fullPoly_gle I p r m

/-- Deficits at disjoint prime sets add. -/
lemma DefHyp.add {δ₁ δ₂ : ℕ → ℕ} (h1 : DefHyp I r m δ₁) (h2 : DefHyp I r m δ₂)
    (hdisj : ∀ p, p.Prime → p < Bnd I r m → δ₁ p = 0 ∨ δ₂ p = 0) :
    DefHyp I r m (fun p => δ₁ p + δ₂ p) := by
  intro p hp hb
  rcases hdisj p hp hb with h | h
  · simp only [h, zero_add]; exact h2 p hp hb
  · simp only [h, add_zero]; exact h1 p hp hb

/-! ### A deficit from a set of "clean" primes -/

/-- Deficit `m` at the primes of a set `clean`. -/
noncomputable def cleanDef (clean : ℕ → Prop) : ℕ → ℕ := fun p => if clean p then m else 0

/-- **Lemma E (hypothesis form).**  At every prime of `clean`, in the Gauss valuation,
`v_p(den) ≤ τ_p - m`. -/
def LemmaEHyp (clean : ℕ → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p < Bnd I r m → clean p → m ≤ tropExp I r m p ∧
    ∀ [Fact p.Prime], GLE p (tropExp I r m p - m) (Fr.fullPoly r m)

lemma defHyp_clean [I.DiagOK r m] {clean : ℕ → Prop} (hE : LemmaEHyp I r m clean) :
    DefHyp I r m (cleanDef m clean) := by
  intro p hp hb
  by_cases hc : clean p
  · have := hE p hp hb hc
    simp only [cleanDef, if_pos hc]
    exact this
  · simp only [cleanDef, if_neg hc]
    refine ⟨Nat.zero_le _, fun [Fact p.Prime] => ?_⟩
    simpa using fullPoly_gle I p r m

end Def

end CatalanCore.Arith.Hybrid
