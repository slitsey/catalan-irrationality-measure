module
public import CatalanCore.Arith.Hybrid.PrimeDenominator

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
  change ∃ z : ℤ, (primeDenominator (Bnd I r m) (fun p => tropExp I r m p - δ p) : ℚ) * (Fr.fullPoly r m).coeff i = z
  apply primeDenominator_integral
  intro p hp
  by_cases hb : p < Bnd I r m
  · simpa only [if_pos hb] using (hδ p hp.out hb).2
  · simp only [if_neg hb]
    have H := fullPoly_gle I p r m
    rwa [tropExp_eq_zero I r m p hp.out (by omega)] at H

lemma log_DhybD (hδ : DefHyp I r m δ) :
    Real.log (DhybD I r m δ) =
      ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, (tropExp I r m p : ℝ) * Real.log p -
      ∑ p ∈ (Finset.range (Bnd I r m)).filter Nat.Prime, (δ p : ℝ) * Real.log p := by
  exact log_primeDenominator_sub (Bnd I r m) (tropExp I r m) δ
    (fun p hp hb => (hδ p hp hb).1)

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
