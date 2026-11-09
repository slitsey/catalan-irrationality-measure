module

public import CatalanCore.Uniform.Content.Shape.Irrational
public import CatalanCore.Uniform.Decay.PolyCells.Assemble

@[expose] public section

/-!
# Theorem S: the support theorem (lane H, wave H2c; ledger S05, S07)

`support_measureLB` is Theorem S of `SUPPORT-THEOREM-2026-11-07.md` §2 for an arbitrary `PolyFamily`:
content on the even-scale restriction, decay on the family, `Λ < D`, a degree bound, evenness and
nonvanishing at every large even scale give an irrationality measure `γ c / (D - Λ)` and irrationality
of every `ξ` with `Fam.const = a ξ + b` (`a ≠ 0` rational).  A plane, a row, ζ(3) and a bank are
instances: the family, the content `Λ`, the certificate and the constant relation are data.

`Certificate` (S05) is the decay certificate of a family: a `PolyCellRulesB` record (which both the
cached tables of `PolyWire3.Top`/`TopFold` and the fold of `PolyWire3.Fold` supply), a spline datum
and a rational polygon whose finite check `checkPB` passes, with the exponents `D = spline.Dt` and
`c = spline.ccert` read off as rationals.  Decay of a concrete family from a certificate is the
business of `Decay.AltDecay`/`AltFold` (simple poles) and `Decay.Jet.Decay` (double poles).
-/

namespace CatalanCore.Uniform.Support

open CatalanCore CatalanCore.Measure CatalanCore.Uniform CatalanCore.Uniform.Decay.PolyCells
  CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Polygon

/-- **S05.** The decay certificate of a family: a polygon cell-rule record with a passing finite
check, the exponent `D` and window constant `c` (rational) being those of the spline datum, `0 < c`. -/
structure Certificate (Vnu : ℂ → ℝ) where
  rules : PolyCellRulesB Vnu
  spline : SplineData
  polygon : RatPolygon
  /-- the finite check -/
  ok : checkPB rules spline polygon = true
  /-- the decay exponent -/
  D : ℚ
  /-- the window constant -/
  c : ℚ
  hD : spline.Dt = D
  hc' : spline.ccert = c
  hc : 0 < c

namespace Certificate

variable {Vnu : ℂ → ℝ}

/-- The certificate's exponent, as a real. -/
noncomputable abbrev Dr (C : Certificate Vnu) : ℝ := (C.D : ℝ)

/-- The certificate's window constant, as a real. -/
noncomputable abbrev cr (C : Certificate Vnu) : ℝ := (C.c : ℝ)

/-- A certificate whose check passes gives the polygon checker of D7. -/
theorem checkP (C : Certificate Vnu) : C.spline.checkP C.rules.toRules C.polygon = true :=
  checkP_of_checkPB C.ok

/-- `Λ < D`, the strict gap of the content below the exponent of a certificate. -/
def Below (C : Certificate Vnu) (Λ : ℝ) : Prop := Λ < C.Dr

end Certificate

/-- **S07, Theorem S.**  For any family `Fam` with scale: content `Λ` on its even-scale restriction,
decay `(D, c)` on the family, `Λ < D`, degree at most `γ·scale + K`, even scales, and nonvanishing at
every large even scale, every `ξ` with `Fam.const = a ξ + b`, `a ≠ 0` rational, is irrational and has
irrationality measure at most `γ c / (D - Λ)`.  Taking `a = q`, `b = 0` gives the form `Fam.const = q ξ`. -/
theorem support_measureLB (Fam : PolyFamily) (scale : Fam.ι → ℕ)
    {Λ D c γ K : ℝ}
    (hΛ : HasScaledContent (Fam.restrictAdm (fun n => scale n % 2 = 0)) scale Λ)
    (hD : HasScaledDecay Fam scale D c) (hη : Λ < D) (hc : 0 < c)
    (hγ : 0 < γ) (hK : 0 ≤ K)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ γ * scale n + K)
    (hnv : ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
      ∃ n, Fam.Adm n ∧ scale n = 2 * s ∧ Fam.evalQ n x ≠ 0)
    {ξ : ℝ} {a b : ℚ} (ha : a ≠ 0) (hconst : Fam.const = (a : ℝ) * ξ + b) :
    MeasureLBAt ξ (γ * c / (D - Λ)) ∧ Irrational ξ := by
  set F' := Fam.restrictAdm (fun n => scale n % 2 = 0) with hF'
  have hD' : HasScaledDecay F' scale D c := by
    intro ε hε
    obtain ⟨R0, hR⟩ := hD ε hε
    exact ⟨R0, fun n hn => hR n hn.1⟩
  have hdeg' : ∀ n, F'.Adm n → (F'.deg n : ℝ) ≤ γ * scale n + K := fun n hn => hdeg n hn.1
  have heven' : ∀ n, F'.Adm n → scale n % 2 = 0 := fun n hn => hn.2
  have hnv' : ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
      ∃ n, F'.Adm n ∧ scale n = 2 * s ∧ F'.evalQ n x ≠ 0 := by
    obtain ⟨R0, h⟩ := hnv
    refine ⟨R0, fun s hs x => ?_⟩
    obtain ⟨n, hn, hsc, hne⟩ := h s hs x
    exact ⟨n, ⟨hn, by omega⟩, hsc, hne⟩
  have hm : F'.MeasureLB (γ * c / (D - Λ)) :=
    measure_of_family_nv0_even F' scale hΛ hD' hη hc hγ hK hdeg' heven' hnv'
  have hirr : Irrational F'.const :=
    irrational_of_family_nv0_even F' scale hΛ hD' hη hc hγ hK hdeg' heven' hnv'
  have hE : 0 ≤ γ * c / (D - Λ) := by
    have : 0 < D - Λ := sub_pos.2 hη
    positivity
  have hmeas : MeasureLBAt (F'.const) (γ * c / (D - Λ)) := hm
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hxi : ξ = ((a⁻¹ : ℚ) : ℝ) * F'.const + ((-(b / a) : ℚ) : ℝ) := by
    have : F'.const = (a : ℝ) * ξ + b := hconst
    rw [this]
    push_cast
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [hxi]
    exact hmeas.affine hE _ _ (inv_ne_zero ha)
  · rw [hxi]
    exact irrational_affine hirr _ _ (inv_ne_zero ha)

/-- Theorem S with the decay supplied by a certificate: the hypothesis `hdecay` is the decay of the
family at the certificate's exponent (produced by `Decay.AltDecay`, `AltFold` or `Decay.Jet.Decay`). -/
theorem support_measureLB_of_certificate {Vnu : ℂ → ℝ} (C : Certificate Vnu)
    (Fam : PolyFamily) (scale : Fam.ι → ℕ) {Λ γ K : ℝ}
    (hΛ : HasScaledContent (Fam.restrictAdm (fun n => scale n % 2 = 0)) scale Λ)
    (hdecay : HasScaledDecay Fam scale C.Dr C.cr) (hη : C.Below Λ)
    (hγ : 0 < γ) (hK : 0 ≤ K)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ γ * scale n + K)
    (hnv : ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
      ∃ n, Fam.Adm n ∧ scale n = 2 * s ∧ Fam.evalQ n x ≠ 0)
    {ξ : ℝ} {a b : ℚ} (ha : a ≠ 0) (hconst : Fam.const = (a : ℝ) * ξ + b) :
    MeasureLBAt ξ (γ * C.cr / (C.Dr - Λ)) ∧ Irrational ξ :=
  support_measureLB Fam scale hΛ hdecay hη (by exact_mod_cast C.hc) hγ hK hdeg hnv ha hconst

end CatalanCore.Uniform.Support

#print axioms CatalanCore.Uniform.Support.support_measureLB
#print axioms CatalanCore.Uniform.Support.support_measureLB_of_certificate
