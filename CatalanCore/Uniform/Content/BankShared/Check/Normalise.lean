import CatalanCore.Uniform.Content.BankShared.Check.Content
import CatalanCore.Uniform.Content.BankShared.NormaliseGLE
set_option Elab.async false

/-! # Normalisation transport of the bank-check hypotheses (lane C1L)

The index set and the admissibility of `AltEven c hc Fr depth` do not depend on the frame, only the member
polynomials do.  If `Fr.Mn a b = N⁻¹ · Fr0.Mn a b` with `N` a `p`-unit, the members of `Fr` and `Fr0` have the same
`p`-clearing exponents (`normalisation_gle`), so `CatValid` and `PreValid` transport from `Fr0` to `Fr`.  For a sign
change (`N = -1`, a unit at every prime): `catValid_neg`, `preValid_neg`.  This serves a bank whose hybrid instance
lives on the sign-normalised frame. -/

namespace CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Basic CatalanCore.Arith.Hybrid

theorem catValid_normalise {c : ℚ} {hc : 0 < c} {Fr Fr0 : Frame} {depth q o Pbad N0 : ℕ}
    {cat : List Branch} {N : ℚ} (hN0 : N ≠ 0) (hMn : ∀ a b, Fr.Mn a b = N⁻¹ * Fr0.Mn a b)
    (hunit : ∀ (p : ℕ) [Fact p.Prime], Pbad < p → N ∈ LocRing p ∧ N⁻¹ ∈ LocRing p)
    (h : CatValid c hc Fr0 depth q o Pbad N0 cat) : CatValid c hc Fr depth q o Pbad N0 cat := by
  intro b hb i hi hi0 p _ hpP hpN hsq j k hk hj0 hjq hk0 hkp hcond
  obtain ⟨n, hn, hle⟩ := h b hb i hi hi0 p hpP hpN hsq j k hk hj0 hjq hk0 hkp hcond
  obtain ⟨hN, hNi⟩ := hunit p hpP
  exact ⟨n, normalisation_gle Fr Fr0 (altGeom c hc).geometry i p n N hN0 hMn hN hNi hn, hle⟩

theorem preValid_normalise {c : ℚ} {hc : 0 < c} {Fr Fr0 : Frame} {depth M : ℕ} {B : SmallBudget}
    {t0 α0b : ℚ} {N : ℚ} (hN0 : N ≠ 0) (hMn : ∀ a b, Fr.Mn a b = N⁻¹ * Fr0.Mn a b)
    (hunit : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ M → N ∈ LocRing p ∧ N⁻¹ ∈ LocRing p)
    (h : PreValid c hc Fr0 depth M B t0 α0b) : PreValid c hc Fr depth M B t0 α0b := by
  intro i hi p _ hpM hp
  obtain ⟨n, hn, hle⟩ := h i hi p hpM hp
  obtain ⟨hN, hNi⟩ := hunit p hpM
  exact ⟨n, normalisation_gle Fr Fr0 (altGeom c hc).geometry i p n N hN0 hMn hN hNi hn, hle⟩

theorem neg_one_units (p : ℕ) [Fact p.Prime] : (-1 : ℚ) ∈ LocRing p ∧ (-1 : ℚ)⁻¹ ∈ LocRing p := by
  have h1 : (-1 : ℚ) ∈ LocRing p := (LocRing p).neg_mem (LocRing p).one_mem
  refine ⟨h1, ?_⟩
  rw [inv_neg, inv_one]
  exact h1

/-- **Sign change**: `CatValid` transports along `Fr.Mn = -Fr0.Mn`. -/
theorem catValid_neg {c : ℚ} {hc : 0 < c} {Fr Fr0 : Frame} {depth q o Pbad N0 : ℕ} {cat : List Branch}
    (hMn : ∀ a b, Fr.Mn a b = -Fr0.Mn a b) (h : CatValid c hc Fr0 depth q o Pbad N0 cat) :
    CatValid c hc Fr depth q o Pbad N0 cat :=
  catValid_normalise (N := -1) (by norm_num) (fun a b => by rw [hMn]; norm_num)
    (fun p _ _ => neg_one_units p) h

/-- **Sign change**: `PreValid` transports along `Fr.Mn = -Fr0.Mn`. -/
theorem preValid_neg {c : ℚ} {hc : 0 < c} {Fr Fr0 : Frame} {depth M : ℕ} {B : SmallBudget} {t0 α0b : ℚ}
    (hMn : ∀ a b, Fr.Mn a b = -Fr0.Mn a b) (h : PreValid c hc Fr0 depth M B t0 α0b) :
    PreValid c hc Fr depth M B t0 α0b :=
  preValid_normalise (N := -1) (by norm_num) (fun a b => by rw [hMn]; norm_num)
    (fun p _ _ => neg_one_units p) h

end CatalanCore.Uniform.Content.BankShared.Check
