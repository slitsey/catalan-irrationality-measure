module

public import CatalanFrames.LambdaMirrorHybrid.MirN
public import CatalanCore.Arith.Hybrid.DefBFinal
public import CatalanCore.Arith.Hybrid.DefC5Fam
public import CatalanCore.Arith.Hybrid.DefC7Fam
public import CatalanCore.Arith.Hybrid.LemmaE.Class1U
public import CatalanCore.Arith.Hybrid.LemmaE.Class3M
public import CatalanCore.Arith.Hybrid.BorderB
public import CatalanCore.Arith.Hybrid.BorderC5
public import CatalanCore.Arith.Hybrid.BorderC7

@[expose] public section

/-!
# The mirror deficits: the generic Lemma E / B / C5 / C7 theorems at offset `o = 3`

The deficit side of the hybrid content bound for `λ' = G/2 + 5π²/96` needs no new mathematics: every
deficit family is the generic statement of `CatalanCore/Arith/Hybrid` instantiated at
`mirNData : LamData mirNFrame 3`.  Classes: `j = 1` is `p ≡ 1 (mod 4)` (`4k = p + 3`), `j = 3` is
`p ≡ 3 (mod 4)` (`4k = 3p + 3`) -- the residue classes are swapped relative to λ.
-/

open Classical CatalanCore CatalanCore.Arith.Hybrid


namespace CatalanFrames.LambdaMirrorHybrid

/-- Theorem B (all primes `r < p < r + m`), mirror. -/
theorem mirN_defHypT_B {I : HybInst mirNFrame} (r m : ℕ) (T : ℕ → ℕ)
    (W : ℕ → Prop) (hW : ∀ p, W p → p < r + m)
    (hSet : ∀ p : ℕ, p.Prime → W p → ∃ j k, BSetup 3 p r m j k)
    (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → W p → ∀ j k, BSetup 3 p r m j k →
      ∑ a, uPot p r k (Frame.hybRow r m a) + ∑ b, uPot p r k (Frame.hybCol r m b) ≤ T p) :
    DefHypT I r m T (fun p => if W p then m - (p - r) else 0) :=
  defHypT_B I mirNData r m T W hW hSet hT hTd

/-- Theorem C5 (`4k = p + 3`, `p ≡ 1 (4)`), mirror. -/
theorem mirN_defHypT_C5 {I : HybInst mirNFrame} (r m : ℕ) (T : ℕ → ℕ)
    (W : ℕ → Prop) (hSet : ∀ p : ℕ, p.Prime → W p → ∃ k, CSetup 3 p r m k)
    (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → W p → ∀ k, CSetup 3 p r m k →
      ∑ a, wC p r k (Frame.hybRow r m a) + ∑ b, wC p r k (Frame.hybCol r m b) ≤ T p) :
    DefHypT I r m T (fun p => if W p then p + (p + 3) / 4 - r - m else 0) :=
  defHypT_C5 I mirNData r m T W hSet hT hTd

/-- Theorem C7 (`4k = 3p + 3`, `p ≡ 3 (4)`), mirror. -/
theorem mirN_defHypT_C7 {I : HybInst mirNFrame} (r m : ℕ) (T : ℕ → ℕ)
    (W : ℕ → Prop) (hSet : ∀ p : ℕ, p.Prime → W p → ∃ k, CSetup7 3 p r m k)
    (hT : ∀ p, p.Prime → p < Bnd I r m → tropExp I r m p ≤ T p)
    (hTd : ∀ p : ℕ, p.Prime → W p → ∀ k, CSetup7 3 p r m k →
      ∑ a, wC7 p r k (Frame.hybRow r m a) + ∑ b, wC7 p r k (Frame.hybCol r m b) ≤ T p) :
    DefHypT I r m T (fun p => if W p then p + (3 * p + 3) / 4 - r - m else 0) :=
  defHypT_C7 I mirNData r m T W hSet hT hTd

/-- Lemma E, class `j = 3` (`p ≡ 3 mod 4`, `4k = 3p + 3`), mirror, in dual form. -/
theorem mirN_gleAt_E3class {p r m k : ℕ} [Fact p.Prime] (S : ESetup 3 p r m 3 k) :
    HasRankWit mirNFrame p r m (fun a => wE p r k (Frame.hybRow r m a))
      (fun b => wE p r k (Frame.hybCol r m b)) m :=
  gleAt_E1_wit mirNData S

/-- Lemma E, class `j = 1` (`p ≡ 1 mod 4`, `4k₁ = p + 3`), mirror; here `p ∤ 6255` holds for every prime
`p ≡ 1 (4)`, `p ≥ 7` (the exceptional prime `139` of λ is `3 mod 4`). -/
theorem mirN_gleAt_E1class {p r m k1 : ℕ} [Fact p.Prime] (S : ESetup3 3 p r m k1)
    (h6255 : ¬ p ∣ 6255) :
    GLE p (2 * r + m - m) (mirNFrame.fullPoly r m) := by
  have := gleAt_E3 S mirNData h6255
  rw [wrc_sum S] at this
  exact this

end CatalanFrames.LambdaMirrorHybrid
