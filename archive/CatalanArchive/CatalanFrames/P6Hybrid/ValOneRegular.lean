module

public import CatalanArchive.CatalanCore.Basic.ValOneDen
public import CatalanArchive.CatalanFrames.P6Hybrid.ValOne
public import CatalanArchive.CatalanFrames.P6Hybrid.Assembly

/-!
# Square-regular P6 hybrid nonvanishing

Only denominator valuations zero and one are needed. The generic arithmetic
helper extracts the localization unit in the valuation-one case.
-/

@[expose] public section

open Finset CatalanCore CatalanCore.Rect CatalanFrames.P6



namespace CatalanFrames.P6Hybrid

variable {ℓ t : ℕ} [Fact ℓ.Prime]

/-- P6's pair is nonvanishing for every denominator not divisible by `ℓ²`.
The valuation-one case already makes the first member nonzero. -/
theorem p6_hyb_nonvanishing_square (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t)
    (m : ℕ) (hm : 1 ≤ m) (hband : 2 * m + 1 ≤ t) {x : ℚ}
    (hx : ¬ ℓ ^ 2 ∣ x.den)
    (h1 : ((after (3 * t - 2 * m) m).Full p6Frame x).det = 0)
    (h2 : ((afterTop (3 * t - 2 * m) m).Full p6Frame x).det = 0) : False := by
  by_cases hdiv : ℓ ∣ x.den
  · obtain ⟨u, hu, hg⟩ := good_mul_of_den_dvd_not_sq x hdiv hx
    exact p6_after_valOne_ne hl ht m hm hband hg hu h1
  · exact p6_hyb_nonvanishing hl ht m hm hband hdiv h1 h2

/-- The reusable pair interface with the square-divisor regularity rule. -/
theorem p6_pairNV_square {Cls : ℕ → Prop} :
    PairNV p6Frame Cls (fun ℓ x => ¬ ℓ ^ 2 ∣ x.den) P6Good := by
  intro ℓ hℓ hc r m ⟨t, hl, ht, hm, hb, hr⟩ x hx h1 h2
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  subst hr
  exact p6_hyb_nonvanishing_square hl ht m hm hb hx h1 h2

#print axioms p6_pairNV_square

end CatalanFrames.P6Hybrid
