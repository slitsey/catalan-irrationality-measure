module

public import CatalanCore.Content.WeightedDet

@[expose] public section

/-!
# Reducing a scaled entry to its leading term (generic)

If `M` has Gauss valuation `≥ e` and `M = p^e · (lift of L0) + (valuation ≥ e+1)`, then any integral lift
`Z` of `p^{-e} M` reduces to the reduction of `L0` (`redMv_lift_eq`).  This is the step that turns the
node-sum expansions of `N9-LAI-CONTENT-EXACT` Lemma N into entries of the reduced block `N̄`.
-/

open MvPolynomial CatalanCore.Basic CatalanCore.Arith.Hybrid

namespace CatalanCore.Content

section ReducedLead

variable {σ : Type*} {p : ℕ} [hp : Fact p.Prime]

/-- **Reduction of a lift to the leading term.** -/
theorem redMv_lift_eq {e : ℤ} {M : MvPolynomial σ ℚ} (L0 : MvPolynomial σ (LocRing p))
    (hM : GV p (e + 1) (M - C ((p : ℚ) ^ e) * toQmv p L0))
    (Z : MvPolynomial σ (LocRing p)) (hZ : toQmv p Z = C ((p : ℚ) ^ (-e)) * M) :
    redMv p Z = redMv p L0 := by
  obtain ⟨g, hg⟩ := hM.exists_lift
  have hp0 : (p : ℚ) ≠ 0 := p_ne_zero
  have e1 : toQmv p (C ((p : ℕ) : LocRing p) * g) = C ((p : ℚ) ^ (-e)) * (M - C ((p : ℚ) ^ e) * toQmv p L0) := by
    have : toQmv (σ := σ) p (C ((p : ℕ) : LocRing p)) = C (p : ℚ) := by simp [toQmv]
    rw [map_mul, this, hg, ← mul_assoc, ← C_mul]
    congr 2
    rw [← zpow_one_add₀ hp0]
    congr 1; ring
  have e2 : toQmv p Z = toQmv p (C ((p : ℕ) : LocRing p) * g) + toQmv p L0 := by
    rw [hZ, e1]
    rw [mul_sub, ← mul_assoc, ← C_mul, ← zpow_add₀ hp0]
    simp
  have e3 : Z = C ((p : ℕ) : LocRing p) * g + L0 := by
    apply toQmv_injective (σ := σ) (p := p)
    rw [e2, map_add]
  rw [e3, map_add, redMv_Cp_mul, zero_add]

lemma redMv_C_mul_X (a : LocRing p) (i : σ) :
    redMv p (C a * X i) =
      algebraMap (MvPolynomial σ (ZMod p)) (FractionRing (MvPolynomial σ (ZMod p)))
        (C (redQ p a) * X i) := by
  simp [redMv]

end ReducedLead

end CatalanCore.Content

#print axioms CatalanCore.Content.redMv_lift_eq
