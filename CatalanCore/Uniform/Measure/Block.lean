module
public import CatalanCore.Uniform.Frame.Block
public import CatalanCore.Uniform.Frame.Deletion
public import CatalanCore.Uniform.Frame.Rational
public import CatalanCore.Uniform.Measure.Coefficient
@[expose] public section

namespace CatalanCore.Uniform.BlockGeom

/-- The all-common-deletion analytic provider supplies the exact family window,
with no leading charge for any fixed selection depth. -/
theorem hasScaledDecay (G : BlockGeom) (Fr : Frame) (depth : ℕ)
    {D c : ℝ} (hc : 0 ≤ c)
    (hminor : NodeFamily.HasAllMinorDecay G.geometry Fr D c) :
    HasScaledDecay (G.family Fr depth) G.scale D c := by
  apply NodeFamily.scaledDecay_of_all_minors G.geometry Fr depth hc
    (γ := G.common.mass) (K := G.common.n)
    (by exact_mod_cast G.common_pos.le) (Nat.cast_nonneg _)
  · intro r
    exact_mod_cast (G.card_common r).2
  · exact hminor

/-- Full general block-family GMT, with actual degree and bounded-deletion
window bridges. All three providers refer to precisely the same members. -/
theorem measure_of_providers (G : BlockGeom) (Fr : Frame) (depth : ℕ)
    {Λ D c : ℝ}
    (hΛ : HasCoefficientContent (G.family Fr depth) G.scale Λ)
    (hminor : NodeFamily.HasAllMinorDecay G.geometry Fr D c)
    (hnv : HasNV0 (G.family Fr depth) G.scale)
    (hη : Λ < D) (hc : 0 < c) :
    (G.family Fr depth).MeasureLB ((G.common.mass : ℝ) * c / (D - Λ)) := by
  apply measure_of_coefficient_content_nv0 (G.family Fr depth) G.scale
    (γ := G.common.mass) (K := G.common.n)
    (fun i => NodeFamily.family_degree Fr G.geometry depth i)
    hΛ (G.hasScaledDecay Fr depth hc.le hminor) hη hc
    (by exact_mod_cast G.common_pos) (Nat.cast_nonneg _)
  · intro i hi
    exact G.degree_bound Fr depth i
  · exact hnv

theorem irrational_of_providers (G : BlockGeom) (Fr : Frame) (depth : ℕ)
    {Λ D c : ℝ}
    (hΛ : HasCoefficientContent (G.family Fr depth) G.scale Λ)
    (hminor : NodeFamily.HasAllMinorDecay G.geometry Fr D c)
    (hnv : HasNV0 (G.family Fr depth) G.scale)
    (hη : Λ < D) (hc : 0 < c) : Irrational Fr.const := by
  apply irrational_of_coefficient_content_nv0 (G.family Fr depth) G.scale
    (γ := G.common.mass) (K := G.common.n)
    (fun i => NodeFamily.family_degree Fr G.geometry depth i)
    hΛ (G.hasScaledDecay Fr depth hc.le hminor) hη
    (by exact_mod_cast G.common_pos) (Nat.cast_nonneg _)
  · intro i hi
    exact G.degree_bound Fr depth i
  · exact hnv

end CatalanCore.Uniform.BlockGeom

