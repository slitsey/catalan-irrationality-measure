module

public import CatalanCore.Uniform.Content.Member.Layers
public import CatalanCore.Uniform.Frame.Block

@[expose] public section

/-!
# `HasContent` for the BlockGeom common-deletion family (lane H5)

For a general rational periodic block geometry `G` (arbitrary common, row and column block
collections, trim policy and positive common mass), a frame `Fr` and any fixed deletion depth, the
family `G.family Fr depth` (members: the actual finite determinants with at most `depth` common
nodes deleted) has content `Λ = (1 / mass)² · contentConstant M tmpl`, the sum over the unit
classes mod `M` of the exact piecewise-linear integrals of the class templates, scaled by the
common mass.  The cover data `ContentCover` is the per-prime minimum of the proved layers
(`ContentCover.ofLayers`).
-/

open CatalanCore CatalanCore.Uniform

namespace CatalanCore.Uniform.Content.Member

variable {M : ℕ} [NeZero M]

/-- **`HasContent` for the BlockGeom common-deletion family.** -/
theorem hasContent_blockGeom (G : BlockGeom) (Fr : Frame) (depth : ℕ)
    (CC : ContentCover (G.family Fr depth) G.scale M) :
    HasContent (G.family Fr depth)
      (((G.common.mass : ℝ)⁻¹) ^ 2 * contentConstant M CC.tmpl) := by
  have hmass : (0 : ℝ) < G.common.mass := by exact_mod_cast G.common_pos
  refine ContentCover.hasContent_of_cover CC (fun i => NodeFamily.family_degree Fr G.geometry depth i)
    (γ := (G.common.mass : ℝ)⁻¹) (γ' := (G.common.mass : ℝ))
    (K0 := ((G.common.n : ℝ) + depth) / G.common.mass) (K1 := G.common.n)
    (inv_nonneg.2 hmass.le) hmass (by positivity) (Nat.cast_nonneg _) ?_ ?_
  · intro i hi
    have hc := (G.card_common i.1).1
    have hc' : (G.common.mass : ℝ) * i.1 - G.common.n ≤ ((G.geometry i.1).C.card : ℝ) := by
      exact_mod_cast hc
    have hAdm : (G.geometry i.1).C.card - i.2.card ≤ depth := hi
    have hle : i.2.card ≤ (G.geometry i.1).C.card := by simpa using Finset.card_le_univ i.2
    have hdep : ((G.geometry i.1).C.card : ℝ) ≤ i.2.card + depth := by
      have : (G.geometry i.1).C.card ≤ i.2.card + depth := by omega
      exact_mod_cast this
    have hdeg : (G.family Fr depth).deg i = i.2.card := rfl
    show (i.1 : ℝ) ≤ (G.common.mass : ℝ)⁻¹ * ((G.family Fr depth).deg i : ℝ) +
      ((G.common.n : ℝ) + depth) / G.common.mass
    rw [hdeg]
    rw [inv_mul_eq_div, ← add_div, le_div_iff₀ hmass]
    nlinarith
  · intro i _
    exact G.degree_bound Fr depth i

end CatalanCore.Uniform.Content.Member
