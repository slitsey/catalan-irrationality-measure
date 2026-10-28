import CatalanCore.Uniform.Content.BankShared.NormaliseBank
import CatalanCore.Uniform.Content.BankShared.Reindex
set_option Elab.async false

/-! # Shared contract 2, block families (lane H17)

For a block geometry `G` and frames `Fr`, `Fr0` with `Fr.Mn = N⁻¹ * Fr0.Mn`,
`Fr.const = N⁻¹ * Fr0.const`: `G.family Fr depth` is `normScale` of `G.family Fr0 depth`, with
`h i = |S| + (G.geometry r).k`, and `h`, `deg` grow linearly in the scale.  Hence
`HasScaledContent` / `HasScaledDecay` of the restriction of `G.family Fr0 depth` to any set of
members transfer to `G.family Fr depth` with unchanged `Λ`, `D`, `c`. -/

namespace CatalanCore.Uniform.Content.BankShared
open Polynomial Finset CatalanCore CatalanCore.Rect CatalanCore.Uniform

/-- The border size is at most the number of row nodes, linear in the scale. -/
theorem geometry_k_le (G : BlockGeom) (r : ℕ) :
    ((G.geometry r).k : ℝ) ≤ (max (G.row.mass : ℝ) 0) * r + G.row.n := by
  have h1 : (G.geometry r).k ≤ (G.row.nodes r).card := by
    rw [geometry_k_eq_borderSize]; exact min_le_left _ _
  have h2 := (G.row.count_bounds r).2
  have h3 : ((G.geometry r).k : ℚ) ≤ G.row.mass * r + G.row.n :=
    (by exact_mod_cast h1 : ((G.geometry r).k : ℚ) ≤ (G.row.nodes r).card).trans h2
  have h4 : ((G.geometry r).k : ℝ) ≤ (G.row.mass : ℝ) * r + G.row.n := by exact_mod_cast h3
  have h5 : (G.row.mass : ℝ) * r ≤ (max (G.row.mass : ℝ) 0) * r :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
  linarith

/-- The exponent `h i = |S| + k` and the degree `|S|` are linear in the scale. -/
theorem normalise_linear (G : BlockGeom) (Fr : Frame) (depth : ℕ) (i : (G.family Fr depth).ι) :
    ((G.family Fr depth).deg i : ℝ) ≤
        ((G.common.mass : ℝ) + max (G.row.mass : ℝ) 0) * G.scale i
          + ((G.common.n : ℝ) + G.row.n) ∧
    (((i.2.card + (G.geometry i.1).k : ℕ) : ℝ)) ≤
        ((G.common.mass : ℝ) + max (G.row.mass : ℝ) 0) * G.scale i
          + ((G.common.n : ℝ) + G.row.n) := by
  have hd := G.degree_bound Fr depth i
  have hk := geometry_k_le G i.1
  have hr0 : (0 : ℝ) ≤ G.scale i := Nat.cast_nonneg _
  have hmax : (0 : ℝ) ≤ max (G.row.mass : ℝ) 0 := le_max_right _ _
  have hcn : (0 : ℝ) ≤ G.common.n := Nat.cast_nonneg _
  have hdeg : ((G.family Fr depth).deg i : ℝ) ≤ (G.common.mass : ℝ) * G.scale i + G.common.n := hd
  have hrn : (0 : ℝ) ≤ G.row.n := Nat.cast_nonneg _
  have hcm : (0 : ℝ) ≤ G.common.mass := by exact_mod_cast G.common_pos.le
  have hkk : ((G.geometry i.1).k : ℝ) ≤ (max (G.row.mass : ℝ) 0) * G.scale i + G.row.n := hk
  constructor
  · nlinarith [mul_nonneg hmax hr0]
  · have : ((i.2.card + (G.geometry i.1).k : ℕ) : ℝ) = ((G.family Fr depth).deg i : ℝ) +
        (G.geometry i.1).k := by push_cast; rfl
    rw [this]
    nlinarith [mul_nonneg hmax hr0]

/-- **Shared contract 2 for block families (content).**  Same `Λ`. -/
theorem bank_content_normalise (G : BlockGeom) (Fr Fr0 : Frame) (depth : ℕ)
    (P : NodeFamily.Index G.geometry → Prop) {N : ℚ} (hN : N ≠ 0)
    (hMn : ∀ a b, Fr.Mn a b = N⁻¹ * Fr0.Mn a b)
    (hconst : Fr.const = ((N⁻¹ : ℚ) : ℝ) * Fr0.const) {Λ : ℝ}
    (H : HasScaledContent ((G.family Fr0 depth).restrictAdm P) G.scale Λ) :
    HasScaledContent ((G.family Fr depth).restrictAdm P) G.scale Λ := by
  have hA : (0 : ℝ) ≤ (G.common.mass : ℝ) + max (G.row.mass : ℝ) 0 := by
    have : (0 : ℝ) ≤ G.common.mass := by exact_mod_cast G.common_pos.le
    have := le_max_right (G.row.mass : ℝ) 0
    linarith
  exact normScale_hasScaledContent ((G.family Fr0 depth).restrictAdm P) G.scale hN _
    Fr.const (G.family Fr depth).Q (fun i => normalisation_poly Fr Fr0 G.geometry i hN hMn)
    (K := (G.common.n : ℝ) + G.row.n) hA (by positivity) (fun i _ => (normalise_linear G Fr0 depth i |>.1))
    (fun i _ => (normalise_linear G Fr0 depth i |>.2)) H

/-- **Shared contract 2 for block families (decay).**  Same `D`, `c`. -/
theorem bank_decay_normalise (G : BlockGeom) (Fr Fr0 : Frame) (depth : ℕ)
    (P : NodeFamily.Index G.geometry → Prop) {N : ℚ} (hN : N ≠ 0)
    (hMn : ∀ a b, Fr.Mn a b = N⁻¹ * Fr0.Mn a b)
    (hconst : Fr.const = ((N⁻¹ : ℚ) : ℝ) * Fr0.const) {D c : ℝ}
    (H : HasScaledDecay ((G.family Fr0 depth).restrictAdm P) G.scale D c) :
    HasScaledDecay ((G.family Fr depth).restrictAdm P) G.scale D c := by
  have hA : (0 : ℝ) ≤ (G.common.mass : ℝ) + max (G.row.mass : ℝ) 0 := by
    have : (0 : ℝ) ≤ G.common.mass := by exact_mod_cast G.common_pos.le
    have := le_max_right (G.row.mass : ℝ) 0
    linarith
  exact normScale_hasScaledDecay ((G.family Fr0 depth).restrictAdm P) G.scale hN _
    Fr.const (G.family Fr depth).Q (fun i => normalisation_poly Fr Fr0 G.geometry i hN hMn)
    hconst (K := (G.common.n : ℝ) + G.row.n) hA (by positivity) (fun i _ => (normalise_linear G Fr0 depth i |>.2)) H

end CatalanCore.Uniform.Content.BankShared
