module
public import CatalanCore.Uniform.Frame.Block
@[expose] public section
namespace CatalanCore.Uniform.BlockGeom

/-- A finite explicit visibility threshold from positive common density. -/
def visibilityThreshold (G : BlockGeom) (k : ℕ) : ℕ :=
  max 1 ⌈((k : ℚ) + G.common.n) / G.common.mass⌉₊

theorem common_ge_of_threshold (G : BlockGeom) (k r : ℕ)
    (hr : G.visibilityThreshold k ≤ r) : k ≤ (G.geometry r).C.card := by
  have hm := G.common_pos
  have hceil : ((k : ℚ) + G.common.n) / G.common.mass ≤ (r : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hr)
  have hmain := (div_le_iff₀ hm).mp hceil
  have hlo := (G.card_common r).1
  have : (k : ℚ) ≤ (G.geometry r).C.card := by nlinarith
  exact_mod_cast this

end CatalanCore.Uniform.BlockGeom
