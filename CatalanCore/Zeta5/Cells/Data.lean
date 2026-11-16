module

public import Mathlib.Data.Rat.Defs

@[expose] public section

/-!
# Z5-CELLS, part 12: data decoding

Generated data are flat integer lists written with `raw_ints%` (no instance synthesis per
element, `lean-efficient` §2): `[n₀, d₀, n₁, d₁, …]` is decoded to the rationals `nᵢ/dᵢ`.
Structural recursion, one `ℚ` division per entry.
-/

namespace CatalanCore.Zeta5.Cells

def decodeQ : List ℤ → List ℚ
  | n :: d :: t => ((n : ℚ) / (d : ℚ)) :: decodeQ t
  | _ => []

end CatalanCore.Zeta5.Cells
