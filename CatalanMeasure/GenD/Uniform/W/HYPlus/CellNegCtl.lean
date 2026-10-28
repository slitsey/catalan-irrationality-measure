module
@[expose] public section

/-! Negative control (recorded, executed once on 2026-10-28): replacing the shift constant `2` by `3`
in `u9_c2`, and checking `PhiHm` constancy on the H+ vector `u9`, both fail under `decide +kernel`.
The certificate pipeline therefore rejects wrong constants and wrong vectors. -/
