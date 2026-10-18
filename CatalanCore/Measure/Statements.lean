module

public import CatalanCore.Measure.Sep
public import CatalanCore.Measure.Core
public import CatalanCore.Measure.Exponent
public import CatalanCore.Measure.Irrational

/-!
# WP6 public entry point (re-export; no declarations, proofs complete)

Imports every WP6 module.  Public API (all in `CatalanCore.Measure` unless noted):
`PrimeRule.HasWindow` (in `CatalanCore`), `sep_core`, `measure_of_family_real`,
`measure_of_family`, `measure_of_family_le`, `measure_of_frame`, `measure_of_frame_le`,
`irrational_of_family`, `irrational_of_frame`, `PolyFamily.MeasureLB.mono`.
-/
