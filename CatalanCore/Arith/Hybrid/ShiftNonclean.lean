module
public import CatalanCore.Arith.Hybrid.ShiftRow
public import CatalanCore.Arith.Hybrid.ShiftNeumann
public import CatalanCore.Arith.Hybrid.ShiftCell
public import CatalanCore.Arith.Hybrid.PoleContraction
public import CatalanCore.Arith.Hybrid.PoleContractionCross
public import CatalanCore.Arith.Hybrid.SignNormalization
public import CatalanCore.Arith.Hybrid.QuadraticResponseReindex
public import CatalanCore.Arith.Hybrid.ResponseLongEq
public import CatalanCore.Arith.Hybrid.SchurDisplacement
@[expose] public section

/-!
# Umbrella for the shifted-constant (two-level) family

Importing this module gives every piece of the two-level family proved so far:
generic two-level determinant bounds (`TwoLevelGLE`, `TwoLevelCauchy`, `TwoLevelFull`),
the frame side (`ShiftLead` = leading cross-cell block, `ShiftCell` = cell constancy,
`ShiftNeumann` = second-order partners, `ResponseLongChain` = free-long response),
and the assembled row theorem `twoLevel_row_both` / `twoLevel_row_local`, which is conditional on
exactly one named obligation, `WeightedSameCell` (the weighted same-cell congruence N1).
No headline theorem is stated here and no existing module imports this file.
-/
