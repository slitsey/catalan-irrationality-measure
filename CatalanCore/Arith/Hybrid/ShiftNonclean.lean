module
public import CatalanCore.Arith.Hybrid.ShiftRow
public import CatalanCore.Arith.Hybrid.ShiftGamma
public import CatalanCore.Arith.Hybrid.ShiftRho
public import CatalanCore.Arith.Hybrid.ShiftRegular
public import CatalanCore.Arith.Hybrid.ShiftFinal
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
`ShiftNeumann`/`ShiftRho` = second-order partners, `ResponseLongChain` = free-long response,
`ShiftCross`/`ShiftV`/`ShiftCrossSum`/`ShiftZRed` = cross-chain terms,
`ShiftOwn` = own-chain transport modulo `p^2`, `ShiftAssemble`/`ShiftFinal` = the assembly),
and the finished results:
`weightedSameCell_zone` (the weighted same-cell congruence N1 for a long cell) and the
unconditional row theorems `twoLevel_row_both_unconditional` / `twoLevel_row_local_unconditional`.
No headline theorem is stated here and no existing module imports this file.
-/
