# Phase 0 hybrid reuse audit

27 October 2026. Read-only source audit against release baseline `5e09e6f`.
No existing source was edited and no build was run for this audit. Names and
hypotheses below were inspected in the Lean sources; compilation is not claimed.

## Result

The general determinant-divisibility, coefficient Gauss norm, integral lift,
partial two-level and Schur assembly machinery already exists. ExactLev and
SingLev supply entry-integrality/tropical constructors, not the UC4 leading-rank
elimination. No existing R0/M_next construction was found in the audited APIs.
Arbitrary-frame pole sources and bounded residue confluence remain substantial
new work. There is no evidence for a dramatic reduction of C-Next's estimate.

All paths below are relative to the Lean worktree. Names are in
`CatalanCore.Arith.Hybrid` unless qualified otherwise.

## Reusable declarations and precise limits

| File and declaration | Reuse and assumptions | Remaining obligation |
|---|---|---|
| `Arith/Hybrid/RankGLE.lean`, `gle_det_of_scaled_dvd` (126) | Integral polynomial lift Bl, row/column scales u,v, actual scaled-entry equality, and p^k dividing det Bl imply GLE(Σu+Σv-k). Truncation at zero is handled. | Supply the actual lift and divisibility. |
| `RankGLE.lean`, `gle_det_of_rank` (172) | Same bridge from reduction rank over RatFunc(ZMod p), with rank+k <= matrix size. | Only one rank layer; no construction of M_next. |
| `RankGLE.lean`, `exists_lift` (192), `phiP` (99), `phiP_eq_zero_iff` (102), `prime_p` (80) | Integral lift, reduction and its exact divisibility kernel. | Generic infrastructure only. |
| `TwoLevelGLE.lean`, `TwoLevelWit` (43), `TwoLevelWit.gle` (74) | Primitive row/column changes, divisible rows and columns, and a rank bound b on the divided intersection yield the total saving σ+(σ-b)_+. | Sufficient saving, not exact UC4 elimination identity. |
| `TwoLevelGLE.lean`, `exists_border_wit` (222), `gle_det_two_level_border` (289) | One-node border transfer costs 2w+1. Requires border entry bounds and the nontruncated-cost hypothesis. | Arbitrary bounded edits require their own geometry/accounting bridge. |
| `TwoLevelFull.lean`, `ShiftCauchyData` (33), `exists_twoLevelWit_of_shiftData` (52), `gle_full_of_shiftData` (89), bordered variant (113) | Existing q4 weighted-Cauchy route, given leading cross responses, divided weighted response and support condition. | Its Cauchy interface is not arbitrary bounded-confluence UC4. |
| `LemmaE/TCore.lean`, `Tscaled` (36), `tcore_of_det_gle` (50) | Generic Schur assembly, given primitive g, A*N=g•1 and exact scaled pivot determinant; transfers a determinant GLE bound. | Does not expose the new general exact valuation identity. |
| `LemmaE/Gauss.lean`, `gn_mul` (34), `gle_iff_gn` (103), `gn_pow` (114) | Existing coefficient Gauss norm multiplicativity and GLE dictionary. | Prefer this to rebuilding a DVR just for denominator bookkeeping. |
| `Linalg/TwoLevelDet.lean`, `two_level_dvd_det` (39), `two_level_dvd_det_of_primitive_changes` (74) | Domain-generic partial two-level theorem with prime element and reduction-kernel characterization; primitive changes need not be invertible over the coefficient ring. | Exact finite-depth Smith stack composition remains new. |

Paths abbreviated in the first column after the first row remain under
`CatalanCore/Arith/Hybrid/`; the Linalg row is under `CatalanCore/`.

## Entry/source infrastructure

`PeriodicEntries.lean:11` defines `Periodic.PoleData` for any Frame. It requires
prime-scaled Delta and squared-prime-scaled Dsq integrality, unit normalization,
and regularity off a periodic singular set. Its `PoleData.good_square` (59),
`good_diagonal` (75), `square_mem` (83), and `good_cross` (105) give the relevant
entry integrality and leading reductions. The square result requires the physical
range bound N<p*p. These are useful inputs, not stable source charts.

`CyclicPrefix.lean` has generic `cyclicPrefix_add_period`, `cyclicPrefix_mod`, and
`cyclicPrefix_congr` for every zero-mean residue function. `LemmaE/Harmonic.lean`
contains reciprocal zero-sum machinery, including `Gs_inv_top` (72, p>=3) and
`Gs_inv_sq_top` (82, p>=5). Fixed small primes can remain explicit exceptions.

`RegularPoleSplit.lean` has reusable `regularInverse` and `good_regularInverse`.
However `regularDelta`, `regularDsq`, and `good_regularPrefix_difference` contain
literal 4 and 16 and implement the quarter reciprocal difference. They cannot be
cited verbatim for the arbitrary-frame, per-pole regular-prefix theorem. Balance
of frame coefficients must not become a hidden hypothesis of UC4.

`Basic/ZModGood.lean` supplies Good arithmetic, inverses, finite sums and determinant
reduction. Source-stability certificates must still prove their denominators and
minors are units outside an explicitly exhibited fixed integer.

## What ExactLev, SingLev and Deficit actually provide

`ExactLev.lean` supplies `HybInst.ofExact`, `pow_count_mem`, `exact_top_Sp`, and
`exact_top_Sp2`. These construct entry-integrality levels for any frame. They do
not compute local leading ranks or compress to next kernels. `SingLev.lean` gives
`HybInst.ofSing` from noncancelling singular-block counts. Its own documentation
warns against using it for P6's cancellation-sensitive levels. Both remain useful
for elementary omitted-band and bad-prime bounds.

`Deficit.lean` provides `DefHyp`, `DhybD_integral`, `log_DhybD`, and `DefHyp.add`.
The addition theorem requires disjoint prime supports. It must not add competing
rank, tropical and Smith savings at the same prime. First combine the new natural
price with tropical by MIN, then express that valid minimum as a tropical deficit.

## Missing UC4 work, preserving the paper's scope

1. Arbitrary rational-pole event decomposition, exact endpoint counts and finite
   source coverage, including the explicit exception integer.
2. Per-pole regular-prefix periodicity without coefficient balance.
3. Stable rational leading matrices K_a, with exact rational left/right kernels
   and unit-minor certificates.
4. Global elimination and actual M_next, proving the compressed same-fiber
   order-p blocks vanish. Arbitrary modular kernel lifts do not justify this.
5. Exact Schur/division identity with charge h_N+R0, then the residual rank bound.
   The initial corank h_N-R0 is already charged and cannot be counted twice.
6. Adaptation from the standard Frame.fullPoly geometry to BlockGeom and bounded
   member edits.

The source comparison used northstar/UNIFORM-CONTENT-THEOREM.md UC4 and the complete
hybrid-content-source/NORTH-STAR-HYBRID-RANK-CONTENT-PROOF.md sections 1-5, together
with northstar/HYBRID-RANK-CONTENT-AUDIT.md. These demand the ORIGINAL X variable,
exact rational stable kernels, same-fiber cancellation, and actual finite counts.

## Revised estimate and decisions

C-Next: approximately 2,000-4,000 new lines (C), narrowed from 2,000-4,500, conditional
on reuse above. Working allocations: 700-1,300 for pole/source arithmetic;
700-1,400 for stable charts and exact elimination; 300-800 for determinant/valuation
assembly; 300-500 for geometry interfaces. These rough allocations overlap and are
not a measured sum. Pair, Integral and Smith remain separate packages.

For Smith, keep the existing partial two-level theorem unchanged and add exact
stack-stage composition and source bindings. A complete Smith normal-form library
is unnecessary. Generic stack and hereditary deletion accounting are not already
proved by the audited APIs.

No theorem scope is reduced. Failure to find a complete existing UC4 implementation
is an implementation gap, not a mathematical obstruction or a recommendation to
pause the broader programme.
