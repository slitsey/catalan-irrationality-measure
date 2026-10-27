# Uniform Lean decision record — Phase 0

27 October 2026. Worktree: `work/catalan-uniform`, branch `codex/uniform-lean`.

## Scope and phase gate

The handoff governs phase order where LEAN-PLAN §4 has older ordering. This run
does Phase 0 only and stops for Sean's review. All four theorem domains, signed
densities, fixed periodic-block geometry, polygons and Phase 5 completeness stay
in scope. A successful arithmetic pilot is not a source theorem or a banked bound.
No full-tree build is authorized before the final approved public-root switch.

## Baseline correction (Sean approved)

The requested `main` is the single initial commit `c31aa79` and has none of
CatalanCore, CatalanFrames or the required GenD development. After creating the
requested branch from main, Sean explicitly approved advancing only that new
branch to release commit `5e09e6f`. The advance was a fast-forward. Release was
read but not edited. Existing release public roots are baseline, not new changes.
Dependency packages and existing library build artifacts were copied, without
sharing writable files, into the new worktree. No atomic tree is rebuilt.

## G prefix reuse

Use arbitrary-scale `RawDigitReduction.raw_zero_digit_reduction`,
`RawDigitFunctional.rawEntry_primeDigitPair`, `RankU` physical row/reversal
lemmas, `RankFilt.fResp_eq_sum_uResp`, and the generic injected-kernel dimension
bridge `SecondaryTentDimension.secondaryTent_rank_of_constraints`.

Do not use `FilterDigitReduction` as an all-quotient theorem: its relevant
filtered statements specialize N=p. `RankFilt.fResp_digit` assumes no carry;
`RankDigits` and `RankSeq` supply particular sufficient-family windows. None
proves the complete p-step split, signed tiling, Frobenius slot split or unique
prefix graphs. The raw-polynomial-response dimension wrapper would impose an
unnecessary raw-response degree condition; use the general injected-kernel bridge.

C-Prefix estimate changes from 3,000–7,000 to **4,000–7,000 lines (C)**, including
chart coverage and exceptions. This is a source audit estimate, not measured work.
The injection simplification removes surjectivity, not auxiliary uniqueness or
physical-support restrictions.

## Hybrid valuation reuse

Reuse `RankGLE.gle_det_of_scaled_dvd`, `gle_det_of_rank`, `TwoLevelWit.gle`,
the `TwoLevelFull` Cauchy interface, `LemmaE.TCore.tcore_of_det_gle`, and the
existing Gauss multiplicativity/integrality API. Preserve the partial two-level
Smith theorem; add stage composition instead of developing a full Smith library.

`ExactLev`/`SingLev` are tropical entry-level constructors, not the UC4 exact
identity. `RegularPoleSplit` has quarter-specific 4/16 constants. The general
pole charts, stable rational leading kernels, actual global elimination and
compressed next matrix still need proofs. `DefHyp.add` requires disjoint prime
supports; competing prices at one prime must be combined by minimum first.

C-Next estimate narrows from 2,000–4,500 to **2,000–4,000 lines (C)**. No dramatic
reduction is justified by the existing sufficient-valuation APIs.

## Corner primitive reuse

Use Mathlib's convex explicit segment-integral primitive theorem, identify it
with the paper's radial `(z-a)*integral_0^1 f(a+t*(z-a))`, and telescope endpoint
values. Pilot the actual chi3 cotangent source on an interior strictly upper
corner reconstructed from saved exact decimal parameter strings. This avoids
reproving differentiation under the integral or a general polygon Cauchy theorem.
The real initial endpoint's pole-free-disk bridge and improper connector estimate
remain future obligations. The finite geometry mirror is not the analytic proof.

## Signed arithmetic representation

Use the complete saved signed chi3 trial (114 physical pieces after conjugation),
with exact dyadic saved weights and decimal rational support coordinates. Repair
the mass to one by a recorded endpoint-zero bump on the last piece. This pilot
does not preserve or assert the numerical optimized ratio. Verify genuinely
negative density values, exact mass, independently computed jet coefficients,
a direct independent potential evaluation at the cell center, and independent
self-energy and positive/negative mutual-energy formulas.

The order-8 potential workload has 466 distinct log/arctan inputs and eight
Bernstein values. A small cell of halfwidth 10^-7 has 698 grouped rational L1
tail contributions, with a scaled upper sum 407569108 at scale 10^36+39.
Check each shared input once, assemble its literal table by a
generic cons lemma, and check each final value separately. Use raw_ints% tapes
also for large exact constants. The self-energy pilot uses one negative-density
piece plus a cross interaction with a positive piece, not a full production
energy matrix. The latter deliberately exposes conditioning of the short-piece
formula at the current scale; its coarse enclosure is not a production budget.
All rational literals are reduced by Fraction; none of 3757 numerator/denominator
pairs has both low 64 bits zero. The evaluator's analytic error and
source/remainder soundness are still unproved: these are kernel arithmetic
measurements only. Block-size policy is finalized in the phase report after
measurements; do not extrapolate the old 0.72-second straight-ray sample to this
larger polygon trial.

## Controls and inference limits

The existing released 590 and hybrid banks remain successful controls and are
not rebuilt. No failed sufficient packet excludes a theorem family. No new
bound, HasContent or HasDecay conclusion follows from these pilots. Physical
prefix transport, characteristic exceptions, source coverage, full energy,
source analytic bridges and final assembly remain explicit later obligations.
