# An irrationality measure for Catalan's constant

A Lean 4 formalization of the following theorem.

> **Theorem.** Let `G = ∑_{j ≥ 0} (-1)^j / (2j+1)^2` be Catalan's constant. For every integer
> `a` and every sufficiently large integer `b`,
>
> `|G - a/b| > b^(-740)`.
>
> So the irrationality exponent of `G` is at most `740`. Chebyshev's bounds
> for final prime selection give `b^(-2220)`; the earlier `b^(-759)`, `b^(-2276)`,
> `b^(-878)` and `b^(-2632)` theorems and the historical
> `b^(-3662)` theorem remains available. Denominator asymptotics and secondary
> coefficient content still use the prime number theorem in this version.

The proof builds on [OpenAI's proof](https://github.com/openai/math) that `G` is irrational and
on its Lean formalization. The companion paper, S. Litsey, *An irrationality measure for
Catalan's constant* (2026), has revised LaTeX source and PDF in [`paper/`](paper/). The earlier 8127 version was
Hexagon preprint `hexagon:2610.00187v1`; this repository update does not upload a new preprint version. R. K. Jha proved earlier, independently, the weaker bound
`μ(G) ≤ 10^8` ([doi:10.5281/zenodo.23237269](https://doi.org/10.5281/zenodo.23237269)).
Related work by M. C. S. Carreira reports `μ(G) < 2715` using another determinant design
([doi:10.5281/zenodo.23326325](https://doi.org/10.5281/zenodo.23326325)); the paper now compares it.

## Companion result: irrationality measures for G ∓ 5π²/48

The repository also contains a separate, fully formalized result. Write
`λ = G/2 − 5π²/96` and `λ′ = G/2 + 5π²/96`, so that `G ∓ 5π²/48 = 2λ, 2λ′`. Both λ and λ′ are irrational.
For all coprime `p, q` with `q` sufficiently large,
`|λ − p/q| > q^(-78)` and `|λ′ − p/q| > q^(-78)`, and `|G + 5π²/48 − p/q| > q^(-79)`.
The exact exponent proved in Lean is `31682445459/409965000 ≈ 77.28`.

- Statements: [`ChallengeLambda.lean`](ChallengeLambda.lean) (Mathlib only, with G written as a series).
- Proofs: [`SolutionLambda.lean`](SolutionLambda.lean) and the library [`CatalanLambda/`](CatalanLambda/).
- Kernel-checked certificate: `CatalanLambda.Cert.certFacts`, using `decide +kernel` only.
- Checking: [`comparator-lambda.json`](comparator-lambda.json). Axioms are `propext`, `Quot.sound` and `Classical.choice`.
- Metadata: [`formalization-lambda.yaml`](formalization-lambda.yaml).
- Paper: [`paper-lambda/`](paper-lambda/), with certificate scripts in `paper-lambda/scripts/`. The paper also proves two stronger
  bounds that are **not formalized**. Both rest on proofs audited by independent Claude agents, not on a human referee:
  - μ(λ) ≤ 57.85 and μ(λ′) ≤ 57.85, by a determinant evaluation.
  - **μ(λ) ≤ 46.45**, by a rectangular "hybrid" Löwner frame. Its interval-arithmetic decay and window certificate is in
    `paper-lambda/scripts-hybrid/`. The hybrid has not been done for λ′, which stays at 57.85.

Build the λ result with `lake build CatalanLambda ChallengeLambda SolutionLambda`. It is not a default target.

## What to read

- [`Challenge.lean`](Challenge.lean) states the strongest bounds and retained historical statements using Mathlib only, with Catalan's
  constant written out as a series. This is the whole trusted statement surface.
- [`Solution.lean`](Solution.lean) proves them from the development.
- [`comparator.json`](comparator.json) tells `lake comparator` to check that `Solution` proves
  exactly the statements of `Challenge`, using only `propext`, `Quot.sound` and
  `Classical.choice`.
- [`formalization.yaml`](formalization.yaml) records provenance, authorship, automation and
  scope.

The current `740` / `2220` bounds add a sixth coefficient-content window (Lemma U6) to the
`759` / `2276` development. For `N >= 1` and every prime `p` with `4N < p` and `2p < 9N`,
the rank of the reduced scaled base matrix is at most `20N - (p - 4N - 1)/2`
(`CatalanMeasure.Parametric.u6_canonical_rank`). The proof is column-side rather than
row-side. Put `d = p - 4N` (odd, with `2d < N`). Identity K6,
`2 X W S_c - (2 - X^(2p)) U_c = 0 (mod X^(24N))` for every row combination `c` (from the
integer identity `U_{m-1} T_n - T_m U_{n-1} = U_{m-n-1}` with `m = 2p`, together with
`T_p = X^p` and `U_{p-1} = (X^2-1)^((p-1)/2)` in characteristic `p`), lets every filtered
column of a block of `5d` columns be written as a constant combination of the digits
`(X-1)^N X W (1-X)^N S_c` at positions `u p + mu`, `u = 2..6`. The Frobenius law
`(1-X)^e Q = (1-X^p) Y`, `e = (d+1)/2`, makes `(d-1)/2` of these digits redundant by a
telescoping class-sum identity. Constraining the `20N - 5d` remaining columns and the other
`4d + e` digits therefore costs `20N - (d-1)/2` conditions, which forces the whole block to
vanish. For `4N < p < 9N/2` the canonical normalizer already has `p`-exponent `40N`, so the
content exponent is `(p - 4N - 1)/2` (a profile `(x-4)/2` of area `1/16` on `[4, 9/2]`) and
adds `624/10000` to the gap: `eta = 505079/200000`, `rho = 519037/5000`,
`kappa = 3700000/519037`, `rho * kappa = 740`; the limiting exponent is
`373706640/505079 = 739.897...` and the Chebyshev exponent `1121119920/505079 = 2219.69...`.
The derivation and formalization of Lemma U6 are due to Claude (Anthropic) working with
Sean Litsey.

The `759` / `2276` bounds add one earlier coefficient-content lemma (Lemma U3) to the
`878` / `2632` development below. For `N >= 1` and every prime `p` with `8N < p < 9N`, the
nullity of the reduced scaled base matrix is at least `18N - 2p - 1`
(`CatalanMeasure.Parametric.u3_canonical_rank`). The proof restricts to the flag subspace
`{c : (1-X^2)^((p+1)/2) | P_c}` (`p + 1 - N` linear conditions), proves identity K
`D_c = Q~_c` below degree `24N` from the Chebyshev Frobenius reflection identity
`T_{p-m} = X^p T_m - (X^2-1)^((p+1)/2) U_{m-1}` in characteristic `p`, shows that the raw
columns in the residue window `27N-3p <= l < 24N-2p` have rank at most one, and counts
`2p + 2N + 1` conditions in total. The resulting content exponent
`min(p-8N-1, 18N-2p-1)^+` over the primes in `(8N, 9N)` (a tent of area `1/3`) adds
`3331/10000` to the gap: `eta = 492599/200000`, `rho = 519037/5000`,
`kappa = 3795000/519037`, `rho * kappa = 759`; the limiting exponent is
`373706640/492599 = 758.64...` and the Chebyshev exponent `1121119920/492599 = 2275.93...`.
The derivation of Lemma U3 is due to Claude (Anthropic) working with Sean Litsey.

The `878` / `2632` development retains the admissible tuple `(20,3,1,2,1)`, degree `18N`,
the actual denominator estimates, secondary content tent and coefficientwise
recycling. Exact supplied first40/second160 trials give target `2.2563367`.
Central-gap interpolation with physical gap `401/2500` and transformed gap
`2005000/6410801` gives residual cap `-0.0524` on the marked domain; its
global near-field cap is `-0.75`. The first and second marked row costs are
`84.2Nm` and `85.8944Nm`. An actual 55-piece circle proof gives joint
coefficient-functional weight exponent `17.913`. Thus `rho = 519037/5000`
and the content-adjusted gap is `eta = 425979/200000`. The limiting recycled
exponent is `41522960/47331 < 878`; Chebyshev final selection gives
`41522960/15777 < 2632`.

All numerical bounds are ordinary kernel-checked rational certificates.
A generic Descartes root budget and disjoint-bracket exhaustion use five
coarse counts and 241 opposite-sign brackets to cover the X/Y critical
points. Field values and the restricted residual intervals are separately
checked. The immutable trial inputs and hashes are recorded in
[`scripts/certgen/gap878/`](scripts/certgen/gap878/); the authoritative
proof data are the Lean source literals.

The retained 955/2864 checkpoint uses the admissible determinant tuple `(20,3,1,2,1)`:
the matrix has `20N` rows and its polynomial has degree at most `18N`. Actual
physical column-pool valuations and sparse residue relations give odd-prime
cost `8795/4800`; the actual two-adic smoothing/minor proof gives
`(21/200) log 2`. Four exact field certificates and a separate treatment of free
and fixed populations prove dual target `U = 2.256085`. Full-interval
quadrature, genuine P-only marked atoms and grouped sheet estimates yield
perturbation exponent `rho = 538/5`, including the critical-radius binomial
factor. The new coefficient theorem proves `q^(2j) | coeff_j Q_N` for
`N < q <= 2N`. Recycling all later bad-prime squares while choosing the
largest good prime gives 1091 after retaining the already certified gap
`eta = 1.7755` and sharpening the existing first-population quadratic.
Its row cost is now `89.6Nm`; the joint atom weights add `18Nm`.
A further explicit full-row residue construction gives nullity at least
`max(0,min(floor((9p-52N)/2),floor((44N-7p)/2)))`. Its compatible extra
coefficient content has logarithmic rate `16/63` and preserves coefficient
recycling. Using rate `507/2000` raises the available gap to `2.029`, giving
the retained **955** theorem. Its literal raw-source, row support, injectivity,
constraint dimension, coefficient-content and PNT bridges all pass the main kernel.
`TwentyCostMain` retains the earlier 1091 result.
The earlier 1095 theorem with radius 108, the 1099 theorem with `eta = 1.77`, and the
1281/3662 checkpoint, remain in their original verified modules.

The 740/2220, 759/2276, 878/2632 and retained 955/2864 bounds pass Lean's main kernel and standard-axiom audits. Independent-kernel
and comparator acceptance remain pending; CI optimization is deferred. The earlier
48-row construction and its 1981/5391 result remain as verified historical modules.

## Structure of the proof

| Directory or file | Content |
|---|---|
| `CatalanMeasure/Parametric/U6Main.lean`, `U6Audit.lean` | current unconditional 740 / 2220 endpoints |
| `CatalanMeasure/Parametric/U6Chebyshev.lean`, `U6Identity.lean`, `U6Block.lean`, `U6Digits.lean`, `U6Rank.lean` | Lemma U6: doubled Chebyshev identity, identity K6, Frobenius class-sum law, block column responses and canonical rank bound |
| `CatalanMeasure/Parametric/U6Content.lean`, `U6PrimeGrowth.lean` | rank to coefficient content for `4N < p < 9N/2` and the area-`1/16` prime sum |
| `CatalanMeasure/Parametric/U3Main.lean`, `U3Audit.lean` | retained unconditional 759 / 2276 endpoints |
| `CatalanMeasure/Parametric/U3ChebyshevFrobenius.lean`, `U3RowIdentity.lean`, `U3Combination.lean`, `U3Digits.lean`, `U3Rank.lean` | Lemma U3: Frobenius reflection identity, identity K, flag subspace, digit response and canonical rank bound |
| `CatalanMeasure/Parametric/U3Content.lean`, `U3PrimeGrowth.lean` | nullity to coefficient content for `8N < p < 9N` and the area-`1/3` prime sum |
| `CatalanMeasure/Parametric/GapMain.lean`, `GapFinalTransfer.lean` | retained unconditional 878 / 2632 endpoints |
| `CatalanMeasure/FirstStrongTrial/`, `StrongTrial/` | supplied trial norms, field values and root-coverage certificates |
| `CatalanMeasure/Parametric/GapNodal.lean`, `GapQuadrature.lean`, `GapAtomCost.lean` | exact gap nodes, marked support and coefficient selection |
| `CatalanMeasure/GapCircle/`, `Parametric/GapActualWeights.lean` | actual circle and coefficient-functional weights |
| `CatalanMeasure/Cert/DescartesBudget.lean`, `RootBracket.lean`, `IntegerHorner.lean`, `RootBudgetCover.lean` | ordinary-kernel root counts, bracket signs and coverage |
| `CatalanMeasure/Parametric/SecondaryTentMain.lean`, `SecondaryTentMeasureTransfer.lean` | retained 955 bound from the uniform secondary coefficient-content tent |
| `CatalanMeasure/Parametric/SecondaryTentChebyshev.lean` | alternate final-selection criterion: exact exponent `5810400/2029 < 2864`, retaining PNT-backed denominator and content estimates |
| `CatalanMeasure/Parametric/SecondaryTentParameters*.lean`, `SecondaryTentRow*.lean`, `SecondaryTentSource*.lean` | concrete full-row construction, exact source compatibility, flags, injection and filtered rank. Archived (under `archive/CatalanArchive/CatalanMeasure/`): `Parametric\SecondaryTentParametersAudit.lean`, `Parametric\SecondaryTentRowAudit.lean`, `Parametric\SecondaryTentRowDirectAudit.lean`, `Parametric\SecondaryTentRowPacketAudit.lean`, `Parametric\SecondaryTentRowRationalAudit.lean`, `Parametric\SecondaryTentRowSourceAudit.lean`, `Parametric\SecondaryTentSourceAudit.lean`, `Parametric\SecondaryTentSourceBridgeAudit.lean`, `Parametric\SecondaryTentSourceBulkResponses.lean`, `Parametric\SecondaryTentSourceGeometry.lean`. |
| `CatalanMeasure/Parametric/TwentyCostMain.lean`, `TwentyFirstCost.lean`, `TwentyAtomCost.lean`, `TwentyCostPerturbation.lean` | retained 1091 bound with cost-parametric marked-atom estimates and the sharper certified gap |
| `CatalanMeasure/Parametric/TwentySharperMain.lean`, `TwentyRecycledMain.lean` | retained 1095 and 1099 bounds combining full-interval perturbation and coefficient recycling |
| `CatalanMeasure/Parametric/TwentyMain.lean`, `TwentyIntegerPolynomial.lean` | retained 1281/3662 bounds, integer polynomial of degree at most 18N and prime-index nonvanishing |
| `CatalanMeasure/Parametric/TwentyCoefficientDivisibility.lean`, `CatalanMeasure/RecycledIntegerLower.lean`, `RecycledPNTWindow.lean` | coefficientwise prime-square divisibility, strengthened integer lower bound, largest-good-prime criterion |
| `CatalanMeasure/Parametric/MarkedSheet*.lean`, `TwentyMarked*.lean`, `TwentyFullAtomDeterminants.lean`, `TwentyFullPerturbation.lean`, `CatalanMeasure/MixedArbitraryAtoms.lean` | original P-only full-interval atoms, marked Hadamard and grouped estimates, atomless mixed integration, exp(-108N) perturbation. Archived (under `archive/CatalanArchive/CatalanMeasure/`): `Parametric\MarkedSheetExpansionAudit.lean`, `Parametric\TwentyMarkedIntegrandAudit.lean`. |
| `CatalanMeasure/Parametric/TwentyDenominators.lean`, `TwentyDenominatorAsymptotic.lean`, `TwentyTwoAdic*.lean`, `TwentyCombinedOddLoss.lean` | actual determinant valuations, exact integrated odd-prime cost, common denominator and PNT growth. Archived (under `archive/CatalanArchive/CatalanMeasure/`): `Parametric\TwentyTwoAdicAudit.lean`. |
| `CatalanMeasure/TwentyTrial/`, `Parametric/TwentyUniformEnergy.lean`, `TwentyWeightedIntegrand.lean` | four kernel-checked endpoint trials and uniform free/fixed population estimates |
| `CatalanMeasure/JointDetExpansion.lean`, `WeightedMixedAndreief.lean`, `Parametric/TwentyPerturbation.lean` | joint atom weights, actual determinant integration and perturbation on exp(-120N) disks |
| `CatalanMeasure/DeltaPoly.lean`, `Degree.lean` | OpenAI's determinant as a polynomial `Δ_N(X)` in the constant; `deg Δ_N ≤ 44N` |
| `CatalanMeasure/Denominators.lean`, `IntegerValued.lean`, `Integrality.lean` | a common denominator `D_N` for `Δ_N` at integers, with `log D_N ≤ (A + ε) n²`; integer-valued polynomials; `Q_N = (44N)! D_N Δ_N ∈ ℤ[X]` |
| `CatalanMeasure/Nonvanishing.lean` | `Δ_p(a/b) ≠ 0` for large primes `p ∤ b` |
| `CatalanMeasure/PrimeWindow.lean`, `Criterion.lean`, `PNTWindow.lean`, `Main.lean` | the irrationality-measure criterion, with Chebyshev and prime-number-theorem prime windows |
| `CatalanMeasure/Quadrature.lean`, `ChebyshevNodes.lean` | quadrature formula for the coefficient of the constant, at the roots of `T_J` moved to `[-1, 0]` |
| `CatalanMeasure/QuadCircle.lean` | the quadrature weights bounded through the unit circle: `|β| ≤ 8 J² K^N` with `K = 95 · 10^46` |
| `CatalanMeasure/DetExpansion.lean` | column expansion of `det(A + δΦβ)` |
| `CatalanMeasure/MixedAndreief.lean` | Andréief's identity with fixed point columns |
| `CatalanMeasure/GenVandermonde.lean`, `GenVandermondeSharp.lean` | `|det[s_l^{E_i}]| ≤ 2^{p(n-p)} |V(s)|` for nodes in `[0, 1]` |
| `CatalanMeasure/PinMajorant.lean`, `PinDampedDual.lean`, `PinSupDual.lean` | pointwise bound for the mixed integrands; OpenAI's energy dual for `p ≤ n` points |
| `CatalanMeasure/Cert/` | general lemmas for kernel-checked bounds on the energy trial fields: computable polynomials, root exclusion (Descartes), logarithm approximations, field values, derivatives, closed-form norms |
| `CatalanMeasure/Dual/`, `CatalanMeasure/DualTwo.lean` | a new certificate for the second case of OpenAI's energy dual (generated data and kernel checks): real-place constant `U = 2.29180925 - (log 2)/2` |
| `archive/CatalanArchive/CatalanMeasure/SharpBarrier.lean` | OpenAI's own certificate read to seven digits (`U = 2.2910468 - (log 2)/2`); not needed for the final theorems |
| `CatalanMeasure/Lemma6.lean` | the original perturbation estimate with `ρ = 404.25`, and the historical 8127/23168 bounds |
| `CatalanMeasure/VandermondeProduct.lean`, `WeightedMajorant.lean` | retain `∏(1+s)` in the mixed determinant bound |
| `CatalanMeasure/WeightedEnergy.lean`, `WeightedBounds.lean`, `WeightedCaseOne.lean`, `WeightedDualTwo/` | two fixed weighted endpoint certificates and their quadratic mass bound. Archived (under `archive/CatalanArchive/CatalanMeasure/`): `WeightedBounds.lean`, `WeightedCaseOne.lean`, `WeightedDualTwo\AQ.lean`, `WeightedDualTwo\ChecksX0.lean`, `WeightedDualTwo\ChecksX1.lean`, `WeightedDualTwo\ChecksX2.lean`, `WeightedDualTwo\ChecksX3.lean`, `WeightedDualTwo\ChecksX4.lean`, `WeightedDualTwo\ChecksX5.lean`, `WeightedDualTwo\ChecksX6.lean`, `WeightedDualTwo\ChecksX7.lean`, `WeightedDualTwo\ChecksX8.lean`, `WeightedDualTwo\ChecksY0.lean`, `WeightedDualTwo\ChecksY1.lean`, `WeightedDualTwo\ChecksY2.lean`, `WeightedDualTwo\ChecksY3.lean`, `WeightedDualTwo\ChecksY4.lean`, `WeightedDualTwo\ChecksY5.lean`, `WeightedDualTwo\Data.lean`, `WeightedDualTwo\IntegerData.lean`, `WeightedDualTwo\Norms.lean`, `WeightedDualTwo\Sup.lean`. |
| `archive/CatalanArchive/CatalanMeasure/WeightedLemma6.lean` | perturbation with `ρ = 392.5`, and the 7891/22494 bounds |
| `archive/CatalanArchive/CatalanMeasure/FixedNodes.lean`, `FixedNodeMajorant.lean`, `FixedNodeLemma6.lean` | retain the fixed-node decay by a quartic inequality; perturbation with `ρ = 370.4`, yielding 7447/21228 |
| `archive/CatalanArchive/CatalanMeasure/SeparateFixedNodes.lean`, `SeparateFixedMajorant.lean`, `SeparateBounds.lean`, `SeparateLemma6.lean` | separate the two fixed-node caps, sharpen the quadratic case-one margin; perturbation with `ρ = 366.3`, yielding the historical 7364/20993 checkpoint |
| `CatalanMeasure/SquareNonvanishing.lean`, `SquarePNTWindow.lean`, `SquareMain.lean` | nonvanishing when p² does not divide the denominator; halves the PNT prime-window surcharge, yielding 7181/20993. Archived (under `archive/CatalanArchive/CatalanMeasure/`): `SquareMain.lean`. |
| `CatalanMeasure/Parametric/Sparse*.lean`, `ChebyshevPrime.lean`, `FiveSourceElimination.lean` | uniform sparse prime-row dependencies and determinant valuation savings; the earlier proposed-parameter experiments remain separate from the selected twenty-row proof. Archived (under `archive/CatalanArchive/CatalanMeasure/`): `Parametric\SparseAudit.lean`. |
| `CatalanMeasure/SparsePrimeGain.lean`, `SparseGainPNT.lean`, `SparseDenominators.lean`, `SparseDenominatorGrowth.lean`, `SparseMain.lean` | exact gain integral, improved common denominator, and the historical 2742/7675 bounds. Archived (under `archive/CatalanArchive/CatalanMeasure/`): `SparseDenominatorGrowth.lean`, `SparseDenominators.lean`, `SparseGainPNT.lean`, `SparseMain.lean`. |
| `CatalanMeasure/Parametric/EarlySparseValuation.lean`, `ResidueRank.lean`, `SparseCombinationRank.lean` | actual residue rank and early-window determinant saving, with explicit injective row-combination maps. Archived (under `archive/CatalanArchive/CatalanMeasure/`): `Parametric/EarlySparseValuation.lean`. |
| `archive/CatalanArchive/CatalanMeasure/DensePrimeGain.lean`, `DenseGainPNT.lean`, `DenseDenominators.lean`, `DenseDenominatorGrowth.lean`, `DenseMain.lean` | gain integral 20/3, denominator saving 5/1728, and the 1981/5391 bounds |
| `OAI/` | the parts of OpenAI's formalization that are used (vendored; see below) |
| `PrimeNumberTheoremAnd/` | the files OpenAI adds to PrimeNumberTheoremAnd (vendored; see below) |

## Archive

The Lean files for the historical theorems (the earlier bounds such as 1981/5391, 2742/7675
and 7181/20993, and their audits and certificates), which the current published bounds no longer
import, now live under `archive/CatalanArchive/CatalanMeasure/`. They are not part of the default
build, but remain buildable with

```text
lake build Archive
```

The archived modules are named `CatalanArchive.CatalanMeasure.*` (Lake cannot share the
`CatalanMeasure` namespace between two source directories, and Mathlib owns the `Archive.*` prefix); their declarations keep their
original names. The main tree never imports the archive.

## Vendored code

Palomar requires Lean v4.35.0-rc2 or later, and every file a submission imports must use Lean's
module system. OpenAI's repository is pinned to Lean v4.34.1 and does not use modules, so it
cannot be imported directly. The 478 original files of OpenAI's formalization vendored for this development (from
commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` of
[openai/math](https://github.com/openai/math)) and the 10 files that OpenAI adds to
PrimeNumberTheoremAnd are therefore copied here. Each was converted mechanically to a module (a
`module` header, `public import`s, `@[expose] public section`) and adjusted where needed for
the newer Lean and Mathlib (see [`PORTING.md`](PORTING.md)). In 37 point-evaluation files of
OpenAI's second-barrier certificate the comparison constants were sharpened from five to seven
digits (the computations themselves are unchanged; see `NOTICE` and `archive/CatalanArchive/CatalanMeasure/SharpBarrier.lean`).
The generic determinant lemmas were subsequently moved without mathematical changes to
`RealDeterminantCore.lean`, bringing the OAI directory to 479 files. Generic denominator lemmas
were copied into `CatalanMeasure/Cert/DenominatorBounds.lean` to avoid importing the superseded
second-case certificate into the main proof. Otherwise their mathematical content is unchanged. Licences and attributions are in [`NOTICE`](NOTICE); all of this code is under the
Apache License 2.0.

## Building and checking

You need [elan](https://github.com/leanprover/elan) and several GiB of free disk.

```text
lake exe cache get
python3 scripts/check-lean-sources.py
lake build            # default targets; `lake build Archive` builds the historical theorems
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

The exact numerical checks are resource-intensive and can use several GiB per Lean process;
use a small worker count (for example `LEAN_NUM_THREADS=2`) on memory-constrained machines.
Independent-kernel replay can take substantially longer than compilation; the CI diagnostic
workflow records its timings. The generator for these files is in
[`scripts/certgen/`](scripts/certgen/). The comparator script needs Linux and `bwrap` (bubblewrap).

## Authorship and use of AI

The original mathematics, Lean development, module conversion and companion paper were
produced by Claude Opus 5.5 (Anthropic) at the request of Sean Litsey. The weighted Vandermonde
refinement, endpoint certificates, separate fixed-node decay inequalities, quadratic case refinement, integer certificate soundness proofs, square-denominator nonvanishing and prime-window refinement, the twenty-row parameter family, full free/fixed population energy, actual local arithmetic and corresponding paper revisions were
developed with OpenAI Codex at his request. The full-interval marked-sheet
assembly, critical-radius perturbation, coefficient recycling and largest-good-prime
criterion giving 1099 were also developed with Codex. The later cost refinement,
secondary content tent, supplied trials, central-gap interpolation, actual
circle weights, root-budget certificates and 878/2632 assembly were developed
with Codex at his request. Lemma U3, its formalization, the content transfer to the primes
in `(8N, 9N)` and the 759/2276 assembly were developed by Claude (Anthropic) working with
Sean Litsey, on top of the Codex pipeline; so were Lemma U6, its formalization, the content
transfer to the primes in `(4N, 9N/2)` and the 740/2220 assembly. Sean Litsey posed the problem,
directed the work, and is responsible for this repository. The vendored code is OpenAI's (see
above).

## Submission

This repository follows the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate).
Submissions to the registry go through the form at https://submit.palomar-registry.org/.

## Licence

Apache License 2.0; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
