# An irrationality measure for Catalan's constant

A Lean 4 formalization of the following theorem.

> **Theorem.** Let `G = ∑_{j ≥ 0} (-1)^j / (2j+1)^2` be Catalan's constant. For every integer
> `a` and every sufficiently large integer `b`,
>
> `|G - a/b| > b^(-1091)`.
>
> So the irrationality exponent of `G` is at most `1091`. The earlier criterion using
> Chebyshev's bounds gives the retained result `b^(-3662)`.

The proof builds on [OpenAI's proof](https://github.com/openai/math) that `G` is irrational and
on its Lean formalization. The companion paper, S. Litsey, *An irrationality measure for
Catalan's constant* (2026), has revised LaTeX source and PDF in [`paper/`](paper/). The earlier 8127 version was
Hexagon preprint `hexagon:2610.00187v1`; this repository update does not upload a new preprint version. R. K. Jha proved earlier, independently, the weaker bound
`μ(G) ≤ 10^8` ([doi:10.5281/zenodo.23237269](https://doi.org/10.5281/zenodo.23237269)).
Related work by M. C. S. Carreira reports `μ(G) < 2715` using another determinant design
([doi:10.5281/zenodo.23326325](https://doi.org/10.5281/zenodo.23326325)); the paper now compares it.

## What to read

- [`Challenge.lean`](Challenge.lean) states the two theorems using Mathlib only, with Catalan's
  constant written out as a series. This is the whole trusted statement surface.
- [`Solution.lean`](Solution.lean) proves them from the development.
- [`comparator.json`](comparator.json) tells `lake comparator` to check that `Solution` proves
  exactly the statements of `Challenge`, using only `propext`, `Quot.sound` and
  `Classical.choice`.
- [`formalization.yaml`](formalization.yaml) records provenance, authorship, automation and
  scope.

The current theorem uses the admissible determinant tuple `(20,3,1,2,1)`:
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
The earlier 1095 theorem with radius 108, the 1099 theorem with `eta = 1.77`, and the
1281/3662 checkpoint, remain in their original verified modules.

Both bounds pass Lean's main kernel and standard-axiom audits. Independent-kernel
and comparator acceptance remain pending; CI optimization is deferred. The earlier
48-row construction and its 1981/5391 result remain as verified historical modules.

## Structure of the proof

| Directory or file | Content |
|---|---|
| `CatalanMeasure/Parametric/TwentyCostMain.lean`, `TwentyFirstCost.lean`, `TwentyAtomCost.lean`, `TwentyCostPerturbation.lean` | current 1091 bound with cost-parametric marked-atom estimates and the sharper certified gap |
| `CatalanMeasure/Parametric/TwentySharperMain.lean`, `TwentyRecycledMain.lean` | retained 1095 and 1099 bounds combining full-interval perturbation and coefficient recycling |
| `CatalanMeasure/Parametric/TwentyMain.lean`, `TwentyIntegerPolynomial.lean` | retained 1281/3662 bounds, integer polynomial of degree at most 18N and prime-index nonvanishing |
| `CatalanMeasure/Parametric/TwentyCoefficientDivisibility.lean`, `CatalanMeasure/RecycledIntegerLower.lean`, `RecycledPNTWindow.lean` | coefficientwise prime-square divisibility, strengthened integer lower bound, largest-good-prime criterion |
| `CatalanMeasure/Parametric/MarkedSheet*.lean`, `TwentyMarked*.lean`, `TwentyFullAtomDeterminants.lean`, `TwentyFullPerturbation.lean`, `CatalanMeasure/MixedArbitraryAtoms.lean` | original P-only full-interval atoms, marked Hadamard and grouped estimates, atomless mixed integration, exp(-108N) perturbation |
| `CatalanMeasure/Parametric/TwentyDenominators.lean`, `TwentyDenominatorAsymptotic.lean`, `TwentyTwoAdic*.lean`, `TwentyCombinedOddLoss.lean` | actual determinant valuations, exact integrated odd-prime cost, common denominator and PNT growth |
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
| `CatalanMeasure/SharpBarrier.lean` | OpenAI's own certificate read to seven digits (`U = 2.2910468 - (log 2)/2`); not needed for the final theorems |
| `CatalanMeasure/Lemma6.lean` | the original perturbation estimate with `ρ = 404.25`, and the historical 8127/23168 bounds |
| `CatalanMeasure/VandermondeProduct.lean`, `WeightedMajorant.lean` | retain `∏(1+s)` in the mixed determinant bound |
| `CatalanMeasure/WeightedEnergy.lean`, `WeightedBounds.lean`, `WeightedCaseOne.lean`, `WeightedDualTwo/` | two fixed weighted endpoint certificates and their quadratic mass bound |
| `CatalanMeasure/WeightedLemma6.lean` | perturbation with `ρ = 392.5`, and the 7891/22494 bounds |
| `CatalanMeasure/FixedNodes.lean`, `FixedNodeMajorant.lean`, `FixedNodeLemma6.lean` | retain the fixed-node decay by a quartic inequality; perturbation with `ρ = 370.4`, yielding 7447/21228 |
| `CatalanMeasure/SeparateFixedNodes.lean`, `SeparateFixedMajorant.lean`, `SeparateBounds.lean`, `SeparateLemma6.lean` | separate the two fixed-node caps, sharpen the quadratic case-one margin; perturbation with `ρ = 366.3`, yielding the historical 7364/20993 checkpoint |
| `CatalanMeasure/SquareNonvanishing.lean`, `SquarePNTWindow.lean`, `SquareMain.lean` | nonvanishing when p² does not divide the denominator; halves the PNT prime-window surcharge, yielding 7181/20993 |
| `CatalanMeasure/Parametric/Sparse*.lean`, `ChebyshevPrime.lean`, `FiveSourceElimination.lean` | uniform sparse prime-row dependencies and determinant valuation savings; the earlier proposed-parameter experiments remain separate from the selected twenty-row proof |
| `CatalanMeasure/SparsePrimeGain.lean`, `SparseGainPNT.lean`, `SparseDenominators.lean`, `SparseDenominatorGrowth.lean`, `SparseMain.lean` | exact gain integral, improved common denominator, and the historical 2742/7675 bounds |
| `CatalanMeasure/Parametric/EarlySparseValuation.lean`, `ResidueRank.lean`, `SparseCombinationRank.lean` | actual residue rank and early-window determinant saving, with explicit injective row-combination maps |
| `CatalanMeasure/DensePrimeGain.lean`, `DenseGainPNT.lean`, `DenseDenominators.lean`, `DenseDenominatorGrowth.lean`, `DenseMain.lean` | gain integral 20/3, denominator saving 5/1728, and the 1981/5391 bounds |
| `OAI/` | the parts of OpenAI's formalization that are used (vendored; see below) |
| `PrimeNumberTheoremAnd/` | the files OpenAI adds to PrimeNumberTheoremAnd (vendored; see below) |

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
digits (the computations themselves are unchanged; see `NOTICE` and `CatalanMeasure/SharpBarrier.lean`).
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
lake build
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
criterion giving 1099 were also developed with Codex. Sean Litsey posed the problem,
directed the work, and is responsible for this repository. The vendored code is OpenAI's (see
above).

## Submission

This repository follows the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate).
Submissions to the registry go through the form at https://submit.palomar-registry.org/.

## Licence

Apache License 2.0; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
