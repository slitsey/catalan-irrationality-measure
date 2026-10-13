# An irrationality measure for Catalan's constant

A Lean 4 formalization of the following theorem.

> **Theorem.** Let `G = ∑_{j ≥ 0} (-1)^j / (2j+1)^2` be Catalan's constant. For every integer
> `a` and every sufficiently large integer `b`,
>
> `|G - a/b| > b^(-1981)`.
>
> So the irrationality exponent of `G` is at most `1981`. With Chebyshev's bounds in place of
> the prime number theorem in the final step, the argument gives `b^(-5391)`.

The proof builds on [OpenAI's proof](https://github.com/openai/math) that `G` is irrational and
on its Lean formalization. The companion paper, S. Litsey, *An irrationality measure for
Catalan's constant* (2026), has revised LaTeX source and PDF in [`paper/`](paper/). The earlier 8127 version was
Hexagon preprint `hexagon:2610.00187v1`; this repository update does not upload a new preprint version. R. K. Jha proved earlier, independently, the weaker bound
`μ(G) ≤ 10^8` ([doi:10.5281/zenodo.23237269](https://doi.org/10.5281/zenodo.23237269)).

## What to read

- [`Challenge.lean`](Challenge.lean) states the two theorems using Mathlib only, with Catalan's
  constant written out as a series. This is the whole trusted statement surface.
- [`Solution.lean`](Solution.lean) proves them from the development.
- [`comparator.json`](comparator.json) tells `lake comparator` to check that `Solution` proves
  exactly the statements of `Challenge`, using only `propext`, `Quot.sound` and
  `Classical.choice`.
- [`formalization.yaml`](formalization.yaml) records provenance, authorship, automation and
  scope.

The arithmetic refinement proves uniform six-row relations and linear combinations
of those relations in the leading prime residues of the actual determinant. The
combined window `18N <= p <= 21N` saves a continuous trapezoid of exact integral
`20/3`. Rank-nullity supplies `3p-54N` independent relations in the earlier window;
this is a uniform proof, not a numerical rank assumption. The resulting decay rate
`η = 8.969` yields 1981 and 5391 with the existing perturbation exponent `ρ = 366.3`.
Both new bounds pass Lean's main kernel and the standard-axiom audit.
Independent-kernel and comparator acceptance remain pending.

## Structure of the proof

| Directory or file | Content |
|---|---|
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
| `CatalanMeasure/Parametric/Sparse*.lean`, `ChebyshevPrime.lean`, `FiveSourceElimination.lean` | uniform sparse prime-row dependencies and determinant valuation savings; exploratory proposed-parameter modules are not needed by the final 1981 theorem |
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
refinement, endpoint certificates, separate fixed-node decay inequalities, quadratic case refinement, integer certificate soundness proofs, square-denominator nonvanishing and prime-window refinement, dependency refactor and corresponding paper revisions were
developed with OpenAI Codex at his request. Sean Litsey posed the problem,
directed the work, and is responsible for this repository. The vendored code is OpenAI's (see
above).

## Submission

This repository follows the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate).
Submissions to the registry go through the form at https://submit.palomar-registry.org/.

## Licence

Apache License 2.0; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
