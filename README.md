# An irrationality measure for Catalan's constant

A Lean 4 formalization of the following theorem.

> **Theorem.** Let `G = ∑_{j ≥ 0} (-1)^j / (2j+1)^2` be Catalan's constant. For every integer
> `a` and every sufficiently large integer `b`,
>
> `|G - a/b| > b^(-34000)`.
>
> So the irrationality exponent of `G` is at most `34000`. With Chebyshev's bounds in place of
> the prime number theorem in the final step, the argument gives `b^(-100800)`.

The proof builds on [OpenAI's proof](https://github.com/openai/math) that `G` is irrational and
on its Lean formalization. The companion paper, S. Litsey, *An irrationality measure for
Catalan's constant* (2026), Hexagon preprint `hexagon:2610.00187v1`, is in [`paper/`](paper/)
(LaTeX source and PDF). R. K. Jha proved earlier, independently, the weaker bound
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

## Structure of the proof

| Directory or file | Content |
|---|---|
| `CatalanMeasure/DeltaPoly.lean`, `Degree.lean` | OpenAI's determinant as a polynomial `Δ_N(X)` in the constant; `deg Δ_N ≤ 44N` |
| `CatalanMeasure/Denominators.lean`, `IntegerValued.lean`, `Integrality.lean` | a common denominator `D_N` for `Δ_N` at integers, with `log D_N ≤ (A + ε) n²`; integer-valued polynomials; `Q_N = (44N)! D_N Δ_N ∈ ℤ[X]` |
| `CatalanMeasure/Nonvanishing.lean` | `Δ_p(a/b) ≠ 0` for large primes `p ∤ b` |
| `CatalanMeasure/PrimeWindow.lean`, `Criterion.lean`, `PNTWindow.lean`, `Main.lean` | the irrationality-measure criterion, with Chebyshev and prime-number-theorem prime windows |
| `CatalanMeasure/Quadrature.lean`, `ChebyshevNodes.lean` | quadrature formula for the coefficient of the constant, at the roots of `T_J` moved to `[-1, 0]` |
| `CatalanMeasure/DetExpansion.lean` | column expansion of `det(A + δΦβ)` |
| `CatalanMeasure/MixedAndreief.lean` | Andréief's identity with fixed point columns |
| `CatalanMeasure/GenVandermonde.lean`, `GenVandermondeSharp.lean` | `|det[s_l^{E_i}]| ≤ 2^{p(n-p)} |V(s)|` for nodes in `[0, 1]` |
| `CatalanMeasure/PinMajorant.lean`, `PinDampedDual.lean`, `PinSupDual.lean` | pointwise bound for the mixed integrands; OpenAI's energy dual for `p ≤ n` points |
| `CatalanMeasure/SharpBarrier.lean` | OpenAI's real-place constant read to seven digits: `U = 2.2910468 - (log 2)/2` |
| `CatalanMeasure/Lemma6.lean` | the perturbation estimate with `ρ = 412`, and the final theorems |
| `OAI/` | the parts of OpenAI's formalization that are used (vendored; see below) |
| `PrimeNumberTheoremAnd/` | the files OpenAI adds to PrimeNumberTheoremAnd (vendored; see below) |

## Vendored code

Palomar requires Lean v4.35.0-rc2 or later, and every file a submission imports must use Lean's
module system. OpenAI's repository is pinned to Lean v4.34.1 and does not use modules, so it
cannot be imported directly. The 478 files of OpenAI's formalization that this proof uses (from
commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` of
[openai/math](https://github.com/openai/math)) and the 10 files that OpenAI adds to
PrimeNumberTheoremAnd are therefore copied here. Each was converted mechanically to a module (a
`module` header, `public import`s, `@[expose] public section`) and adjusted where needed for
the newer Lean and Mathlib (see [`PORTING.md`](PORTING.md)). In 37 point-evaluation files of
OpenAI's second-barrier certificate the comparison constants were sharpened from five to seven
digits (the computations themselves are unchanged; see `NOTICE` and `CatalanMeasure/SharpBarrier.lean`).
Otherwise their mathematical content is unchanged. Licences and attributions are in [`NOTICE`](NOTICE); all of this code is under the
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

Building OpenAI's code takes a while (roughly an hour on a few cores, after the Mathlib
cache). The comparator script needs Linux and `bwrap` (bubblewrap).

## Authorship and use of AI

The mathematics, all of the Lean code in `CatalanMeasure/`, `Challenge.lean` and
`Solution.lean`, the module conversion, and the companion paper were produced by the AI system
Claude Opus 5.5 (Anthropic) at the request of Sean Litsey. Sean Litsey posed the problem,
directed the work, and is responsible for this repository. The vendored code is OpenAI's (see
above).

## Submission

This repository follows the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate).
Submissions to the registry go through the form at https://submit.palomar-registry.org/.

## Licence

Apache License 2.0; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
