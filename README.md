# Irrationality measures for Catalan's constant and related constants

A Lean 4 formalization of four irrationality measures. Let `G = ∑_{j ≥ 0} (-1)^j / (2j+1)^2` be
Catalan's constant and `L(2, χ₋₃) = ∑_{k ≥ 0} (1/(3k+1)^2 − 1/(3k+2)^2)`.

> **Theorem.**
>
> - μ(G) ≤ 728;
> - μ(G − 5π²/48) ≤ 32.44;
> - μ(G + 5π²/48) ≤ 32.44;
> - μ(L(2, χ₋₃)) ≤ 14.35.

For `G` this means `|G − a/b| > b^(-728)` for every integer `a` and every sufficiently large
integer `b`. For the other three constants `x` with exponent `E` it means: for every `e > 0`,
`|x − p/q| > q^(-(E+e))` for all large `q` and all `p` coprime to `q`.

All four proofs are kernel-checked in Lean and use only the axioms `propext`, `Quot.sound` and
`Classical.choice`.

## Papers

- S. Litsey, *An irrationality measure for Catalan's constant* (2026): LaTeX source and PDF in
  [`paper/`](paper/) (`catalan-measure-hexagon.tex` is the single-file version), Hexagon preprint
  `hexagon:2610.00187`.
- S. Litsey, *Irrationality measures for G ± 5π²/48 and L(2, χ₋₃)* (2026): LaTeX source and PDF in
  [`paper-lambda/`](paper-lambda/) (`lambda-irrationality-hexagon.tex` is the single-file version),
  Hexagon preprint [`hexagon:2610.00401`](https://hexagonmath.org/2610.00401).

The proofs build on OpenAI's proof that `G` is irrational and on its Lean formalization
([openai/math](https://github.com/openai/math); preprint dated September 24, 2026, released
October 6, 2026). Other bounds in the literature:
- R. K. Jha proved `μ(G) ≤ 10^8` independently ([doi:10.5281/zenodo.23237269](https://doi.org/10.5281/zenodo.23237269)).
- M. C. S. Carreira reports `μ(G) < 2715` with another determinant design ([doi:10.5281/zenodo.23326325](https://doi.org/10.5281/zenodo.23326325)).
- For `L(2, χ₋₃)`, Calegari, Dimitrov and Tang give 24781 (arXiv:2510.04156, Theorem 5.1).

## What to read

| File | Content |
|---|---|
| [`Challenge.lean`](Challenge.lean), [`ChallengeHybrid.lean`](ChallengeHybrid.lean) | the four statements, using Mathlib only, with the constants written as series. This is the whole trusted statement surface |
| [`Solution.lean`](Solution.lean), [`SolutionHybrid.lean`](SolutionHybrid.lean) | their proofs |
| [`comparator.json`](comparator.json), [`comparator-hybrid.json`](comparator-hybrid.json) | configurations for `lake comparator`, stating that each `Solution` proves exactly the statements of its `Challenge` with the three permitted axioms. Comparator has not yet been run on them (it requires Linux); the axiom check was done with `#print axioms` |
| [`formalization.yaml`](formalization.yaml), [`formalization-hybrid.yaml`](formalization-hybrid.yaml) | provenance, authorship, automation and scope |

## The bound for G

OpenAI's construction is used with a determinant of size `20N`, whose value is a polynomial of
degree at most `18N` in the constant. A Gauss-type quadrature formula and an Andréief identity with
fixed points bound this polynomial on an interval of length `exp(−ρN)` around `G`, with
`ρ = 259299/2500`. Rank deficiencies of the reduced matrix modulo the primes in `(52N/9, 44N/7)`,
`(8N, 9N)` and `(4N, 9N/2)`, proved with Chebyshev identities in characteristic `p`, make every
coefficient divisible by a common factor of logarithm at least `0.649 N²`. Prime squares in the
denominator of a rational approximation are recovered from the coefficients, and the largest
admissible prime is chosen. The energy estimate uses trial sequences with 640 Chebyshev
coefficients and 56 geometric terms, 22 of them complex: logarithmic potentials of point charges
placed near the edges of the support of the extremal measure. Their fields are bounded on cells with
an exact local Taylor expansion. The margin is `η = 64169/25000`, and the limiting exponent is
`18ρ/η = 46673820/64169 = 727.357…`.

The Lean development is in `CatalanMeasure/G728/` (cells, norms, budgets, final assembly) and
`CatalanMeasure/Parametric/` (the determinant of size `20N`, rank deficiencies, divisibility of the
coefficients and the choice of the prime).

## The bounds for G ± 5π²/48 and L(2, χ₋₃)

These proofs use rectangular Löwner matrices of digamma differences, in the libraries `CatalanCore/`
and `CatalanFrames/`, with nonvanishing proved modulo a prime or by characteristic-zero selection,
and decay proved with Cauchy determinants and Andréief's identity.

- **G ± 5π²/48 (32.44).** The content constant is bounded by `p`-adic assignment problems, rank
  deficits modulo `p`, a uniform rescaled-core deficit and a second-level deficit at primes where
  the leading block is not clean: `Λ ≤ 2015079667893797/547747200000000 < 3.67885`. The decay
  certificate has contour rays of slope 5/2, `ρ = 1/4096` and atoms placed on the support of an
  extremal dual measure (`D ≥ 3.90557`, `c ≤ 7.3546`). Lean theorems: `lam_hybrid_measure_3244`,
  `mir_hybrid_measure_3244`.
- **L(2, χ₋₃) (14.35).** Characteristic-zero selection with at most one common-node deletion
  allows a quarter border. With the saving at small primes, the content constant is
  `Λ = 339258406689121/82516315939200`. A kernel-checked certificate with 1600 atoms gives
  `D ≥ 4.633628` and `c = 7.49256`, so `c/(D − Λ) = 14.3475713…`. Lean theorem:
  `chi3_hybrid_measure_1435`. The exact certificate data are in
  [`paper-lambda/certificates/`](paper-lambda/certificates/).

## Kernel-checked certificates

All numerical bounds are ordinary kernel-checked rational and integer certificates
(`decide +kernel`; no `native_decide`). Large certificates are split into many small declarations
with explicit intermediate values, chained by general lemmas. Integer recurrences whose values are
divisible by large powers of 2 (the Clenshaw and Chebyshev recurrences in
`CatalanMeasure/G728/ZNorm.lean` and `MGNorm.lean`) are checked on the quotients by those powers,
with one lemma relating the two. The generators are in [`scripts/`](scripts/); the authoritative
proof data are the Lean source literals.

## Vendored code

Palomar requires Lean v4.35.0-rc2 or later, and every imported file must use Lean's module
system. OpenAI's repository is pinned to Lean v4.34.1 and does not use modules, so the 479 files of
OpenAI's formalization used here (from commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` of
[openai/math](https://github.com/openai/math)) and the 10 files that OpenAI adds to
PrimeNumberTheoremAnd are copied into `OAI/` and `PrimeNumberTheoremAnd/`. Each was converted to a
module and adjusted for the newer Lean and Mathlib (see [`PORTING.md`](PORTING.md)). In 37
point-evaluation files of OpenAI's certificate the comparison constants are given to seven digits
(the computations are unchanged; see `NOTICE`). Licences and attributions are in
[`NOTICE`](NOTICE); all of this code is under the Apache License 2.0.

The directory `archive/` holds Lean modules that the four theorems do not import. It is not part of
the default build and is not used by any proof above.

## Building and checking

You need [elan](https://github.com/leanprover/elan) and several GiB of free disk.

```text
lake exe cache get
python3 scripts/check-lean-sources.py
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

The numerical checks can use several GiB per Lean process; use a small worker count (for example
`LEAN_NUM_THREADS=2`) on memory-constrained machines. The comparator script needs Linux and `bwrap`
(bubblewrap).

## Authorship and use of AI

The mathematics, Lean development, certificate generators and papers were produced by AI systems at
the request of Sean Litsey, who posed the problems, directed the work and is responsible for this
repository.

- **Claude Opus 5.5 and Claude Sonnet 5.5 (Anthropic)** produced:
  - for `G`: the measure framework and the perturbation estimate by quadrature; the rank
    deficiencies at the primes in `(8N, 9N)` and `(4N, 9N/2)` with their consequences for the
    coefficients; the trial sequences with complex geometric terms and their verification on cells;
    the final assembly; and the module conversion of OpenAI's formalization;
  - for `G ± 5π²/48` and `L(2, χ₋₃)`: the rectangular frames, the content bounds and rank deficits,
    the nonvanishing argument and the decay certificates; the second-level deficit at non-clean
    primes; the decay estimate with the slope of the contour rays as a parameter, and the
    certificate with atoms placed on the support of an extremal dual measure;
  - the corresponding Lean proofs and the two papers.
- **OpenAI Codex** produced:
  - for `G`: the determinant of size `20N` with its local arithmetic and nonvanishing; the energy
    estimates with fixed columns and the first trial; the quadrature nodes and the weight bound;
    the divisibility of the coefficients by prime squares and the choice of the largest admissible
    prime; the rank deficiency at the primes in `(52N/9, 44N/7)`;
  - for `L(2, χ₋₃)`: the valuation-one reduction, bounded-deletion transfer, the periodic content
    profile, the quarter border with characteristic-zero selection, the analytic certificate and
    the saving at small primes;
  - for `G ± 5π²/48`: the uniform rescaled-core argument with its finite interval profile;
  - the repository infrastructure, the corresponding Lean proofs and paper text.

The vendored code is OpenAI's (see above).

## Submission

This repository follows the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate).
Submissions to the registry go through the form at https://submit.palomar-registry.org/.

## Licence

Apache License 2.0; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
