# Irrationality measures for Catalan's constant and related constants

A Lean 4 formalization of five irrationality measures. Let `G = ∑_{j ≥ 0} (-1)^j / (2j+1)^2` be
Catalan's constant and `L(2, χ₋₃) = ∑_{k ≥ 0} (1/(3k+1)^2 − 1/(3k+2)^2)`.

> **Theorem.**
>
> - μ(G) ≤ 590;
> - μ(G − 5π²/48) ≤ 32.44;
> - μ(G + 5π²/48) ≤ 32.44;
> - μ(L(2, χ₋₃)) ≤ 14.35;
> - μ(L(2, χ₋₃) ± π²/9) ≤ 10.61 (both signs).

For `G` this means `|G − a/b| > b^(-590)` for every integer `a` and every sufficiently large
integer `b`. For the other constants `x` with exponent `E` it means: for every `e > 0`,
`|x − p/q| > q^(-(E+e))` for all large `q` and all `p` coprime to `q`.

All proofs are kernel-checked in Lean and use only the axioms `propext`, `Quot.sound` and
`Classical.choice`.

## Papers

- S. Litsey, *An irrationality measure for Catalan's constant* (2026): LaTeX source and PDF in
  [`paper/`](paper/) (`catalan-measure-hexagon.tex` is the single-file version), Hexagon preprint
  `hexagon:2610.00187`.
- S. Litsey, *Irrationality measures for G ± 5π²/48, L(2, χ₋₃) and L(2, χ₋₃) ± π²/9* (2026): LaTeX source and PDF in
  [`paper-lambda/`](paper-lambda/) (`lambda-irrationality-hexagon.tex` is the single-file version),
  Hexagon preprint [`hexagon:2610.00401`](https://hexagonmath.org/2610.00401).

The proofs build on OpenAI's proof that `G` is irrational and on its Lean formalization
([openai/math](https://github.com/openai/math); preprint dated September 24, 2026, released
October 6, 2026). Other bounds in the literature:
- R. K. Jha proved `μ(G) ≤ 10^8` independently ([doi:10.5281/zenodo.23237269](https://doi.org/10.5281/zenodo.23237269)).
- M. C. S. Carreira obtains `μ(G) < 2294` with another determinant design ([doi:10.5281/zenodo.23532239](https://doi.org/10.5281/zenodo.23532239)).
- For `L(2, χ₋₃)` and its combinations with `π²`, Calegari, Dimitrov and Tang give 24781 (arXiv:2510.04156, Theorem 5.1 and the remark after it).

## What to read

| File | Content |
|---|---|
| [`Challenge.lean`](Challenge.lean), [`ChallengeHybrid.lean`](ChallengeHybrid.lean) | the five statements, using Mathlib only, with the constants written as series. This is the whole trusted statement surface |
| [`Solution.lean`](Solution.lean), [`SolutionHybrid.lean`](SolutionHybrid.lean) | their proofs |
| [`comparator.json`](comparator.json), [`comparator-hybrid.json`](comparator-hybrid.json) | configurations for `lake comparator`, stating that each `Solution` proves exactly the statements of its `Challenge` with the three permitted axioms. Comparator has not yet been run on them (it requires Linux); the axiom check was done with `#print axioms` |
| [`CatalanMeasure/GenD/`](CatalanMeasure/GenD/) | the proof for `G`: the generic layer for an arbitrary design (denominators, rank deficiencies, quadrature, criterion) and `GenD/D58/` for the design (58, 9, 3, 5, 3) |
| [`formalization.yaml`](formalization.yaml), [`formalization-hybrid.yaml`](formalization-hybrid.yaml) | provenance, authorship, automation and scope |

## The bound for G

OpenAI's determinant construction is carried out for an arbitrary design `(n₀, b₀, q₀, g₀, h₀)` of five
integers. The design used here is `(58, 9, 3, 5, 3)`: the determinant has size `58N` and, as a
polynomial in the constant, degree `53N`. For every design the reduction modulo a prime `p` of the
matrix of rational parts has a kernel whose dimension is bounded below by explicit piecewise linear
functions of `p` on four windows of primes (`12N < p ≤ 26N` for this design); proved with
antisymmetric row combinations, a reflection of Chebyshev polynomials modulo `p` and Frobenius
relations, they lower the denominator of the determinant by `35369/1848` in units of `N²`. A
Gauss-type quadrature formula with `53N` nodes and an Andréief identity with fixed points bound the
determinant on an interval of length `exp(−ρN)` around `G`, with `ρ = 301.54258…`. The energy
estimate uses trial sequences with 160 Chebyshev coefficients and 75 geometric terms, 41 of them
complex: logarithmic potentials of point charges near the edges of the support of the extremal
measure, bounded on cells (373, 302 and 176 in the three covers) with an exact local Taylor
expansion. The decay rate is `η = 27.124717…`, and the criterion, with a free lower end `(κ − 3/4) log b`
of the window of primes and `κ = 1.9566…`, gives the limiting exponent `53ρ/η = 589.19…`; the integer 590
is the one proved. Details are in [`paper/`](paper/).

The Lean development is in `CatalanMeasure/GenD/` (the generic layer: denominators, rank deficiencies,
nonvanishing, the criterion and the budget interface; `GenD/D58/`: the design, the bank of constants
`Budget590`, the certificates `Cert590/` and `FirstCert/`, and the assembly `Main590`) and
`CatalanMeasure/Parametric/` (the determinant, rank deficiencies and the choice of the prime).

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

## The thirds frames: L(2, χ₋₃) ± π²/9

The digamma differences `ψ(z+1) − ψ(z+s)` with shifts `s = 1/3, 2/3` give `ψ'(1/3) = 2π²/3 + 9L/2` and
`ψ'(2/3) = 2π²/3 − 9L/2` with `L = L(2, χ₋₃)`, hence the numbers `L ± π²/9 = L ± (2/3)ζ(2)`. The rational
kernel is `M[a,b] = −e/(9(b−a)) · Σ 1/(k(3k−e))` (`e = 2` for `s = 1/3`, `e = 1` for `s = 2/3`), with
the denominators `k(3k−e)` and zeros modulo a prime power near `q/3` and `2q/3`. With the quarter
border and characteristic-zero selection of the `L(2, χ₋₃)` bound, the content constant is the
exact table value `Λ = 43074084803/13330437120 = 3.2312582…`. The decay certificate has the same form as
the slope-5/2 certificate, with its own measure of 2950 atoms on the segment, the rays and the line:
`D ≥ 3.87115` and `c = 6.78788`, so `c/(D − Λ) = 10.6078…`. Lean theorems:
`chi3_plus_pi2_hybrid_measure_1061` and `chi3_minus_pi2_hybrid_measure_1061`; the frames and the content
tables are in `CatalanFrames/Thirds/`, the certificate in `CatalanCore/Cert/SigmaThirds/`. The derivation is in [`paper-lambda/thirds-shift.tex`](paper-lambda/thirds-shift.tex).

## Kernel-checked certificates

All numerical bounds are ordinary kernel-checked rational and integer certificates
(`decide +kernel`; no `native_decide`). Large certificates are split into many small declarations
with explicit intermediate values, chained by general lemmas. Integer recurrences whose values are
divisible by large powers of 2 (the Clenshaw and Chebyshev recurrences in
`CatalanMeasure/Cert/`) are checked on the quotients by those powers,
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

The directory `archive/` holds Lean modules that the theorems above do not import. It is not part of
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

The mathematics, the Lean formalization, the certificate generators and the text were produced by AI systems at the request of the author, who posed the problems, directed the work and is responsible for it: Claude Opus 5.5, Claude Sonnet 5.5 and Claude Haiku 5.5 (Anthropic), running in Claude Code, and GPT-6.1 Sol (OpenAI), running in Codex. The underlying irrationality proof for G and its Lean formalization are OpenAI's.

The vendored code is OpenAI's (see above).

## Submission

This repository follows the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate).
Submissions to the registry go through the form at https://submit.palomar-registry.org/.

## Licence

Apache License 2.0; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
