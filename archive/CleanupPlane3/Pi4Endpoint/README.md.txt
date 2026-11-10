# Irrationality measures for Catalan's constant and related constants

A Lean 4 formalization of irrationality measures for Catalan's constant and, by a construction with Löwner
determinants, for three planes of constants and further related constants. Let `G = ∑_{j ≥ 0} (−1)^j / (2j+1)^2` be Catalan's constant,
`L₋₃ = L(2, χ₋₃) = ∑_{k ≥ 0} (1/(3k+1)^2 − 1/(3k+2)^2)` the Calegari–Dimitrov–Tang constant, and
`ψ′(x) = ∑_{n ≥ 0} 1/(n+x)^2` the trigamma function, so that `ψ′(1) = ζ(2) = π²/6`. The irrationality exponent `μ(ξ)` of a real number
`ξ` is the infimum of the `μ` such that `|ξ − p/q| > q^(−μ)` for all integers `p` and all sufficiently
large integers `q`.

> **Theorem.**
>
> - μ(G) ≤ 270;
> - μ(a L₋₃ + b π²) ≤ 20.6622 for all rationals a, b, not both zero;
> - μ(L₋₃) ≤ 13.6839;
> - μ(L₋₃ ± π²/9) ≤ 9.4913, μ(L₋₃ ± 2π²/27) ≤ 14, μ(L₋₃ ± π²/27) ≤ 15.359 and
>   μ(L₋₃ ± π²/18) ≤ 17.492, for both signs;
> - μ(a ζ(3) + b π²) ≤ 335.20 for all rationals a, b, not both zero;
> - μ(a ζ(3) + b π⁴) ≤ 118 for all rationals a, b, not both zero, including μ(π⁴) ≤ 118;
> - μ(ζ(3)) ≤ 6.0382 and μ(π²) ≤ 6.5214 (weaker than the known bounds, included for completeness);
> - μ(G ± 5π²/48) ≤ 31.1973, for both signs;
> - μ(ψ′(a/5) − π²/6) ≤ 23.7756 for a = 1, 2, 3, 4;
> - μ(ψ′(a/7) − π²/6) ≤ 1806.1719 for a = 1, …, 6.

Each Lean statement has the same form. For a number `x` with exponent `μ` above, it is `|x − a/b| > b^(−μ)`
for every integer `a` and every sufficiently large integer `b`. The three plane theorems take the rational
coefficients as arguments and write the fraction as `p/q`. Each statement implies that the number is
irrational. As far as we know, the bound for `a ζ(3) + b π²` is the first irrationality measure valid on the
whole plane. The third plane and π⁴ endpoint illustrate the same construction with poles of order three; no best-known bound is claimed for π⁴.

All proofs are kernel-checked in Lean and use only the axioms `propext`, `Quot.sound` and
`Classical.choice`.

## Papers

- S. Litsey, *An irrationality measure for Catalan's constant* (2026), the proof of μ(G) ≤ 270: LaTeX
  source and PDF in [`paper/`](paper/) (`catalan-measure-hexagon.tex` is the single-file version),
  Hexagon preprint [`hexagon:2610.00187`](https://hexagonmath.org/2610.00187).
- S. Litsey, *Irrationality measures from Löwner determinants* (2026), the other
  measures: LaTeX source and PDF in [`paper-trigamma/`](paper-trigamma/) (`trigamma-irrationality-hexagon.tex`
  is the single-file version), Hexagon preprint [`hexagon:2610.00401`](https://hexagonmath.org/2610.00401).

Both papers build on OpenAI's proof that `G` is irrational ([openai/math](https://github.com/openai/math);
preprint dated September 24, 2026, released October 6, 2026), and the proof of μ(G) ≤ 270 also builds on
its Lean formalization. Other bounds in the literature:
- For `G`, R. K. Jha proved μ(G) ≤ 10^8 ([doi:10.5281/zenodo.23237269](https://doi.org/10.5281/zenodo.23237269)).
  M. C. S. Carreira treated the five parameters of OpenAI's construction as free and obtained μ(G) < 2294
  ([doi:10.5281/zenodo.23532239](https://doi.org/10.5281/zenodo.23532239)); H. S. Bojnal instantiated his
  general theorem at the design (36, 6, 2, 3, 2) to obtain μ(G) < 2401.74
  ([proof-factory/catalan-exponent](https://github.com/proof-factory/catalan-exponent)). R. Xu reported
  μ(G) ≤ 727.03 for the design (20, 3, 1, 2, 1), with a numerical certificate in ball arithmetic that is
  not formalized ([issue #5](https://github.com/slitsey/catalan-irrationality-measure/issues/5)).
  C. Davis obtained μ(G) ≤ 528.23288 with the design and arithmetic of this repository and new quadrature
  nodes, formalized in Lean ([1337isnot1337/catalan-constant](https://github.com/1337isnot1337/catalan-constant));
  the MultiAgency agent swarm regenerated Davis's polynomial and reached μ(G) ≤ 528.2315, also formalized in Lean
  ([darkhipo/catalan-constant-gen5](https://github.com/darkhipo/catalan-constant-gen5)). The proof of
  μ(G) ≤ 270 uses its own quadrature nodes and two of Davis's Lean files (commit `3c45153`, Apache License 2.0),
  `GeneralNodalWeights` and `NodalRootDeletion`, which bound the weights of nodal polynomials. They are ported
  unchanged into [`CatalanMeasure/GenD/Signed/Davis/`](CatalanMeasure/GenD/Signed/Davis/); the other 31 ported
  files are in `archive/` and are not part of the build. See [`NOTICE`](NOTICE) and `PROVENANCE.json` there.
- For `L₋₃` and its rational linear combinations with `π²`, Calegari, Dimitrov and Tang give
  24781 (arXiv:2510.04156, Theorem 5.1 and the remark after it).
- We know of no earlier irrationality result for `G ± 5π²/48`, `ψ′(a/5) − ζ(2)` or `ψ′(a/7) − ζ(2)`.

## What to read

| File | Content |
|---|---|
| [`Challenge.lean`](Challenge.lean), [`ChallengeHybrid.lean`](ChallengeHybrid.lean) | the twenty-six statements, using Mathlib only, with the constants written as series: μ(G) ≤ 270 in `Challenge.lean` (namespace `CatalanIrrationalityMeasure`) and the other twenty-five in `ChallengeHybrid.lean` (namespace `TrigammaDifferences`). This is the whole trusted statement surface |
| [`Solution.lean`](Solution.lean), [`SolutionHybrid.lean`](SolutionHybrid.lean) | their proofs, each file ending with `#print axioms` for its theorems |
| [`comparator.json`](comparator.json), [`comparator-hybrid.json`](comparator-hybrid.json) | configurations for `lake comparator`, stating that each `Solution` file proves exactly the statements of its `Challenge` file with the three permitted axioms. The `comparator` job of the CI workflow [`.github/workflows/ci.yml`](.github/workflows/ci.yml) runs [`scripts/verify-comparator.sh`](scripts/verify-comparator.sh) on `comparator.json`, with Lean's kernel and the NanoDa kernel bundled with the toolchain, the two kernels Palomar requires; the manually dispatched workflow [`comparator-timing.yml`](.github/workflows/comparator-timing.yml) times the same check with each external kernel separately. `comparator-hybrid.json` is not run in CI. The proofs are kernel-checked; μ(G) ≤ 270 has not been run through `lake comparator` |
| [`CatalanMeasure/GenD/`](CatalanMeasure/GenD/) | the proof of μ(G) ≤ 270 |
| [`CatalanCore/Uniform/`](CatalanCore/Uniform/) | the proofs of the plane theorems and the other measures |
| [`formalization.yaml`](formalization.yaml), [`formalization-hybrid.yaml`](formalization-hybrid.yaml) | provenance, authorship, automation and scope |

## Catalan's constant: μ(G) ≤ 270

OpenAI's proof compares, for a determinant whose entries are linear forms in `1` and `G`, a lower bound
coming from its denominators with an upper bound coming from an integral representation. The construction
depends on five integer parameters `(n₀, b₀, q₀, g₀, h₀)`, a *design*, and the arguments are carried out
for an arbitrary design, except for the numerical data. The design used is `(58, 9, 3, 5, 3)`: the
determinant has size `58N`, and as a polynomial in the constant it has degree at most `53N`.

- **Corank modulo p.** At a prime `p` each unit of corank of the matrix of rational parts lowers the
  denominator by a factor `p`. Closed formulas, proved for every design with antisymmetric row
  combinations, a reflection formula for Chebyshev polynomials modulo `p` and the relation
  `(1 − X)^p = 1 − X^p`, bound the corank on a range of large primes. All these kernels come from one
  counting inequality: a space of row combinations, with a few linear conditions that make every entry
  of the combined row vanish modulo `p`. On the remaining intervals of primes the inequality is applied to
  every constant subspace at once. Only upper bounds for ranks are then needed, and these come from forced
  intersections of row spaces. Together they give a piecewise linear profile whose area, at least
  `22.0607` in units of `N²`, is the gain in the denominators.
- **A bound for the row determinant.** OpenAI's integrand contains a determinant `det L` of size `n` that
  the energy method bounds by `e^(O(n log n))`. A phase inequality for Pick matrices shows that `det L` loses only a
  factor `499ⁿ` when the weight `−5` of the positive nodes is replaced by `0`, as soon as one phase
  statistic of the nodes is large enough. The proof interpolates the data of a singular Pick matrix by a
  finite Blaschke product and follows its argument along an arc of the unit circle. The statistic is large
  on every configuration close to the maximum of OpenAI's energy, and OpenAI's bound suffices on the
  others. With weight `0` the determinant factors through two Gram determinants. Fischer's inequality and
  a finite Andréief identity bound it by two logarithmic gases, one in the plane and one in the Joukowski
  coordinate, and tangent inequalities against fixed reference measures bound the gases. This adds `24.64`
  in units of `N²` to the decay rate.
- **The neighbourhood of G.** A quadrature formula with `53N` nodes extends the bound to
  `|x − G| ≤ e^(−ρN)` with `ρ = 278.376313578`. The nodes are Chebyshev nodes of 106 short intervals with
  dyadic end points, and their Lagrange polynomials are bounded by the Green functions of the intervals.
  The cost is paid column by column. The weight of each replaced column and its generalized Vandermonde
  factor are bounded together. A weighted Hadamard inequality with the parameter `ζ = 3/4` makes the
  dependence on the column cancel, and one contour of radius `3/4` serves all columns, by concavity along
  the circle. The part of the weight that depends on the node is bounded by a chord table and carried into
  the energy bound as an external field.
- **Criterion.** For large `N` the integer polynomials obtained by clearing denominators are at most
  `e^(−ηN²)` on that neighbourhood, with `η = 54.68745`. A criterion with a free lower end of the window
  of primes, which uses the largest prime of the window whose square does not divide `b`, gives
  `|G − a/b| > b^(−270)`. Its last condition reads `270 > dρ/(η − 4dδ) = 269.78696…` with `d = 53` and
  `δ = 2.9·10⁻⁷`. The prime number theorem enters through the denominators and the choice of the prime.

The energy estimates use trial sequences whose generating functions are logarithmic potentials of point
charges near the edges of the support of the extremal measure. When some columns are prescribed, the trial
sequences move linearly with the fraction of prescribed columns, so their fields are bounded by chords
between two end points. The fields are bounded by isolating the critical points and by covers by cells, as
kernel-checked rational inequalities. The reference measures of
the row determinant are piecewise uniform on finitely many cells, completed by auxiliary measures on 16
circles. Their fields are bounded by polynomial majorants, and each majorant by an exact sum of squares
identity between Chebyshev series.

In Lean, `CatalanMeasure/GenD/` is the design-generic layer: the denominators, the closed formulas
(`t_rank`, `u_rank`, `u6_rank_closed`, `s_rank`), the nonvanishing, the real place (`Analytic/`, `Cert/`)
and the criterion. `GenD/Uniform/W/` contains the counting inequality (`w_core`).
`GenD/Signed/Count/` applies it to every constant subspace and assembles the profile (`Count.LedgerContent.content`).
`GenD/DesignInstance/` holds the first-field and positivity certificates of the design. `GenD/Signed/`
holds the column costs (`BinomVandermonde`, `Keyhole`), the determinant comparison (`PickDet`, `PhysicalPick`)
and Davis's two lemmas on the weights of nodal polynomials (`Davis/`). `GenD/Signed/RouteI/` holds the
quadrature nodes and the rest of the row determinant bound: the interval nodes and the chord table
(`IntervalNodes`, `IntervalNodesData`, `ChordTable`, `ChordTableData`), the contour bound for the weights
(`HCirc`), the phase theorem (`PhaseHoleProof`), the Gram and log-gas bounds (`CompletedGasTangent`), the
reference measures and their fields (`CapSourceData`, `CapFields`), the certificates of the bounds
(`RowCert/`, `ColCert/`, `Ang*`, `GasEnergy*`, `OrdHf`), the moving trial sequences (`ShiftG*`) and the
assembly (`T4Instance`, `T4Leaf*`, `TerminalC`). The generic valuation theorems of the construction are in
`CatalanMeasure/Parametric/`. The theorem is
`CatalanMeasure.GenD.Signed.RouteI.Measure270.catalan_irrationalityMeasure_270` in
[`Measure270.lean`](CatalanMeasure/GenD/Signed/RouteI/Measure270.lean), and the public theorem is
`CatalanIrrationalityMeasure.catalan_irrationalityMeasure_270`.

## The Löwner-determinant measures

The approximations are determinants of rectangular Löwner matrices, the matrices of divided differences, of
a rational combination of digamma functions `ψ(z + s)` and their derivatives at integer nodes: a common
block of `r` nodes, which carries the variable, and an interleaved border of about `cr/2` row nodes and
`cr/2` column nodes, where `c` is the only parameter of the geometry.

When the combination is a difference of two digamma functions, the constant is a difference of trigamma
values. For `0 < s < t ≤ 1` put `Ψ(s, t) = ψ′(s) − ψ′(t)`. Many of the numbers above are, up to rational
factors, values of `Ψ`:

```text
Ψ(1/4, 1) = 8 (G + 5π²/48),          Ψ(3/4, 1) = −8 (G − 5π²/48),
Ψ(1/3, 1) = (9/2) (L₋₃ + π²/9),      Ψ(2/3, 1) = −(9/2) (L₋₃ − π²/9),
Ψ(1/3, 2/3) = 9 L₋₃,                 Ψ(a/q, 1) = ψ′(a/q) − ζ(2),
Ψ(1/6, 1/3) = 18 (L₋₃ + 2π²/27),     Ψ(2/3, 5/6) = 18 (L₋₃ − 2π²/27),
Ψ(1/3, 1/2) = (9/2) (L₋₃ + π²/27),   Ψ(1/2, 2/3) = (9/2) (L₋₃ − π²/27).
```

With `s, t` in `{1/6, 1/3, 1/2, 2/3, 5/6, 1}`, every `Ψ(s, t)` lies in the first plane, the rational span of
`L₋₃` and `π²` modulo the rationals. The second plane is the rational span of `ζ(3)` and `π²`; it
contains `ψ″(1) = −2ζ(3)`. A general point of the first plane needs three digamma terms, and `ζ(3)` comes from
`ψ′(z + 1)` itself, so not every number here is a single value of `Ψ`.

Three estimates are proved once, for every frame.


- **Content.** As in the arithmetic method of Rhin and Viola, the `p`-adic valuation of the common
  denominator is bounded prime by prime, by a finite list of local bounds: assignment problems with
  explicit potentials, the rank of the reduction modulo `p` of a rescaled matrix, and windows of the
  border free of poles, where the reduction is translation invariant (for the small primes, which meet
  the border several times, the windows are read modulo `p`). Each is an explicit integer expression in
  the scale, the border, the prime and the first poles of the frame modulo `p`. One theorem turns a
  finite table of affine pieces, checked by comparisons of rational numbers, into the bound
  `(Λ + o(1)) r²` for the logarithm of the denominator, using the prime number theorem in arithmetic
  progressions; the same table serves every shift with the same denominator `q`.
- **Nonvanishing.** By Hermite interpolation in characteristic zero, after deleting a bounded number of
  common nodes (at most 64), some member of the family is nonzero at any given rational point. No prime
  is involved.
- **Decay.** Andréief's identity for the row and column nodes, with Cauchy determinants, reduces the size
  of the determinant to a discrete logarithmic energy. A lower bound for this energy comes from a
  comparison measure on finitely many segments, through the conditional positive definiteness of the
  logarithmic kernel, and is verified on a finite cover by cells in exact rational arithmetic. The result
  is `|P(x)| ≤ e^(−(D − o(1)) r²)` for `|x − ξ| ≤ e^(−γr)`.

Together they give `μ ≤ γ/(D − Λ)`:

| number | (s, t) | c | Λ | D | γ | γ/(D − Λ) | μ ≤ |
|---|---|---|---|---|---|---|---|
| a L₋₃ + b π² | first plane | 1/6 | 3.2227428 | 3.5503512 | 6.7690926 | 20.66214 | 20.6622 |
| L₋₃ ± 2π²/27 | (1/6, 1/3), (2/3, 5/6) | 1/6 | 3.0668400 | 3.5503512 | 6.7690926 | 13.99987 | 14 |
| L₋₃ ± π²/27 | (1/3, 1/2), (1/2, 2/3) | 1/6 | 3.1096062 | 3.5503512 | 6.7690926 | 15.35830 | 15.359 |
| L₋₃ ± π²/18 | first plane | 1/4 | 3.4140176 | 3.8109776 | 6.9434368 | 17.49153 | 17.492 |
| a ζ(3) + b π² | second plane | 6/41 | 3.4768376 | 3.4982052 | 7.1600631 | 335.0886 | 335.20 |
| ζ(3) | ψ′(z + 1) | 3/10 | 2.9128390 | 3.9790633 | 6.4345402 | 6.034884 | 6.0382 |
| a ζ(3) + b π⁴ | third plane | 1/10 | 3.2941777 | 3.3533776 | 6.9643459 | 117.6410 | 118 |
| G ± 5π²/48 | (1/4, 1), (3/4, 1) | 1/5 | 3.5149036 | 3.7453322 | 7.1887383 | 31.19724 | 31.1973 |
| L₋₃ | (1/3, 2/3) | 1/2 | 4.0959278 | 4.6442402 | 7.5030223 | 13.68385 | 13.6839 |
| L₋₃ ± π²/9 | (1/3, 1), (2/3, 1) | 3/10 | 3.3104458 | 4.0295805 | 6.8255087 | 9.491278 | 9.4913 |
| ψ′(a/5) − π²/6 | (a/5, 1) | 2/9 | 3.5128488 | 3.8141613 | 7.1638755 | 23.77556 | 23.7756 |
| ψ′(a/7) − π²/6 | (a/7, 1) | 1/6 | 3.6391158643 | 3.6432250312 | 7.4218615374 | 1806.172 | 1806.1719 |
| π² | (1/2, 1) | 3/10 | 2.9923824 | 3.9790633 | 6.4345402 | 6.521399 | 6.5214 |

Here `Λ` is the content constant, `D` the decay constant and `γ` the window constant. They are the
rational numbers of the formal proof, rounded outward (`Λ` and `γ` up, `D` down); the column
`γ/(D − Λ)` is the exact quotient, rounded up. The last column is the bound stated in Lean. The row for π² uses `Ψ(1/2, 1) = π²/3`. The bounds for `ζ(3)`,
`π²` and the third plane are weaker than the known bounds and are included for completeness.

The shared results are in `CatalanCore/Uniform/` (namespace `CatalanCore.Uniform`): the content theorem
`Content.BankShared.Check.hasScaledContent_of_check`, and its form for frames with several first poles,
`Content.BankShared.KTerm.hasScaledContent_of_kcheck`; the rank bound
`Content.BankShared.TwoTerm.LP2HypW.gle` and the window bound
`Content.BankShared.TwoTerm.Pre.prefix_gle`; the third-order bound at the primes where the border of the
matrix wraps around, `Content.UFSimple.WrapPrefixCheck.catValid_prefix_full`; the selection theorem `BlockGeom.hasNV0`; the decay theorem
`Decay.AltDecay.altGeom_hasScaledDecay`; and the deduction `measure_of_family_nv0_even`. They also use
modules from the rest of `CatalanCore/` and from `CatalanFrames/` and `CatalanLambda/` (among them the
frames, Cauchy determinants and Andréief's identity). The data of each family are in
`CatalanCore/Uniform/Bank/`.

### The first plane

The plane theorem is proved once for all rationals `a, b`, not both zero. Each point `a L₋₃ + b π²` with
`a ≠ 0` is the constant of a frame `(a', b', c')` of three digamma terms with `a' + b' + c' = 0`, on one of two
supports; the point `a = 0` uses a frame of weight zero. All frames share one decay cover. Their content is
one instance of the periodic content theorem `Content.BankShared.KTerm.Periodic.hasScaledContent_of_periodic`:
a base cell certified once covers every translate. The data are in `Bank/Plane1/`; the theorem is
`CatalanCore.Uniform.Bank.Plane1.plane_point_ab`, and the public theorem `TrigammaDifferences.plane1_measure`.

### Special points of the first plane

At `L₋₃ ± 2π²/27`, `± π²/27` and `± π²/18` the frames `(2, −1, −1)`, `(1, −2, 1)` and `(4, −3, −1)` admit
further local bounds, from the rank of the reduction modulo `p` in an assignment form. At a boundary between
two types of these bounds, the bound used near the boundary is the largest over the few configurations
that occur there; that these configurations are all that occur is proved for every prime by linear integer
arithmetic. The decay cover is the plane's. The data are in `Bank/Plane1/Dips/`; the theorem is
`CatalanCore.Uniform.Bank.Plane1.Dips.dip_point`, and the public theorems are
`TrigammaDifferences.dip_2_27_plus_measure`, `dip_2_27_minus_measure`, `dip_1_27_plus_measure`,
`dip_1_27_minus_measure`, `dip_1_18_plus_measure` and `dip_1_18_minus_measure`.

### The second plane

The plane theorem is proved once for all rationals `a, b`, not both zero, from Löwner families over one geometry
with `c = 6/41` and one decay cover. Its content is again an instance of the periodic content theorem; the
two ends `a = 0` and `b = 0` are one-term data on the same cover. The data are in `Bank/Plane2/`; the theorem is
`CatalanCore.Uniform.Bank.Plane2.plane2_point_ab_of_content`, and the public theorem
`TrigammaDifferences.plane2_measure`.

### ζ(3)

The function is `ψ′(z + 1)`, on the geometry of `π²` with `c = 3/10`, with its own local bounds. The theorem is
`CatalanCore.Uniform.Bank.Plane2.zeta3_measure_le`, and the public theorem `TrigammaDifferences.zeta3_measure`.
The bound `6.0382` is weaker than the known bounds for `μ(ζ(3))`.

### G ± 5π²/48

The shifts `1/4` and `3/4`, with `ψ′(1/4) = π² + 8G` and `ψ′(3/4) = π² − 8G`. The two shifts exchange the
two classes of primes modulo 4, so they have the same content constant, and one decay certificate serves
both. The frame, the decay cover and the nonvanishing are in `Bank/Fourths/`, the content table in
`Bank/FourthsContent/`. The theorem is `CatalanCore.Uniform.Bank.FourthsContent.Level3Bound.lambda_measure`,
whose Boolean argument selects the sign; the public theorems are `TrigammaDifferences.lambda_minus_measure`
and `TrigammaDifferences.lambda_plus_measure` (the names refer to `λ± = G/2 ± 5π²/96`, so that
`G ± 5π²/48 = 2λ±`).

### L₋₃

The frame is `−⅓ ψ(z + ⅓) + ½ ψ(z + ½) − ⅙ ψ(z + 1)`, with `c = 1/2`. It has three digamma terms, so the
local bounds at a prime `p` involve two first poles; on each class of primes modulo 6 both are affine in
one index, and the content theorem applies with `q` replaced by 6. The content constant is
`Λ = 4.09592776731…`, and `γ/(D − Λ) = 13.683844… < 13.6839`. The content is in `Bank/Chi3/KContent/`
(`chi3_k_content`), the decay in `Bank/Chi3New/` (`chi3_decay`) with its cover in `Bank/Chi3/Cover/`, and
the theorem is `CatalanCore.Uniform.Bank.Chi3.KContent.chi3_measure_L2_k`; the public theorem is
`TrigammaDifferences.chi3_measure`.

### L₋₃ ± π²/9

The shifts `1/3` and `2/3`, with `ψ′(1/3) = 2π²/3 + 9L₋₃/2` and `ψ′(2/3) = 2π²/3 − 9L₋₃/2`.
The content table uses the primes in the classes modulo 6. The data are in `Bank/Thirds/` and
`Bank/ThirdsContent/`; the theorems are `CatalanCore.Uniform.Bank.ThirdsContent.Level3Bound.thirds_plus_measure`
and `thirds_minus_measure`, and the public theorems `TrigammaDifferences.chi3_plus_pi2_measure` and
`TrigammaDifferences.chi3_minus_pi2_measure`.

### ψ′(a/5) − π²/6

For `1 ≤ a ≤ 4`, `ψ′(a/5) − ζ(2)` is a rational linear combination of the values `L(2, χ)` for the
Dirichlet characters `χ` modulo 5. The four shifts share one content table, indexed by the four root
classes of the primes, and one decay certificate. The data are in `Bank/Fifths/` and
`Bank/FifthsContent/`; the theorems are `CatalanCore.Uniform.Bank.FifthsContent.Level3Bound.fifths1_measure`,
…, `fifths4_measure`, and the public theorems `TrigammaDifferences.fifths1_measure`, …,
`TrigammaDifferences.fifths4_measure`.

### ψ′(a/7) − π²/6

For `1 ≤ a ≤ 6`, likewise a combination of the values `L(2, χ)`, `χ` modulo 7, and of `π²`, with six root
classes. Here `D − Λ` is about `4.1·10⁻³`, and the exponent is correspondingly large. The data are in
`Bank/Sevenths/` and `Bank/SeventhsContent/`; the theorem is
`CatalanCore.Uniform.Bank.SeventhsContent.Level3Bound.sevenths_measure`, whose argument is `a − 1` in `Fin 6`,
and the public theorems are `TrigammaDifferences.sevenths1_measure`, …,
`TrigammaDifferences.sevenths6_measure`.

### π²

The shift `1/2`, with `Ψ(1/2, 1) = π²/3`. The data are in `Bank/Halves/` and `Bank/HalvesContent/`; the
theorem is `CatalanCore.Uniform.Bank.HalvesContent.Bound.pi2_measure`, and the public theorem is
`TrigammaDifferences.pi2_measure`. The bound `6.5214` is weaker than the known bounds for `μ(π²)`.

## Kernel-checked certificates

All numerical bounds are ordinary kernel-checked rational and integer computations (`decide +kernel`;
no `native_decide`): for `G`, the inverses of the base matrices modulo 1009, the trial sequences, the
reference measures and their bounds, and the rank data; for the trigamma differences, the content tables and the cell
covers of the decay certificates. The certificate data were computed with floating-point optimisation and
interval arithmetic (Arb), which are not trusted: Lean rechecks every inequality.
Large certificates are split into many small declarations with explicit intermediate values, chained by
general lemmas, and integer recurrences whose values are divisible by large powers of 2, such as the
Chebyshev and Clenshaw recurrences, are checked on the quotients by those powers. The scripts that
generated the data are in [`scripts/`](scripts/); the authoritative proof data are the Lean source
literals.

## Vendored code

Palomar requires Lean v4.35.0-rc2 or later, and every imported file must use Lean's module
system. OpenAI's repository is pinned to Lean v4.34.1 and does not use modules, so 479 files of
OpenAI's formalization (from commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` of
[openai/math](https://github.com/openai/math)) and the 10 files that OpenAI adds to
PrimeNumberTheoremAnd are copied into `OAI/` and `PrimeNumberTheoremAnd/`. Each was converted to a
module and adjusted for the newer Lean and Mathlib (see [`PORTING.md`](PORTING.md)). The proof of
μ(G) ≤ 270 imports 117 of the files in `OAI/` and all 10 in `PrimeNumberTheoremAnd/`; the proofs for the
trigamma differences import no file of `OAI/` and, for the Wiener–Ikehara theorem, 9 of the files in
`PrimeNumberTheoremAnd/`. In 37 point-evaluation files of OpenAI's certificate, which the theorems above do not import,
the comparison constants are given to seven digits (the computations are unchanged; see `NOTICE`).
Licences and attributions are in [`NOTICE`](NOTICE); all of this code is under the Apache License 2.0.

The directory `archive/` holds Lean modules that the theorems above do not import. It is not part of
the default build and is not used by any proof above.

## Building and checking

You need [elan](https://github.com/leanprover/elan) and several GiB of free disk.

```text
lake exe cache get
python3 scripts/check-lean-sources.py
lake build
ruby scripts/validate-formalization.rb
ruby scripts/validate-formalization.rb formalization-hybrid.yaml
./scripts/verify-comparator.sh
```

`lake build` builds both solution files. The numerical checks can use several GiB per Lean process; use
a small worker count (for example `LEAN_NUM_THREADS=2`) on memory-constrained machines. The comparator
script checks `comparator.json`; it needs Linux and `bwrap` (bubblewrap).

## Authorship and use of AI

The mathematics, the Lean formalization, the certificate generators and the text were produced by AI systems at the request of the author, who posed the problems, directed the work and is responsible for it: Claude Opus 5.5, Claude Sonnet 5.5 and Claude Haiku 5.5 (Anthropic), running in Claude Code, and GPT-6.1 Sol (OpenAI), running in Codex. The underlying irrationality proof for G and its Lean formalization are OpenAI's, as is the vendored code described above.

## Submission

This repository follows the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate).
Submissions to the registry go through the form at https://submit.palomar-registry.org/.

## Licence

Apache License 2.0; see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
