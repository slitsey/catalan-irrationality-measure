# Parametric research foundation

The public solution certifies bounds 1981 and 5391 using the baseline construction
and residue-kernel combinations. The new population-energy construction described
below remains research; its proposed 1281 bound is not a theorem.

The primitive tuple `(20,3,1,2,1)` now has kernel-checked actual base entries,
three modular inverse certificates, rational base nonsingularity, and uniform prime
nonvanishing in `TwentyBase/Nonvanishing`. `PopulationOneLogs` and
`PopulationPhysicalValue` identify both actual product majorants with their exact
normalized energies. `FreePopulationFields`, `PopulationFields`, and
`LogFieldStability` provide the separate free/fixed duals and uniform finite
endpoint corrections. The shifted-field derivative, approximation, and stationary
cover framework is proved in `Cert/Shifted*.lean`; the four frozen numerical trials
still require their concrete certificates. `TwentyPopulationAudit` reports only
the three standard Lean axioms for fifteen further principal statements.

`Parameters` describes integer multiples of `(n0,b0,q0,g0,h0)`. Admissibility requires
positive n0,b0,q0,h0 and 2g0<n0. The proposed tuple is `(96,15,7,7,5)`.

The selected modules compile in Lean 4.35.0-rc2. A separate axiom audit reports only
propext, Classical.choice and Quot.sound for the principal statements. Independent
kernel replay of this bundle has not yet been run.

* `Polynomial` and `Degree`: affine determinant polynomial and degree at most n-g;
  in particular at most 89N for the proposed tuple, including N=0.
* `RowFrobenius`, `RowExtraction`, `CoefficientBounds`: generic rational row identity,
  Frobenius separation, coefficient extraction, and row support bounds.
* `Contractions`, `BaseResidues`, `RawDigitReduction`, `FilterDigitReduction`: moment,
  zeta and filter contractions and the full scaled rational-entry reduction.
* `BlockAlgebra`, `PrimeNonvanishing`: reduction of uniform prime nonvanishing to
  the three finite base matrices B0, B0+B1 and B0-B1. The theorem explicitly assumes
  their determinants are nonzero modulo the prime. `ProposedBase/Nonvanishing`
  now discharges the proposed tuple's three rational base conditions from the
  complete literal-entry and inverse certificates modulo1009.
* `GoodPrimes`: three nonzero finite rational base determinants imply nonvanishing
  for every sufficiently large prime, with an explicit fixed cutoff.
* `IntegerRows`, `ProposedRowsData`: sound integer coefficient algorithms and all
  97 literal P/D row lists for the proposed tuple, certified with `decide +kernel`.
  These are coefficient certificates, not determinant nonsingularity certificates.
* `CommonFactor`, `RestrictedQuadrature`, `PolynomialFunctional`, `RestrictedWeights`:
  the exact common row factor, interpolation with only n-g nodes, and a reduced
  quadrature formula for the actual filtered Catalan coefficient. For the proposed
  tuple the shared-factor node weight times the absolute quadrature weight is at
  most 260000 N K^N, uniformly in the column index, where K=10^65.
* `RadiusCoefficients`, `ResidualCircle`, `RadiusQuadrature`: roots-of-unity
  coefficient estimates rescaled to radius1001/1000 and 15 exact rational interval
  certificates proving K<=exp(150). The entire factor (1-X)^(h+q) is retained in
  this estimate. No contour-integral formalization or numerical supremum is assumed.

The entry reduction requires an odd prime p>H(1) and a p-unit denominator for p*z.
It therefore retains the square-denominator improvement. This condition is weaker
than requiring a p-unit denominator for z.

The companion `CatalanMeasure/PopulationDual.lean` proves a generic finite population
dual, an undamped interaction bound with explicit uniform regularization errors,
and the actual fixed/free case coupling. Connecting this interaction to the full
determinant integrand, certifying the frozen rational fields and norms, and proving
the generalized denominator estimate remain necessary.

`Cert/ResidualField.lean` and `ResidualFixed{0,1}Certificate.lean` certify both frozen
second-case residual fields at most -1/8 on the entire interval [-1,0]. Their exact
logarithm, derivative and root-cover certificates use the main Lean kernel. These
are field bounds; the complete generalized determinant majorant remains unfinished.
All 96 proposed moment/zeta columns are now kernel-certified in `ProposedBase`, and
`EntryBridge` proves their integer contraction agrees with the actual base entries.
All97 literal-entry rows and all three96x96 inverse certificates have now passed.
`ProposedBase/Nonvanishing` proves actual rational base nonsingularity and uniform
prime nonvanishing for the proposed tuple, retaining the p*z denominator condition.

`Contact`, `RealEvaluation`, `RealIntegral` and `PairedIntegral` prove cancellation
of the zeta(2) term and identify the actual generalized determinant polynomial at
Catalan with an integrable paired moment determinant. `RealSheet`, `RealSheetBounds`
and `FirstSheetBounds` supply the exact coordinate factorization and both row
determinant estimates, retaining the first-sheet dimension and case hypotheses.
`WeightedRestrictedBounds` bounds the actual quadrature weights jointly with
the fixed fields by260000*N*exp(158N) or260000*N*exp(138N).
`PerturbedMoment` expresses the actual rational entry as its Catalan moment
integral plus the reduced atom sum, with factor z-G. This connects the generalized
perturbation to the row values used in mixed determinant integrals.
`LowRankPole` gives a generic valuation bound for a pole whose residue factors
through r dimensions, and the associated double-pole saving n-min(n,r).
The uniform residue factorization needed for the experimental prime windows has
not been proved. `CheckpointAudit` audits the principal component statements.
The full determinant majorant and generalized valuations are still unfinished;
no new irrationality-measure exponent follows from these components alone.

The Frobenius and block arguments adapt the vendored OpenAI generic identities and
linear algebra; their original sources are named in the imports. The new parameter
record, uniform parameter generalization, population interaction, and square
transfer were developed by Codex. The existing repository NOTICE applies.

The research mission is the standard irrationality-measure bound μ(G)≤2, with
3300 as an earlier intermediate proposed target; the restricted row space suggests
a stronger numerical candidate near3000, still requiring the remaining arithmetic
and determinant majorant proofs. Publish proved mathematical improvements
after main Lean kernel certification and update the paper when its bound changes.
Defer CI optimization, external-kernel replay and Palomar preparation until the
bound-reduction research is genuinely stalled.
