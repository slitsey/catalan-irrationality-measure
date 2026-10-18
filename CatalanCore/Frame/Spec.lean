module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The contract between work packages: frames, polynomial families, and the four paper inputs

STATEMENTS ONLY.  This file is owned by WP0 and is frozen after milestone M0 (design.md 6.2);
any change goes through the coordinator.  It contains:

* `Frame`        : the Loewner data `(d, mu, w, norm, xs, delta0, n0off)` of design 2.2.
* `Frame.M`, `Frame.MRect`, `Frame.Ppoly`, `Frame.P`, `Frame.const` : derived objects.
  `MRect` takes a row node family and a column node family (design 9.3), so square minors,
  rectangular Loewner minors and the hybrid matrix `Full(X)` are all built from `Frame.Mn`.
* `PolyFamily`   : a constant, an index type, a degree function, an admissibility predicate
  and a polynomial `Q n`.  `PolyFamily.ofFrame` is the square case, `PolyFamily.hybrid` the
  rectangular hybrid (design 9.2).
* `HasContent`, `HasDecay`, `HasNV`, `PrimeRule` : the Prop-valued interfaces.
* `measureExp`   : the exponent formula, `c * (g2 / (g1 * (D - Lam)) + g2 * s)`.
* `PolyFamily.MeasureLB` : the shape of every final measure statement.

## Design notes recorded by the coordinator (not Lean content, but binding on instances)

* (a) The mission is the LOWEST bound per constant.  P6 therefore uses its own sigma (FK row D,
  `mu` about 29.94), not lambda's `sigma300`.  Every instance supplies its own certificate data
  through `CertCore`; nothing here fixes a sigma.
* (b) Existing Challenge statements (77.28 / 78 / 79) stay fixed.  Improved bounds get NEW
  statement blocks (new names in new Challenge modules); no existing statement is edited.
* (c) Palomar: respect the rules only (module headers, file size, no `native_decide`,
  axioms `propext`, `Quot.sound`, `Classical.choice`); no optimisation.

## Known open conventions (hypotheses, not facts)

* `Frame.ContourGap` is deliberately NOT a field of `Frame`: the sign/shift convention of the
  contour abscissa differs between design 2.2 (literal formula) and the legacy lambda code, and
  is to be fixed by WP2a (`Decay/Contour`).  Instances prove it once the convention is fixed.
* `PolyFamily.hybrid` takes the denominator clearing factor `den` as a parameter, so that
  `Q (r, m) = den (r, m) * det Full(X)`; WP-H1 (`Rect/Geometry`) fixes the actual `den` and the
  sign convention of the `X'`/`Y'` block.  `CertCore.Dof` will receive the node-measure data
  `(alpha, Inu)` (design 9.4); it is not part of this file.
-/

@[expose] public section

open Polynomial Finset

namespace CatalanCore

/-- `zeta(2, mu) = ∑_{n ≥ 0} 1 / (n + mu)^2`, the Hurwitz zeta function at 2, as a series. -/
noncomputable def hurwitzTail2 (μ : ℚ) : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + (μ : ℝ)) ^ 2

/-- A Loewner frame.  `F(z) = ∑ i, w i • ψ(z + μ i)` with shifts in `(0, 1]` and integer weights
of total sum zero.  The Loewner-type matrix is `T = (1/norm) • L_F` on nodes `0, 1, …`.
Examples:
* lambda  : `μ = ![3/4, 1]`, `w = ![-1, 1]`, `norm = 16`, `xs = 5/8`, `δ0 = 3/8`, `n0off = 0`;
* lambda' : `μ = ![1/4, 1]`, `w = ![-1, 1]`, `norm = 16` (`T̄ = -(λ' I + N0)`; sign handled by an
  instance lemma, not a field);
* P6      : `μ = ![1, 1/3, 1/2]`, `w = ![1, 2, -3]`, `norm = 36`, `xs = 3/4`, `δ0 = 1/4`,
  `n0off = 1`. -/
structure Frame where
  /-- number of atom families (2, 2, 3) -/
  d : ℕ
  /-- shifts `μ i ∈ (0, 1]` -/
  μ : Fin d → ℚ
  /-- integer weights -/
  w : Fin d → ℤ
  /-- normalisation: the matrix is `(1/norm)` times the Loewner matrix of `F` -/
  norm : ℚ
  /-- contour abscissa offset: `x* = -N0 - xs` -/
  xs : ℚ
  /-- distance from `x*` to the nearest real pole -/
  δ0 : ℚ
  /-- `N0 = ⌊r0 h⌋ - n0off` -/
  n0off : ℕ
  /-- shifts lie in `(0, 1]` -/
  hμ : ∀ i, 0 < μ i ∧ μ i ≤ 1
  /-- atoms `-(n + μ i)` are pairwise distinct -/
  hμinj : ∀ i j, i ≠ j → μ i ≠ μ j
  /-- `∑ w = 0` kills the constant term of `E` and gives `e^{-2π|Im z|}` decay -/
  hw : ∑ i, w i = 0
  /-- positive normalisation -/
  hnorm : 0 < norm

namespace Frame

variable (Fr : Frame)

/-- `Δ_k = F(k) - F(k-1) = ∑ w_i / (k-1+μ_i)`. -/
def Delta (k : ℕ) : ℚ := ∑ i, (Fr.w i : ℚ) / ((k : ℚ) - 1 + Fr.μ i)

/-- `D_k = F'(k-1) - F'(k) = ∑ w_i / (k-1+μ_i)^2`. -/
def Dsq (k : ℕ) : ℚ := ∑ i, (Fr.w i : ℚ) / ((k : ℚ) - 1 + Fr.μ i) ^ 2

/-- Loewner entry at natural nodes `(a, b)` (row node `a`, column node `b`).
Off-diagonal: `(1/(norm (b-a))) ∑_{a<k≤b} Δ_k` (symmetric in `a, b`);
diagonal: `-(1/norm) ∑_{k≤a} D_k`. -/
def Mn (a b : ℕ) : ℚ :=
  if a = b then -(1 / Fr.norm) * ∑ k ∈ Icc 1 a, Fr.Dsq k
  else (1 / Fr.norm) * (1 / (((max a b : ℕ) : ℚ) - ((min a b : ℕ) : ℚ))) *
    ∑ k ∈ Ioc (min a b) (max a b), Fr.Delta k

/-- The Loewner matrix on a ROW node family `s : ι → ℕ` and a COLUMN node family `t : κ → ℕ`
(design 9.3).  Square principal minors are `s = t`; rectangular minors with removed common
nodes and the hybrid matrix use `s ≠ t`. -/
def MRect {ι κ : Type} (s : ι → ℕ) (t : κ → ℕ) : Matrix ι κ ℚ :=
  Matrix.of fun a b => Fr.Mn (s a) (t b)

/-- The `h × h` matrix `M` on nodes `0, …, h-1`. -/
def M (h : ℕ) : Matrix (Fin h) (Fin h) ℚ :=
  Fr.MRect (fun a : Fin h => (a : ℕ)) (fun b : Fin h => (b : ℕ))

/-- `P_h(X) = det (X I + M)` as a polynomial over `ℚ`. -/
noncomputable def Ppoly (h : ℕ) : ℚ[X] :=
  (Matrix.of fun a b : Fin h => (if a = b then (X : ℚ[X]) else 0) + C (Fr.Mn a b)).det

/-- `P_h(r) = det (r I + M)` at a rational `r`. -/
def P (h : ℕ) (r : ℚ) : ℚ := (r • (1 : Matrix (Fin h) (Fin h) ℚ) + Fr.M h).det

/-- The constant: `T = const • I + M`, `const = F'(0) / norm = (∑ w_i ζ(2, μ_i)) / norm`. -/
noncomputable def const : ℝ := (∑ i, (Fr.w i : ℝ) * hurwitzTail2 (Fr.μ i)) / (Fr.norm : ℝ)

/-- Contour hypothesis (NOT a field of `Frame`; convention to be fixed by WP2a, see header):
the abscissa `x* ≡ -xs` keeps distance `δ0` from every pole `-(n + μ i)`. -/
def ContourGap : Prop :=
  0 < Fr.δ0 ∧ ∀ (i : Fin Fr.d) (n : ℤ), Fr.δ0 ≤ |(n : ℚ) + Fr.μ i - Fr.xs|

/-- Row node of the hybrid matrix `Full(X)` of size `(r+m)`: rows `C ∪ X'`,
`C = [0, r)`, `X' = {r + 2i}`. -/
def hybRow (r m : ℕ) : Fin r ⊕ Fin m → ℕ :=
  Sum.elim (fun c => (c : ℕ)) (fun i => r + 2 * (i : ℕ))

/-- Column node of the hybrid matrix: columns `C ∪ Y'`, `Y' = {r + 2i + 1}`. -/
def hybCol (r m : ℕ) : Fin r ⊕ Fin m → ℕ :=
  Sum.elim (fun c => (c : ℕ)) (fun i => r + 2 * (i : ℕ) + 1)

/-- `det Full(X)` as a polynomial in `X`: the `(r+m)`-square Loewner matrix on node families
`(hybRow, hybCol)` with `X` added at the cells `(c, c)`, `c ∈ C`.  Schur reduction gives
`det Full(X) = det R_{X'Y'} * P_r(X)` (design 9.1); sign convention fixed by WP-H1. -/
noncomputable def fullPoly (r m : ℕ) : ℚ[X] :=
  (Matrix.of fun a b : Fin r ⊕ Fin m =>
    (match a, b with
      | Sum.inl c, Sum.inl c' => if c = c' then (X : ℚ[X]) else 0
      | _, _ => 0) + C (Fr.Mn (hybRow r m a) (hybCol r m b))).det

end Frame

/-- A constant, a sequence of polynomials and a degree.  Square frames and hybrids are instances
(design 9.2).  All three interfaces below are stated for a `PolyFamily`. -/
structure PolyFamily where
  /-- the constant being approximated -/
  const : ℝ
  /-- index type of the members -/
  ι : Type
  /-- degree of member `n` (`n` for the square frame; `r` for the hybrid) -/
  deg : ι → ℕ
  /-- admissible members: `True` (square), `|m - α r| ≤ 1` (hybrid) -/
  Adm : ι → Prop
  /-- the member polynomials, over `ℚ` -/
  Q : ι → ℚ[X]

namespace PolyFamily

/-- Rational evaluation `Q_n(p/q)`. -/
noncomputable def evalQ (Fam : PolyFamily) (n : Fam.ι) (x : ℚ) : ℚ := (Fam.Q n).eval x

/-- Real evaluation `Q_n(x)`. -/
noncomputable def evalR (Fam : PolyFamily) (n : Fam.ι) (x : ℝ) : ℝ := (Fam.Q n).aeval x

/-- Square case: `ι = ℕ`, `deg n = n`, every member admissible, `Q n = P_n`. -/
noncomputable def ofFrame (Fr : Frame) : PolyFamily where
  const := Fr.const
  ι := ℕ
  deg := id
  Adm := fun _ => True
  Q := Fr.Ppoly

/-- Hybrid case with density `α = m/r` and denominator-clearing factor `den`:
`ι = ℕ × ℕ`, `deg (r, m) = r`, `Adm (r, m) := |m - α r| ≤ 1`,
`Q (r, m) = den (r, m) * det Full(X)` (so no division by `det R_{X'Y'}` is needed). -/
noncomputable def hybrid (Fr : Frame) (α : ℚ) (den : ℕ × ℕ → ℚ) : PolyFamily where
  const := Fr.const
  ι := ℕ × ℕ
  deg := Prod.fst
  Adm := fun rm => |(rm.2 : ℚ) - α * rm.1| ≤ 1
  Q := fun rm => C (den rm) * Fr.fullPoly rm.1 rm.2

/-- Shape of every final measure statement: `|const - p/q| > q^{-(E + e)}` for all `e > 0`,
all large `q`, all `p` coprime to `q`. -/
def MeasureLB (Fam : PolyFamily) (E : ℝ) : Prop :=
  ∀ e > 0, ∃ q₀ : ℕ, ∀ (p : ℤ) (q : ℕ), q₀ ≤ q → IsCoprime p (q : ℤ) →
    (q : ℝ) ^ (-(E + e)) < |Fam.const - (p : ℝ) / q|

end PolyFamily

/-- (1) CONTENT: `q^deg · Dden n · Q_n(p/q) ∈ ℤ` for admissible `n`, and
`log Dden n ≤ (Λ + ε) (deg n)^2` for admissible `n` of large degree. -/
def HasContent (Fam : PolyFamily) (Λ : ℝ) : Prop :=
  ∃ Dden : Fam.ι → ℕ, (∀ n, 0 < Dden n) ∧
    (∀ n, Fam.Adm n → ∀ (p q : ℤ), 0 < q →
      ∃ z : ℤ, (q : ℚ) ^ Fam.deg n * Dden n * Fam.evalQ n (p / q) = z) ∧
    (∀ ε > 0, ∃ N₀ : ℕ, ∀ n, Fam.Adm n → N₀ ≤ Fam.deg n →
      Real.log (Dden n) ≤ (Λ + ε) * (Fam.deg n : ℝ) ^ 2)

/-- (2) DECAY + WINDOW: `|Q_n(const + t)| ≤ exp(-(D - δ) (deg n)^2)` for `|t| ≤ exp(-c deg n)`,
admissible `n` of large degree. -/
def HasDecay (Fam : PolyFamily) (D c : ℝ) : Prop :=
  ∀ δ > 0, ∃ N₀ : ℕ, ∀ n, Fam.Adm n → N₀ ≤ Fam.deg n → ∀ t : ℝ,
    |t| ≤ Real.exp (-c * (Fam.deg n : ℝ)) →
      |Fam.evalR n (Fam.const + t)| ≤ Real.exp (-(D - δ) * (Fam.deg n : ℝ) ^ 2)

/-- Prime classes and "bad" primes for a given denominator `q`. -/
structure PrimeRule where
  /-- modulus: primes `l ≡ r (mod m)` are used; density `1 / φ(m)` -/
  m : ℕ
  /-- the residue class -/
  r : ZMod m
  /-- the class is a unit class -/
  hr : IsUnit r
  /-- `Bad l q`: the prime `l` may not be used for the denominator `q` -/
  Bad : ℕ → ℕ → Prop
  /-- `∏_{bad l ≤ x} l ≤ q^weight` (1 for "l ∣ q", 1/2 for "l² ∥ q") -/
  weight : ℚ

/-- `s = weight * φ(m)`: the window length needed in `exists_prime_window`. -/
def PrimeRule.s (R : PrimeRule) : ℚ := R.weight * (Nat.totient R.m : ℚ)

/-- (3) NV: for all large primes `l` in the class, and every `p/q` in lowest terms with `l` not
bad for `q`, some admissible member of degree in `[g₁ l - C, g₂ l + C]` does not vanish at `p/q`.
(Hybrid member-pair arguments, and Lemma 3, live inside the instance's proof.) -/
def HasNV (Fam : PolyFamily) (R : PrimeRule) (g₁ g₂ : ℝ) : Prop :=
  ∃ (C : ℝ) (l₀ : ℕ), ∀ l : ℕ, l.Prime → l₀ ≤ l → (l : ZMod R.m) = R.r →
    ∀ (p q : ℤ), 0 < q → IsCoprime p q → ¬ R.Bad l q.natAbs →
      ∃ n, Fam.Adm n ∧ g₁ * l - C ≤ (Fam.deg n : ℝ) ∧ (Fam.deg n : ℝ) ≤ g₂ * l + C ∧
        Fam.evalQ n (p / q) ≠ 0

/-- Pure arithmetic, so that final theorems are `norm_num`. -/
def measureExp (c Λ D g₁ g₂ s : ℚ) : ℚ := c * (g₂ / (g₁ * (D - Λ)) + g₂ * s)

end CatalanCore
