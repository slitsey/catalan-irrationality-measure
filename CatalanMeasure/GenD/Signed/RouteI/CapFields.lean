module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option Elab.async false

/-!
# Route I `CapFields`: the shared source record and the cap bundle of the tangent

Data-free semantic interface for rows C4, C5, C6, C8 and the completed-gas tangent (T4).

* `CapSource` is the ONE source record: cube gas Y-cells per species, separately normalized
  reference rows and columns at anchors 0 and 1, auxiliary (radial) entries with phases and
  nonnegative weights, the decimal `sigma`/`radial` seeds and the `eps` that determines `q`.
  `CapSource.Admissible` carries support, positivity and exact normalization.
* Every field is DEFINED from the record by the point-integral formulas of pc29
  (`RowField`, `ColumnField`, `NearField`, `cosine_potential`): no function named `field` is
  supplied from outside.
* `Trunc` separates the EXACT infinite fields (`Trunc.exact`, `tsum`) from the finite polynomial
  upper surrogates (`Trunc.finite K`, degree `K`, with the positive geometric tail added once).
  `Dominates` is the exact-field <= finite-upper theorem that source constructors discharge.
* `CapBundle` collects the real inequalities the tangent needs. It has no determinant conclusion.
  The intercept values are explicit arguments (owned by C8/C9, bound by their own modules).

Finite-N corrections, source-to-population transfer and the Gram/tangent step are separate
generic theorems (T4 `CompletedGasTangent`); none of that is assumed here.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.CapFields

open Real Set intervalIntegral
open scoped BigOperators

noncomputable section

/-! ### Signs, flavours, truncation -/

/-- Species / sign of the real variable. -/
inductive Sign | neg | pos
  deriving DecidableEq

/-- Sign of a nonzero real `x` (`x<0` is `neg`). -/
def signOf (x : ℝ) : Sign := if x < 0 then Sign.neg else Sign.pos

/-- Row constants `AL, BE, gamma` of pc29 `RowField`: free rows at an anchor versus marked rows. -/
structure Flavor where
  al : ℝ
  be : ℝ
  gamma : ℝ

/-- `marked=False`: `AL=11/29, BE=3/29, gamma=39/29` (both anchors). -/
def Flavor.free : Flavor := ⟨11 / 29, 3 / 29, 39 / 29⟩
/-- `marked=True`: `AL=BE=0`, `gamma=53/58`. -/
def Flavor.marked : Flavor := ⟨0, 0, 53 / 58⟩

/-- Angular constants `kappa_sigma` (design C literals, GU §3: negative `5463909/10^8`, positive
`14762657/10^8`; they clear the Jensen polynomial plus the true square loss on all 32 radii). -/
def kappa : Sign → ℝ
  | Sign.neg => 5463909 / 100000000
  | Sign.pos => 14762657 / 100000000

/-- Exact infinite series versus finite degree-`K` polynomial upper surrogate. -/
inductive Trunc
  | exact
  | finite (K : ℕ)

/-- `sum_{k>=1} f k`, exact (`tsum`) or truncated at degree `K`. -/
def Trunc.sum : Trunc → (ℕ → ℝ) → ℝ
  | Trunc.exact, f => ∑' k : ℕ, f (k + 1)
  | Trunc.finite K, f => ∑ k ∈ Finset.range K, f (k + 1)

/-! ### Cells -/

/-- A uniform Y-cell `[lo,hi]` of mass `w`. -/
structure YCell where
  lo : ℝ
  hi : ℝ
  w : ℝ
  lo_lt : lo < hi
  w_nonneg : 0 ≤ w

namespace YCell

/-- Mass-weighted average `w/(hi-lo) * int_lo^hi f`. -/
def avg (c : YCell) (f : ℝ → ℝ) : ℝ := c.w / (c.hi - c.lo) * ∫ s in c.lo..c.hi, f s

/-- Inverse branch magnitude `X(Y)`, `Y = X + 1/X`, `|X|<=1`, for `|Y|>=2`. -/
def physX (Y : ℝ) : ℝ :=
  if 0 ≤ Y then 2 / (Y + √(Y ^ 2 - 4)) else -(2 / (-Y + √(Y ^ 2 - 4)))

/-- Logarithmic potential of the cell at the Y-point `y`. -/
def pot (c : YCell) (y : ℝ) : ℝ := c.avg fun s => Real.log |y - s|

/-- Average of `f` over the physical pushforward `x = X(Y)`. -/
def phys (c : YCell) (f : ℝ → ℝ) : ℝ := c.avg fun Y => f (physX Y)

/-- The cell with endpoints doubled (column references enter the row potential this way). -/
def dil2 (c : YCell) : YCell := ⟨2 * c.lo, 2 * c.hi, c.w, by linarith [c.lo_lt], c.w_nonneg⟩

end YCell

/-- Sum over a cell list. -/
def potL (l : List YCell) (y : ℝ) : ℝ := (l.map fun c => c.pot y).sum
def physL (l : List YCell) (f : ℝ → ℝ) : ℝ := (l.map fun c => c.phys f).sum
def massL (l : List YCell) : ℝ := (l.map fun c => c.w).sum

/-- An auxiliary (radial) entry: radius index, phase and nonnegative weight. -/
structure AuxEntry where
  rad : ℕ
  phase : ℝ
  w : ℝ
  w_nonneg : 0 ≤ w

/-! ### The source record -/

/-- The single source record of the cap fields. `gas σ` is the species-`σ` part of the cube,
`refRow a`, `refCol a` the separately normalized anchor-`a` references, `aux σ` the auxiliary
population, `sigma`/`radial` the seeds, `eps` determines `q`. Radii are `exp (-sigma i)`. -/
structure CapSource where
  gas : Sign → List YCell
  refRow : Fin 2 → List YCell
  refCol : Fin 2 → List YCell
  aux : Sign → List AuxEntry
  sigma : ℕ → ℝ
  radial : ℕ → ℝ
  nRad : ℕ
  eps : ℝ
  /-- The reflection polynomial `reflPoly` has degree `reflDeg + 1` and `reflTail` retains the
  nonnegative remainder after it (GD3: the design value lives in the instance). -/
  reflDeg : ℕ

namespace CapSource
variable (S : CapSource)

def rad (i : ℕ) : ℝ := Real.exp (-S.sigma i)
def q : ℝ := Real.exp (-S.eps / 2)
/-- `normalizer = (1+4r+r^2)/(1-r)^2`, `r=q^2`. -/
def normalizer : ℝ := (1 + 4 * S.q ^ 2 + (S.q ^ 2) ^ 2) / (1 - S.q ^ 2) ^ 2
/-- Strength `3(1+r)/(2(1-r)normalizer)`. -/
def strength : ℝ := 3 * (1 + S.q ^ 2) / (2 * (1 - S.q ^ 2) * S.normalizer)
/-- Curvature `1/(2 normalizer)`. -/
def curvature : ℝ := 1 / (2 * S.normalizer)

/-- Auxiliary kernel coefficient `-q^k (1+A k+B k^2)/k`. -/
def coef (k : ℕ) : ℝ :=
  -(S.q ^ k * (1 + S.strength * k + S.curvature * k ^ 2) / k)

/-- Total auxiliary mass of the species. -/
def auxMass (σ : Sign) : ℝ := ((S.aux σ).map fun e => e.w).sum

/-- The positive geometric tail of the degree-`K` surrogate (zero for the exact field),
including the factor `2` on the negative species. Added once. -/
def auxTail : Trunc → Sign → ℝ
  | Trunc.exact, _ => 0
  | Trunc.finite K, σ =>
    S.q ^ (K + 1) * ((1 / ((K : ℝ) + 1) + S.strength) * (1 / (1 - S.q)) +
      S.curvature * (((K : ℝ) + 1) * (1 / (1 - S.q)) + S.q * (1 / (1 - S.q)) ^ 2)) *
    S.auxMass σ * (if σ = Sign.neg then 2 else 1)

/-- Admissibility: support, positivity, exact normalization (gas total `1`, auxiliary totals
`1-m_+`, `53/58-m_-`, anchor masses `1` and `49/50`), radii in `(0,1]`. -/
structure Admissible : Prop where
  eps_pos : 0 < S.eps
  sigma_nonneg : ∀ i, 0 ≤ S.sigma i
  sigma_mono : Monotone S.sigma
  aux_rad : ∀ σ, ∀ e ∈ S.aux σ, e.rad < S.nRad
  gas_pos : ∀ c ∈ S.gas Sign.pos, 2 ≤ c.lo
  gas_neg : ∀ c ∈ S.gas Sign.neg, c.hi ≤ -2
  ref_away : ∀ a, ∀ c ∈ S.refRow a, 2 ≤ c.lo ∨ c.hi ≤ -2
  gas_mass : massL (S.gas Sign.pos) + massL (S.gas Sign.neg) = 1
  aux_pos_mass : S.auxMass Sign.pos = 1 - massL (S.gas Sign.pos)
  aux_neg_mass : S.auxMass Sign.neg = 53 / 58 - massL (S.gas Sign.neg)
  ref0_perm : (S.refRow 0).Perm (S.gas Sign.pos ++ S.gas Sign.neg)
  ref_row_mass0 : massL (S.refRow 0) = 1
  ref_col_mass0 : massL (S.refCol 0) = 1
  ref_row_mass1 : massL (S.refRow 1) = 49 / 50
  ref_col_mass1 : massL (S.refCol 1) = 49 / 50

/-! ### Fields -/

/-- Radial ratio `psi = r/x` if `r<|x|`, else `x/r`. -/
def psi (r x : ℝ) : ℝ := if r < |x| then r / x else x / r

/-- Auxiliary (radial) part `A_sigma(x)` of the row field: `m log max(|x|,r)` plus the kernel
series in `psi`, plus the mirror series `(r x)^k` for the negative species. -/
def radialA (t : Trunc) (σ : Sign) (x : ℝ) : ℝ :=
  ((S.aux σ).map fun e =>
    e.w * (Real.log (max |x| (S.rad e.rad)) +
      t.sum (fun k => S.coef k * (psi (S.rad e.rad) x) ^ k * Real.cos (k * e.phase)) +
      (if σ = Sign.neg then
        t.sum (fun k => S.coef k * (S.rad e.rad * x) ^ k * Real.cos (k * e.phase))
       else 0))).sum

/-- Positive-species reflection moment `m_k = int x^k dmu_+`. -/
def reflMoment (k : ℕ) : ℝ := physL (S.gas Sign.pos) fun x => x ^ k

/-- Reflection polynomial `reflPoly(x) = sum_{k<=reflDeg+1} m_k x^k / k`
(GD3: the degree is the field `reflDeg`; the design value lives in the instance). -/
def reflPoly (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (S.reflDeg + 1), S.reflMoment (k + 1) * x ^ (k + 1) / ((k : ℝ) + 1)

/-- Retained nonnegative reflection tail `reflTail`. -/
def reflTail : ℝ :=
  ((S.gas Sign.pos).map fun c =>
    let prim : ℝ → ℝ := fun x => x ^ (S.reflDeg + 1) / ((S.reflDeg : ℝ) + 1) +
      x ^ (S.reflDeg + 2) / ((S.reflDeg : ℝ) + 2)
    c.w / (c.hi - c.lo) * (prim (YCell.physX c.lo) - prim (YCell.physX c.hi)) /
      ((S.reflDeg : ℝ) + 2)).sum

/-- Row reference lists (`none` = empty references, the ordinary marked branch). -/
def refR : Option (Fin 2) → List YCell
  | none => []
  | some a => S.refRow a
def refC : Option (Fin 2) → List YCell
  | none => []
  | some a => S.refCol a

/-- The row field of pc29 `RowField` (exact point-integral expression, no interval allowances):
`L(R)+L(G_s)-kappa_s + Pot(G_s+R-2C, Y x) + (m_s+AL) log|x| - gamma log(1+x^2)
 + BE log(1-x) + [pos] (reflPoly+reflTail) + A_s(x) + tail`. -/
def rowField (t : Trunc) (σ : Sign) (fl : Flavor) (ref : Option (Fin 2)) (x : ℝ) : ℝ :=
  physL (S.refR ref) (fun u => Real.log |u|) + physL (S.gas σ) (fun u => Real.log |u|) -
    kappa σ +
  (potL (S.gas σ) (x + 1 / x) + potL (S.refR ref) (x + 1 / x) -
    potL ((S.refC ref).map YCell.dil2) (x + 1 / x)) +
  (massL (S.gas σ) + fl.al) * Real.log |x| - fl.gamma * Real.log (1 + x ^ 2) +
  fl.be * Real.log (1 - x) +
  (if σ = Sign.pos then S.reflPoly x + S.reflTail else 0) +
  S.radialA t σ x + S.auxTail t σ

/-- Free row at anchor `a` (`marked=False`); species by the sign of `x`. -/
def freeRow (t : Trunc) (a : Fin 2) (x : ℝ) : ℝ :=
  S.rowField t (signOf x) Flavor.free (some a) x

/-- Ordinary marked row (`marked=True`, empty references); `x = t` for pos, `x = -t` for neg. -/
def ordField (t : Trunc) (σ : Sign) (x : ℝ) : ℝ :=
  S.rowField t σ Flavor.marked none x

/-- Anchor free column field `-L(R_a)+2 Pot(C_a,s)-Pot(R_a,2s)+(9/58)log s+(3/58)log(1-s)`. -/
def colField (a : Fin 2) (s : ℝ) : ℝ :=
  -physL (S.refRow a) (fun u => Real.log |u|) + 2 * potL (S.refCol a) s -
    potL (S.refRow a) (2 * s) + 9 / 58 * Real.log s + 3 / 58 * Real.log (1 - s)

/-- Near marked source field `(48/58)log y-(53/58)log(1+y^2)-kappa_+ - R900(y)
+ sum_j P_j(r_j y) + Eaux_+`. -/
def nearField (t : Trunc) (y : ℝ) : ℝ :=
  48 / 58 * Real.log y - 53 / 58 * Real.log (1 + y ^ 2) - kappa Sign.pos - S.reflPoly y +
  ((S.aux Sign.pos).map fun e =>
    e.w * t.sum (fun k => S.coef k * (S.rad e.rad * y) ^ k * Real.cos (k * e.phase))).sum +
  S.auxTail t Sign.pos

/-- Angular field at radius index `i`, angle `theta`: gas potential `(1/2) log |r e^{i th}-x|^2`
(factor `1/2` is essential) plus, for the negative species, the mirror `(1/2) log|1-r e^{i th}x|^2`;
auxiliary constant and kernel series; the exact external term `(53 sigma_i - radial_i/2)/58`. -/
def angular (t : Trunc) (σ : Sign) (i : ℕ) (θ : ℝ) : ℝ :=
  physL (S.gas σ) (fun x => (1 / 2) * Real.log ((S.rad i) ^ 2 - 2 * S.rad i * x * Real.cos θ + x ^ 2)) +
  (if σ = Sign.neg then
    physL (S.gas σ) (fun x =>
      (1 / 2) * Real.log (1 - 2 * S.rad i * x * Real.cos θ + (S.rad i) ^ 2 * x ^ 2))
   else 0) +
  ((S.aux σ).map fun e =>
    e.w * (-S.sigma (min i e.rad) +
      t.sum (fun k => S.coef k *
        ((S.rad (max i e.rad) / S.rad (min i e.rad)) ^ k +
          (if σ = Sign.neg then (S.rad i * S.rad e.rad) ^ k else 0)) *
        Real.cos (k * e.phase) * Real.cos (k * θ)))).sum +
  (53 * S.sigma i - S.radial i / 2) / 58 + S.auxTail t σ

/-! ### Cap predicates (one per component) and the bundle -/

/-- Domain of free rows: `[-1,0) ∪ (0,1)`. -/
def rowDom : Set ℝ := Ico (-1 : ℝ) 0 ∪ Ioo 0 1
/-- Domain of the ordinary marked rows in the `t=|x|` coordinate. -/
def ordDom : Sign → Set ℝ
  | Sign.neg => Icc (19501 / 100000 : ℝ) 1
  | Sign.pos => Icc (98749 / 1000000 : ℝ) 1

/-- `anchorFreeRow(a,sign,t)`: both signs, cap `c`. -/
def FreeRowCap (t : Trunc) (a : Fin 2) (c : ℝ) : Prop :=
  ∀ x ∈ rowDom, S.freeRow t a x ≤ c
/-- `anchorFreeColumn(a,c)` on `0<s<1`. -/
def FreeColCap (a : Fin 2) (c : ℝ) : Prop :=
  ∀ s ∈ Ioo (0 : ℝ) 1, S.colField a s ≤ c
/-- `ordinaryMarked(sign,t)` with the node correction `d` (GP §11.1: `δ̂/58`) on the window `G`:
`ordField + d ≤ c` wherever `G` holds.  `d = 0`, `G = True` is the original cap. -/
def OrdCap (t : Trunc) (σ : Sign) (d : ℝ → ℝ) (G : ℝ → Prop) (c : ℝ) : Prop :=
  ∀ s ∈ ordDom σ, G ((if σ = Sign.neg then -1 else 1) * s) →
    S.ordField t σ ((if σ = Sign.neg then -1 else 1) * s) +
      d ((if σ = Sign.neg then -1 else 1) * s) ≤ c
/-- `nearMarked(y)` on `0<y<1` with the node correction `d` on the window `G`. -/
def NearCap (t : Trunc) (d : ℝ → ℝ) (G : ℝ → Prop) (c : ℝ) : Prop :=
  ∀ y ∈ Ioo (0 : ℝ) 1, G y → S.nearField t y + d y ≤ c
/-- `angular(sign,i,theta)`: every active radius index, every real angle. -/
def AngCap (t : Trunc) (σ : Sign) (c : ℝ) : Prop :=
  ∀ i, i < S.nRad → ∀ θ : ℝ, S.angular t σ i θ ≤ c

/-- The cap bundle consumed by the completed-gas / two-anchor tangent. `gasI` and `anchI` are the
exact intercept values owned by C8/C9 (bound by their own modules to the same source). -/
structure CapBundle (t : Trunc) (d : ℝ → ℝ) (G : ℝ → Prop) (gasI : ℝ) (anchI : Fin 2 → ℝ) where
  rowCap : Fin 2 → ℝ
  colCap : Fin 2 → ℝ
  ordCap : Sign → ℝ
  nearCap : ℝ
  angCap : Sign → ℝ
  gasICap : ℝ
  anchICap : Fin 2 → ℝ
  row : ∀ a, S.FreeRowCap t a (rowCap a)
  col : ∀ a, S.FreeColCap a (colCap a)
  ord : ∀ σ, S.OrdCap t σ d G (ordCap σ)
  near : S.NearCap t d G nearCap
  ang : ∀ σ, S.AngCap t σ (angCap σ)
  gasI_le : gasI ≤ gasICap
  anchI_le : ∀ a, anchI a ≤ anchICap a

/-- Exact-field <= finite-upper dominance (fixed positive tail counted once, inside `finite K`). -/
structure Dominates (K : ℕ) : Prop where
  row : ∀ a, ∀ x ∈ rowDom, S.freeRow Trunc.exact a x ≤ S.freeRow (Trunc.finite K) a x
  ord : ∀ σ, ∀ s ∈ ordDom σ,
    S.ordField Trunc.exact σ ((if σ = Sign.neg then -1 else 1) * s) ≤
      S.ordField (Trunc.finite K) σ ((if σ = Sign.neg then -1 else 1) * s)
  near : ∀ y ∈ Ioo (0 : ℝ) 1, S.nearField Trunc.exact y ≤ S.nearField (Trunc.finite K) y
  ang : ∀ σ, ∀ i, i < S.nRad → ∀ θ : ℝ, S.angular Trunc.exact σ i θ ≤ S.angular (Trunc.finite K) σ i θ

/-- A bundle for the finite upper surrogates gives the bundle for the exact fields. -/
def CapBundle.toExact {K : ℕ} (hd : S.Dominates K) {d : ℝ → ℝ} {G : ℝ → Prop} {gasI : ℝ}
    {anchI : Fin 2 → ℝ}
    (B : S.CapBundle (Trunc.finite K) d G gasI anchI) : S.CapBundle Trunc.exact d G gasI anchI where
  rowCap := B.rowCap
  colCap := B.colCap
  ordCap := B.ordCap
  nearCap := B.nearCap
  angCap := B.angCap
  gasICap := B.gasICap
  anchICap := B.anchICap
  row a x hx := (hd.row a x hx).trans (B.row a x hx)
  col := B.col
  ord σ s hs hG := (add_le_add_left (hd.ord σ s hs) _).trans (B.ord σ s hs hG)
  near y hy hG := (add_le_add_left (hd.near y hy) _).trans (B.near y hy hG)
  ang σ i hi θ := (hd.ang σ i hi θ).trans (B.ang σ i hi θ)
  gasI_le := B.gasI_le
  anchI_le := B.anchI_le

/-- Tangent consumer (T4): the averaged free-row plus free-column fields at an anchor are bounded
by the two caps. This is the hypothesis shape `hR`, `hC` of the finite free-Q cap consumer. -/
theorem free_average_le {r : ℕ} (t : Trunc) (a : Fin 2) {R C : ℝ}
    (hR : S.FreeRowCap t a R) (hC : S.FreeColCap a C)
    (xs ss : Fin r → ℝ) (hx : ∀ i, xs i ∈ rowDom) (hs : ∀ i, ss i ∈ Ioo (0 : ℝ) 1) :
    (∑ i, S.freeRow t a (xs i)) + (∑ i, S.colField a (ss i)) ≤ (r : ℝ) * (R + C) := by
  have h1 : (∑ i, S.freeRow t a (xs i)) ≤ ∑ _i : Fin r, R :=
    Finset.sum_le_sum fun i _ => hR _ (hx i)
  have h2 : (∑ i, S.colField a (ss i)) ≤ ∑ _i : Fin r, C :=
    Finset.sum_le_sum fun i _ => hC _ (hs i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
  nlinarith

end CapSource

end

end CatalanMeasure.GenD.Signed.RouteI.CapFields
