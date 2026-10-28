module

public import CatalanCore.Uniform.Decay.Spline.Final
public import CatalanCore.Uniform.Decay.Spline.PolyBridge
public import CatalanCore.Uniform.Decay.Cert.Cover

@[expose] public section

/-!
# Rational spline-trial data and its elementary Boolean checks (lane D, package D5)

`SplineData` is the raw rational data of a signed polynomial-on-segments trial measure (one
`Seg` per segment: endpoints `A_i, B_i`, density coefficient list, Bernstein bound `M_i`, conjugate
index) together with the certificate numbers (`r0, W, umax, m', g_min, S_cap, I_bound, c_cert`), the
cover lists and the bridge tolerances.  `basicOk` is the Boolean check of every *elementary*
obligation:

* `A_i ≠ B_i`, nonempty coefficient lists, Bernstein `|f_i| ≤ M_i` (`bernOkK`, both signs);
* exact mass one;
* conjugation involution `τ` (`A_{τ i} = conj A_i`, `B_{τ i} = conj B_i`, `f_{τ i} = f_i`);
* radius bound `‖A_i‖,‖B_i‖ ≤ R_c`, smoothing-loss bound `π ρ B_s ≤ lossS`;
* the covers of `[0, umax]` (ray) and `[0, 1]` (line);
* `0 ≤ c_cert`, `2 (m' - g_min) ≤ c_cert`, and the decay target `D ≤ Dof - bridgeLoss`.

`basicOk_sound` extracts the semantic facts.
-/

namespace CatalanCore.Uniform.Decay.Cert

open Finset CatalanCore.Uniform.Decay.Spline CatalanCore.Uniform.Decay.Tools

/-- One segment of the trial measure. -/
structure Seg where
  ax : ℚ
  ay : ℚ
  bx : ℚ
  byy : ℚ
  coef : List ℚ
  M : ℚ
  Lq : ℚ
  tau : ℕ

/-- The full finite data of a spline certificate. -/
structure SplineData where
  segs : List Seg
  sl : ℚ
  Mq : ℚ
  ε : ℚ
  r0 : ℚ
  W : ℚ
  umax : ℚ
  mprime : ℚ
  gmin : ℚ
  Scap : ℚ
  Ibound : ℚ
  ccert : ℚ
  rayBoxes : List (ℚ × ℚ)
  lineCells : List (ℚ × ℚ)
  rho : ℚ
  theta : ℚ
  etaS : ℚ
  lossS : ℚ
  Rc : ℚ
  Inu : ℚ
  Dt : ℚ
  dim : ℕ

namespace SplineData

variable (D : SplineData)

/-- Number of segments. -/
abbrev n : ℕ := D.segs.length

/-- Segment `i`. -/
def seg (i : Fin D.n) : Seg := D.segs[i.1]'i.2

/-- Segment start point. -/
def A (i : Fin D.n) : ℂ := ⟨((D.seg i).ax : ℝ), ((D.seg i).ay : ℝ)⟩

/-- Segment end point. -/
def B (i : Fin D.n) : ℂ := ⟨((D.seg i).bx : ℝ), ((D.seg i).byy : ℝ)⟩

/-- Density coefficient list. -/
def l (i : Fin D.n) : List ℚ := (D.seg i).coef

/-- Density as a function. -/
noncomputable def f (i : Fin D.n) : ℝ → ℝ := ratPoly (D.l i)

/-- Bernstein bound. -/
def M (i : Fin D.n) : ℚ := (D.seg i).M

/-- Conjugate index (a safe lookup). -/
def tauF (i : Fin D.n) : Fin D.n :=
  if h : (D.seg i).tau < D.n then ⟨(D.seg i).tau, h⟩ else i

/-- The total variation `V = 1` (nonnegative densities). -/
def V (_D : SplineData) : ℚ := 1

/-- Exact mass of one density. -/
def massOf (l : List ℚ) : ℚ := ∑ j ∈ range (l.length - 1 + 1), coeffs l j / ((j : ℚ) + 1)

/-- The arclength-density sum, rationally bounded. -/
def BsQ : ℚ := ∑ i : Fin D.n, (D.M i) / (D.seg i).Lq

/-- Per-segment elementary checks. -/
def segOk (i : Fin D.n) : Bool :=
  let s := D.seg i
  decide (s.ax ≠ s.bx ∨ s.ay ≠ s.byy) && decide (s.coef ≠ []) && bernOkK s.coef 0 s.M &&
  decide (0 < s.Lq) && decide (0 ≤ s.M) && decide (s.Lq ^ 2 ≤ (s.bx - s.ax) ^ 2 + (s.byy - s.ay) ^ 2) &&
  decide (s.ax ^ 2 + s.ay ^ 2 ≤ D.Rc ^ 2) && decide (s.bx ^ 2 + s.byy ^ 2 ≤ D.Rc ^ 2) &&
  decide (s.tau < D.n)

/-- Conjugation-pair checks (index `i`, partner `tauF i`). -/
def conjOk (i : Fin D.n) : Bool :=
  let s := D.seg i
  let t := D.seg (D.tauF i)
  decide (t.ax = s.ax) && decide (t.ay = -s.ay) && decide (t.bx = s.bx) && decide (t.byy = -s.byy) &&
  decide (t.coef = s.coef) && decide ((D.seg (D.tauF i)).tau = i.1)

/-- Bridge decay exponent target check. -/
def dofOk : Bool :=
  let V := D.V
  decide (D.Dt ≤ 2 * (D.Mq * D.mprime + D.dim * D.Scap) - D.Mq ^ 2 * D.Ibound + D.Inu
    - (2 * D.Mq ^ 2 * (D.lossS + D.theta) + 2 * D.dim * D.etaS
      + D.Mq ^ 2 * (V * D.lossS + 2 * V * D.theta)))

/-- All elementary checks. -/
def basicOk : Bool :=
  decide (0 < D.Mq) && decide (0 < D.ε) && decide (D.ε < 1) && decide (0 < D.r0) && decide (0 < D.W) &&
  decide (0 < D.rho) && decide (0 < D.theta) && decide (0 < D.etaS) && decide (0 ≤ D.Rc) &&
  decide (0 ≤ D.ccert) && decide (2 * (D.mprime - D.gmin) ≤ D.ccert) &&
  (List.finRange D.n).all D.segOk && (List.finRange D.n).all D.conjOk &&
  decide (∑ i : Fin D.n, massOf (D.l i) = 1) &&
  decide (0 ≤ D.lossS) && decide ((315 / 100 : ℚ) * D.rho * D.BsQ ≤ D.lossS) &&
  coverOk 0 D.umax D.rayBoxes && coverOk 0 1 D.lineCells && D.dofOk

end SplineData

end CatalanCore.Uniform.Decay.Cert
