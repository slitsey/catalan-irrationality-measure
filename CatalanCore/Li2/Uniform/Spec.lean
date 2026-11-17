module

public import CatalanCore.Decay.CurveFamily
public import CatalanCore.Li2.Family
public import CatalanCore.Uniform.Measure.NV0

@[expose] public section

/-! Shared definition and structure API, C8/C9/C10. No theorem proof is implemented here. -/
open MeasureTheory Set Filter Complex
open scoped Topology BigOperators

namespace CatalanCore.Li2.Uniform

structure DualFrame where
  lattice : Set ℝ
  free : ℤ → Set ℂ
  lattice_mem : ∀ x ∈ lattice, 0 ≤ x
  lattice_kind : lattice = Ici 0 ∨ ∃ c : ℝ, 0 ≤ c ∧ lattice = Icc 0 c
  pure : Bool
  pure_lattice : pure = true → lattice = Ici 0
  pure_free : pure = true → ∀ s, free s = ∅

structure PolygonFrame where
  cut : ℝ
  nonneg : 0 ≤ cut
  edges : ℕ
  edges_pos : 0 < edges
  vertex : ℕ → ℂ
  initial : vertex 0 = (cut:ℂ)
  real_pos : ∀ j, 1 ≤ j → j ≤ edges → 0 < (vertex j).re
  imag_strict : ∀ i j, i < j → j ≤ edges → (vertex i).im < (vertex j).im

noncomputable def polygonPieces (g : PolygonFrame) : List CatalanCore.Decay.CurveFamily.Piece :=
  (List.range g.edges).map (fun j =>
    ⟨g.vertex j, g.vertex (j+1)-g.vertex j, false⟩) ++
      [⟨g.vertex g.edges, Complex.I, true⟩]
def pieceSet (p : CatalanCore.Decay.CurveFamily.Piece) : Set ℂ :=
  p.zeta '' (if p.ray then Ici 0 else Icc 0 1)
def piecesSet (ps : List CatalanCore.Decay.CurveFamily.Piece) : Set ℂ := ⋃ p ∈ ps, pieceSet p
noncomputable def polygonSet (g : PolygonFrame) : Set ℂ :=
  piecesSet (polygonPieces g) ∪ (starRingEnd ℂ '' piecesSet (polygonPieces g))
noncomputable def polygonFree (g : PolygonFrame) (s : ℤ) : Set ℂ :=
  polygonSet g ∪ (if s=1 then ofReal '' Ici g.cut else ∅)

inductive FrameGeometry (F : DualFrame) : Type
  | pure (hp : F.pure=true) (hl : F.lattice=Ici 0)
      (hf : ∀ s : ℤ, F.free s=∅) : FrameGeometry F
  | polygon (g : PolygonFrame) (hp : F.pure=false)
      (hl : F.lattice=Icc 0 g.cut)
      (hf : ∀ s : ℤ, F.free s=polygonFree g s) : FrameGeometry F

def GoodFrame (F : DualFrame) : Prop := Nonempty (FrameGeometry F)
def frameCut {F : DualFrame} : FrameGeometry F → Option ℝ
  | .pure _ _ _ => none
  | .polygon g _ _ _ => some g.cut
noncomputable def free (F : DualFrame) (z : ℝ) : Set ℂ :=
  F.free (if 0 < z then 1 else -1)
def lat (F : DualFrame) : Set ℝ := F.lattice

noncomputable def pieceArc (p : CatalanCore.Decay.CurveFamily.Piece) : Measure ℂ :=
  ENNReal.ofReal ‖p.D‖ • p.nu.map p.zeta
noncomputable def piecesArc (ps : List CatalanCore.Decay.CurveFamily.Piece) : Measure ℂ :=
  (ps.map pieceArc).sum
noncomputable def arcLength {F : DualFrame} (g : FrameGeometry F) (s : ℤ) : Measure ℂ :=
  match g with
  | .pure _ _ _ => 0
  | .polygon p _ _ _ =>
      piecesArc (polygonPieces p) + piecesArc ((polygonPieces p).map CatalanCore.Decay.CurveFamily.Piece.conj) +
      (if s=1 then (volume.restrict (Ici p.cut)).map ofReal else 0)

noncomputable def crossing (g : PolygonFrame) (n : ℕ) : ℝ :=
  (Nat.floor (g.cut*(n:ℝ)):ℝ)+1/2
noncomputable def firstAtOne (g : PolygonFrame) (n : ℕ) : ℂ :=
  ((n:ℝ)*g.cut + ((g.vertex 1).re-g.cut)/(g.vertex 1).im:ℂ)+Complex.I
noncomputable def upperModified (g : PolygonFrame) (n : ℕ) : List CatalanCore.Decay.CurveFamily.Piece :=
  CatalanCore.Decay.CurveFamily.chainPieces ([(crossing g n:ℂ), (crossing g n:ℂ)+Complex.I, firstAtOne g n] ++
    (List.range g.edges).map (fun j => (n:ℂ)*g.vertex (j+1))) ++
    [⟨(n:ℂ)*g.vertex g.edges, Complex.I, true⟩]
noncomputable def gammaN {F : DualFrame} (g : FrameGeometry F) (n : ℕ) : Set ℂ :=
  match g with
  | .pure _ _ _ => ∅
  | .polygon p _ _ _ => piecesSet (upperModified p n) ∪
      piecesSet ((upperModified p n).map CatalanCore.Decay.CurveFamily.Piece.conj)
noncomputable def contourSet {F : DualFrame} (g : FrameGeometry F) : Set ℂ :=
  match g with
  | .pure _ _ _ => ∅
  | .polygon p _ _ _ => polygonSet p
noncomputable def contourArcN {F : DualFrame} (g : FrameGeometry F) (n : ℕ) : Measure ℂ :=
  match g with
  | .pure _ _ _ => 0
  | .polygon p _ _ _ => piecesArc (upperModified p n) +
      piecesArc ((upperModified p n).map CatalanCore.Decay.CurveFamily.Piece.conj)
noncomputable def pieceIntegral (p : CatalanCore.Decay.CurveFamily.Piece) (f : ℂ → ℂ) : ℂ :=
  ∫ t, f (p.zeta t)*p.D ∂p.nu
noncomputable def lineIntegral {F : DualFrame} (g : FrameGeometry F)
    (n : ℕ) (f : ℂ → ℂ) : ℂ :=
  match g with
  | .pure _ _ _ => 0
  | .polygon p _ _ _ =>
      -((upperModified p n).map (fun q => pieceIntegral q f)).sum +
      (((upperModified p n).map CatalanCore.Decay.CurveFamily.Piece.conj).map (fun q => pieceIntegral q f)).sum
noncomputable def replacementUpper (p : PolygonFrame) (n : ℕ) : List CatalanCore.Decay.CurveFamily.Piece :=
  CatalanCore.Decay.CurveFamily.chainPieces [(crossing p n:ℂ), (crossing p n:ℂ)+Complex.I, firstAtOne p n]
noncomputable def replacement {F : DualFrame} (g : FrameGeometry F) (n : ℕ) : Set ℂ :=
  match g with
  | .pure _ _ _ => ∅
  | .polygon p _ _ _ => piecesSet (replacementUpper p n) ∪
      piecesSet ((replacementUpper p n).map CatalanCore.Decay.CurveFamily.Piece.conj)
noncomputable def replacementLength {F : DualFrame} (g : FrameGeometry F) (n : ℕ) : ℝ :=
  match g with
  | .pure _ _ _ => 0
  | .polygon p _ _ _ => 2*((replacementUpper p n).map (fun q => ‖q.D‖)).sum


noncomputable def phi0 (u : ℂ) : ℝ :=
  3 * (∫ x in (0 : ℝ)..1, Real.log ‖u + (x : ℂ)‖) -
    (∫ x in (0 : ℝ)..4, Real.log ‖u + (x : ℂ)‖)
noncomputable def pot (σ : Measure ℂ) (u : ℂ) : ℝ := ∫ y, -Real.log ‖u - y‖ ∂σ
noncomputable def energy (σ : Measure ℂ) : ℝ := ∫ u, pot σ u ∂σ

structure DualDatum where
  σ : Measure ℂ
  finite : IsFiniteMeasure σ
  mass : σ.real univ = 2
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  bounded : ∀ᵐ z ∂σ, ‖z‖ ≤ radius
  holderExponent : ℝ
  holderPos : 0 < holderExponent
  holderLe : holderExponent ≤ 1
  holderConstant : NNReal
  holder : ∀ u v : ℂ, |pot σ u - pot σ v| ≤
    (holderConstant : ℝ) * ‖u - v‖ ^ holderExponent
  pointLogIntegrable : ∀ u : ℂ, Integrable (fun y => Real.log ‖u - y‖) σ
  selfIntegrable : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (σ.prod σ)
  selfDistinct : ∀ᵐ p ∂(σ.prod σ), p.1 ≠ p.2

noncomputable def signOf (z : ℝ) : ℤ := if 0 < z then 1 else -1
noncomputable def W (s : ℤ) (t : ℝ) (d : DualDatum) (u : ℂ) : ℝ :=
  phi0 u - t * u.re - (if s = 1 then 2 * Real.pi else Real.pi) * |u.im| - 2 * pot d.σ u
noncomputable def A (t r : ℝ) (d : DualDatum) (x : ℝ) : ℝ :=
  phi0 (-(x : ℂ)) + t * x - r - 2 * pot d.σ (-(x : ℂ))
def Admissible (F : DualFrame) (s : ℤ) (t : ℝ) (d : DualDatum) (θ : ℝ) : Prop :=
  ∀ u ∈ F.free s, W s t d u ≤ θ
noncomputable def dual (F : DualFrame) (s : ℤ) (t r : ℝ) (d : DualDatum) (θ : ℝ) : ℝ :=
  -(12 * Real.log 2 + 4) - energy d.σ - 2 * θ -
    2 * (∫ x in F.lattice, max (W s t d (x : ℂ) - θ) 0) -
    (∫ x in (1 : ℝ)..4, max (A t r d x - θ) 0)
def CapIntegrable (F : DualFrame) (s : ℤ) (t r : ℝ) (d : DualDatum) (θ : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => max (W s t d (x : ℂ) - θ) 0) F.lattice ∧
    IntervalIntegrable (fun x => max (A t r d x - θ) 0) volume 1 4
def WindowBound (z : ℚ) (r D : ℝ) : Prop :=
  CatalanCore.Uniform.HasScaledDecay (CatalanCore.Li2.li2Family z)
    CatalanCore.Li2.scale D r

attribute [instance] DualDatum.finite

end CatalanCore.Li2.Uniform

#print axioms CatalanCore.Li2.Uniform.FrameGeometry
#print axioms CatalanCore.Li2.Uniform.DualDatum
#print axioms CatalanCore.Li2.Uniform.gammaN
#print axioms CatalanCore.Li2.Uniform.dual
#print axioms CatalanCore.Li2.Uniform.WindowBound
