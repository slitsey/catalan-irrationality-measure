module

public import CatalanCore.Uniform.Decay.Polygon.Data

@[expose] public section

/-!
# D5 adapter, part 1: the normalisation `Γ_r = r Γ + h_r`, `N0 = ⌊r0 r⌋ - n0off`

Part 2 of the paper fixes a normalised polygon `p₀ = -r0, p₁, …, p_m` (rational, `Im p_j > 0`) and
the physical path `Γ_r = r Γ + h_r` with `h_r = r0 r - N0 - xs`, `N0 = ⌊r0 r⌋ - n0off`.
D4's `polygon_sourceRep` is stated for the physical vertices `x* + r (p_j - p₀)`,
`x* = -N0 - xs`.  This module identifies the two and discharges, for all large `r`, the three
explicit side conditions of `polygon_sourceRep`:

* `physPts_eq_scaled` : `x* + r (p_j + r0) = r p_j + h_r` (vertex-wise) and `xstar_eq_base`;
* `hShift_abs_le` : `|h_r| ≤ 1 + n0off + xs`  (so `H = 1 + n0off + xs` as in the paper);
* `polygonRep_scaled` : for `r ≥ Rmin` (one explicit threshold), the `SourceRep` for the scaled
  path with the `r`-independent cotangent constant `CP` and growth constant
  `|x*| + r vRat ≤ r (r0 + vRat) + xs`.
-/

open MeasureTheory Set Filter Topology Complex
open CatalanCore.Uniform.Decay.Polygon

namespace CatalanCore.Uniform.Decay.Assembly

variable {Fr : Frame}

/-- The head size `N0 = ⌊r0 r⌋ - n0off` (truncated subtraction; eventually the exact value). -/
noncomputable def N0Of (Fr : Frame) (r0 : ℚ) (r : ℝ) : ℕ := ⌊(r0 : ℝ) * r⌋₊ - Fr.n0off

/-- The horizontal shift `h_r = r0 r - N0 - xs`. -/
noncomputable def hShift (Fr : Frame) (r0 : ℚ) (r : ℝ) : ℝ :=
  (r0 : ℝ) * r - (N0Of Fr r0 r : ℝ) - (Fr.xs : ℝ)

/-- The vertex `p_j` as a complex number. -/
def vertC (p : ℚ × ℚ) : ℂ := ⟨(p.1 : ℝ), (p.2 : ℝ)⟩

theorem xstar_eq_base (Fr : Frame) (r0 : ℚ) (r : ℝ) :
    Fr.xstar (N0Of Fr r0 r) = r * (-(r0 : ℝ)) + hShift Fr r0 r := by
  unfold Frame.xstar hShift; ring

/-- Physical vertices: `x* + r (p_j - p₀) = r p_j + h_r`. -/
theorem physPts_eq_scaled (P : RatPolygon) (Fr : Frame) (r : ℝ) :
    P.physPts (Fr.xstar (N0Of Fr P.r0 r)) r
      = P.verts.map (fun p => (r : ℂ) * vertC p + (hShift Fr P.r0 r : ℂ)) := by
  unfold RatPolygon.physPts
  refine List.map_congr_left (fun p _ => ?_)
  apply Complex.ext <;>
    simp [RatPolygon.off, vertC, hShift, Frame.xstar] <;>
    push_cast <;> ring

theorem N0Of_cast {Fr : Frame} {r0 : ℚ} {r : ℝ} (h : Fr.n0off ≤ ⌊(r0 : ℝ) * r⌋₊) :
    (N0Of Fr r0 r : ℝ) = (⌊(r0 : ℝ) * r⌋₊ : ℝ) - Fr.n0off := by
  unfold N0Of; rw [Nat.cast_sub h]

theorem hShift_bounds {Fr : Frame} {r0 : ℚ} {r : ℝ} (hr0 : 0 < r0) (hr : 0 ≤ r)
    (h : Fr.n0off ≤ ⌊(r0 : ℝ) * r⌋₊) :
    (Fr.n0off : ℝ) - Fr.xs ≤ hShift Fr r0 r ∧ hShift Fr r0 r < (Fr.n0off : ℝ) + 1 - Fr.xs := by
  have hx : 0 ≤ (r0 : ℝ) * r := mul_nonneg (by exact_mod_cast hr0.le) hr
  have h1 := Nat.floor_le hx
  have h2 := Nat.lt_floor_add_one ((r0 : ℝ) * r)
  unfold hShift
  rw [N0Of_cast h]
  constructor <;> linarith

theorem hShift_abs_le (hC : Fr.ContourOK) {r0 : ℚ} {r : ℝ} (hr0 : 0 < r0) (hr : 0 ≤ r)
    (h : Fr.n0off ≤ ⌊(r0 : ℝ) * r⌋₊) :
    |hShift Fr r0 r| ≤ 1 + Fr.n0off + Fr.xs := by
  obtain ⟨h1, h2⟩ := hShift_bounds hr0 hr h
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
  have hn : (0 : ℝ) ≤ Fr.n0off := Nat.cast_nonneg _
  rw [abs_le]; constructor <;> linarith

/-- The head abscissa on the normalised scale: `x*/r = -r0 + h_r / r`. -/
theorem xstar_div (Fr : Frame) (r0 : ℚ) {r : ℝ} (hr : r ≠ 0) :
    Fr.xstar (N0Of Fr r0 r) / r = -(r0 : ℝ) + hShift Fr r0 r / r := by
  rw [xstar_eq_base]; field_simp

/-! ### Explicit thresholds -/

/-- `max_j 1 / Im p_j` (so `1 ≤ r Im p_j` for `r` at least this). -/
noncomputable def _root_.CatalanCore.Uniform.Decay.Polygon.RatPolygon.invIm (P : RatPolygon) : ℚ := (P.verts.map (fun p => 1 / p.2)).foldr max 0

theorem _root_.CatalanCore.Uniform.Decay.Polygon.RatPolygon.le_invIm (P : RatPolygon) {p : ℚ × ℚ} (hp : p ∈ P.verts) : 1 / p.2 ≤ P.invIm := by
  unfold RatPolygon.invIm
  have key : ∀ (l : List ℚ), ∀ x ∈ l, x ≤ l.foldr max 0 := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro x hx
      rcases List.mem_cons.1 hx with h | h
      · rw [h]; exact le_max_left _ _
      · exact (ih x h).trans (le_max_right _ _)
  exact key _ _ (List.mem_map.2 ⟨p, hp, rfl⟩)

/-- The scale threshold: `r ≥ Rmin` gives `r > 0`, `1 ≤ r Im p_j`, `n0off ≤ ⌊r0 r⌋` and
`x* + |q| ≤ -1`. -/
noncomputable def Rmin (Fr : Frame) (P : RatPolygon) : ℝ :=
  max 1 (max (P.invIm : ℝ) ((|(P.qRat : ℝ)| + 2 + Fr.n0off) / (P.r0 : ℝ)))

theorem high_of_ge {P : RatPolygon} (hP : P.OK) {r : ℝ} (hr : (P.invIm : ℝ) ≤ r) :
    ∀ p ∈ P.verts, 1 ≤ r * (p.2 : ℝ) := by
  intro p hp
  have hp2 : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast hP.upper p hp
  have h1 : (1 : ℝ) / (p.2 : ℝ) ≤ (P.invIm : ℝ) := by exact_mod_cast P.le_invIm hp
  rw [div_le_iff₀ hp2] at h1
  nlinarith

theorem floor_ge {Fr : Frame} {P : RatPolygon} (hP : P.OK) {r : ℝ}
    (hr : (|(P.qRat : ℝ)| + 2 + Fr.n0off) / (P.r0 : ℝ) ≤ r) :
    |(P.qRat : ℝ)| + 1 + Fr.n0off ≤ (⌊(P.r0 : ℝ) * r⌋₊ : ℝ) := by
  have hr0 : (0 : ℝ) < (P.r0 : ℝ) := by exact_mod_cast hP.r0_pos
  rw [div_le_iff₀ hr0] at hr
  have hx : 0 ≤ (P.r0 : ℝ) * r := by
    have : 0 ≤ |(P.qRat : ℝ)| + 2 + Fr.n0off := by positivity
    nlinarith
  have := Nat.lt_floor_add_one ((P.r0 : ℝ) * r)
  linarith

/-- **D5 adapter, normalisation.**  For every scale `r ≥ Rmin`, the physical polygon
`r Γ + h_r` carries the full source representation of D4, with the `r`-independent cotangent
constant `CP Fr q`, growth constant `|x*| + r vRat`, and shift `|h_r| ≤ 1 + n0off + xs`. -/
theorem polygonRep_scaled (hC : Fr.ContourOK) {P : RatPolygon} (hP : P.OK) {r : ℝ}
    (hr : Rmin Fr P ≤ r) :
    SourceRep Fr (N0Of Fr P.r0 r)
        (P.verts.map (fun p => (r : ℂ) * vertC p + (hShift Fr P.r0 r : ℂ))) P.tailDir
        (CP Fr (P.qRat : ℝ)) (|Fr.xstar (N0Of Fr P.r0 r)| + r * (P.vRat : ℝ)) ∧
      |hShift Fr P.r0 r| ≤ 1 + Fr.n0off + Fr.xs := by
  have hr0 : (0 : ℝ) < (P.r0 : ℝ) := by exact_mod_cast hP.r0_pos
  have hr1 : (1 : ℝ) ≤ r := (le_max_left _ _).trans hr
  have hrpos : 0 < r := by linarith
  have hinv : (P.invIm : ℝ) ≤ r := ((le_max_left _ _).trans (le_max_right _ _)).trans hr
  have hq : (|(P.qRat : ℝ)| + 2 + Fr.n0off) / (P.r0 : ℝ) ≤ r :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hr
  have hfl := floor_ge (Fr := Fr) hP hq
  have hn : Fr.n0off ≤ ⌊(P.r0 : ℝ) * r⌋₊ := by
    have : (Fr.n0off : ℝ) ≤ (⌊(P.r0 : ℝ) * r⌋₊ : ℝ) := by
      have : 0 ≤ |(P.qRat : ℝ)| := abs_nonneg _
      linarith
    exact_mod_cast this
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
  have hfar : Fr.xstar (N0Of Fr P.r0 r) + |(P.qRat : ℝ)| ≤ -1 := by
    unfold Frame.xstar
    rw [N0Of_cast hn]
    linarith
  refine ⟨?_, hShift_abs_le hC hP.r0_pos hrpos.le hn⟩
  rw [← physPts_eq_scaled]
  exact polygon_sourceRep hC hP (N0Of Fr P.r0 r) hrpos (high_of_ge hP hinv) hfar

/-- The growth constant is `O(r)` with an explicit linear bound. -/
theorem growth_const_le (hC : Fr.ContourOK) {P : RatPolygon} (hP : P.OK) {r : ℝ}
    (hr : Rmin Fr P ≤ r) :
    |Fr.xstar (N0Of Fr P.r0 r)| + r * (P.vRat : ℝ)
      ≤ r * ((P.r0 : ℝ) + (P.vRat : ℝ)) + Fr.xs := by
  have hr0 : (0 : ℝ) < (P.r0 : ℝ) := by exact_mod_cast hP.r0_pos
  have hrpos : 0 < r := by have := (le_max_left _ _).trans hr; linarith
  have hx := xstar_eq_base Fr P.r0 r
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
  have hq : (|(P.qRat : ℝ)| + 2 + Fr.n0off) / (P.r0 : ℝ) ≤ r :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hr
  have hfl := floor_ge (Fr := Fr) hP hq
  have hn : Fr.n0off ≤ ⌊(P.r0 : ℝ) * r⌋₊ := by
    have : (Fr.n0off : ℝ) ≤ (⌊(P.r0 : ℝ) * r⌋₊ : ℝ) := by
      have : 0 ≤ |(P.qRat : ℝ)| := abs_nonneg _
      linarith
    exact_mod_cast this
  have hxneg : Fr.xstar (N0Of Fr P.r0 r) ≤ 0 := by
    unfold Frame.xstar
    have : (0 : ℝ) ≤ (N0Of Fr P.r0 r : ℝ) := Nat.cast_nonneg _
    linarith
  have hfloor := Nat.floor_le (mul_nonneg hr0.le hrpos.le)
  rw [abs_of_nonpos hxneg]
  unfold Frame.xstar
  rw [N0Of_cast hn]
  have hn0 : (0 : ℝ) ≤ Fr.n0off := Nat.cast_nonneg _
  nlinarith

end CatalanCore.Uniform.Decay.Assembly
