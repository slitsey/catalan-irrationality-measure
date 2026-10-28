module

public import CatalanCore.Uniform.Decay.Polygon.Mass

@[expose] public section

/-!
# Fixed finite rational upper polygons and the polygon source theorem (Part 2)

A normalised polygon is `p₀ = -r0`, rational vertices `p₁, …, p_m` (stored as `(Re, Im)`), and
a northwest tail `p_m + u(-1 + i s)`.  At scale `r` and head size `N0`, the physical upper path
is `x* + r (p_j - p₀)` (`x* = -N0 - xs`), i.e. `r p_j + h_r` with `h_r = r r0 + x*`, followed by
the tail `+ u(-1 + i s)` (any positive rescaling of the tail parameter gives the same integrals).

`RatPolygon.OK`: `r0 > 0`, every `Im p_j > 0`, `s ≥ 1` — the Part 2 admissibility conditions
(`p_j ≠ p_{j-1}` is not needed: zero-length edges are harmless).

**`polygon_sourceRep`** collects the certificate-independent source theorem for the determinant
over a polygon, uniform over all row/column node lists (hence over all deletions):
the exact entry formula, the rectangular Andréief bound, the weight bound with the
cotangent constant `CP Fr (qRat P)` (independent of `r`, `N0`), node distance `≥ 1`,
the growth bound, and the residual mass.  Its extra hypotheses are exact rational tests:
`1 ≤ r Im p_j` for all `j` and `x* + |q| ≤ -1`, where `q = qRat P` is the first-edge inverse
slope (`(Re p₁ + r0)/Im p₁`, or `-1/s` if `m = 0`).  These are the `hyp.py` tests
"`r*Im p_j >= 1`" and "`v + |q| <= -1`".
-/

open MeasureTheory Set Filter Topology Complex

namespace CatalanCore.Uniform.Decay.Polygon

/-- A normalised rational upper polygon: base `-r0`, vertices `(Re p_j, Im p_j)`, tail slope `s`. -/
structure RatPolygon where
  r0 : ℚ
  verts : List (ℚ × ℚ)
  s : ℚ

namespace RatPolygon

/-- Part 2 admissibility of a polygon. -/
structure OK (P : RatPolygon) : Prop where
  r0_pos : 0 < P.r0
  upper : ∀ p ∈ P.verts, 0 < p.2
  slope : 1 ≤ P.s

/-- The tail direction `-1 + i s`. -/
def tailDir (P : RatPolygon) : ℂ := ⟨-1, P.s⟩

/-- Offset of a vertex from the base, `p_j - p₀ = (Re p_j + r0) + i Im p_j`. -/
def off (P : RatPolygon) (p : ℚ × ℚ) : ℂ := ⟨((p.1 + P.r0 : ℚ) : ℝ), ((p.2 : ℚ) : ℝ)⟩

/-- Physical vertices `x + r (p_j - p₀)`. -/
noncomputable def physPts (P : RatPolygon) (x r : ℝ) : List ℂ :=
  P.verts.map (fun p => (x : ℂ) + (r : ℂ) * P.off p)

/-- The first-edge inverse slope `q`. -/
def qRat (P : RatPolygon) : ℚ :=
  match P.verts with
  | [] => -1 / P.s
  | p :: _ => (p.1 + P.r0) / p.2

/-- A rational bound for the vertex offsets: `max_j (|Re p_j + r0| + Im p_j)`. -/
def vRat (P : RatPolygon) : ℚ := (P.verts.map (fun p => |p.1 + P.r0| + |p.2|)).foldr max 0

theorem le_vRat (P : RatPolygon) {p : ℚ × ℚ} (hp : p ∈ P.verts) :
    |p.1 + P.r0| + |p.2| ≤ P.vRat := by
  unfold vRat
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

theorem vRat_nonneg (P : RatPolygon) : 0 ≤ P.vRat := by
  unfold vRat
  generalize (P.verts.map (fun p => |p.1 + P.r0| + |p.2|)) = l
  induction l with
  | nil => simp
  | cons a l ih => exact ih.trans (le_max_right _ _)

theorem tailDir_im (P : RatPolygon) : P.tailDir.im = (P.s : ℝ) := rfl
theorem tailDir_re (P : RatPolygon) : P.tailDir.re = -1 := rfl

theorem tailDir_im_pos {P : RatPolygon} (hP : P.OK) : 0 < P.tailDir.im := by
  rw [tailDir_im]; have := hP.slope; exact_mod_cast (show (0 : ℚ) < P.s by linarith)

theorem tailDir_slope {P : RatPolygon} (hP : P.OK) : |P.tailDir.re| ≤ P.tailDir.im := by
  rw [tailDir_re, tailDir_im]; norm_num; exact_mod_cast hP.slope

theorem mem_physPts {P : RatPolygon} {x r : ℝ} {z : ℂ} (hz : z ∈ P.physPts x r) :
    ∃ p ∈ P.verts, z = (x : ℂ) + (r : ℂ) * P.off p := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz; exact ⟨p, hp, rfl⟩

theorem im_phys (P : RatPolygon) (x r : ℝ) (p : ℚ × ℚ) :
    ((x : ℂ) + (r : ℂ) * P.off p).im = r * (p.2 : ℝ) := by
  simp [off]

theorem physPts_upper {P : RatPolygon} (hP : P.OK) (x : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ z ∈ P.physPts x r, 0 < z.im := by
  intro z hz
  obtain ⟨p, hp, rfl⟩ := mem_physPts hz
  rw [im_phys]; have := hP.upper p hp
  exact mul_pos hr (by exact_mod_cast this)

theorem polyOK {P : RatPolygon} (hP : P.OK) (x : ℝ) {r : ℝ} (hr : 0 < r) :
    PolyOK (P.physPts x r) P.tailDir :=
  ⟨physPts_upper hP x hr, tailDir_im_pos hP⟩

theorem physPts_high {P : RatPolygon} (x r : ℝ) (hhigh : ∀ p ∈ P.verts, 1 ≤ r * (p.2 : ℝ)) :
    ∀ z ∈ P.physPts x r, 1 ≤ z.im := by
  intro z hz
  obtain ⟨p, hp, rfl⟩ := mem_physPts hz
  rw [im_phys]; exact hhigh p hp

theorem qFirst_phys {P : RatPolygon} (hP : P.OK) (x : ℝ) {r : ℝ} (hr : 0 < r) :
    qFirst (x : ℂ) (P.physPts x r) P.tailDir = (P.qRat : ℝ) := by
  unfold qFirst qRat physPts
  cases h : P.verts with
  | nil =>
    simp only [List.map_nil, firstDir, tailDir]
    push_cast; ring
  | cons p l =>
    simp only [List.map_cons, firstDir, add_sub_cancel_left]
    have hp2 : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast hP.upper p (by rw [h]; simp)
    simp only [off, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero]
    push_cast
    field_simp

theorem norm_phys_le (P : RatPolygon) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) {p : ℚ × ℚ}
    (hp : p ∈ P.verts) : ‖(x : ℂ) + (r : ℂ) * P.off p‖ ≤ |x| + r * (P.vRat : ℝ) := by
  have h1 : ‖P.off p‖ ≤ |((p.1 + P.r0 : ℚ) : ℝ)| + |((p.2 : ℚ) : ℝ)| :=
    Complex.norm_le_abs_re_add_abs_im _
  have h2 : |((p.1 + P.r0 : ℚ) : ℝ)| + |((p.2 : ℚ) : ℝ)| ≤ (P.vRat : ℝ) := by
    have := P.le_vRat hp
    have : ((|p.1 + P.r0| + |p.2| : ℚ) : ℝ) ≤ (P.vRat : ℝ) := by exact_mod_cast this
    push_cast at this ⊢; exact this
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hr, Real.norm_eq_abs]
  have := mul_le_mul_of_nonneg_left (h1.trans h2) hr
  linarith

/-- The traversed length of the physical finite edges is `r` times the normalised length
`L_Γ = chainLen 0 (offsets)` (multiplicities counted). -/
theorem chainLen_physPts (P : RatPolygon) (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    chainLen (x : ℂ) (P.physPts x r) = r * chainLen 0 (P.verts.map P.off) := by
  have key : ∀ (l : List ℂ) (a : ℂ), chainLen ((x : ℂ) + (r : ℂ) * a)
      (l.map (fun z => (x : ℂ) + (r : ℂ) * z)) = r * chainLen a l := by
    intro l
    induction l with
    | nil => intro a; simp [chainLen]
    | cons b l ih =>
      intro a
      simp only [List.map_cons, chainLen]
      rw [ih b]
      have : (x : ℂ) + (r : ℂ) * b - ((x : ℂ) + (r : ℂ) * a) = (r : ℂ) * (b - a) := by ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]
      ring
  have h := key (P.verts.map P.off) 0
  rw [mul_zero, add_zero, List.map_map] at h
  exact h

end RatPolygon

/-! ### The polygon source theorem -/

variable {Fr : Frame}

/-- The certificate-independent source representation over a physical polygon `x* → pts → d`
with cotangent constant `C` and growth constant `V`.  Every field is uniform over all node lists. -/
structure SourceRep (Fr : Frame) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (C V : ℝ) : Prop where
  /-- exact entries `norm · T_ab`, all natural `a, b` -/
  entry : ∀ a b : ℕ,
    ∫ z, polyW Fr N0 pts d z * (polyPt Fr N0 pts d z - a)⁻¹ * (polyPt Fr N0 pts d z - b)⁻¹
        ∂(Fr.muT N0) = (((Fr.norm : ℝ) * Fr.Tent a b : ℝ) : ℂ)
  /-- rectangular Andréief bound for every injective row/column list -/
  andreief : ∀ (k : ℕ) (s t : Fin k → ℕ), Function.Injective s → Function.Injective t →
    ‖(Matrix.of fun i j : Fin k => (((Fr.norm : ℝ) * Fr.Tent (s i) (t j) : ℝ) : ℂ)).det‖
      ≤ (1 / (k.factorial : ℝ)) * ∫ z : Fin k → Fr.XT N0,
          (∏ l, ‖polyW Fr N0 pts d (z l)‖) *
            (‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((polyPt Fr N0 pts d (z l') - polyPt Fr N0 pts d (z l)) * ((s l : ℂ) - s l')))
              / ∏ l, ∏ i, (polyPt Fr N0 pts d (z l) - s i)‖ *
            ‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((polyPt Fr N0 pts d (z l') - polyPt Fr N0 pts d (z l)) * ((t l : ℂ) - t l')))
              / ∏ l, ∏ i, (polyPt Fr N0 pts d (z l) - t i)‖) ∂(Measure.pi fun _ => Fr.muT N0)
  /-- head weights -/
  weight_atom : ∀ p : ↥(Fr.atomIdx N0), ‖polyW Fr N0 pts d (Sum.inl p)‖ = |(Fr.w p.1.2 : ℝ)|
  /-- upper weight bound (cotangent separation on the physical path) -/
  weight_up : ∀ u : ℝ, 0 ≤ u → ‖wUpP Fr N0 pts d u‖ ≤ C / (2 * Real.pi)
      * Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|))
      * ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖
  /-- lower weight bound -/
  weight_low : ∀ u : ℝ, 0 ≤ u → ‖wLowP Fr N0 pts d u‖ ≤ C / (2 * Real.pi)
      * Real.exp (-(2 * Real.pi * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|))
      * ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖
  /-- the lower copy is the conjugate of the upper copy -/
  conj_pt : ∀ u : ℝ, pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u
      = starRingEnd ℂ (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u)
  conj_der : ∀ u : ℝ, pathDer (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u
      = starRingEnd ℂ (pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u)
  /-- node distance `≥ 1` from `[0, ∞)` (upper; the lower follows by `conj_pt`) -/
  node_dist : ∀ u : ℝ, 0 ≤ u → ∀ x : ℝ, 0 ≤ x →
      1 ≤ ‖pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u - (x : ℂ)‖
  /-- growth -/
  growth : ∀ u : ℝ, 0 ≤ u → ‖pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖
      ≤ V + 2 * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|
  /-- residual mass of the (upper) path; multiplicities counted -/
  mass : ∀ c : ℝ, 0 < c →
      IntegrableOn (fun u => Real.exp (-(c * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|))
        * ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), Real.exp (-(c * |(pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u).im|))
        * ‖pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u‖
        ≤ chainLen ((Fr.xstar N0 : ℝ) : ℂ) pts + ‖d‖ / (c * d.im)
  /-- the head has at most `d (N0 + ⌈xs⌉)` labels -/
  atoms : (Fr.atomIdx N0).card ≤ (N0 + ⌈(Fr.xs : ℝ)⌉₊) * Fr.d

theorem card_atomIdx_le (Fr : Frame) (N0 : ℕ) :
    (Fr.atomIdx N0).card ≤ (N0 + ⌈(Fr.xs : ℝ)⌉₊) * Fr.d := by
  classical
  unfold Frame.atomIdx
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_fin]

/-- **Polygon source theorem** (Part 2, Lemmas `deform`, `sourcebounds`, Proposition `gram`).
For every frame with `ContourOK`, every admissible rational polygon, every `N0` and every scale
`r > 0` with `1 ≤ r Im p_j` (all `j`) and `x* + |q| ≤ -1`, the physical polygon carries the full
source representation, with cotangent constant `CP Fr q` (independent of `r` and `N0`) and growth
constant `|x*| + r · vRat`. -/
theorem polygon_sourceRep (hC : Fr.ContourOK) {P : RatPolygon} (hP : P.OK) (N0 : ℕ) {r : ℝ}
    (hr : 0 < r) (hhigh : ∀ p ∈ P.verts, 1 ≤ r * (p.2 : ℝ))
    (hfar : Fr.xstar N0 + |(P.qRat : ℝ)| ≤ -1) :
    SourceRep Fr N0 (P.physPts (Fr.xstar N0) r) P.tailDir (CP Fr (P.qRat : ℝ))
      (|Fr.xstar N0| + r * (P.vRat : ℝ)) := by
  have hok := RatPolygon.polyOK hP (Fr.xstar N0) hr
  have hone := RatPolygon.physPts_high (Fr.xstar N0) r hhigh
  have hlow : ∀ z ∈ P.physPts (Fr.xstar N0) r, 1 / 8 ≤ z.im := fun z hz => by
    linarith [hone z hz]
  have hq := RatPolygon.qFirst_phys hP (Fr.xstar N0) hr
  have hd := RatPolygon.tailDir_im_pos hP
  refine ⟨fun a b => polygon_entry hC N0 a b hok,
    fun k s t hs ht => polygon_andreief_rect hC N0 k hok s t hs ht,
    fun p => by simp [polyW], ?_, ?_,
    fun u => conjL_conj_path N0 _ _ u, fun u => conjL_conj_der N0 _ _ u, ?_, ?_, ?_,
    card_atomIdx_le Fr N0⟩
  · intro u hu
    have := norm_wUpP_le hC N0 hlow hd hu
    rwa [hq] at this
  · intro u hu
    have := norm_wLowP_le hC N0 hlow hd hu
    rwa [hq] at this
  · intro u hu x hx
    exact path_node_dist (by simp) hone hd (by rw [hq]; simpa using hfar) hu hx
  · intro u hu
    refine path_growth (by simp) (fun z hz => ?_) (fun z hz => (hok.upper z hz).le)
      (RatPolygon.tailDir_slope hP) hu
    have hV0 : 0 ≤ r * (P.vRat : ℝ) := mul_nonneg hr.le (by exact_mod_cast P.vRat_nonneg)
    rcases List.mem_cons.1 hz with h | h
    · rw [h, Complex.norm_real, Real.norm_eq_abs]; linarith
    · obtain ⟨p, hp, rfl⟩ := RatPolygon.mem_physPts h
      exact P.norm_phys_le (Fr.xstar N0) hr.le hp
  · intro c hc
    refine pathMass hc hd _ _ ?_
    have hm := List.getLast_mem (List.cons_ne_nil ((Fr.xstar N0 : ℝ) : ℂ) (P.physPts (Fr.xstar N0) r))
    rcases List.mem_cons.1 hm with h | h
    · rw [h]; simp
    · exact (hok.upper _ h).le

end CatalanCore.Uniform.Decay.Polygon
