module

public import CatalanCore.Uniform.Decay.Polygon.Source

@[expose] public section

/-!
# The polygon source space and the Andréief bound (Part 2, Proposition `gram`)

The source parameter space is the old combined space `Fr.XT N0 = atoms ⊕ (ray ⊕ ray)` with the
old measure `Fr.muT N0` (counting measure on the head labels, Lebesgue measure on `(0,∞)`), but
the two `(0,∞)` copies now parametrise the upper polygon `x* → pts → tail d` and its conjugate
(`Path.lean`: edge `j` on `(j, j+1]`, tail after; edge multiplicities kept).

* position `polyPt`: atoms `-(m + μ_i)`, upper `γ(u)`, lower `γ̄(u)`;
* weight `polyW`: atoms `w_i`, upper `-(2πi)⁻¹ E(γ) γ'`, lower `(2πi)⁻¹ E(γ̄) γ̄'`.

`polygon_entry` : `∫ polyW (z-a)⁻¹ (z-b)⁻¹ = norm · T_ab` for all natural `a, b` (incl. `a = b`);
`polygon_andreief_rect` : for injective row/column lists `s, t` of size `k`,
`|det (norm · T[s,t])| ≤ (1/k!) ∫ ∏|polyW| · |C(z,s)| · |C(z,t)|`.

Both are uniform over all node lists, hence over all deletions.
-/

open MeasureTheory Set Filter Topology Complex
open CatalanLambda.Decay (rayPt rayI contL sumM integrable_sumM_iff integral_sumM
  norm_det_le_andreief)

namespace CatalanCore.Uniform.Decay.Polygon

/-! ### Generic: parameter integrals of a deformable integrand -/

section generic

variable {f : ℂ → ℂ} {σ δ : ℝ} {v : ℂ}

theorem chainSet_sub_convex {s : Set ℂ} (hs : Convex ℝ s) :
    ∀ (l : List ℂ) (a : ℂ), a ∈ s → (∀ z ∈ l, z ∈ s) → chainSet a l ⊆ s
  | [], _, _, _ => by simp [chainSet]
  | b :: l, a, ha, hl => by
    have hb : b ∈ s := hl b (by simp)
    intro z hz
    rcases hz with h | h
    · exact hs.segment_subset ha hb h
    · exact chainSet_sub_convex hs l b hb (fun z hz => hl z (by simp [hz])) h

/-- The finite edges of a polygon based at the real point `v` lie in the disk or half-plane. -/
theorem chainSet_sub_start (hv : v.im = 0) (hδ : 0 < δ) :
    ∀ (pts : List ℂ), (∀ z ∈ pts, 0 < σ * z.im) →
      ∀ z ∈ chainSet v pts, z ∈ Metric.ball v δ ∨ z ∈ halfP σ
  | [], _ => by simp [chainSet]
  | b :: l, hpts => by
    intro z hz
    have hb : 0 < σ * b.im := hpts b (by simp)
    rcases hz with h | h
    · exact segment_sub hv hδ hb z h
    · right
      exact chainSet_sub_convex (convex_halfP σ) l b hb (fun w hw => hpts w (by simp [hw])) h

/-- Every parameter point of the polygon lies in the disk or the half-plane. -/
theorem pathPt_mem_start (hv : v.im = 0) (hδ : 0 < δ) (pts : List ℂ)
    (hpts : ∀ z ∈ pts, 0 < σ * z.im) {d : ℂ} (hd : 0 < σ * d.im) {u : ℝ} (hu : 0 ≤ u) :
    pathPt d v pts u ∈ Metric.ball v δ ∨ pathPt d v pts u ∈ halfP σ := by
  rcases pathPt_mem d pts v hu with h | ⟨t, ht, he⟩
  · exact chainSet_sub_start hv hδ pts hpts _ h
  · rw [he]
    exact ray_mem hδ (mem_or_half pts hpts _ (List.getLast_mem _)) hd hv ht

/-- Under the hypotheses of `deform`, the parameter integrand is integrable and integrates to
the polygon integral. -/
theorem pathInt_of_deform (hv : v.im = 0) (hδ : 0 < δ) (hfH : DifferentiableOn ℂ f (halfP σ))
    (hfB : DifferentiableOn ℂ f (Metric.ball v δ)) (pts : List ℂ)
    (hpts : ∀ z ∈ pts, 0 < σ * z.im) {d : ℂ} (hd : 0 < σ * d.im)
    {K : ℝ} (hK : 0 ≤ K) (hdec : ∀ z : ℂ, 1 ≤ σ * z.im → ‖f z‖ ≤ K / (σ * z.im) ^ 2) :
    IntegrableOn (fun u => f (pathPt d v pts u) * pathDer d v pts u) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), f (pathPt d v pts u) * pathDer d v pts u = polyI f v pts d := by
  have hdiff : ∀ z, (z ∈ Metric.ball v δ ∨ z ∈ halfP σ) → DifferentiableAt ℂ f z :=
    fun z hz => diffAt_of_mem hδ hfH hfB hz
  set L := (v :: pts).getLast (List.cons_ne_nil v pts)
  have hLm : L = v ∨ 0 < σ * L.im := mem_or_half pts hpts L (List.getLast_mem _)
  have hL0 : 0 ≤ σ * L.im := by
    rcases hLm with h | h
    · rw [h, hv, mul_zero]
    · exact h.le
  refine pathInt_eq f d pts v (fun z hz => (hdiff z (chainSet_sub_start hv hδ pts hpts z hz)).continuousAt) ?_
  exact integrableOn_ray hL0 hd hK hdec
    (fun u hu => (hdiff _ (ray_mem hδ hLm hd hv hu)).continuousAt)

end generic

/-! ### The polygon space of a frame -/

variable {Fr : Frame}

/-- The conjugate list of vertices (the lower polygon). -/
noncomputable def conjL (pts : List ℂ) : List ℂ := pts.map (starRingEnd ℂ)

/-- Positions on the polygon space. -/
noncomputable def polyPt (Fr : Frame) (N0 : ℕ) (pts : List ℂ) (d : ℂ) : Fr.XT N0 → ℂ :=
  Sum.elim (fun p => ((Fr.atomPos p.1 : ℝ) : ℂ))
    (Sum.elim (fun r => pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r.1)
      (fun r => pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r.1))

/-- Upper polygon weight `-(2πi)⁻¹ E(γ) γ'`. -/
noncomputable def wUpP (Fr : Frame) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (r : ℝ) : ℂ :=
  -((2 * Real.pi * I)⁻¹ * (Fr.EC (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r)
    * pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts r))

/-- Lower polygon weight `(2πi)⁻¹ E(γ̄) γ̄'`. -/
noncomputable def wLowP (Fr : Frame) (N0 : ℕ) (pts : List ℂ) (d : ℂ) (r : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * (Fr.EC (pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r)
    * pathDer (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r)

/-- Complex weights on the polygon space. -/
noncomputable def polyW (Fr : Frame) (N0 : ℕ) (pts : List ℂ) (d : ℂ) : Fr.XT N0 → ℂ :=
  Sum.elim (fun p => ((Fr.w p.1.2 : ℤ) : ℂ))
    (Sum.elim (fun r => wUpP Fr N0 pts d r.1) (fun r => wLowP Fr N0 pts d r.1))

/-- An admissible physical upper polygon based at `x*`: strictly upper vertices, upper tail. -/
structure PolyOK (pts : List ℂ) (d : ℂ) : Prop where
  upper : ∀ z ∈ pts, 0 < z.im
  tail : 0 < d.im

theorem PolyOK.lower {pts : List ℂ} {d : ℂ} (h : PolyOK pts d) :
    ∀ z ∈ conjL pts, 0 < (-1 : ℝ) * z.im := by
  intro z hz
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hz
  simpa using h.upper w hw

theorem PolyOK.upper' {pts : List ℂ} {d : ℂ} (h : PolyOK pts d) :
    ∀ z ∈ pts, 0 < (1 : ℝ) * z.im := fun z hz => by simpa using h.upper z hz

theorem upper_path (hC : Fr.ContourOK) (N0 a b : ℕ) {pts : List ℂ} {d : ℂ} (h : PolyOK pts d) :
    IntegrableOn (fun u => srcF Fr a b (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u)
        * pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), srcF Fr a b (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts u)
        * pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts u
        = polyI (srcF Fr a b) ((Fr.xstar N0 : ℝ) : ℂ) pts d :=
  pathInt_of_deform (σ := 1) (by simp) (diskR_pos hC) (srcF_differentiableOn_halfP 1 a b)
    (srcF_differentiableOn_ball hC N0 a b) pts h.upper' (by simpa using h.tail) Khi_nonneg
    (srcF_decay (by simp) a b)

theorem lower_path (hC : Fr.ContourOK) (N0 a b : ℕ) {pts : List ℂ} {d : ℂ} (h : PolyOK pts d) :
    IntegrableOn (fun u => srcF Fr a b (pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u)
        * pathDer (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u) (Ioi 0) ∧
      ∫ u in Ioi (0 : ℝ), srcF Fr a b (pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u)
        * pathDer (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) u
        = polyI (srcF Fr a b) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) (starRingEnd ℂ d) :=
  pathInt_of_deform (σ := -1) (by simp) (diskR_pos hC) (srcF_differentiableOn_halfP (-1) a b)
    (srcF_differentiableOn_ball hC N0 a b) (conjL pts) h.lower (by simpa using h.tail) Khi_nonneg
    (srcF_decay (by simp) a b)

theorem polygon_integrable_entry (hC : Fr.ContourOK) (N0 a b : ℕ) {pts : List ℂ} {d : ℂ}
    (h : PolyOK pts d) :
    Integrable (fun z => polyW Fr N0 pts d z * (polyPt Fr N0 pts d z - a)⁻¹
      * (polyPt Fr N0 pts d z - b)⁻¹) (Fr.muT N0) := by
  unfold Frame.muT
  rw [integrable_sumM_iff, integrable_sumM_iff]
  refine ⟨Integrable.of_finite, ?_, ?_⟩
  · have hi := ((upper_path hC N0 a b h).1).const_mul (-(2 * Real.pi * I)⁻¹)
    refine (Decay.integrable_comap_Ioi (fun r => wUpP Fr N0 pts d r
      * (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r - a)⁻¹
      * (pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts r - b)⁻¹)).2
      (IntegrableOn.congr_fun hi (fun r _ => ?_) measurableSet_Ioi)
    simp only [wUpP, srcF]; ring
  · have hi := ((lower_path hC N0 a b h).1).const_mul ((2 * Real.pi * I)⁻¹)
    refine (Decay.integrable_comap_Ioi (fun r => wLowP Fr N0 pts d r
      * (pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r - a)⁻¹
      * (pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts) r - b)⁻¹)).2
      (IntegrableOn.congr_fun hi (fun r _ => ?_) measurableSet_Ioi)
    simp only [wLowP, srcF]; ring

theorem polygon_atom_sum (N0 a b : ℕ) (pts : List ℂ) (d : ℂ) :
    ∑ p : ↥(Fr.atomIdx N0), (polyW Fr N0 pts d (Sum.inl p) * (polyPt Fr N0 pts d (Sum.inl p) - a)⁻¹
        * (polyPt Fr N0 pts d (Sum.inl p) - b)⁻¹)
      = ((Fr.atomHead N0 a b : ℝ) : ℂ) := by
  have key : ∀ p : ↥(Fr.atomIdx N0), (polyW Fr N0 pts d (Sum.inl p)
        * (polyPt Fr N0 pts d (Sum.inl p) - a)⁻¹ * (polyPt Fr N0 pts d (Sum.inl p) - b)⁻¹)
      = ((Fr.atomR p.1.2 a b (p.1.1 : ℝ) : ℝ) : ℂ) := by
    intro p
    simp only [polyW, polyPt, Sum.elim_inl, Frame.atomPos]
    rw [mul_assoc, Frame.atom_pt_prod a b]
    unfold Frame.atomR
    push_cast
    ring
  simp_rw [key]
  rw [Finset.sum_coe_sort (Fr.atomIdx N0) (fun p => ((Fr.atomR p.2 a b (p.1 : ℝ) : ℝ) : ℂ)),
    Frame.atomHead_eq]
  push_cast
  rfl

/-- **Exact polygon Gram representation, entries** (Part 2, Proposition `gram`). -/
theorem polygon_entry (hC : Fr.ContourOK) (N0 a b : ℕ) {pts : List ℂ} {d : ℂ}
    (h : PolyOK pts d) :
    ∫ z, polyW Fr N0 pts d z * (polyPt Fr N0 pts d z - a)⁻¹ * (polyPt Fr N0 pts d z - b)⁻¹
        ∂(Fr.muT N0)
      = (((Fr.norm : ℝ) * Fr.Tent a b : ℝ) : ℂ) := by
  have hint := polygon_integrable_entry hC N0 a b h
  unfold Frame.muT at hint ⊢
  rw [integral_sumM _ _ _ hint]
  have hint2 := ((integrable_sumM_iff _ _ _).1 hint).2
  rw [integral_sumM _ _ _ hint2]
  rw [integral_count, polygon_atom_sum]
  set γ := pathPt d ((Fr.xstar N0 : ℝ) : ℂ) pts
  set γ' := pathDer d ((Fr.xstar N0 : ℝ) : ℂ) pts
  set η := pathPt (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts)
  set η' := pathDer (starRingEnd ℂ d) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts)
  have hU : ∫ x : Decay.RayP, (polyW Fr N0 pts d (Sum.inr (Sum.inl x))
        * (polyPt Fr N0 pts d (Sum.inr (Sum.inl x)) - a)⁻¹
        * (polyPt Fr N0 pts d (Sum.inr (Sum.inl x)) - b)⁻¹)
        ∂(Measure.comap Subtype.val (volume : Measure ℝ))
      = ∫ r in Ioi (0 : ℝ), wUpP Fr N0 pts d r * (γ r - a)⁻¹ * (γ r - b)⁻¹ :=
    integral_subtype_comap measurableSet_Ioi (fun r => wUpP Fr N0 pts d r * (γ r - a)⁻¹
      * (γ r - b)⁻¹)
  have hL : ∫ x : Decay.RayP, (polyW Fr N0 pts d (Sum.inr (Sum.inr x))
        * (polyPt Fr N0 pts d (Sum.inr (Sum.inr x)) - a)⁻¹
        * (polyPt Fr N0 pts d (Sum.inr (Sum.inr x)) - b)⁻¹)
        ∂(Measure.comap Subtype.val (volume : Measure ℝ))
      = ∫ r in Ioi (0 : ℝ), wLowP Fr N0 pts d r * (η r - a)⁻¹ * (η r - b)⁻¹ :=
    integral_subtype_comap measurableSet_Ioi (fun r => wLowP Fr N0 pts d r * (η r - a)⁻¹
      * (η r - b)⁻¹)
  have eU : ∫ r in Ioi (0 : ℝ), wUpP Fr N0 pts d r * (γ r - a)⁻¹ * (γ r - b)⁻¹
      = -(2 * Real.pi * I)⁻¹ * polyI (srcF Fr a b) ((Fr.xstar N0 : ℝ) : ℂ) pts d := by
    rw [← (upper_path hC N0 a b h).2, ← integral_const_mul]
    congr 1; funext r; simp only [wUpP, srcF, γ, γ']; ring
  have eL : ∫ r in Ioi (0 : ℝ), wLowP Fr N0 pts d r * (η r - a)⁻¹ * (η r - b)⁻¹
      = (2 * Real.pi * I)⁻¹ * polyI (srcF Fr a b) ((Fr.xstar N0 : ℝ) : ℂ) (conjL pts)
          (starRingEnd ℂ d) := by
    rw [← (lower_path hC N0 a b h).2, ← integral_const_mul]
    congr 1; funext r; simp only [wLowP, srcF, η, η']; ring
  rw [hU, hL, eU, eL, polygon_contour_identity hC N0 a b pts h.upper h.tail]
  unfold conjL
  ring

/-- No point of the polygon space is a natural-number node. -/
theorem polyPt_ne (hC : Fr.ContourOK) (N0 : ℕ) {pts : List ℂ} {d : ℂ} (h : PolyOK pts d)
    (z : Fr.XT N0) (n : ℕ) : polyPt Fr N0 pts d z ≠ (n : ℂ) := by
  have hv : (((Fr.xstar N0 : ℝ) : ℂ)).im = 0 := by simp
  rcases z with p | r | r
  · simp only [polyPt, Sum.elim_inl, Frame.atomPos]
    intro hp
    have h' : (-(((p.1.1 : ℕ) : ℝ) + (Fr.μ p.1.2 : ℝ))) = (n : ℝ) := by exact_mod_cast hp
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ ((p.1.1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have := Frame.mu_pos (Fr := Fr) p.1.2
    linarith
  · simp only [polyPt, Sum.elim_inr, Sum.elim_inl]
    intro he
    rcases pathPt_mem_start (σ := 1) hv (diskR_pos hC) pts h.upper' (by simpa using h.tail)
      (le_of_lt r.2) with hb | hh
    · exact node_ne_of_ball hC N0 n hb (sub_eq_zero.2 he)
    · exact sub_nat_ne_of_im (im_ne_of_halfP hh) n (sub_eq_zero.2 he)
  · simp only [polyPt, Sum.elim_inr]
    intro he
    rcases pathPt_mem_start (σ := -1) hv (diskR_pos hC) (conjL pts) h.lower (d := starRingEnd ℂ d) (by simpa using h.tail)
      (le_of_lt r.2) with hb | hh
    · exact node_ne_of_ball hC N0 n hb (sub_eq_zero.2 he)
    · exact sub_nat_ne_of_im (im_ne_of_halfP hh) n (sub_eq_zero.2 he)

/-- **Rectangular Andréief bound on the polygon space** (Part 2, Proposition `gram`), for every
injective row list `s` and column list `t` of equal size, i.e. uniformly over all deletions. -/
theorem polygon_andreief_rect (hC : Fr.ContourOK) (N0 k : ℕ) {pts : List ℂ} {d : ℂ}
    (h : PolyOK pts d) (s t : Fin k → ℕ) (hs : Function.Injective s) (ht : Function.Injective t) :
    ‖(Matrix.of fun i j : Fin k => (((Fr.norm : ℝ) * Fr.Tent (s i) (t j) : ℝ) : ℂ)).det‖
      ≤ (1 / (k.factorial : ℝ)) * ∫ z : Fin k → Fr.XT N0,
          (∏ l, ‖polyW Fr N0 pts d (z l)‖) *
            (‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((polyPt Fr N0 pts d (z l') - polyPt Fr N0 pts d (z l)) * ((s l : ℂ) - s l')))
              / ∏ l, ∏ i, (polyPt Fr N0 pts d (z l) - s i)‖ *
            ‖(∏ l, ∏ l' ∈ Finset.Ioi l,
                ((polyPt Fr N0 pts d (z l') - polyPt Fr N0 pts d (z l)) * ((t l : ℂ) - t l')))
              / ∏ l, ∏ i, (polyPt Fr N0 pts d (z l) - t i)‖) ∂(Measure.pi fun _ => Fr.muT N0) := by
  have hb := norm_det_le_andreief (Fr.muT N0) (polyW Fr N0 pts d)
    (fun (i : Fin k) z => (polyPt Fr N0 pts d z - (s i : ℂ))⁻¹)
    (fun (i : Fin k) z => (polyPt Fr N0 pts d z - (t i : ℂ))⁻¹)
    (fun i j => polygon_integrable_entry hC N0 (s i) (t j) h)
  have hM : (Matrix.of fun i j : Fin k => ∫ z, polyW Fr N0 pts d z
        * (polyPt Fr N0 pts d z - (s i : ℂ))⁻¹ * (polyPt Fr N0 pts d z - (t j : ℂ))⁻¹ ∂(Fr.muT N0))
      = Matrix.of fun i j : Fin k => (((Fr.norm : ℝ) * Fr.Tent (s i) (t j) : ℝ) : ℂ) := by
    ext i j; exact polygon_entry hC N0 (s i) (t j) h
  rw [hM] at hb
  refine hb.trans (le_of_eq ?_)
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [Frame.det_inv_eq_cauchy s hs (fun l => polyPt Fr N0 pts d (z l))
      (fun l i => polyPt_ne hC N0 h (z l) (s i)),
    Frame.det_inv_eq_cauchy t ht (fun l => polyPt Fr N0 pts d (z l))
      (fun l i => polyPt_ne hC N0 h (z l) (t i))]
  ring

end CatalanCore.Uniform.Decay.Polygon
