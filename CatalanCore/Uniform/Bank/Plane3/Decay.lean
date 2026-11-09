module

public import CatalanCore.Uniform.Bank.Plane3.Frame
public import CatalanCore.Uniform.Decay.Jet.Source

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # The third-plane full-window decay instance (Q10)
The existing fixed reference geometry supplies the lattice estimates. The
actual arbitrary-rational order3 datum is handled by the frozen unconditional
pole source; every admissible member and window point is retained.
-/
namespace CatalanCore.Uniform.Bank.Plane3
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support
open CatalanCore.Uniform.Bank.Plane2 CatalanCore.Uniform.Content.Shape
open CatalanCore.Uniform.Decay.Jet CatalanCore.Uniform.Decay.Polygon
open CatalanCore.Uniform.Decay.PolyChain CatalanCore.Uniform.Decay.Assembly
open CatalanCore.Uniform.Decay.AltDecay CatalanCore.Uniform.Decay.Cert
open CatalanCore.Uniform.Decay.Nodes
open CatalanCore.Uniform.Decay.PolyFull
open Finset Set Complex

/-! Fixed reference geometry only. Reuse the inherited order2 setup theorem for
its reference-space geometry; the actual order3 source uses the frozen engine. -/
private noncomputable def geometricMatch := p2Ref 1 1 (by norm_num) (by norm_num)

private theorem referenceSetup {P : RatPolygon} (hP : P.OK)
    (hneg : ∀ p ∈ P.verts, p.1 + P.r0 ≤ 0) {r : ℕ}
    (hr : Rmin p2ref P ≤ (r : ℝ)) :
    geometricMatch.JetSetup (N0Of p2ref P.r0 r) (physL p2ref P r) P.tailDir
      (1 / 8) (3 / 8) (1 / 2) (1 / 4) (1 / 4) := by
  have hs : geometricMatch.JetSetup (N0Of p2ref P.r0 r) (physL p2ref P r) P.tailDir
      (1 / 8) (3 / 8) (1 / 2) (1 / 4) (p2ref.δ0 : ℝ) := by
    refine geometricMatch.jetSetup_of_polygon (ρ := 1 / 8) (a := 3 / 8) (a0 := 1 / 2) (g := 1 / 4)
      hP (Frame.contourOK_of_check p2ref_contour) hneg hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      p2ref_w_ne p2ref_sep ?_ ?_ (by norm_num) p2ref_mu_ge (by norm_num)
    · intro j
      obtain ⟨j, hj⟩ := j
      fin_cases j
      · norm_num [geometricMatch, p2Ref, p2Role, p2ref, Datum.plane2]
      · simp [Datum.plane2] at hj
    · intro i; fin_cases i <;> norm_num [Datum.plane2]
  have hdelta : (p2ref.δ0 : ℝ) = 1 / 4 := by norm_num [p2ref]
  simpa only [hdelta] using hs

noncomputable def coefficientBound (v u : ℚ) (hu : u ≠ 0) : ℝ :=
  1 + ∑ q : Fin p2ref.d, ∑ j : Fin ((split v u hu).J + 1),
    ‖((split v u hu).coeff ((refMatch v u hu).role q) j : ℂ)‖

theorem coefficientBound_nonneg (v u : ℚ) (hu : u ≠ 0) :
    0 ≤ coefficientBound v u hu := by
  unfold coefficientBound
  positivity

private theorem coefficient_le_bound (v u : ℚ) (hu : u ≠ 0)
    (q : Fin p2ref.d) (j : Fin ((split v u hu).J + 1)) :
    ‖((split v u hu).coeff ((refMatch v u hu).role q) j : ℂ)‖ ≤ coefficientBound v u hu := by
  have h1 := Finset.single_le_sum
    (f := fun j : Fin ((split v u hu).J + 1) =>
      ‖((split v u hu).coeff ((refMatch v u hu).role q) j : ℂ)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  have h2 := Finset.single_le_sum
    (f := fun q : Fin p2ref.d => ∑ j : Fin ((split v u hu).J + 1),
      ‖((split v u hu).coeff ((refMatch v u hu).role q) j : ℂ)‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ q)
  unfold coefficientBound
  linarith

private theorem reference_head_injective (N0 : ℕ) (pts : List ℂ) (dir : ℂ) :
    Function.Injective (fun p : ↥(p2ref.atomIdx N0) =>
      polyPt p2ref N0 pts dir (Sum.inl p)) := by
  intro p p' h
  by_contra hne
  have hs := p2ref_sep p.1.1 p'.1.1 p.1.2 p'.1.2 (fun e => hne (Subtype.ext e))
  have h' : polyPt p2ref N0 pts dir (Sum.inl p) = polyPt p2ref N0 pts dir (Sum.inl p') := h
  rw [RefMatch.pos0_atom, RefMatch.pos0_atom] at h'
  have he := congrArg Complex.re h'
  simp only [Complex.ofReal_re] at he
  have hz : ((p.1.1 : ℝ) + (p2ref.μ p.1.2 : ℝ)) -
      ((p'.1.1 : ℝ) + (p2ref.μ p'.1.2 : ℝ)) = 0 := by linarith
  rw [hz, abs_zero] at hs
  norm_num at hs

theorem datum_contour (v u : ℚ) (hu : u ≠ 0) :
    ((datum v u hu).clearanceFrame p2ref.xs p2ref.δ0 p2ref.n0off).ContourOK := by
  change ((datum 0 1 (by norm_num)).clearanceFrame p2ref.xs p2ref.δ0 p2ref.n0off).ContourOK
  exact Frame.contourOK_of_check (by decide +kernel)

theorem physical_setup (v u : ℚ) (hu : u ≠ 0)
    {P : RatPolygon} (hP : P.OK) (hneg : ∀ p ∈ P.verts, p.1 + P.r0 ≤ 0)
    (r : ℕ) (hr : Rmin p2ref P ≤ (r : ℝ)) :
    PoleJetSetup (datum v u hu) (split v u hu) p2ref (refMatch v u hu)
      (N0Of p2ref P.r0 r) (physL p2ref P r) P.tailDir
      (coefficientBound v u hu) (1 / 2) (1 / 4) (1 / 4) (1 / 2) := by
  let N0 := N0Of p2ref P.r0 r
  let pts := physL p2ref P r
  let dir := P.tailDir
  have st := referenceSetup hP hneg hr
  have him_up (z : Decay.RayP) :
      (polyPt p2ref N0 pts dir (Sum.inr (Sum.inl z))).im ≠ 0 := st.rayim_up z
  have him_low (z : Decay.RayP) :
      (polyPt p2ref N0 pts dir (Sum.inr (Sum.inr z))).im ≠ 0 := st.rayim_low z
  refine ⟨p2ref_w_ne, ?_⟩
  constructor
  · intro z hz
    rcases z with p | z
    · simp only [poleCenter, Sum.elim_inl, datum, Complex.sub_im, Complex.neg_im,
        Complex.ofReal_im, Complex.natCast_im, sub_zero, neg_zero]
      constructor
      · simp
      · have hm : (0 : ℝ) ≤ p.1.1 := Nat.cast_nonneg _
        norm_num
        linarith
    · simp [poleHead] at hz
  · intro z hz
    rcases z with p | z
    · rw [RefMatch.pos0_atom]; simp
    · simp [poleHead] at hz
  · intro z hz
    rcases z with p | z
    · have he : poleCenter (refMatch v u hu) N0 pts dir (Sum.inl p) -
          polyPt p2ref N0 pts dir (Sum.inl p) =
          (((p2ref.μ p.1.2 : ℝ) - 1 : ℝ) : ℂ) := by
        rw [RefMatch.pos0_atom]
        simp only [poleCenter, Sum.elim_inl, datum]
        push_cast
        ring
      rw [he, Complex.norm_real, Real.norm_eq_abs]
      rcases p2ref_mu_real p.1.2 with h | h | h <;> rw [h] <;> norm_num
    · simp [poleHead] at hz
  · intro z hz j
    rcases z with p | z
    · exact coefficient_le_bound v u hu p.1.2 j
    · simp [poleHead] at hz
  · intro z hz
    cases z with
    | inl p => simp [poleHead] at hz
    | inr z => rfl
  · intro z z' hz hz' hne
    rcases z with p | z <;> rcases z' with p' | z'
    · have hs := p2ref_sep p.1.1 p'.1.1 p.1.2 p'.1.2
        (fun he => hne (by rw [Subtype.ext he]))
      rw [RefMatch.pos0_atom, RefMatch.pos0_atom, RefMatch.norm_ofReal_sub]
      simpa only [neg_sub_neg, abs_sub_comm] using hs
    all_goals simp_all [poleHead]
  · intro z z' hz hz'
    have h1 : (polyPt p2ref N0 pts dir z).im = 0 := by
      rcases z with p | z
      · rw [RefMatch.pos0_atom]; simp
      · simp [poleHead] at hz
    have h2 : (polyPt p2ref N0 pts dir z').im ≠ 0 := by
      rcases z' with p | z' | z'
      · simp [poleHead] at hz'
      · exact him_up z'
      · exact him_low z'
    have hgap := st.rayR z z' h1 h2
    simpa only [norm_sub_rev] using hgap
  · intro z t ht
    rcases z with p | z | z
    · have he := congrArg Complex.re ht
      rw [RefMatch.pos0_atom] at he
      simp only [Complex.ofReal_re, Complex.natCast_re] at he
      have hm := p2ref_mu_ge p.1.2
      have h0 : (0 : ℝ) ≤ p.1.1 := Nat.cast_nonneg _
      have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
      linarith
    · apply him_up z
      rw [ht]; simp
    · apply him_low z
      rw [ht]; simp
  · intro z z' he t
    rcases z with p | z | z <;> rcases z' with p' | z' | z'
    · have hp := reference_head_injective N0 pts dir he
      subst hp
      rfl
    · exact False.elim (him_up z' (by rw [← he, RefMatch.pos0_atom]; simp))
    · exact False.elim (him_low z' (by rw [← he, RefMatch.pos0_atom]; simp))
    · exact False.elim (him_up z (by rw [he, RefMatch.pos0_atom]; simp))
    · simp only [jetRowFinite, poleHead, Sum.elim_inr, ↓reduceIte]
      rw [he]
    · simp only [jetRowFinite, poleHead, Sum.elim_inr, ↓reduceIte]
      rw [he]
    · exact False.elim (him_low z (by rw [he, RefMatch.pos0_atom]; simp))
    · simp only [jetRowFinite, poleHead, Sum.elim_inr, ↓reduceIte]
      rw [he]
    · simp only [jetRowFinite, poleHead, Sum.elim_inr, ↓reduceIte]
      rw [he]

theorem plane3_decay (v u : ℚ) (hu : u ≠ 0) (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1)
    (Ct : Support.Certificate (Content.Shape.altGeom c hc).nodePot)
    (hneg : ∀ p ∈ Ct.polygon.verts, p.1 + Ct.polygon.r0 ≤ 0)
    (hMq : Ct.spline.Mq = 1 + c / 2)
    (hd : Ct.spline.dim = 3)
    (hInu : (Ct.spline.Inu : ℝ) ≤
      (Content.Shape.altGeom c hc).nodeEnergy)
    (heps : 0 < Ct.spline.ε) (depth : ℕ) :
    HasScaledDecay ((Content.Shape.altGeom c hc).seqFamily
      (datum v u hu).f (datum v u hu).e (datum v u hu).xi depth)
      (SeqFamily.scale (Content.Shape.altGeom c hc).geometry)
      Ct.Dr Ct.cr := by
  obtain ⟨B, hP, _, C, hCW, hCm, hCg, hCS, hCI, hCc⟩ := SplineData.checkP_sound Ct.checkP
  have hepsR : (0 : ℝ) < (Ct.spline.ε : ℝ) := by exact_mod_cast heps
  obtain ⟨hbc, hbr, hbq⟩ := altGeom_blocks_v c hc hc1
  refine pole_support_decay (datum v u hu) (split v u hu)
    (altGeom c hc) (refMatch v u hu)
    (Frame.contourOK_of_check p2ref_contour) (datum_contour v u hu)
    p2ref_hAR Ct hneg ?_ hd hInu
    (nodePot_conj _) ((nodePot_real_continuous _).continuousOn)
    (altGeom_supp c hc)
    (Bd := 2) (by norm_num) hbc hbr hbq
    (m0 := 1 / 2) (by norm_num) p2ref_mu_ge
    (e := (Ct.spline.ε : ℝ) / 2) (by linarith) (by linarith) depth
    (coefficientBound v u hu) (1 / 2) (1 / 4) (1 / 4) (1 / 2)
    (coefficientBound_nonneg v u hu) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun r hr => physical_setup v u hu hP hneg r hr)
  rw [altGeom_totalMass]
  simpa using hMq

end CatalanCore.Uniform.Bank.Plane3
#print axioms CatalanCore.Uniform.Bank.Plane3.physical_setup
#print axioms CatalanCore.Uniform.Bank.Plane3.datum_contour
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_decay
