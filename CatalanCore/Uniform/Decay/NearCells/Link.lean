import CatalanCore.Uniform.Decay.NearCells.Cell
import CatalanCore.Uniform.Decay.Cells.Far
set_option Elab.async false

/-!
# From `SplineData` to the cell rule (lane D, package D6b)

`cellPieces D nu` lists the weighted segments of `g = Mq U₀ - Vnu + (1-ε) π |Im|`, where the second
potential is `Vnu z = ∑_{j ∈ nu} ∫ f_j (-log‖z - p_j(t)‖)` (the node measure as piecewise
polynomial segments).  `nearCell_sound` is the soundness of `cellOk` as a lower bound for `gNu`.
-/

namespace CatalanCore.Uniform.Decay.NearCells

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.Spline
  CatalanCore.Uniform.Decay.Cert CatalanCore.Uniform.Decay.Cells

def segWP (w : ℚ) (sg : Seg) : WP :=
  ⟨w, sg.coef, ⟨sg.ax, sg.ay⟩, ⟨sg.bx, sg.byy⟩, sg.M, sg.Lq⟩

def cellPieces (D : SplineData) (nu : List Seg) : List WP :=
  D.segs.map (segWP D.Mq) ++ nu.map (segWP (-1))

/-- Potential of a second measure given by segments. -/
noncomputable def nuPot (nu : List Seg) (z : ℂ) : ℝ :=
  (nu.map fun sg => ∫ t in (0 : ℝ)..1, ratPoly sg.coef t *
    (-Real.log ‖z - ((⟨(sg.ax : ℝ), (sg.ay : ℝ)⟩ : ℂ) + (t : ℂ) *
      ((⟨(sg.bx : ℝ), (sg.byy : ℝ)⟩ : ℂ) - ⟨(sg.ax : ℝ), (sg.ay : ℝ)⟩))‖)).sum

theorem PhiW_segWP (w : ℚ) (sg : Seg) (z : ℂ) :
    PhiW (segWP w sg) z = ∫ t in (0 : ℝ)..1, ratPoly sg.coef t *
      Real.log ‖z - ((⟨(sg.ax : ℝ), (sg.ay : ℝ)⟩ : ℂ) + (t : ℂ) *
        ((⟨(sg.bx : ℝ), (sg.byy : ℝ)⟩ : ℂ) - ⟨(sg.ax : ℝ), (sg.ay : ℝ)⟩))‖ := rfl

theorem PhiW_w (w w' : ℚ) (sg : Seg) (z : ℂ) : PhiW (segWP w sg) z = PhiW (segWP w' sg) z := rfl

theorem sum_fin_segs {α : Type*} [AddCommMonoid α] (l : List Seg) (F : Seg → α) :
    ∑ i : Fin l.length, F (l[i.1]'i.2) = (l.map F).sum := by
  rw [Fin.sum_univ_def]
  have : (List.finRange l.length).map (fun i : Fin l.length => F (l[i.1]'i.2))
      = (List.finRange l.length).map (fun i => F (l.get i)) := rfl
  rw [this]
  have h2 : (List.map (fun i => F (l.get i)) (List.finRange l.length))
      = List.map F (List.map l.get (List.finRange l.length)) := by rw [List.map_map]; rfl
  rw [h2, List.map_get_finRange]

theorem gNu_eq (D : SplineData) (nu : List Seg) {Vnu : ℂ → ℝ} (hV : ∀ z, Vnu z = nuPot nu z) (z : ℂ) :
    gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f z =
      -((cellPieces D nu).map (fun P => (P.w : ℝ) * PhiW P z)).sum
        + (1 - (D.ε : ℝ)) * Real.pi * |z.im| := by
  unfold gNu
  rw [hV z]
  have hU : U0 D.A D.B D.f z = -(D.segs.map (fun sg => PhiW (segWP 1 sg) z)).sum := by
    unfold U0
    have : ∀ i : Fin D.n, ∫ t in (0 : ℝ)..1, D.f i t * (-Real.log ‖z - pt D.A D.B i t‖)
        = -PhiW (segWP 1 (D.segs[i.1]'i.2)) z := by
      intro i
      rw [PhiW_segWP, ← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [SplineData.f, SplineData.l, SplineData.seg, pt, SplineData.A, SplineData.B]
      ring
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_neg_distrib]
    congr 1
    exact sum_fin_segs D.segs (fun sg => PhiW (segWP 1 sg) z)
  have hN : nuPot nu z = (nu.map (fun sg => -PhiW (segWP (-1) sg) z)).sum := by
    unfold nuPot
    congr 1
    refine List.map_congr_left fun sg _ => ?_
    rw [PhiW_segWP, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [hU, hN]
  unfold cellPieces
  rw [List.map_append, List.sum_append]
  simp only [List.map_map, Function.comp_def]
  have e1 : (D.segs.map (fun sg => ((segWP D.Mq sg).w : ℝ) * PhiW (segWP D.Mq sg) z)).sum
      = (D.Mq : ℝ) * (D.segs.map (fun sg => PhiW (segWP 1 sg) z)).sum := by
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun sg _ => ?_)
    rw [PhiW_w D.Mq 1]; rfl
  have e2 : (nu.map (fun sg => ((segWP (-1) sg).w : ℝ) * PhiW (segWP (-1) sg) z)).sum
      = (nu.map (fun sg => -PhiW (segWP (-1) sg) z)).sum := by
    refine congrArg List.sum (List.map_congr_left fun sg _ => ?_)
    simp [segWP]
  rw [e1, e2]
  ring

/-- **Soundness of the generic cell rule as a lower bound for `gNu`.** -/
theorem nearCell_sound (D : SplineData) (nu : List Seg) {Vnu : ℂ → ℝ}
    (hV : ∀ z, Vnu z = nuPot nu z) (hε : D.ε < 1) {n : ℕ} {zc dd : CQ}
    {h Rtwo lo : ℚ} {Cs : List ℚ} {Fs : ℚ} {eW eP : ℕ}
    (hc : cellOk n (cellPieces D nu) zc dd h D.W Rtwo ((1 - D.ε) * piLo) lo D.mprime Cs Fs eW eP = true)
    (s δ : ℝ) (hs : |s| ≤ h) (hδ : |δ| ≤ D.W) :
    (D.mprime : ℝ) ≤ gNu D.Mq Vnu (D.ε : ℝ) D.A D.B D.f
      (zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)) := by
  rw [gNu_eq D nu hV]
  have key := cellOk_sound hc s δ hs hδ
  have hε1 : (D.ε : ℝ) < 1 := by exact_mod_cast hε
  have hcp : ((((1 - D.ε) * piLo : ℚ)) : ℝ) * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im|
      ≤ (1 - (D.ε : ℝ)) * Real.pi * |(zc.toC + (s : ℂ) * dd.toC + (δ : ℂ)).im| := by
    push_cast
    have := piLo_lt
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply mul_le_mul_of_nonneg_left this.le (by linarith)
  linarith

end CatalanCore.Uniform.Decay.NearCells
