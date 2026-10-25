module
public import CatalanCore.Cert.QuarterContour.Box
public import CatalanCore.Decay.Rect.CertG
@[expose] public section
namespace CatalanCore.Cert.QuarterContour
open CatalanCore.Cert.SigmaP6

def pointAt (pts : List Pt) (k : ℕ) : Pt := pts.getD k (0, 0, 0)
noncomputable def positions (pts : List Pt) (k : Fin pts.length) : ℂ :=
  ⟨((pointAt pts k).1 : ℝ) / 2 ^ 40, ((pointAt pts k).2.1 : ℝ) / 2 ^ 40⟩
noncomputable def masses (pts : List Pt) (k : Fin pts.length) : ℝ :=
  ((pointAt pts k).2.2 : ℝ) / 2 ^ 32

lemma points_ofFn (pts : List Pt) : pts = List.ofFn (fun k : Fin pts.length => pointAt pts k) := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    rw [List.getElem_ofFn]
    unfold pointAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    rfl

lemma sum_points (pts : List Pt) (f : Pt → ℝ) :
    ∑ k : Fin pts.length, f (pointAt pts k) = (pts.map f).sum := by
  conv_rhs => rw [points_ofFn pts, List.map_ofFn, List.sum_ofFn]
  rfl

theorem Usig_bridge (pts : List Pt) (x y : ℝ) :
    CatalanLambda.Decay.Usig (1 / 2048 : ℝ) (positions pts) (masses pts) ⟨x, y⟩ =
      CatalanCore.Cert.SigmaP6.Usig pts x y := by
  unfold CatalanLambda.Decay.Usig
  rw [Usig_eq_sum, ← sum_points]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  unfold CatalanLambda.Decay.krho masses positions
  rw [norm_sq_mk]

theorem mass_sum (pts : List Pt) (h : (pts.map (fun p => p.2.2)).sum = 2 ^ 32) :
    ∑ k, masses pts k = 1 := by
  have hh := sum_points pts (fun p => (p.2.2 : ℝ) / 2 ^ 32)
  change (∑ k : Fin pts.length, (pointAt pts k).2.2 / (2 : ℝ) ^ 32) = 1
  have msum_list (l : List Pt) :
      (l.map (fun p => (p.2.2 : ℝ) / 2 ^ 32)).sum =
        (((l.map (fun p => p.2.2)).sum : ℕ) : ℝ) / 2 ^ 32 := by
    induction l with
    | nil => simp
    | cons p ps ih => simp only [List.map_cons, List.sum_cons, ih]; push_cast; ring
  rw [hh, msum_list, h]
  norm_num

theorem mass_nonneg (pts : List Pt) (k : Fin pts.length) : 0 ≤ masses pts k := by
  unfold masses
  positivity

lemma div_threeHalf (x y : ℝ) :
    (⟨x, y⟩ : ℂ) / (3 / 2 : ℂ) = ⟨2 * x / 3, 2 * y / 3⟩ := by
  apply Complex.ext <;> simp [Complex.div_re, Complex.div_im] <;> ring

theorem gAlpha_bridge (epsilon : ℚ) (pts : List Pt) (x y : ℝ) (hx : x < 0) (hy : 0 ≤ y) :
    CatalanCore.Cert.gAlpha (1 / 2048 : ℝ) epsilon (positions pts) (masses pts) (1 / 4)
      (CatalanCore.Decay.Unu (1 / 4)) ⟨x, y⟩ = gQuarter epsilon pts x y := by
  unfold CatalanCore.Cert.gAlpha gQuarter
  rw [SigmaQuarter.Unu_quarter, Usig_bridge, div_threeHalf,
    Utau_bridge x y hx, Utau_bridge (2 * x / 3) (2 * y / 3) (by linarith)]
  have habs : |(⟨x, y⟩ : ℂ).im| = y := abs_of_nonneg hy
  rw [habs]
  ring

theorem gAlpha_bridge_axis (epsilon : ℚ) (pts : List Pt) (x : ℝ) (hx : x ≤ 1) :
    CatalanCore.Cert.gAlpha (1 / 2048 : ℝ) epsilon (positions pts) (masses pts) (1 / 4)
      (CatalanCore.Decay.Unu (1 / 4)) ⟨x, 0⟩ = gQuarter epsilon pts x 0 := by
  unfold CatalanCore.Cert.gAlpha gQuarter
  rw [SigmaQuarter.Unu_quarter, Usig_bridge, div_threeHalf]
  simp only [mul_zero, zero_div]
  rw [Utau_bridge_axis x hx, Utau_bridge_axis (2 * x / 3) (by linarith)]
  simp only [abs_zero, mul_zero, add_zero]
  ring
end CatalanCore.Cert.QuarterContour
#print axioms CatalanCore.Cert.QuarterContour.Usig_bridge
#print axioms CatalanCore.Cert.QuarterContour.mass_sum
#print axioms CatalanCore.Cert.QuarterContour.gAlpha_bridge
#print axioms CatalanCore.Cert.QuarterContour.gAlpha_bridge_axis
