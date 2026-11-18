module
public import CatalanCore.Li2.DecayCert.Bent.Analytic
public import CatalanCore.Li2.Decay.Bent
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem bentMajorant_antitone (z : ℝ) (hz : ValidZ z) (hn : z < 0) (d : DualDatum)
    (x : ℝ) (hx : 0 ≤ x) : AntitoneOn (bentMajorant x d.radius) (Ici 1) := by
  have hh := (bent_tail z hz hn d x hx).2
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 1)
  · intro y hy
    exact (hh y hy).1.continuousAt.continuousWithinAt
  · intro y hy
    exact (hh y ((interior_subset hy))).1.hasDerivWithinAt
  · intro y hy
    have hy1 : 1 ≤ y := interior_subset hy
    have hd := (hh y hy1).2
    have hq : 3/y ≤ (3:ℝ) := (div_le_iff₀ (by linarith)).mpr (by linarith)
    linarith [Real.pi_gt_three]

theorem bentMajorant_height_bound (x R H : ℝ) (hx : 0 ≤ x) (hR : 0 ≤ R) (hH : 1 ≤ H) :
    bentMajorant x R H ≤ 3*Real.log (x+H+1)-4*Real.log H+
      4*Real.log (x+H+R)-Real.pi*H := by
  have hH0 : 0 < H := by linarith
  have hr0 : 0 < Real.sqrt (x^2+H^2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg x])
  have hr : Real.sqrt (x^2+H^2) ≤ x+H := by
    apply (Real.sqrt_le_iff).2
    constructor
    · linarith
    · nlinarith [mul_nonneg hx hH0.le]
  have h1 := Real.log_le_log (show 0 < Real.sqrt (x^2+H^2)+1 by linarith)
    (add_le_add hr (le_refl 1))
  have h2 := Real.log_le_log (show 0 < Real.sqrt (x^2+H^2)+R by linarith)
    (add_le_add hr (le_refl R))
  dsimp only [bentMajorant]
  linarith

theorem bent_tail_checked (z : ℚ) (hz : ValidZ (z:ℝ)) (hn : z < 0)
    (b : BentInput) (c : BentCert) (hd : datumCheck b.data c.density=true)
    (hp : placementCheck b=true) (hc : scalarUpperCheck (bentTailExpr b c) c.ell=true) :
    ∀ y : ℝ,(b.height:ℝ) ≤ y → W (z:ℝ) b.data.dual.σ
      (((b.geom.coord b.geom.polygon.edges).1:ℝ)+y*Complex.I) ≤ (c.ell:ℝ) := by
  have hplace := hp
  simp only [placementCheck,Bool.and_eq_true] at hplace
  have hH : (1:ℝ) ≤ (b.height:ℝ) := by exact_mod_cast (of_decide_eq_true hplace.1.1).2.1
  have hR : (0:ℝ) ≤ (b.data.radius:ℝ) := by
    exact_mod_cast (sourceDataCheck_parts b.data.segments b.data.radius c.density hd).1.1
  let d : DualDatum := { b.data.dual with
    radius := (b.data.radius:ℝ)
    radius_nonneg := hR
    bounded := (datumCheck_positive b.data c.density hd).2 }
  have hx : (0:ℝ) ≤ ((b.geom.coord b.geom.polygon.edges).1:ℝ) := by
    have h := (bent_vertex_quadrant b b.geom.polygon.edges le_rfl).1
    have he := congrArg Complex.re (b.geom.coord_eq b.geom.polygon.edges le_rfl)
    rw [← he] at h
    simpa only [cqReal_mk] using h
  have hnR : (z:ℝ) < 0 := by exact_mod_cast hn
  have hmaj := bentMajorant_height_bound ((b.geom.coord b.geom.polygon.edges).1:ℝ)
    (b.data.radius:ℝ) (b.height:ℝ) hx hR hH
  have hscalar := scalarUpperCheck_sound _ _ hc
  have hexpr : (bentTailExpr b c).value=
      3*Real.log (((b.geom.coord b.geom.polygon.edges).1:ℝ)+(b.height:ℝ)+1)-
      4*Real.log (b.height:ℝ)+4*Real.log (((b.geom.coord b.geom.polygon.edges).1:ℝ)+
      (b.height:ℝ)+(b.data.radius:ℝ))-Real.pi*(b.height:ℝ) := by
    simp only [bentTailExpr,seSum,List.foldl_cons,List.foldl_nil,seAdd_value,seScale_value,
      seRat_value,ScalarExpr.value]
    push_cast
    ring
  rw [hexpr] at hscalar
  intro y hy
  have hfield := (bent_tail (z:ℝ) hz hnR d _ hx).1 y (hH.trans hy)
  have hanti := bentMajorant_antitone (z:ℝ) hz hnR d _ hx hH (hH.trans hy) hy
  exact hfield.trans (hanti.trans (hmaj.trans hscalar))
#print axioms bentMajorant_antitone
#print axioms bentMajorant_height_bound
#print axioms bent_tail_checked
end
end CatalanCore.Li2.DecayCert
