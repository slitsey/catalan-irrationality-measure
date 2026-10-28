import CatalanCore.Uniform.Decay.Polygon.Data
import CatalanCore.Uniform.Decay.Polygon.Rules

/-!
Axiom audit for the D4 polygon package, plus an exact rational instance: the sevenths polygon of
`sevenths-decay-2026-10-27/exact-check/exact-A-tight.json` (checked there by `hyp.py`) is
admissible, has first-edge inverse slope `q = -2521/5000`, and satisfies `1 ≤ r Im p_j` for
`r ≥ 13`.
-/

open CatalanCore.Uniform.Decay.Polygon

namespace CatalanCore.Uniform.Decay.Polygon.AuditD4

/-- The sevenths polygon (`hyp.py`): `p₀ = -273/2000`, two vertices, tail slope `5000/1353`. -/
def sevenths : RatPolygon where
  r0 := 273 / 2000
  verts := [(-8809027 / 50000000, 787 / 10000), (-11253987 / 50000000, 1041 / 5000)]
  s := 5000 / 1353

theorem sevenths_ok : sevenths.OK where
  r0_pos := by norm_num [sevenths]
  upper := by
    intro p hp
    simp only [sevenths, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> norm_num
  slope := by norm_num [sevenths]

theorem sevenths_q : sevenths.qRat = -2521 / 5000 := by
  norm_num [RatPolygon.qRat, sevenths]

theorem sevenths_high {r : ℝ} (hr : 13 ≤ r) : ∀ p ∈ sevenths.verts, 1 ≤ r * (p.2 : ℝ) := by
  intro p hp
  simp only [sevenths, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> push_cast <;> nlinarith

end CatalanCore.Uniform.Decay.Polygon.AuditD4

#print axioms segI_add
#print axioms chainI_eq
#print axioms chain_close
#print axioms connector_tendsto_zero
#print axioms deform
#print axioms pathInt_eq
#print axioms polygon_contour_identity
#print axioms polygon_entry
#print axioms polygon_andreief_rect
#print axioms firstEdge_sep
#print axioms two_mul_norm_sub_round_le
#print axioms path_sin_lower
#print axioms norm_EC_path
#print axioms norm_EC_path_lower
#print axioms path_node_dist
#print axioms path_growth
#print axioms pathMass
#print axioms polygon_sourceRep
#print axioms convexHull_sub_tube
#print axioms segment_sub_cover
#print axioms abs_mul_logPot_sub_logPot_le
#print axioms tail_rule
#print axioms CatalanCore.Uniform.Decay.Polygon.AuditD4.sevenths_ok
#print axioms CatalanCore.Uniform.Decay.Polygon.AuditD4.sevenths_q
#print axioms CatalanCore.Uniform.Decay.Polygon.AuditD4.sevenths_high
#print axioms RatPolygon.chainLen_physPts
