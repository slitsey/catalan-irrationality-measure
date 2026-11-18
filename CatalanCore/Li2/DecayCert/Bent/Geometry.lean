module
public import CatalanCore.Li2.DecayCert.Bent.Analytic
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem contour_cover_point (z : ℚ) (hz : z ≠ 0) (b : BentInput) (dw : DensityWitness)
    (hd : datumCheck b.data dw=true) (cs : List ContourCell) (hc : contourCoverCheck b cs=true)
    (ell : ℚ) (hb : ∀ c ∈ cs,∃ B,contourBounds z b c=some B ∧ B.2 ≤ ell)
    (j : ℕ) (hj : j ≤ b.geom.polygon.edges) (hlim : 0 < edgeLimit b j)
    (t : ℝ) (ht : t ∈ Icc 0 (edgeLimit b j:ℝ)) :
    W (z:ℝ) b.data.dual.σ (cqReal (edgeOrigin b j)+cqReal (edgeDirection b j)*(t:ℂ)) ≤ (ell:ℝ) := by
  have hh := hc
  simp only [contourCoverCheck,Bool.and_eq_true] at hh
  let selected := cs.filter (fun c => c.edge==j)
  let intervals := selected.map (fun c : ContourCell => (⟨c.left,c.right⟩:QInterval))
  have hchain : chainCheck 0 (edgeLimit b j) intervals=true :=
    (List.all_eq_true.mp hh.1) j (List.mem_range.mpr (by omega))
  have hcover := chainCheck_closed_cover 0 (edgeLimit b j) intervals hlim hchain
  norm_num only [Rat.cast_zero] at hcover
  have hm : t ∈ Icc (0:ℝ) (edgeLimit b j:ℝ) := ht
  rw [hcover] at hm
  rcases mem_iUnion.1 hm with ⟨q,hm⟩
  rcases mem_iUnion.1 hm with ⟨hq,htq⟩
  rcases List.mem_map.mp hq with ⟨c,hcsel,rfl⟩
  rcases List.mem_filter.mp hcsel with ⟨hcc,he⟩
  have hej : c.edge=j := by simpa using he
  rcases hb c hcc with ⟨B,hBc,hBell⟩
  have hv := (contourBounds_physical z hz b dw hd c B hBc t htq).2
  rw [hej] at hv
  exact hv.trans (by exact_mod_cast hBell)

theorem base_source_im_nonneg (b : BentInput) (hp : placementCheck b=true)
    (s : QSegment) (hs : s ∈ baseSegments b) : ∀ᵐ u : ℂ ∂s.measure,0 ≤ u.im := by
  have hparam : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ (cqReal s.mid+cqReal s.half*(x:ℂ)).im := by
    intro x hx
    rcases List.mem_append.mp hs with hs | hs
    · rcases List.getElem_of_mem hs with ⟨j,hj,hsj⟩
      have hplace := hp
      simp only [placementCheck,Bool.and_eq_true] at hplace
      have hlen := (of_decide_eq_true hplace.1.1).1
      have hjp : j < b.placements.length := by omega
      let p := b.placements[j]
      have hrow := placementCheck_upper_row b hp j hj s p
        (by rw [List.getElem?_eq_getElem hj,hsj]) (List.getElem?_eq_getElem hjp)
      rw [placement_source_point b s p hrow.2.2.2.2.1 hrow.2.2.2.2.2 x]
      apply (bent_edge_quadrant b p.edge hrow.1.le _ _).2
      have hl : (0:ℝ) ≤ (p.left:ℝ) := by exact_mod_cast hrow.2.1
      have hlt : (p.left:ℝ) < (p.right:ℝ) := by exact_mod_cast hrow.2.2.1
      have hr : (p.right:ℝ) ≤ 1 := by exact_mod_cast hrow.2.2.2.1
      have he : edgeLimit b p.edge=1 := by simp only [edgeLimit,if_neg (Nat.ne_of_lt hrow.1)]
      rw [he,Rat.cast_one]
      constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hlt.le) (show 0 ≤ x+1 by linarith [hx.1]),
        mul_nonneg (sub_nonneg.mpr hlt.le) (sub_nonneg.mpr hx.2)]
    · have ha := placementCheck_atom b hp s hs
      rw [atom_source_point s ha.1 ha.2.1 x]
      simp
  rw [← sourceParameter_map s]
  apply (ae_map_iff (by fun_prop) (by measurability)).2
  filter_upwards [ae_iff.mpr (sourceParameter_supported s)] with x hx
  exact hparam x hx
#print axioms contour_cover_point
#print axioms base_source_im_nonneg
end
end CatalanCore.Li2.DecayCert
