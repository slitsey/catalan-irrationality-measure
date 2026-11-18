module
public import CatalanCore.Li2.DecayCert.Seg.NodeDefs
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert.Seg
open CatalanCore.Li2.DecayCert CatalanCore.Li2.Decay
open CatalanCore.Li2.Uniform (piecesSet pieceSet polygonPieces polygonSet polygonFree)
open CatalanCore.Decay.CurveFamily (Piece)
noncomputable section

variable {CC AC : Type} [ContourProj CC] [AtomProj AC]

theorem node_contour_cover_point (z : ℚ) (b : BentInput) (cs : List (CC × QBox))
    (hc : nodeContourCoverCheck b cs=true) (ell : ℚ) (hb : ∀ x ∈ cs,x.2.2 ≤ ell)
    (hphys : NodeContourPhysical z b cs)
    (j : ℕ) (hj : j ≤ b.geom.polygon.edges) (hlim : 0 < edgeLimit b j)
    (t : ℝ) (ht : t ∈ Icc 0 (edgeLimit b j:ℝ)) :
    W (z:ℝ) b.data.dual.σ (cqReal (edgeOrigin b j)+cqReal (edgeDirection b j)*(t:ℂ)) ≤ (ell:ℝ) := by
  have hh := hc
  simp only [nodeContourCoverCheck,Bool.and_eq_true] at hh
  let selected := cs.filter (fun c => ContourProj.edge c.1==j)
  let intervals := selected.map (fun c : CC × QBox => (⟨ContourProj.left c.1,ContourProj.right c.1⟩:QInterval))
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
  have hej : ContourProj.edge c.1=j := by simpa using he
  have hv := (hphys c hcc t htq).2
  rw [hej] at hv
  exact hv.trans (by exact_mod_cast hb c hcc)

theorem node_upper_bound (z : ℚ) (hz : ValidZ (z:ℝ)) (hn : z < 0)
    (b : BentInput) (c : NodeCert CC AC) (hd : datumCheck b.data c.density=true)
    (hp : placementCheck b=true) (hc : nodeContourCoverCheck b c.contour=true)
    (hb : ∀ x ∈ c.contour,x.2.2 ≤ c.ell) (hphys : NodeContourPhysical z b c.contour)
    (htail : scalarUpperCheck (bentTailExpr b c.toBent) c.ell=true) :
    ∀ u ∈ piecesSet (polygonPieces b.geom.polygon),W (z:ℝ) b.data.dual.σ u ≤ (c.ell:ℝ) := by
  intro u hu
  rcases mem_iUnion.1 hu with ⟨p,hu⟩
  rcases mem_iUnion.1 hu with ⟨hpm,hu⟩
  change p ∈ ((List.range b.geom.polygon.edges).map (fun j =>
    (⟨b.geom.polygon.vertex j,b.geom.polygon.vertex (j+1)-b.geom.polygon.vertex j,false⟩:Piece))++
      [⟨b.geom.polygon.vertex b.geom.polygon.edges,Complex.I,true⟩]) at hpm
  rcases List.mem_append.mp hpm with hpm | hpm
  · rcases List.mem_map.mp hpm with ⟨j,hj,rfl⟩
    have hj' := List.mem_range.mp hj
    rcases hu with ⟨t,ht,rfl⟩
    change t ∈ Icc 0 1 at ht
    have hlim : edgeLimit b j=1 := by simp [edgeLimit,Nat.ne_of_lt hj']
    have hv := node_contour_cover_point z b c.contour hc c.ell hb hphys j hj'.le
      (by rw [hlim]; norm_num) t (by simpa only [hlim,Rat.cast_one] using ht)
    rw [edgeOrigin_value b j hj'.le,edgeDirection_finite_value b j hj'] at hv
    simpa only [Piece.zeta,mul_comm] using hv
  · have he : p=⟨b.geom.polygon.vertex b.geom.polygon.edges,Complex.I,true⟩ := List.mem_singleton.mp hpm
    subst p
    rcases hu with ⟨t,ht,rfl⟩
    change 0 ≤ t at ht
    let v := b.geom.polygon.vertex b.geom.polygon.edges
    have hv : cqReal (b.geom.coord b.geom.polygon.edges)=v := b.geom.coord_eq _ le_rfl
    have hvre : ((b.geom.coord b.geom.polygon.edges).1:ℝ)=v.re := by
      have hh := congrArg Complex.re hv
      simpa only [cqReal_mk] using hh
    by_cases hy : (b.height:ℝ) ≤ v.im+t
    · have hh := bent_tail_checked z hz hn b c.toBent hd hp htail (v.im+t) hy
      rw [hvre] at hh
      have hpoint : (⟨v,Complex.I,true⟩:Piece).zeta t=(v.re:ℂ)+(v.im+t)*Complex.I := by
        apply Complex.ext <;> simp [Piece.zeta,Complex.mul_re,Complex.mul_im] <;> ring
      simpa only [v,hpoint,Complex.ofReal_add,NodeCert.toBent] using hh
    · have hlt : v.im+t < (b.height:ℝ) := lt_of_not_ge hy
      have hvim : ((b.geom.coord b.geom.polygon.edges).2:ℝ)=v.im := by
        have hh := congrArg Complex.im hv
        simpa only [cqReal_mk] using hh
      have hlim : (edgeLimit b b.geom.polygon.edges:ℝ)=(b.height:ℝ)-v.im := by
        simp only [edgeLimit,ite_true,Rat.cast_sub,hvim]
      have hlimpos : 0 < edgeLimit b b.geom.polygon.edges := by
        have hr : (0:ℝ) < (edgeLimit b b.geom.polygon.edges:ℝ) := by rw [hlim]; linarith
        exact_mod_cast hr
      have hh := node_contour_cover_point z b c.contour hc c.ell hb hphys _ le_rfl hlimpos t
        (by rw [hlim]; constructor <;> linarith)
      rw [edgeOrigin_value b _ le_rfl,edgeDirection_ray_value] at hh
      simpa only [Piece.zeta,v,mul_comm] using hh

theorem node_free_bound (z : ℚ) (hz : ValidZ (z:ℝ)) (hn : z < 0)
    (b : BentInput) (c : NodeCert CC AC) (hd : datumCheck b.data c.density=true)
    (hp : placementCheck b=true) (hc : nodeContourCoverCheck b c.contour=true)
    (hb : ∀ x ∈ c.contour,x.2.2 ≤ c.ell) (hphys : NodeContourPhysical z b c.contour)
    (htail : scalarUpperCheck (bentTailExpr b c.toBent) c.ell=true) :
    FreeBound (z:ℝ) b.geom.frame b.data.dual (c.ell:ℝ) := by
  have hupper := node_upper_bound z hz hn b c hd hp hc hb hphys htail
  intro u hu
  have hneg : ¬(0:ℝ)<(z:ℝ) := by exact_mod_cast not_lt.mpr hn.le
  have hf : CatalanCore.Li2.Uniform.free b.geom.frame (z:ℝ)=polygonSet b.geom.polygon := by
    rw [CatalanCore.Li2.Uniform.free,if_neg hneg,b.geom.hfree]
    simp only [polygonFree,show (-1:ℤ) ≠ 1 by norm_num,ite_false,union_empty]
  change u ∈ CatalanCore.Li2.Uniform.free b.geom.frame (z:ℝ) at hu
  rw [hf] at hu
  rcases hu with hu | hu
  · exact hupper u hu
  · rcases hu with ⟨v,hv,rfl⟩
    rw [bent_W_conj (z:ℝ) b hp]
    exact hupper v hv
#print axioms node_upper_bound
#print axioms node_free_bound
end
end CatalanCore.Li2.DecayCert.Seg
