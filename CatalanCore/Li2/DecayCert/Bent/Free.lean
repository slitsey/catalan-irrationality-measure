module
public import CatalanCore.Li2.DecayCert.Bent.Geometry
public import CatalanCore.Li2.DecayCert.Bent.Tail
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
open CatalanCore.Li2.Uniform (piecesSet pieceSet polygonPieces polygonSet polygonFree)
open CatalanCore.Decay.CurveFamily (Piece)
noncomputable section

theorem edgeOrigin_value (b : BentInput) (j : ℕ) (hj : j ≤ b.geom.polygon.edges) :
    cqReal (edgeOrigin b j)=b.geom.polygon.vertex j := b.geom.coord_eq j hj

theorem edgeDirection_finite_value (b : BentInput) (j : ℕ) (hj : j < b.geom.polygon.edges) :
    cqReal (edgeDirection b j)=b.geom.polygon.vertex (j+1)-b.geom.polygon.vertex j := by
  rw [edgeDirection,if_neg (Nat.ne_of_lt hj),cqReal_sub,b.geom.coord_eq (j+1) (by omega),b.geom.coord_eq j hj.le]

theorem edgeDirection_ray_value (b : BentInput) : cqReal (edgeDirection b b.geom.polygon.edges)=Complex.I := by
  simp [edgeDirection,cqReal]

theorem bent_upper_bound (z : ℚ) (hz : ValidZ (z:ℝ)) (hn : z < 0)
    (b : BentInput) (c : BentCert) (hd : datumCheck b.data c.density=true)
    (hp : placementCheck b=true) (hc : contourCoverCheck b c.contour=true)
    (hb : ∀ cell ∈ c.contour,∃ B,contourBounds z b cell=some B ∧ B.2 ≤ c.ell)
    (htail : scalarUpperCheck (bentTailExpr b c) c.ell=true) :
    ∀ u ∈ piecesSet (polygonPieces b.geom.polygon),W (z:ℝ) b.data.dual.σ u ≤ (c.ell:ℝ) := by
  intro u hu
  rcases mem_iUnion.1 hu with ⟨p,hu⟩
  rcases mem_iUnion.1 hu with ⟨hpm,hu⟩
  have hz0 : z ≠ 0 := ne_of_lt hn
  change p ∈ ((List.range b.geom.polygon.edges).map (fun j =>
    (⟨b.geom.polygon.vertex j,b.geom.polygon.vertex (j+1)-b.geom.polygon.vertex j,false⟩:Piece))++
      [⟨b.geom.polygon.vertex b.geom.polygon.edges,Complex.I,true⟩]) at hpm
  rcases List.mem_append.mp hpm with hpm | hpm
  · rcases List.mem_map.mp hpm with ⟨j,hj,rfl⟩
    have hj' := List.mem_range.mp hj
    rcases hu with ⟨t,ht,rfl⟩
    change t ∈ Icc 0 1 at ht
    have hlim : edgeLimit b j=1 := by simp [edgeLimit,Nat.ne_of_lt hj']
    have hv := contour_cover_point z hz0 b c.density hd c.contour hc c.ell hb j hj'.le
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
    · have hh := bent_tail_checked z hz hn b c hd hp htail (v.im+t) hy
      rw [hvre] at hh
      have hpoint : (⟨v,Complex.I,true⟩:Piece).zeta t=(v.re:ℂ)+(v.im+t)*Complex.I := by
        apply Complex.ext <;> simp [Piece.zeta,Complex.mul_re,Complex.mul_im] <;> ring
      simpa only [v,hpoint,Complex.ofReal_add] using hh
    · have hlt : v.im+t < (b.height:ℝ) := lt_of_not_ge hy
      have hvim : ((b.geom.coord b.geom.polygon.edges).2:ℝ)=v.im := by
        have hh := congrArg Complex.im hv
        simpa only [cqReal_mk] using hh
      have hlim : (edgeLimit b b.geom.polygon.edges:ℝ)=(b.height:ℝ)-v.im := by
        simp only [edgeLimit,ite_true,Rat.cast_sub,hvim]
      have hlimpos : 0 < edgeLimit b b.geom.polygon.edges := by
        have hr : (0:ℝ) < (edgeLimit b b.geom.polygon.edges:ℝ) := by rw [hlim]; linarith
        exact_mod_cast hr
      have hh := contour_cover_point z hz0 b c.density hd c.contour hc c.ell hb _ le_rfl hlimpos t
        (by rw [hlim]; constructor <;> linarith)
      rw [edgeOrigin_value b _ le_rfl,edgeDirection_ray_value] at hh
      simpa only [Piece.zeta,v,mul_comm] using hh

theorem bent_free_bound (z : ℚ) (hz : ValidZ (z:ℝ)) (hn : z < 0)
    (b : BentInput) (c : BentCert) (hd : datumCheck b.data c.density=true)
    (hp : placementCheck b=true) (hc : contourCoverCheck b c.contour=true)
    (hb : ∀ cell ∈ c.contour,∃ B,contourBounds z b cell=some B ∧ B.2 ≤ c.ell)
    (htail : scalarUpperCheck (bentTailExpr b c) c.ell=true) :
    FreeBound (z:ℝ) b.geom.frame b.data.dual (c.ell:ℝ) := by
  have hupper := bent_upper_bound z hz hn b c hd hp hc hb htail
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
#print axioms bent_upper_bound
#print axioms bent_free_bound
end
end CatalanCore.Li2.DecayCert
