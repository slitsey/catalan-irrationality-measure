module
public import CatalanCore.Li2.DecayCert.BentSpec
public import CatalanCore.Li2.DecayCert.Holder
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay
noncomputable section

theorem positiveSources_exprSum (xs : List CellExpr) (hx : ∀ e ∈ xs,PositiveSources e) :
    PositiveSources (exprSum xs) := by
  have hh : ∀ xs : List CellExpr,∀ b : CellExpr,PositiveSources b →
      (∀ e ∈ xs,PositiveSources e) → PositiveSources (xs.foldl CellExpr.add b) := by
    intro xs
    induction xs with
    | nil => simp
    | cons e xs ih => intro b hb hx; exact ih (.add b e) ⟨hb,hx e List.mem_cons_self⟩ (fun q hq => hx q (List.mem_cons_of_mem e hq))
  exact hh xs (.constant (.rat 0)) trivial hx

theorem positiveSources_segmentSum (ss : List QSegment) (p e : CQ)
    (hp : ∀ s ∈ ss,PositiveSources (.segment s p e)) :
    PositiveSources (exprSum (ss.map (fun s => .scale 2 (.segment s p e)))) := by
  apply positiveSources_exprSum
  intro x hx
  rcases List.mem_map.mp hx with ⟨s,hs,rfl⟩
  exact hp s hs

theorem atomExpr_positive (terms : ℕ) (z : ℚ) (ss : List QSegment) (x dir : ℚ)
    (hp : ∀ s ∈ ss,∀ t ∈ Icc (-1:ℝ) 1,0 ≤ CatalanCore.Zeta5.Potential.chebF
      (fun k => (s.c k:ℝ)) (s.coeff.length-1) t) : PositiveSources (atomExpr terms z ss x dir) := by
  apply positiveSources_exprSum
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false]
  intro e he
  rcases he with rfl | rfl | rfl | rfl | rfl
  all_goals try trivial
  exact positiveSources_segmentSum ss _ _ hp

theorem atomCell_parameter_bounds (c : AtomCell)
    (hc : 1 ≤ c.left ∧ c.left < c.right ∧ c.right ≤ 4)
    (u : ℝ) (hu : u ∈ Icc 0 ((c.right-c.left:ℚ):ℝ)) :
    (c.start:ℝ)+(c.dir:ℝ)*u ∈ Icc 1 4 := by
  have hl : (1:ℝ) ≤ (c.left:ℝ) := by exact_mod_cast hc.1
  have hr : (c.right:ℝ) ≤ (4:ℝ) := by exact_mod_cast hc.2.2
  have huR : u ≤ (c.right:ℝ)-(c.left:ℝ) := by simpa only [Rat.cast_sub] using hu.2
  cases hb : c.backwards <;> simp only [AtomCell.start,AtomCell.dir,hb,Bool.false_eq_true,ite_false,ite_true,
    Rat.cast_neg,Rat.cast_one,one_mul,neg_one_mul] <;> constructor <;> linarith [hu.1]

theorem lineCell_atomPoly (z : ℚ) (hz : z ≠ 0) (d : SegmentDatum)
    (dw : DensityWitness) (hd : datumCheck d dw=true) (c : AtomCell)
    (hc : atomCellCheck z d c=true) :
    ∀ u ∈ Icc 0 ((c.right-c.left:ℚ):ℝ),omega (z:ℝ) ((c.start:ℝ)+(c.dir:ℝ)*u)-
      2*U d.dual.σ (-(((c.start:ℝ)+(c.dir:ℝ)*u:ℝ):ℂ)) ≤ (c.witness.a:ℝ)+(c.witness.b:ℝ)*u := by
  have hc' := hc
  simp only [atomCellCheck,Bool.and_eq_true,decide_eq_true_eq] at hc'
  have hp := atomExpr_positive c.terms z d.segments c.start c.dir (datumCheck_positive d dw hd).1
  intro u hu
  have hv := lineCellF_spec (atomCellInput z d c) c.witness hp hc'.2 u hu
  change (atomExpr c.terms z d.segments c.start c.dir).value u ≤ _ at hv
  rw [atomExpr_value _ _ hz d dw hd _ _ u (atomCell_parameter_bounds c hc'.1 u hu)] at hv
  convert hv using 1 <;> push_cast <;> ring

theorem bent_vertex_quadrant (b : BentInput) (j : ℕ) (hj : j ≤ b.geom.polygon.edges) :
    0 ≤ (b.geom.polygon.vertex j).re ∧ 0 ≤ (b.geom.polygon.vertex j).im := by
  by_cases hz : j=0
  · subst j
    rw [b.geom.polygon.initial,b.geom.cut_zero]
    norm_num
  · have hj0 : 1 ≤ j := by omega
    have hre := (b.geom.polygon.real_pos j hj0 hj).le
    have him := b.geom.polygon.imag_strict 0 j (by omega) hj
    rw [b.geom.polygon.initial,b.geom.cut_zero] at him
    exact ⟨hre,by simpa using him.le⟩

theorem bent_edge_quadrant (b : BentInput) (j : ℕ) (hj : j ≤ b.geom.polygon.edges)
    (t : ℝ) (ht : t ∈ Icc 0 (edgeLimit b j:ℝ)) :
    0 ≤ (cqReal (edgeOrigin b j)+cqReal (edgeDirection b j)*(t:ℂ)).re ∧
    0 ≤ (cqReal (edgeOrigin b j)+cqReal (edgeDirection b j)*(t:ℂ)).im := by
  have h0 := bent_vertex_quadrant b j hj
  have ho : cqReal (edgeOrigin b j)=b.geom.polygon.vertex j := b.geom.coord_eq j hj
  rw [ho]
  by_cases he : j=b.geom.polygon.edges
  · simp only [edgeDirection,if_pos he,cqReal,Rat.cast_zero,Rat.cast_one,zero_add,one_mul,
      Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_mul,sub_zero,add_zero,Complex.add_im,Complex.mul_im,mul_one]
    exact ⟨h0.1,add_nonneg h0.2 ht.1⟩
  · have hj1 : j+1 ≤ b.geom.polygon.edges := by omega
    have h1 := bent_vertex_quadrant b (j+1) hj1
    have hdir : cqReal (edgeDirection b j)=b.geom.polygon.vertex (j+1)-b.geom.polygon.vertex j := by
      rw [edgeDirection,if_neg he,cqReal_sub,b.geom.coord_eq (j+1) hj1,b.geom.coord_eq j hj]
    rw [hdir]
    have ht1 : t ≤ 1 := by simpa [edgeLimit,he] using ht.2
    simp only [Complex.add_re,Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero,Complex.add_im,Complex.mul_im,Complex.sub_im,zero_mul,add_zero]
    constructor
    · nlinarith [mul_nonneg ht.1 h1.1,mul_nonneg (sub_nonneg.mpr ht1) h0.1]
    · nlinarith [mul_nonneg ht.1 h1.2,mul_nonneg (sub_nonneg.mpr ht1) h0.2]

theorem contour_cell_parameter (b : BentInput) (c : ContourCell) (u : ℝ) :
    cqReal (contourNodeCell b c).p+cqReal (contourNodeCell b c).e*(u:ℂ)=
      cqReal (edgeOrigin b c.edge)+cqReal (edgeDirection b c.edge)*
        (((if c.backwards then (c.right:ℝ)-u else (c.left:ℝ)+u):ℝ):ℂ) := by
  cases hb : c.backwards <;> simp only [contourNodeCell,hb,Bool.false_eq_true,ite_false,ite_true,
    cqReal_add,cqReal_scale,cqReal_neg,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_ratCast] <;> ring

theorem cellC1_okF (z : ℚ) (hz : z ≠ 0) (b : BentInput)
    (dw : DensityWitness) (hd : datumCheck b.data dw=true) (c : ContourCell) (B : QBox)
    (hc : contourBounds z b c=some B) :
    ∀ u ∈ Icc 0 ((c.right-c.left:ℚ):ℝ),W (z:ℝ) b.data.dual.σ
      (cqReal (contourNodeCell b c).p+cqReal (contourNodeCell b c).e*(u:ℂ)) ∈ Icc (B.1:ℝ) (B.2:ℝ) := by
  unfold contourBounds at hc
  split_ifs at hc with hg
  have hparam (u : ℝ) (hu : u ∈ Icc 0 ((c.right-c.left:ℚ):ℝ)) :
      (if c.backwards then (c.right:ℝ)-u else (c.left:ℝ)+u) ∈ Icc 0 (edgeLimit b c.edge:ℝ) := by
    have hleft : (0:ℝ) ≤ (c.left:ℝ) := by exact_mod_cast hg.2.1
    have hright : (c.right:ℝ) ≤ (edgeLimit b c.edge:ℝ) := by exact_mod_cast hg.2.2.2
    have huR : u ≤ (c.right:ℝ)-(c.left:ℝ) := by simpa only [Rat.cast_sub] using hu.2
    cases hb : c.backwards <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true] <;> constructor <;> linarith [hu.1]
  have hquad (u : ℝ) (hu : u ∈ Icc 0 ((contourNodeCell b c).width:ℝ)) :
      0 ≤ (cqReal (contourNodeCell b c).p+cqReal (contourNodeCell b c).e*(u:ℂ)).re ∧
      0 ≤ (cqReal (contourNodeCell b c).p+cqReal (contourNodeCell b c).e*(u:ℂ)).im := by
    rw [contour_cell_parameter]
    exact bent_edge_quadrant b c.edge hg.1 _ (hparam u hu)
  exact fieldCellBounds_sound z hz b.data dw hd (contourNodeCell b c) c.method B hc
    (fun u hu => (hquad u hu).1) (fun u hu => (hquad u hu).2)
#print axioms positiveSources_exprSum
#print axioms atomExpr_positive
#print axioms lineCell_atomPoly
#print axioms bent_vertex_quadrant
#print axioms bent_edge_quadrant
#print axioms contour_cell_parameter
#print axioms cellC1_okF
end
end CatalanCore.Li2.DecayCert
