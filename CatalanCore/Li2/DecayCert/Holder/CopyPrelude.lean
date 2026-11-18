module
public import CatalanCore.Li2.DecayCert.Holder.Geometry
public import CatalanCore.Li2.DecayCert.Holder.Enclosure
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Tools.Joukowski
noncomputable section

def holderFQ (d : QSegment) (H : ℚ) : ℚ :=
  ((List.range d.coeff.length).map (fun k : ℕ => |d.c k| *H^k)).sum

def holderAQ (d : QSegment) (H : ℚ) : ℚ :=
  ((List.range (d.coeff.length-1)).map (fun k : ℕ => (k+1:ℚ)*|d.c (k+1)| *H^k)).sum

theorem holderFQ_value (d : QSegment) (H : ℚ) :
    (holderFQ d H:ℝ)=∑ k ∈ Finset.range d.coeff.length,|(d.c k:ℝ)| *(H:ℝ)^k := by
  unfold holderFQ
  rw [list_sum_map_range]
  push_cast
  rfl

theorem holderAQ_value (d : QSegment) (H : ℚ) :
    (holderAQ d H:ℝ)=∑ k ∈ Finset.range (d.coeff.length-1),(k+1:ℕ)*|(d.c (k+1):ℝ)| *(H:ℝ)^k := by
  unfold holderAQ
  rw [list_sum_map_range]
  push_cast
  rfl

theorem holderCopyBound_common (d : QSegment) (p e : CQ) (R : ℚ) (w : HolderCopyWitness) (H : ℚ)
    (hc : holderCopyBound d p e R w=some H) :
    cqSq d.half ≠ 0 ∧ 0 ≤ R ∧ 0 ≤ w.gammaHi ∧ 0 ≤ w.zetaHi ∧
    cqSq (cqDiv e d.half) ≤ w.gammaHi^2 ∧ cqSq (cqDiv (cqSub p d.mid) d.half) ≤ w.zetaHi^2 ∧
    w.zetaHi+w.gammaHi*R ≤ w.phiHi ∧
    (w.zetaHi+w.gammaHi*R)^2+1 ≤ (w.phiHi-(w.zetaHi+w.gammaHi*R))^2 := by
  unfold holderCopyBound at hc
  dsimp only at hc
  split at hc
  · contradiction
  · rename_i hbad
    push_neg at hbad
    exact hbad

theorem holderCopyBound_ellipse (d : QSegment) (p e : CQ) (R : ℚ) (w : HolderCopyWitness) (H : ℚ)
    (hc : holderCopyBound d p e R w=some H) :
    ∃ hh : cqReal d.half ≠ 0,
      0 ≤ R ∧ ‖cqReal e/cqReal d.half‖*(R:ℝ) ≤ (w.gammaHi*R:ℚ) ∧
      endPhi (d.toSegment hh) (cqReal p) (cqReal e) R ≤ (w.phiHi:ℝ) ∧
      (∑ k ∈ Finset.range (d.coeff.length-1+1),|(d.c k:ℝ)| *
        (endPhi (d.toSegment hh) (cqReal p) (cqReal e) R)^k) ≤ (holderFQ d w.phiHi:ℝ) ∧
      (∑ k ∈ Finset.range (d.coeff.length-1),(k+1:ℕ)*|(d.c (k+1):ℝ)| *
        (endPhi (d.toSegment hh) (cqReal p) (cqReal e) R)^k) ≤ (holderAQ d w.phiHi:ℝ) := by
  rcases holderCopyBound_common d p e R w H hc with ⟨hh0,hR,hg,hz,hgsq,hzsq,hH,hHsq⟩
  have hh := cqReal_ne_of_cqSq_ne d.half hh0
  have hr : 0 ≤ (R:ℝ) := by exact_mod_cast hR
  have hγ : ‖cqReal e/cqReal d.half‖ ≤ (w.gammaHi:ℝ) := by
    rw [← cqReal_div]
    exact norm_cqReal_le_of_cqSq_le hg hgsq
  have hζ : ‖(cqReal p-cqReal d.mid)/cqReal d.half‖ ≤ (w.zetaHi:ℝ) := by
    rw [← cqReal_sub,← cqReal_div]
    exact norm_cqReal_le_of_cqSq_le hz hzsq
  have hZ : endZ (d.toSegment hh) (cqReal p) (cqReal e) R ≤
      (w.zetaHi:ℝ)+(w.gammaHi:ℝ)*(R:ℝ) :=
    add_le_add hζ (mul_le_mul_of_nonneg_right hγ hr)
  have hΦ := endPhi_le_of_upper (d.toSegment hh) (cqReal p) (cqReal e) R
    ((w.zetaHi:ℝ)+(w.gammaHi:ℝ)*(R:ℝ)) w.phiHi hr hZ (by exact_mod_cast hH) (by exact_mod_cast hHsq)
  have hp0 : 0 ≤ endPhi (d.toSegment hh) (cqReal p) (cqReal e) R :=
    zero_le_one.trans (endPhi_one_le _ _ _ _ hr)
  refine ⟨hh,hR,?_,hΦ,?_,?_⟩
  · push_cast
    exact mul_le_mul_of_nonneg_right hγ hr
  · rw [holderFQ_value]
    exact qsegment_F_bound d _ _ hp0 hΦ
  · rw [holderAQ_value]
    exact qsegment_A_bound d _ _ hp0 hΦ
#print axioms holderFQ_value
#print axioms holderAQ_value
#print axioms holderCopyBound_common
#print axioms holderCopyBound_ellipse
end
end CatalanCore.Li2.DecayCert
