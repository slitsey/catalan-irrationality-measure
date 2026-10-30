module
public import CatalanCore.Cert.QuarterContour.Glue
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.SegmentFold
open CatalanCore.Cert.SigmaQuarter

/-- Integer numerator of the clipped, weighted segment contribution. -/
def sval (p q : ℤ) (b : QBox) : ℤ :=
  (b.1.2.1-b.1.1)*min (q*b.2.2.2.1-p*2^32) 0
def svalues (p q : ℤ) (bs : List QBox) : ℤ := (bs.map (sval p q)).sum

lemma cost_sval (p q : ℤ) (hq : 0 < q) (b : QBox) :
    QuarterContour.segCost ((p : ℚ)/(q : ℚ)) b = (sval p q b : ℚ)/((q : ℚ)*2^72) := by
  have hqr : 0 < (q : ℚ) := by exact_mod_cast hq
  have hden : 0 < (q : ℚ)*2^32 := by positivity
  have he : (b.2.2.2.1 : ℚ)/2^32-(p : ℚ)/(q : ℚ) =
      ((q*b.2.2.2.1-p*2^32 : ℤ) : ℚ)/((q : ℚ)*2^32) := by
    push_cast
    field_simp [hqr.ne'] <;> ring
  unfold QuarterContour.segCost QuarterContour.axisInterval QuarterContour.gamma SigmaP6.qmin
  rw [he]
  by_cases hi : q*b.2.2.2.1-p*2^32 ≤ 0
  · have hr : ((q*b.2.2.2.1-p*2^32 : ℤ) : ℚ) ≤ 0 := by exact_mod_cast hi
    rw [if_pos (div_nonpos_of_nonpos_of_nonneg hr hden.le)]
    simp only [sval,min_eq_left hi]
    push_cast
    field_simp [hqr.ne'] <;> ring
  · have hir : 0 < ((q*b.2.2.2.1-p*2^32 : ℤ) : ℚ) := by exact_mod_cast (lt_of_not_ge hi)
    rw [if_neg (not_le_of_gt (div_pos hir hden))]
    simp only [sval,min_eq_right (le_of_lt (lt_of_not_ge hi)),mul_zero,Int.cast_zero,zero_div]

lemma cost_sum_sval (p q : ℤ) (hq : 0 < q) (bs : List QBox) :
    (bs.map (QuarterContour.segCost ((p : ℚ)/(q : ℚ)))).sum =
      (svalues p q bs : ℚ)/((q : ℚ)*2^72) := by
  induction bs with
  | nil => simp [svalues]
  | cons b bs ih =>
    rw [List.map_cons,List.sum_cons,cost_sval p q hq b,ih]
    simp only [svalues,List.map_cons,List.sum_cons,Int.cast_add]
    ring

lemma svalues_append (p q : ℤ) (xs ys : List QBox) :
    svalues p q (xs++ys) = svalues p q xs+svalues p q ys := by
  simp only [svalues,List.map_append,List.sum_append]

lemma boxes_append (xs ys : List Macro) : QuarterContour.boxes (xs++ys) =
    QuarterContour.boxes xs++QuarterContour.boxes ys := by
  simp only [QuarterContour.boxes,List.flatMap_append]
lemma intervals_append (xs ys : List Macro) : QuarterContour.intervals (xs++ys) =
    QuarterContour.intervals xs++QuarterContour.intervals ys := by
  simp only [QuarterContour.intervals,boxes_append,List.map_append]
end CatalanCore.Cert.QuarterContour.SegmentFold
#print axioms CatalanCore.Cert.QuarterContour.SegmentFold.cost_sum_sval
