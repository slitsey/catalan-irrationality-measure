module
public import CatalanCore.Cert.QuarterCompute.SegmentLedger
public import Init.Data.List.Int.Sum
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.SegmentLedger
theorem svalues_append (p q : Int) (xs ys : List FastNode.QBox) :
    svalues p q (xs++ys) = svalues p q xs+svalues p q ys := by
  simp only [svalues,List.map_append,List.sum_append_int]
end CatalanCore.Cert.QuarterCompute.SegmentLedger
