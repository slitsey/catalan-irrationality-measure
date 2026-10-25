module
public import CatalanCore.Cert.QuarterCompute.FastNode
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.SegmentLedger
open CatalanCore.Cert.QuarterCompute.FastNode

def sval (p q : Int) (b : QBox) : Int :=
  (b.1.2.1-b.1.1)*min (q*b.2.2.2.1-p*2^32) 0
def svalues (p q : Int) (bs : List QBox) : Int := (bs.map (sval p q)).sum
def shape (b : QBox) : Prop := b.1.1 ≤ b.1.2.1 ∧ b.1.2.1 ≤ 0
instance (b : QBox) : Decidable (shape b) := by unfold shape; infer_instance

def chainCovers : List QBox → Int → Int → Bool
  | [], _, _ => false
  | b::bs, lo, hi => decide (b.1.1 ≤ lo) && (decide (hi ≤ b.1.2.1) || chainCovers bs b.1.2.1 hi)
end CatalanCore.Cert.QuarterCompute.SegmentLedger
