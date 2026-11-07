module
public import CatalanFrames.HybGen.ClassBand
@[expose] public section
open CatalanCore.Arith.Hybrid
namespace CatalanFrames.P6Hybrid
lemma covers_mk (c : ZMod 6) (cn : ℕ) (hcn : ∀ p : ℕ, (p : ZMod 6) = c → p % 6 = cn)
    (wf : ℕ → ℕ) (r sn sd tn td : ℕ) (A B E D : ℤ) (hD : 0 < D)
    (h : ∀ p : ℕ, sn * r / sd < p → p ≤ tn * r / td → p % 6 = cn →
      D * (wf p : ℤ) ≤ A * r + B * p + E) :
    Covers c (fun p => (wf p : ℝ)) r (mkPiece sn sd tn td A B E D) :=
  HybGen.covers_mkM c (fun p => p%6=cn) (fun p _ hc => hcn p hc)
    wf r sn sd tn td A B E D hD (fun p hs ht _ hc => h p hs ht hc)

lemma cls_one {p : ℕ} (h : (p : ZMod 6) = 1) : p % 6 = 1 := by
  have := (ZMod.natCast_eq_natCast_iff' p 1 6).mp (by simpa using h)
  omega

lemma cls_five {p : ℕ} (h : (p : ZMod 6) = 5) : p % 6 = 5 := by
  have := (ZMod.natCast_eq_natCast_iff' p 5 6).mp (by simpa using h)
  omega

end CatalanFrames.P6Hybrid
