module
public import CatalanFrames.P6Hybrid.MinorCorank.Reflection
public import CatalanFrames.P6Hybrid.MinorCorank.Borders
public import CatalanFrames.P6Hybrid.MinorCorank.Rescue
public import CatalanCore.Linalg.PrincipalDeletion.BorderScale
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Rect CatalanFrames.P6 CatalanFrames.P6.NV
open CatalanFrames.LambdaHybrid.NV CatalanCore.Linalg.CauchyPolynomial
open CatalanCore.Arith.Hybrid.FiniteFieldCorank
namespace CatalanFrames.P6Hybrid
variable {ell t : ℕ} [Fact ell.Prime]

theorem physical_low_rescue (hl : ell=6*t+1) (ht : 1≤t) (r m : ℕ)
    (hKr : 2*t+1≤r) (htop : r+2*m≤3*t) (xb : ZMod ell)
    (d : Finset (Fin (2*t+1)))
    (hmodel : ((fromBlocks
      (cauchyGram (modelLow ell (2*t+1)) (highBand ell (ell-r-2*m)) (bandSign (3*t+1)) -
        (cc ell t-36*xb) • (1 : Matrix (Fin (2*t+1)) (Fin (2*t+1)) (ZMod ell)))
      (cauchy (modelLow ell (2*t+1))
        (fun i : Fin m => ((ell-r-2*m+2*i.val+1 : ℕ) : ZMod ell)))
      (cauchy (modelLow ell (2*t+1))
        (fun i : Fin m => ((ell-r-2*m+2*i.val+2 : ℕ) : ZMod ell))).transpose 0).submatrix
      (Sum.map (Subtype.val : {a // a ∉ d} → Fin (2*t+1)) id)
      (Sum.map (Subtype.val : {a // a ∉ d} → Fin (2*t+1)) id)).det ≠ 0) :
    ((borderedN ((p6Data3 hl ht).h+xb/(p6Data3 hl ht).κ)
      (minorGram hl ht r m) (WX ell (2*t+1) (after r m)) (WY ell (2*t+1) (after r m))).submatrix
      (Sum.map (Subtype.val : {a // a ∉ d} → Fin (2*t+1)) id)
      (Sum.map (Subtype.val : {a // a ∉ d} → Fin (2*t+1)) id)).det ≠ 0 := by
  let A := {a : Fin (2*t+1) // a ∉ d}
  let c : A → Fin (2*t+1) := Subtype.val
  let M := cauchyGram (modelLow ell (2*t+1)) (highBand ell (ell-r-2*m)) (bandSign (3*t+1)) -
    (cc ell t-36*xb) • (1 : Matrix (Fin (2*t+1)) (Fin (2*t+1)) (ZMod ell))
  let X := cauchy (modelLow ell (2*t+1))
    (fun i : Fin m => ((ell-r-2*m+2*i.val+2 : ℕ) : ZMod ell))
  let Y := cauchy (modelLow ell (2*t+1))
    (fun i : Fin m => ((ell-r-2*m+2*i.val+1 : ℕ) : ZMod ell))
  have hm : (fromBlocks (M.submatrix c c) (Y.submatrix c id)
      (X.submatrix c id).transpose (0 : Matrix (Fin m) (Fin m) (ZMod ell))).det ≠ 0 := by
    convert hmodel using 1
    congr 1
    ext (a|i) (b|j) <;> rfl
  have hs := CatalanCore.Linalg.PrincipalDeletion.bordered_smul_ne_zero
    (M.submatrix c c) (X.submatrix c id) (Y.submatrix c id) (-1/2 : ZMod ell)
    (div_ne_zero (neg_ne_zero.mpr one_ne_zero) (two_ne hl ht)) hm
  let e : (A ⊕ Fin m) ≃ (A ⊕ Fin (after r m).k) :=
    Equiv.sumCongr (Equiv.refl A) (reverseBorder r m)
  rw [← Matrix.det_submatrix_equiv_self e]
  convert hs using 1
  congr 1
  have hg : r+2*m+(ell-r-2*m)=ell := by omega
  have hM := minorPencil_reflect hl ht r m hKr htop xb
  have hX := WX_after_rev (K := 2*t+1) hg
  have hY := WY_after_rev (K := 2*t+1) hg
  ext (a|i) (b|j)
  · exact congrFun (congrFun hM (c a)) (c b)
  · exact congrFun (congrFun hY (c a)) j
  · exact congrFun (congrFun hX (c b)) i
  · rfl

#print axioms physical_low_rescue
end CatalanFrames.P6Hybrid
