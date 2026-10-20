module
public import CatalanFrames.P6Hybrid.MinorNV
public import CatalanCore.Linalg.CauchyPolynomial
@[expose] public section
open Matrix CatalanCore CatalanCore.Rect
open CatalanFrames.LambdaHybrid.NV CatalanCore.Linalg.CauchyPolynomial
namespace CatalanFrames.P6Hybrid
variable {ell K r m g : ℕ} [Fact ell.Prime]

def reverseBorder (r m : ℕ) : Fin m ≃ Fin (after r m).k :=
  Fin.revPerm.trans (finCongr (after_k r m)).symm

@[simp] lemma reverseBorder_val (r m : ℕ) (i : Fin m) :
    (reverseBorder r m i).val = m - (i.val + 1) := rfl

lemma WX_after_rev (hg : r + 2*m + g = ell) :
    (WX ell K (after r m)).submatrix id (reverseBorder r m) =
      cauchy (fun a : Fin K => -(a.val : ZMod ell))
        (fun i : Fin m => ((g + 2*i.val + 2 : ℕ) : ZMod ell)) := by
  ext a i
  simp only [WX, Wnode, Matrix.submatrix_apply, Matrix.of_apply, id, after_xs,
    reverseBorder_val, cauchy]
  have hn : (r + 2*(m-(i.val+1))) + (g+2*i.val+2) = ell := by have := i.2; omega
  have hc : ((r + 2*(m-(i.val+1)) : ℕ) : ZMod ell) +
      ((g+2*i.val+2 : ℕ) : ZMod ell) = 0 := by
    rw [← Nat.cast_add, hn]
    exact ZMod.natCast_self ell
  push_cast at hc
  congr 1
  push_cast
  linear_combination -hc

lemma WY_after_rev (hg : r + 2*m + g = ell) :
    (WY ell K (after r m)).submatrix id (reverseBorder r m) =
      cauchy (fun a : Fin K => -(a.val : ZMod ell))
        (fun i : Fin m => ((g + 2*i.val + 1 : ℕ) : ZMod ell)) := by
  ext a i
  simp only [WY, Wnode, Matrix.submatrix_apply, Matrix.of_apply, id, after_ys,
    reverseBorder_val, cauchy]
  have hn : (r + 2*(m-(i.val+1))+1) + (g+2*i.val+1) = ell := by have := i.2; omega
  have hc : ((r + 2*(m-(i.val+1))+1 : ℕ) : ZMod ell) +
      ((g+2*i.val+1 : ℕ) : ZMod ell) = 0 := by
    rw [← Nat.cast_add, hn]
    exact ZMod.natCast_self ell
  push_cast at hc
  congr 1
  push_cast
  linear_combination -hc
lemma reflected_gram_ne (hg : r + 2*m + g = ell)
    (hGram : ((WX ell K (after r m)).transpose * WY ell K (after r m)).det ≠ 0) :
    ((cauchy (fun a : Fin K => -(a.val : ZMod ell))
      (fun i : Fin m => ((g+2*i.val+2 : ℕ) : ZMod ell))).transpose *
      cauchy (fun a : Fin K => -(a.val : ZMod ell))
      (fun i : Fin m => ((g+2*i.val+1 : ℕ) : ZMod ell))).det ≠ 0 := by
  rw [← WX_after_rev hg, ← WY_after_rev hg]
  have he : ((WX ell K (after r m)).submatrix id (reverseBorder r m)).transpose *
      (WY ell K (after r m)).submatrix id (reverseBorder r m) =
      ((WX ell K (after r m)).transpose * WY ell K (after r m)).submatrix
        (reverseBorder r m) (reverseBorder r m) := by
    ext i j
    simp [Matrix.mul_apply]
  rw [he, Matrix.det_submatrix_equiv_self]
  exact hGram
end CatalanFrames.P6Hybrid
#print axioms CatalanFrames.P6Hybrid.WX_after_rev
