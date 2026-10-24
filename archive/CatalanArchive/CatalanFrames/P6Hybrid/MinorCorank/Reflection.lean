module
public import CatalanArchive.CatalanFrames.P6Hybrid.MinorNV
public import CatalanArchive.CatalanCore.Linalg.CauchyPolynomial.Reflection
@[expose] public section
open Finset Matrix Polynomial CatalanCore CatalanCore.Rect CatalanFrames.P6
open CatalanFrames.LambdaHybrid.NV CatalanFrames.P6.NV
open CatalanCore.Linalg.CauchyPolynomial
open CatalanCore.Arith.Hybrid.FiniteFieldCorank
namespace CatalanFrames.P6Hybrid
variable {ell t : ℕ} [Fact ell.Prime]

lemma absentGram_eq_interval (r m : ℕ) :
    Gcols ell (2*t+1) (absentNodes r m t) *
      (Gcols ell (2*t+1) (absentNodes r m t)).transpose =
    (fun a b : Fin (2*t+1) => ∑ n ∈ Ico (r+2*m) (3*t+1),
      Wnode ell (2*t+1) n a * Wnode ell (2*t+1) n b) := by
  ext a b
  simp only [Gcols, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, absentNodes]
  rw [Finset.sum_Ico_eq_sum_range]
  exact (Finset.sum_range (fun i => Wnode ell (2*t+1) (r+2*m+i) a *
    Wnode ell (2*t+1) (r+2*m+i) b)).symm

lemma absentGram_reflect (hl : ell=6*t+1) (ht : 1 ≤ t) (r m : ℕ)
    (hKr : 2*t+1 ≤ r) (htop : r+2*m ≤ 3*t) :
    Gcols ell (2*t+1) (absentNodes r m t) *
      (Gcols ell (2*t+1) (absentNodes r m t)).transpose =
    cauchyGram (fun a : Fin (2*t+1) => -(a.val : ZMod ell))
      (zband ell (3*t+1) (ell-r-2*m+1)) (fun _ => 1) := by
  rw [absentGram_eq_interval]
  have he := physical_gram_reflect ell (2*t+1) (r+2*m) (3*t+1)
    (by omega) (by omega) (by omega)
  have h1 : ell-(3*t+1)+1=3*t+1 := by omega
  have h2 : ell-(r+2*m)+1=ell-r-2*m+1 := by omega
  ext a b
  simpa only [Wnode, h1, h2] using congrFun (congrFun he a) b

lemma topGram_reflect (hl : ell=6*t+1) (ht : 1 ≤ t) :
    Ttop ell (2*t+1) (3*t+1) =
    cauchyGram (fun a : Fin (2*t+1) => -(a.val : ZMod ell))
      (zband ell 1 (3*t+1)) (fun _ => 1) := by
  have he := physical_gram_reflect ell (2*t+1) (3*t+1) ell
    (by omega) (by omega) le_rfl
  have h1 : ell-(3*t+1)+1=3*t+1 := by omega
  ext a b
  simpa only [Ttop, Wnode, Matrix.of_apply, Nat.sub_self, zero_add, h1] using
    congrFun (congrFun he a) b

lemma minorGram_reflect (hl : ell=6*t+1) (ht : 1 ≤ t) (r m : ℕ)
    (hKr : 2*t+1 ≤ r) (htop : r+2*m ≤ 3*t) :
    minorGram hl ht r m = (-1/2 : ZMod ell) •
      cauchyGram (fun a : Fin (2*t+1) => -(a.val : ZMod ell))
        (highBand ell (ell-r-2*m)) (bandSign (3*t+1)) := by
  have hs : 3*t+1 ≤ ell-r-2*m+1 := by omega
  have hg : ell-r-2*m+1 ≤ ell := by omega
  rw [cauchyGram_signed_split _ (by omega) hs hg]
  unfold minorGram
  rw [absentGram_reflect hl ht r m hKr htop, topGram_reflect hl ht]
  have h2 := two_ne hl ht
  have h18 := eighteen_ne hl ht
  have h36 := n36_ne hl ht
  have hc : (p6Data3 hl ht).τ₀ / (p6Data3 hl ht).κ = (-1/2 : ZMod ell) := by
    change (1/36 : ZMod ell) / (-1/18) = -1/2
    field_simp <;> norm_num
  rw [hc]
  ext a b
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp <;> ring

#print axioms minorGram_reflect



lemma minorPencil_reflect (hl : ell=6*t+1) (ht : 1 ≤ t) (r m : ℕ)
    (hKr : 2*t+1 ≤ r) (htop : r+2*m ≤ 3*t) (xb : ZMod ell) :
    ((p6Data3 hl ht).h + xb / (p6Data3 hl ht).κ) •
        (1 : Matrix (Fin (2*t+1)) (Fin (2*t+1)) (ZMod ell)) + minorGram hl ht r m =
      (-1/2 : ZMod ell) •
        (cauchyGram (fun a : Fin (2*t+1) => -(a.val : ZMod ell))
          (highBand ell (ell-r-2*m)) (bandSign (3*t+1)) -
        (cc ell t - 36*xb) • 1) := by
  rw [minorGram_reflect hl ht r m hKr htop]
  have h2 := two_ne hl ht
  have h18 := eighteen_ne hl ht
  ext a b
  simp only [p6Data3, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  field_simp <;> ring

#print axioms minorPencil_reflect
end CatalanFrames.P6Hybrid
