module
public import CatalanCore.Arith.Hybrid.FiniteFieldCorank.BandsGeometry
public import CatalanCore.Linalg.CauchyPolynomial
@[expose] public section
open Finset Polynomial Matrix
namespace CatalanCore.Linalg.CauchyPolynomial
open CatalanCore.Arith.Hybrid.FiniteFieldCorank

lemma sum_Ico_reflect_nat {M : Type*} [AddCommMonoid M]
    (ell A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) (hB : B ≤ ell) (f : ℕ → M) :
    (∑ n ∈ Ico A B, f (ell-n)) = ∑ y ∈ Ico (ell-B+1) (ell-A+1), f y := by
  apply Finset.sum_bij (fun n _ => ell-n)
  · intro n hn
    have hn' := mem_Ico.mp hn
    apply mem_Ico.mpr
    omega
  · intro n hn n' hn' he
    have h1 := mem_Ico.mp hn
    have h2 := mem_Ico.mp hn'
    omega
  · intro y hy
    have h := mem_Ico.mp hy
    refine ⟨ell-y, mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    omega
  · intro n hn
    rfl

lemma sum_zband_nat {ell lo hi : ℕ} [NeZero ell] {M : Type*} [AddCommMonoid M]
    (hh : hi ≤ ell) (f : ZMod ell → M) :
    (∑ y ∈ zband ell lo hi, f y) = ∑ n ∈ Ico lo hi, f (n : ZMod ell) := by
  rw [zband, Finset.sum_image]
  intro a ha b hb hab
  have h1 := (mem_Ico.mp ha).2
  have h2 := (mem_Ico.mp hb).2
  have he := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt (show a < ell by omega),
    ZMod.val_natCast_of_lt (show b < ell by omega)] using he

lemma physical_gram_reflect (ell K A B : ℕ) [Fact ell.Prime]
    (hA : 1 ≤ A) (hAB : A ≤ B) (hB : B ≤ ell) :
    (fun a b : Fin K => ∑ n ∈ Ico A B,
      (1 / ((a.val : ZMod ell) - (n : ZMod ell))) *
      (1 / ((b.val : ZMod ell) - (n : ZMod ell)))) =
    cauchyGram (fun a : Fin K => -(a.val : ZMod ell))
      (zband ell (ell-B+1) (ell-A+1)) (fun _ => 1) := by
  ext a b
  simp only [cauchyGram, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, one_mul]
  rw [sum_zband_nat (by omega)]
  rw [← sum_Ico_reflect_nat ell A B hA hAB hB]
  apply Finset.sum_congr rfl
  intro n hn
  have hne : n ≤ ell := by have := (mem_Ico.mp hn).2; omega
  have he : ((ell-n : ℕ) : ZMod ell) = -(n : ZMod ell) := by
    rw [Nat.cast_sub hne, ZMod.natCast_self, zero_sub]
  simp only [he, sub_neg_eq_add]
  congr 2 <;> ring




lemma cauchyGram_signed_split {ell K S g : ℕ} [Fact ell.Prime]
    (low : Fin K → ZMod ell) (hS : 1 ≤ S) (hSg : S ≤ g+1) (hg : g+1 ≤ ell) :
    cauchyGram low (highBand ell g) (bandSign S) =
      cauchyGram low (zband ell 1 S) (fun _ => 1) +
      (-2 : ZMod ell) • cauchyGram low (zband ell S (g+1)) (fun _ => 1) := by
  have hu : highBand ell g = zband ell 1 S ∪ zband ell S (g+1) := by
    ext x
    simp only [highBand, mem_union, mem_zband_iff hg, mem_zband_iff (show S ≤ ell by omega)]
    omega
  have hd : Disjoint (zband ell 1 S) (zband ell S (g+1)) :=
    zband_disjoint (by omega) hg le_rfl
  ext a b
  simp only [cauchyGram, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, Matrix.add_apply, one_mul]
  rw [hu, Finset.sum_union hd, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro x hx
    have hv := (mem_zband_iff (show S ≤ ell by omega) x).mp hx
    simp [bandSign, hv.2]
  · apply Finset.sum_congr rfl
    intro x hx
    have hv := (mem_zband_iff hg x).mp hx
    rw [bandSign, if_neg (by omega)]

end CatalanCore.Linalg.CauchyPolynomial
