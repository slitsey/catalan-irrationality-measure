module
public import CatalanCore.Arith.Hybrid.FiniteFieldCorank.BandPencil
public import CatalanCore.Arith.Hybrid.FiniteFieldCorank.BandsNodes
public import CatalanCore.Arith.Hybrid.FiniteFieldCorank.MomentComparison
@[expose] public section
open Polynomial Matrix Module Finset
open CatalanCore.Arith.Hybrid.FiniteFieldCorank CatalanCore.Linalg.CauchyPolynomial
namespace CatalanFrames.P6Hybrid
variable {ell K m S g : ℕ} [Fact ell.Prime]

noncomputable def modelBX (ell g m : ℕ) [Fact ell.Prime] : (ZMod ell)[X] :=
  denom (fun a : Fin m => ((g+2*a.val+2 : ℕ) : ZMod ell))
noncomputable def modelBY (ell g m : ℕ) [Fact ell.Prime] : (ZMod ell)[X] :=
  denom (fun a : Fin m => ((g+2*a.val+1 : ℕ) : ZMod ell))
def modelLow (ell K : ℕ) (a : Fin K) : ZMod ell := -(a.val : ZMod ell)

noncomputable def modelCompressed (ell K m S g : ℕ) [Fact ell.Prime] (z : ZMod ell) :=
  (residueBasis (modelLow ell K) (modelBY ell g m) (K-m)).transpose *
    (cauchyGram (modelLow ell K) (highBand ell g) (bandSign S) - z • (1 : Matrix (Fin K) (Fin K) (ZMod ell))) *
    residueBasis (modelLow ell K) (modelBX ell g m) (K-m)

theorem modelCompressed_eq_bandPencil (H : BandGeometry ell K m S g)
    (hn : 3 ≤ K-m) (hng : K-m ≤ g) (h2 : (2 : ZMod ell) ≠ 0) (z : ZMod ell) :
    modelCompressed ell K m S g z = bandPencil H hn hng h2 z := by
  have hm : m≤K := by omega
  have hBX : (modelBX ell g m).natDegree + (K-m) ≤ K := by
    rw [modelBX, denom_natDegree]; omega
  have hBY : (modelBY ell g m).natDegree + (K-m) ≤ K := by
    rw [modelBY, denom_natDegree]; omega
  have hs : ∀ y∈highBand ell g, ∀ a : Fin K, y≠modelLow ell K a := by
    intro y hy a he
    have hl : modelLow ell K a ∈ lowBand ell K := by
      rw [lowBand_eq_image_neg H]
      exact mem_image_of_mem _ (mem_univ a)
    exact disjoint_left.1 (low_high_disjoint H) (he ▸ hl) hy
  unfold modelCompressed
  rw [compressed_eq_moment (modelLow ell K) (show Function.Injective (modelLow ell K) from negNatNodes_injective H) (modelBX ell g m) (modelBY ell g m) hBX hBY (highBand ell g) (bandSign S) hs z]
  have hD := lowBand_rootProduct_eq_denom H
  have hR := borderBand_rootProduct_eq_interleaved H
  have hlowset : univ.image (modelLow ell K) = lowBand ell K := (lowBand_eq_image_neg H).symm
  rw [hlowset]
  unfold bandPencil
  congr 1
  funext y
  change (if y ∈ lowBand ell K then -z*(modelBX ell g m * modelBY ell g m).eval y / ((denom (fun a : Fin K => -(a.val : ZMod ell))).derivative.eval y)^2
    else bandSign S y*(modelBX ell g m * modelBY ell g m).eval y / (denom (fun a : Fin K => -(a.val : ZMod ell))).eval y^2) =
    (if y ∈ lowBand ell K then -z*(rootProduct (borderBand ell g m)).eval y / ((rootProduct (lowBand ell K)).derivative.eval y)^2
    else bandSign S y*(rootProduct (borderBand ell g m)).eval y / (rootProduct (lowBand ell K)).eval y^2)
  rw [hD, hR]
  rfl

theorem model_compressed_corank (H : BandGeometry ell K m S g)
    (hn : 3 ≤ K-m) (hng : K-m ≤ g) (h2 : (2 : ZMod ell) ≠ 0) (z : ZMod ell) :
    finrank (ZMod ell) (LinearMap.ker (modelCompressed ell K m S g z).mulVecLin) ≤ 3 := by
  rw [modelCompressed_eq_bandPencil H hn hng h2 z]
  exact bandPencil_corank H hn hng h2 z

theorem model_compressed_symmetric (H : BandGeometry ell K m S g)
    (hn : 3 ≤ K-m) (hng : K-m ≤ g) (h2 : (2 : ZMod ell) ≠ 0) (z : ZMod ell) :
    (modelCompressed ell K m S g z).transpose = modelCompressed ell K m S g z := by
  rw [modelCompressed_eq_bandPencil H hn hng h2 z]
  ext i j
  simp only [bandPencil, momentMatrix, Matrix.transpose_apply, Nat.add_comm]

#print axioms model_compressed_corank
end CatalanFrames.P6Hybrid
