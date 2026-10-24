module
public import CatalanArchive.CatalanFrames.P6Hybrid.MinorCorank
public import CatalanArchive.CatalanFrames.P6Hybrid.MinorCorank.ModelNodes
public import CatalanArchive.CatalanCore.Linalg.CauchyPolynomial.Deletion
@[expose] public section
open Polynomial Matrix Module Finset
open CatalanCore.Arith.Hybrid.FiniteFieldCorank CatalanCore.Linalg.CauchyPolynomial
namespace CatalanFrames.P6Hybrid
variable {ell K m S g : ℕ} [Fact ell.Prime]

theorem model_low_rescue (H : BandGeometry ell K m S g)
    (hn : 3 ≤ K-m) (hng : K-m ≤ g) (h2 : (2 : ZMod ell) ≠ 0) (z : ZMod ell)
    (hGram : ((cauchy (modelLow ell K) (fun a : Fin m => ((g+2*a.val+2 : ℕ) : ZMod ell))).transpose *
      cauchy (modelLow ell K) (fun a : Fin m => ((g+2*a.val+1 : ℕ) : ZMod ell))).det ≠ 0) :
    ∃ d : Finset (Fin K), d.card≤3 ∧
      ((Matrix.fromBlocks
        (cauchyGram (modelLow ell K) (highBand ell g) (bandSign S) - z • (1 : Matrix (Fin K) (Fin K) (ZMod ell)))
        (cauchy (modelLow ell K) (fun a : Fin m => ((g+2*a.val+1 : ℕ) : ZMod ell)))
        (cauchy (modelLow ell K) (fun a : Fin m => ((g+2*a.val+2 : ℕ) : ZMod ell))).transpose 0).submatrix
          (Sum.map (Subtype.val : {a // a ∉ d} → Fin K) id)
          (Sum.map (Subtype.val : {a // a ∉ d} → Fin K) id)).det ≠ 0 := by
  obtain ⟨d, hd, hdet⟩ := exists_low_minor_ne (modelLow ell K)
    (show Function.Injective (modelLow ell K) from negNatNodes_injective H)
    (fun a : Fin m => ((g+2*a.val+2 : ℕ) : ZMod ell))
    (fun a : Fin m => ((g+2*a.val+1 : ℕ) : ZMod ell))
    (model_border_injective H 2 (by omega)) (model_border_injective H 1 (by omega))
    (model_border_ne_low H 2 (by omega)) (model_border_ne_low H 1 (by omega))
    (by omega : 0<K-m) (by omega : m+(K-m)=K)
    (cauchyGram (modelLow ell K) (highBand ell g) (bandSign S) - z • (1 : Matrix (Fin K) (Fin K) (ZMod ell)))
    hGram (model_compressed_symmetric H hn hng h2 z)
  refine ⟨d, ?_, hdet⟩
  rw [hd]
  exact model_compressed_corank H hn hng h2 z
#print axioms model_low_rescue
end CatalanFrames.P6Hybrid
