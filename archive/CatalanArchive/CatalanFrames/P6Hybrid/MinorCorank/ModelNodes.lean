module
public import CatalanArchive.CatalanCore.Arith.Hybrid.FiniteFieldCorank.BandsNodes
@[expose] public section
open Finset
open CatalanCore.Arith.Hybrid.FiniteFieldCorank
namespace CatalanFrames.P6Hybrid
variable {ell K m S g : ℕ} [Fact ell.Prime]

theorem model_border_injective (H : BandGeometry ell K m S g) (c : ℕ) (hc : 1≤c ∧ c≤2) :
    Function.Injective (fun a : Fin m => ((g+2*a.val+c : ℕ) : ZMod ell)) := by
  intro a b hab
  apply Fin.ext
  have hk:=H.hK; have hr:=H.room
  have he := congrArg ZMod.val hab
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at he
  omega

theorem model_border_mem (H : BandGeometry ell K m S g) (c : ℕ) (hc : 1≤c ∧ c≤2) (a : Fin m) :
    ((g+2*a.val+c : ℕ) : ZMod ell) ∈ borderBand ell g m := by
  have hk:=H.hK; have hr:=H.room
  rw [borderBand, mem_zband_iff (by omega), ZMod.val_natCast_of_lt (by omega)]
  omega

theorem model_border_ne_low (H : BandGeometry ell K m S g) (c : ℕ) (hc : 1≤c ∧ c≤2)
    (i : Fin m) (a : Fin K) : ((g+2*i.val+c : ℕ) : ZMod ell) ≠ -(a.val : ZMod ell) := by
  intro he
  have hl : -(a.val : ZMod ell) ∈ lowBand ell K := by
    rw [lowBand_eq_image_neg H]
    exact mem_image_of_mem _ (mem_univ a)
  exact disjoint_left.1 (low_border_disjoint H) (he ▸ hl) (model_border_mem H c hc i)
end CatalanFrames.P6Hybrid
