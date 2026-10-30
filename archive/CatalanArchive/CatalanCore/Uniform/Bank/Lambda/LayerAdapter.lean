import CatalanCore.Uniform.Bank.Lambda.Layers
import CatalanCore.Uniform.Content.Wire.LP
import CatalanCore.Uniform.Content.Wire.M3D
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Member
  CatalanCore.Uniform.Content.Wire

/-- Use a debit layer only on its proved validity window, with a certified fallback. -/
noncomputable def certifyDebitLayer (Fr : Frame) (depth : ℕ)
    (fallback : CertifiedPrice (FamE Fr depth)) (L : DebitLayer FL Fr depth) :
    CertifiedPrice (FamE Fr depth) := by
  classical
  refine ⟨fun i p => if L.valid i.1 p then L.eff i.1 p else fallback.price i p, ?_⟩
  intro i hi p hp
  split_ifs with h
  · exact (L.gle i hi.1 p h).mono
      (Nat.add_le_add_left (Nat.mul_le_mul_left L.debit (delCount_le FL Fr depth i hi.1)) _)
  · exact fallback.gle i hi p

/-- The standard no-UF layer list. Rank is supplied as an extension; future UF
can be appended to that same extension without altering the core constructors. -/
noncomputable def noUFPrices (Fr : Frame) (depth : ℕ)
    (fallback : CertifiedPrice (FamE Fr depth)) (a b : ℕ → ℕ → ℕ)
    (o : ℕ) (kf jf : ℕ → ℕ → ℕ) (ext : List (DebitLayer FL Fr depth)) :
    List (CertifiedPrice (FamE Fr depth)) :=
  ([m3dLayer FL Fr depth a b, lp1Layer FL Fr depth 4 o kf jf,
    lp2Layer FL Fr depth 4 o kf jf] ++ ext).map (certifyDebitLayer Fr depth fallback)

#print axioms certifyDebitLayer
end CatalanCore.Uniform.Bank.Lambda

