import CatalanCore.Uniform.Content.BankShared.AltCrude
import CatalanCore.Uniform.Bank.Lambda.Layers
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.BankShared

/-- Unconditional clearing fallback on the actual even-scale Lambda family. -/
noncomputable def lambdaCrudePrice (Fr : Frame) (depth : ℕ) :
    CertifiedPrice (FamE Fr depth) where
  price := fun i p => Ecrude (cFr Fr) i.1 p
  gle := by
    intro i hi p hp
    exact altGeom_gle_Ecrude (1 / 5) one_fifth_pos (by norm_num) Fr depth i hi.2 p

#print axioms lambdaCrudePrice
end CatalanCore.Uniform.Bank.Lambda
