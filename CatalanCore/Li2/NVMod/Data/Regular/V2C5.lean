module
public import CatalanCore.Li2.NVMod.Data.Families.V2C5
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialEndpointSources
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false
open Polynomial Finset
namespace CatalanCore.Li2.NVMod.RegularFamily.V2C5
open CatalanCore.Li2.NVMod CatalanCore.Li2.NVMod.DataSupport
open CatalanCore.Li2.NVMod.FamilySource.V2C5
noncomputable section
def regularNumerators : List ℤ := raw_ints% []
def regularDenominators : List ℤ := raw_ints% []
def regularValueAt (e : ℕ) : ℚ := (regularNumerators.getD e 0:ℚ)/(regularDenominators.getD e 1:ℚ)
theorem regular_prefix (e : ℕ) (he : e<0) : regularValueAt e=regularMomentWith indices rho e := by
  omega
def regularValue (e : ℕ) : ℚ := if e<0 then regularValueAt e else regularMomentWith indices rho e
theorem regular_source (size e : ℕ) : regularValue e=regularMoment (key size) e := by
  have h:=regularMomentWith_spec (key size) indices rho indices_nodup
    ((indices_set size).trans (poles_eq_poleSet _)) (rho_source size) e
  simpa only [regularValue,Nat.not_lt_zero,ite_false] using h
theorem h0_key (size : ℕ) : h0 (key size)=(-1) := by
  rw [h0_formula]
  rfl
#print axioms regular_source
end
end CatalanCore.Li2.NVMod.RegularFamily.V2C5
