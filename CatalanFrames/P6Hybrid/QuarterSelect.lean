module
public import CatalanFrames.P6Hybrid.QuarterContent
public import CatalanFrames.P6Hybrid.CharZeroNV
public import CatalanFrames.P6Hybrid.WindowSquare
@[expose] public section
open CatalanCore CatalanCore.Rect CatalanFrames.P6
namespace CatalanFrames.P6Hybrid.Quarter

/-- Characteristic-zero selection supplies a full unit-width pin window at the
quarter border, where the older finite-field selector's window collapses. -/
theorem hasNVPin :
    HasNVPinC (commonMinorFam p6Frame Adm 1) P6Cls1 P6BadSquare 1 2 :=
  CharZeroNV.commonMinor_hasNVPinC Adm (fun r _ => adm_exists r)
    P6Cls1 P6BadSquare 1 2

end CatalanFrames.P6Hybrid.Quarter
#print axioms CatalanFrames.P6Hybrid.Quarter.hasNVPin
