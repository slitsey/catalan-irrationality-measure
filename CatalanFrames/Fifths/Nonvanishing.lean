module
public import CatalanFrames.Fifths.Admissible
public import CatalanFrames.Fifths.Window
@[expose] public section
open CatalanCore CatalanCore.Rect
namespace CatalanFrames.Fifths
theorem fifths1_NV : HasNVPinC (commonMinorFam fifths1 FifthsAdm 1)
    (Thirds.ClsIn 30 unitClasses) (Thirds.PowBad 2) 1 2 :=
  fifths1_hasNVPinC FifthsAdm adm_exists _ _ _ _
theorem fifths2_NV : HasNVPinC (commonMinorFam fifths2 FifthsAdm 1)
    (Thirds.ClsIn 30 unitClasses) (Thirds.PowBad 2) 1 2 :=
  fifths2_hasNVPinC FifthsAdm adm_exists _ _ _ _
theorem fifths3_NV : HasNVPinC (commonMinorFam fifths3 FifthsAdm 1)
    (Thirds.ClsIn 30 unitClasses) (Thirds.PowBad 2) 1 2 :=
  fifths3_hasNVPinC FifthsAdm adm_exists _ _ _ _
theorem fifths4_NV : HasNVPinC (commonMinorFam fifths4 FifthsAdm 1)
    (Thirds.ClsIn 30 unitClasses) (Thirds.PowBad 2) 1 2 :=
  fifths4_hasNVPinC FifthsAdm adm_exists _ _ _ _
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.fifths1_NV
#print axioms CatalanFrames.Fifths.fifths2_NV
#print axioms CatalanFrames.Fifths.fifths3_NV
#print axioms CatalanFrames.Fifths.fifths4_NV
