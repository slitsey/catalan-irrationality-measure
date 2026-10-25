module

public import CatalanFrames.Thirds.ContourGeneric
public import CatalanFrames.Thirds.CharZero

@[expose] public section

/-! Fifths instances. PREPARED, UNBUILT. All analytic engines are reused. -/
open CatalanCore
namespace CatalanFrames.Fifths

def fifths1 : Frame :=
  CatalanFrames.Thirds.thirdsFrame (1 / 5) 25 (3/5) (1 / 4) 1
    (by norm_num) (by norm_num) (by norm_num)

theorem fifths1_decayOKs' (sl : Real) (hsl : 1 <= sl) : fifths1.DecayOKs' sl := by
  apply CatalanFrames.Thirds.thirds_decayOKs' _ _ _ _ _ _ _ _
    (by norm_num) (by norm_num) 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) sl hsl
  · push_cast
    nlinarith
  · norm_num
  · norm_num
  · norm_num

theorem fifths1_hasNVPinC
    (Adm : Nat -> Nat -> Prop) (hAdm : forall r, 1 <= r -> exists m, Adm r m)
    (Cls : Nat -> Prop) (Bad : Nat -> Nat -> Prop) (alpha beta : Real) :
    HasNVPinC (CatalanCore.Rect.commonMinorFam fifths1 Adm 1) Cls Bad alpha beta := by
  exact CatalanFrames.Thirds.thirds_hasNVPinC _ _ _ _ _ _ _ _
    Adm hAdm Cls Bad alpha beta

def fifths2 : Frame :=
  CatalanFrames.Thirds.thirdsFrame (2 / 5) 25 (7/10) (1 / 4) 1
    (by norm_num) (by norm_num) (by norm_num)

theorem fifths2_decayOKs' (sl : Real) (hsl : 1 <= sl) : fifths2.DecayOKs' sl := by
  apply CatalanFrames.Thirds.thirds_decayOKs' _ _ _ _ _ _ _ _
    (by norm_num) (by norm_num) 1 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) sl hsl
  · push_cast
    nlinarith
  · norm_num
  · norm_num
  · norm_num

theorem fifths2_hasNVPinC
    (Adm : Nat -> Nat -> Prop) (hAdm : forall r, 1 <= r -> exists m, Adm r m)
    (Cls : Nat -> Prop) (Bad : Nat -> Nat -> Prop) (alpha beta : Real) :
    HasNVPinC (CatalanCore.Rect.commonMinorFam fifths2 Adm 1) Cls Bad alpha beta := by
  exact CatalanFrames.Thirds.thirds_hasNVPinC _ _ _ _ _ _ _ _
    Adm hAdm Cls Bad alpha beta

def fifths3 : Frame :=
  CatalanFrames.Thirds.thirdsFrame (3 / 5) 25 (3/10) (1 / 4) 0
    (by norm_num) (by norm_num) (by norm_num)

theorem fifths3_decayOKs' (sl : Real) (hsl : 1 <= sl) : fifths3.DecayOKs' sl := by
  apply CatalanFrames.Thirds.thirds_decayOKs' _ _ _ _ _ _ _ _
    (by norm_num) (by norm_num) 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) sl hsl
  · push_cast
    nlinarith
  · norm_num
  · norm_num
  · norm_num

theorem fifths3_hasNVPinC
    (Adm : Nat -> Nat -> Prop) (hAdm : forall r, 1 <= r -> exists m, Adm r m)
    (Cls : Nat -> Prop) (Bad : Nat -> Nat -> Prop) (alpha beta : Real) :
    HasNVPinC (CatalanCore.Rect.commonMinorFam fifths3 Adm 1) Cls Bad alpha beta := by
  exact CatalanFrames.Thirds.thirds_hasNVPinC _ _ _ _ _ _ _ _
    Adm hAdm Cls Bad alpha beta

def fifths4 : Frame :=
  CatalanFrames.Thirds.thirdsFrame (4 / 5) 25 (2/5) (1 / 4) 0
    (by norm_num) (by norm_num) (by norm_num)

theorem fifths4_decayOKs' (sl : Real) (hsl : 1 <= sl) : fifths4.DecayOKs' sl := by
  apply CatalanFrames.Thirds.thirds_decayOKs' _ _ _ _ _ _ _ _
    (by norm_num) (by norm_num) 0 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) sl hsl
  · push_cast
    nlinarith
  · norm_num
  · norm_num
  · norm_num

theorem fifths4_hasNVPinC
    (Adm : Nat -> Nat -> Prop) (hAdm : forall r, 1 <= r -> exists m, Adm r m)
    (Cls : Nat -> Prop) (Bad : Nat -> Nat -> Prop) (alpha beta : Real) :
    HasNVPinC (CatalanCore.Rect.commonMinorFam fifths4 Adm 1) Cls Bad alpha beta := by
  exact CatalanFrames.Thirds.thirds_hasNVPinC _ _ _ _ _ _ _ _
    Adm hAdm Cls Bad alpha beta

end CatalanFrames.Fifths

#print axioms CatalanFrames.Fifths.fifths1_decayOKs'
#print axioms CatalanFrames.Fifths.fifths1_hasNVPinC

#print axioms CatalanFrames.Fifths.fifths2_decayOKs'
#print axioms CatalanFrames.Fifths.fifths2_hasNVPinC

#print axioms CatalanFrames.Fifths.fifths3_decayOKs'
#print axioms CatalanFrames.Fifths.fifths3_hasNVPinC

#print axioms CatalanFrames.Fifths.fifths4_decayOKs'
#print axioms CatalanFrames.Fifths.fifths4_hasNVPinC
