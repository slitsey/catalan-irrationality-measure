module
public import CatalanFrames.HybGen.NumerologyAny
public import CatalanCore.Arith.Hybrid.SingLev
public import CatalanFrames.Fifths.Instance
public import CatalanFrames.Fifths.RationalData
public import CatalanFrames.Fifths.RootArithmetic
public import CatalanFrames.HybGen.TropGood
@[expose] public section
open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.HybGen
namespace CatalanFrames.Fifths
variable {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u)
lemma fifths_arithmetic : ArithmeticInfo (fifthsInst T) 5 2 where
  L_eq := rfl
  Ebd_le := fifths_Ebd_cubic T
  cOf_le := fifths_cOf_le T
lemma fifths_kq_lower {p : ℕ} (hp : p.Prime) (h7 : 7≤p) :
    p+1≤5*(fifthsInst T).cd.kq p := by
  obtain ⟨hq,hb⟩ := fifths_good T hp h7
  obtain ⟨hq5,hu5⟩ := good_primePower_inputs hq hb
  have hs := firstRoot_spec T.hu0 T.hu1 hq5 hu5
  have hmul : p≤classIndex u p*p := by
    simpa using Nat.mul_le_mul_right p hs.2.2.2.1
  have hu0 := T.hu0
  change p+1≤5*firstRoot u p
  omega
/-- The tropical weight is exactly zero beyond7r, not merely bounded by an additive6. -/
lemma fifths_tail {r m p : ℕ} (hp : p.Prime) (h7 : 7≤p) (hr : 400≤r)
    (hm1 : r≤8*m) (hm2 : 8*m≤r+9) (hcut : 7*r<p) :
    WGm (fifthsInst T) r m p=0 := by
  have hk := fifths_kq_lower T hp h7
  have h6 := XGm_D6_good (fifths_levels T) r m p hp h7 (by omega) (by omega)
  have hz : XGm (fifthsInst T) r m p=0 := by omega
  simp [WGm,hz]
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.fifths_tail
