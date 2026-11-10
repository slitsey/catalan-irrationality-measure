module

public import CatalanCore.Uniform.Content.BankShared.KTerm.Expr
public import CatalanCore.Uniform.Bank.Plane1.Dips.KnownZero.Value

@[expose] public section
set_option Elab.async false

/-! Geometry-free exact clipped known-zero dual price in KExpr. -/
namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore.Uniform.Bank.Plane1.Dips
open KExpr

def zPoleLo : KExpr := mn (vk 0) (vk 1)
def zPoleHi : KExpr := mx (vk 0) (vk 1)
def zNodeEnd : KExpr := add vr (smul 2 vm)
def zBase : KExpr := add (smul 2 vr) (smul 2 vm)
def zSavings (win : Bool) : KExpr :=
  add (add (add
    (tsub (mn zPoleLo vr) (tsub vr vp))
    (tsub (mn zPoleLo vr) (tsub zNodeEnd vp)))
    (tsub (mn zPoleLo zNodeEnd) (mx (tsub zNodeEnd vp) vr)))
    (if win then tsub (mn vp zNodeEnd) (mx (mx zPoleHi (tsub zNodeEnd vp)) vr) else cst 0)
def knownZeroPrice (win : Bool) : KExpr := tsub zBase (zSavings win)

def knownZeroBranch (win : Bool) : KBranch :=
  ⟨knownZeroPrice win,
    [⟨-1,2,-2,[0,0],0,false⟩,⟨0,1,-2,[0,0],-1,false⟩] ++
      (if win then [⟨0,0,0,[1,-1],-1,false⟩] else []),2⟩

theorem knownZeroPrice_eval (r m p : ℕ) (kv : ℕ → ℕ) (win : Bool)
    (hpodd : p%2=1) (hk : min (kv 0) (kv 1)≤p) :
    (knownZeroPrice win).evalN r p m kv =
      zPrice r m p (knownIntervals r m p (min (kv 0) (kv 1)) (max (kv 0) (kv 1)) win) := by
  have he : (zSavings win).evalN r p m kv =
      zSaving r m p (min (kv 0) (kv 1)) (max (kv 0) (kv 1)) win := by
    cases win <;> rfl
  change (2*r+2*m)-(zSavings win).evalN r p m kv=_
  rw [he]
  have h := zPrice_intervals r m p (min (kv 0) (kv 1)) (max (kv 0) (kv 1)) win hpodd
    ((min_le_left _ _).trans (le_max_left _ _)) hk
  have hsum : ((zPrice r m p (knownIntervals r m p (min (kv 0) (kv 1))
      (max (kv 0) (kv 1)) win)+zSaving r m p (min (kv 0) (kv 1)) (max (kv 0) (kv 1)) win : ℕ):ℚ)=
      ((2*r+2*m:ℕ):ℚ) := by
    push_cast at h ⊢
    linarith
  have hn : zPrice r m p (knownIntervals r m p (min (kv 0) (kv 1))
      (max (kv 0) (kv 1)) win)+zSaving r m p (min (kv 0) (kv 1)) (max (kv 0) (kv 1)) win=2*r+2*m := by
    exact_mod_cast hsum
  omega

end CatalanCore.Uniform.Content.BankShared.KTerm
#print axioms CatalanCore.Uniform.Content.BankShared.KTerm.knownZeroPrice_eval
