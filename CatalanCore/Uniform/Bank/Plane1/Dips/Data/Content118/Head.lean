module
public import CatalanCore.Uniform.Bank.Plane1.ContentClosed
public import CatalanCore.Uniform.Content.BankShared.KTerm.KnownZero
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
def rq (xs : List ℤ) : ℚ := (xs.getD 0 0 : ℚ)/(xs.getD 1 1 : ℚ)
def headCat : List KBranch := planeTrop ++ [knownZeroBranch false,knownZeroBranch true] ++ [kbrPre 0 0 [0,0], kbrPre 0 0 [0,1], kbrPre 0 0 [0,2], kbrPre 0 0 [1,0], kbrPre 0 0 [1,1], kbrPre 0 0 [1,2], kbrPre 0 0 [2,0], kbrPre 0 0 [2,1], kbrPre 0 0 [2,2], kbrPre 0 1 [0,0], kbrPre 0 1 [0,1], kbrPre 0 1 [0,2], kbrPre 0 1 [1,0], kbrPre 0 1 [1,1], kbrPre 0 1 [1,2], kbrPre 0 1 [2,0], kbrPre 0 1 [2,1], kbrPre 0 1 [2,2]]
def header (ρ a : ℕ) : KBankDataC where
  Q := 6
  M := 6
  α := 1/8
  a := a
  shifts := [⟨3,ρ,1⟩,⟨2,1,1⟩]
  depth := 64
  cF := 23
  Pbad := 6
  α0 := 9/4
  τ := 9
  Λ := (rq (raw_ints% [3074826950896963023007953057179983581846892470200980473294476538304590872571859764024513607148603409522213891098567970933460551644789478005789060697209386378477523645663782184607643839454129805727520496043714272258360038402104432663862617319947940767602476120625241934361045232682723164494873403259152522903375446113068047453236734616888171902462298108061530778091167787022597094171716977427,900647672456211245792270223900965796312445512761494171738432407081820629708410582173557053056984197264666868129987692452493305500961575151550631579426814277664860719847258108195774147381115705317381085352387665425972844630950249400204583220673687177847771208167751101093908268078639224667224262501446806208581051373431244927762317371185718367443228674867777996734738660657214158142955520000]))
  α0b := 9/4
  t0 := 1/68
  Rt := 2
  kcat := headCat
  tmpls := []

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118

#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.header
