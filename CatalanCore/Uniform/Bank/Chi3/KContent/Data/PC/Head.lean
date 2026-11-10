module
public import CatalanCore.Uniform.Bank.Chi3.KContent.Data.Head
public import CatalanCore.Uniform.Content.BankShared.KTerm.Periodic
public import CatalanCore.Uniform.Content.BankShared.KTerm.PeriodTranslation
public import CatalanMeasure.CellCert.RawInts
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Chi3.KContent
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
def pcRat (xs : List ℤ) : ℚ := (xs.getD 0 0 : ℚ)/(xs.getD 1 1 : ℚ)
def pcBaseCat : List KBranch := [kbD1xB, kbrPre 1 0 [0,0], kbrPre 1 0 [0,1], kbrPre 1 0 [1,0], kbrPre 1 0 [1,1], kbrPre 1 1 [1,1], kbrPre 1 1 [1,2], kbrPre 1 1 [2,1], kbrPre 1 1 [2,2]]

end CatalanCore.Uniform.Bank.Chi3.KContent

#print axioms CatalanCore.Uniform.Bank.Chi3.KContent.pcBaseCat
