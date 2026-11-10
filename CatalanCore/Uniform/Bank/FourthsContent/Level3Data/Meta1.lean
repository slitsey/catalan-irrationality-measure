module

public import CatalanCore.Uniform.Bank.FourthsContent.Level3Data.Basic

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: complete full metadata qualification322.269s/9.625GiB; no branch proofs hidden here.
set_option profiler true in
-- kcost: complete full metadata qualification322.269s/9.625GiB; no branch proofs hidden here.
theorem pcParams1 : kcheckParams (pcBank 1) = true := by decide +kernel
set_option profiler true in
-- kcost: complete full metadata qualification322.269s/9.625GiB; no branch proofs hidden here.
theorem pcClasses1 : kclassOK (pcBank 1) = true := by decide +kernel
#print axioms pcParams1
#print axioms pcClasses1

set_option profiler true in
-- kcost: complete full metadata qualification322.269s/9.625GiB; no branch proofs hidden here.
theorem pcTemplate1Head1 : ktmplHead (pcBank 1) 1 (pcTmpl1.toK 10 22 bankHead.cF) = true := by decide +kernel
#print axioms pcTemplate1Head1

set_option profiler true in
-- kcost: complete full metadata qualification322.269s/9.625GiB; no branch proofs hidden here.
theorem pcTemplate3Head1 : ktmplHead (pcBank 1) 3 (pcTmpl3.toK 10 22 bankHead.cF) = true := by decide +kernel
#print axioms pcTemplate3Head1

end CatalanCore.Uniform.Bank.FourthsContent.Level3Auto
