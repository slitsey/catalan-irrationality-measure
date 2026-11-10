module

public import CatalanCore.Uniform.Bank.FifthsContent.Level3Data.Basic

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000
namespace CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

-- kcost: complete full metadata qualification322.269s/9.625GiB; no branch proofs hidden here.
set_option profiler true in
-- kcost: complete full metadata qualification322.269s/9.625GiB; no branch proofs hidden here.
theorem pcParams2 : kcheckParams (pcBank 2) = true := by decide +kernel
set_option profiler true in
-- kcost: complete full metadata qualification322.269s/9.625GiB; no branch proofs hidden here.
theorem pcClasses2 : kclassOK (pcBank 2) = true := by decide +kernel
#print axioms pcParams2
#print axioms pcClasses2

set_option profiler true in
-- kcost: complete full metadata qualification322.269s/9.625GiB; no branch proofs hidden here.
theorem pcTemplate1Head2 : ktmplHead (pcBank 2) 1 (pcTmpl1.toK 9 20 bankHead.cF) = true := by decide +kernel
#print axioms pcTemplate1Head2

set_option profiler true in
-- kcost: complete full metadata qualification322.269s/9.625GiB; no branch proofs hidden here.
theorem pcTemplate2Head2 : ktmplHead (pcBank 2) 2 (pcTmpl2.toK 9 20 bankHead.cF) = true := by decide +kernel
#print axioms pcTemplate2Head2

set_option profiler true in
-- kcost: complete full metadata qualification322.269s/9.625GiB; no branch proofs hidden here.
theorem pcTemplate3Head2 : ktmplHead (pcBank 2) 3 (pcTmpl3.toK 9 20 bankHead.cF) = true := by decide +kernel
#print axioms pcTemplate3Head2

set_option profiler true in
-- kcost: complete full metadata qualification322.269s/9.625GiB; no branch proofs hidden here.
theorem pcTemplate4Head2 : ktmplHead (pcBank 2) 4 (pcTmpl4.toK 9 20 bankHead.cF) = true := by decide +kernel
#print axioms pcTemplate4Head2

end CatalanCore.Uniform.Bank.FifthsContent.Level3Auto
