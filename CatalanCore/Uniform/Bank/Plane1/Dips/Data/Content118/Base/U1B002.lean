module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
def cell1_48 : PCell := ⟨(rq (raw_ints% [1,2])),(rq (raw_ints% [4,5])),0,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_48_ok : cell1_48.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_48_ok
def cell1_49 : PCell := ⟨(rq (raw_ints% [4,9])),(rq (raw_ints% [1,2])),0,0,(rq (raw_ints% [-1,2])),(rq (raw_ints% [5,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_49_ok : cell1_49.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_49_ok
def cell1_50 : PCell := ⟨(rq (raw_ints% [2,5])),(rq (raw_ints% [4,9])),0,0,(rq (raw_ints% [1,2])),(rq (raw_ints% [-1,1])),.pre 0 1 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_50_ok : cell1_50.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_50_ok
def cell1_51 : PCell := ⟨(rq (raw_ints% [1,3])),(rq (raw_ints% [2,5])),0,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,4])),.pre 0 1 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_51_ok : cell1_51.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_51_ok
def cell1_52 : PCell := ⟨(rq (raw_ints% [8,27])),(rq (raw_ints% [1,3])),0,0,(rq (raw_ints% [-1,3])),(rq (raw_ints% [5,4])),.pre 0 1 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_52_ok : cell1_52.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_52_ok
def cell1_53 : PCell := ⟨(rq (raw_ints% [4,15])),(rq (raw_ints% [8,27])),0,0,(rq (raw_ints% [1,3])),(rq (raw_ints% [-1,1])),.pre 0 0 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_53_ok : cell1_53.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_53_ok
def cell1_54 : PCell := ⟨(rq (raw_ints% [0,1])),(rq (raw_ints% [4,15])),0,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,4])),.pre 0 0 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_54_ok : cell1_54.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_54_ok

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
