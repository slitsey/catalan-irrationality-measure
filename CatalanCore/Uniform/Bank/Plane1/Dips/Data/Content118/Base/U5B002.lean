module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
def cell5_48 : PCell := ⟨(rq (raw_ints% [2,3])),(rq (raw_ints% [4,5])),0,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_48_ok : cell5_48.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_48_ok
def cell5_49 : PCell := ⟨(rq (raw_ints% [16,27])),(rq (raw_ints% [2,3])),0,0,(rq (raw_ints% [-2,3])),(rq (raw_ints% [5,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_49_ok : cell5_49.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_49_ok
def cell5_50 : PCell := ⟨(rq (raw_ints% [8,15])),(rq (raw_ints% [16,27])),0,0,(rq (raw_ints% [2,3])),(rq (raw_ints% [-1,1])),.pre 0 0 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_50_ok : cell5_50.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_50_ok
def cell5_51 : PCell := ⟨(rq (raw_ints% [1,2])),(rq (raw_ints% [8,15])),0,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,4])),.pre 0 0 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_51_ok : cell5_51.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_51_ok
def cell5_52 : PCell := ⟨(rq (raw_ints% [4,9])),(rq (raw_ints% [1,2])),0,0,(rq (raw_ints% [-1,2])),(rq (raw_ints% [5,4])),.pre 0 0 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_52_ok : cell5_52.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_52_ok
def cell5_53 : PCell := ⟨(rq (raw_ints% [2,5])),(rq (raw_ints% [4,9])),0,0,(rq (raw_ints% [1,2])),(rq (raw_ints% [-1,1])),.pre 0 0 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_53_ok : cell5_53.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_53_ok
def cell5_54 : PCell := ⟨(rq (raw_ints% [0,1])),(rq (raw_ints% [2,5])),0,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,4])),.pre 0 0 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_54_ok : cell5_54.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_54_ok

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
