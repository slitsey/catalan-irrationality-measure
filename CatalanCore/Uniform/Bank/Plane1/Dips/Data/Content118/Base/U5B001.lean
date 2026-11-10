module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
def cell5_24 : PCell := ⟨(rq (raw_ints% [44,9])),(rq (raw_ints% [5,1])),4,0,(rq (raw_ints% [1,1])),(rq (raw_ints% [-1,8])),.d1x⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_24_ok : cell5_24.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_24_ok
def cell5_25 : PCell := ⟨(rq (raw_ints% [24,5])),(rq (raw_ints% [44,9])),4,0,(rq (raw_ints% [13,2])),(rq (raw_ints% [-5,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_25_ok : cell5_25.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_25_ok
def cell5_26 : PCell := ⟨(rq (raw_ints% [9,2])),(rq (raw_ints% [24,5])),4,0,(rq (raw_ints% [1,2])),(rq (raw_ints% [0,1])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_26_ok : cell5_26.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_26_ok
def cell5_27 : PCell := ⟨(rq (raw_ints% [40,9])),(rq (raw_ints% [9,2])),4,0,(rq (raw_ints% [-4,1])),(rq (raw_ints% [1,1])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_27_ok : cell5_27.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_27_ok
def cell5_28 : PCell := ⟨(rq (raw_ints% [4,1])),(rq (raw_ints% [40,9])),4,0,(rq (raw_ints% [1,1])),(rq (raw_ints% [-1,8])),.d1x⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_28_ok : cell5_28.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_28_ok
def cell5_29 : PCell := ⟨(rq (raw_ints% [18,5])),(rq (raw_ints% [4,1])),3,0,(rq (raw_ints% [1,2])),(rq (raw_ints% [0,1])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_29_ok : cell5_29.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_29_ok
def cell5_30 : PCell := ⟨(rq (raw_ints% [32,9])),(rq (raw_ints% [18,5])),3,0,(rq (raw_ints% [-4,1])),(rq (raw_ints% [5,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_30_ok : cell5_30.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_30_ok
def cell5_31 : PCell := ⟨(rq (raw_ints% [28,9])),(rq (raw_ints% [32,9])),3,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,8])),.d1x⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_31_ok : cell5_31.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_31_ok
def cell5_32 : PCell := ⟨(rq (raw_ints% [3,1])),(rq (raw_ints% [28,9])),3,0,(rq (raw_ints% [7,2])),(rq (raw_ints% [-1,1])),.pre 0 0 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_32_ok : cell5_32.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_32_ok
def cell5_33 : PCell := ⟨(rq (raw_ints% [14,5])),(rq (raw_ints% [3,1])),2,0,(rq (raw_ints% [1,2])),(rq (raw_ints% [0,1])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_33_ok : cell5_33.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_33_ok
def cell5_34 : PCell := ⟨(rq (raw_ints% [8,3])),(rq (raw_ints% [14,5])),2,0,(rq (raw_ints% [-3,1])),(rq (raw_ints% [5,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_34_ok : cell5_34.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_34_ok
def cell5_35 : PCell := ⟨(rq (raw_ints% [12,5])),(rq (raw_ints% [8,3])),2,0,(rq (raw_ints% [1,3])),(rq (raw_ints% [0,1])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_35_ok : cell5_35.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_35_ok
def cell5_36 : PCell := ⟨(rq (raw_ints% [64,27])),(rq (raw_ints% [12,5])),2,0,(rq (raw_ints% [-8,3])),(rq (raw_ints% [5,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_36_ok : cell5_36.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_36_ok
def cell5_37 : PCell := ⟨(rq (raw_ints% [20,9])),(rq (raw_ints% [64,27])),2,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,8])),.d1x⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_37_ok : cell5_37.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_37_ok
def cell5_38 : PCell := ⟨(rq (raw_ints% [2,1])),(rq (raw_ints% [20,9])),2,0,(rq (raw_ints% [5,2])),(rq (raw_ints% [-1,1])),.pre 0 0 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_38_ok : cell5_38.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_38_ok
def cell5_39 : PCell := ⟨(rq (raw_ints% [16,9])),(rq (raw_ints% [2,1])),1,0,(rq (raw_ints% [-2,1])),(rq (raw_ints% [5,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_39_ok : cell5_39.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_39_ok
def cell5_40 : PCell := ⟨(rq (raw_ints% [5,3])),(rq (raw_ints% [16,9])),1,0,(rq (raw_ints% [2,1])),(rq (raw_ints% [-1,1])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_40_ok : cell5_40.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_40_ok
def cell5_41 : PCell := ⟨(rq (raw_ints% [8,5])),(rq (raw_ints% [5,3])),1,0,(rq (raw_ints% [1,3])),(rq (raw_ints% [0,1])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_41_ok : cell5_41.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_41_ok
def cell5_42 : PCell := ⟨(rq (raw_ints% [40,27])),(rq (raw_ints% [8,5])),1,0,(rq (raw_ints% [-5,3])),(rq (raw_ints% [5,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_42_ok : cell5_42.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_42_ok
def cell5_43 : PCell := ⟨(rq (raw_ints% [4,3])),(rq (raw_ints% [40,27])),1,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,8])),.d1x⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_43_ok : cell5_43.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_43_ok
def cell5_44 : PCell := ⟨(rq (raw_ints% [6,5])),(rq (raw_ints% [4,3])),1,0,(rq (raw_ints% [3,2])),(rq (raw_ints% [-1,1])),.pre 0 0 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_44_ok : cell5_44.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_44_ok
def cell5_45 : PCell := ⟨(rq (raw_ints% [1,1])),(rq (raw_ints% [6,5])),1,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,4])),.pre 0 0 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_45_ok : cell5_45.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_45_ok
def cell5_46 : PCell := ⟨(rq (raw_ints% [8,9])),(rq (raw_ints% [1,1])),0,0,(rq (raw_ints% [-1,1])),(rq (raw_ints% [5,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_46_ok : cell5_46.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_46_ok
def cell5_47 : PCell := ⟨(rq (raw_ints% [4,5])),(rq (raw_ints% [8,9])),0,0,(rq (raw_ints% [1,1])),(rq (raw_ints% [-1,1])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_47_ok : cell5_47.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_47_ok

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
