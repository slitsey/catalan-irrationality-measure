module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
def cell1_24 : PCell := ⟨(rq (raw_ints% [22,5])),(rq (raw_ints% [40,9])),4,0,(rq (raw_ints% [6,1])),(rq (raw_ints% [-5,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_24_ok : cell1_24.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_24_ok
def cell1_25 : PCell := ⟨(rq (raw_ints% [4,1])),(rq (raw_ints% [22,5])),4,0,(rq (raw_ints% [1,2])),(rq (raw_ints% [0,1])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_25_ok : cell1_25.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_25_ok
def cell1_26 : PCell := ⟨(rq (raw_ints% [32,9])),(rq (raw_ints% [4,1])),3,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,8])),.d1x⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_26_ok : cell1_26.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_26_ok
def cell1_27 : PCell := ⟨(rq (raw_ints% [7,2])),(rq (raw_ints% [32,9])),3,0,(rq (raw_ints% [4,1])),(rq (raw_ints% [-1,1])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_27_ok : cell1_27.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_27_ok
def cell1_28 : PCell := ⟨(rq (raw_ints% [16,5])),(rq (raw_ints% [7,2])),3,0,(rq (raw_ints% [1,2])),(rq (raw_ints% [0,1])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_28_ok : cell1_28.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_28_ok
def cell1_29 : PCell := ⟨(rq (raw_ints% [28,9])),(rq (raw_ints% [16,5])),3,0,(rq (raw_ints% [-7,2])),(rq (raw_ints% [5,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_29_ok : cell1_29.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_29_ok
def cell1_30 : PCell := ⟨(rq (raw_ints% [3,1])),(rq (raw_ints% [28,9])),3,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,8])),.d1x⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_30_ok : cell1_30.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_30_ok
def cell1_31 : PCell := ⟨(rq (raw_ints% [8,3])),(rq (raw_ints% [3,1])),2,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,8])),.d1x⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_31_ok : cell1_31.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_31_ok
def cell1_32 : PCell := ⟨(rq (raw_ints% [5,2])),(rq (raw_ints% [8,3])),2,0,(rq (raw_ints% [3,1])),(rq (raw_ints% [-1,1])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_32_ok : cell1_32.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_32_ok
def cell1_33 : PCell := ⟨(rq (raw_ints% [12,5])),(rq (raw_ints% [5,2])),2,0,(rq (raw_ints% [1,2])),(rq (raw_ints% [0,1])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_33_ok : cell1_33.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_33_ok
def cell1_34 : PCell := ⟨(rq (raw_ints% [20,9])),(rq (raw_ints% [12,5])),2,0,(rq (raw_ints% [-5,2])),(rq (raw_ints% [5,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_34_ok : cell1_34.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_34_ok
def cell1_35 : PCell := ⟨(rq (raw_ints% [56,27])),(rq (raw_ints% [20,9])),2,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,8])),.d1x⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_35_ok : cell1_35.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_35_ok
def cell1_36 : PCell := ⟨(rq (raw_ints% [2,1])),(rq (raw_ints% [56,27])),2,0,(rq (raw_ints% [7,3])),(rq (raw_ints% [-1,1])),.pre 0 0 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_36_ok : cell1_36.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_36_ok
def cell1_37 : PCell := ⟨(rq (raw_ints% [28,15])),(rq (raw_ints% [2,1])),1,0,(rq (raw_ints% [1,3])),(rq (raw_ints% [0,1])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_37_ok : cell1_37.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_37_ok
def cell1_38 : PCell := ⟨(rq (raw_ints% [16,9])),(rq (raw_ints% [28,15])),1,0,(rq (raw_ints% [-2,1])),(rq (raw_ints% [5,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_38_ok : cell1_38.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_38_ok
def cell1_39 : PCell := ⟨(rq (raw_ints% [8,5])),(rq (raw_ints% [16,9])),1,0,(rq (raw_ints% [2,1])),(rq (raw_ints% [-1,1])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_39_ok : cell1_39.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_39_ok
def cell1_40 : PCell := ⟨(rq (raw_ints% [3,2])),(rq (raw_ints% [8,5])),1,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_40_ok : cell1_40.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_40_ok
def cell1_41 : PCell := ⟨(rq (raw_ints% [4,3])),(rq (raw_ints% [3,2])),1,0,(rq (raw_ints% [-3,2])),(rq (raw_ints% [5,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_41_ok : cell1_41.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_41_ok
def cell1_42 : PCell := ⟨(rq (raw_ints% [6,5])),(rq (raw_ints% [4,3])),1,0,(rq (raw_ints% [1,6])),(rq (raw_ints% [0,1])),.pre 0 1 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_42_ok : cell1_42.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_42_ok
def cell1_43 : PCell := ⟨(rq (raw_ints% [32,27])),(rq (raw_ints% [6,5])),1,0,(rq (raw_ints% [-4,3])),(rq (raw_ints% [5,4])),.pre 0 1 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_43_ok : cell1_43.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_43_ok
def cell1_44 : PCell := ⟨(rq (raw_ints% [16,15])),(rq (raw_ints% [32,27])),1,0,(rq (raw_ints% [4,3])),(rq (raw_ints% [-1,1])),.pre 0 0 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_44_ok : cell1_44.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_44_ok
def cell1_45 : PCell := ⟨(rq (raw_ints% [1,1])),(rq (raw_ints% [16,15])),1,0,(rq (raw_ints% [0,1])),(rq (raw_ints% [1,4])),.pre 0 0 0⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_45_ok : cell1_45.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_45_ok
def cell1_46 : PCell := ⟨(rq (raw_ints% [8,9])),(rq (raw_ints% [1,1])),0,0,(rq (raw_ints% [-1,1])),(rq (raw_ints% [5,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_46_ok : cell1_46.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_46_ok
def cell1_47 : PCell := ⟨(rq (raw_ints% [4,5])),(rq (raw_ints% [8,9])),0,0,(rq (raw_ints% [1,1])),(rq (raw_ints% [-1,1])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_47_ok : cell1_47.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_47_ok

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
