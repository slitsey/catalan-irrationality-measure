module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
def cell1_0 : PCell := ⟨(rq (raw_ints% [38,5])),(rq (raw_ints% [8,1])),7,0,(rq (raw_ints% [2,1])),(rq (raw_ints% [-1,4])),.pre 1 2 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_0_ok : cell1_0.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_0_ok
def cell1_1 : PCell := ⟨(rq (raw_ints% [68,9])),(rq (raw_ints% [38,5])),7,0,(rq (raw_ints% [-15,2])),(rq (raw_ints% [1,1])),.pre 1 2 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_1_ok : cell1_1.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_1_ok
def cell1_2 : PCell := ⟨(rq (raw_ints% [15,2])),(rq (raw_ints% [68,9])),7,0,(rq (raw_ints% [19,2])),(rq (raw_ints% [-5,4])),.pre 1 2 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_2_ok : cell1_2.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_2_ok
def cell1_3 : PCell := ⟨(rq (raw_ints% [112,15])),(rq (raw_ints% [15,2])),7,0,(rq (raw_ints% [2,1])),(rq (raw_ints% [-1,4])),.pre 1 2 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_3_ok : cell1_3.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_3_ok
def cell1_4 : PCell := ⟨(rq (raw_ints% [200,27])),(rq (raw_ints% [112,15])),7,0,(rq (raw_ints% [-22,3])),(rq (raw_ints% [1,1])),.pre 1 2 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_4_ok : cell1_4.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_4_ok
def cell1_5 : PCell := ⟨(rq (raw_ints% [22,3])),(rq (raw_ints% [200,27])),7,0,(rq (raw_ints% [28,3])),(rq (raw_ints% [-5,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_5_ok : cell1_5.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_5_ok
def cell1_6 : PCell := ⟨(rq (raw_ints% [36,5])),(rq (raw_ints% [22,3])),7,0,(rq (raw_ints% [2,1])),(rq (raw_ints% [-1,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_6_ok : cell1_6.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_6_ok
def cell1_7 : PCell := ⟨(rq (raw_ints% [64,9])),(rq (raw_ints% [36,5])),7,0,(rq (raw_ints% [-7,1])),(rq (raw_ints% [1,1])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_7_ok : cell1_7.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_7_ok
def cell1_8 : PCell := ⟨(rq (raw_ints% [7,1])),(rq (raw_ints% [64,9])),7,0,(rq (raw_ints% [9,1])),(rq (raw_ints% [-5,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_8_ok : cell1_8.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_8_ok
def cell1_9 : PCell := ⟨(rq (raw_ints% [34,5])),(rq (raw_ints% [7,1])),6,0,(rq (raw_ints% [2,1])),(rq (raw_ints% [-1,4])),.pre 1 2 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_9_ok : cell1_9.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_9_ok
def cell1_10 : PCell := ⟨(rq (raw_ints% [20,3])),(rq (raw_ints% [34,5])),6,0,(rq (raw_ints% [-13,2])),(rq (raw_ints% [1,1])),.pre 1 2 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_10_ok : cell1_10.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_10_ok
def cell1_11 : PCell := ⟨(rq (raw_ints% [176,27])),(rq (raw_ints% [20,3])),6,0,(rq (raw_ints% [1,1])),(rq (raw_ints% [-1,8])),.d1x⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_11_ok : cell1_11.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_11_ok
def cell1_12 : PCell := ⟨(rq (raw_ints% [32,5])),(rq (raw_ints% [176,27])),6,0,(rq (raw_ints% [25,3])),(rq (raw_ints% [-5,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_12_ok : cell1_12.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_12_ok
def cell1_13 : PCell := ⟨(rq (raw_ints% [19,3])),(rq (raw_ints% [32,5])),6,0,(rq (raw_ints% [1,3])),(rq (raw_ints% [0,1])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_13_ok : cell1_13.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_13_ok
def cell1_14 : PCell := ⟨(rq (raw_ints% [56,9])),(rq (raw_ints% [19,3])),6,0,(rq (raw_ints% [-6,1])),(rq (raw_ints% [1,1])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_14_ok : cell1_14.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_14_ok
def cell1_15 : PCell := ⟨(rq (raw_ints% [6,1])),(rq (raw_ints% [56,9])),6,0,(rq (raw_ints% [8,1])),(rq (raw_ints% [-5,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_15_ok : cell1_15.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_15_ok
def cell1_16 : PCell := ⟨(rq (raw_ints% [52,9])),(rq (raw_ints% [6,1])),5,0,(rq (raw_ints% [-11,2])),(rq (raw_ints% [1,1])),.pre 1 2 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_16_ok : cell1_16.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_16_ok
def cell1_17 : PCell := ⟨(rq (raw_ints% [152,27])),(rq (raw_ints% [52,9])),5,0,(rq (raw_ints% [1,1])),(rq (raw_ints% [-1,8])),.d1x⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_17_ok : cell1_17.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_17_ok
def cell1_18 : PCell := ⟨(rq (raw_ints% [28,5])),(rq (raw_ints% [152,27])),5,0,(rq (raw_ints% [22,3])),(rq (raw_ints% [-5,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_18_ok : cell1_18.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_18_ok
def cell1_19 : PCell := ⟨(rq (raw_ints% [16,3])),(rq (raw_ints% [28,5])),5,0,(rq (raw_ints% [1,3])),(rq (raw_ints% [0,1])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_19_ok : cell1_19.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_19_ok
def cell1_20 : PCell := ⟨(rq (raw_ints% [26,5])),(rq (raw_ints% [16,3])),5,0,(rq (raw_ints% [7,1])),(rq (raw_ints% [-5,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_20_ok : cell1_20.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_20_ok
def cell1_21 : PCell := ⟨(rq (raw_ints% [5,1])),(rq (raw_ints% [26,5])),5,0,(rq (raw_ints% [1,2])),(rq (raw_ints% [0,1])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_21_ok : cell1_21.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_21_ok
def cell1_22 : PCell := ⟨(rq (raw_ints% [44,9])),(rq (raw_ints% [5,1])),4,0,(rq (raw_ints% [-9,2])),(rq (raw_ints% [1,1])),.pre 1 2 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_22_ok : cell1_22.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_22_ok
def cell1_23 : PCell := ⟨(rq (raw_ints% [40,9])),(rq (raw_ints% [44,9])),4,0,(rq (raw_ints% [1,1])),(rq (raw_ints% [-1,8])),.d1x⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell1_23_ok : cell1_23.ok (1/8) (1/3) (1/2)=true := by decide +kernel
#print axioms cell1_23_ok

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
