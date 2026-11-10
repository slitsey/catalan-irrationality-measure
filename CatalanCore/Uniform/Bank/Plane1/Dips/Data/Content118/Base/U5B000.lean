module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
def cell5_0 : PCell := ⟨(rq (raw_ints% [116,15])),(rq (raw_ints% [8,1])),7,0,(rq (raw_ints% [2,1])),(rq (raw_ints% [-1,4])),.pre 1 2 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_0_ok : cell5_0.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_0_ok
def cell5_1 : PCell := ⟨(rq (raw_ints% [208,27])),(rq (raw_ints% [116,15])),7,0,(rq (raw_ints% [-23,3])),(rq (raw_ints% [1,1])),.pre 1 2 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_1_ok : cell5_1.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_1_ok
def cell5_2 : PCell := ⟨(rq (raw_ints% [23,3])),(rq (raw_ints% [208,27])),7,0,(rq (raw_ints% [29,3])),(rq (raw_ints% [-5,4])),.pre 1 1 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_2_ok : cell5_2.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_2_ok
def cell5_3 : PCell := ⟨(rq (raw_ints% [38,5])),(rq (raw_ints% [23,3])),7,0,(rq (raw_ints% [2,1])),(rq (raw_ints% [-1,4])),.pre 1 1 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_3_ok : cell5_3.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_3_ok
def cell5_4 : PCell := ⟨(rq (raw_ints% [68,9])),(rq (raw_ints% [38,5])),7,0,(rq (raw_ints% [-15,2])),(rq (raw_ints% [1,1])),.pre 1 1 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_4_ok : cell5_4.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_4_ok
def cell5_5 : PCell := ⟨(rq (raw_ints% [15,2])),(rq (raw_ints% [68,9])),7,0,(rq (raw_ints% [19,2])),(rq (raw_ints% [-5,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_5_ok : cell5_5.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_5_ok
def cell5_6 : PCell := ⟨(rq (raw_ints% [36,5])),(rq (raw_ints% [15,2])),7,0,(rq (raw_ints% [2,1])),(rq (raw_ints% [-1,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_6_ok : cell5_6.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_6_ok
def cell5_7 : PCell := ⟨(rq (raw_ints% [64,9])),(rq (raw_ints% [36,5])),7,0,(rq (raw_ints% [-7,1])),(rq (raw_ints% [1,1])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_7_ok : cell5_7.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_7_ok
def cell5_8 : PCell := ⟨(rq (raw_ints% [7,1])),(rq (raw_ints% [64,9])),7,0,(rq (raw_ints% [9,1])),(rq (raw_ints% [-5,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_8_ok : cell5_8.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_8_ok
def cell5_9 : PCell := ⟨(rq (raw_ints% [104,15])),(rq (raw_ints% [7,1])),6,0,(rq (raw_ints% [2,1])),(rq (raw_ints% [-1,4])),.pre 1 2 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_9_ok : cell5_9.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_9_ok
def cell5_10 : PCell := ⟨(rq (raw_ints% [184,27])),(rq (raw_ints% [104,15])),6,0,(rq (raw_ints% [-20,3])),(rq (raw_ints% [1,1])),.pre 1 2 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_10_ok : cell5_10.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_10_ok
def cell5_11 : PCell := ⟨(rq (raw_ints% [34,5])),(rq (raw_ints% [184,27])),6,0,(rq (raw_ints% [26,3])),(rq (raw_ints% [-5,4])),.pre 1 1 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_11_ok : cell5_11.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_11_ok
def cell5_12 : PCell := ⟨(rq (raw_ints% [20,3])),(rq (raw_ints% [34,5])),6,0,(rq (raw_ints% [1,6])),(rq (raw_ints% [0,1])),.pre 1 1 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_12_ok : cell5_12.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_12_ok
def cell5_13 : PCell := ⟨(rq (raw_ints% [13,2])),(rq (raw_ints% [20,3])),6,0,(rq (raw_ints% [17,2])),(rq (raw_ints% [-5,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_13_ok : cell5_13.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_13_ok
def cell5_14 : PCell := ⟨(rq (raw_ints% [32,5])),(rq (raw_ints% [13,2])),6,0,(rq (raw_ints% [2,1])),(rq (raw_ints% [-1,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_14_ok : cell5_14.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_14_ok
def cell5_15 : PCell := ⟨(rq (raw_ints% [56,9])),(rq (raw_ints% [32,5])),6,0,(rq (raw_ints% [-6,1])),(rq (raw_ints% [1,1])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_15_ok : cell5_15.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_15_ok
def cell5_16 : PCell := ⟨(rq (raw_ints% [92,15])),(rq (raw_ints% [56,9])),6,0,(rq (raw_ints% [8,1])),(rq (raw_ints% [-5,4])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_16_ok : cell5_16.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_16_ok
def cell5_17 : PCell := ⟨(rq (raw_ints% [6,1])),(rq (raw_ints% [92,15])),6,0,(rq (raw_ints% [1,3])),(rq (raw_ints% [0,1])),.pre 0 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_17_ok : cell5_17.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_17_ok
def cell5_18 : PCell := ⟨(rq (raw_ints% [160,27])),(rq (raw_ints% [6,1])),5,0,(rq (raw_ints% [-17,3])),(rq (raw_ints% [1,1])),.pre 1 2 2⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_18_ok : cell5_18.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_18_ok
def cell5_19 : PCell := ⟨(rq (raw_ints% [52,9])),(rq (raw_ints% [160,27])),5,0,(rq (raw_ints% [1,1])),(rq (raw_ints% [-1,8])),.d1x⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_19_ok : cell5_19.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_19_ok
def cell5_20 : PCell := ⟨(rq (raw_ints% [28,5])),(rq (raw_ints% [52,9])),5,0,(rq (raw_ints% [15,2])),(rq (raw_ints% [-5,4])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_20_ok : cell5_20.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_20_ok
def cell5_21 : PCell := ⟨(rq (raw_ints% [11,2])),(rq (raw_ints% [28,5])),5,0,(rq (raw_ints% [1,2])),(rq (raw_ints% [0,1])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_21_ok : cell5_21.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_21_ok
def cell5_22 : PCell := ⟨(rq (raw_ints% [16,3])),(rq (raw_ints% [11,2])),5,0,(rq (raw_ints% [-5,1])),(rq (raw_ints% [1,1])),.pre 1 1 1⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_22_ok : cell5_22.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_22_ok
def cell5_23 : PCell := ⟨(rq (raw_ints% [5,1])),(rq (raw_ints% [16,3])),5,0,(rq (raw_ints% [1,1])),(rq (raw_ints% [-1,8])),.d1x⟩
-- kcost: one complete closed endpoint check, at most25pairs/two endpoints; no repeated32period arithmetic.
set_option profiler true in
theorem cell5_23_ok : cell5_23.ok (1/8) (2/3) (1/2)=true := by decide +kernel
#print axioms cell5_23_ok

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
