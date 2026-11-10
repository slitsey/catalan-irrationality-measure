module
public import CatalanCore.Uniform.Bank.Chi3.KContent.Data.PC.Head
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Chi3.KContent
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
def pcBase5_0 : QPiece × Cert := (⟨(qq (1) 8), (qq (9) 70), (qq (3) 1), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨8, [], [], (qq (960) 1)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_0_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_0=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_0_ok
def pcBase5_1 : QPiece × Cert := (⟨(qq (9) 70), (qq (15) 116), (qq (3) 2), (qq (23) 3), (qq (1000000000000) 1)⟩, ⟨8, [], [], (qq (24500) 27)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_1_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_1=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_1_ok
def pcBase5_2 : QPiece × Cert := (⟨(qq (15) 116), (qq (3) 23), (qq (4) 1), (qq (-35) 3), (qq (1000000000000) 1)⟩, ⟨6, [], [], (qq (13456) 15)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_2_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_2=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_2_ok
def pcBase5_3 : QPiece × Cert := (⟨(qq (3) 23), (qq (5) 38), (qq (3) 2), (qq (15) 2), (qq (1000000000000) 1)⟩, ⟨6, [], [], (qq (2645) 3)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_3_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_3=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_3_ok
def pcBase5_4 : QPiece × Cert := (⟨(qq (5) 38), (qq (2) 15), (qq (4) 1), (qq (-23) 2), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (4332) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_4_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_4=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_4_ok
def pcBase5_5 : QPiece × Cert := (⟨(qq (2) 15), (qq (3) 22), (qq (3) 1), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (3375) 4)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_5_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_5=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_5_ok
def pcBase5_6 : QPiece × Cert := (⟨(qq (3) 22), (qq (5) 36), (qq (3) 2), (qq (7) 1), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (2420) 3)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_6_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_6=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_6_ok
def pcBase5_7 : QPiece × Cert := (⟨(qq (5) 36), (qq (9) 64), (qq (4) 1), (qq (-11) 1), (qq (1000000000000) 1)⟩, ⟨4, [], [], (qq (3888) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_7_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_7=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_7_ok
def pcBase5_8 : QPiece × Cert := (⟨(qq (9) 64), (qq (1) 7), (qq (5) 2), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨4, [], [], (qq (20480) 27)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_8_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_8=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_8_ok
def pcBase5_9 : QPiece × Cert := (⟨(qq (1) 7), (qq (15) 104), (qq (3) 2), (qq (20) 3), (qq (1000000000000) 1)⟩, ⟨8, [], [], (qq (735) 1)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_9_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_9=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_9_ok
def pcBase5_10 : QPiece × Cert := (⟨(qq (15) 104), (qq (5) 34), (qq (11) 4), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (10816) 15)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_10_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_10=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_10_ok
def pcBase5_11 : QPiece × Cert := (⟨(qq (5) 34), (qq (3) 20), (qq (4) 1), (qq (-21) 2), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (3468) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_11_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_11=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_11_ok
def pcBase5_12 : QPiece × Cert := (⟨(qq (3) 20), (qq (2) 13), (qq (5) 2), (qq (-1) 2), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (2000) 3)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_12_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_12=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_12_ok
def pcBase5_13 : QPiece × Cert := (⟨(qq (2) 13), (qq (5) 32), (qq (3) 2), (qq (6) 1), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (2535) 4)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_13_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_13=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_13_ok
def pcBase5_14 : QPiece × Cert := (⟨(qq (5) 32), (qq (1) 6), (qq (11) 4), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3072) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_14_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_14=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_14_ok
def pcBase5_15 : QPiece × Cert := (⟨(qq (1) 6), (qq (3) 17), (qq (5) 2), (qq (-1) 2), (qq (1000000000000) 1)⟩, ⟨5, [(qq (9) 52)], [], (qq (540) 1)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_15_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_15=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_15_ok
def pcBase5_16 : QPiece × Cert := (⟨(qq (3) 17), (qq (5) 28), (qq (1) 1), (qq (8) 1), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (1445) 3)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_16_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_16=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_16_ok
def pcBase5_17 : QPiece × Cert := (⟨(qq (5) 28), (qq (5) 26), (qq (9) 4), (qq (1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2352) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_17_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_17=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_17_ok
def pcBase5_18 : QPiece × Cert := (⟨(qq (5) 26), (qq (1) 5), (qq (7) 2), (qq (-11) 2), (qq (1000000000000) 1)⟩, ⟨1, [(qq (9) 46)], [], (qq (2028) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_18_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_18=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_18_ok
def pcBase5_19 : QPiece × Cert := (⟨(qq (1) 5), (qq (5) 24), (qq (1) 1), (qq (7) 1), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (375) 1)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_19_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_19=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_19_ok
def pcBase5_20 : QPiece × Cert := (⟨(qq (5) 24), (qq (3) 14), (qq (7) 2), (qq (-5) 1), (qq (1000000000000) 1)⟩, ⟨4, [], [], (qq (1728) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_20_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_20=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_20_ok
def pcBase5_21 : QPiece × Cert := (⟨(qq (3) 14), (qq (15) 68), (qq (1) 1), (qq (20) 3), (qq (1000000000000) 1)⟩, ⟨4, [], [], (qq (980) 3)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_21_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_21=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_21_ok
def pcBase5_22 : QPiece × Cert := (⟨(qq (15) 68), (qq (2) 9), (qq (7) 2), (qq (-14) 3), (qq (1000000000000) 1)⟩, ⟨2, [], [], (qq (4624) 15)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_22_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_22=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_22_ok
def pcBase5_23 : QPiece × Cert := (⟨(qq (2) 9), (qq (9) 40), (qq (5) 2), (qq (-1) 6), (qq (1000000000000) 1)⟩, ⟨2, [], [], (qq (1215) 4)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase5_23_ok : cellOKb kHead pcBaseCat 5 16 4 10000 pcBase5_23=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase5_23_ok

end CatalanCore.Uniform.Bank.Chi3.KContent
