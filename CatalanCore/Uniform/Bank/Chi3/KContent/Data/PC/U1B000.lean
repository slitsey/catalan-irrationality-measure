module
public import CatalanCore.Uniform.Bank.Chi3.KContent.Data.PC.Head
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Chi3.KContent
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
def pcBase1_0 : QPiece × Cert := (⟨(qq (1) 8), (qq (3) 23), (qq (3) 1), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨8, [], [], (qq (960) 1)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_0_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_0=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_0_ok
def pcBase1_1 : QPiece × Cert := (⟨(qq (3) 23), (qq (5) 38), (qq (3) 2), (qq (15) 2), (qq (1000000000000) 1)⟩, ⟨8, [], [], (qq (2645) 3)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_1_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_1=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_1_ok
def pcBase1_2 : QPiece × Cert := (⟨(qq (5) 38), (qq (9) 68), (qq (4) 1), (qq (-23) 2), (qq (1000000000000) 1)⟩, ⟨7, [], [], (qq (4332) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_2_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_2=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_2_ok
def pcBase1_3 : QPiece × Cert := (⟨(qq (9) 68), (qq (2) 15), (qq (5) 2), (qq (-1) 6), (qq (1000000000000) 1)⟩, ⟨7, [], [], (qq (23120) 27)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_3_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_3=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_3_ok
def pcBase1_4 : QPiece × Cert := (⟨(qq (2) 15), (qq (15) 112), (qq (3) 2), (qq (22) 3), (qq (1000000000000) 1)⟩, ⟨7, [], [], (qq (3375) 4)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_4_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_4=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_4_ok
def pcBase1_5 : QPiece × Cert := (⟨(qq (15) 112), (qq (3) 22), (qq (4) 1), (qq (-34) 3), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (12544) 15)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_5_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_5=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_5_ok
def pcBase1_6 : QPiece × Cert := (⟨(qq (3) 22), (qq (5) 36), (qq (3) 2), (qq (7) 1), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (2420) 3)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_6_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_6=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_6_ok
def pcBase1_7 : QPiece × Cert := (⟨(qq (5) 36), (qq (1) 7), (qq (4) 1), (qq (-11) 1), (qq (1000000000000) 1)⟩, ⟨4, [], [], (qq (3888) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_7_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_7=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_7_ok
def pcBase1_8 : QPiece × Cert := (⟨(qq (1) 7), (qq (5) 34), (qq (3) 2), (qq (13) 2), (qq (1000000000000) 1)⟩, ⟨8, [(qq (9) 62)], [], (qq (735) 1)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_8_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_8=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_8_ok
def pcBase1_9 : QPiece × Cert := (⟨(qq (5) 34), (qq (5) 32), (qq (11) 4), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (3468) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_9_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_9=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_9_ok
def pcBase1_10 : QPiece × Cert := (⟨(qq (5) 32), (qq (3) 19), (qq (4) 1), (qq (-10) 1), (qq (1000000000000) 1)⟩, ⟨4, [], [], (qq (3072) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_10_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_10=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_10_ok
def pcBase1_11 : QPiece × Cert := (⟨(qq (3) 19), (qq (1) 6), (qq (5) 2), (qq (-1) 2), (qq (1000000000000) 1)⟩, ⟨4, [(qq (9) 56)], [], (qq (1805) 3)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_11_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_11=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_11_ok
def pcBase1_12 : QPiece × Cert := (⟨(qq (1) 6), (qq (5) 28), (qq (9) 4), (qq (1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (540) 1)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_12_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_12=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_12_ok
def pcBase1_13 : QPiece × Cert := (⟨(qq (5) 28), (qq (2) 11), (qq (7) 2), (qq (-6) 1), (qq (1000000000000) 1)⟩, ⟨4, [], [], (qq (2352) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_13_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_13=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_13_ok
def pcBase1_14 : QPiece × Cert := (⟨(qq (2) 11), (qq (3) 16), (qq (5) 2), (qq (-1) 2), (qq (1000000000000) 1)⟩, ⟨4, [], [], (qq (1815) 4)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_14_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_14=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_14_ok
def pcBase1_15 : QPiece × Cert := (⟨(qq (3) 16), (qq (5) 26), (qq (1) 1), (qq (15) 2), (qq (1000000000000) 1)⟩, ⟨4, [], [], (qq (1280) 3)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_15_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_15=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_15_ok
def pcBase1_16 : QPiece × Cert := (⟨(qq (5) 26), (qq (15) 76), (qq (9) 4), (qq (1) 1), (qq (1000000000000) 1)⟩, ⟨0, [], [], (qq (2028) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_16_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_16=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_16_ok
def pcBase1_17 : QPiece × Cert := (⟨(qq (15) 76), (qq (1) 5), (qq (7) 2), (qq (-16) 3), (qq (1000000000000) 1)⟩, ⟨1, [], [], (qq (5776) 15)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_17_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_17=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_17_ok
def pcBase1_18 : QPiece × Cert := (⟨(qq (1) 5), (qq (9) 44), (qq (5) 2), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (375) 1)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_18_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_18=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_18_ok
def pcBase1_19 : QPiece × Cert := (⟨(qq (9) 44), (qq (5) 24), (qq (1) 1), (qq (7) 1), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (9680) 27)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_19_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_19=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_19_ok
def pcBase1_20 : QPiece × Cert := (⟨(qq (5) 24), (qq (3) 14), (qq (7) 2), (qq (-5) 1), (qq (1000000000000) 1)⟩, ⟨4, [], [], (qq (1728) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_20_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_20=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_20_ok
def pcBase1_21 : QPiece × Cert := (⟨(qq (3) 14), (qq (2) 9), (qq (2) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨4, [], [], (qq (980) 3)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_21_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_21=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_21_ok
def pcBase1_22 : QPiece × Cert := (⟨(qq (2) 9), (qq (5) 22), (qq (1) 1), (qq (13) 2), (qq (1000000000000) 1)⟩, ⟨4, [], [], (qq (1215) 4)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_22_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_22=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_22_ok
def pcBase1_23 : QPiece × Cert := (⟨(qq (5) 22), (qq (3) 13), (qq (7) 2), (qq (-9) 2), (qq (1000000000000) 1)⟩, ⟨3, [], [], (qq (1452) 5)⟩)
-- kcost: one actual complete basepiece, one period only; no16fold repeated checks.
set_option profiler true in
theorem pcBase1_23_ok : cellOKb kHead pcBaseCat 1 16 4 10000 pcBase1_23=true := by
  -- kcost: 0.20 s basepiece budget; actual max0.146s typecheck, accepted100check/fullmetadata unit38.719s; at most24pieces/module
  decide +kernel
#print axioms pcBase1_23_ok

end CatalanCore.Uniform.Bank.Chi3.KContent
