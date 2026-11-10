module
public import CatalanCore.Uniform.Bank.Chi3.KContent.Data.PC.U1B000
public import CatalanCore.Uniform.Bank.Chi3.KContent.Data.PC.U1B001
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Chi3.KContent
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
def pcHead1_0 : QPiece × Cert := (⟨(qq (1) 4), (qq (3) 11), (qq (3) 1), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨14, [], [], (qq (240) 1)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_0_ok : kpieceAll kHead 1 [pcHead1_0]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_0_ok
def pcHead1_1 : QPiece × Cert := (⟨(qq (3) 11), (qq (5) 18), (qq (3) 2), (qq (7) 2), (qq (1000000000000) 1)⟩, ⟨13, [], [], (qq (605) 3)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_1_ok : kpieceAll kHead 1 [pcHead1_1]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_1_ok
def pcHead1_2 : QPiece × Cert := (⟨(qq (5) 18), (qq (9) 32), (qq (4) 1), (qq (-11) 2), (qq (1000000000000) 1)⟩, ⟨12, [], [], (qq (972) 5)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_2_ok : kpieceAll kHead 1 [pcHead1_2]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_2_ok
def pcHead1_3 : QPiece × Cert := (⟨(qq (9) 32), (qq (2) 7), (qq (5) 2), (qq (-1) 6), (qq (1000000000000) 1)⟩, ⟨12, [], [], (qq (5120) 27)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_3_ok : kpieceAll kHead 1 [pcHead1_3]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_3_ok
def pcHead1_4 : QPiece × Cert := (⟨(qq (2) 7), (qq (15) 52), (qq (3) 2), (qq (10) 3), (qq (1000000000000) 1)⟩, ⟨12, [], [], (qq (735) 4)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_4_ok : kpieceAll kHead 1 [pcHead1_4]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_4_ok
def pcHead1_5 : QPiece × Cert := (⟨(qq (15) 52), (qq (3) 10), (qq (4) 1), (qq (-16) 3), (qq (1000000000000) 1)⟩, ⟨10, [], [], (qq (2704) 15)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_5_ok : kpieceAll kHead 1 [pcHead1_5]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_5_ok
def pcHead1_6 : QPiece × Cert := (⟨(qq (3) 10), (qq (5) 16), (qq (3) 2), (qq (3) 1), (qq (1000000000000) 1)⟩, ⟨10, [], [], (qq (500) 3)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_6_ok : kpieceAll kHead 1 [pcHead1_6]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_6_ok
def pcHead1_7 : QPiece × Cert := (⟨(qq (5) 16), (qq (1) 3), (qq (4) 1), (qq (-5) 1), (qq (1000000000000) 1)⟩, ⟨9, [], [], (qq (768) 5)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_7_ok : kpieceAll kHead 1 [pcHead1_7]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_7_ok
def pcHead1_8 : QPiece × Cert := (⟨(qq (1) 3), (qq (5) 14), (qq (3) 2), (qq (5) 2), (qq (1000000000000) 1)⟩, ⟨9, [(qq (9) 26)], [], (qq (135) 1)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_8_ok : kpieceAll kHead 1 [pcHead1_8]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_8_ok
def pcHead1_9 : QPiece × Cert := (⟨(qq (5) 14), (qq (5) 12), (qq (11) 4), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨1, [], [], (qq (588) 5)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_9_ok : kpieceAll kHead 1 [pcHead1_9]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_9_ok
def pcHead1_10 : QPiece × Cert := (⟨(qq (5) 12), (qq (3) 7), (qq (4) 1), (qq (-4) 1), (qq (1000000000000) 1)⟩, ⟨7, [], [], (qq (432) 5)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_10_ok : kpieceAll kHead 1 [pcHead1_10]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_10_ok
def pcHead1_11 : QPiece × Cert := (⟨(qq (3) 7), (qq (1) 2), (qq (5) 2), (qq (-1) 2), (qq (1000000000000) 1)⟩, ⟨7, [(qq (9) 20)], [], (qq (245) 3)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_11_ok : kpieceAll kHead 1 [pcHead1_11]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_11_ok
def pcHead1_12 : QPiece × Cert := (⟨(qq (1) 2), (qq (5) 8), (qq (9) 4), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨1, [], [], (qq (60) 1)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_12_ok : kpieceAll kHead 1 [pcHead1_12]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_12_ok
def pcHead1_13 : QPiece × Cert := (⟨(qq (5) 8), (qq (2) 3), (qq (7) 2), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (192) 5)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_13_ok : kpieceAll kHead 1 [pcHead1_13]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_13_ok
def pcHead1_14 : QPiece × Cert := (⟨(qq (2) 3), (qq (3) 4), (qq (5) 2), (qq (-1) 2), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (135) 4)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_14_ok : kpieceAll kHead 1 [pcHead1_14]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_14_ok
def pcHead1_15 : QPiece × Cert := (⟨(qq (3) 4), (qq (5) 6), (qq (1) 1), (qq (3) 2), (qq (1000000000000) 1)⟩, ⟨5, [], [], (qq (80) 3)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_15_ok : kpieceAll kHead 1 [pcHead1_15]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_15_ok
def pcHead1_16 : QPiece × Cert := (⟨(qq (5) 6), (qq (15) 16), (qq (9) 4), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨1, [], [], (qq (108) 5)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_16_ok : kpieceAll kHead 1 [pcHead1_16]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_16_ok
def pcHead1_17 : QPiece × Cert := (⟨(qq (15) 16), (qq (9) 8), (qq (7) 2), (qq (-4) 3), (qq (1000000000000) 1)⟩, ⟨3, [(qq (1) 1)], [], (qq (272) 15)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_17_ok : kpieceAll kHead 1 [pcHead1_17]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_17_ok
def pcHead1_18 : QPiece × Cert := (⟨(qq (9) 8), (qq (3) 2), (qq (5) 1), (qq (-8) 3), (qq (1000000000000) 1)⟩, ⟨3, [], [], (qq (136) 9)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_18_ok : kpieceAll kHead 1 [pcHead1_18]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_18_ok
def pcHead1_19 : QPiece × Cert := (⟨(qq (3) 2), (qq (2) 1), (qq (2) 1), (qq (-2) 3), (qq (1000000000000) 1)⟩, ⟨3, [], [], (qq (34) 3)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_19_ok : kpieceAll kHead 1 [pcHead1_19]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_19_ok
def pcHead1_20 : QPiece × Cert := (⟨(qq (2) 1), (qq (3) 1), (qq (1) 1), (qq (-1) 6), (qq (1000000000000) 1)⟩, ⟨3, [], [], (qq (17) 2)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_20_ok : kpieceAll kHead 1 [pcHead1_20]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_20_ok
def pcHead1_21 : QPiece × Cert := (⟨(qq (3) 1), (qq (9) 2), (qq (3) 2), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨2, [], [], (qq (2) 1)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_21_ok : kpieceAll kHead 1 [pcHead1_21]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_21_ok
def pcHead1_22 : QPiece × Cert := (⟨(qq (9) 2), (qq (9) 1), (qq (0) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨2, [], [], (qq (4) 3)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead1_22_ok : kpieceAll kHead 1 [pcHead1_22]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead1_22_ok
def pcBases1 : List (QPiece × Cert) := [pcBase1_0, pcBase1_1, pcBase1_2, pcBase1_3, pcBase1_4, pcBase1_5, pcBase1_6, pcBase1_7, pcBase1_8, pcBase1_9, pcBase1_10, pcBase1_11, pcBase1_12, pcBase1_13, pcBase1_14, pcBase1_15, pcBase1_16, pcBase1_17, pcBase1_18, pcBase1_19, pcBase1_20, pcBase1_21, pcBase1_22, pcBase1_23, pcBase1_24, pcBase1_25, pcBase1_26]
def pcHeads1 : List (QPiece × Cert) := [pcHead1_0, pcHead1_1, pcHead1_2, pcHead1_3, pcHead1_4, pcHead1_5, pcHead1_6, pcHead1_7, pcHead1_8, pcHead1_9, pcHead1_10, pcHead1_11, pcHead1_12, pcHead1_13, pcHead1_14, pcHead1_15, pcHead1_16, pcHead1_17, pcHead1_18, pcHead1_19, pcHead1_20, pcHead1_21, pcHead1_22]
def pcTmpl1 : KTmplP := ⟨(pcRat (raw_ints% [1,68])),16,0,pcBases1,pcHeads1,4⟩
def ktmpl1 : KTmpl := pcTmpl1.toK 4 10 kHead.cF
-- kcost: complete chain/tail metadata over unchanged432translated profiles+23heads, no branch rechecks.
set_option profiler true in
theorem ktmpl1_head : ktmplHead kHead 1 ktmpl1=true := by
  -- kcost: 2.0 s metadata budget; actual ktmpl1/5 typechecks1.52/1.31s,432translated profiles+23heads, no branch rechecks
  decide +kernel
#print axioms ktmpl1_head

end CatalanCore.Uniform.Bank.Chi3.KContent
