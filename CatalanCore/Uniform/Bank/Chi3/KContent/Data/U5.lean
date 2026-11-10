module
public import CatalanCore.Uniform.Bank.Chi3.KContent.Data.PC.U5B000
public import CatalanCore.Uniform.Bank.Chi3.KContent.Data.PC.U5B001
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Chi3.KContent
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check
def pcHead5_0 : QPiece × Cert := (⟨(qq (1) 4), (qq (9) 34), (qq (3) 1), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨14, [], [], (qq (240) 1)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_0_ok : kpieceAll kHead 5 [pcHead5_0]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_0_ok
def pcHead5_1 : QPiece × Cert := (⟨(qq (9) 34), (qq (15) 56), (qq (3) 2), (qq (11) 3), (qq (1000000000000) 1)⟩, ⟨13, [], [], (qq (5780) 27)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_1_ok : kpieceAll kHead 5 [pcHead5_1]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_1_ok
def pcHead5_2 : QPiece × Cert := (⟨(qq (15) 56), (qq (3) 11), (qq (4) 1), (qq (-17) 3), (qq (1000000000000) 1)⟩, ⟨11, [], [], (qq (3136) 15)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_2_ok : kpieceAll kHead 5 [pcHead5_2]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_2_ok
def pcHead5_3 : QPiece × Cert := (⟨(qq (3) 11), (qq (5) 18), (qq (3) 2), (qq (7) 2), (qq (1000000000000) 1)⟩, ⟨11, [], [], (qq (605) 3)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_3_ok : kpieceAll kHead 5 [pcHead5_3]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_3_ok
def pcHead5_4 : QPiece × Cert := (⟨(qq (5) 18), (qq (2) 7), (qq (4) 1), (qq (-11) 2), (qq (1000000000000) 1)⟩, ⟨10, [], [], (qq (972) 5)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_4_ok : kpieceAll kHead 5 [pcHead5_4]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_4_ok
def pcHead5_5 : QPiece × Cert := (⟨(qq (2) 7), (qq (3) 10), (qq (3) 1), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨10, [], [], (qq (735) 4)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_5_ok : kpieceAll kHead 5 [pcHead5_5]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_5_ok
def pcHead5_6 : QPiece × Cert := (⟨(qq (3) 10), (qq (5) 16), (qq (3) 2), (qq (3) 1), (qq (1000000000000) 1)⟩, ⟨10, [], [], (qq (500) 3)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_6_ok : kpieceAll kHead 5 [pcHead5_6]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_6_ok
def pcHead5_7 : QPiece × Cert := (⟨(qq (5) 16), (qq (9) 28), (qq (4) 1), (qq (-5) 1), (qq (1000000000000) 1)⟩, ⟨9, [], [], (qq (768) 5)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_7_ok : kpieceAll kHead 5 [pcHead5_7]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_7_ok
def pcHead5_8 : QPiece × Cert := (⟨(qq (9) 28), (qq (1) 3), (qq (5) 2), (qq (-1) 3), (qq (1000000000000) 1)⟩, ⟨9, [], [], (qq (3920) 27)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_8_ok : kpieceAll kHead 5 [pcHead5_8]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_8_ok
def pcHead5_9 : QPiece × Cert := (⟨(qq (1) 3), (qq (15) 44), (qq (3) 2), (qq (8) 3), (qq (1000000000000) 1)⟩, ⟨9, [], [], (qq (135) 1)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_9_ok : kpieceAll kHead 5 [pcHead5_9]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_9_ok
def pcHead5_10 : QPiece × Cert := (⟨(qq (15) 44), (qq (5) 14), (qq (11) 4), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨1, [], [], (qq (1936) 15)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_10_ok : kpieceAll kHead 5 [pcHead5_10]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_10_ok
def pcHead5_11 : QPiece × Cert := (⟨(qq (5) 14), (qq (3) 8), (qq (4) 1), (qq (-9) 2), (qq (1000000000000) 1)⟩, ⟨8, [], [], (qq (588) 5)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_11_ok : kpieceAll kHead 5 [pcHead5_11]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_11_ok
def pcHead5_12 : QPiece × Cert := (⟨(qq (3) 8), (qq (2) 5), (qq (5) 2), (qq (-1) 2), (qq (1000000000000) 1)⟩, ⟨8, [], [], (qq (320) 3)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_12_ok : kpieceAll kHead 5 [pcHead5_12]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_12_ok
def pcHead5_13 : QPiece × Cert := (⟨(qq (2) 5), (qq (5) 12), (qq (3) 2), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨8, [], [], (qq (375) 4)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_13_ok : kpieceAll kHead 5 [pcHead5_13]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_13_ok
def pcHead5_14 : QPiece × Cert := (⟨(qq (5) 12), (qq (1) 2), (qq (11) 4), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨1, [], [], (qq (432) 5)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_14_ok : kpieceAll kHead 5 [pcHead5_14]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_14_ok
def pcHead5_15 : QPiece × Cert := (⟨(qq (1) 2), (qq (3) 5), (qq (5) 2), (qq (-1) 2), (qq (1000000000000) 1)⟩, ⟨6, [(qq (9) 16)], [], (qq (60) 1)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_15_ok : kpieceAll kHead 5 [pcHead5_15]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_15_ok
def pcHead5_16 : QPiece × Cert := (⟨(qq (3) 5), (qq (5) 8), (qq (1) 1), (qq (2) 1), (qq (1000000000000) 1)⟩, ⟨6, [], [], (qq (125) 3)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_16_ok : kpieceAll kHead 5 [pcHead5_16]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_16_ok
def pcHead5_17 : QPiece × Cert := (⟨(qq (5) 8), (qq (5) 6), (qq (9) 4), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨1, [], [], (qq (192) 5)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_17_ok : kpieceAll kHead 5 [pcHead5_17]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_17_ok
def pcHead5_18 : QPiece × Cert := (⟨(qq (5) 6), (qq (1) 1), (qq (7) 2), (qq (-3) 2), (qq (1000000000000) 1)⟩, ⟨2, [], [], (qq (108) 5)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_18_ok : kpieceAll kHead 5 [pcHead5_18]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_18_ok
def pcHead5_19 : QPiece × Cert := (⟨(qq (1) 1), (qq (3) 2), (qq (4) 1), (qq (-2) 1), (qq (1000000000000) 1)⟩, ⟨2, [], [], (qq (15) 1)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_19_ok : kpieceAll kHead 5 [pcHead5_19]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_19_ok
def pcHead5_20 : QPiece × Cert := (⟨(qq (3) 2), (qq (2) 1), (qq (5) 2), (qq (-1) 1), (qq (1000000000000) 1)⟩, ⟨2, [], [], (qq (20) 3)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_20_ok : kpieceAll kHead 5 [pcHead5_20]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_20_ok
def pcHead5_21 : QPiece × Cert := (⟨(qq (2) 1), (qq (3) 1), (qq (3) 2), (qq (-1) 2), (qq (1000000000000) 1)⟩, ⟨2, [], [], (qq (15) 4)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_21_ok : kpieceAll kHead 5 [pcHead5_21]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_21_ok
def pcHead5_22 : QPiece × Cert := (⟨(qq (3) 1), (qq (9) 1), (qq (0) 1), (qq (0) 1), (qq (1000000000000) 1)⟩, ⟨2, [], [], (qq (2) 1)⟩)
-- kcost: one complete inherited original head certificate.
set_option profiler true in
theorem pcHead5_22_ok : kpieceAll kHead 5 [pcHead5_22]=true := by
  -- kcost: 0.20 s headpiece budget; actual max0.124s typecheck in accepted100check/fullmetadata unit38.719s;23heads/module
  decide +kernel
#print axioms pcHead5_22_ok
def pcBases5 : List (QPiece × Cert) := [pcBase5_0, pcBase5_1, pcBase5_2, pcBase5_3, pcBase5_4, pcBase5_5, pcBase5_6, pcBase5_7, pcBase5_8, pcBase5_9, pcBase5_10, pcBase5_11, pcBase5_12, pcBase5_13, pcBase5_14, pcBase5_15, pcBase5_16, pcBase5_17, pcBase5_18, pcBase5_19, pcBase5_20, pcBase5_21, pcBase5_22, pcBase5_23, pcBase5_24, pcBase5_25, pcBase5_26]
def pcHeads5 : List (QPiece × Cert) := [pcHead5_0, pcHead5_1, pcHead5_2, pcHead5_3, pcHead5_4, pcHead5_5, pcHead5_6, pcHead5_7, pcHead5_8, pcHead5_9, pcHead5_10, pcHead5_11, pcHead5_12, pcHead5_13, pcHead5_14, pcHead5_15, pcHead5_16, pcHead5_17, pcHead5_18, pcHead5_19, pcHead5_20, pcHead5_21, pcHead5_22]
def pcTmpl5 : KTmplP := ⟨(pcRat (raw_ints% [1,68])),16,0,pcBases5,pcHeads5,4⟩
def ktmpl5 : KTmpl := pcTmpl5.toK 4 10 kHead.cF
-- kcost: complete chain/tail metadata over unchanged432translated profiles+23heads, no branch rechecks.
set_option profiler true in
theorem ktmpl5_head : ktmplHead kHead 5 ktmpl5=true := by
  -- kcost: 2.0 s metadata budget; actual ktmpl1/5 typechecks1.52/1.31s,432translated profiles+23heads, no branch rechecks
  decide +kernel
#print axioms ktmpl5_head

end CatalanCore.Uniform.Bank.Chi3.KContent
