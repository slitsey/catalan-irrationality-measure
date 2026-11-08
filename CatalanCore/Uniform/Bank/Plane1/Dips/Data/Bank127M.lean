module

public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Lines127
public import CatalanCore.Uniform.Bank.Plane1.Dips.Rows
public import CatalanCore.Uniform.Bank.Plane1.Data.Common
public import CatalanCore.Uniform.Bank.Plane1.Data.Exp1
public import CatalanCore.Uniform.Bank.Plane1.Data.Exp5

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! # Dip frame (1, -2, 1), support `Support.minus`: the closed bank, `DipBankOK`, and the point theorem (wave R1b; ledger R01-R03)

The catalogue `dipCat` = plane branches, the 8 lines (ln19, ln22, ln24, ln25, ln27, ln28, ln29, ln63) checked by `DipLine.ok`, the 5 bridges
(br18, br21, br23, br24, br26) and the 7 prefix windows; the head pieces of the two root classes
(`θ ∈ (1/12, 9]`) with their certificates; the content `Λ = 3.109606175540`.  The periodic layer (cells, expansion,
masses) is the plane 1 layer unchanged (`Plane1.Data.Exp1`, `Exp5`): the lines act on `θ ≥ 0.3 > 1/12` only. -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.F127
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Uniform
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.KTerm
  CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanCore.Uniform.Bank.Plane1 CatalanCore.Measure CatalanFrames.P6 CatalanCore.Uniform.Bank.Plane1.Dips
open CatalanCore.Uniform.Bank.Plane1.Data

theorem ln19_okM : ln19.ok Support.minus.rho 1 (-2) (1) = true := by
  -- kcost: 1.0 s measured (type feasibility of the line, 100 types per side)
  decide +kernel

theorem ln22_okM : ln22.ok Support.minus.rho 1 (-2) (1) = true := by
  -- kcost: 1.0 s measured (type feasibility of the line, 100 types per side)
  decide +kernel

theorem ln24_okM : ln24.ok Support.minus.rho 1 (-2) (1) = true := by
  -- kcost: 1.0 s measured (type feasibility of the line, 100 types per side)
  decide +kernel

theorem ln25_okM : ln25.ok Support.minus.rho 1 (-2) (1) = true := by
  -- kcost: 1.0 s measured (type feasibility of the line, 100 types per side)
  decide +kernel

theorem ln27_okM : ln27.ok Support.minus.rho 1 (-2) (1) = true := by
  -- kcost: 1.0 s measured (type feasibility of the line, 100 types per side)
  decide +kernel

theorem ln28_okM : ln28.ok Support.minus.rho 1 (-2) (1) = true := by
  -- kcost: 1.0 s measured (type feasibility of the line, 100 types per side)
  decide +kernel

theorem ln29_okM : ln29.ok Support.minus.rho 1 (-2) (1) = true := by
  -- kcost: 1.0 s measured (type feasibility of the line, 100 types per side)
  decide +kernel

theorem ln63_okM : ln63.ok Support.minus.rho 1 (-2) (1) = true := by
  -- kcost: 1.0 s measured (type feasibility of the line, 100 types per side)
  decide +kernel

def lnsM : List DipLine := [ln19, ln22, ln24, ln25, ln27, ln28, ln29, ln63]

def brsM : List DipBridge := [br18, br21, br23, br24, br26]

def presM : List (ℕ × ℕ × ℕ × ℕ) := [(0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 1, 1), (0, 1, 1, 1), (0, 1, 1, 2), (0, 1, 2, 1), (0, 1, 2, 2)]

theorem lnsM_ok : ∀ L ∈ lnsM, L.ok Support.minus.rho 1 (-2) (1) = true := by
  intro L hL
  simp only [lnsM, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [ln19_okM, ln22_okM, ln24_okM, ln25_okM, ln27_okM, ln28_okM, ln29_okM, ln63_okM]

theorem brsM_ok : ∀ B ∈ brsM, (∀ L ∈ B.lines, L ∈ lnsM) ∧ B.Member Support.minus.rho := by
  intro B hB
  simp only [brsM, List.mem_cons, List.not_mem_nil, or_false] at hB
  rcases hB with rfl | rfl | rfl | rfl | rfl
  exacts [⟨by simp [br18, lnsM], br18_member _⟩, ⟨by simp [br21, lnsM], br21_member _⟩, ⟨by simp [br23, lnsM], br23_member _⟩, ⟨by simp [br24, lnsM], br24_member _⟩, ⟨by simp [br26, lnsM], br26_member _⟩]

/-- The header bank. -/
def eHeadM : KBankDataC := { planeHeadC 1 5 [] with kcat := dipCat Support.minus.rho lnsM brsM presM }

/-- The content `Λ` (3.109606175540). -/
def dipLamM : ℚ := qq 120323096881040949034271843023279876029511587974412959975686182335134141382157308381791570934906094561607269236976586827992971595305055793812023478755208299657754469730317898047874979654938160057150210227391809060024230147790003447112350355925430651561701835659581590907639982990172386345606479743168403545930087256562124884293505208165070945786614323895013083568427466321620931322862035567256913034530945834635278551430070680568631642707644824383408563073347503413727149612731059368118389837148634721956353927557858246297217429111790613865498042164318419416454159 38693998560815721154477424811456539125902808714412331647258789773322779117422533276563454554357036461859573524658078589488124644635371022776149764753497713295116871216515371879858552036067512455941048666350337309258791320392368630384032423134412123956148303408439745637226819382889182624336070502023300366337638637345540230232111428308293777212069351212822142476211165616857627779549503086854833941671093567127027969404750664207286462536582575306230903295602445939504081462833716496373393591729305070517587483276608674545875114588037760831803360513616728350720000

def uM1_0 : List (QPiece × Cert) := [
  (⟨qq (1) 12, qq (7) 81, qq (7) 3, qq (-2) 1, qq (1000000000000) 1⟩, ⟨25, [], [], qq (1872) 1⟩),
  (⟨qq (7) 81, qq (13) 150, qq (7) 6, qq (23) 2, qq (1000000000000) 1⟩, ⟨25, [], [], qq (85293) 49⟩),
  (⟨qq (13) 150, qq (2) 23, qq (10) 3, qq (-27) 2, qq (1000000000000) 1⟩, ⟨24, [], [], qq (22500) 13⟩),
  (⟨qq (2) 23, qq (7) 80, qq (7) 3, qq (-2) 1, qq (1000000000000) 1⟩, ⟨24, [], [], qq (6877) 4⟩),
  (⟨qq (7) 80, qq (13) 148, qq (7) 6, qq (34) 3, qq (1000000000000) 1⟩, ⟨24, [], [], qq (83200) 49⟩),
  (⟨qq (13) 148, qq (3) 34, qq (10) 3, qq (-40) 3, qq (1000000000000) 1⟩, ⟨22, [], [], qq (21904) 13⟩),
  (⟨qq (3) 34, qq (7) 78, qq (7) 3, qq (-2) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (15028) 9⟩),
  (⟨qq (7) 78, qq (13) 144, qq (7) 6, qq (11) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (79092) 49⟩),
  (⟨qq (13) 144, qq (1) 11, qq (10) 3, qq (-13) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (20736) 13⟩),
  (⟨qq (1) 11, qq (7) 75, qq (7) 3, qq (-2) 1, qq (1000000000000) 1⟩, ⟨25, [], [], qq (1573) 1⟩)]

def uM1_1 : List (QPiece × Cert) := [
  (⟨qq (7) 75, qq (13) 138, qq (7) 6, qq (21) 2, qq (1000000000000) 1⟩, ⟨25, [], [], qq (73125) 49⟩),
  (⟨qq (13) 138, qq (7) 74, qq (10) 3, qq (-25) 2, qq (1000000000000) 1⟩, ⟨24, [], [], qq (19044) 13⟩),
  (⟨qq (7) 74, qq (2) 21, qq (13) 6, qq (-1) 6, qq (1000000000000) 1⟩, ⟨24, [], [], qq (71188) 49⟩),
  (⟨qq (2) 21, qq (13) 136, qq (7) 6, qq (31) 3, qq (1000000000000) 1⟩, ⟨24, [], [], qq (5733) 4⟩),
  (⟨qq (13) 136, qq (3) 31, qq (10) 3, qq (-37) 3, qq (1000000000000) 1⟩, ⟨22, [], [], qq (18496) 13⟩),
  (⟨qq (3) 31, qq (7) 72, qq (7) 3, qq (-2) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (12493) 9⟩),
  (⟨qq (7) 72, qq (13) 132, qq (7) 6, qq (10) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (67392) 49⟩),
  (⟨qq (13) 132, qq (1) 10, qq (10) 3, qq (-12) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (17424) 13⟩),
  (⟨qq (1) 10, qq (7) 69, qq (7) 3, qq (-2) 1, qq (1000000000000) 1⟩, ⟨25, [], [], qq (1300) 1⟩),
  (⟨qq (7) 69, qq (13) 126, qq (7) 6, qq (19) 2, qq (1000000000000) 1⟩, ⟨25, [(qq (7) 68)], [], qq (61893) 49⟩)]

def uM1_2 : List (QPiece × Cert) := [
  (⟨qq (13) 126, qq (13) 124, qq (9) 4, qq (-1) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (15876) 13⟩),
  (⟨qq (13) 124, qq (7) 66, qq (10) 3, qq (-34) 3, qq (1000000000000) 1⟩, ⟨22, [], [], qq (15376) 13⟩),
  (⟨qq (7) 66, qq (3) 28, qq (13) 6, qq (-1) 3, qq (1000000000000) 1⟩, ⟨22, [], [], qq (56628) 49⟩),
  (⟨qq (3) 28, qq (13) 120, qq (7) 6, qq (9) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (10192) 9⟩),
  (⟨qq (13) 120, qq (1) 9, qq (10) 3, qq (-11) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (14400) 13⟩),
  (⟨qq (1) 9, qq (13) 114, qq (7) 6, qq (17) 2, qq (1000000000000) 1⟩, ⟨25, [(qq (7) 62)], [], qq (1053) 1⟩),
  (⟨qq (13) 114, qq (13) 112, qq (9) 4, qq (-1) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (12996) 13⟩),
  (⟨qq (13) 112, qq (7) 60, qq (10) 3, qq (-31) 3, qq (1000000000000) 1⟩, ⟨22, [], [], qq (12544) 13⟩),
  (⟨qq (7) 60, qq (3) 25, qq (13) 6, qq (-1) 3, qq (1000000000000) 1⟩, ⟨22, [], [], qq (46800) 49⟩),
  (⟨qq (3) 25, qq (13) 108, qq (7) 6, qq (8) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (8125) 9⟩)]

def uM1_3 : List (QPiece × Cert) := [
  (⟨qq (13) 108, qq (7) 57, qq (10) 3, qq (-10) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (11664) 13⟩),
  (⟨qq (7) 57, qq (1) 8, qq (13) 6, qq (-1) 2, qq (1000000000000) 1⟩, ⟨21, [], [], qq (42237) 49⟩),
  (⟨qq (1) 8, qq (13) 102, qq (7) 6, qq (15) 2, qq (1000000000000) 1⟩, ⟨25, [], [], qq (832) 1⟩),
  (⟨qq (13) 102, qq (13) 96, qq (9) 4, qq (-1) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (10404) 13⟩),
  (⟨qq (13) 96, qq (7) 51, qq (10) 3, qq (-9) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (9216) 13⟩),
  (⟨qq (7) 51, qq (1) 7, qq (13) 6, qq (-1) 2, qq (1000000000000) 1⟩, ⟨21, [(qq (7) 50)], [], qq (33813) 49⟩),
  (⟨qq (1) 7, qq (13) 90, qq (7) 6, qq (13) 2, qq (1000000000000) 1⟩, ⟨25, [], [], qq (637) 1⟩),
  (⟨qq (13) 90, qq (13) 84, qq (9) 4, qq (-1) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (8100) 13⟩),
  (⟨qq (13) 84, qq (7) 45, qq (10) 3, qq (-8) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (7056) 13⟩),
  (⟨qq (7) 45, qq (1) 6, qq (13) 6, qq (-1) 2, qq (1000000000000) 1⟩, ⟨21, [(qq (7) 44)], [], qq (26325) 49⟩)]

def uM1_4 : List (QPiece × Cert) := [
  (⟨qq (1) 6, qq (13) 72, qq (25) 12, qq (0) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (468) 1⟩),
  (⟨qq (13) 72, qq (2) 11, qq (19) 6, qq (-6) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (5184) 13⟩),
  (⟨qq (2) 11, qq (7) 36, qq (13) 6, qq (-1) 2, qq (1000000000000) 1⟩, ⟨21, [(qq (3) 16)], [], qq (1573) 4⟩),
  (⟨qq (7) 36, qq (13) 66, qq (1) 1, qq (11) 2, qq (1000000000000) 1⟩, ⟨21, [], [], qq (16848) 49⟩),
  (⟨qq (13) 66, qq (13) 60, qq (25) 12, qq (0) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (4356) 13⟩),
  (⟨qq (13) 60, qq (2) 9, qq (19) 6, qq (-5) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (3600) 13⟩),
  (⟨qq (2) 9, qq (7) 30, qq (13) 6, qq (-1) 2, qq (1000000000000) 1⟩, ⟨21, [(qq (3) 13)], [], qq (1053) 4⟩),
  (⟨qq (7) 30, qq (13) 54, qq (1) 1, qq (9) 2, qq (1000000000000) 1⟩, ⟨21, [], [], qq (11700) 49⟩),
  (⟨qq (13) 54, qq (1) 4, qq (25) 12, qq (0) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (2916) 13⟩),
  (⟨qq (1) 4, qq (7) 26, qq (13) 6, qq (-1) 3, qq (1000000000000) 1⟩, ⟨22, [], [], qq (208) 1⟩)]

def uM1_5 : List (QPiece × Cert) := [
  (⟨qq (7) 26, qq (13) 48, qq (1) 1, qq (4) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (8788) 49⟩),
  (⟨qq (13) 48, qq (2) 7, qq (19) 6, qq (-4) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (2304) 13⟩),
  (⟨qq (2) 7, qq (7) 24, qq (13) 6, qq (-1) 2, qq (1000000000000) 1⟩, ⟨21, [], [], qq (637) 4⟩),
  (⟨qq (7) 24, qq (13) 42, qq (1) 1, qq (7) 2, qq (1000000000000) 1⟩, ⟨21, [(qq (3) 10)], [], qq (7488) 49⟩),
  (⟨qq (13) 42, qq (13) 40, qq (25) 12, qq (0) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (1764) 13⟩),
  (⟨qq (13) 40, qq (1) 3, qq (19) 6, qq (-10) 3, qq (1000000000000) 1⟩, ⟨19, [], [], qq (1600) 13⟩),
  (⟨qq (1) 3, qq (7) 20, qq (13) 6, qq (-1) 3, qq (1000000000000) 1⟩, ⟨22, [], [], qq (117) 1⟩),
  (⟨qq (7) 20, qq (13) 36, qq (1) 1, qq (3) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (5200) 49⟩),
  (⟨qq (13) 36, qq (7) 18, qq (19) 6, qq (-3) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (1296) 13⟩),
  (⟨qq (7) 18, qq (2) 5, qq (2) 1, qq (0) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (4212) 49⟩)]

def uM1_6 : List (QPiece × Cert) := [
  (⟨qq (2) 5, qq (13) 30, qq (1) 1, qq (5) 2, qq (1000000000000) 1⟩, ⟨21, [(qq (3) 7)], [], qq (325) 4⟩),
  (⟨qq (13) 30, qq (13) 28, qq (25) 12, qq (0) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (900) 13⟩),
  (⟨qq (13) 28, qq (1) 2, qq (19) 6, qq (-7) 3, qq (1000000000000) 1⟩, ⟨19, [], [], qq (784) 13⟩),
  (⟨qq (1) 2, qq (7) 12, qq (10) 3, qq (-8) 3, qq (1000000000000) 1⟩, ⟨6, [], [⟨false, 14, (qq (1) 12), (qq (1) 1)⟩], qq (240000) 7⟩),
  (⟨qq (7) 12, qq (2) 3, qq (13) 6, qq (-2) 3, qq (1000000000000) 1⟩, ⟨7, [], [⟨true, 14, (qq (1) 12), (qq (3) 2)⟩, ⟨false, 15, (qq (1) 12), (qq (7) 3)⟩], qq (70000) 1⟩),
  (⟨qq (2) 3, qq (3) 4, qq (19) 6, qq (-13) 6, qq (1000000000000) 1⟩, ⟨8, [], [⟨false, 16, (qq (1) 12), (qq (2) 1)⟩], qq (160000) 3⟩),
  (⟨qq (3) 4, qq (7) 9, qq (19) 6, qq (-13) 6, qq (1000000000000) 1⟩, ⟨9, [], [⟨false, 17, (qq (1) 36), (qq (3) 1)⟩], qq (540000) 7⟩),
  (⟨qq (7) 9, qq (7) 8, qq (2) 1, qq (-2) 3, qq (1000000000000) 1⟩, ⟨10, [], [⟨false, 18, (qq (7) 72), (qq (11) 4)⟩], qq (440000) 7⟩),
  (⟨qq (7) 8, qq (1) 1, qq (2) 1, qq (-2) 3, qq (1000000000000) 1⟩, ⟨11, [], [], qq (832) 49⟩),
  (⟨qq (1) 1, qq (7) 6, qq (1) 1, qq (1) 3, qq (1000000000000) 1⟩, ⟨12, [], [⟨false, 3, (qq (1) 6), (qq (2) 1)⟩], qq (24) 1⟩)]

def uM1_7 : List (QPiece × Cert) := [
  (⟨qq (7) 6, qq (3) 1, qq (13) 6, qq (-2) 3, qq (1000000000000) 1⟩, ⟨3, [], [], qq (12) 1⟩),
  (⟨qq (3) 1, qq (7) 2, qq (7) 6, qq (-1) 3, qq (1000000000000) 1⟩, ⟨4, [], [], qq (2) 1⟩),
  (⟨qq (7) 2, qq (9) 1, qq (0) 1, qq (0) 1, qq (1000000000000) 1⟩, ⟨4, [], [], qq (4) 1⟩)]

theorem uM1_0_ok : kpieceAll eHeadM.toK 1 uM1_0 = true := by
  -- kcost: 1.0 s measured, 10 pieces
  decide +kernel

theorem uM1_1_ok : kpieceAll eHeadM.toK 1 uM1_1 = true := by
  -- kcost: 1.0 s measured, 10 pieces
  decide +kernel

theorem uM1_2_ok : kpieceAll eHeadM.toK 1 uM1_2 = true := by
  -- kcost: 1.0 s measured, 10 pieces
  decide +kernel

theorem uM1_3_ok : kpieceAll eHeadM.toK 1 uM1_3 = true := by
  -- kcost: 1.0 s measured, 10 pieces
  decide +kernel

theorem uM1_4_ok : kpieceAll eHeadM.toK 1 uM1_4 = true := by
  -- kcost: 1.0 s measured, 10 pieces
  decide +kernel

theorem uM1_5_ok : kpieceAll eHeadM.toK 1 uM1_5 = true := by
  -- kcost: 1.0 s measured, 10 pieces
  decide +kernel

theorem uM1_6_ok : kpieceAll eHeadM.toK 1 uM1_6 = true := by
  -- kcost: 1.0 s measured, 10 pieces
  decide +kernel

theorem uM1_7_ok : kpieceAll eHeadM.toK 1 uM1_7 = true := by
  -- kcost: 1.0 s measured, 3 pieces
  decide +kernel

def hM1 : List (QPiece × Cert) := uM1_0 ++ (uM1_1 ++ (uM1_2 ++ (uM1_3 ++ (uM1_4 ++ (uM1_5 ++ (uM1_6 ++ (uM1_7)))))))

theorem hM1_ok : kpieceAll eHeadM.toK 1 hM1 = true := by
  unfold hM1
  simp only [kpieceAll_append, uM1_0_ok, uM1_1_ok, uM1_2_ok, uM1_3_ok, uM1_4_ok, uM1_5_ok, uM1_6_ok, uM1_7_ok, Bool.and_self]

def uM5_0 : List (QPiece × Cert) := [
  (⟨qq (1) 12, qq (7) 82, qq (7) 3, qq (-2) 1, qq (1000000000000) 1⟩, ⟨25, [], [], qq (1872) 1⟩),
  (⟨qq (7) 82, qq (13) 152, qq (7) 6, qq (35) 3, qq (1000000000000) 1⟩, ⟨25, [], [], qq (87412) 49⟩),
  (⟨qq (13) 152, qq (3) 35, qq (10) 3, qq (-41) 3, qq (1000000000000) 1⟩, ⟨23, [], [], qq (23104) 13⟩),
  (⟨qq (3) 35, qq (7) 81, qq (7) 3, qq (-2) 1, qq (1000000000000) 1⟩, ⟨23, [], [], qq (15925) 9⟩),
  (⟨qq (7) 81, qq (13) 150, qq (7) 6, qq (23) 2, qq (1000000000000) 1⟩, ⟨23, [], [], qq (85293) 49⟩),
  (⟨qq (13) 150, qq (2) 23, qq (10) 3, qq (-27) 2, qq (1000000000000) 1⟩, ⟨22, [], [], qq (22500) 13⟩),
  (⟨qq (2) 23, qq (7) 78, qq (7) 3, qq (-2) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (6877) 4⟩),
  (⟨qq (7) 78, qq (13) 144, qq (7) 6, qq (11) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (79092) 49⟩),
  (⟨qq (13) 144, qq (1) 11, qq (10) 3, qq (-13) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (20736) 13⟩),
  (⟨qq (1) 11, qq (7) 76, qq (7) 3, qq (-2) 1, qq (1000000000000) 1⟩, ⟨25, [], [], qq (1573) 1⟩)]

def uM5_1 : List (QPiece × Cert) := [
  (⟨qq (7) 76, qq (13) 140, qq (7) 6, qq (32) 3, qq (1000000000000) 1⟩, ⟨25, [], [], qq (75088) 49⟩),
  (⟨qq (13) 140, qq (7) 75, qq (10) 3, qq (-38) 3, qq (1000000000000) 1⟩, ⟨23, [], [], qq (19600) 13⟩),
  (⟨qq (7) 75, qq (3) 32, qq (13) 6, qq (-1) 6, qq (1000000000000) 1⟩, ⟨23, [], [], qq (73125) 49⟩),
  (⟨qq (3) 32, qq (13) 138, qq (7) 6, qq (21) 2, qq (1000000000000) 1⟩, ⟨23, [], [], qq (13312) 9⟩),
  (⟨qq (13) 138, qq (2) 21, qq (10) 3, qq (-25) 2, qq (1000000000000) 1⟩, ⟨22, [], [], qq (19044) 13⟩),
  (⟨qq (2) 21, qq (7) 72, qq (7) 3, qq (-2) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (5733) 4⟩),
  (⟨qq (7) 72, qq (13) 132, qq (7) 6, qq (10) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (67392) 49⟩),
  (⟨qq (13) 132, qq (1) 10, qq (10) 3, qq (-12) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (17424) 13⟩),
  (⟨qq (1) 10, qq (13) 128, qq (7) 6, qq (29) 3, qq (1000000000000) 1⟩, ⟨25, [], [], qq (1300) 1⟩),
  (⟨qq (13) 128, qq (13) 126, qq (9) 4, qq (-1) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (16384) 13⟩)]

def uM5_2 : List (QPiece × Cert) := [
  (⟨qq (13) 126, qq (2) 19, qq (10) 3, qq (-23) 2, qq (1000000000000) 1⟩, ⟨22, [(qq (3) 29)], [], qq (15876) 13⟩),
  (⟨qq (2) 19, qq (7) 66, qq (7) 3, qq (-2) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (4693) 4⟩),
  (⟨qq (7) 66, qq (13) 120, qq (7) 6, qq (9) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (56628) 49⟩),
  (⟨qq (13) 120, qq (7) 64, qq (10) 3, qq (-11) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (14400) 13⟩),
  (⟨qq (7) 64, qq (1) 9, qq (13) 6, qq (-1) 3, qq (1000000000000) 1⟩, ⟨21, [], [], qq (53248) 49⟩),
  (⟨qq (1) 9, qq (13) 116, qq (7) 6, qq (26) 3, qq (1000000000000) 1⟩, ⟨25, [], [], qq (1053) 1⟩),
  (⟨qq (13) 116, qq (13) 114, qq (9) 4, qq (-1) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (13456) 13⟩),
  (⟨qq (13) 114, qq (7) 60, qq (10) 3, qq (-21) 2, qq (1000000000000) 1⟩, ⟨22, [(qq (3) 26)], [], qq (12996) 13⟩),
  (⟨qq (7) 60, qq (2) 17, qq (13) 6, qq (-1) 2, qq (1000000000000) 1⟩, ⟨22, [], [], qq (46800) 49⟩),
  (⟨qq (2) 17, qq (13) 108, qq (7) 6, qq (8) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (3757) 4⟩)]

def uM5_3 : List (QPiece × Cert) := [
  (⟨qq (13) 108, qq (7) 58, qq (10) 3, qq (-10) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (11664) 13⟩),
  (⟨qq (7) 58, qq (1) 8, qq (13) 6, qq (-1) 3, qq (1000000000000) 1⟩, ⟨21, [], [], qq (43732) 49⟩),
  (⟨qq (1) 8, qq (13) 102, qq (9) 4, qq (-1) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (832) 1⟩),
  (⟨qq (13) 102, qq (7) 54, qq (10) 3, qq (-19) 2, qq (1000000000000) 1⟩, ⟨22, [], [], qq (10404) 13⟩),
  (⟨qq (7) 54, qq (2) 15, qq (13) 6, qq (-1) 2, qq (1000000000000) 1⟩, ⟨22, [(qq (3) 23)], [], qq (37908) 49⟩),
  (⟨qq (2) 15, qq (13) 96, qq (7) 6, qq (7) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (2925) 4⟩),
  (⟨qq (13) 96, qq (13) 90, qq (9) 4, qq (-1) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (9216) 13⟩),
  (⟨qq (13) 90, qq (7) 48, qq (10) 3, qq (-17) 2, qq (1000000000000) 1⟩, ⟨22, [], [], qq (8100) 13⟩),
  (⟨qq (7) 48, qq (2) 13, qq (13) 6, qq (-1) 2, qq (1000000000000) 1⟩, ⟨22, [(qq (3) 20)], [], qq (29952) 49⟩),
  (⟨qq (2) 13, qq (13) 84, qq (7) 6, qq (6) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (2197) 4⟩)]

def uM5_4 : List (QPiece × Cert) := [
  (⟨qq (13) 84, qq (1) 6, qq (9) 4, qq (-1) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (7056) 13⟩),
  (⟨qq (1) 6, qq (7) 39, qq (13) 6, qq (-1) 2, qq (1000000000000) 1⟩, ⟨22, [(qq (7) 40)], [], qq (468) 1⟩),
  (⟨qq (7) 39, qq (13) 72, qq (1) 1, qq (6) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (19773) 49⟩),
  (⟨qq (13) 72, qq (13) 66, qq (25) 12, qq (0) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (5184) 13⟩),
  (⟨qq (13) 66, qq (1) 5, qq (19) 6, qq (-11) 2, qq (1000000000000) 1⟩, ⟨19, [], [], qq (4356) 13⟩),
  (⟨qq (1) 5, qq (7) 33, qq (13) 6, qq (-1) 2, qq (1000000000000) 1⟩, ⟨22, [(qq (7) 34)], [], qq (325) 1⟩),
  (⟨qq (7) 33, qq (13) 60, qq (1) 1, qq (5) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (14157) 49⟩),
  (⟨qq (13) 60, qq (13) 54, qq (25) 12, qq (0) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (3600) 13⟩),
  (⟨qq (13) 54, qq (1) 4, qq (19) 6, qq (-9) 2, qq (1000000000000) 1⟩, ⟨19, [], [], qq (2916) 13⟩),
  (⟨qq (1) 4, qq (7) 27, qq (13) 6, qq (-1) 2, qq (1000000000000) 1⟩, ⟨22, [], [], qq (208) 1⟩)]

def uM5_5 : List (QPiece × Cert) := [
  (⟨qq (7) 27, qq (13) 48, qq (1) 1, qq (4) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (9477) 49⟩),
  (⟨qq (13) 48, qq (3) 11, qq (19) 6, qq (-4) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (2304) 13⟩),
  (⟨qq (3) 11, qq (7) 24, qq (13) 6, qq (-1) 3, qq (1000000000000) 1⟩, ⟨21, [], [], qq (1573) 9⟩),
  (⟨qq (7) 24, qq (13) 44, qq (1) 1, qq (11) 3, qq (1000000000000) 1⟩, ⟨21, [], [], qq (7488) 49⟩),
  (⟨qq (13) 44, qq (13) 42, qq (25) 12, qq (0) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (1936) 13⟩),
  (⟨qq (13) 42, qq (1) 3, qq (19) 6, qq (-7) 2, qq (1000000000000) 1⟩, ⟨19, [(qq (7) 22)], [], qq (1764) 13⟩),
  (⟨qq (1) 3, qq (13) 36, qq (1) 1, qq (3) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (117) 1⟩),
  (⟨qq (13) 36, qq (3) 8, qq (19) 6, qq (-3) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (1296) 13⟩),
  (⟨qq (3) 8, qq (7) 18, qq (13) 6, qq (-1) 3, qq (1000000000000) 1⟩, ⟨21, [], [], qq (832) 9⟩),
  (⟨qq (7) 18, qq (13) 32, qq (1) 1, qq (8) 3, qq (1000000000000) 1⟩, ⟨21, [], [], qq (4212) 49⟩)]

def uM5_6 : List (QPiece × Cert) := [
  (⟨qq (13) 32, qq (13) 30, qq (25) 12, qq (0) 1, qq (1000000000000) 1⟩, ⟨1, [], [], qq (1024) 13⟩),
  (⟨qq (13) 30, qq (7) 15, qq (19) 6, qq (-5) 2, qq (1000000000000) 1⟩, ⟨19, [(qq (7) 16)], [], qq (900) 13⟩),
  (⟨qq (7) 15, qq (1) 2, qq (2) 1, qq (0) 1, qq (1000000000000) 1⟩, ⟨19, [], [], qq (2925) 49⟩),
  (⟨qq (1) 2, qq (13) 24, qq (1) 1, qq (2) 1, qq (1000000000000) 1⟩, ⟨22, [], [], qq (52) 1⟩),
  (⟨qq (13) 24, qq (7) 12, qq (19) 6, qq (-2) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (576) 13⟩),
  (⟨qq (7) 12, qq (3) 5, qq (2) 1, qq (0) 1, qq (1000000000000) 1⟩, ⟨21, [], [], qq (1872) 49⟩),
  (⟨qq (3) 5, qq (13) 20, qq (1) 1, qq (5) 3, qq (1000000000000) 1⟩, ⟨21, [], [], qq (325) 9⟩),
  (⟨qq (13) 20, qq (2) 3, qq (19) 6, qq (-5) 3, qq (1000000000000) 1⟩, ⟨20, [], [], qq (400) 13⟩),
  (⟨qq (2) 3, qq (7) 10, qq (13) 6, qq (-1) 6, qq (1000000000000) 1⟩, ⟨20, [], [], qq (117) 4⟩),
  (⟨qq (7) 10, qq (13) 18, qq (1) 1, qq (3) 2, qq (1000000000000) 1⟩, ⟨13, [], [], qq (54) 1⟩)]

def uM5_7 : List (QPiece × Cert) := [
  (⟨qq (13) 18, qq (7) 9, qq (19) 6, qq (-3) 2, qq (1000000000000) 1⟩, ⟨2, [], [], qq (324) 13⟩),
  (⟨qq (7) 9, qq (1) 1, qq (13) 3, qq (-3) 1, qq (1000000000000) 1⟩, ⟨2, [], [], qq (1053) 49⟩),
  (⟨qq (1) 1, qq (7) 6, qq (10) 3, qq (-2) 1, qq (1000000000000) 1⟩, ⟨3, [], [], qq (13) 1⟩),
  (⟨qq (7) 6, qq (2) 1, qq (13) 6, qq (-1) 1, qq (1000000000000) 1⟩, ⟨3, [], [], qq (12) 1⟩),
  (⟨qq (2) 1, qq (7) 3, qq (7) 6, qq (-1) 2, qq (1000000000000) 1⟩, ⟨4, [], [], qq (13) 4⟩),
  (⟨qq (7) 3, qq (9) 1, qq (0) 1, qq (0) 1, qq (1000000000000) 1⟩, ⟨4, [], [], qq (3) 1⟩)]

theorem uM5_0_ok : kpieceAll eHeadM.toK 5 uM5_0 = true := by
  -- kcost: 1.0 s measured, 10 pieces
  decide +kernel

theorem uM5_1_ok : kpieceAll eHeadM.toK 5 uM5_1 = true := by
  -- kcost: 1.0 s measured, 10 pieces
  decide +kernel

theorem uM5_2_ok : kpieceAll eHeadM.toK 5 uM5_2 = true := by
  -- kcost: 1.0 s measured, 10 pieces
  decide +kernel

theorem uM5_3_ok : kpieceAll eHeadM.toK 5 uM5_3 = true := by
  -- kcost: 1.0 s measured, 10 pieces
  decide +kernel

theorem uM5_4_ok : kpieceAll eHeadM.toK 5 uM5_4 = true := by
  -- kcost: 1.0 s measured, 10 pieces
  decide +kernel

theorem uM5_5_ok : kpieceAll eHeadM.toK 5 uM5_5 = true := by
  -- kcost: 1.0 s measured, 10 pieces
  decide +kernel

theorem uM5_6_ok : kpieceAll eHeadM.toK 5 uM5_6 = true := by
  -- kcost: 1.0 s measured, 10 pieces
  decide +kernel

theorem uM5_7_ok : kpieceAll eHeadM.toK 5 uM5_7 = true := by
  -- kcost: 1.0 s measured, 6 pieces
  decide +kernel

def hM5 : List (QPiece × Cert) := uM5_0 ++ (uM5_1 ++ (uM5_2 ++ (uM5_3 ++ (uM5_4 ++ (uM5_5 ++ (uM5_6 ++ (uM5_7)))))))

theorem hM5_ok : kpieceAll eHeadM.toK 5 hM5 = true := by
  unfold hM5
  simp only [kpieceAll_append, uM5_0_ok, uM5_1_ok, uM5_2_ok, uM5_3_ok, uM5_4_ok, uM5_5_ok, uM5_6_ok, uM5_7_ok, Bool.and_self]

def tM1 : KTmplC := ⟨qq 1 396, 32, cells1, hM1, 5⟩
def tM5 : KTmplC := ⟨qq 1 396, 32, cells5, hM5, 5⟩

/-- The closed content bank of the dip frame on the support. -/
def bankM : KBankDataC := { eHeadM with Λ := dipLamM, tmpls := [(1, tM1), (5, tM5)] }

theorem bankM_params : kcParams bankM = true := by
  -- kcost: 1.0 s measured (a dozen comparisons)
  decide +kernel

theorem bankM_head1 : ktmplHead bankM.toK 1 (tM1.toK bankM.α) = true := by
  -- kcost: 1.0 s measured (chain, tail test and end of the head pieces of a class)
  exact ktmplHead_toK_of (e0 := qq 1 12) (by decide +kernel) (by decide +kernel) exp1_chain exp1_end
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bankM_head5 : ktmplHead bankM.toK 5 (tM5.toK bankM.α) = true := by
  -- kcost: 1.0 s measured (chain, tail test and end of the head pieces of a class)
  exact ktmplHead_toK_of (e0 := qq 1 12) (by decide +kernel) (by decide +kernel) exp5_chain exp5_end
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bankM_heads : kcHeads bankM = true := by
  unfold kcHeads
  show [(1, tM1), (5, tM5)].all (fun x => ktmplHead bankM.toK x.1 (x.2.toK bankM.α) && decide (1 ≤ x.2.N)) = true
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨bankM_head1, by decide⟩, ⟨bankM_head5, by decide⟩⟩

theorem bankM_kappa : kappaOf bankM.toK 1 0 = qq 1 3 ∧ kappaOf bankM.toK 1 1 = qq 1 2 ∧
    kappaOf bankM.toK 5 0 = qq 2 3 ∧ kappaOf bankM.toK 5 1 = qq 1 2 := by
  -- kcost: 1.0 s measured (four pole positions)
  decide +kernel

theorem bankM_cells : kcCells bankM = true := by
  obtain ⟨k10, k11, k50, k51⟩ := bankM_kappa
  unfold kcCells
  show [(1, tM1), (5, tM5)].all (fun x => x.2.cells.all (fun c =>
    c.ok bankM.α (kappaOf bankM.toK x.1 0) (kappaOf bankM.toK x.1 1))) = true
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  rw [k10, k11, k50, k51]
  exact ⟨cells1_ok, cells5_ok⟩

theorem bankM_pieces : kcPieces bankM = true := by
  unfold kcPieces
  show [(1, tM1), (5, tM5)].all (fun x => kpieceAll bankM.toK x.1 x.2.head) = true
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨hM1_ok, hM5_ok⟩

theorem bankM_mass : ((tM1.toK bankM.α).toQ.mass bankM.toK.α0 + (tM5.toK bankM.α).toQ.mass bankM.toK.α0 =
    bankM.toK.Λ * 2) := by
  rw [KTmplC.mass_toK, KTmplC.mass_toK]
  rw [show (tM1.expP bankM.α) = expPs (qq 1 12) 32 cells1 from rfl,
    show (tM5.expP bankM.α) = expPs (qq 1 12) 32 cells5 from rfl, exp1_mass, exp5_mass]
  -- kcost: 1.0 s measured (masses of the head pieces of each class and the final comparison)
  decide +kernel

theorem bankM_class : kcClass bankM = true :=
  kclassOK_six bankM.toK rfl rfl (Or.inr rfl) (T1 := tM1.toK bankM.α) (T5 := tM5.toK bankM.α) rfl rfl
    bankM_mass

/-- **The closed content bank of the dip frame passes `kcheckC`.** -/
theorem bankM_check : kcheckC bankM = true :=
  kcheckC_of bankM_params bankM_heads bankM_cells bankM_pieces bankM_class

theorem bankM_ok : DipBankOK Support.minus 1 (-2) (1) (by norm_num) bankM lnsM brsM where
  check := bankM_check
  shifts := rfl
  alpha := by norm_num [planeC, bankM, eHeadM, planeHeadC, qq]
  hlns := lnsM_ok
  hbr := brsM_ok
  cat := dipCat_mem Support.minus.rho lnsM brsM presM
  hQ := by decide
  hP := by decide
  hM := by decide
  ht0 := by norm_num [bankM, eHeadM, planeHeadC, qq]
  hα0 := by norm_num [bankM, eHeadM, planeHeadC, qq]
  hcF := by decide
  hdepth := planeDepth_le

theorem bankM_eta : (dipLamM : ℚ) < Dp1.Dt := by
  -- kcost: 1.0 s measured (one rational comparison)
  decide +kernel

theorem bankM_mu : Dp1.ccert / (Dp1.Dt - dipLamM) ≤ (15359 / 1000 : ℚ) := by
  -- kcost: 1.0 s measured (one rational division and comparison against Dp1)
  decide +kernel

/-- **μ(L(2, χ₋₃) + (1/27) π²) ≤ 15.359**, and the number is irrational (dip frame (1, -2, 1), support `Support.minus`). -/
theorem dip_1_27_plus_measure :
    MeasureLBAt (chi3L2 + (((1 / 27 : ℚ) : ℚ) : ℝ) * Real.pi ^ 2) (((15359 / 1000 : ℚ) : ℚ) : ℝ) ∧
      Irrational (chi3L2 + (((1 / 27 : ℚ) : ℚ) : ℝ) * Real.pi ^ 2) := by
  have h := dip_point Support.minus 1 (-2) (1) (by norm_num) (by norm_num) (by norm_num) (by norm_num) bankM_ok bankM_eta
    (by decide +kernel) (B := (15359 / 1000 : ℚ)) bankM_mu
  have ht : planeT Support.minus 1 (-2) = (1 / 27 : ℚ) := by
    simp only [planeT, Support.sgn]
    norm_num
  rw [ht] at h
  exact h

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.F127

#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Data.F127.bankM_check
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Data.F127.dip_1_27_plus_measure
