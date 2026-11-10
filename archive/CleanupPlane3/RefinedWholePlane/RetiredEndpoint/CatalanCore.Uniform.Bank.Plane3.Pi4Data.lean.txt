module

public import CatalanCore.Uniform.Bank.Plane3.Data
public import CatalanCore.Uniform.Support.HPoleRefinedCatalogue

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! Dedicated pure endpoint content bank. The entire accepted decay cover and
the two periodic low cells are reused. Each new complete affine head check is
separate; boundary bridges charge their actual mass. -/
namespace CatalanCore.Uniform.Bank.Plane3
open CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore.Uniform.Support

def pi4Chambers : List ℕ := [2,3,4,5,6,7,8,9,10]
def pi4Catalogue : List KBranch := HPolePeriodRows.refinedCatalogue 4 pi4Chambers

def pi4Piece0 : QPiece := ⟨(1/40 : ℚ), (1/30 : ℚ), (425001/100000 : ℚ), (-2 : ℚ), plane3Slack⟩
def pi4Cert0 : Cert := ⟨0, [], [], plane3Threshold⟩

def pi4Piece1 : QPiece := ⟨(1/30 : ℚ), (1/20 : ℚ), (415001/100000 : ℚ), (1 : ℚ), plane3Slack⟩
def pi4Cert1 : Cert := ⟨0, [], [], plane3Threshold⟩

def pi4Piece2 : QPiece := ⟨(1/20 : ℚ), (1/10 : ℚ), (425001/100000 : ℚ), (-1 : ℚ), plane3Slack⟩
def pi4Cert2 : Cert := ⟨0, [], [], plane3Threshold⟩

def pi4Piece3 : QPiece := ⟨(1/10 : ℚ), (21/200 : ℚ), (205001/100000 : ℚ), (20 : ℚ), plane3Slack⟩
def pi4Cert3 : Cert := ⟨30, [], [], plane3Threshold⟩

def pi4Piece4 : QPiece := ⟨(21/200 : ℚ), (1099999/10000000 : ℚ), (625001/100000 : ℚ), (-20 : ℚ), plane3Slack⟩
def pi4Cert4 : Cert := ⟨31, [], [], plane3Threshold⟩

def pi4Piece5 : QPiece := ⟨(1099999/10000000 : ℚ), (11/100 : ℚ), (415001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert5 : Cert := ⟨0, [], [], plane3Threshold⟩

def pi4Piece6 : QPiece := ⟨(11/100 : ℚ), (1/9 : ℚ), (405001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert6 : Cert := ⟨29, [], [], plane3Threshold⟩

def pi4Piece7 : QPiece := ⟨(1/9 : ℚ), (7/60 : ℚ), (205001/100000 : ℚ), (18 : ℚ), plane3Slack⟩
def pi4Cert7 : Cert := ⟨27, [], [], plane3Threshold⟩

def pi4Piece8 : QPiece := ⟨(7/60 : ℚ), (10999991/90000000 : ℚ), (625001/100000 : ℚ), (-18 : ℚ), plane3Slack⟩
def pi4Cert8 : Cert := ⟨28, [], [], plane3Threshold⟩

def pi4Piece9 : QPiece := ⟨(10999991/90000000 : ℚ), (11/90 : ℚ), (415001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert9 : Cert := ⟨0, [], [], plane3Threshold⟩

def pi4Piece10 : QPiece := ⟨(11/90 : ℚ), (1/8 : ℚ), (405001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert10 : Cert := ⟨26, [], [], plane3Threshold⟩

def pi4Piece11 : QPiece := ⟨(1/8 : ℚ), (21/160 : ℚ), (205001/100000 : ℚ), (16 : ℚ), plane3Slack⟩
def pi4Cert11 : Cert := ⟨24, [], [], plane3Threshold⟩

def pi4Piece12 : QPiece := ⟨(21/160 : ℚ), (1374999/10000000 : ℚ), (625001/100000 : ℚ), (-16 : ℚ), plane3Slack⟩
def pi4Cert12 : Cert := ⟨25, [], [], plane3Threshold⟩

def pi4Piece13 : QPiece := ⟨(1374999/10000000 : ℚ), (11/80 : ℚ), (415001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert13 : Cert := ⟨0, [], [], plane3Threshold⟩

def pi4Piece14 : QPiece := ⟨(11/80 : ℚ), (1/7 : ℚ), (405001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert14 : Cert := ⟨23, [], [], plane3Threshold⟩

def pi4Piece15 : QPiece := ⟨(1/7 : ℚ), (3/20 : ℚ), (205001/100000 : ℚ), (14 : ℚ), plane3Slack⟩
def pi4Cert15 : Cert := ⟨21, [], [], plane3Threshold⟩

def pi4Piece16 : QPiece := ⟨(3/20 : ℚ), (10999993/70000000 : ℚ), (625001/100000 : ℚ), (-14 : ℚ), plane3Slack⟩
def pi4Cert16 : Cert := ⟨22, [], [], plane3Threshold⟩

def pi4Piece17 : QPiece := ⟨(10999993/70000000 : ℚ), (11/70 : ℚ), (415001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert17 : Cert := ⟨0, [], [], plane3Threshold⟩

def pi4Piece18 : QPiece := ⟨(11/70 : ℚ), (1/6 : ℚ), (405001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert18 : Cert := ⟨20, [], [], plane3Threshold⟩

def pi4Piece19 : QPiece := ⟨(1/6 : ℚ), (7/40 : ℚ), (205001/100000 : ℚ), (12 : ℚ), plane3Slack⟩
def pi4Cert19 : Cert := ⟨18, [], [], plane3Threshold⟩

def pi4Piece20 : QPiece := ⟨(7/40 : ℚ), (5499997/30000000 : ℚ), (625001/100000 : ℚ), (-12 : ℚ), plane3Slack⟩
def pi4Cert20 : Cert := ⟨19, [], [], plane3Threshold⟩

def pi4Piece21 : QPiece := ⟨(5499997/30000000 : ℚ), (11/60 : ℚ), (415001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert21 : Cert := ⟨0, [], [], plane3Threshold⟩

def pi4Piece22 : QPiece := ⟨(11/60 : ℚ), (1/5 : ℚ), (405001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert22 : Cert := ⟨17, [], [], plane3Threshold⟩

def pi4Piece23 : QPiece := ⟨(1/5 : ℚ), (21/100 : ℚ), (205001/100000 : ℚ), (10 : ℚ), plane3Slack⟩
def pi4Cert23 : Cert := ⟨15, [], [], plane3Threshold⟩

def pi4Piece24 : QPiece := ⟨(21/100 : ℚ), (2199999/10000000 : ℚ), (625001/100000 : ℚ), (-10 : ℚ), plane3Slack⟩
def pi4Cert24 : Cert := ⟨16, [], [], plane3Threshold⟩

def pi4Piece25 : QPiece := ⟨(2199999/10000000 : ℚ), (11/50 : ℚ), (415001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert25 : Cert := ⟨0, [], [], plane3Threshold⟩

def pi4Piece26 : QPiece := ⟨(11/50 : ℚ), (1/4 : ℚ), (405001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert26 : Cert := ⟨14, [], [], plane3Threshold⟩

def pi4Piece27 : QPiece := ⟨(1/4 : ℚ), (21/80 : ℚ), (205001/100000 : ℚ), (8 : ℚ), plane3Slack⟩
def pi4Cert27 : Cert := ⟨12, [], [], plane3Threshold⟩

def pi4Piece28 : QPiece := ⟨(21/80 : ℚ), (2749999/10000000 : ℚ), (625001/100000 : ℚ), (-8 : ℚ), plane3Slack⟩
def pi4Cert28 : Cert := ⟨13, [], [], plane3Threshold⟩

def pi4Piece29 : QPiece := ⟨(2749999/10000000 : ℚ), (11/40 : ℚ), (415001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert29 : Cert := ⟨0, [], [], plane3Threshold⟩

def pi4Piece30 : QPiece := ⟨(11/40 : ℚ), (1/3 : ℚ), (405001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert30 : Cert := ⟨11, [], [], plane3Threshold⟩

def pi4Piece31 : QPiece := ⟨(1/3 : ℚ), (7/20 : ℚ), (205001/100000 : ℚ), (6 : ℚ), plane3Slack⟩
def pi4Cert31 : Cert := ⟨9, [], [], plane3Threshold⟩

def pi4Piece32 : QPiece := ⟨(7/20 : ℚ), (10999997/30000000 : ℚ), (625001/100000 : ℚ), (-6 : ℚ), plane3Slack⟩
def pi4Cert32 : Cert := ⟨10, [], [], plane3Threshold⟩

def pi4Piece33 : QPiece := ⟨(10999997/30000000 : ℚ), (11/30 : ℚ), (415001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert33 : Cert := ⟨0, [], [], plane3Threshold⟩

def pi4Piece34 : QPiece := ⟨(11/30 : ℚ), (1/2 : ℚ), (405001/100000 : ℚ), (0 : ℚ), plane3Slack⟩
def pi4Cert34 : Cert := ⟨8, [], [], plane3Threshold⟩

def pi4Piece35 : QPiece := ⟨(1/2 : ℚ), (21/40 : ℚ), (205001/100000 : ℚ), (4 : ℚ), plane3Slack⟩
def pi4Cert35 : Cert := ⟨6, [], [], plane3Threshold⟩

def pi4Piece36 : QPiece := ⟨(21/40 : ℚ), (11/20 : ℚ), (730001/100000 : ℚ), (-6 : ℚ), plane3Slack⟩
def pi4Cert36 : Cert := ⟨2, [], [], plane3Threshold⟩

def pi4Piece37 : QPiece := ⟨(11/20 : ℚ), (1 : ℚ), (840001/100000 : ℚ), (-8 : ℚ), plane3Slack⟩
def pi4Cert37 : Cert := ⟨1, [], [], plane3Threshold⟩

def pi4Piece38 : QPiece := ⟨(1 : ℚ), (880001/800000 : ℚ), (440001/100000 : ℚ), (-4 : ℚ), plane3Slack⟩
def pi4Cert38 : Cert := ⟨3, [(11/10 : ℚ)], [], plane3Threshold⟩

def pi4PCTemplate : KTmplP :=
  ⟨1/40,1,0,[(pi4Piece0, pi4Cert0), (pi4Piece1, pi4Cert1)],
    [(pi4Piece2, pi4Cert2), (pi4Piece3, pi4Cert3), (pi4Piece4, pi4Cert4), (pi4Piece5, pi4Cert5), (pi4Piece6, pi4Cert6), (pi4Piece7, pi4Cert7), (pi4Piece8, pi4Cert8), (pi4Piece9, pi4Cert9), (pi4Piece10, pi4Cert10), (pi4Piece11, pi4Cert11), (pi4Piece12, pi4Cert12), (pi4Piece13, pi4Cert13), (pi4Piece14, pi4Cert14), (pi4Piece15, pi4Cert15), (pi4Piece16, pi4Cert16), (pi4Piece17, pi4Cert17), (pi4Piece18, pi4Cert18), (pi4Piece19, pi4Cert19), (pi4Piece20, pi4Cert20), (pi4Piece21, pi4Cert21), (pi4Piece22, pi4Cert22), (pi4Piece23, pi4Cert23), (pi4Piece24, pi4Cert24), (pi4Piece25, pi4Cert25), (pi4Piece26, pi4Cert26), (pi4Piece27, pi4Cert27), (pi4Piece28, pi4Cert28), (pi4Piece29, pi4Cert29), (pi4Piece30, pi4Cert30), (pi4Piece31, pi4Cert31), (pi4Piece32, pi4Cert32), (pi4Piece33, pi4Cert33), (pi4Piece34, pi4Cert34), (pi4Piece35, pi4Cert35), (pi4Piece36, pi4Cert36), (pi4Piece37, pi4Cert37), (pi4Piece38, pi4Cert38)],4⟩

def pi4Lambda : ℚ := 41076914608111573/12600000000000000
def pi4Bank : KBankData :=
  { plane3Bank 1 with
    Λ := pi4Lambda
    kcat := pi4Catalogue
    tmpls := [(1,pi4PCTemplate.toK 20 84 1)] }

-- kcost: <1s estimated, fixed frame fields and two shifts only.
theorem pi4_params : kcheckParams pi4Bank = true := by decide +kernel
-- kcost: 2s estimated, 39 scalar chain links, existing low-cell transforms, tail fields.
theorem pi4_heads : ktmplHead pi4Bank 1 (pi4PCTemplate.toK 20 84 1) = true := by decide +kernel
-- kcost: 4s estimated, one unit class and 39 exact scalar integrals plus two low transforms.
theorem pi4_class : kclassOK pi4Bank = true := by decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece2_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece2 pi4Cert2 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece3_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece3 pi4Cert3 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece4_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece4 pi4Cert4 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece5_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece5 pi4Cert5 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece6_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece6 pi4Cert6 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece7_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece7 pi4Cert7 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece8_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece8 pi4Cert8 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece9_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece9 pi4Cert9 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece10_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece10 pi4Cert10 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece11_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece11 pi4Cert11 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece12_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece12 pi4Cert12 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece13_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece13 pi4Cert13 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece14_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece14 pi4Cert14 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece15_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece15 pi4Cert15 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece16_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece16 pi4Cert16 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece17_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece17 pi4Cert17 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece18_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece18 pi4Cert18 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece19_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece19 pi4Cert19 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece20_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece20 pi4Cert20 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece21_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece21 pi4Cert21 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece22_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece22 pi4Cert22 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece23_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece23 pi4Cert23 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece24_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece24 pi4Cert24 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece25_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece25 pi4Cert25 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece26_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece26 pi4Cert26 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece27_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece27 pi4Cert27 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece28_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece28 pi4Cert28 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece29_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece29 pi4Cert29 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece30_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece30 pi4Cert30 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece31_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece31 pi4Cert31 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece32_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece32 pi4Cert32 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece33_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece33 pi4Cert33 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece34_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece34 pi4Cert34 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece35_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece35 pi4Cert35 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece36_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece36 pi4Cert36 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece37_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece37 pi4Cert37 = true := by
  decide +kernel

-- kcost: <2s estimated, one affine head, <=6 conditions, fixed rational thresholds.
theorem pi4Piece38_check :
    pieceOK (pi4Bank.cat 1) 2 (1/20) (1/2) 1 1 2 pi4Piece38 pi4Cert38 = true := by
  decide +kernel

private theorem pi4_strip_depth (cat : List Branch)
    (hz : ∀ br ∈ cat,br.debit=0) (q : ℕ) (α κ : ℚ) (depth : ℕ)
    (P : QPiece) (br : Branch) (R e : ℚ) (st : Strip) :
    stripOK cat q α κ depth P br R e st = stripOK cat q α κ 0 P br R e st := by
  unfold stripOK
  cases h : nth cat st.yi with
  | none => rfl
  | some y =>
    have hy := hz y (nth_mem cat st.yi h)
    simp only [hy,Nat.zero_mul,zero_mul,Nat.cast_zero,add_zero]

private theorem pi4_piece_depth (cat : List Branch)
    (hz : ∀ br ∈ cat,br.debit=0) (q : ℕ) (α κ : ℚ) (depth cF Pbad : ℕ)
    (P : QPiece) (cert : Cert) :
    pieceOK cat q α κ depth cF Pbad P cert = pieceOK cat q α κ 0 cF Pbad P cert := by
  unfold pieceOK
  cases h : nth cat cert.bi with
  | none => rfl
  | some br =>
    have hb := hz br (nth_mem cat cert.bi h)
    simp only [hb,Nat.zero_mul,zero_mul,Nat.cast_zero,add_zero]
    simp_rw [pi4_strip_depth cat hz q α κ depth]

private theorem pi4_low_depth (y : QPiece × Cert)
    (h : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 1 20 64 y = true) :
    cellOKb pi4Bank plane3BaseCatalogue 1 1 20 64 y = true := by
  have hz : ∀ br ∈ plane3BaseCatalogue.map
      (KBranch.compile pi4Bank.tS (pi4Bank.bS 1) pi4Bank.cS),br.debit=0 := by
    intro br hb
    obtain ⟨b,hmem,heq⟩ := List.mem_map.mp hb
    subst br
    simp only [plane3BaseCatalogue,List.mem_singleton] at hmem
    subst b
    rfl
  unfold cellOKb
  change (pieceOK _ 2 (1/20) (1/2) 1 1 2 y.1 y.2 && _) = true
  rw [pi4_piece_depth _ hz]
  exact h

-- Reuse source-bound low-cell acceptance; only zero-debit depth changes.
theorem pi4_cell0 : cellOKb pi4Bank plane3BaseCatalogue 1 1 20 64
    (pi4Piece0,pi4Cert0) = true := by exact pi4_low_depth _ plane3_cell0
theorem pi4_cell1 : cellOKb pi4Bank plane3BaseCatalogue 1 1 20 64
    (pi4Piece1,pi4Cert1) = true := by exact pi4_low_depth _ plane3_cell1

-- kcost: <1s estimated, exact scalar comparisons only.
theorem pi4_mass_bound : pi4Lambda ≤ 32604/10000 := by decide +kernel
end CatalanCore.Uniform.Bank.Plane3
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4_params
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4_heads
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4_class
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece2_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece3_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece4_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece5_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece6_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece7_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece8_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece9_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece10_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece11_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece12_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece13_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece14_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece15_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece16_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece17_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece18_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece19_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece20_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece21_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece22_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece23_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece24_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece25_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece26_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece27_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece28_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece29_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece30_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece31_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece32_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece33_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece34_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece35_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece36_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece37_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4Piece38_check
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4_cell0
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4_cell1
#print axioms CatalanCore.Uniform.Bank.Plane3.pi4_mass_bound
