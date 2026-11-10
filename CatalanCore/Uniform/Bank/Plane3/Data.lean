module

public import CatalanCore.Uniform.Content.BankShared.KTerm.Periodic
public import CatalanCore.Uniform.Support.HPoleRefinedCatalogue

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! Coefficient-free refined full-plane content bank. All arithmetic coefficients
and finite depths are parameters of the consumer. Each actual scalar check is
separate; no pure endpoint or decay witness is copied. -/
namespace CatalanCore.Uniform.Bank.Plane3
open CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore.Uniform.Support

def firstBranch : KBranch :=
  ⟨.tsub (.smul 4 (.add .vr .vm)) (.dist .vm), [], 0⟩
def secondBranch : KBranch :=
  ⟨.smul 8 (.tsub (.add .vr .vm) .vp), [⟨1,-1,0,[],0,false⟩], 0⟩
def thirdBranch : KBranch :=
  ⟨.tsub (.add (.smul 7 .vr) (.smul 6 .vm)) (.smul 6 .vp),
    [⟨1,-1,0,[],0,false⟩, ⟨-1,2,0,[],0,false⟩,
     ⟨0,1,-2,[],0,false⟩, ⟨-1,3,-2,[],0,false⟩], 0⟩
def fourthBranch : KBranch :=
  ⟨.smul 4 (.tsub (.add .vr (.smul 2 .vm)) .vp), [⟨-1,1,0,[],0,false⟩], 0⟩
def zeroBranch : KBranch := ⟨.cst 0, [⟨-1,1,-2,[],0,false⟩], 0⟩

def plane3Chambers : List ℕ := [2,3,4,5,6,7,8]
def plane3Catalogue : List KBranch := HPolePeriodRows.refinedCatalogue 4 plane3Chambers
def plane3BaseCatalogue : List KBranch := [firstBranch]
def plane3Slack : ℚ := 10000000000000000000000000
def plane3Threshold : ℚ := 10000000000

def contentPiece0 : QPiece := ⟨(13/400 : ℚ),(13/300 : ℚ),(432501/100000 : ℚ),(-2 : ℚ),plane3Slack⟩
def contentCert0 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece1 : QPiece := ⟨(13/300 : ℚ),(13/200 : ℚ),(419501/100000 : ℚ),(1 : ℚ),plane3Slack⟩
def contentCert1 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece2 : QPiece := ⟨(13/200 : ℚ),(13/100 : ℚ),(432501/100000 : ℚ),(-1 : ℚ),plane3Slack⟩
def contentCert2 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece3 : QPiece := ⟨(13/100 : ℚ),(213/1600 : ℚ),(206501/100000 : ℚ),(16 : ℚ),plane3Slack⟩
def contentCert3 : Cert := ⟨24,[],[],plane3Threshold⟩

def contentPiece4 : QPiece := ⟨(213/1600 : ℚ),(1412499/10000000 : ℚ),(632501/100000 : ℚ),(-16 : ℚ),plane3Slack⟩
def contentCert4 : Cert := ⟨25,[],[],plane3Threshold⟩

def contentPiece5 : QPiece := ⟨(1412499/10000000 : ℚ),(113/800 : ℚ),(419501/100000 : ℚ),(0 : ℚ),plane3Slack⟩
def contentCert5 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece6 : QPiece := ⟨(113/800 : ℚ),(1/7 : ℚ),(406501/100000 : ℚ),(0 : ℚ),plane3Slack⟩
def contentCert6 : Cert := ⟨23,[],[],plane3Threshold⟩

def contentPiece7 : QPiece := ⟨(1/7 : ℚ),(213/1400 : ℚ),(206501/100000 : ℚ),(14 : ℚ),plane3Slack⟩
def contentCert7 : Cert := ⟨21,[],[],plane3Threshold⟩

def contentPiece8 : QPiece := ⟨(213/1400 : ℚ),(11299993/70000000 : ℚ),(632501/100000 : ℚ),(-14 : ℚ),plane3Slack⟩
def contentCert8 : Cert := ⟨22,[],[],plane3Threshold⟩

def contentPiece9 : QPiece := ⟨(11299993/70000000 : ℚ),(113/700 : ℚ),(419501/100000 : ℚ),(0 : ℚ),plane3Slack⟩
def contentCert9 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece10 : QPiece := ⟨(113/700 : ℚ),(1/6 : ℚ),(406501/100000 : ℚ),(0 : ℚ),plane3Slack⟩
def contentCert10 : Cert := ⟨20,[],[],plane3Threshold⟩

def contentPiece11 : QPiece := ⟨(1/6 : ℚ),(71/400 : ℚ),(206501/100000 : ℚ),(12 : ℚ),plane3Slack⟩
def contentCert11 : Cert := ⟨18,[],[],plane3Threshold⟩

def contentPiece12 : QPiece := ⟨(71/400 : ℚ),(5649997/30000000 : ℚ),(632501/100000 : ℚ),(-12 : ℚ),plane3Slack⟩
def contentCert12 : Cert := ⟨19,[],[],plane3Threshold⟩

def contentPiece13 : QPiece := ⟨(5649997/30000000 : ℚ),(113/600 : ℚ),(419501/100000 : ℚ),(0 : ℚ),plane3Slack⟩
def contentCert13 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece14 : QPiece := ⟨(113/600 : ℚ),(1/5 : ℚ),(406501/100000 : ℚ),(0 : ℚ),plane3Slack⟩
def contentCert14 : Cert := ⟨17,[],[],plane3Threshold⟩

def contentPiece15 : QPiece := ⟨(1/5 : ℚ),(213/1000 : ℚ),(206501/100000 : ℚ),(10 : ℚ),plane3Slack⟩
def contentCert15 : Cert := ⟨15,[],[],plane3Threshold⟩

def contentPiece16 : QPiece := ⟨(213/1000 : ℚ),(2259999/10000000 : ℚ),(632501/100000 : ℚ),(-10 : ℚ),plane3Slack⟩
def contentCert16 : Cert := ⟨16,[],[],plane3Threshold⟩

def contentPiece17 : QPiece := ⟨(2259999/10000000 : ℚ),(113/500 : ℚ),(419501/100000 : ℚ),(0 : ℚ),plane3Slack⟩
def contentCert17 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece18 : QPiece := ⟨(113/500 : ℚ),(1/4 : ℚ),(406501/100000 : ℚ),(0 : ℚ),plane3Slack⟩
def contentCert18 : Cert := ⟨14,[],[],plane3Threshold⟩

def contentPiece19 : QPiece := ⟨(1/4 : ℚ),(213/800 : ℚ),(206501/100000 : ℚ),(8 : ℚ),plane3Slack⟩
def contentCert19 : Cert := ⟨12,[],[],plane3Threshold⟩

def contentPiece20 : QPiece := ⟨(213/800 : ℚ),(2824999/10000000 : ℚ),(632501/100000 : ℚ),(-8 : ℚ),plane3Slack⟩
def contentCert20 : Cert := ⟨13,[],[],plane3Threshold⟩

def contentPiece21 : QPiece := ⟨(2824999/10000000 : ℚ),(113/400 : ℚ),(419501/100000 : ℚ),(0 : ℚ),plane3Slack⟩
def contentCert21 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece22 : QPiece := ⟨(113/400 : ℚ),(1/3 : ℚ),(406501/100000 : ℚ),(0 : ℚ),plane3Slack⟩
def contentCert22 : Cert := ⟨11,[],[],plane3Threshold⟩

def contentPiece23 : QPiece := ⟨(1/3 : ℚ),(71/200 : ℚ),(206501/100000 : ℚ),(6 : ℚ),plane3Slack⟩
def contentCert23 : Cert := ⟨9,[],[],plane3Threshold⟩

def contentPiece24 : QPiece := ⟨(71/200 : ℚ),(11299997/30000000 : ℚ),(632501/100000 : ℚ),(-6 : ℚ),plane3Slack⟩
def contentCert24 : Cert := ⟨10,[],[],plane3Threshold⟩

def contentPiece25 : QPiece := ⟨(11299997/30000000 : ℚ),(113/300 : ℚ),(419501/100000 : ℚ),(0 : ℚ),plane3Slack⟩
def contentCert25 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece26 : QPiece := ⟨(113/300 : ℚ),(1/2 : ℚ),(406501/100000 : ℚ),(0 : ℚ),plane3Slack⟩
def contentCert26 : Cert := ⟨8,[],[],plane3Threshold⟩

def contentPiece27 : QPiece := ⟨(1/2 : ℚ),(213/400 : ℚ),(206501/100000 : ℚ),(4 : ℚ),plane3Slack⟩
def contentCert27 : Cert := ⟨6,[],[],plane3Threshold⟩

def contentPiece28 : QPiece := ⟨(213/400 : ℚ),(113/200 : ℚ),(739001/100000 : ℚ),(-6 : ℚ),plane3Slack⟩
def contentCert28 : Cert := ⟨2,[],[],plane3Threshold⟩

def contentPiece29 : QPiece := ⟨(113/200 : ℚ),(1 : ℚ),(852001/100000 : ℚ),(-8 : ℚ),plane3Slack⟩
def contentCert29 : Cert := ⟨1,[],[],plane3Threshold⟩

def contentPiece30 : QPiece := ⟨(1 : ℚ),(904001/800000 : ℚ),(452001/100000 : ℚ),(-4 : ℚ),plane3Slack⟩
def contentCert30 : Cert := ⟨3,[(113/100 : ℚ)],[],plane3Threshold⟩

def plane3PCTemplate : KTmplP :=
  ⟨13/400,1,0,[(contentPiece0,contentCert0), (contentPiece1,contentCert1)],
    [(contentPiece2,contentCert2), (contentPiece3,contentCert3), (contentPiece4,contentCert4), (contentPiece5,contentCert5), (contentPiece6,contentCert6), (contentPiece7,contentCert7), (contentPiece8,contentCert8), (contentPiece9,contentCert9), (contentPiece10,contentCert10), (contentPiece11,contentCert11), (contentPiece12,contentCert12), (contentPiece13,contentCert13), (contentPiece14,contentCert14), (contentPiece15,contentCert15), (contentPiece16,contentCert16), (contentPiece17,contentCert17), (contentPiece18,contentCert18), (contentPiece19,contentCert19), (contentPiece20,contentCert20), (contentPiece21,contentCert21), (contentPiece22,contentCert22), (contentPiece23,contentCert23), (contentPiece24,contentCert24), (contentPiece25,contentCert25), (contentPiece26,contentCert26), (contentPiece27,contentCert27), (contentPiece28,contentCert28), (contentPiece29,contentCert29), (contentPiece30,contentCert30)],4⟩
def plane3Lambda : ℚ := 14069082037637989/4200000000000000
def plane3Bank (depth : ℕ) : KBankData where
  Q := 2
  M := 2
  α := 13/200
  a := 1
  shifts := [⟨2,1,1⟩,⟨2,1,1⟩]
  depth := depth
  cF := 1
  Pbad := 2
  α0 := 426001/100000
  τ := 2
  Λ := plane3Lambda
  α0b := 426001/100000
  t0 := 13/400
  Rt := plane3Threshold
  kcat := plane3Catalogue
  tmpls := [(1,plane3PCTemplate.toK 200 852 1)]

-- kcost: 1 s estimated, fixed frame and two shifts.
theorem plane3_params : kcheckParams (plane3Bank 0) = true := by -- kcost: 1 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel
-- kcost: 2 s estimated,31 scalar chain links/tail and actual low transforms.
theorem plane3_heads : ktmplHead (plane3Bank 0) 1 (plane3PCTemplate.toK 200 852 1) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel
-- kcost: 4 s estimated, single unit class and31 exact scalar integrals.
theorem plane3_class : kclassOK (plane3Bank 0) = true := by -- kcost: 4 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece2_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece2 contentCert2 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece3_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece3 contentCert3 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece4_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece4 contentCert4 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece5_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece5 contentCert5 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece6_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece6 contentCert6 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece7_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece7 contentCert7 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece8_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece8 contentCert8 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece9_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece9 contentCert9 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece10_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece10 contentCert10 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece11_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece11 contentCert11 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece12_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece12 contentCert12 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece13_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece13 contentCert13 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece14_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece14 contentCert14 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece15_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece15 contentCert15 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece16_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece16 contentCert16 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece17_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece17 contentCert17 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece18_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece18 contentCert18 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece19_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece19 contentCert19 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece20_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece20 contentCert20 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece21_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece21 contentCert21 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece22_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece22 contentCert22 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece23_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece23 contentCert23 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece24_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece24 contentCert24 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece25_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece25 contentCert25 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece26_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece26 contentCert26 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece27_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece27 contentCert27 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece28_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece28 contentCert28 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece29_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece29 contentCert29 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece30_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece30 contentCert30 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell0 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 1 200 232
    (contentPiece0,contentCert0) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell1 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 1 200 232
    (contentPiece1,contentCert1) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel

end CatalanCore.Uniform.Bank.Plane3
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_params
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_heads
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_class
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece2_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece3_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece4_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece5_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece6_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece7_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece8_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece9_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece10_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece11_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece12_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece13_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece14_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece15_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece16_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece17_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece18_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece19_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece20_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece21_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece22_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece23_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece24_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece25_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece26_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece27_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece28_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece29_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece30_check
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell0
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell1
