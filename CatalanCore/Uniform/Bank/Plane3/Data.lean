module

public import CatalanCore.Uniform.Content.BankShared.KTerm.Periodic
public import CatalanCore.Uniform.Support.HPoleRefinedCatalogue
public import CatalanCore.Uniform.Bank.Common.Schema

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! Coefficient-free refined full-plane content bank. All arithmetic coefficients
and finite depths are parameters of the consumer. Each actual scalar check is
separate; no pure endpoint or decay witness is copied. The 26 base cells
`contentPiece0`-`25` resolve the teeth n = 1..13 of the sawtooth (one period of 1/θ,
b = 200); the three translate strips of the template cover n = 14..39. The 29 head
pieces `contentPiece26`-`54` use ε = 10⁻⁸ and δ = 10⁻⁹. All rationals are `raw_ints%`
numerator/denominator pairs. -/
namespace CatalanCore.Uniform.Bank.Plane3
open CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore.Uniform.Support
open CatalanCore.Uniform.Bank.Common

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


def contentPiece0 : QPiece := ⟨q1 (raw_ints% [13, 2800]),q1 (raw_ints% [13, 2700]),q1 (raw_ints% [432500001, 100000000]),q1 (raw_ints% [-14, 1]),plane3Slack⟩
def contentCert0 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece1 : QPiece := ⟨q1 (raw_ints% [13, 2700]),q1 (raw_ints% [1, 200]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [13, 1]),plane3Slack⟩
def contentCert1 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece2 : QPiece := ⟨q1 (raw_ints% [1, 200]),q1 (raw_ints% [13, 2500]),q1 (raw_ints% [432500001, 100000000]),q1 (raw_ints% [-13, 1]),plane3Slack⟩
def contentCert2 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece3 : QPiece := ⟨q1 (raw_ints% [13, 2500]),q1 (raw_ints% [13, 2400]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [12, 1]),plane3Slack⟩
def contentCert3 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece4 : QPiece := ⟨q1 (raw_ints% [13, 2400]),q1 (raw_ints% [13, 2300]),q1 (raw_ints% [432500001, 100000000]),q1 (raw_ints% [-12, 1]),plane3Slack⟩
def contentCert4 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece5 : QPiece := ⟨q1 (raw_ints% [13, 2300]),q1 (raw_ints% [13, 2200]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [11, 1]),plane3Slack⟩
def contentCert5 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece6 : QPiece := ⟨q1 (raw_ints% [13, 2200]),q1 (raw_ints% [13, 2100]),q1 (raw_ints% [432500001, 100000000]),q1 (raw_ints% [-11, 1]),plane3Slack⟩
def contentCert6 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece7 : QPiece := ⟨q1 (raw_ints% [13, 2100]),q1 (raw_ints% [13, 2000]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [10, 1]),plane3Slack⟩
def contentCert7 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece8 : QPiece := ⟨q1 (raw_ints% [13, 2000]),q1 (raw_ints% [13, 1900]),q1 (raw_ints% [432500001, 100000000]),q1 (raw_ints% [-10, 1]),plane3Slack⟩
def contentCert8 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece9 : QPiece := ⟨q1 (raw_ints% [13, 1900]),q1 (raw_ints% [13, 1800]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [9, 1]),plane3Slack⟩
def contentCert9 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece10 : QPiece := ⟨q1 (raw_ints% [13, 1800]),q1 (raw_ints% [13, 1700]),q1 (raw_ints% [432500001, 100000000]),q1 (raw_ints% [-9, 1]),plane3Slack⟩
def contentCert10 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece11 : QPiece := ⟨q1 (raw_ints% [13, 1700]),q1 (raw_ints% [13, 1600]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [8, 1]),plane3Slack⟩
def contentCert11 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece12 : QPiece := ⟨q1 (raw_ints% [13, 1600]),q1 (raw_ints% [13, 1500]),q1 (raw_ints% [432500001, 100000000]),q1 (raw_ints% [-8, 1]),plane3Slack⟩
def contentCert12 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece13 : QPiece := ⟨q1 (raw_ints% [13, 1500]),q1 (raw_ints% [13, 1400]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [7, 1]),plane3Slack⟩
def contentCert13 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece14 : QPiece := ⟨q1 (raw_ints% [13, 1400]),q1 (raw_ints% [1, 100]),q1 (raw_ints% [432500001, 100000000]),q1 (raw_ints% [-7, 1]),plane3Slack⟩
def contentCert14 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece15 : QPiece := ⟨q1 (raw_ints% [1, 100]),q1 (raw_ints% [13, 1200]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [6, 1]),plane3Slack⟩
def contentCert15 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece16 : QPiece := ⟨q1 (raw_ints% [13, 1200]),q1 (raw_ints% [13, 1100]),q1 (raw_ints% [432500001, 100000000]),q1 (raw_ints% [-6, 1]),plane3Slack⟩
def contentCert16 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece17 : QPiece := ⟨q1 (raw_ints% [13, 1100]),q1 (raw_ints% [13, 1000]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [5, 1]),plane3Slack⟩
def contentCert17 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece18 : QPiece := ⟨q1 (raw_ints% [13, 1000]),q1 (raw_ints% [13, 900]),q1 (raw_ints% [432500001, 100000000]),q1 (raw_ints% [-5, 1]),plane3Slack⟩
def contentCert18 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece19 : QPiece := ⟨q1 (raw_ints% [13, 900]),q1 (raw_ints% [13, 800]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [4, 1]),plane3Slack⟩
def contentCert19 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece20 : QPiece := ⟨q1 (raw_ints% [13, 800]),q1 (raw_ints% [13, 700]),q1 (raw_ints% [432500001, 100000000]),q1 (raw_ints% [-4, 1]),plane3Slack⟩
def contentCert20 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece21 : QPiece := ⟨q1 (raw_ints% [13, 700]),q1 (raw_ints% [13, 600]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [3, 1]),plane3Slack⟩
def contentCert21 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece22 : QPiece := ⟨q1 (raw_ints% [13, 600]),q1 (raw_ints% [13, 500]),q1 (raw_ints% [432500001, 100000000]),q1 (raw_ints% [-3, 1]),plane3Slack⟩
def contentCert22 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece23 : QPiece := ⟨q1 (raw_ints% [13, 500]),q1 (raw_ints% [13, 400]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [2, 1]),plane3Slack⟩
def contentCert23 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece24 : QPiece := ⟨q1 (raw_ints% [13, 400]),q1 (raw_ints% [13, 300]),q1 (raw_ints% [432500001, 100000000]),q1 (raw_ints% [-2, 1]),plane3Slack⟩
def contentCert24 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece25 : QPiece := ⟨q1 (raw_ints% [13, 300]),q1 (raw_ints% [13, 200]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [1, 1]),plane3Slack⟩
def contentCert25 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece26 : QPiece := ⟨q1 (raw_ints% [13, 200]),q1 (raw_ints% [13, 100]),q1 (raw_ints% [432500001, 100000000]),q1 (raw_ints% [-1, 1]),plane3Slack⟩
def contentCert26 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece27 : QPiece := ⟨q1 (raw_ints% [13, 100]),q1 (raw_ints% [213, 1600]),q1 (raw_ints% [206500001, 100000000]),q1 (raw_ints% [16, 1]),plane3Slack⟩
def contentCert27 : Cert := ⟨24,[],[],plane3Threshold⟩

def contentPiece28 : QPiece := ⟨q1 (raw_ints% [213, 1600]),q1 (raw_ints% [141249999, 1000000000]),q1 (raw_ints% [632500001, 100000000]),q1 (raw_ints% [-16, 1]),plane3Slack⟩
def contentCert28 : Cert := ⟨25,[],[],plane3Threshold⟩

def contentPiece29 : QPiece := ⟨q1 (raw_ints% [141249999, 1000000000]),q1 (raw_ints% [113, 800]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [0, 1]),plane3Slack⟩
def contentCert29 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece30 : QPiece := ⟨q1 (raw_ints% [113, 800]),q1 (raw_ints% [1, 7]),q1 (raw_ints% [406500001, 100000000]),q1 (raw_ints% [0, 1]),plane3Slack⟩
def contentCert30 : Cert := ⟨23,[],[],plane3Threshold⟩

def contentPiece31 : QPiece := ⟨q1 (raw_ints% [1, 7]),q1 (raw_ints% [213, 1400]),q1 (raw_ints% [206500001, 100000000]),q1 (raw_ints% [14, 1]),plane3Slack⟩
def contentCert31 : Cert := ⟨21,[],[],plane3Threshold⟩

def contentPiece32 : QPiece := ⟨q1 (raw_ints% [213, 1400]),q1 (raw_ints% [1129999993, 7000000000]),q1 (raw_ints% [632500001, 100000000]),q1 (raw_ints% [-14, 1]),plane3Slack⟩
def contentCert32 : Cert := ⟨22,[],[],plane3Threshold⟩

def contentPiece33 : QPiece := ⟨q1 (raw_ints% [1129999993, 7000000000]),q1 (raw_ints% [113, 700]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [0, 1]),plane3Slack⟩
def contentCert33 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece34 : QPiece := ⟨q1 (raw_ints% [113, 700]),q1 (raw_ints% [1, 6]),q1 (raw_ints% [406500001, 100000000]),q1 (raw_ints% [0, 1]),plane3Slack⟩
def contentCert34 : Cert := ⟨20,[],[],plane3Threshold⟩

def contentPiece35 : QPiece := ⟨q1 (raw_ints% [1, 6]),q1 (raw_ints% [71, 400]),q1 (raw_ints% [206500001, 100000000]),q1 (raw_ints% [12, 1]),plane3Slack⟩
def contentCert35 : Cert := ⟨18,[],[],plane3Threshold⟩

def contentPiece36 : QPiece := ⟨q1 (raw_ints% [71, 400]),q1 (raw_ints% [564999997, 3000000000]),q1 (raw_ints% [632500001, 100000000]),q1 (raw_ints% [-12, 1]),plane3Slack⟩
def contentCert36 : Cert := ⟨19,[],[],plane3Threshold⟩

def contentPiece37 : QPiece := ⟨q1 (raw_ints% [564999997, 3000000000]),q1 (raw_ints% [113, 600]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [0, 1]),plane3Slack⟩
def contentCert37 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece38 : QPiece := ⟨q1 (raw_ints% [113, 600]),q1 (raw_ints% [1, 5]),q1 (raw_ints% [406500001, 100000000]),q1 (raw_ints% [0, 1]),plane3Slack⟩
def contentCert38 : Cert := ⟨17,[],[],plane3Threshold⟩

def contentPiece39 : QPiece := ⟨q1 (raw_ints% [1, 5]),q1 (raw_ints% [213, 1000]),q1 (raw_ints% [206500001, 100000000]),q1 (raw_ints% [10, 1]),plane3Slack⟩
def contentCert39 : Cert := ⟨15,[],[],plane3Threshold⟩

def contentPiece40 : QPiece := ⟨q1 (raw_ints% [213, 1000]),q1 (raw_ints% [225999999, 1000000000]),q1 (raw_ints% [632500001, 100000000]),q1 (raw_ints% [-10, 1]),plane3Slack⟩
def contentCert40 : Cert := ⟨16,[],[],plane3Threshold⟩

def contentPiece41 : QPiece := ⟨q1 (raw_ints% [225999999, 1000000000]),q1 (raw_ints% [113, 500]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [0, 1]),plane3Slack⟩
def contentCert41 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece42 : QPiece := ⟨q1 (raw_ints% [113, 500]),q1 (raw_ints% [1, 4]),q1 (raw_ints% [406500001, 100000000]),q1 (raw_ints% [0, 1]),plane3Slack⟩
def contentCert42 : Cert := ⟨14,[],[],plane3Threshold⟩

def contentPiece43 : QPiece := ⟨q1 (raw_ints% [1, 4]),q1 (raw_ints% [213, 800]),q1 (raw_ints% [206500001, 100000000]),q1 (raw_ints% [8, 1]),plane3Slack⟩
def contentCert43 : Cert := ⟨12,[],[],plane3Threshold⟩

def contentPiece44 : QPiece := ⟨q1 (raw_ints% [213, 800]),q1 (raw_ints% [282499999, 1000000000]),q1 (raw_ints% [632500001, 100000000]),q1 (raw_ints% [-8, 1]),plane3Slack⟩
def contentCert44 : Cert := ⟨13,[],[],plane3Threshold⟩

def contentPiece45 : QPiece := ⟨q1 (raw_ints% [282499999, 1000000000]),q1 (raw_ints% [113, 400]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [0, 1]),plane3Slack⟩
def contentCert45 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece46 : QPiece := ⟨q1 (raw_ints% [113, 400]),q1 (raw_ints% [1, 3]),q1 (raw_ints% [406500001, 100000000]),q1 (raw_ints% [0, 1]),plane3Slack⟩
def contentCert46 : Cert := ⟨11,[],[],plane3Threshold⟩

def contentPiece47 : QPiece := ⟨q1 (raw_ints% [1, 3]),q1 (raw_ints% [71, 200]),q1 (raw_ints% [206500001, 100000000]),q1 (raw_ints% [6, 1]),plane3Slack⟩
def contentCert47 : Cert := ⟨9,[],[],plane3Threshold⟩

def contentPiece48 : QPiece := ⟨q1 (raw_ints% [71, 200]),q1 (raw_ints% [1129999997, 3000000000]),q1 (raw_ints% [632500001, 100000000]),q1 (raw_ints% [-6, 1]),plane3Slack⟩
def contentCert48 : Cert := ⟨10,[],[],plane3Threshold⟩

def contentPiece49 : QPiece := ⟨q1 (raw_ints% [1129999997, 3000000000]),q1 (raw_ints% [113, 300]),q1 (raw_ints% [419500001, 100000000]),q1 (raw_ints% [0, 1]),plane3Slack⟩
def contentCert49 : Cert := ⟨0,[],[],plane3Threshold⟩

def contentPiece50 : QPiece := ⟨q1 (raw_ints% [113, 300]),q1 (raw_ints% [1, 2]),q1 (raw_ints% [406500001, 100000000]),q1 (raw_ints% [0, 1]),plane3Slack⟩
def contentCert50 : Cert := ⟨8,[],[],plane3Threshold⟩

def contentPiece51 : QPiece := ⟨q1 (raw_ints% [1, 2]),q1 (raw_ints% [213, 400]),q1 (raw_ints% [206500001, 100000000]),q1 (raw_ints% [4, 1]),plane3Slack⟩
def contentCert51 : Cert := ⟨6,[],[],plane3Threshold⟩

def contentPiece52 : QPiece := ⟨q1 (raw_ints% [213, 400]),q1 (raw_ints% [113, 200]),q1 (raw_ints% [739000001, 100000000]),q1 (raw_ints% [-6, 1]),plane3Slack⟩
def contentCert52 : Cert := ⟨2,[],[],plane3Threshold⟩

def contentPiece53 : QPiece := ⟨q1 (raw_ints% [113, 200]),q1 (raw_ints% [1, 1]),q1 (raw_ints% [852000001, 100000000]),q1 (raw_ints% [-8, 1]),plane3Slack⟩
def contentCert53 : Cert := ⟨1,[],[],plane3Threshold⟩

def contentPiece54 : QPiece := ⟨q1 (raw_ints% [1, 1]),q1 (raw_ints% [904000001, 800000000]),q1 (raw_ints% [452000001, 100000000]),q1 (raw_ints% [-4, 1]),plane3Slack⟩
def contentCert54 : Cert := ⟨3,[q1 (raw_ints% [113, 100])],[],plane3Threshold⟩


def plane3PCTemplate : KTmplP :=
  ⟨13/8000,3,0,[(contentPiece0,contentCert0), (contentPiece1,contentCert1), (contentPiece2,contentCert2), (contentPiece3,contentCert3), (contentPiece4,contentCert4), (contentPiece5,contentCert5), (contentPiece6,contentCert6), (contentPiece7,contentCert7), (contentPiece8,contentCert8), (contentPiece9,contentCert9), (contentPiece10,contentCert10), (contentPiece11,contentCert11), (contentPiece12,contentCert12), (contentPiece13,contentCert13), (contentPiece14,contentCert14), (contentPiece15,contentCert15), (contentPiece16,contentCert16), (contentPiece17,contentCert17), (contentPiece18,contentCert18), (contentPiece19,contentCert19), (contentPiece20,contentCert20), (contentPiece21,contentCert21), (contentPiece22,contentCert22), (contentPiece23,contentCert23), (contentPiece24,contentCert24), (contentPiece25,contentCert25)],
    [(contentPiece26,contentCert26), (contentPiece27,contentCert27), (contentPiece28,contentCert28), (contentPiece29,contentCert29), (contentPiece30,contentCert30), (contentPiece31,contentCert31), (contentPiece32,contentCert32), (contentPiece33,contentCert33), (contentPiece34,contentCert34), (contentPiece35,contentCert35), (contentPiece36,contentCert36), (contentPiece37,contentCert37), (contentPiece38,contentCert38), (contentPiece39,contentCert39), (contentPiece40,contentCert40), (contentPiece41,contentCert41), (contentPiece42,contentCert42), (contentPiece43,contentCert43), (contentPiece44,contentCert44), (contentPiece45,contentCert45), (contentPiece46,contentCert46), (contentPiece47,contentCert47), (contentPiece48,contentCert48), (contentPiece49,contentCert49), (contentPiece50,contentCert50), (contentPiece51,contentCert51), (contentPiece52,contentCert52), (contentPiece53,contentCert53), (contentPiece54,contentCert54)],4⟩
def plane3Lambda : ℚ := q1 (raw_ints% [2093141963035255548476961845489855904191277848149, 624885257513513299995586450872000000000000000000])

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
-- kcost: 3 s estimated, 55 scalar chain links/tail and actual low transforms (3 strips).
theorem plane3_heads : ktmplHead (plane3Bank 0) 1 (plane3PCTemplate.toK 200 852 1) = true := by -- kcost: 3 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel
-- kcost: 6 s estimated, 107 exact scalar piece masses (literal heights <= 161 bits, none = 0 mod 2^64).
theorem plane3_class : kclassOK (plane3Bank 0) = true := by -- kcost: 6 s estimated; complete scalar checker, fixed rational field operations.
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


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece31_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece31 contentCert31 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece32_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece32 contentCert32 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece33_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece33 contentCert33 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece34_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece34 contentCert34 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece35_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece35 contentCert35 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece36_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece36 contentCert36 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece37_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece37 contentCert37 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece38_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece38 contentCert38 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece39_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece39 contentCert39 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece40_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece40 contentCert40 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece41_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece41 contentCert41 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece42_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece42 contentCert42 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece43_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece43 contentCert43 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece44_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece44 contentCert44 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece45_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece45 contentCert45 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece46_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece46 contentCert46 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece47_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece47 contentCert47 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece48_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece48 contentCert48 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece49_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece49 contentCert49 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece50_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece50 contentCert50 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece51_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece51 contentCert51 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece52_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece52 contentCert52 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece53_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece53 contentCert53 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete affine head,<=6 conditions and fixed thresholds.
theorem contentPiece54_check :
    pieceOK ((plane3Bank 0).cat 1) 2 (13/200) (1/2) 0 1 2 contentPiece54 contentCert54 = true := by
  -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell0 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece0,contentCert0) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell1 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece1,contentCert1) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell2 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece2,contentCert2) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell3 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece3,contentCert3) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell4 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece4,contentCert4) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell5 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece5,contentCert5) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell6 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece6,contentCert6) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell7 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece7,contentCert7) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell8 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece8,contentCert8) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell9 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece9,contentCert9) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell10 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece10,contentCert10) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell11 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece11,contentCert11) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell12 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece12,contentCert12) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell13 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece13,contentCert13) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell14 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece14,contentCert14) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell15 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece15,contentCert15) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell16 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece16,contentCert16) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell17 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece17,contentCert17) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell18 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece18,contentCert18) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell19 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece19,contentCert19) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell20 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece20,contentCert20) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell21 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece21,contentCert21) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell22 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece22,contentCert22) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell23 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece23,contentCert23) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell24 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece24,contentCert24) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


-- kcost: 2 s estimated, one complete low cell with actual covariance/rounding fields.
theorem plane3_cell25 : cellOKb (plane3Bank 0) plane3BaseCatalogue 1 3 200 816
    (contentPiece25,contentCert25) = true := by -- kcost: 2 s estimated; complete scalar checker, fixed rational field operations.
  decide +kernel


end CatalanCore.Uniform.Bank.Plane3

#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_params
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_heads
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_class
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece26_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece27_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece28_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece29_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece30_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece31_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece32_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece33_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece34_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece35_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece36_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece37_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece38_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece39_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece40_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece41_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece42_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece43_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece44_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece45_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece46_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece47_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece48_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece49_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece50_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece51_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece52_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece53_check
#print axioms CatalanCore.Uniform.Bank.Plane3.contentPiece54_check
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell0
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell1
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell2
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell3
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell4
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell5
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell6
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell7
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell8
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell9
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell10
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell11
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell12
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell13
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell14
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell15
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell16
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell17
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell18
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell19
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell20
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell21
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell22
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell23
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell24
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_cell25
