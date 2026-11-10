module

public import CatalanCore.Uniform.Bank.Common.Data.Plane3.Segs
public import CatalanCore.Uniform.Bank.Common.Data.Plane3.Cells

@[expose] public section

namespace CatalanCore.Uniform.Bank.Common.Data.Plane3
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; scalar certificate numbers and the assembled `SplineData`. -/

def s_sl : ℚ := q1 (raw_ints% [1000, 271])
def s_Mq : ℚ := q1 (raw_ints% [21, 20])
def s_eps : ℚ := q1 (raw_ints% [1, 1000000])
def s_r0 : ℚ := q1 (raw_ints% [1, 10])
def s_W : ℚ := q1 (raw_ints% [1, 1000000000000000])
def s_umax : ℚ := q1 (raw_ints% [8, 1])
def s_mprime : ℚ := q1 (raw_ints% [10089946145697407, 5000000000000000])
def s_gmin : ℚ := q1 (raw_ints% [-7320918443504577, 5000000000000000])
def s_Scap : ℚ := q1 (raw_ints% [-195819562702325003, 7500000000000000000])
def s_Ibound : ℚ := q1 (raw_ints% [2424089303356047783, 1152921504606846976])
def s_ccert : ℚ := q1 (raw_ints% [272044759206281, 39062500000000])
def s_rho : ℚ := q1 (raw_ints% [1, 1000000000000])
def s_theta : ℚ := q1 (raw_ints% [1, 1000000000000000000000000])
def s_etaS : ℚ := q1 (raw_ints% [775001, 2500000000000000000])
def s_lossS : ℚ := q1 (raw_ints% [102246383, 1152921504606846976])
def s_Rc : ℚ := q1 (raw_ints% [2, 1])
def s_Inu : ℚ := q1 (raw_ints% [397582719621, 250000000000])
def s_Dt : ℚ := q1 (raw_ints% [670675532185005206293, 200000000000000000000])

def data : SplineData where
  segs := segs
  sl := s_sl
  Mq := s_Mq
  ε := s_eps
  r0 := s_r0
  W := s_W
  umax := s_umax
  mprime := s_mprime
  gmin := s_gmin
  Scap := s_Scap
  Ibound := s_Ibound
  ccert := s_ccert
  rayBoxes := rayCells
  lineCells := lineCells
  rho := s_rho
  theta := s_theta
  etaS := s_etaS
  lossS := s_lossS
  Rc := s_Rc
  Inu := s_Inu
  Dt := s_Dt
  dim := 3

end CatalanCore.Uniform.Bank.Common.Data.Plane3
