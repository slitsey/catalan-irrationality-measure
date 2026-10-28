import CatalanCore.Uniform.Bank.Common.Data.Thirds.Segs
import CatalanCore.Uniform.Bank.Common.Data.Thirds.Cells

namespace CatalanCore.Uniform.Bank.Common.Data.Thirds
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; scalar certificate numbers and the assembled `SplineData`. -/

def s_sl : ℚ := q1 (raw_ints% [100000, 31399])
def s_Mq : ℚ := q1 (raw_ints% [23, 20])
def s_eps : ℚ := q1 (raw_ints% [1, 1000])
def s_r0 : ℚ := q1 (raw_ints% [33, 250])
def s_W : ℚ := q1 (raw_ints% [1, 1000000000000000])
def s_umax : ℚ := q1 (raw_ints% [8, 1])
def s_mprime : ℚ := q1 (raw_ints% [4188977988104769, 2000000000000000])
def s_gmin : ℚ := q1 (raw_ints% [-824461473287503, 625000000000000])
def s_Scap : ℚ := q1 (raw_ints% [-3527891141027225033, 62500000000000000000])
def s_Ibound : ℚ := q1 (raw_ints% [1737147483497, 1000000000000])
def s_ccert : ℚ := q1 (raw_ints% [34136273513123893, 5000000000000000])
def s_rho : ℚ := q1 (raw_ints% [1, 1000000000000])
def s_theta : ℚ := q1 (raw_ints% [1, 1000000000000000000000000])
def s_etaS : ℚ := q1 (raw_ints% [27225033, 62500000000000000000])
def s_lossS : ℚ := q1 (raw_ints% [470241, 5000000000000000])
def s_Rc : ℚ := q1 (raw_ints% [2, 1])
def s_Inu : ℚ := q1 (raw_ints% [867481404213, 500000000000])
def s_Dt : ℚ := q1 (raw_ints% [251820307144120719543, 62500000000000000000])

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
  dim := 2

end CatalanCore.Uniform.Bank.Common.Data.Thirds
