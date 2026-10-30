import CatalanCore.Uniform.Bank.Common.Data.Fourths.Segs
import CatalanCore.Uniform.Bank.Common.Data.Fourths.Cells

namespace CatalanCore.Uniform.Bank.Common.Data.Fourths
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; scalar certificate numbers and the assembled `SplineData`. -/

def s_sl : ℚ := q1 (raw_ints% [100000, 25253])
def s_Mq : ℚ := q1 (raw_ints% [11, 10])
def s_eps : ℚ := q1 (raw_ints% [1, 1000])
def s_r0 : ℚ := q1 (raw_ints% [4161, 31250])
def s_W : ℚ := q1 (raw_ints% [1, 1000000000000000])
def s_umax : ℚ := q1 (raw_ints% [8, 1])
def s_mprime : ℚ := q1 (raw_ints% [4237467689331319, 2000000000000000])
def s_gmin : ℚ := q1 (raw_ints% [-738239892830379, 500000000000000])
def s_Scap : ℚ := q1 (raw_ints% [-466394071550203804161, 7812500000000000000000])
def s_Ibound : ℚ := q1 (raw_ints% [193829207631, 100000000000])
def s_ccert : ℚ := q1 (raw_ints% [1438085452130567, 200000000000000])
def s_rho : ℚ := q1 (raw_ints% [1, 1000000000000])
def s_theta : ℚ := q1 (raw_ints% [1, 1000000000000000000000000])
def s_etaS : ℚ := q1 (raw_ints% [3328804161, 7812500000000000000000])
def s_lossS : ℚ := q1 (raw_ints% [733729, 10000000000000000])
def s_Rc : ℚ := q1 (raw_ints% [2, 1])
def s_Inu : ℚ := q1 (raw_ints% [1667634099983, 1000000000000])
def s_Dt : ℚ := q1 (raw_ints% [14627817894518751186053, 3906250000000000000000])

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

end CatalanCore.Uniform.Bank.Common.Data.Fourths
