module

public import CatalanCore.Uniform.Bank.Common.Data.P1N25.Segs
public import CatalanCore.Uniform.Bank.Common.Data.P1N25.Cells

@[expose] public section

namespace CatalanCore.Uniform.Bank.Common.Data.P1N25
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; scalar certificate numbers and the assembled `SplineData`. -/

def s_sl : ℚ := q1 (raw_ints% [1, 1])
def s_Mq : ℚ := q1 (raw_ints% [13, 12])
def s_eps : ℚ := q1 (raw_ints% [1, 1000000])
def s_r0 : ℚ := q1 (raw_ints% [343, 4000])
def s_W : ℚ := q1 (raw_ints% [1, 1000000000000000])
def s_umax : ℚ := q1 (raw_ints% [8, 1])
def s_mprime : ℚ := q1 (raw_ints% [5034544901743743, 2500000000000000])
def s_gmin : ℚ := q1 (raw_ints% [-13707283103991811, 10000000000000000])
def s_Scap : ℚ := q1 (raw_ints% [-9501230313308616781, 400000000000000000000])
def s_Ibound : ℚ := q1 (raw_ints% [1971239263473, 1000000000000])
def s_ccert : ℚ := q1 (raw_ints% [33845462710966783, 5000000000000000])
def s_rho : ℚ := q1 (raw_ints% [1, 1000000000000])
def s_theta : ℚ := q1 (raw_ints% [1, 1000000000000000000000000])
def s_etaS : ℚ := q1 (raw_ints% [108616781, 400000000000000000000])
def s_lossS : ℚ := q1 (raw_ints% [38991, 500000000000000])
def s_Rc : ℚ := q1 (raw_ints% [2, 1])
def s_Inu : ℚ := q1 (raw_ints% [102691611939, 62500000000])
def s_Dt : ℚ := q1 (raw_ints% [99853629795114224867, 28125000000000000000])

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

end CatalanCore.Uniform.Bank.Common.Data.P1N25
