module

public import CatalanCore.Uniform.Bank.Common.Data.Dip18.Segs
public import CatalanCore.Uniform.Bank.Common.Data.Dip18.Cells

@[expose] public section

namespace CatalanCore.Uniform.Bank.Common.Data.Dip18
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; scalar certificate numbers and the assembled `SplineData`. -/

def s_sl : ℚ := q1 (raw_ints% [1, 1])
def s_Mq : ℚ := q1 (raw_ints% [9, 8])
def s_eps : ℚ := q1 (raw_ints% [1, 1000000])
def s_r0 : ℚ := q1 (raw_ints% [179, 2000])
def s_W : ℚ := q1 (raw_ints% [1, 1000000000000000])
def s_umax : ℚ := q1 (raw_ints% [8, 1])
def s_mprime : ℚ := q1 (raw_ints% [2082992951481589, 1000000000000000])
def s_gmin : ℚ := q1 (raw_ints% [-13887254433044033, 10000000000000000])
def s_Scap : ℚ := q1 (raw_ints% [-38094079023936313037, 1500000000000000000000])
def s_Ibound : ℚ := q1 (raw_ints% [2209806917487782845, 1152921504606846976])
def s_ccert : ℚ := q1 (raw_ints% [34717183947859923, 5000000000000000])
def s_rho : ℚ := q1 (raw_ints% [1, 1000000000000])
def s_theta : ℚ := q1 (raw_ints% [1, 1000000000000000000000000])
def s_etaS : ℚ := q1 (raw_ints% [145437679, 500000000000000000000])
def s_lossS : ℚ := q1 (raw_ints% [58129963, 576460752303423488])
def s_Rc : ℚ := q1 (raw_ints% [2, 1])
def s_Inu : ℚ := q1 (raw_ints% [851222875571, 500000000000])
def s_Dt : ℚ := q1 (raw_ints% [15243910584818244128783, 4000000000000000000000])

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

end CatalanCore.Uniform.Bank.Common.Data.Dip18

#print axioms CatalanCore.Uniform.Bank.Common.Data.Dip18.data
