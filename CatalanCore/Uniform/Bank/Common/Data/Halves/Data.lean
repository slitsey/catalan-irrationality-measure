module

public import CatalanCore.Uniform.Bank.Common.Data.Halves.Segs
public import CatalanCore.Uniform.Bank.Common.Data.Halves.Cells

@[expose] public section

namespace CatalanCore.Uniform.Bank.Common.Data.Halves
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; scalar certificate numbers and the assembled `SplineData`. -/

def s_sl : ℚ := q1 (raw_ints% [100000, 31399])
def s_Mq : ℚ := q1 (raw_ints% [23, 20])
def s_eps : ℚ := q1 (raw_ints% [1, 1000000])
def s_r0 : ℚ := q1 (raw_ints% [33, 250])
def s_W : ℚ := q1 (raw_ints% [1, 1000000000000000])
def s_umax : ℚ := q1 (raw_ints% [8, 1])
def s_mprime : ℚ := q1 (raw_ints% [10065252583214803, 5000000000000000])
def s_gmin : ℚ := q1 (raw_ints% [-12042195493375613, 10000000000000000])
def s_Scap : ℚ := q1 (raw_ints% [-3372530277683475033, 62500000000000000000])
def s_Ibound : ℚ := q1 (raw_ints% [945907227765526785, 576460752303423488])
def s_ccert : ℚ := q1 (raw_ints% [32172700659805219, 5000000000000000])
def s_rho : ℚ := q1 (raw_ints% [1, 1000000000000])
def s_theta : ℚ := q1 (raw_ints% [1, 1000000000000000000000000])
def s_etaS : ℚ := q1 (raw_ints% [27225033, 62500000000000000000])
def s_lossS : ℚ := q1 (raw_ints% [113041319, 1152921504606846976])
def s_Rc : ℚ := q1 (raw_ints% [2, 1])
def s_Inu : ℚ := q1 (raw_ints% [867481404213, 500000000000])
def s_Dt : ℚ := q1 (raw_ints% [1989531686815038326599, 500000000000000000000])

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

end CatalanCore.Uniform.Bank.Common.Data.Halves

#print axioms CatalanCore.Uniform.Bank.Common.Data.Halves.data
