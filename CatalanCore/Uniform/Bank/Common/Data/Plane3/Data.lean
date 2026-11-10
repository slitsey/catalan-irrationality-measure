module

public import CatalanCore.Uniform.Bank.Common.Data.Plane3.Segs
public import CatalanCore.Uniform.Bank.Common.Data.Plane3.Cells

@[expose] public section

namespace CatalanCore.Uniform.Bank.Common.Data.Plane3
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; scalar certificate numbers and the assembled `SplineData`. -/

def s_sl : ℚ := q1 (raw_ints% [1000, 271])
def s_Mq : ℚ := q1 (raw_ints% [213, 200])
def s_eps : ℚ := q1 (raw_ints% [1, 1000000])
def s_r0 : ℚ := q1 (raw_ints% [9, 100])
def s_W : ℚ := q1 (raw_ints% [1, 1000000000000000])
def s_umax : ℚ := q1 (raw_ints% [8, 1])
def s_mprime : ℚ := q1 (raw_ints% [10170586122671399, 5000000000000000])
def s_gmin : ℚ := q1 (raw_ints% [-14558098535023393, 10000000000000000])
def s_Scap : ℚ := q1 (raw_ints% [-1803000706946127527, 75000000000000000000])
def s_Ibound : ℚ := q1 (raw_ints% [599090308765092567, 288230376151711744])
def s_ccert : ℚ := q1 (raw_ints% [34899270780366191, 5000000000000000])
def s_rho : ℚ := q1 (raw_ints% [1, 1000000000000])
def s_theta : ℚ := q1 (raw_ints% [1, 1000000000000000000000000])
def s_etaS : ℚ := q1 (raw_ints% [7042509, 25000000000000000000])
def s_lossS : ℚ := q1 (raw_ints% [847293, 9007199254740992])
def s_Rc : ℚ := q1 (raw_ints% [2, 1])
def s_Inu : ℚ := q1 (raw_ints% [322937543877, 200000000000])
def s_Dt : ℚ := q1 (raw_ints% [68912340510797043323527, 20000000000000000000000])

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

#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_sl
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_Mq
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_eps
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_r0
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_W
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_umax
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_mprime
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_gmin
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_Scap
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_Ibound
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_ccert
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_rho
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_theta
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_etaS
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_lossS
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_Rc
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_Inu
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.s_Dt
#print axioms CatalanCore.Uniform.Bank.Common.Data.Plane3.data
