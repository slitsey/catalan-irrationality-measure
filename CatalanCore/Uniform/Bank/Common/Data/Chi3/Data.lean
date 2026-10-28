import CatalanCore.Uniform.Bank.Common.Data.Chi3.Segs
import CatalanCore.Uniform.Bank.Common.Data.Chi3.Cells

namespace CatalanCore.Uniform.Bank.Common.Data.Chi3
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; scalar certificate numbers and the assembled `SplineData`. -/

def s_sl : ℚ := q1 (raw_ints% [200, 191])
def s_Mq : ℚ := q1 (raw_ints% [5, 4])
def s_eps : ℚ := q1 (raw_ints% [1, 1000])
def s_r0 : ℚ := q1 (raw_ints% [49, 500])
def s_W : ℚ := q1 (raw_ints% [1, 1000000000000000])
def s_umax : ℚ := q1 (raw_ints% [8, 1])
def s_mprime : ℚ := q1 (raw_ints% [23147017380990627, 10000000000000000])
def s_gmin : ℚ := q1 (raw_ints% [-1437485340257611, 1000000000000000])
def s_Scap : ℚ := q1 (raw_ints% [-11229698095003625147, 375000000000000000000])
def s_Ibound : ℚ := q1 (raw_ints% [1797022360369, 1000000000000])
def s_ccert : ℚ := q1 (raw_ints% [37521870783566737, 5000000000000000])
def s_rho : ℚ := q1 (raw_ints% [1, 1000000000000])
def s_theta : ℚ := q1 (raw_ints% [1, 1000000000000000000000000])
def s_etaS : ℚ := q1 (raw_ints% [42875049, 125000000000000000000])
def s_lossS : ℚ := q1 (raw_ints% [941419, 10000000000000000])
def s_Rc : ℚ := q1 (raw_ints% [2, 1])
def s_Inu : ℚ := q1 (raw_ints% [28816875853, 15625000000])
def s_Dt : ℚ := q1 (raw_ints% [4643511791526209475773, 1000000000000000000000])

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

end CatalanCore.Uniform.Bank.Common.Data.Chi3
