import CatalanCore.Uniform.Bank.Common.Data.Fifths.Segs
import CatalanCore.Uniform.Bank.Common.Data.Fifths.Cells

namespace CatalanCore.Uniform.Bank.Common.Data.Fifths
open CatalanCore.Uniform.Bank.Common CatalanCore.Uniform.Decay.Cert

/-! Generated; scalar certificate numbers and the assembled `SplineData`. -/

def s_sl : ℚ := q1 (raw_ints% [12500, 3259])
def s_Mq : ℚ := q1 (raw_ints% [10, 9])
def s_eps : ℚ := q1 (raw_ints% [1, 1000])
def s_r0 : ℚ := q1 (raw_ints% [16741, 125000])
def s_W : ℚ := q1 (raw_ints% [1, 1000000000000000])
def s_umax : ℚ := q1 (raw_ints% [8, 1])
def s_mprime : ℚ := q1 (raw_ints% [4249229687861759, 2000000000000000])
def s_gmin : ℚ := q1 (raw_ints% [-14581682903972277, 10000000000000000])
def s_Scap : ℚ := q1 (raw_ints% [-3763831774214471642733, 62500000000000000000000])
def s_Ibound : ℚ := q1 (raw_ints% [951871754267, 500000000000])
def s_ccert : ℚ := q1 (raw_ints% [2239239458955067, 312500000000000])
def s_rho : ℚ := q1 (raw_ints% [1, 1000000000000])
def s_theta : ℚ := q1 (raw_ints% [1, 1000000000000000000000000])
def s_etaS : ℚ := q1 (raw_ints% [26971642733, 62500000000000000000000])
def s_lossS : ℚ := q1 (raw_ints% [727619, 10000000000000000])
def s_Rc : ℚ := q1 (raw_ints% [2, 1])
def s_Inu : ℚ := q1 (raw_ints% [841699663751, 500000000000])
def s_Dt : ℚ := q1 (raw_ints% [476697473213463, 125000000000000])

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

end CatalanCore.Uniform.Bank.Common.Data.Fifths
