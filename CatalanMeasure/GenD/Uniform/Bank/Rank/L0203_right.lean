module

public import CatalanCore.Uniform.Content.RankCertificate

public import CatalanMeasure.CellCert.RawInts

@[expose] public section

set_option Elab.async false

set_option profiler true

set_option maxRecDepth 100000

namespace CatalanMeasure.GenD.Uniform.Bank.Rank.L0203_right

open Matrix CatalanCore.Uniform.Content

def intMat (m n : Nat) (xs : List Int) : Matrix (Fin m) (Fin n) Int :=
  fun i j => xs.getD (i.val*n+j.val) 0

def V : Matrix (Fin 20) (Fin 3) Int := intMat 20 3 (raw_ints% [253, 0, 0, 0, 253, 0, 0, 0, 253, 0, 253, 0, -391, 0, 0, 0, -391, 0, 0, 0, 115, 0, 115, 0, 159, 0, 0, 0, 159, 0, 0, 0, -117, 0, -117, 0, -21, 0, 0, 0, -21, 0, 0, 0, 21, 0, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

def L : Matrix (Fin 3) (Fin 20) Int := intMat 3 20 (raw_ints% [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])

def basisScale : Int := 253

theorem basis_check : L*V=basisScale • 1 := by decide +kernel

theorem basis_rank (K : Type*) [Field K] (hs : (basisScale : K)≠0) : (castMatrix K V).rank=3 := integral_basis_rank K V L basisScale basis_check hs

def B0 : Matrix (Fin 5) (Fin 20) Int := intMat 5 20 (raw_ints% [0, 0, 253, -506, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, -506, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, -506, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, -506, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, -506, 0, 0])

def C0 : Matrix (Fin 5) (Fin 1) Int := intMat 5 1 (raw_ints% [253, 115, -117, 21, 0])

def T0 : Matrix (Fin 1) (Fin 3) Int := intMat 1 3 (raw_ints% [0, -506, 253])

def mapScale0 : Int := 253

theorem map0_check : B0*V=C0*T0 := by decide +kernel

theorem map0_rank (K : Type*) [Field K] : (castMatrix K B0*castMatrix K V).rank≤1 := integral_image_rank_le K B0 V C0 T0 map0_check

def B1 : Matrix (Fin 3) (Fin 20) Int := intMat 3 20 (raw_ints% [33, 0, -17, 16, 15, -11, -1, -27, -25, -3, -39, 35, -71, 0, -7, -32, 25, -8, -8, -8, 0, 33, 0, -33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 33, 0, 0, 0, 0])

def C1 : Matrix (Fin 3) (Fin 0) Int := intMat 3 0 (raw_ints% [])

def T1 : Matrix (Fin 0) (Fin 3) Int := intMat 0 3 (raw_ints% [])

def mapScale1 : Int := 33

theorem map1_check : B1*V=C1*T1 := by decide +kernel

theorem map1_rank (K : Type*) [Field K] : (castMatrix K B1*castMatrix K V).rank≤0 := integral_image_rank_le K B1 V C1 T1 map1_check

def B2 : Matrix (Fin 2) (Fin 20) Int := intMat 2 20 (raw_ints% [0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0])

def C2 : Matrix (Fin 2) (Fin 0) Int := intMat 2 0 (raw_ints% [])

def T2 : Matrix (Fin 0) (Fin 3) Int := intMat 0 3 (raw_ints% [])

def mapScale2 : Int := 1

theorem map2_check : B2*V=C2*T2 := by decide +kernel

theorem map2_rank (K : Type*) [Field K] : (castMatrix K B2*castMatrix K V).rank≤0 := integral_image_rank_le K B2 V C2 T2 map2_check

def B3 : Matrix (Fin 10) (Fin 20) Int := intMat 10 20 (raw_ints% [253, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 0])

def C3 : Matrix (Fin 10) (Fin 2) Int := intMat 10 2 (raw_ints% [253, 0, 0, 253, -391, 0, 0, 115, 159, 0, 0, -117, -21, 0, 0, 21, 0, 0, 0, 0])

def T3 : Matrix (Fin 2) (Fin 3) Int := intMat 2 3 (raw_ints% [253, 0, 0, 0, 0, 253])

def mapScale3 : Int := 253

theorem map3_check : B3*V=C3*T3 := by decide +kernel

theorem map3_rank (K : Type*) [Field K] : (castMatrix K B3*castMatrix K V).rank≤2 := integral_image_rank_le K B3 V C3 T3 map3_check

def B4 : Matrix (Fin 6) (Fin 20) Int := intMat 6 20 (raw_ints% [253, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 253, 0])

def C4 : Matrix (Fin 6) (Fin 1) Int := intMat 6 1 (raw_ints% [253, -391, 159, -21, 0, 0])

def T4 : Matrix (Fin 1) (Fin 3) Int := intMat 1 3 (raw_ints% [253, 0, 0])

def mapScale4 : Int := 253

theorem map4_check : B4*V=C4*T4 := by decide +kernel

theorem map4_rank (K : Type*) [Field K] : (castMatrix K B4*castMatrix K V).rank≤1 := integral_image_rank_le K B4 V C4 T4 map4_check

def B5 : Matrix (Fin 1) (Fin 20) Int := intMat 1 20 (raw_ints% [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0])

def C5 : Matrix (Fin 1) (Fin 0) Int := intMat 1 0 (raw_ints% [])

def T5 : Matrix (Fin 0) (Fin 3) Int := intMat 0 3 (raw_ints% [])

def mapScale5 : Int := 1

theorem map5_check : B5*V=C5*T5 := by decide +kernel

theorem map5_rank (K : Type*) [Field K] : (castMatrix K B5*castMatrix K V).rank≤0 := integral_image_rank_le K B5 V C5 T5 map5_check

def B6 : Matrix (Fin 14) (Fin 20) Int := intMat 14 20 (raw_ints% [47741100, 0, 0, 0, 0, 0, -47741100, 0, -38192880, 0, 9548220, 0, 0, 0, 28644660, 0, 23870550, 0, -2387055, 0, 0, 47741100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47741100, 0, 0, 0, -47741100, 0, -38192880, 0, 9548220, 0, 0, 0, 28644660, 0, -23870550, 0, -2387055, 0, 0, 0, 0, 47741100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47741100, 0, 47741100, 0, -92299460, 0, -187781660, 0, 0, 0, 280081120, 0, 0, 0, 50923840, 0, 0, 0, 0, 0, 0, 47741100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47741100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47741100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47741100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47741100, 0, 47741100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47741100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47741100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47741100, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 47741100])

def C6 : Matrix (Fin 14) (Fin 2) Int := intMat 14 2 (raw_ints% [9548220, 0, 0, 9548220, -9654480, 0, 0, 9548220, -53008560, 0, 0, -14756340, 0, 4340100, 0, 6000660, 0, -4415580, -1593900, 0, 0, -792540, 0, 792540, 0, 0, 0, 0])

def T6 : Matrix (Fin 2) (Fin 3) Int := intMat 2 3 (raw_ints% [629, 0, -629, 0, 1265, 0])

def mapScale6 : Int := 47741100

theorem map6_check : B6*V=C6*T6 := by decide +kernel

theorem map6_rank (K : Type*) [Field K] : (castMatrix K B6*castMatrix K V).rank≤2 := integral_image_rank_le K B6 V C6 T6 map6_check

def B7 : Matrix (Fin 12) (Fin 20) Int := intMat 12 20 (raw_ints% [9867, 0, 42757, 0, -9867, 0, -62491, 0, -23023, 0, 49335, 0, 0, 0, -26312, 0, -16445, 0, -13156, 0, 0, 9867, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9867, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9867, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9867, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9867, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9867, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9867, 0, 9867, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9867, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9867, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9867, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9867])

def C7 : Matrix (Fin 12) (Fin 2) Int := intMat 12 2 (raw_ints% [9867, 0, 0, 9867, 0, 9867, 0, -15249, 0, 4485, 0, 6201, 0, -4563, -759, 0, 0, -819, 0, 819, 0, 0, 0, 0])

def T7 : Matrix (Fin 2) (Fin 3) Int := intMat 2 3 (raw_ints% [273, 0, -273, 0, 253, 0])

def mapScale7 : Int := 9867

theorem map7_check : B7*V=C7*T7 := by decide +kernel

theorem map7_rank (K : Type*) [Field K] : (castMatrix K B7*castMatrix K V).rank≤2 := integral_image_rank_le K B7 V C7 T7 map7_check

def B8 : Matrix (Fin 11) (Fin 20) Int := intMat 11 20 (raw_ints% [759, 0, 3289, 0, -759, 0, -4807, 0, -1771, 0, 3795, 0, 9867, 0, 7843, 0, -1265, 0, -1012, 0, 0, 759, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 759, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 759, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 759, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 759, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 759, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 759, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 759, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 759, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 759])

def C8 : Matrix (Fin 11) (Fin 1) Int := intMat 11 1 (raw_ints% [0, 759, 759, -1173, 345, 477, -351, -63, 63, 0, 0])

def T8 : Matrix (Fin 1) (Fin 3) Int := intMat 1 3 (raw_ints% [0, 253, 0])

def mapScale8 : Int := 759

theorem map8_check : B8*V=C8*T8 := by decide +kernel

theorem map8_rank (K : Type*) [Field K] : (castMatrix K B8*castMatrix K V).rank≤1 := integral_image_rank_le K B8 V C8 T8 map8_check

def B9 : Matrix (Fin 2) (Fin 20) Int := intMat 2 20 (raw_ints% [3, -17, 13, -15, -3, 1, -19, 33, -7, 25, 15, -9, 39, -33, 31, -49, -5, -1, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3])

def C9 : Matrix (Fin 2) (Fin 0) Int := intMat 2 0 (raw_ints% [])

def T9 : Matrix (Fin 0) (Fin 3) Int := intMat 0 3 (raw_ints% [])

def mapScale9 : Int := 3

theorem map9_check : B9*V=C9*T9 := by decide +kernel

theorem map9_rank (K : Type*) [Field K] : (castMatrix K B9*castMatrix K V).rank≤0 := integral_image_rank_le K B9 V C9 T9 map9_check

#print axioms basis_rank

end CatalanMeasure.GenD.Uniform.Bank.Rank.L0203_right
