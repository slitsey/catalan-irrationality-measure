module

public import Mathlib.Data.Rat.Defs

public import CatalanMeasure.CellCert.RawInts

@[expose] public section

set_option Elab.async false

set_option profiler true

namespace CatalanMeasure.GenD.Uniform.Bank.Profile205

/-! Frozen exact leading-profile arithmetic. Physical source transport and content
are supplied separately; these arithmetic checks alone assert no nullity bound. -/

def pieceIntegral (l r c s : Rat) : Rat := c*(r-l)+s*(r*r-l*l)/2

def cell000 : Rat := pieceIntegral (2 / 1 : Rat) (75 / 37 : Rat) (-5 / 1 : Rat) (5 / 2 : Rat)

theorem cell000_check : cell000=(5 / 5476 : Rat) := by decide +kernel

def cell001 : Rat := pieceIntegral (75 / 37 : Rat) (69 / 34 : Rat) (-5 / 1 : Rat) (5 / 2 : Rat)

theorem cell001_check : cell001=(1065 / 6330256 : Rat) := by decide +kernel

def cell002 : Rat := pieceIntegral (69 / 34 : Rat) (128 / 63 : Rat) (64 / 1 : Rat) (-63 / 2 : Rat) + pieceIntegral (128 / 63 : Rat) (53 / 26 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell002_check : cell002=(25 / 291312 : Rat) := by decide +kernel

def cell003 : Rat := pieceIntegral (53 / 26 : Rat) (39 / 19 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell003_check : cell003=(0 / 1 : Rat) := by decide +kernel

def cell004 : Rat := pieceIntegral (39 / 19 : Rat) (35 / 17 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell004_check : cell004=(0 / 1 : Rat) := by decide +kernel

def cell005 : Rat := pieceIntegral (35 / 17 : Rat) (56 / 27 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell005_check : cell005=(0 / 1 : Rat) := by decide +kernel

def cell006 : Rat := pieceIntegral (56 / 27 : Rat) (106 / 51 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (106 / 51 : Rat) (25 / 12 : Rat) (-53 / 1 : Rat) (51 / 2 : Rat)

theorem cell006_check : cell006=(1 / 3264 : Rat) := by decide +kernel

def cell007 : Rat := pieceIntegral (25 / 12 : Rat) (48 / 23 : Rat) (-53 / 1 : Rat) (51 / 2 : Rat)

theorem cell007_check : cell007=(21 / 33856 : Rat) := by decide +kernel

def cell008 : Rat := pieceIntegral (48 / 23 : Rat) (23 / 11 : Rat) (-5 / 1 : Rat) (5 / 2 : Rat)

theorem cell008_check : cell008=(225 / 256036 : Rat) := by decide +kernel

def cell009 : Rat := pieceIntegral (23 / 11 : Rat) (128 / 61 : Rat) (64 / 1 : Rat) (-61 / 2 : Rat) + pieceIntegral (128 / 61 : Rat) (78 / 37 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell009_check : cell009=(25 / 29524 : Rat) := by decide +kernel

def cell010 : Rat := pieceIntegral (78 / 37 : Rat) (53 / 25 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell010_check : cell010=(0 / 1 : Rat) := by decide +kernel

def cell011 : Rat := pieceIntegral (53 / 25 : Rat) (70 / 33 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell011_check : cell011=(0 / 1 : Rat) := by decide +kernel

def cell012 : Rat := pieceIntegral (70 / 33 : Rat) (15 / 7 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell012_check : cell012=(0 / 1 : Rat) := by decide +kernel

def cell013 : Rat := pieceIntegral (15 / 7 : Rat) (28 / 13 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell013_check : cell013=(0 / 1 : Rat) := by decide +kernel

def cell014 : Rat := pieceIntegral (28 / 13 : Rat) (69 / 32 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell014_check : cell014=(0 / 1 : Rat) := by decide +kernel

def cell015 : Rat := pieceIntegral (69 / 32 : Rat) (67 / 31 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (67 / 31 : Rat) (13 / 6 : Rat) (-67 / 1 : Rat) (31 / 1 : Rat)

theorem cell015_check : cell015=(1 / 2232 : Rat) := by decide +kernel

def cell016 : Rat := pieceIntegral (13 / 6 : Rat) (24 / 11 : Rat) (11 / 1 : Rat) (-5 / 1 : Rat)

theorem cell016_check : cell016=(17 / 8712 : Rat) := by decide +kernel

def cell017 : Rat := pieceIntegral (24 / 11 : Rat) (59 / 27 : Rat) (59 / 1 : Rat) (-27 / 1 : Rat) + pieceIntegral (59 / 27 : Rat) (35 / 16 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell017_check : cell017=(1 / 6534 : Rat) := by decide +kernel

def cell018 : Rat := pieceIntegral (35 / 16 : Rat) (11 / 5 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell018_check : cell018=(0 / 1 : Rat) := by decide +kernel

def cell019 : Rat := pieceIntegral (11 / 5 : Rat) (75 / 34 : Rat) (-11 / 1 : Rat) (5 / 1 : Rat)

theorem cell019_check : cell019=(1 / 11560 : Rat) := by decide +kernel

def cell020 : Rat := pieceIntegral (75 / 34 : Rat) (53 / 24 : Rat) (-11 / 1 : Rat) (5 / 1 : Rat)

theorem cell020_check : cell020=(29 / 332928 : Rat) := by decide +kernel

def cell021 : Rat := pieceIntegral (53 / 24 : Rat) (69 / 31 : Rat) (-11 / 1 : Rat) (5 / 1 : Rat)

theorem cell021_check : cell021=(1651 / 1107072 : Rat) := by decide +kernel

def cell022 : Rat := pieceIntegral (69 / 31 : Rat) (78 / 35 : Rat) (58 / 1 : Rat) (-26 / 1 : Rat)

theorem cell022_check : cell022=(303 / 1177225 : Rat) := by decide +kernel

def cell023 : Rat := pieceIntegral (78 / 35 : Rat) (29 / 13 : Rat) (58 / 1 : Rat) (-26 / 1 : Rat) + pieceIntegral (29 / 13 : Rat) (56 / 25 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell023_check : cell023=(1 / 15925 : Rat) := by decide +kernel

def cell024 : Rat := pieceIntegral (56 / 25 : Rat) (9 / 4 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell024_check : cell024=(0 / 1 : Rat) := by decide +kernel

def cell025 : Rat := pieceIntegral (9 / 4 : Rat) (70 / 31 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell025_check : cell025=(0 / 1 : Rat) := by decide +kernel

def cell026 : Rat := pieceIntegral (70 / 31 : Rat) (59 / 26 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (59 / 26 : Rat) (25 / 11 : Rat) (-59 / 1 : Rat) (26 / 1 : Rat)

theorem cell026_check : cell026=(1 / 6292 : Rat) := by decide +kernel

def cell027 : Rat := pieceIntegral (25 / 11 : Rat) (16 / 7 : Rat) (-59 / 1 : Rat) (26 / 1 : Rat)

theorem cell027_check : cell027=(20 / 5929 : Rat) := by decide +kernel

def cell028 : Rat := pieceIntegral (16 / 7 : Rat) (39 / 17 : Rat) (-11 / 1 : Rat) (5 / 1 : Rat)

theorem cell028_check : cell028=(107 / 28322 : Rat) := by decide +kernel

def cell029 : Rat := pieceIntegral (39 / 17 : Rat) (23 / 10 : Rat) (67 / 1 : Rat) (-29 / 1 : Rat)

theorem cell029_check : cell029=(131 / 57800 : Rat) := by decide +kernel

def cell030 : Rat := pieceIntegral (23 / 10 : Rat) (53 / 23 : Rat) (67 / 1 : Rat) (-29 / 1 : Rat)

theorem cell030_check : cell030=(109 / 105800 : Rat) := by decide +kernel

def cell031 : Rat := pieceIntegral (53 / 23 : Rat) (67 / 29 : Rat) (67 / 1 : Rat) (-29 / 1 : Rat) + pieceIntegral (67 / 29 : Rat) (7 / 3 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell031_check : cell031=(8 / 15341 : Rat) := by decide +kernel

def cell032 : Rat := pieceIntegral (7 / 3 : Rat) (75 / 32 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell032_check : cell032=(0 / 1 : Rat) := by decide +kernel

def cell033 : Rat := pieceIntegral (75 / 32 : Rat) (59 / 25 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (59 / 25 : Rat) (26 / 11 : Rat) (-59 / 1 : Rat) (25 / 1 : Rat)

theorem cell033_check : cell033=(1 / 6050 : Rat) := by decide +kernel

def cell034 : Rat := pieceIntegral (26 / 11 : Rat) (83 / 35 : Rat) (19 / 1 : Rat) (-8 / 1 : Rat) + pieceIntegral (83 / 35 : Rat) (69 / 29 : Rat) (-64 / 1 : Rat) (27 / 1 : Rat)

theorem cell034_check : cell034=(5447 / 3561635 : Rat) := by decide +kernel

def cell035 : Rat := pieceIntegral (69 / 29 : Rat) (12 / 5 : Rat) (5 / 1 : Rat) (-2 / 1 : Rat)

theorem cell035_check : cell035=(96 / 21025 : Rat) := by decide +kernel

def cell036 : Rat := pieceIntegral (12 / 5 : Rat) (118 / 49 : Rat) (53 / 1 : Rat) (-22 / 1 : Rat) + pieceIntegral (118 / 49 : Rat) (53 / 22 : Rat) (-6 / 1 : Rat) (5 / 2 : Rat)

theorem cell036_check : cell036=(2181 / 2371600 : Rat) := by decide +kernel

def cell037 : Rat := pieceIntegral (53 / 22 : Rat) (70 / 29 : Rat) (-6 / 1 : Rat) (5 / 2 : Rat)

theorem cell037_check : cell037=(219 / 1628176 : Rat) := by decide +kernel

def cell038 : Rat := pieceIntegral (70 / 29 : Rat) (128 / 53 : Rat) (64 / 1 : Rat) (-53 / 2 : Rat) + pieceIntegral (128 / 53 : Rat) (75 / 31 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell038_check : cell038=(1 / 44573 : Rat) := by decide +kernel

def cell039 : Rat := pieceIntegral (75 / 31 : Rat) (56 / 23 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell039_check : cell039=(0 / 1 : Rat) := by decide +kernel

def cell040 : Rat := pieceIntegral (56 / 23 : Rat) (39 / 16 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell040_check : cell040=(0 / 1 : Rat) := by decide +kernel

def cell041 : Rat := pieceIntegral (39 / 16 : Rat) (22 / 9 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell041_check : cell041=(0 / 1 : Rat) := by decide +kernel

def cell042 : Rat := pieceIntegral (22 / 9 : Rat) (32 / 13 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (32 / 13 : Rat) (69 / 28 : Rat) (-64 / 1 : Rat) (26 / 1 : Rat)

theorem cell042_check : cell042=(1 / 10192 : Rat) := by decide +kernel

def cell043 : Rat := pieceIntegral (69 / 28 : Rat) (5 / 2 : Rat) (5 / 1 : Rat) (-2 / 1 : Rat)

theorem cell043_check : cell043=(1 / 784 : Rat) := by decide +kernel

def cell044 : Rat := pieceIntegral (5 / 2 : Rat) (78 / 31 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell044_check : cell044=(0 / 1 : Rat) := by decide +kernel

def cell045 : Rat := pieceIntegral (78 / 31 : Rat) (53 / 21 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell045_check : cell045=(0 / 1 : Rat) := by decide +kernel

def cell046 : Rat := pieceIntegral (53 / 21 : Rat) (48 / 19 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell046_check : cell046=(0 / 1 : Rat) := by decide +kernel

def cell047 : Rat := pieceIntegral (48 / 19 : Rat) (28 / 11 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell047_check : cell047=(0 / 1 : Rat) := by decide +kernel

def cell048 : Rat := pieceIntegral (28 / 11 : Rat) (23 / 9 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell048_check : cell048=(0 / 1 : Rat) := by decide +kernel

def cell049 : Rat := pieceIntegral (23 / 9 : Rat) (75 / 29 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell049_check : cell049=(0 / 1 : Rat) := by decide +kernel

def cell050 : Rat := pieceIntegral (75 / 29 : Rat) (70 / 27 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell050_check : cell050=(0 / 1 : Rat) := by decide +kernel

def cell051 : Rat := pieceIntegral (70 / 27 : Rat) (13 / 5 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell051_check : cell051=(0 / 1 : Rat) := by decide +kernel

def cell052 : Rat := pieceIntegral (13 / 5 : Rat) (53 / 20 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell052_check : cell052=(0 / 1 : Rat) := by decide +kernel

def cell053 : Rat := pieceIntegral (53 / 20 : Rat) (61 / 23 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (61 / 23 : Rat) (69 / 26 : Rat) (-61 / 1 : Rat) (23 / 1 : Rat)

theorem cell053_check : cell053=(1 / 31096 : Rat) := by decide +kernel

def cell054 : Rat := pieceIntegral (69 / 26 : Rat) (8 / 3 : Rat) (8 / 1 : Rat) (-3 / 1 : Rat)

theorem cell054_check : cell054=(1 / 4056 : Rat) := by decide +kernel

def cell055 : Rat := pieceIntegral (8 / 3 : Rat) (75 / 28 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell055_check : cell055=(0 / 1 : Rat) := by decide +kernel

def cell056 : Rat := pieceIntegral (75 / 28 : Rat) (78 / 29 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell056_check : cell056=(0 / 1 : Rat) := by decide +kernel

def cell057 : Rat := pieceIntegral (78 / 29 : Rat) (35 / 13 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell057_check : cell057=(0 / 1 : Rat) := by decide +kernel

def cell058 : Rat := pieceIntegral (35 / 13 : Rat) (11 / 4 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell058_check : cell058=(0 / 1 : Rat) := by decide +kernel

def cell059 : Rat := pieceIntegral (11 / 4 : Rat) (69 / 25 : Rat) (-11 / 1 : Rat) (4 / 1 : Rat)

theorem cell059_check : cell059=(1 / 5000 : Rat) := by decide +kernel

def cell060 : Rat := pieceIntegral (69 / 25 : Rat) (58 / 21 : Rat) (58 / 1 : Rat) (-21 / 1 : Rat) + pieceIntegral (58 / 21 : Rat) (25 / 9 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell060_check : cell060=(1 / 26250 : Rat) := by decide +kernel

def cell061 : Rat := pieceIntegral (25 / 9 : Rat) (39 / 14 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell061_check : cell061=(0 / 1 : Rat) := by decide +kernel

def cell062 : Rat := pieceIntegral (39 / 14 : Rat) (53 / 19 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell062_check : cell062=(0 / 1 : Rat) := by decide +kernel

def cell063 : Rat := pieceIntegral (53 / 19 : Rat) (14 / 5 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell063_check : cell063=(0 / 1 : Rat) := by decide +kernel

def cell064 : Rat := pieceIntegral (14 / 5 : Rat) (59 / 21 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (59 / 21 : Rat) (48 / 17 : Rat) (-59 / 1 : Rat) (21 / 1 : Rat)

theorem cell064_check : cell064=(25 / 12138 : Rat) := by decide +kernel

def cell065 : Rat := pieceIntegral (48 / 17 : Rat) (23 / 8 : Rat) (-11 / 1 : Rat) (4 / 1 : Rat)

theorem cell065_check : cell065=(189 / 9248 : Rat) := by decide +kernel

def cell066 : Rat := pieceIntegral (23 / 8 : Rat) (75 / 26 : Rat) (58 / 1 : Rat) (-20 / 1 : Rat)

theorem cell066_check : cell066=(21 / 5408 : Rat) := by decide +kernel

def cell067 : Rat := pieceIntegral (75 / 26 : Rat) (26 / 9 : Rat) (58 / 1 : Rat) (-20 / 1 : Rat)

theorem cell067_check : cell067=(31 / 27378 : Rat) := by decide +kernel

def cell068 : Rat := pieceIntegral (26 / 9 : Rat) (29 / 10 : Rat) (58 / 1 : Rat) (-20 / 1 : Rat) + pieceIntegral (29 / 10 : Rat) (35 / 12 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell068_check : cell068=(1 / 810 : Rat) := by decide +kernel

def cell069 : Rat := pieceIntegral (35 / 12 : Rat) (53 / 18 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell069_check : cell069=(0 / 1 : Rat) := by decide +kernel

def cell070 : Rat := pieceIntegral (53 / 18 : Rat) (56 / 19 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell070_check : cell070=(0 / 1 : Rat) := by decide +kernel

def cell071 : Rat := pieceIntegral (56 / 19 : Rat) (59 / 20 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (59 / 20 : Rat) (3 / 1 : Rat) (-59 / 1 : Rat) (20 / 1 : Rat)

theorem cell071_check : cell071=(1 / 40 : Rat) := by decide +kernel

def cell072 : Rat := pieceIntegral (3 / 1 : Rat) (70 / 23 : Rat) (64 / 1 : Rat) (-21 / 1 : Rat)

theorem cell072_check : cell072=(25 / 1058 : Rat) := by decide +kernel

def cell073 : Rat := pieceIntegral (70 / 23 : Rat) (64 / 21 : Rat) (64 / 1 : Rat) (-21 / 1 : Rat) + pieceIntegral (64 / 21 : Rat) (28 / 9 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell073_check : cell073=(2 / 11109 : Rat) := by decide +kernel

def cell074 : Rat := pieceIntegral (28 / 9 : Rat) (53 / 17 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell074_check : cell074=(0 / 1 : Rat) := by decide +kernel

def cell075 : Rat := pieceIntegral (53 / 17 : Rat) (78 / 25 : Rat) (-53 / 1 : Rat) (17 / 1 : Rat)

theorem cell075_check : cell075=(1 / 21250 : Rat) := by decide +kernel

def cell076 : Rat := pieceIntegral (78 / 25 : Rat) (25 / 8 : Rat) (-53 / 1 : Rat) (17 / 1 : Rat)

theorem cell076_check : cell076=(33 / 80000 : Rat) := by decide +kernel

def cell077 : Rat := pieceIntegral (25 / 8 : Rat) (69 / 22 : Rat) (-53 / 1 : Rat) (17 / 1 : Rat)

theorem cell077_check : cell077=(39 / 15488 : Rat) := by decide +kernel

def cell078 : Rat := pieceIntegral (69 / 22 : Rat) (22 / 7 : Rat) (16 / 1 : Rat) (-5 / 1 : Rat)

theorem cell078_check : cell078=(93 / 47432 : Rat) := by decide +kernel

def cell079 : Rat := pieceIntegral (22 / 7 : Rat) (35 / 11 : Rat) (5 / 1 : Rat) (-3 / 2 : Rat)

theorem cell079_check : cell079=(237 / 23716 : Rat) := by decide +kernel

def cell080 : Rat := pieceIntegral (35 / 11 : Rat) (118 / 37 : Rat) (75 / 1 : Rat) (-47 / 2 : Rat) + pieceIntegral (118 / 37 : Rat) (16 / 5 : Rat) (16 / 1 : Rat) (-5 / 1 : Rat)

theorem cell080_check : cell080=(119 / 89540 : Rat) := by decide +kernel

def cell081 : Rat := pieceIntegral (16 / 5 : Rat) (13 / 4 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell081_check : cell081=(0 / 1 : Rat) := by decide +kernel

def cell082 : Rat := pieceIntegral (13 / 4 : Rat) (75 / 23 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell082_check : cell082=(0 / 1 : Rat) := by decide +kernel

def cell083 : Rat := pieceIntegral (75 / 23 : Rat) (128 / 39 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (128 / 39 : Rat) (23 / 7 : Rat) (-64 / 1 : Rat) (39 / 2 : Rat)

theorem cell083_check : cell083=(1 / 7644 : Rat) := by decide +kernel

def cell084 : Rat := pieceIntegral (23 / 7 : Rat) (56 / 17 : Rat) (5 / 1 : Rat) (-3 / 2 : Rat)

theorem cell084_check : cell084=(31 / 56644 : Rat) := by decide +kernel

def cell085 : Rat := pieceIntegral (56 / 17 : Rat) (53 / 16 : Rat) (5 / 1 : Rat) (-3 / 2 : Rat)

theorem cell085_check : cell085=(245 / 295936 : Rat) := by decide +kernel

def cell086 : Rat := pieceIntegral (53 / 16 : Rat) (10 / 3 : Rat) (5 / 1 : Rat) (-3 / 2 : Rat)

theorem cell086_check : cell086=(1 / 3072 : Rat) := by decide +kernel

def cell087 : Rat := pieceIntegral (10 / 3 : Rat) (78 / 23 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell087_check : cell087=(0 / 1 : Rat) := by decide +kernel

def cell088 : Rat := pieceIntegral (78 / 23 : Rat) (75 / 22 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell088_check : cell088=(0 / 1 : Rat) := by decide +kernel

def cell089 : Rat := pieceIntegral (75 / 22 : Rat) (58 / 17 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (58 / 17 : Rat) (24 / 7 : Rat) (-58 / 1 : Rat) (17 / 1 : Rat)

theorem cell089_check : cell089=(2 / 833 : Rat) := by decide +kernel

def cell090 : Rat := pieceIntegral (24 / 7 : Rat) (69 / 20 : Rat) (-10 / 1 : Rat) (3 / 1 : Rat)

theorem cell090_check : cell090=(267 / 39200 : Rat) := by decide +kernel

def cell091 : Rat := pieceIntegral (69 / 20 : Rat) (59 / 17 : Rat) (59 / 1 : Rat) (-17 / 1 : Rat) + pieceIntegral (59 / 17 : Rat) (7 / 2 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell091_check : cell091=(49 / 13600 : Rat) := by decide +kernel

def cell092 : Rat := pieceIntegral (7 / 2 : Rat) (53 / 15 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell092_check : cell092=(0 / 1 : Rat) := by decide +kernel

def cell093 : Rat := pieceIntegral (53 / 15 : Rat) (39 / 11 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell093_check : cell093=(0 / 1 : Rat) := by decide +kernel

def cell094 : Rat := pieceIntegral (39 / 11 : Rat) (25 / 7 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell094_check : cell094=(0 / 1 : Rat) := by decide +kernel

def cell095 : Rat := pieceIntegral (25 / 7 : Rat) (29 / 8 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (29 / 8 : Rat) (69 / 19 : Rat) (-58 / 1 : Rat) (16 / 1 : Rat)

theorem cell095_check : cell095=(1 / 2888 : Rat) := by decide +kernel

def cell096 : Rat := pieceIntegral (69 / 19 : Rat) (11 / 3 : Rat) (11 / 1 : Rat) (-3 / 1 : Rat)

theorem cell096_check : cell096=(2 / 1083 : Rat) := by decide +kernel

def cell097 : Rat := pieceIntegral (11 / 3 : Rat) (70 / 19 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell097_check : cell097=(0 / 1 : Rat) := by decide +kernel

def cell098 : Rat := pieceIntegral (70 / 19 : Rat) (59 / 16 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (59 / 16 : Rat) (48 / 13 : Rat) (-59 / 1 : Rat) (16 / 1 : Rat)

theorem cell098_check : cell098=(1 / 5408 : Rat) := by decide +kernel

def cell099 : Rat := pieceIntegral (48 / 13 : Rat) (26 / 7 : Rat) (-11 / 1 : Rat) (3 / 1 : Rat)

theorem cell099_check : cell099=(20 / 8281 : Rat) := by decide +kernel

def cell100 : Rat := pieceIntegral (26 / 7 : Rat) (67 / 18 : Rat) (67 / 1 : Rat) (-18 / 1 : Rat) + pieceIntegral (67 / 18 : Rat) (56 / 15 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell100_check : cell100=(1 / 1764 : Rat) := by decide +kernel

def cell101 : Rat := pieceIntegral (56 / 15 : Rat) (15 / 4 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell101_check : cell101=(0 / 1 : Rat) := by decide +kernel

def cell102 : Rat := pieceIntegral (15 / 4 : Rat) (53 / 14 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell102_check : cell102=(0 / 1 : Rat) := by decide +kernel

def cell103 : Rat := pieceIntegral (53 / 14 : Rat) (23 / 6 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell103_check : cell103=(0 / 1 : Rat) := by decide +kernel

def cell104 : Rat := pieceIntegral (23 / 6 : Rat) (35 / 9 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell104_check : cell104=(0 / 1 : Rat) := by decide +kernel

def cell105 : Rat := pieceIntegral (35 / 9 : Rat) (39 / 10 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell105_check : cell105=(0 / 1 : Rat) := by decide +kernel

def cell106 : Rat := pieceIntegral (39 / 10 : Rat) (75 / 19 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell106_check : cell106=(0 / 1 : Rat) := by decide +kernel

def cell107 : Rat := pieceIntegral (75 / 19 : Rat) (4 / 1 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell107_check : cell107=(0 / 1 : Rat) := by decide +kernel

def cell108 : Rat := pieceIntegral (4 / 1 : Rat) (150 / 37 : Rat) (-8 / 1 : Rat) (2 / 1 : Rat) + pieceIntegral (150 / 37 : Rat) (69 / 17 : Rat) (-83 / 1 : Rat) (41 / 2 : Rat)

theorem cell108_check : cell108=(157 / 42772 : Rat) := by decide +kernel

def cell109 : Rat := pieceIntegral (69 / 17 : Rat) (53 / 13 : Rat) (-14 / 1 : Rat) (7 / 2 : Rat)

theorem cell109_check : cell109=(210 / 48841 : Rat) := by decide +kernel

def cell110 : Rat := pieceIntegral (53 / 13 : Rat) (78 / 19 : Rat) (-14 / 1 : Rat) (7 / 2 : Rat)

theorem cell110_check : cell110=(2205 / 244036 : Rat) := by decide +kernel

def cell111 : Rat := pieceIntegral (78 / 19 : Rat) (70 / 17 : Rat) (64 / 1 : Rat) (-31 / 2 : Rat)

theorem cell111_check : cell111=(352 / 104329 : Rat) := by decide +kernel

def cell112 : Rat := pieceIntegral (70 / 17 : Rat) (128 / 31 : Rat) (64 / 1 : Rat) (-31 / 2 : Rat) + pieceIntegral (128 / 31 : Rat) (25 / 6 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell112_check : cell112=(9 / 8959 : Rat) := by decide +kernel

def cell113 : Rat := pieceIntegral (25 / 6 : Rat) (30 / 7 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (30 / 7 : Rat) (56 / 13 : Rat) (-75 / 1 : Rat) (35 / 2 : Rat)

theorem cell113_check : cell113=(5 / 1183 : Rat) := by decide +kernel

def cell114 : Rat := pieceIntegral (56 / 13 : Rat) (69 / 16 : Rat) (-131 / 1 : Rat) (61 / 2 : Rat)

theorem cell114_check : cell114=(381 / 173056 : Rat) := by decide +kernel

def cell115 : Rat := pieceIntegral (69 / 16 : Rat) (13 / 3 : Rat) (-62 / 1 : Rat) (29 / 2 : Rat)

theorem cell115_check : cell115=(131 / 9216 : Rat) := by decide +kernel

def cell116 : Rat := pieceIntegral (13 / 3 : Rat) (48 / 11 : Rat) (16 / 1 : Rat) (-7 / 2 : Rat)

theorem cell116_check : cell116=(103 / 4356 : Rat) := by decide +kernel

def cell117 : Rat := pieceIntegral (48 / 11 : Rat) (35 / 8 : Rat) (64 / 1 : Rat) (-29 / 2 : Rat)

theorem cell117_check : cell117=(227 / 30976 : Rat) := by decide +kernel

def cell118 : Rat := pieceIntegral (35 / 8 : Rat) (22 / 5 : Rat) (64 / 1 : Rat) (-29 / 2 : Rat)

theorem cell118_check : cell118=(61 / 6400 : Rat) := by decide +kernel

def cell119 : Rat := pieceIntegral (22 / 5 : Rat) (75 / 17 : Rat) (64 / 1 : Rat) (-29 / 2 : Rat)

theorem cell119_check : cell119=(39 / 28900 : Rat) := by decide +kernel

def cell120 : Rat := pieceIntegral (75 / 17 : Rat) (128 / 29 : Rat) (64 / 1 : Rat) (-29 / 2 : Rat) + pieceIntegral (128 / 29 : Rat) (53 / 12 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell120_check : cell120=(1 / 33524 : Rat) := by decide +kernel

def cell121 : Rat := pieceIntegral (53 / 12 : Rat) (9 / 2 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell121_check : cell121=(0 / 1 : Rat) := by decide +kernel

def cell122 : Rat := pieceIntegral (9 / 2 : Rat) (32 / 7 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (32 / 7 : Rat) (78 / 17 : Rat) (-64 / 1 : Rat) (14 / 1 : Rat)

theorem cell122_check : cell122=(4 / 2023 : Rat) := by decide +kernel

def cell123 : Rat := pieceIntegral (78 / 17 : Rat) (23 / 5 : Rat) (-64 / 1 : Rat) (14 / 1 : Rat)

theorem cell123_check : cell123=(27 / 7225 : Rat) := by decide +kernel

def cell124 : Rat := pieceIntegral (23 / 5 : Rat) (14 / 3 : Rat) (5 / 1 : Rat) (-1 / 1 : Rat)

theorem cell124_check : cell124=(11 / 450 : Rat) := by decide +kernel

def cell125 : Rat := pieceIntegral (14 / 3 : Rat) (75 / 16 : Rat) (75 / 1 : Rat) (-16 / 1 : Rat)

theorem cell125_check : cell125=(1 / 288 : Rat) := by decide +kernel

def cell126 : Rat := pieceIntegral (75 / 16 : Rat) (24 / 5 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell126_check : cell126=(0 / 1 : Rat) := by decide +kernel

def cell127 : Rat := pieceIntegral (24 / 5 : Rat) (53 / 11 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell127_check : cell127=(0 / 1 : Rat) := by decide +kernel

def cell128 : Rat := pieceIntegral (53 / 11 : Rat) (39 / 8 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell128_check : cell128=(0 / 1 : Rat) := by decide +kernel

def cell129 : Rat := pieceIntegral (39 / 8 : Rat) (64 / 13 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (64 / 13 : Rat) (69 / 14 : Rat) (-64 / 1 : Rat) (13 / 1 : Rat)

theorem cell129_check : cell129=(1 / 5096 : Rat) := by decide +kernel

def cell130 : Rat := pieceIntegral (69 / 14 : Rat) (5 / 1 : Rat) (5 / 1 : Rat) (-1 / 1 : Rat)

theorem cell130_check : cell130=(1 / 392 : Rat) := by decide +kernel

def cell131 : Rat := pieceIntegral (5 / 1 : Rat) (56 / 11 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell131_check : cell131=(0 / 1 : Rat) := by decide +kernel

def cell132 : Rat := pieceIntegral (56 / 11 : Rat) (26 / 5 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell132_check : cell132=(0 / 1 : Rat) := by decide +kernel

def cell133 : Rat := pieceIntegral (26 / 5 : Rat) (58 / 11 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (58 / 11 : Rat) (53 / 10 : Rat) (-58 / 1 : Rat) (11 / 1 : Rat)

theorem cell133_check : cell133=(9 / 2200 : Rat) := by decide +kernel

def cell134 : Rat := pieceIntegral (53 / 10 : Rat) (69 / 13 : Rat) (-58 / 1 : Rat) (11 / 1 : Rat)

theorem cell134_check : cell134=(89 / 33800 : Rat) := by decide +kernel

def cell135 : Rat := pieceIntegral (69 / 13 : Rat) (16 / 3 : Rat) (11 / 1 : Rat) (-2 / 1 : Rat)

theorem cell135_check : cell135=(14 / 1521 : Rat) := by decide +kernel

def cell136 : Rat := pieceIntegral (16 / 3 : Rat) (75 / 14 : Rat) (59 / 1 : Rat) (-11 / 1 : Rat)

theorem cell136_check : cell136=(17 / 3528 : Rat) := by decide +kernel

def cell137 : Rat := pieceIntegral (75 / 14 : Rat) (59 / 11 : Rat) (59 / 1 : Rat) (-11 / 1 : Rat) + pieceIntegral (59 / 11 : Rat) (70 / 13 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell137_check : cell137=(1 / 4312 : Rat) := by decide +kernel

def cell138 : Rat := pieceIntegral (70 / 13 : Rat) (11 / 2 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell138_check : cell138=(0 / 1 : Rat) := by decide +kernel

def cell139 : Rat := pieceIntegral (11 / 2 : Rat) (39 / 7 : Rat) (-11 / 1 : Rat) (2 / 1 : Rat)

theorem cell139_check : cell139=(1 / 196 : Rat) := by decide +kernel

def cell140 : Rat := pieceIntegral (39 / 7 : Rat) (67 / 12 : Rat) (67 / 1 : Rat) (-12 / 1 : Rat) + pieceIntegral (67 / 12 : Rat) (28 / 5 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell140_check : cell140=(1 / 1176 : Rat) := by decide +kernel

def cell141 : Rat := pieceIntegral (28 / 5 : Rat) (23 / 4 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell141_check : cell141=(0 / 1 : Rat) := by decide +kernel

def cell142 : Rat := pieceIntegral (23 / 4 : Rat) (75 / 13 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell142_check : cell142=(0 / 1 : Rat) := by decide +kernel

def cell143 : Rat := pieceIntegral (75 / 13 : Rat) (35 / 6 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell143_check : cell143=(0 / 1 : Rat) := by decide +kernel

def cell144 : Rat := pieceIntegral (35 / 6 : Rat) (53 / 9 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell144_check : cell144=(0 / 1 : Rat) := by decide +kernel

def cell145 : Rat := pieceIntegral (53 / 9 : Rat) (59 / 10 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (59 / 10 : Rat) (6 / 1 : Rat) (-59 / 1 : Rat) (10 / 1 : Rat)

theorem cell145_check : cell145=(1 / 20 : Rat) := by decide +kernel

def cell146 : Rat := pieceIntegral (6 / 1 : Rat) (73 / 12 : Rat) (73 / 1 : Rat) (-12 / 1 : Rat) + pieceIntegral (73 / 12 : Rat) (56 / 9 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell146_check : cell146=(1 / 24 : Rat) := by decide +kernel

def cell147 : Rat := pieceIntegral (56 / 9 : Rat) (25 / 4 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell147_check : cell147=(0 / 1 : Rat) := by decide +kernel

def cell148 : Rat := pieceIntegral (25 / 4 : Rat) (69 / 11 : Rat) (-75 / 1 : Rat) (12 / 1 : Rat)

theorem cell148_check : cell148=(3 / 968 : Rat) := by decide +kernel

def cell149 : Rat := pieceIntegral (69 / 11 : Rat) (70 / 11 : Rat) (-6 / 1 : Rat) (1 / 1 : Rat)

theorem cell149_check : cell149=(7 / 242 : Rat) := by decide +kernel

def cell150 : Rat := pieceIntegral (70 / 11 : Rat) (32 / 5 : Rat) (64 / 1 : Rat) (-10 / 1 : Rat) + pieceIntegral (32 / 5 : Rat) (13 / 2 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell150_check : cell150=(4 / 605 : Rat) := by decide +kernel

def cell151 : Rat := pieceIntegral (13 / 2 : Rat) (53 / 8 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell151_check : cell151=(0 / 1 : Rat) := by decide +kernel

def cell152 : Rat := pieceIntegral (53 / 8 : Rat) (61 / 9 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (61 / 9 : Rat) (75 / 11 : Rat) (-61 / 1 : Rat) (9 / 1 : Rat)

theorem cell152_check : cell152=(8 / 1089 : Rat) := by decide +kernel

def cell153 : Rat := pieceIntegral (75 / 11 : Rat) (48 / 7 : Rat) (-61 / 1 : Rat) (9 / 1 : Rat)

theorem cell153_check : cell153=(249 / 11858 : Rat) := by decide +kernel

def cell154 : Rat := pieceIntegral (48 / 7 : Rat) (62 / 9 : Rat) (-13 / 1 : Rat) (2 / 1 : Rat) + pieceIntegral (62 / 9 : Rat) (69 / 10 : Rat) (-75 / 1 : Rat) (11 / 1 : Rat)

theorem cell154_check : cell154=(2911 / 88200 : Rat) := by decide +kernel

def cell155 : Rat := pieceIntegral (69 / 10 : Rat) (7 / 1 : Rat) (-6 / 1 : Rat) (1 / 1 : Rat)

theorem cell155_check : cell155=(19 / 200 : Rat) := by decide +kernel

def cell156 : Rat := pieceIntegral (7 / 1 : Rat) (78 / 11 : Rat) (64 / 1 : Rat) (-9 / 1 : Rat)

theorem cell156_check : cell156=(13 / 242 : Rat) := by decide +kernel

def cell157 : Rat := pieceIntegral (78 / 11 : Rat) (64 / 9 : Rat) (64 / 1 : Rat) (-9 / 1 : Rat) + pieceIntegral (64 / 9 : Rat) (22 / 3 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell157_check : cell157=(2 / 1089 : Rat) := by decide +kernel

def cell158 : Rat := pieceIntegral (22 / 3 : Rat) (15 / 2 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell158_check : cell158=(0 / 1 : Rat) := by decide +kernel

def cell159 : Rat := pieceIntegral (15 / 2 : Rat) (53 / 7 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell159_check : cell159=(0 / 1 : Rat) := by decide +kernel

def cell160 : Rat := pieceIntegral (53 / 7 : Rat) (23 / 3 : Rat) (-53 / 1 : Rat) (7 / 1 : Rat)

theorem cell160_check : cell160=(2 / 63 : Rat) := by decide +kernel

def cell161 : Rat := pieceIntegral (23 / 3 : Rat) (54 / 7 : Rat) (16 / 1 : Rat) (-2 / 1 : Rat) + pieceIntegral (54 / 7 : Rat) (70 / 9 : Rat) (-65 / 1 : Rat) (17 / 2 : Rat)

theorem cell161_check : cell161=(47 / 567 : Rat) := by decide +kernel

def cell162 : Rat := pieceIntegral (70 / 9 : Rat) (39 / 5 : Rat) (5 / 1 : Rat) (-1 / 2 : Rat)

theorem cell162_check : cell162=(199 / 8100 : Rat) := by decide +kernel

def cell163 : Rat := pieceIntegral (39 / 5 : Rat) (134 / 17 : Rat) (83 / 1 : Rat) (-21 / 2 : Rat) + pieceIntegral (134 / 17 : Rat) (8 / 1 : Rat) (16 / 1 : Rat) (-2 / 1 : Rat)

theorem cell163_check : cell163=(117 / 1700 : Rat) := by decide +kernel

def cell164 : Rat := pieceIntegral (8 / 1 : Rat) (25 / 3 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell164_check : cell164=(0 / 1 : Rat) := by decide +kernel

def cell165 : Rat := pieceIntegral (25 / 3 : Rat) (146 / 17 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (146 / 17 : Rat) (69 / 8 : Rat) (-73 / 1 : Rat) (17 / 2 : Rat)

theorem cell165_check : cell165=(25 / 4352 : Rat) := by decide +kernel

def cell166 : Rat := pieceIntegral (69 / 8 : Rat) (26 / 3 : Rat) (-73 / 1 : Rat) (17 / 2 : Rat)

theorem cell166_check : cell166=(47 / 2304 : Rat) := by decide +kernel

def cell167 : Rat := pieceIntegral (26 / 3 : Rat) (35 / 4 : Rat) (5 / 1 : Rat) (-1 / 2 : Rat)

theorem cell167_check : cell167=(31 / 576 : Rat) := by decide +kernel

def cell168 : Rat := pieceIntegral (35 / 4 : Rat) (150 / 17 : Rat) (75 / 1 : Rat) (-17 / 2 : Rat) + pieceIntegral (150 / 17 : Rat) (53 / 6 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell168_check : cell168=(25 / 1088 : Rat) := by decide +kernel

def cell169 : Rat := pieceIntegral (53 / 6 : Rat) (9 / 1 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell169_check : cell169=(0 / 1 : Rat) := by decide +kernel

def cell170 : Rat := pieceIntegral (9 / 1 : Rat) (28 / 3 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell170_check : cell170=(0 / 1 : Rat) := by decide +kernel

def cell171 : Rat := pieceIntegral (28 / 3 : Rat) (75 / 8 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell171_check : cell171=(0 / 1 : Rat) := by decide +kernel

def cell172 : Rat := pieceIntegral (75 / 8 : Rat) (48 / 5 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell172_check : cell172=(0 / 1 : Rat) := by decide +kernel

def cell173 : Rat := pieceIntegral (48 / 5 : Rat) (39 / 4 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell173_check : cell173=(0 / 1 : Rat) := by decide +kernel

def cell174 : Rat := pieceIntegral (39 / 4 : Rat) (128 / 13 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (128 / 13 : Rat) (69 / 7 : Rat) (-64 / 1 : Rat) (13 / 2 : Rat)

theorem cell174_check : cell174=(1 / 2548 : Rat) := by decide +kernel

def cell175 : Rat := pieceIntegral (69 / 7 : Rat) (10 / 1 : Rat) (5 / 1 : Rat) (-1 / 2 : Rat)

theorem cell175_check : cell175=(1 / 196 : Rat) := by decide +kernel

def cell176 : Rat := pieceIntegral (10 / 1 : Rat) (53 / 5 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell176_check : cell176=(0 / 1 : Rat) := by decide +kernel

def cell177 : Rat := pieceIntegral (53 / 5 : Rat) (75 / 7 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell177_check : cell177=(0 / 1 : Rat) := by decide +kernel

def cell178 : Rat := pieceIntegral (75 / 7 : Rat) (11 / 1 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell178_check : cell178=(0 / 1 : Rat) := by decide +kernel

def cell179 : Rat := pieceIntegral (11 / 1 : Rat) (78 / 7 : Rat) (-11 / 1 : Rat) (1 / 1 : Rat)

theorem cell179_check : cell179=(1 / 98 : Rat) := by decide +kernel

def cell180 : Rat := pieceIntegral (78 / 7 : Rat) (67 / 6 : Rat) (67 / 1 : Rat) (-6 / 1 : Rat) + pieceIntegral (67 / 6 : Rat) (56 / 5 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell180_check : cell180=(1 / 588 : Rat) := by decide +kernel

def cell181 : Rat := pieceIntegral (56 / 5 : Rat) (23 / 2 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell181_check : cell181=(0 / 1 : Rat) := by decide +kernel

def cell182 : Rat := pieceIntegral (23 / 2 : Rat) (35 / 3 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell182_check : cell182=(0 / 1 : Rat) := by decide +kernel

def cell183 : Rat := pieceIntegral (35 / 3 : Rat) (59 / 5 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (59 / 5 : Rat) (12 / 1 : Rat) (-59 / 1 : Rat) (5 / 1 : Rat)

theorem cell183_check : cell183=(1 / 10 : Rat) := by decide +kernel

def cell184 : Rat := pieceIntegral (12 / 1 : Rat) (25 / 2 : Rat) (-5 / 1 : Rat) (1 / 2 : Rat)

theorem cell184_check : cell184=(9 / 16 : Rat) := by decide +kernel

def cell185 : Rat := pieceIntegral (25 / 2 : Rat) (13 / 1 : Rat) (-5 / 1 : Rat) (1 / 2 : Rat)

theorem cell185_check : cell185=(11 / 16 : Rat) := by decide +kernel

def cell186 : Rat := pieceIntegral (13 / 1 : Rat) (53 / 4 : Rat) (73 / 1 : Rat) (-11 / 2 : Rat)

theorem cell186_check : cell186=(13 / 64 : Rat) := by decide +kernel

def cell187 : Rat := pieceIntegral (53 / 4 : Rat) (146 / 11 : Rat) (73 / 1 : Rat) (-11 / 2 : Rat) + pieceIntegral (146 / 11 : Rat) (150 / 11 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (150 / 11 : Rat) (69 / 5 : Rat) (-75 / 1 : Rat) (11 / 2 : Rat)

theorem cell187_check : cell187=(1321 / 17600 : Rat) := by decide +kernel

def cell188 : Rat := pieceIntegral (69 / 5 : Rat) (14 / 1 : Rat) (-6 / 1 : Rat) (1 / 2 : Rat)

theorem cell188_check : cell188=(19 / 100 : Rat) := by decide +kernel

def cell189 : Rat := pieceIntegral (14 / 1 : Rat) (128 / 9 : Rat) (64 / 1 : Rat) (-9 / 2 : Rat) + pieceIntegral (128 / 9 : Rat) (15 / 1 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell189_check : cell189=(1 / 9 : Rat) := by decide +kernel

def cell190 : Rat := pieceIntegral (15 / 1 : Rat) (106 / 7 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (106 / 7 : Rat) (78 / 5 : Rat) (-53 / 1 : Rat) (7 / 2 : Rat)

theorem cell190_check : cell190=(64 / 175 : Rat) := by decide +kernel

def cell191 : Rat := pieceIntegral (78 / 5 : Rat) (16 / 1 : Rat) (25 / 1 : Rat) (-3 / 2 : Rat)

theorem cell191_check : cell191=(13 / 25 : Rat) := by decide +kernel

def cell192 : Rat := pieceIntegral (16 / 1 : Rat) (178 / 11 : Rat) (73 / 1 : Rat) (-9 / 2 : Rat) + pieceIntegral (178 / 11 : Rat) (118 / 7 : Rat) (-16 / 1 : Rat) (1 / 1 : Rat) + pieceIntegral (118 / 7 : Rat) (69 / 4 : Rat) (-75 / 1 : Rat) (9 / 2 : Rat)

theorem cell192_check : cell192=(5629 / 4928 : Rat) := by decide +kernel

def cell193 : Rat := pieceIntegral (69 / 4 : Rat) (35 / 2 : Rat) (-6 / 1 : Rat) (1 / 2 : Rat)

theorem cell193_check : cell193=(43 / 64 : Rat) := by decide +kernel

def cell194 : Rat := pieceIntegral (35 / 2 : Rat) (53 / 3 : Rat) (64 / 1 : Rat) (-7 / 2 : Rat)

theorem cell194_check : cell194=(59 / 144 : Rat) := by decide +kernel

def cell195 : Rat := pieceIntegral (53 / 3 : Rat) (128 / 7 : Rat) (64 / 1 : Rat) (-7 / 2 : Rat) + pieceIntegral (128 / 7 : Rat) (56 / 3 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell195_check : cell195=(169 / 252 : Rat) := by decide +kernel

def cell196 : Rat := pieceIntegral (56 / 3 : Rat) (75 / 4 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell196_check : cell196=(0 / 1 : Rat) := by decide +kernel

def cell197 : Rat := pieceIntegral (75 / 4 : Rat) (39 / 2 : Rat) (0 / 1 : Rat) (0 / 1 : Rat)

theorem cell197_check : cell197=(0 / 1 : Rat) := by decide +kernel

def cell198 : Rat := pieceIntegral (39 / 2 : Rat) (64 / 3 : Rat) (0 / 1 : Rat) (0 / 1 : Rat) + pieceIntegral (64 / 3 : Rat) (22 / 1 : Rat) (-64 / 1 : Rat) (3 / 1 : Rat)

theorem cell198_check : cell198=(2 / 3 : Rat) := by decide +kernel

def cell199 : Rat := pieceIntegral (22 / 1 : Rat) (23 / 1 : Rat) (-64 / 1 : Rat) (3 / 1 : Rat)

theorem cell199_check : cell199=(7 / 2 : Rat) := by decide +kernel

def cell200 : Rat := pieceIntegral (23 / 1 : Rat) (70 / 3 : Rat) (5 / 1 : Rat) (0 / 1 : Rat)

theorem cell200_check : cell200=(5 / 3 : Rat) := by decide +kernel

def cell201 : Rat := pieceIntegral (70 / 3 : Rat) (24 / 1 : Rat) (5 / 1 : Rat) (0 / 1 : Rat)

theorem cell201_check : cell201=(10 / 3 : Rat) := by decide +kernel

def cell202 : Rat := pieceIntegral (24 / 1 : Rat) (25 / 1 : Rat) (53 / 1 : Rat) (-2 / 1 : Rat)

theorem cell202_check : cell202=(4 / 1 : Rat) := by decide +kernel

def cell203 : Rat := pieceIntegral (25 / 1 : Rat) (26 / 1 : Rat) (53 / 1 : Rat) (-2 / 1 : Rat)

theorem cell203_check : cell203=(2 / 1 : Rat) := by decide +kernel

def cell204 : Rat := pieceIntegral (26 / 1 : Rat) (53 / 2 : Rat) (53 / 1 : Rat) (-2 / 1 : Rat)

theorem cell204_check : cell204=(1 / 4 : Rat) := by decide +kernel

def integratedProfile : Rat := cell000 + cell001 + cell002 + cell003 + cell004 + cell005 + cell006 + cell007 + cell008 + cell009 + cell010 + cell011 + cell012 + cell013 + cell014 + cell015 + cell016 + cell017 + cell018 + cell019 + cell020 + cell021 + cell022 + cell023 + cell024 + cell025 + cell026 + cell027 + cell028 + cell029 + cell030 + cell031 + cell032 + cell033 + cell034 + cell035 + cell036 + cell037 + cell038 + cell039 + cell040 + cell041 + cell042 + cell043 + cell044 + cell045 + cell046 + cell047 + cell048 + cell049 + cell050 + cell051 + cell052 + cell053 + cell054 + cell055 + cell056 + cell057 + cell058 + cell059 + cell060 + cell061 + cell062 + cell063 + cell064 + cell065 + cell066 + cell067 + cell068 + cell069 + cell070 + cell071 + cell072 + cell073 + cell074 + cell075 + cell076 + cell077 + cell078 + cell079 + cell080 + cell081 + cell082 + cell083 + cell084 + cell085 + cell086 + cell087 + cell088 + cell089 + cell090 + cell091 + cell092 + cell093 + cell094 + cell095 + cell096 + cell097 + cell098 + cell099 + cell100 + cell101 + cell102 + cell103 + cell104 + cell105 + cell106 + cell107 + cell108 + cell109 + cell110 + cell111 + cell112 + cell113 + cell114 + cell115 + cell116 + cell117 + cell118 + cell119 + cell120 + cell121 + cell122 + cell123 + cell124 + cell125 + cell126 + cell127 + cell128 + cell129 + cell130 + cell131 + cell132 + cell133 + cell134 + cell135 + cell136 + cell137 + cell138 + cell139 + cell140 + cell141 + cell142 + cell143 + cell144 + cell145 + cell146 + cell147 + cell148 + cell149 + cell150 + cell151 + cell152 + cell153 + cell154 + cell155 + cell156 + cell157 + cell158 + cell159 + cell160 + cell161 + cell162 + cell163 + cell164 + cell165 + cell166 + cell167 + cell168 + cell169 + cell170 + cell171 + cell172 + cell173 + cell174 + cell175 + cell176 + cell177 + cell178 + cell179 + cell180 + cell181 + cell182 + cell183 + cell184 + cell185 + cell186 + cell187 + cell188 + cell189 + cell190 + cell191 + cell192 + cell193 + cell194 + cell195 + cell196 + cell197 + cell198 + cell199 + cell200 + cell201 + cell202 + cell203 + cell204

theorem integratedProfile_exact : integratedProfile=(534121468871212736197 / 24183176360959455840 : Rat) := by
  simp only [integratedProfile, cell000_check, cell001_check, cell002_check, cell003_check, cell004_check, cell005_check, cell006_check, cell007_check, cell008_check, cell009_check, cell010_check, cell011_check, cell012_check, cell013_check, cell014_check, cell015_check, cell016_check, cell017_check, cell018_check, cell019_check, cell020_check, cell021_check, cell022_check, cell023_check, cell024_check, cell025_check, cell026_check, cell027_check, cell028_check, cell029_check, cell030_check, cell031_check, cell032_check, cell033_check, cell034_check, cell035_check, cell036_check, cell037_check, cell038_check, cell039_check, cell040_check, cell041_check, cell042_check, cell043_check, cell044_check, cell045_check, cell046_check, cell047_check, cell048_check, cell049_check, cell050_check, cell051_check, cell052_check, cell053_check, cell054_check, cell055_check, cell056_check, cell057_check, cell058_check, cell059_check, cell060_check, cell061_check, cell062_check, cell063_check, cell064_check, cell065_check, cell066_check, cell067_check, cell068_check, cell069_check, cell070_check, cell071_check, cell072_check, cell073_check, cell074_check, cell075_check, cell076_check, cell077_check, cell078_check, cell079_check, cell080_check, cell081_check, cell082_check, cell083_check, cell084_check, cell085_check, cell086_check, cell087_check, cell088_check, cell089_check, cell090_check, cell091_check, cell092_check, cell093_check, cell094_check, cell095_check, cell096_check, cell097_check, cell098_check, cell099_check, cell100_check, cell101_check, cell102_check, cell103_check, cell104_check, cell105_check, cell106_check, cell107_check, cell108_check, cell109_check, cell110_check, cell111_check, cell112_check, cell113_check, cell114_check, cell115_check, cell116_check, cell117_check, cell118_check, cell119_check, cell120_check, cell121_check, cell122_check, cell123_check, cell124_check, cell125_check, cell126_check, cell127_check, cell128_check, cell129_check, cell130_check, cell131_check, cell132_check, cell133_check, cell134_check, cell135_check, cell136_check, cell137_check, cell138_check, cell139_check, cell140_check, cell141_check, cell142_check, cell143_check, cell144_check, cell145_check, cell146_check, cell147_check, cell148_check, cell149_check, cell150_check, cell151_check, cell152_check, cell153_check, cell154_check, cell155_check, cell156_check, cell157_check, cell158_check, cell159_check, cell160_check, cell161_check, cell162_check, cell163_check, cell164_check, cell165_check, cell166_check, cell167_check, cell168_check, cell169_check, cell170_check, cell171_check, cell172_check, cell173_check, cell174_check, cell175_check, cell176_check, cell177_check, cell178_check, cell179_check, cell180_check, cell181_check, cell182_check, cell183_check, cell184_check, cell185_check, cell186_check, cell187_check, cell188_check, cell189_check, cell190_check, cell191_check, cell192_check, cell193_check, cell194_check, cell195_check, cell196_check, cell197_check, cell198_check, cell199_check, cell200_check, cell201_check, cell202_check, cell203_check, cell204_check]
  decide +kernel

theorem integratedProfile_target : (2191363/100000 : Rat) < integratedProfile := by
  rw [integratedProfile_exact]
  decide +kernel

#print axioms integratedProfile_exact

end CatalanMeasure.GenD.Uniform.Bank.Profile205
