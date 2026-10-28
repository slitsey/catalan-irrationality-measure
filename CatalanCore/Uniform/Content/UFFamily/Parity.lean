module

public import CatalanCore.Uniform.Content.UFFamily.Realize

@[expose] public section

/-!
# UF families: parity of `mkFib` with the Python generator (lane H10)

The 14 joint types of sevenths class 1 (`q = 7`, `a = 1`, so `o = 6`, `p mod 7 = 1`, `nrm = 1`, `u₀ = 2`)
are given only by the pairs `(⌊c/p⌋, ⌊(7c-6)/p⌋)` of their nodes.  The kernel evaluates
`IntOK` (the common denominator clears every entry) and the integer data `mkFib`, which equals entry
for entry the data produced by `gen_pilot.py` from the Python values `(digit, L, E)`.
-/

open CatalanCore.Uniform.Content.UFFamily

namespace CatalanCore.Uniform.Content.UFFamily.Parity

def par1 : JType := { nodes := [(0, 0), (1, 1), (2, 8), (3, 15), (4, 22), (5, 29)], zone := (6, 36) }
theorem par1_ok : IntOK 7 6 1 1 2 par1 4396075200 := by decide +kernel
theorem par1_val : (mkFib 7 6 1 1 2 par1 4396075200).M = [[8792150400, -26376451200, -14012489700, -9537040920, -7227713790, -5818552344], [-26376451200, 219803760000, -1648528200, -1117335780, -844801320, -679077630], [-14012489700, -1648528200, 222070486275, -586143360, -442937880, -355927440], [-9537040920, -1117335780, -586143360, 222539400963, -299732400, -240819480], [-7227713790, -844801320, -442937880, -299732400, 222709703463, -181906560], [-5818552344, -679077630, -355927440, -240819480, -181906560, 222789993255]] ∧ (mkFib 7 6 1 1 2 par1 4396075200).s = [-4869145820, -567684744, -297473880, -201250720, -152009880, -122113200] ∧ (mkFib 7 6 1 1 2 par1 4396075200).u = [0, -26376451200, -28024979400, -28611122760, -28910855160, -29092761720] ∧ (mkFib 7 6 1 1 2 par1 4396075200).z = -29214874920 := by decide +kernel
-- size 6
def par2 : JType := { nodes := [(0, 1), (1, 8), (2, 15), (3, 22), (4, 29), (5, 36)], zone := (6, 43) }
theorem par2_ok : IntOK 7 6 1 1 2 par2 567093700800 := by decide +kernel
theorem par2_val : (mkFib 7 6 1 1 2 par2 567093700800).M = [[28921778740800, 70886712600, 44894917980, 32794054920, 25817725890, 21284284824], [70886712600, 28788866154675, 18903123360, 13747726080, 10794730320, 8883677880], [44894917980, 18903123360, 28770593135427, 8592328800, 6740533800, 5543862720], [32794054920, 13747726080, 8592328800, 28764995103027, 4888738800, 4019629680], [25817725890, 10794730320, 6740533800, 4888738800, 28762592877927, 3150520560], [21284284824, 8883677880, 5543862720, 4019629680, 3150520560, 28761350172595]] ∧ (mkFib 7 6 1 1 2 par2 567093700800).s = [18103243620, 7546549824, 4707406440, 3412432320, 2674279080, 2198037600] ∧ (mkFib 7 6 1 1 2 par2 567093700800).u = [-3969655905600, -3898769193000, -3879866069640, -3871273740840, -3866385002040, -3863234481480] ∧ (mkFib 7 6 1 1 2 par2 567093700800).z = -3861036443880 := by decide +kernel
-- size 6
def par3 : JType := { nodes := [(0, 1), (1, 8), (2, 15), (3, 22), (4, 29)], zone := (5, 36) }
theorem par3_ok : IntOK 7 6 1 1 2 par3 4396075200 := by decide +kernel
theorem par3_val : (mkFib 7 6 1 1 2 par3 4396075200).M = [[224199835200, 549509400, 348022620, 254217480, 200137410], [549509400, 223169505075, 146535840, 106571520, 83680080], [348022620, 146535840, 223027853763, 66607200, 52252200], [254217480, 106571520, 66607200, 222984458163, 37897200], [200137410, 83680080, 52252200, 37897200, 222965836263]] ∧ (mkFib 7 6 1 1 2 par3 4396075200).s = [164994456, 68865720, 42975680, 31159920, 24422640] ∧ (mkFib 7 6 1 1 2 par3 4396075200).u = [-30772526400, -30223017000, -30076481160, -30009873960, -29971976760] ∧ (mkFib 7 6 1 1 2 par3 4396075200).z = -29947554120 := by decide +kernel
-- size 5
def par4 : JType := { nodes := [(0, 0), (1, 1), (2, 8), (3, 15), (4, 22)], zone := (5, 29) }
theorem par4_ok : IntOK 7 6 1 1 2 par4 50529600 := by decide +kernel
theorem par4_val : (mkFib 7 6 1 1 2 par4 50529600).M = [[101059200, -303177600, -161063100, -109621160, -83077170], [-303177600, 2526480000, -18948600, -12842940, -9710360], [-161063100, -18948600, 2552534325, -6737280, -5091240], [-109621160, -12842940, -6737280, 2557924149, -3445200], [-83077170, -9710360, -5091240, -3445200, 2559881649]] ∧ (mkFib 7 6 1 1 2 par4 50529600).s = [-66879912, -7805490, -4091120, -2768040, -2090880] ∧ (mkFib 7 6 1 1 2 par4 50529600).u = [0, -303177600, -322126200, -328863480, -332308680] ∧ (mkFib 7 6 1 1 2 par4 50529600).z = -334399560 := by decide +kernel
-- size 5
def par5 : JType := { nodes := [(0, 1), (1, 8), (2, 15), (3, 22)], zone := (4, 29) }
theorem par5_ok : IntOK 7 6 1 1 2 par5 50529600 := by decide +kernel
theorem par5_val : (mkFib 7 6 1 1 2 par5 50529600).M = [[2577009600, 6316200, 4000260, 2922040], [6316200, 2565166725, 1684320, 1224960], [4000260, 1684320, 2563538549, 765600], [2922040, 1224960, 765600, 2563039749]] ∧ (mkFib 7 6 1 1 2 par5 50529600).s = [2300430, 961840, 600600, 435600] ∧ (mkFib 7 6 1 1 2 par5 50529600).u = [-353707200, -347391000, -345706680, -344941080] ∧ (mkFib 7 6 1 1 2 par5 50529600).z = -344505480 := by decide +kernel
-- size 4
def par6 : JType := { nodes := [(0, 0), (1, 1), (2, 8), (3, 15)], zone := (4, 22) }
theorem par6_ok : IntOK 7 6 1 1 2 par6 158400 := by decide +kernel
theorem par6_val : (mkFib 7 6 1 1 2 par6 158400).M = [[316800, -950400, -504900, -343640], [-950400, 7920000, -59400, -40260], [-504900, -59400, 8001675, -21120], [-343640, -40260, -21120, 8018571]] ∧ (mkFib 7 6 1 1 2 par6 158400).s = [-260430, -30440, -15960, -10800] ∧ (mkFib 7 6 1 1 2 par6 158400).u = [0, -950400, -1009800, -1030920] ∧ (mkFib 7 6 1 1 2 par6 158400).z = -1041720 := by decide +kernel
-- size 4
def par7 : JType := { nodes := [(0, 1), (1, 8), (2, 15)], zone := (3, 22) }
theorem par7_ok : IntOK 7 6 1 1 2 par7 158400 := by decide +kernel
theorem par7_val : (mkFib 7 6 1 1 2 par7 158400).M = [[8078400, 19800, 12540], [19800, 8041275, 5280], [12540, 5280, 8036171]] ∧ (mkFib 7 6 1 1 2 par7 158400).s = [9160, 3840, 2400] ∧ (mkFib 7 6 1 1 2 par7 158400).u = [-1108800, -1089000, -1083720] ∧ (mkFib 7 6 1 1 2 par7 158400).z = -1081320 := by decide +kernel
-- size 3
def par8 : JType := { nodes := [(0, 0), (1, 1), (2, 8)], zone := (3, 15) }
theorem par8_ok : IntOK 7 6 1 1 2 par8 2880 := by decide +kernel
theorem par8_val : (mkFib 7 6 1 1 2 par8 2880).M = [[5760, -17280, -9180], [-17280, 144000, -1080], [-9180, -1080, 145485]] ∧ (mkFib 7 6 1 1 2 par8 2880).s = [-6248, -732, -384] ∧ (mkFib 7 6 1 1 2 par8 2880).u = [0, -17280, -18360] ∧ (mkFib 7 6 1 1 2 par8 2880).z = -18744 := by decide +kernel
-- size 3
def par9 : JType := { nodes := [(0, 1), (1, 8)], zone := (2, 15) }
theorem par9_ok : IntOK 7 6 1 1 2 par9 960 := by decide +kernel
theorem par9_val : (mkFib 7 6 1 1 2 par9 960).M = [[48960, 120], [120, 48735]] ∧ (mkFib 7 6 1 1 2 par9 960).s = [76, 32] ∧ (mkFib 7 6 1 1 2 par9 960).u = [-6720, -6600] ∧ (mkFib 7 6 1 1 2 par9 960).z = -6568 := by decide +kernel
-- size 2
def par10 : JType := { nodes := [(0, 0), (1, 1)], zone := (2, 8) }
theorem par10_ok : IntOK 7 6 1 1 2 par10 16 := by decide +kernel
theorem par10_val : (mkFib 7 6 1 1 2 par10 16).M = [[32, -96], [-96, 800]] ∧ (mkFib 7 6 1 1 2 par10 16).s = [-51, -6] ∧ (mkFib 7 6 1 1 2 par10 16).u = [0, -96] ∧ (mkFib 7 6 1 1 2 par10 16).z = -102 := by decide +kernel
-- size 2
def par11 : JType := { nodes := [(0, 1)], zone := (1, 8) }
theorem par11_ok : IntOK 7 6 1 1 2 par11 8 := by decide +kernel
theorem par11_val : (mkFib 7 6 1 1 2 par11 8).M = [[408]] ∧ (mkFib 7 6 1 1 2 par11 8).s = [1] ∧ (mkFib 7 6 1 1 2 par11 8).u = [-56] ∧ (mkFib 7 6 1 1 2 par11 8).z = -55 := by decide +kernel
-- size 1
def par12 : JType := { nodes := [(0, 0)], zone := (1, 1) }
theorem par12_ok : IntOK 7 6 1 1 2 par12 1 := by decide +kernel
theorem par12_val : (mkFib 7 6 1 1 2 par12 1).M = [[2]] ∧ (mkFib 7 6 1 1 2 par12 1).s = [-6] ∧ (mkFib 7 6 1 1 2 par12 1).u = [0] ∧ (mkFib 7 6 1 1 2 par12 1).z = -6 := by decide +kernel
-- size 1
def par13 : JType := { nodes := [], zone := (0, 1) }
theorem par13_ok : IntOK 7 6 1 1 2 par13 1 := by decide +kernel
theorem par13_val : (mkFib 7 6 1 1 2 par13 1).M = [] ∧ (mkFib 7 6 1 1 2 par13 1).s = [] ∧ (mkFib 7 6 1 1 2 par13 1).u = [] ∧ (mkFib 7 6 1 1 2 par13 1).z = -7 := by decide +kernel
-- size 0
def par14 : JType := { nodes := [], zone := (0, 0) }
theorem par14_ok : IntOK 7 6 1 1 2 par14 1 := by decide +kernel
theorem par14_val : (mkFib 7 6 1 1 2 par14 1).M = [] ∧ (mkFib 7 6 1 1 2 par14 1).s = [] ∧ (mkFib 7 6 1 1 2 par14 1).u = [] ∧ (mkFib 7 6 1 1 2 par14 1).z = 0 := by decide +kernel
-- size 0

end CatalanCore.Uniform.Content.UFFamily.Parity
