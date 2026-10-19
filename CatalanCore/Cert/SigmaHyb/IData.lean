module

public import CatalanCore.Cert.SigmaHyb.HSymm
public import CatalanLambda.Cert.IBound

@[expose] public section

/-! Generated (emitI.py): cross and lambda-lambda energy sums, chunked. -/
namespace CatalanCore.Cert.SigmaHyb

open CatalanLambda.Cert

set_option maxRecDepth 100000

def iTotL (B : List Pt) : List Pt → ℤ
  | [] => 0
  | p :: ps => (p.2.2 : ℤ) * iRow p B + iTotL B ps

def sChunk (r : ℕ) : List Pt := (sigmaS.drop (30 * r)).take 30
def lChunk (r : ℕ) : List Pt := (lamS.drop (30 * r)).take 30

theorem X1_0 : iTotL lamS (sChunk 0) = (-13701570181109005285710320787288129950 : ℤ) := by decide +kernel
theorem X1_1 : iTotL lamS (sChunk 1) = (-13965209530498305758975643930654077928 : ℤ) := by decide +kernel
theorem X1_2 : iTotL lamS (sChunk 2) = (-14128904428093205043696773061540947548 : ℤ) := by decide +kernel
theorem X1_3 : iTotL lamS (sChunk 3) = (-14238999217309900191036785266865274094 : ℤ) := by decide +kernel
theorem X1_4 : iTotL lamS (sChunk 4) = (-14333137431918379770951696718713506070 : ℤ) := by decide +kernel
theorem X1_5 : iTotL lamS (sChunk 5) = (-14412666939998184088861338437863689262 : ℤ) := by decide +kernel
theorem X1_6 : iTotL lamS (sChunk 6) = (-14468358644747903065845017666950504972 : ℤ) := by decide +kernel
theorem X1_7 : iTotL lamS (sChunk 7) = (-13877344766817266239553413722083659239 : ℤ) := by decide +kernel
theorem X1_8 : iTotL lamS (sChunk 8) = (-12403513258286893336443661626466907330 : ℤ) := by decide +kernel
theorem X1_9 : iTotL lamS (sChunk 9) = (-11350131001147599224619431227833284401 : ℤ) := by decide +kernel
theorem X2_0 : iTotL lamS (lChunk 0) = (-5020580667134983122617517846513186742 : ℤ) := by decide +kernel
theorem X2_1 : iTotL lamS (lChunk 1) = (-3349533360244087068194287347526656074 : ℤ) := by decide +kernel
theorem X2_2 : iTotL lamS (lChunk 2) = (-2686521816875113619444161078360347612 : ℤ) := by decide +kernel
theorem X2_3 : iTotL lamS (lChunk 3) = (-2504348845493477035985007194616284324 : ℤ) := by decide +kernel
theorem X2_4 : iTotL lamS (lChunk 4) = (-2514680223878284551831349813714628078 : ℤ) := by decide +kernel
theorem X2_5 : iTotL lamS (lChunk 5) = (-1186408827641668864992313609158271316 : ℤ) := by decide +kernel

theorem sigmaS_chunks' : sigmaS = sChunk 0 ++ sChunk 1 ++ sChunk 2 ++ sChunk 3 ++ sChunk 4 ++ sChunk 5 ++ sChunk 6 ++ sChunk 7 ++ sChunk 8 ++ sChunk 9 := by decide +kernel
theorem lamS_chunks : lamS = lChunk 0 ++ lChunk 1 ++ lChunk 2 ++ lChunk 3 ++ lChunk 4 ++ lChunk 5 := by decide +kernel

end CatalanCore.Cert.SigmaHyb
