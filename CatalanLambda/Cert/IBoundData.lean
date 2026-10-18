import CatalanLambda.Cert.Bridge

/-! Generated (gen_I.py): I_rho(sigma) upper bound; 300 rows in 10 chunks of 30. -/
namespace CatalanLambda.Cert

set_option maxRecDepth 100000

def qII (p q : Pt) : ℕ := (p.1 - q.1).natAbs ^ 2 + (p.2.1 - q.2.1).natAbs ^ 2 + 2 ^ 60

def iRow (p : Pt) : List Pt → ℤ
  | [] => 0
  | q :: qs => (q.2.2 : ℤ) * logLoS (qII p q) + iRow p qs

def iTot : List Pt → ℤ
  | [] => 0
  | p :: ps => (p.2.2 : ℤ) * iRow p sigmaS + iTot ps

def iChunk (r : ℕ) : List Pt := (sigmaS.drop (30 * r)).take 30

theorem iChunk_0 : iTot (iChunk 0) = (-92610528074455902600883680655004381652 : ℤ) := by decide +kernel
theorem iChunk_1 : iTot (iChunk 1) = (-113875246751935060282401872445656553812 : ℤ) := by decide +kernel
theorem iChunk_2 : iTot (iChunk 2) = (-128782790317623434983483205176123439326 : ℤ) := by decide +kernel
theorem iChunk_3 : iTot (iChunk 3) = (-140747920453254925329470090904044916570 : ℤ) := by decide +kernel
theorem iChunk_4 : iTot (iChunk 4) = (-150927466070427850959434573451021172218 : ℤ) := by decide +kernel
theorem iChunk_5 : iTot (iChunk 5) = (-159794012265223239294584759426852564680 : ℤ) := by decide +kernel
theorem iChunk_6 : iTot (iChunk 6) = (-167493460544132176890503020541414075410 : ℤ) := by decide +kernel
theorem iChunk_7 : iTot (iChunk 7) = (-170789715255267767751552451055939560488 : ℤ) := by decide +kernel
theorem iChunk_8 : iTot (iChunk 8) = (-162541288517334917080537586916212991837 : ℤ) := by decide +kernel
theorem iChunk_9 : iTot (iChunk 9) = (-148919593169615267880775381422180560269 : ℤ) := by decide +kernel

theorem sigmaS_chunks : sigmaS = iChunk 0 ++ iChunk 1 ++ iChunk 2 ++ iChunk 3 ++ iChunk 4 ++ iChunk 5 ++ iChunk 6 ++ iChunk 7 ++ iChunk 8 ++ iChunk 9 := by decide +kernel

def IBOUND : ℚ := 211073 / 100000

end CatalanLambda.Cert
