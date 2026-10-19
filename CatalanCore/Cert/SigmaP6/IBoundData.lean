module

public import CatalanCore.Cert.SigmaP6.Bridge

@[expose] public section

/-! Generated (genI.py): I_rho(sigma) upper bound; 699 rows in 24 chunks of 30. -/
namespace CatalanCore.Cert.SigmaP6

open CatalanLambda.Cert

set_option maxRecDepth 100000

def qII (p q : Pt) : ℕ := (p.1 - q.1).natAbs ^ 2 + (p.2.1 - q.2.1).natAbs ^ 2 + 2 ^ 58

def iRow (p : Pt) : List Pt → ℤ
  | [] => 0
  | q :: qs => (q.2.2 : ℤ) * logLoS (qII p q) + iRow p qs

def iTot : List Pt → ℤ
  | [] => 0
  | p :: ps => (p.2.2 : ℤ) * iRow p sigD + iTot ps

def iChunk (r : ℕ) : List Pt := (sigD.drop (30 * r)).take 30

lemma iTot_append (a b : List Pt) : iTot (a ++ b) = iTot a + iTot b := by
  induction a with
  | nil => simp [iTot]
  | cons p ps ih => simp only [List.cons_append, iTot, ih]; ring

theorem iChunk_0 : iTot (iChunk 0) = (-9870436749204648718420646399797245458 : ℤ) := by decide +kernel
theorem iChunk_1 : iTot (iChunk 1) = (-40060108900722691910920870752487664224 : ℤ) := by decide +kernel
theorem iChunk_2 : iTot (iChunk 2) = (-44361869941468814161574594068757382918 : ℤ) := by decide +kernel
theorem iChunk_3 : iTot (iChunk 3) = (-47921829955945546729874952336482827816 : ℤ) := by decide +kernel
theorem iChunk_4 : iTot (iChunk 4) = (-51025892924687847236109809382353318236 : ℤ) := by decide +kernel
theorem iChunk_5 : iTot (iChunk 5) = (-53774872721695903664554007355766796510 : ℤ) := by decide +kernel
theorem iChunk_6 : iTot (iChunk 6) = (-56283126636124189440599831137665732500 : ℤ) := by decide +kernel
theorem iChunk_7 : iTot (iChunk 7) = (-58581571989184681821684152423434135464 : ℤ) := by decide +kernel
theorem iChunk_8 : iTot (iChunk 8) = (-60743649216803670722091864837252033902 : ℤ) := by decide +kernel
theorem iChunk_9 : iTot (iChunk 9) = (-62757574844079815115556378087832345536 : ℤ) := by decide +kernel
theorem iChunk_10 : iTot (iChunk 10) = (-64643455324261866884595090001921310678 : ℤ) := by decide +kernel
theorem iChunk_11 : iTot (iChunk 11) = (-66439664020419558137553851599007877934 : ℤ) := by decide +kernel
theorem iChunk_12 : iTot (iChunk 12) = (-68170280373707155921406174512239303098 : ℤ) := by decide +kernel
theorem iChunk_13 : iTot (iChunk 13) = (-69840081482508492597035059187267408304 : ℤ) := by decide +kernel
theorem iChunk_14 : iTot (iChunk 14) = (-71488230543575550838819651587993143848 : ℤ) := by decide +kernel
theorem iChunk_15 : iTot (iChunk 15) = (-73110406936437486245294465035722123816 : ℤ) := by decide +kernel
theorem iChunk_16 : iTot (iChunk 16) = (-74571752785415167550576090251615663843 : ℤ) := by decide +kernel
theorem iChunk_17 : iTot (iChunk 17) = (-75431820618082344643476189840475786090 : ℤ) := by decide +kernel
theorem iChunk_18 : iTot (iChunk 18) = (-74812910513665657470164334206883842150 : ℤ) := by decide +kernel
theorem iChunk_19 : iTot (iChunk 19) = (-73652791492135211003341764177656997218 : ℤ) := by decide +kernel
theorem iChunk_20 : iTot (iChunk 20) = (-71869706273948794659567410853737370613 : ℤ) := by decide +kernel
theorem iChunk_21 : iTot (iChunk 21) = (-69448693022993589295375812415688640026 : ℤ) := by decide +kernel
theorem iChunk_22 : iTot (iChunk 22) = (-66135783107971922437700864316950124827 : ℤ) := by decide +kernel
theorem iChunk_23 : iTot (iChunk 23) = (-19044993378352754690153095639550989461 : ℤ) := by decide +kernel

theorem sigD_chunks : sigD = iChunk 0 ++ iChunk 1 ++ iChunk 2 ++ iChunk 3 ++ iChunk 4 ++ iChunk 5 ++ iChunk 6 ++ iChunk 7 ++ iChunk 8 ++ iChunk 9 ++ iChunk 10 ++ iChunk 11 ++ iChunk 12 ++ iChunk 13 ++ iChunk 14 ++ iChunk 15 ++ iChunk 16 ++ iChunk 17 ++ iChunk 18 ++ iChunk 19 ++ iChunk 20 ++ iChunk 21 ++ iChunk 22 ++ iChunk 23 := by decide +kernel

theorem iTot_sigD_val : iTot sigD = (-1424041503753393361896446960408540064470 : ℤ) := by
  conv_lhs => rw [sigD_chunks]
  simp only [iTot_append]
  rw [iChunk_0, iChunk_1, iChunk_2, iChunk_3, iChunk_4, iChunk_5, iChunk_6, iChunk_7, iChunk_8, iChunk_9, iChunk_10, iChunk_11, iChunk_12, iChunk_13, iChunk_14, iChunk_15, iChunk_16, iChunk_17, iChunk_18, iChunk_19, iChunk_20, iChunk_21, iChunk_22, iChunk_23]
  norm_num

def IBOUND : ℚ := 41849 / 20000

end CatalanCore.Cert.SigmaP6
