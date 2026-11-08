module

public import CatalanMeasure.GenD.Signed.RouteI.T4Instance

@[expose] public section

/-!
# T4 leaf data, physical window, steps 0 to 7

The three diagonal checks `wPq`, `phiQ`, `omQ` of GP §9 (c), (d) on each of the steps 0 to 7 of the 64-step cover of
`[0, 51/500]` (design C): one `polyNonneg_of_ints` leaf per check, `checkZ` on an integer list.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys0
open CatalanMeasure.GenD.Signed.RouteI.T4Instance
noncomputable section

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_0 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (3731 / 500000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (0 : ℚ) (51 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [2791083360178047107584000000, -2855211088607143017959648000, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_0 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (13553 / 250000 : ℚ))) (0 : ℚ) (51 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [924491288010748329984, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_0 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (86383 / 1000000 : ℚ))) (0 : ℚ) (51 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [126411591385088, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_1 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (759 / 100000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (51 / 32000 : ℚ) (51 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [2581084900386228976388121923, -2658565127569348284432108154, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_1 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (2187 / 40000 : ℚ))) (51 / 32000 : ℚ) (51 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [879651568754823067879, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_1 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (87121 / 1000000 : ℚ))) (51 / 32000 : ℚ) (51 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [123713305078633, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_2 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (7709 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (51 / 16000 : ℚ) (153 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [2388654223236363018719783692, -2461919166531553550904568308, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_2 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (27551 / 500000 : ℚ))) (51 / 16000 : ℚ) (153 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [836433145364751184334, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_2 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (87801 / 1000000 : ℚ))) (51 / 16000 : ℚ) (153 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [121085566965458, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_3 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (3909 / 500000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (153 / 32000 : ℚ) (51 / 8000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [2193893753351133394578985307, -2265273205493758817377028462, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_3 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (5549 / 100000 : ℚ))) (153 / 32000 : ℚ) (51 / 8000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [794971125829353794229, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_3 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (4421 / 50000 : ℚ))) (153 / 32000 : ℚ) (51 / 8000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [118532026090043, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_4 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (7917 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (51 / 8000 : ℚ) (51 / 6400 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [1996803490730540103965726768, -2068627244455964083849488616, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_4 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (55841 / 1000000 : ℚ))) (51 / 8000 : ℚ) (51 / 6400 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [755175438156083487644, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_4 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (44489 / 500000 : ℚ))) (51 / 8000 : ℚ) (51 / 6400 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [116052682452388, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_5 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (4003 / 500000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (51 / 6400 : ℚ) (153 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [1797383435374583146880008075, -1871981283418169350321948770, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_5 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (28077 / 500000 : ℚ))) (51 / 6400 : ℚ) (153 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 / 23 : ℚ)) (zs := [31177874710487563893, -1042958825269559375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_5 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (89477 / 1000000 : ℚ))) (51 / 6400 : ℚ) (153 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [113645103356173, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_6 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1617 / 200000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (153 / 16000 : ℚ) (357 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [1595633587283262523321829228, -1675335322380374616794408924, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_6 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (5643 / 100000 : ℚ))) (153 / 16000 : ℚ) (357 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 / 23 : ℚ)) (zs := [29594483929933544998, -1042958825269559375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_6 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (89917 / 1000000 : ℚ))) (153 / 16000 : ℚ) (357 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [111309288801398, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_7 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1631 / 200000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (357 / 32000 : ℚ) (51 / 4000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [1411451521833894073291190227, -1478689361342579883266869078, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_7 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (28337 / 500000 : ℚ))) (357 / 32000 : ℚ) (51 / 4000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [645696294316487659089, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_7 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (45153 / 500000 : ℚ))) (357 / 32000 : ℚ) (51 / 4000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [109035508002783, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring


end
end CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys0

