module

public import CatalanMeasure.GenD.Signed.RouteI.T4Instance

@[expose] public section

/-!
# T4 leaf data, physical window, steps 40 to 47

The three diagonal checks `wPq`, `phiQ`, `omQ` of GP §9 (c), (d) on each of the steps 40 to 47 of the 64-step cover of
`[0, 51/500]` (design C): one `polyNonneg_of_ints` leaf per check, `checkZ` on an integer list.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys5
open CatalanMeasure.GenD.Signed.RouteI.T4Instance
noncomputable section

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_40 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (5157 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (51 / 800 : ℚ) (2091 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [35497401415102011229956800, 5010627352904646323141945840, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_40 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (11267 / 250000 : ℚ))) (51 / 800 : ℚ) (2091 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 / 23 : ℚ)) (zs := [16381666029978776488, -1042958825269559375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_40 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (71813 / 1000000 : ℚ))) (51 / 800 : ℚ) (2091 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [72108929501288, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_41 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (49 / 10000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (2091 / 32000 : ℚ) (1071 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [30770862868474821135672563, 5207273313942441056669485686, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_41 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (43931 / 1000000 : ℚ))) (2091 / 32000 : ℚ) (1071 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [403996193471514533119, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_41 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (7 / 100 : ℚ))) (2091 / 32000 : ℚ) (1071 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [72513547350993, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_42 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (4633 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (1071 / 16000 : ℚ) (2193 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [23714531586483964568928172, 5403919274980235790197025532, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_42 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (42717 / 1000000 : ℚ))) (1071 / 16000 : ℚ) (2193 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [434681839966592488934, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_42 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (68067 / 1000000 : ℚ))) (1071 / 16000 : ℚ) (2193 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [73064126979898, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_43 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (4357 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (2193 / 32000 : ℚ) (561 / 8000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [34225982946445281529723627, 5600565236018030523724565378, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_43 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (1657 / 40000 : ℚ))) (2193 / 32000 : ℚ) (561 / 8000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [468880294171019431629, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_43 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (8251 / 125000 : ℚ))) (2193 / 32000 : ℚ) (561 / 8000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [73767966476963, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_44 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (407 / 100000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (561 / 8000 : ℚ) (459 / 6400 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [22510066193727092018058928, 5797211197055825257252105224, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_44 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (20019 / 500000 : ℚ))) (561 / 8000 : ℚ) (459 / 6400 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [507357168021448345524, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_44 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (63797 / 1000000 : ℚ))) (561 / 8000 : ℚ) (459 / 6400 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [74656690894348, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_45 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1887 / 500000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (459 / 6400 : ℚ) (1173 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [28361932082961076033934075, 5993857158093619990779645070, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_45 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (19277 / 500000 : ℚ))) (459 / 6400 : ℚ) (1173 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [550202533510426640539, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_45 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (61433 / 1000000 : ℚ))) (459 / 6400 : ℚ) (1173 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [75731516580213, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_46 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (867 / 250000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (1173 / 16000 : ℚ) (2397 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [31884005236831393577349068, 6190503119131414724307184916, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_46 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (18479 / 500000 : ℚ))) (1173 / 16000 : ℚ) (2397 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [598091930582059891074, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_46 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (5889 / 100000 : ℚ))) (1173 / 16000 : ℚ) (2397 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [77024068586718, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_47 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (197 / 62500 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (2397 / 32000 : ℚ) (153 / 2000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [33076285655338044648303907, 6387149080169209457834724762, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_47 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (17617 / 500000 : ℚ))) (2397 / 32000 : ℚ) (153 / 2000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [651745935176727376489, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_47 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (56143 / 1000000 : ℚ))) (2397 / 32000 : ℚ) (153 / 2000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [78564755617863, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring


end
end CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys5

