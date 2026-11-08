module

public import CatalanMeasure.GenD.Signed.RouteI.T4Instance

@[expose] public section

/-!
# T4 leaf data, physical window, steps 32 to 39

The three diagonal checks `wPq`, `phiQ`, `omQ` of GP §9 (c), (d) on each of the steps 32 to 39 of the 64-step cover of
`[0, 51/500]` (design C): one `polyNonneg_of_ints` leaf per check, `checkZ` on an integer list.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys4
open CatalanMeasure.GenD.Signed.RouteI.T4Instance
noncomputable section

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_32 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1371 / 200000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (51 / 1000 : ℚ) (1683 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [29232322069659218975665152, 3437459664602288454921627072, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_32 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (51961 / 1000000 : ℚ))) (51 / 1000 : ℚ) (1683 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [258249620224462494944, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_32 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (16559 / 200000 : ℚ))) (51 / 1000 : ℚ) (1683 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [73155964923168, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_33 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (6677 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (1683 / 32000 : ℚ) (867 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [23246550028625520661062147, 3634105625640083188449166918, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_33 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (51281 / 1000000 : ℚ))) (1683 / 32000 : ℚ) (867 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [264886044709382002119, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_33 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (81713 / 1000000 : ℚ))) (1683 / 32000 : ℚ) (867 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [72671432267913, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_34 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (649 / 100000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (867 / 16000 : ℚ) (357 / 6400 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [34828560629543995873998988, 3830751586677877921976706764, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_34 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (25279 / 500000 : ℚ))) (867 / 16000 : ℚ) (357 / 6400 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [273459017034070822574, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_34 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (80561 / 1000000 : ℚ))) (867 / 16000 : ℚ) (357 / 6400 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [72272043983858, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_35 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1573 / 250000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (357 / 6400 : ℚ) (459 / 8000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [24183203117782964614475675, 4027397547715672655504246610, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_35 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (49781 / 1000000 : ℚ))) (357 / 6400 : ℚ) (459 / 8000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [284463933157539710869, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_35 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (79323 / 1000000 : ℚ))) (357 / 6400 : ℚ) (459 / 8000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [71977261641563, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_36 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1217 / 200000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (459 / 8000 : ℚ) (1887 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [31105628247974106882492208, 4224043508753467389031786456, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_36 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (9791 / 200000 : ℚ))) (459 / 8000 : ℚ) (1887 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 / 23 : ℚ)) (zs := [12942417960800875748, -1042958825269559375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_36 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (78007 / 1000000 : ℚ))) (459 / 8000 : ℚ) (1887 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [71777354455748, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_37 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1467 / 250000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (1887 / 32000 : ℚ) (969 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [35698260642801582678048587, 4420689469791262122559326302, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_37 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (1923 / 40000 : ℚ))) (1887 / 32000 : ℚ) (969 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [313319236838080641379, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_37 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (76603 / 1000000 : ℚ))) (1887 / 32000 : ℚ) (969 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [71684485908013, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_38 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (141 / 25000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (969 / 16000 : ℚ) (1989 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [18063524924949552001144812, 4617335430829056856086866148, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_38 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (47131 / 1000000 : ℚ))) (969 / 16000 : ℚ) (1989 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [331845164339258257994, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_38 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (751 / 10000 : ℚ))) (969 / 16000 : ℚ) (1989 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [71712035828118, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_39 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (5403 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (1989 / 32000 : ℚ) (51 / 800 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [17996571849049694851780883, 4813981391866851589614405994, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_39 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (4613 / 100000 : ℚ))) (1989 / 32000 : ℚ) (51 / 800 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [352938143628037057329, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_39 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (36753 / 500000 : ℚ))) (1989 / 32000 : ℚ) (51 / 800 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [71850273430783, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring


end
end CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys4

