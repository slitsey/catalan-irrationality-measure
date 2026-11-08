module

public import CatalanMeasure.GenD.Signed.RouteI.T4Instance

@[expose] public section

/-!
# T4 leaf data, physical window, steps 16 to 23

The three diagonal checks `wPq`, `phiQ`, `omQ` of GP §9 (c), (d) on each of the steps 16 to 23 of the 64-step cover of
`[0, 51/500]` (design C): one `polyNonneg_of_ints` leaf per check, `checkZ` on an integer list.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys2
open CatalanMeasure.GenD.Signed.RouteI.T4Instance
noncomputable section

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_16 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (4177 / 500000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (51 / 2000 : ℚ) (867 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [27026191867213991754732288, 291124287997572718480989536, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_16 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (57361 / 1000000 : ℚ))) (51 / 2000 : ℚ) (867 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [398864088045653560944, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_16 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (91401 / 1000000 : ℚ))) (51 / 2000 : ℚ) (867 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [91498014488208, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_17 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (4167 / 500000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (867 / 32000 : ℚ) (459 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [18521952837367276999491747, 487770249035367452008529382, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_17 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (14323 / 250000 : ℚ))) (867 / 32000 : ℚ) (459 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [377983518807339337559, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_17 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (91291 / 1000000 : ℚ))) (867 / 32000 : ℚ) (459 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [89831191421433, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_18 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1661 / 200000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (459 / 16000 : ℚ) (969 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [27585496449472735771791052, 684416210073162185536069228, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_18 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (7149 / 125000 : ℚ))) (459 / 16000 : ℚ) (969 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [358499065453509967934, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_18 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (22783 / 250000 : ℚ))) (459 / 16000 : ℚ) (969 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [88223969414498, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_19 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (4133 / 500000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (969 / 32000 : ℚ) (51 / 1600 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [34319247326214528071630203, 881062171110956919063609074, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_19 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (28529 / 500000 : ℚ))) (969 / 32000 : ℚ) (51 / 1600 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [340545835972986566949, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_19 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (45459 / 500000 : ℚ))) (969 / 32000 : ℚ) (51 / 1600 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [86683646556363, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_20 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1027 / 125000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (51 / 1600 : ℚ) (1071 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [18825630090276813899009200, 1077708132148751652591148920, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_20 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (11377 / 200000 : ℚ))) (51 / 1600 : ℚ) (1071 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [324349010347137659404, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_20 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (90643 / 1000000 : ℚ))) (51 / 1600 : ℚ) (1071 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [85217520935988, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_21 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (8157 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (1071 / 32000 : ℚ) (561 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [20899795496291273253928043, 1274354093186546386118688766, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_21 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (56681 / 1000000 : ℚ))) (1071 / 32000 : ℚ) (561 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [309548300605773605619, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_21 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (90317 / 1000000 : ℚ))) (1071 / 32000 : ℚ) (561 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [83813429071773, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_22 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1011 / 125000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (561 / 16000 : ℚ) (1173 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [20644168166942066136386732, 1471000054224341119646228612, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_22 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (1411 / 25000 : ℚ))) (561 / 16000 : ℚ) (1173 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [296413922726536635354, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_22 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (44967 / 500000 : ℚ))) (561 / 16000 : ℚ) (1173 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [82478669052678, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem physW_23 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (8009 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (1173 / 32000 : ℚ) (153 / 4000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [18058748102229192546385267, 1667646015262135853173768458, 98322980518897366763769923]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_23 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (14041 / 250000 : ℚ))) (1173 / 32000 : ℚ) (153 / 4000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [284855804716879338689, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_23 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (44747 / 500000 : ℚ))) (1173 / 32000 : ℚ) (153 / 4000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [81213240878703, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring


end
end CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys2

