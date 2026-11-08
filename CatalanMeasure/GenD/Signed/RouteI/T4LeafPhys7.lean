module

public import CatalanMeasure.GenD.Signed.RouteI.T4Instance

@[expose] public section

/-!
# T4 leaf data, physical window, steps 56 to 63

The three diagonal checks `wPq`, `phiQ`, `omQ` of GP §9 (c), (d) on each of the steps 56 to 63 of the 64-step cover of
`[0, 51/500]` (design C): one `polyNonneg_of_ints` leaf per check, `checkZ` on an integer list.
-/

namespace CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys7
open CatalanMeasure.GenD.Signed.RouteI.T4Instance
noncomputable section

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem physW_56 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (357 / 4000 : ℚ) (2907 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [2784319415286698033026190528, 8156962729509362059582583376, 98322980518897366763769923]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_56 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (157 / 250000 : ℚ))) (357 / 4000 : ℚ) (2907 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [1994369145393762431624, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_56 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (1 / 1000 : ℚ))) (357 / 4000 : ℚ) (2907 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [129432249925368, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem physW_57 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (2907 / 32000 : ℚ) (1479 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [11039605125314957459372543827, 8353608690547156793110123222, 98322980518897366763769923]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_57 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (157 / 250000 : ℚ))) (2907 / 32000 : ℚ) (1479 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [1970381092412562565999, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_57 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (1 / 1000 : ℚ))) (2907 / 32000 : ℚ) (1479 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [127631628560993, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem physW_58 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (1479 / 16000 : ℚ) (3009 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [19491536796381011619246436972, 8550254651584951526637663068, 98322980518897366763769923]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_58 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (157 / 250000 : ℚ))) (1479 / 16000 : ℚ) (3009 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [1946393039431362700374, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_58 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (1 / 1000 : ℚ))) (1479 / 16000 : ℚ) (3009 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [125831007196618, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem physW_59 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (3009 / 32000 : ℚ) (153 / 1600 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [28140114428484860512647869963, 8746900612622746260165202914, 98322980518897366763769923]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_59 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (157 / 250000 : ℚ))) (3009 / 32000 : ℚ) (153 / 1600 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [1922404986450162834749, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_59 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (1 / 1000 : ℚ))) (3009 / 32000 : ℚ) (153 / 1600 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [124030385832243, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem physW_60 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (153 / 1600 : ℚ) (3111 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [36985338021626504139576842800, 8943546573660540993692742760, 98322980518897366763769923]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_60 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (157 / 250000 : ℚ))) (153 / 1600 : ℚ) (3111 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [1898416933468962969124, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_60 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (1 / 1000 : ℚ))) (153 / 1600 : ℚ) (3111 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [122229764467868, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem physW_61 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (3111 / 32000 : ℚ) (1581 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [46027207575805942500033355483, 9140192534698335727220282606, 98322980518897366763769923]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_61 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (157 / 250000 : ℚ))) (3111 / 32000 : ℚ) (1581 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [1874428880487763103499, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_61 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (1 / 1000 : ℚ))) (3111 / 32000 : ℚ) (1581 / 16000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [120429143103493, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem physW_62 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (1581 / 16000 : ℚ) (3213 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [55265723091023175594017408012, 9336838495736130460747822452, 98322980518897366763769923]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_62 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (157 / 250000 : ℚ))) (1581 / 16000 : ℚ) (3213 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [1850440827506563237874, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_62 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (1 / 1000 : ℚ))) (1581 / 16000 : ℚ) (3213 / 32000 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [118628521739118, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem physW_63 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (1 / 1000000 : ℚ) [(1547241039 / 2000000000 : ℚ), (-117647903 / 102000000 : ℚ), (5215061 / 10404000 : ℚ)] [(-253949899 / 100000000 : ℚ), (2565597 / 1700000 : ℚ)] [(7 / 1000 : ℚ), (-169 / 510 : ℚ)] [(7 / 1000 : ℚ), (163 / 1020 : ℚ)]) (3213 / 32000 : ℚ) (51 / 500 : ℚ) := by
  refine polyNonneg_of_ints (D := (19897575377315840000000000000000 : ℚ)) (zs := [64700884567278203421529000387, 9533484456773925194275362298, 98322980518897366763769923]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physPhi_63 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (phiQ (992223195 / 1073741824 : ℚ) (879 / 10000 : ℚ) (-94801106659613 / 9007199254740992 : ℚ) (157 / 250000 : ℚ))) (3213 / 32000 : ℚ) (51 / 500 : ℚ) := by
  refine polyNonneg_of_ints (D := (45035996273704960000000 : ℚ)) (zs := [1826452774525363372249, -23988052981199865625]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [phiQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 1
theorem physOm_63 : PolyNonneg (addQ [-(1 / 10000000 : ℚ)] (omQ (-187 / 1000 : ℚ) (60881 / 8388608 : ℚ) (1 / 1000 : ℚ))) (3213 / 32000 : ℚ) (51 / 500 : ℚ) := by
  refine polyNonneg_of_ints (D := (2432696320000000 : ℚ)) (zs := [116827900374743, -1800621364375]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [omQ, a1Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring


end
end CatalanMeasure.GenD.Signed.RouteI.T4LeafPhys7

