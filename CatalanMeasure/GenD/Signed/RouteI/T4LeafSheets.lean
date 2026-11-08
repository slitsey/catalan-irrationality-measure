module

public import CatalanMeasure.GenD.Signed.RouteI.T4LeafDefs

@[expose] public section

/-!
# T4 leaf data, large and first sheets, signed piece 2

The `wPq` checks of the six pieces of the large sheet (GP §9 (b)) and of the first sheet (GP §9 (e)), and the signed
signed pieces 1 and 2 on `[0, 1/25]`, `[1/25, 51/500]` (`σ = 33871/10^5`, `I1 = 2366997/10^6`).
-/

namespace CatalanMeasure.GenD.Signed.RouteI.T4LeafSheets
open CatalanMeasure.GenD.Signed.RouteI.T4Instance CatalanMeasure.GenD.Signed.RouteI.T4LeafDefs
noncomputable section

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem largeW_0 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (0 : ℚ) [(264475071 / 400000000 : ℚ)] [(-2992221769 / 1225000000 : ℚ), (5482893 / 9800000 : ℚ)] [(-67 / 2500 : ℚ)] [(233 / 10000 : ℚ)]) (51 / 500 : ℚ) (1 / 5 : ℚ) := by
  refine polyNonneg_of_ints (D := (4857806488602500000000000000 : ℚ)) (zs := [18142772077439870640275423, 44013811249118539058634254, 58440483979530556799995323]) (f := 1) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem largeW_1 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (0 : ℚ) [(264475071 / 400000000 : ℚ)] [(-122133697 / 50000000 : ℚ), (1119397 / 2000000 : ℚ)] [(-67 / 2500 : ℚ)] [(233 / 10000 : ℚ)]) (1 / 5 : ℚ) (3 / 10 : ℚ) := by
  refine polyNonneg_of_ints (D := (1943122595441000000000000 : ℚ)) (zs := [48238826922435586599562, 65637198184871958927602, 24344327499915813235123]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem largeW_2 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (0 : ℚ) [(264475071 / 400000000 : ℚ)] [(-48852457 / 20000000 : ℚ), (2797641 / 5000000 : ℚ)] [(-67 / 2500 : ℚ)] [(233 / 10000 : ℚ)]) (3 / 10 : ℚ) (2 / 5 : ℚ) := by
  refine polyNonneg_of_ints (D := (1943122595441000000000000 : ℚ)) (zs := [138220352607223358762287, 114349017149163837558848, 24341018362135777212123]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem largeW_3 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (0 : ℚ) [(264475071 / 400000000 : ℚ)] [(-244265443 / 100000000 : ℚ), (11192143 / 20000000 : ℚ)] [(-67 / 2500 : ℚ)] [(233 / 10000 : ℚ)]) (2 / 5 : ℚ) (3 / 5 : ℚ) := by
  refine polyNonneg_of_ints (D := (971561297720500000000000 : ℚ)) (zs := [138455194059261486766629, 163021849301700787966094, 48685104914849755763246]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem largeW_4 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (0 : ℚ) [(264475071 / 400000000 : ℚ)] [(-244265737 / 100000000 : ℚ), (11192241 / 20000000 : ℚ)] [(-67 / 2500 : ℚ)] [(233 / 10000 : ℚ)]) (3 / 5 : ℚ) (4 / 5 : ℚ) := by
  refine polyNonneg_of_ints (D := (971561297720500000000000 : ℚ)) (zs := [350162148275812030495969, 260391678279371593056586, 48685295340864108981246]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem largeW_5 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (0 : ℚ) [(264475071 / 400000000 : ℚ)] [(-244267229 / 100000000 : ℚ), (5596307 / 10000000 : ℚ)] [(-67 / 2500 : ℚ)] [(233 / 10000 : ℚ)]) (4 / 5 : ℚ) (1 : ℚ) := by
  refine polyNonneg_of_ints (D := (971561297720500000000000 : ℚ)) (zs := [659239121896047732533801, 357761544176371711526078, 48686020125592208474246]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 7 cellOK calls, degree 2
theorem firstW_0 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (0 : ℚ) [(67761 / 100000 : ℚ), (-10354269 / 27500000 : ℚ), (4096781 / 48400000 : ℚ)] [(-49767 / 20000 : ℚ), (16973379 / 22000000 : ℚ)] [(1096 / 3125 : ℚ), (223 / 22000 : ℚ)] [(1096 / 3125 : ℚ), (223 / 22000 : ℚ)]) (0 : ℚ) (11 / 50 : ℚ) := by
  refine polyNonneg_of_ints (D := (21025000000000000 / 3 : ℚ)) (zs := [263091445936250, -650409778189650, 464669154088361]) (f := 2) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem firstW_1 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (0 : ℚ) [(598872629 / 1000000000 : ℚ)] [(-953609 / 390625 : ℚ), (1114753 / 2000000 : ℚ)] [(7059 / 20000 : ℚ)] [(7059 / 20000 : ℚ)]) (11 / 50 : ℚ) (3 / 10 : ℚ) := by
  refine polyNonneg_of_ints (D := (21025000000000000 : ℚ)) (zs := [232052465504883, 18319359538624, 168270466421168]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem firstW_2 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (0 : ℚ) [(598872629 / 1000000000 : ℚ)] [(-24418439 / 10000000 : ℚ), (5593927 / 10000000 : ℚ)] [(7059 / 20000 : ℚ)] [(7059 / 20000 : ℚ)]) (3 / 10 : ℚ) (2 / 5 : ℚ) := by
  refine polyNonneg_of_ints (D := (841000000000000 : ℚ)) (zs := [16745691658587, 17624320925048, 10533860393323]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem firstW_3 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (0 : ℚ) [(598872629 / 1000000000 : ℚ)] [(-122096657 / 50000000 : ℚ), (2798079 / 5000000 : ℚ)] [(7059 / 20000 : ℚ)] [(7059 / 20000 : ℚ)]) (2 / 5 : ℚ) (3 / 5 : ℚ) := by
  refine polyNonneg_of_ints (D := (420500000000000 : ℚ)) (zs := [22451936488479, 38680784085694, 21071473328646]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem firstW_4 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (0 : ℚ) [(598872629 / 1000000000 : ℚ)] [(-244193317 / 100000000 : ℚ), (11192317 / 20000000 : ℚ)] [(7059 / 20000 : ℚ)] [(7059 / 20000 : ℚ)]) (3 / 5 : ℚ) (4 / 5 : ℚ) := by
  refine polyNonneg_of_ints (D := (420500000000000 : ℚ)) (zs := [82204193902819, 80823729060986, 21071474169646]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 1 cellOK calls, degree 2
theorem firstW_5 : PolyNonneg (wPq (33871 / 100000 : ℚ) (1 / 10000000 : ℚ) (0 : ℚ) [(598872629 / 1000000000 : ℚ)] [(-244193313 / 100000000 : ℚ), (2798079 / 5000000 : ℚ)] [(7059 / 20000 : ℚ)] [(7059 / 20000 : ℚ)]) (4 / 5 : ℚ) (1 : ℚ) := by
  refine polyNonneg_of_ints (D := (420500000000000 : ℚ)) (zs := [184099397133451, 122966678241278, 21071473328646]) (f := 0) (by norm_num) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [wPq, wVq, loQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 35 cellOK calls, degree 2
theorem sigP1_ok : PolyNonneg (sigP1 lC) 0 aeQ := by
  refine polyNonneg_of_ints (D := (10512500000000000 : ℚ)) (zs := [189741537325, -4592901908375, 27825150749056]) (f := 8) (by norm_num [aeQ, a1Q]) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [sigP1, sigP2, sigVq, sigJ1q, sigR1q, sigC1q, sigC2q, lC, aeQ, a1Q, hiQ, MQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring

-- kcost: 0.2 s per leaf measured (24 leaves 4.8 s over the import baseline); 3 cellOK calls, degree 2
theorem sigP2_ok : PolyNonneg (sigP2 lC) aeQ a1Q := by
  refine polyNonneg_of_ints (D := (262812500000000000 : ℚ)) (zs := [585549759450150, -1254629401976910, 1265573062079051]) (f := 1) (by norm_num [aeQ, a1Q]) (by norm_num) (fun w => ?_) (by decide +kernel)
  simp only [sigP1, sigP2, sigVq, sigJ1q, sigR1q, sigC1q, sigC2q, lC, aeQ, a1Q, hiQ, MQ, tQ, c2Q, evalQ_addQ, evalQ_smulQ, evalQ_mulQ, evalQ_cons, evalQ_nil, evalZ]
  push_cast
  ring


end
end CatalanMeasure.GenD.Signed.RouteI.T4LeafSheets

