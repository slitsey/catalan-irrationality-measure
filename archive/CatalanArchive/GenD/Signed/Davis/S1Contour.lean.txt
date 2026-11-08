module

public import CatalanMeasure.GenD.Signed.Davis.CircleCheb
public import CatalanMeasure.GenD.Signed.Davis.DesignWeights
public import CatalanMeasure.GenD.Signed.Davis.Normalized130
public import CatalanMeasure.GenD.Signed.LogEval

@[expose] public section

/-!
# S1 circle bound for the degree-130 polynomial (C1)

`normSq_circle_le_of_cheb_square`: on `‖z‖ = 3/5`, `(‖P z‖^7 ‖1-z‖^103)^2 < U2 * (2^871)^2`
with `U2 = 20550646924241/2^44`, from one packed Laurent residual (`CircleCheb`). The
only data are the 131 coefficients of `P` (already in the tree) and the 256 square
numerators below. `hcirc58` is the circle hypothesis of `hweights58` with cap `709/20`,
for the same `realP`, `m = 130` and `green58` as the weights.
-/

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

namespace CatalanMeasure.GenD.Signed.Davis.S1Contour

open Polynomial CatalanMeasure.GenD.Analytic CatalanMeasure.GenD.Signed.Davis.CircleCheb
open CatalanMeasure.Refinement.Trimmed130 CatalanMeasure.GenD.Signed.LogEval
open CatalanMeasure.Parametric OAI.InternalCatalan

noncomputable section

/-! ### Rescaling to the unit circle -/

/-- Entry `i` of `l` times `a^i * b^(len-1-i)`. -/
def scaleAB (a b : ℤ) : List ℤ → List ℤ
  | [] => []
  | x :: t => x * b ^ t.length :: (scaleAB a b t).map (a * ·)

theorem evC_map_mul (z : ℂ) (a : ℤ) (l : List ℤ) : evC z (l.map (a * ·)) = a * evC z l := by
  induction l with
  | nil => simp [evC]
  | cons x t ih => simp only [List.map_cons, evC, ih]; push_cast; ring

theorem evC_scaleAB (a b : ℤ) (hb : (b : ℂ) ≠ 0) (ζ : ℂ) (l : List ℤ) :
    evC ζ (scaleAB a b l) * b = (b : ℂ) ^ l.length * evC (a * ζ / b) l := by
  induction l with
  | nil => simp [scaleAB, evC]
  | cons x t ih =>
    simp only [scaleAB, evC, evC_map_mul, List.length_cons]
    push_cast
    have : evC ζ (scaleAB a b t) = (b : ℂ) ^ t.length * evC (a * ζ / b) t / b := by
      field_simp; exact ih
    rw [this]
    field_simp
    ring

/-- Palindromic coefficient list `[b_k, ..., b_1, 2 b_0, b_1, ..., b_k]`. -/
def palList : List ℤ → List ℤ
  | [] => []
  | b0 :: t => t.reverse ++ (2 * b0) :: t

theorem palList_reverse (b : List ℤ) : (palList b).reverse = palList b := by
  cases b with
  | nil => rfl
  | cons b0 t => simp [palList]

/-- The audited square numerators (denominator `2^56`). -/
def sqNum : List ℤ := [75873106253900736, 373968607586415, 2562792956244700, -1088311832510692, -2244082290035538, 1705379323245838, 1747269287496680, -2171591740633785, -1119896094209624, 2448874867869424, 421010232475458, -2518249926122209, 285210890935378, 2381230199362460, -936212816776710, -2058925238205700, 1477393741026367, 1589041008282654, -1867292483077816, -1021216163464839, 2081088361952301, 411317937712055, -2112101613583480, 184585879175918, 1971245277562073, -715867482730192, -1684631705240758, 1141976983646160, 1289745392990600, -1435630644658724, -830733706305796, 1584313928539341, 353424916264768, -1590086838426136, 99341743858738, 1467882461280926, -491585417179060, -1242648265223566, 796911184321554, 945777188625185, -999928181457234, -611305892791445, 1096364213266796, 272324813356807, -1092033614563627, 42038801416873, 1000926346037197, -308820056622627, -842748914365751, 512482413696415, 640260647971644, -645258897620155, -416718096390475, 706679802352912, 193676876633819, -702470495672168, 10682158324076, 643040645436253, -182623099167598, -541790774865829, 313322736570357, 413439193545427, -398801844611933, -272530355867215, 439429871182591, 132233794096463, -439134930067712, -3489579134463, 404453166171078, -105491322451035, -343538187966537, 189400840452670, 265227703801483, -245735930896339, -178236190064091, 274496182732256, 90514039511692, -277746497072569, -8788624109121, 259109049118470, -61716924343106, -223238466835844, 117404970188508, 175321719391281, -156290261314877, -120631754570979, 177881197022391, 64152881334363, -182984023486146, -10286967231856, 173456260383892, -37357170941803, -151932461021204, 76093537933920, 121541997018431, -104213491490205, -85635339724529, 120972880830765, 47532402054304, -126521282303795, -10303838499994, 121784102394780, -23406370861582, -108309315686186, 51511344438023, 88091278156492, -72561759393147, -63384294727539, 85776209535078, 36518305618260, -91024143556725, -9728109835773, 88766704702194, -14994042746162, -79963052902453, 36014814903363, 65951450767951, -52140004741231, -48315400235471, 62656336804739, 28745358334379, -67335340554505, -8906043956207, 66402430129599, -9681851449719, -60476489545488, 25738484346183, 50486909712698, -38295270554086, -37576031838173, 46736258017326, 22995299558677, -50810137744619, -8003138991901, 50614700165241, -6228251817263, -46557356469104, 18691303202438, 39296735041962, -28602352757107, -29671269850374, 35439247073847, 18621100104874, -38956490861626, -7109516523705, 39178844105128, -3950330432581, -36375730938914, 13758624630233, 31019989985721, -21678290135803, -23735309635859, 27268225354252, 15237127074167, -30299344895223, -6271829134982, 30753727394955, -2441195663984, -28808353424531, 10260691622366, 24805898677057, -16664713870215, -19215772010993, 21279681557951, 12589025848633, -23896186665936, -5510910450809, 24471481804163, -1445292614466, -23119534311270, 7759906719064, 20090357129133, -13001300247531, -15740962330379, 16851193315193, 10500700753711, -19119703134343, -4833938633961, 19749825948477, -797015698275, -18811836215533, 5966064596161, 16488771212828, -10312297039941, -13054720198268, 13562074282198, 8848023345860, -15543134795673, -4241692422142, 16190281060177, -386608068247, -15542845077526, 4682821674285, 13734701964818, -8341091212767, -10978076027894, 11123168595972, 7542735496721, -12871607999024, -3732385438496, 13516221209664, -139861045433, -13073786952446, 3775119402134, 11641482176433, -6909851981930, -9384912533859, 9333129624455, 6521938376812, -10899057630955, -3303706418280, 11533789123915, -5600994006, -11236962235151, 3148795840844, 10077793692489, -5894101101715, -8186414759175, 8050759125896, 5741325572918, -9480901605789, -2954056026576, 10107060918725, 52247030320, -9915033835366, 2737596798222, 8952138082227, -5206479463978, -7321208819992, 7177330682912, 5170947704453, -8516573557357, -2683447758594, 9142181654179, 59863223673, -9027826623588, 2494730030846, 8202991143790, -4786231434804, -6749189607158, 6645177451872, 4792684848675, -7938293910247, -2494299989692, 8577231605659, 37089650233, -8523981101973, 2387252911094, 7792688852933, -4592320719258, -6447832076870, 6410320209134, 4598940681555, -7703928185350, -2392268307868, 8375914101585]

/-- Integer coefficients of `P` rescaled to the unit circle `|z| = 3/5`. -/
def psS1 : List ℤ := scaleAB 3 5 integerCoefficients

def lamS1 : ℤ := ((10 ^ 280 * 5 ^ 1013 * 2 ^ 871 : ℕ) : ℤ)

/-- The packed Laurent residual of the degree-1013 norm square. -/
theorem s1_check : checkCircle 8552 11 psS1 [5, -3] (palList sqNum) 7 103 1013 503
    (4 * lamS1 ^ 2 * 2 ^ 112 * 20550646924241) (4 * 2 ^ 44 * 2 ^ 112) (2 ^ 44 * lamS1 ^ 2)
      = true := by
  -- kcost: 47 s measured standalone (single declaration, 3.8 GB commit incl. Mathlib import)
  decide +kernel

/-! ### Transfer to `P` -/

theorem evalPairs_real (z : ℂ) (l : List ℤ) :
    GaussianHorner.evalPairs (l.map fun a => (a, 0)) z = evC z l := by
  induction l with
  | nil => simp [GaussianHorner.evalPairs, evC]
  | cons a t ih => simp [GaussianHorner.evalPairs, evC, GaussianHorner.castPair_real, ih]

theorem complexP_eval (z : ℂ) :
    (realP.map (algebraMap ℝ ℂ)).eval z = evC z integerCoefficients / (10 ^ 40 : ℂ) := by
  rw [Normalized130.realP_eval_eq_integer, evalPairs_real]
  norm_num [coefficientDenominator]

/-- Norm-square bound for `Q = P^7 (1-z)^103` on the circle of radius `3/5`. -/
theorem normSq_circle_le_of_cheb_square {z : ℂ} (hz : ‖z‖ = 3 / 5) :
    (‖(realP.map (algebraMap ℝ ℂ)).eval z‖ ^ 7 * ‖(1 : ℂ) - z‖ ^ 103) ^ 2 <
      (20550646924241 / 17592186044416 : ℝ) * ((2 : ℝ) ^ 871) ^ 2 := by
  set ζ : ℂ := (5 / 3 : ℂ) * z with hζ
  have hζn : ‖ζ‖ = 1 := by
    rw [hζ, norm_mul, hz]; norm_num
  have hmain := circle_normSq_lt s1_check hζn
  have h5 : ((5 : ℤ) : ℂ) ≠ 0 := by norm_num
  have hps : evC ζ psS1 = 5 ^ 130 * evC z integerCoefficients := by
    have h := evC_scaleAB 3 5 h5 ζ integerCoefficients
    have hlen : integerCoefficients.length = 131 := by
      -- kcost: 0.01 s estimated, one list length
      decide +kernel
    have harg : ((3 : ℤ) : ℂ) * ζ / ((5 : ℤ) : ℂ) = z := by
      rw [hζ]; push_cast; ring
    rw [harg, hlen] at h
    push_cast at h
    unfold psS1
    have : (5 : ℂ) ^ 130 * 5 ≠ 0 := by norm_num
    apply mul_right_cancel₀ (by norm_num : (5 : ℂ) ≠ 0)
    rw [h]; ring
  have hlin : evC ζ [5, -3] = 5 * (1 - z) := by
    simp only [evC]; push_cast; rw [hζ]; ring
  set P : ℂ := (realP.map (algebraMap ℝ ℂ)).eval z with hP
  have hPz : evC z integerCoefficients = 10 ^ 40 * P := by
    rw [hP, complexP_eval]; field_simp
  have hA : evC ζ psS1 ^ 7 * evC ζ [5, -3] ^ 103 =
      (((5 ^ 130 * 10 ^ 40) ^ 7 * 5 ^ 103 : ℝ) : ℂ) * (P ^ 7 * (1 - z) ^ 103) := by
    rw [hps, hlin, hPz]; push_cast; ring
  rw [hA] at hmain
  have hn : Complex.normSq (P ^ 7 * (1 - z) ^ 103) = (‖P‖ ^ 7 * ‖(1 : ℂ) - z‖ ^ 103) ^ 2 := by
    rw [← Complex.sq_norm, norm_mul, norm_pow, norm_pow]
  rw [Complex.normSq_mul, Complex.normSq_ofReal, hn] at hmain
  set t : ℝ := ‖P‖ ^ 7 * ‖(1 : ℂ) - z‖ ^ 103 with ht
  have hΛ : (((5 : ℝ) ^ 130 * 10 ^ 40) ^ 7 * 5 ^ 103) = 10 ^ 280 * 5 ^ 1013 := by
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm ((5 : ℝ) ^ (130 * 7)), mul_assoc, ← pow_add]
  have hl : ((lamS1 : ℤ) : ℝ) = (10 ^ 280 * 5 ^ 1013) * 2 ^ 871 := by
    unfold lamS1; push_cast; ring
  have gen : ∀ Λ T : ℝ, 4 * (Λ * T) ^ 2 * 2 ^ 112 * 20550646924241 =
      (4 * 2 ^ 44 * 2 ^ 112 * (Λ * Λ)) * (20550646924241 / 17592186044416 * T ^ 2) := by
    intro Λ T; ring
  have hc : (((4 * 2 ^ 44 * 2 ^ 112 : ℤ)) : ℝ) = 4 * 2 ^ 44 * 2 ^ 112 := by push_cast; ring
  have hc1 : (((4 * lamS1 ^ 2 * 2 ^ 112 * 20550646924241 : ℤ)) : ℝ) =
      (4 * 2 ^ 44 * 2 ^ 112 * ((10 ^ 280 * 5 ^ 1013) * (10 ^ 280 * 5 ^ 1013))) *
        (20550646924241 / 17592186044416 * ((2 : ℝ) ^ 871) ^ 2) := by
    push_cast; rw [hl]; ring
  rw [hc, hc1, hΛ] at hmain
  set Λ : ℝ := 10 ^ 280 * 5 ^ 1013 with hΛd
  set C2 : ℝ := 4 * 2 ^ 44 * 2 ^ 112 with hC2
  have hpos : 0 < C2 * (Λ * Λ) := by rw [hC2, hΛd]; positivity
  have h2 : C2 * (Λ * Λ) * t ^ 2 <
      C2 * (Λ * Λ) * (20550646924241 / 17592186044416 * ((2 : ℝ) ^ 871) ^ 2) := by
    rw [mul_assoc]; exact hmain
  exact lt_of_mul_lt_mul_left h2 hpos.le

/-! ### The scalar transfer -/

theorem ellipseLog_le_log (w : ℂ) : ellipseLog w ≤ Real.log (2 * (‖w‖ + 1)) := by
  have hH := ellipseH_ge_one w
  have hHle : ellipseH w ≤ ‖w‖ + 1 := by
    unfold ellipseH
    have h1 : ‖w - 1‖ ≤ ‖w‖ + 1 := by simpa using norm_sub_le w 1
    have h2 : ‖w + 1‖ ≤ ‖w‖ + 1 := by simpa using norm_add_le w 1
    linarith
  have hw : 0 < 2 * (‖w‖ + 1) := by positivity
  rw [Real.le_log_iff_exp_le hw]
  unfold ellipseLog
  rw [Real.exp_arcosh hH]
  have hs : Real.sqrt (ellipseH w ^ 2 - 1) ≤ ellipseH w := by
    calc Real.sqrt (ellipseH w ^ 2 - 1) ≤ Real.sqrt (ellipseH w ^ 2) :=
          Real.sqrt_le_sqrt (by linarith)
      _ = ellipseH w := Real.sqrt_sq (by linarith)
  linarith

theorem log_le_of_logQ {n : ℕ} {q v e : ℚ} (h : logQ n q = some (v, e)) :
    Real.log (q : ℝ) ≤ ((v + e : ℚ) : ℝ) :=
  (logQ_spec h).2.le_upper

def UQ : ℚ := 20550646924241 / 17592186044416

def largeOK : Bool :=
  match logQ 8 2, logQ 8 UQ, logQ 8 (8 / 5) with
  | some (v2, e2), some (vu, eu), some (v8, e8) =>
      decide ((53 / 910) * (871 * (v2 + e2) + (1 / 2) * (vu + eu)) + (53 / 130) * (v2 + e2) +
        (1 / 910) * (v8 + e8) + 53 / (130 * 2 ^ 64) ≤ 709 / 20)
  | _, _, _ => false

def smallOK : Bool :=
  match logQ 8 (8 / 5), logQ 8 (2 * (2 ^ 64 + 1)) with
  | some (v8, e8), some (vb, eb) => decide (6 * (v8 + e8) + (53 / 130) * (vb + eb) ≤ 709 / 20)
  | _, _ => false

theorem largeOK_true : largeOK = true := by
  -- kcost: 0.05 s estimated; four logQ at n = 8 (S1Selector uses n = 12 per cell)
  decide +kernel

theorem smallOK_true : smallOK = true := by
  -- kcost: 0.03 s estimated
  decide +kernel

theorem large_real :
    (53 / 910 : ℝ) * (871 * Real.log 2 +
        (1 / 2) * Real.log (20550646924241 / 17592186044416)) +
      (53 / 130) * Real.log 2 + (1 / 910) * Real.log (8 / 5) + 53 / 130 / 2 ^ 64 ≤ 709 / 20 := by
  have h := largeOK_true
  unfold largeOK at h
  cases h2 : logQ 8 2 with
  | none => simp [h2] at h
  | some p2 =>
    obtain ⟨v2, e2⟩ := p2
    cases hu : logQ 8 UQ with
    | none => simp [h2, hu] at h
    | some pu =>
      obtain ⟨vu, eu⟩ := pu
      cases h8 : logQ 8 (8 / 5) with
      | none => simp [h2, hu, h8] at h
      | some p8 =>
        obtain ⟨v8, e8⟩ := p8
        simp only [h2, hu, h8] at h
        have hf := of_decide_eq_true h
        have hfR := (Rat.cast_le (K := ℝ)).mpr hf
        have l2 := log_le_of_logQ h2
        have lu := log_le_of_logQ hu
        have l8 := log_le_of_logQ h8
        push_cast [UQ] at hfR l2 lu l8
        norm_num at l2 lu l8 hfR ⊢
        linarith

theorem small_real :
    6 * Real.log (8 / 5) + (53 / 130 : ℝ) * Real.log (2 * (2 ^ 64 + 1)) ≤ 709 / 20 := by
  have h := smallOK_true
  unfold smallOK at h
  cases h8 : logQ 8 (8 / 5) with
  | none => simp [h8] at h
  | some p8 =>
    obtain ⟨v8, e8⟩ := p8
    cases hb : logQ 8 (2 * (2 ^ 64 + 1)) with
    | none => simp [h8, hb] at h
    | some pb =>
      obtain ⟨vb, eb⟩ := pb
      simp only [h8, hb] at h
      have hf := of_decide_eq_true h
      have hfR := (Rat.cast_le (K := ℝ)).mpr hf
      have l8 := log_le_of_logQ h8
      have lb := log_le_of_logQ hb
      push_cast at hfR l8 lb
      exact (add_le_add (mul_le_mul_of_nonneg_left l8 (by norm_num : (0 : ℝ) ≤ 6))
        (mul_le_mul_of_nonneg_left lb (by norm_num : (0 : ℝ) ≤ 53 / 130))).trans hfR

/-- The circle hypothesis of `hweights58` at cap `709/20`, for the same `realP`, `m = 130`. -/
theorem hcirc58 {z : ℂ} (hz : ‖z‖ = 3 / 5) :
    6 * Real.log ‖(1 : ℂ) - z‖ + 53 * green58 z ≤ 709 / 20 := by
  set w : ℂ := (realP.map (algebraMap ℝ ℂ)).eval z with hw
  have hb1 : ‖(1 : ℂ) - z‖ ≤ 8 / 5 := by
    have := norm_sub_le (1 : ℂ) z
    rw [norm_one, hz] at this; linarith
  have hb0 : 2 / 5 ≤ ‖(1 : ℂ) - z‖ := by
    have := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one, hz] at this; linarith
  have hbpos : 0 < ‖(1 : ℂ) - z‖ := by linarith
  have hg : 53 * green58 z = (53 / 130 : ℝ) * ellipseLog w := by
    unfold green58 nodalGreen
    rw [← hw]; push_cast; ring
  rw [hg]
  have hE := ellipseLog_le_log w
  have hlogb := Real.log_le_log hbpos hb1
  by_cases hcase : (2 : ℝ) ^ 64 ≤ ‖w‖
  · have hapos : 0 < ‖w‖ := lt_of_lt_of_le (by positivity) hcase
    have hQ := normSq_circle_le_of_cheb_square hz
    rw [← hw] at hQ
    have hlogQ : 7 * Real.log ‖w‖ + 103 * Real.log ‖(1 : ℂ) - z‖ ≤
        (1 / 2) * Real.log (20550646924241 / 17592186044416) + 871 * Real.log 2 := by
      have hprod : 0 < ‖w‖ ^ 7 * ‖(1 : ℂ) - z‖ ^ 103 := by positivity
      have h1 := Real.log_le_log (pow_pos hprod 2) hQ.le
      have hL : Real.log ((‖w‖ ^ 7 * ‖(1 : ℂ) - z‖ ^ 103) ^ 2) =
          2 * (7 * Real.log ‖w‖ + 103 * Real.log ‖(1 : ℂ) - z‖) := by
        rw [Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow,
          Real.log_pow]
        push_cast; ring
      have hR : Real.log (20550646924241 / 17592186044416 * ((2 : ℝ) ^ 871) ^ 2) =
          Real.log (20550646924241 / 17592186044416) + 2 * (871 * Real.log 2) := by
        rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_pow]
        push_cast; ring
      rw [hL, hR] at h1
      linarith
    have hsplit : Real.log (2 * (‖w‖ + 1)) =
        Real.log 2 + Real.log ‖w‖ + Real.log ((‖w‖ + 1) / ‖w‖) := by
      rw [← Real.log_mul (by norm_num) hapos.ne', ← Real.log_mul (by positivity) (by positivity)]
      congr 1; field_simp
    have hlast : Real.log ((‖w‖ + 1) / ‖w‖) ≤ 1 / 2 ^ 64 := by
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
      have : (‖w‖ + 1) / ‖w‖ - 1 = 1 / ‖w‖ := by field_simp; ring
      rw [this]
      exact one_div_le_one_div_of_le (by positivity) hcase
    have := large_real
    have h53 : (53 / 130 : ℝ) / 2 ^ 64 = (53 / 130) * (1 / 2 ^ 64) := by ring
    linarith [hE, hsplit, hlast, hlogQ, hlogb, this]
  · push_neg at hcase
    have hapos : 0 ≤ ‖w‖ := norm_nonneg _
    have h1 : Real.log (2 * (‖w‖ + 1)) ≤ Real.log (2 * (2 ^ 64 + 1)) :=
      Real.log_le_log (by positivity) (by linarith)
    have hs := small_real
    calc 6 * Real.log ‖(1 : ℂ) - z‖ + 53 / 130 * ellipseLog w
        ≤ 6 * Real.log (8 / 5) + 53 / 130 * Real.log (2 * (2 ^ 64 + 1)) :=
          add_le_add (mul_le_mul_of_nonneg_left hlogb (by norm_num))
            (mul_le_mul_of_nonneg_left (hE.trans h1) (by norm_num))
      _ ≤ 709 / 20 := hs

/-- `hweights58` with its circle hypothesis discharged at cap `709/20`; segment and entropy
hypotheses are unchanged. -/
theorem hweights58_of_cheb
    (τ : ∀ N : ℕ, Fin (53 * N) → ℝ)
    (hτ : τ = inverseQuadratureNodes dc58.toParameters branchCertificate (by norm_num))
    (Ψ : ℝ)
    (hseg : ∀ κ ∈ Set.Icc (0 : ℝ) 1, ∀ x : ℝ, (3 / 5 : ℝ) ≤ |x| → |x| ≤ 1 →
      nodalPhi dc58.toParameters green58 κ (x : ℂ) ≤
        (10 - 58 * κ) * Real.log (3 / 5) + 709 / 20)
    (hΨ : ∀ κ ∈ Set.Icc (0 : ℝ) 1, omega58 (709 / 20) κ + binomRate κ ≤ Ψ / 58)
    (hΨstrict : Ψ < (8723 / 100 : ℝ)) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ a b : ℕ, a + b = 58 * N →
      ∀ k : ℕ, k < 58 * N → ∀ i : Fin (53 * N),
        |(rowCommonFactor dc58.toParameters N).eval (τ N i)| *
          |restrictedWeight dc58.toParameters N k (τ N) i| *
          (CatalanMeasure.binomBeta a b k : ℝ) ≤
            108000 * (N : ℝ) * Real.exp ((8723 / 100 : ℝ) * N) :=
  hweights58 τ hτ (709 / 20) Ψ (fun _ hz => hcirc58 hz) hseg hΨ hΨstrict

end

end CatalanMeasure.GenD.Signed.Davis.S1Contour

#print axioms CatalanMeasure.GenD.Signed.Davis.S1Contour.s1_check
#print axioms CatalanMeasure.GenD.Signed.Davis.S1Contour.normSq_circle_le_of_cheb_square
#print axioms CatalanMeasure.GenD.Signed.Davis.S1Contour.hcirc58
#print axioms CatalanMeasure.GenD.Signed.Davis.S1Contour.hweights58_of_cheb
