module

public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RTab
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.Data
public import CatalanMeasure.GenD.Cert.WLogSpec
public import CatalanMeasure.GenD.Analytic.Glue
public import CatalanMeasure.GenD.Signed.RouteI.T4Instance
public import CatalanMeasure.GenD.Signed.RouteI.ChordTableData

@[expose] public section

/-!
# C15: the D58 instance of the unsigned extension `[98749/1000000, 401/2500]`

Theorem side plus a three-cell cover; no new engine.

The generic route (`RouteI.UnsignedExtension.residual_sup_unsigned`: endpoint value plus four
derivative caps of order-12 rational-pole remainders, then the mean value theorem) is not used.  The
residual cap `MR = -315531/5000000` has a large margin on the extension (the field takes the values
`-0.0882` at `98749/1000000` down to `-0.2090` at `401/2500`, so the cap is never close), and the
retained Taylor cells of `RCover` (order `m = 5`, `L = 65`, polynomial data `D_R`, global constant
`MGL_R` from `RTab`) cover the extension directly with three cells.  The statement proved is the one
of `residual_sup_unsigned` (same conclusion, same `hret`/`hres`), with no endpoint or derivative
hypothesis.

Imports: `RTab` (`D_R`, `MGL_R`, `D_R_ok`, `hMGL_R`; built), `Data` (`Pc`, `P`, `MR`, `tailsP`,
`P_nonzero`; built), `WLogSpec` (`resSpecW`, `resSpecW_sound`; built), `Analytic.Glue`
(`resFieldGen`, `gRes`).  `RCover` and `RZ` (held) are not imported: `hZ_R` (the `RZ` theorem) and
`hret` (`RCover.residual_sup_S`) are hypotheses of the final theorem and plug in by definitional
equality.

kcost: three `cellT` checks of order 5 over 76 poles (`resSpecW`), one centre log-sum each, plus one
`coverFrom` on three cells.  Far below 200 terms.
-/

open Set

namespace CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance
open CatalanMeasure.CellCert CatalanMeasure.Cert CatalanMeasure.GenD CatalanMeasure.GenD.Analytic
  CatalanMeasure.GenD.D58.Cert590 CatalanMeasure.Parametric OAI.InternalCatalan
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
noncomputable section

/-- Three Taylor cells `(centre, half width, type)` in units of `2^-40`, covering
`[98749/1000000, 401/2500]`. -/
def cellsExt : List TCell :=
  [(119313091971, 10737418240, 0), (142935412099, 12884901888, 0), (168705215875, 12884901888, 0)]

theorem cover_ext :
    coverFrom (401 / 2500) (qfloor ((98749 / 1000000 : ℚ) * (TT : ℚ))) cellsExt = true := by
  decide +kernel

theorem cells_ext_ok :
    ∀ c ∈ cellsExt, cellT (resSpecW (53 / 58 : ℚ) Pc P) D_R.toD 5 65 MGL_R MR c = true := by
  decide +kernel

/-- **The extension cap.**  On `[98749/1000000, 401/2500]` the field is at most `MR`. -/
theorem ext_cap
    (hZ_R : ∀ x : ℝ, -2 * finUR Pc x = ptZ D_R.toD.Z 0 x) :
    ∀ x ∈ Icc (98749 / 1000000 : ℝ) (401 / 2500),
      resFieldW (((53 / 58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) x ≤ (MR : ℝ) := by
  intro x hx
  refine field_le_of_cells _ (resSpecW (53 / 58 : ℚ) Pc P) D_R.toD D_R_ok 5 65 MGL_R hMGL_R MR
    cellsExt (fun c _ => resSpecW_sound (53 / 58 : ℚ) tailsP P_nonzero D_R.toD hZ_R c.2.2)
    (qfloor ((98749 / 1000000 : ℚ) * (TT : ℚ))) (401 / 2500) cover_ext cells_ext_ok x
    (floor_le_of_ge (98749 / 1000000) x (by push_cast; linarith [hx.1])) (by push_cast; linarith [hx.2])
    (fun c _ pr h => by simp [resSpecW] at h)

/-- **D58 instance of `residual_sup_unsigned`** (same conclusion, `G` any set inside
`x ≤ -19501/100000 ∨ 98749/1000000 ≤ x`, e.g. `RouteI.G58` by `fun x h => h`).  `hρ` is
`Analytic.Instances.d58_gRes` at the design `D58.Odd.design`; `hZ_R` is `RZ.hZ_R`; `hret` is
`RCover.residual_sup_S` (with `residual := (MR : ℝ)`, then `hres` is `by norm_num [MR]`). -/
theorem residual_sup_d58 {Pa : Parameters} {G : ℝ → Prop} {residual : ℝ}
    (hρ : gRes Pa = 53 / 58)
    (hZ_R : ∀ x : ℝ, -2 * finUR Pc x = ptZ D_R.toD.Z 0 x)
    (hG : ∀ x, G x → x ≤ -19501 / 100000 ∨ (98749 / 1000000 : ℝ) ≤ x)
    (hret : ∀ x ∈ Icc (-1 : ℝ) 1, (401 / 2500 : ℝ) ≤ |x| →
      resFieldW (((53 / 58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) x ≤ residual)
    (hres : (-315531 / 5000000 : ℝ) ≤ residual) :
    ∀ x ∈ Icc (-1 : ℝ) 1, G x → resFieldGen (gRes Pa) (trialSeqS Pc P) x ≤ residual := by
  have hq : (((53 / 58 : ℚ) : ℚ) : ℝ) = 53 / 58 := by norm_num
  have hF : resFieldGen (gRes Pa) (trialSeqS Pc P) =
      resFieldW (((53 / 58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) := by
    rw [hρ, hq]; rfl
  rw [hF]
  have hMR : (MR : ℝ) = -315531 / 5000000 := by unfold MR; norm_num
  intro x hx hGx
  rcases le_or_gt (401 / 2500 : ℝ) |x| with hab | hab
  · exact hret x hx hab
  · rcases hG x hGx with hneg | hpos
    · exfalso
      have : -x ≤ |x| := neg_le_abs x
      linarith only [hneg, hab, this]
    · refine (ext_cap hZ_R x ⟨hpos, ?_⟩).trans ?_
      · have : x ≤ |x| := le_abs_self x
        linarith only [hab, this]
      · rw [hMR]; exact hres


/-! ### The frozen trials of design C as data (G35)

Three trial increments over the K590 base trial (`Pc`, `P`; GP §1).  Entry `k` of a list is the
increment of the sequence at index `k + 1` (the Python `du[k]` of `/(k + 1)` sums).  The trial of a
record is `p₀ + τ du` (`τ ∈ [0, 1]`).  Sources: K = 128 signed family
`avd/out/tr-A1_128_1_24.1_0.04.npz` (`da0, dv0, da1, dv1`, rounded to `2⁻⁴⁰`); K = 40 unsigned
`avd/out/rbp1w-full.json` key `40_0.102` (rounded to `2⁻²⁴`); K = 24 constrained
`avd/out/finalw_24_241000.json` (exact `2⁻²⁴` rationals).  Extracted by
`work/tools/g3/t4/trials.json` (one pass, seconds). -/

/-- K = 128 signed family, `da⁰`, numerators over `2^40`. -/
def da0_128 : List ℤ :=
  [-1500840, 8240459, 23790179, 135593107, 36531186, -157440218, 101760900, 91449185, 20058218, -6438706, 24199983, 184244732, 132597319, -129227254, 5107076, 264491777, 87623783, -272170839, -6097409, 315363337, 134615303, -163078248, 80928797, 352944612, 215815717, -53642268, -97722764, -50668100, -44869740, -36472113, -154390904, -247331408, -151414164, 20340722, -187140933, -338475642, -112229324, 155742514, -188916614, -396494341, -48939565, 266696888, -249358426, -521508181, -78603252, 314949825, -288349142, -577387222, -74341113, 404318396, -177418083, -473050014, -2897091, 459543752, -21673073, -353798734, 5562750, 350626878, 73936590, -254559507, -15487659, 194110936, 205394229, -47340351, 36629995, 108454866, 353470579, 217481682, 43065126, -998761, 357042303, 394982458, -73996292, -139200853, 276904775, 555121296, -152957255, -174464303, 267277012, 743531135, -150850918, -182692212, 255645857, 795405145, -174879378, -311805275, 202730835, 689774936, -165479093, -468008054, 225649204, 592003617, -41771291, -534968545, 305117179, 526850258, 61541754, -579227605, 278437440, 430864171, 58239908, -594677925, 184390131, 371309320, 43537818, -488654750, 123903901, 385122709, 48958020, -323555915, 62501247, 359906828, -3664862, -205848561, -48534269, 284658197, -93252356, -102863680, -110329192, 227260227, -90038574, 2173165, -70686904, 171652033, -34265200, 33106961, -22322519, 68841631]

/-- K = 128 signed family, `dv⁰`, over `2^40`. -/
def dv0_128 : List ℤ :=
  [9539, -9407457, -44745655, -35214382, -5065372, 32596302, -36553198, -109402705, -135918098, -72030785, -12052258, 19144587, 21630753, 30113977, 48587010, 48332373, 15279299, -43811946, -58262663, -36406480, -7700238, -30359080, -33371571, -13540688, 13350263, -37816128, -85090930, -88730267, -22683366, -2147602, 2656676, 13116997, 99364479, 153210432, 153333216, 82542295, 72270278, 86763248, 93370503, 13968782, -6255665, 45972603, 114571713, 41538412, -22875788, 9123692, 91835996, -3839252, -132902062, -130972374, -19996538, -97012172, -234050021, -199481526, 4356949, 3404765, -108346869, -47055959, 194463604, 163221218, -61809057, -96003116, 132039203, 112872016, -111654138, -99546359, 239182724, 290320879, 17984513, -71575505, 202252381, 208570415, -130999493, -265073814, 53378697, 154968550, -139840393, -310433553, -45293232, 44775942, -229700135, -381161623, -81498274, 96881339, -70875094, -201328899, 15285159, 130458123, 934146, -92163920, 54252278, 76382757, -56829125, -151593102, -113126833, -172914537, -190997491, -90951697, 8250419, -76122008, -58824481, 52690186, 34954631, -138318345, -74174695, 14377071, -171620115, -345807302, -21438740, 188290863, -136028955, -275025800, 303515990, 441562513, -254794132, -407391558, 398437226, 325737925, -593565921, -264160648, 748785691, -125025056, -995333024, 591448123, 549312497, -2121918760, 1637174117, -1009132542]

/-- K = 128 signed family, `da¹`, over `2^40`. -/
def da1_128 : List ℤ :=
  [-15479855706, 5649759240, 1353916940, 1329839036, 419762669, 115695073, 1093344940, 2930960082, 1359046588, -226571109, 1636246509, 3901807447, 1765890191, -462200988, 1929995195, 4484612663, 1897544313, -716744764, 1957994895, 4619078579, 1763449604, -987938237, 1728551582, 4300166512, 1403239798, -1244970253, 1301680293, 3603742035, 899926574, -1425898624, 761340759, 2644684644, 345284087, -1504026519, 189709295, 1530425425, -185473980, -1459815031, -338796865, 412633279, -616981077, -1257538441, -749322033, -568836514, -893032827, -906271427, -1004180073, -1332961940, -1004005559, -444787371, -1090510713, -1820940662, -935828216, 78309782, -1000623969, -2028863637, -714873222, 587337266, -785659476, -1992080213, -387338534, 1024113862, -483166158, -1744456948, -10486934, 1360237686, -174194173, -1348246404, 341098206, 1551546034, 112242414, -881678822, 638703409, 1580266581, 307756738, -420418720, 802001580, 1436900013, 402782353, -32483630, 872651368, 1145984439, 419979464, 261529573, 839217550, 777268133, 363183963, 480620131, 724401272, 409037819, 229645211, 622872878, 550268100, 83098053, 82376968, 697770446, 379449658, -176213332, -83828129, 670732778, 213271792, -368143717, -203473043, 607338144, 123482873, -430487108, -233183664, 558435127, 113027492, -367145989, -227072018, 487175087, 69838653, -300885023, -219473012, 347256118, 41461259, -214142766, -156598974, 249445149, 58580400, -84564515, -82650950, 170921931, 17136233, -17350734, -31818278, 99357241]

/-- K = 128 signed family, `dv¹`, over `2^40`. -/
def dv1_128 : List ℤ :=
  [33761453881, -26653959390, -16141981414, 15361083557, 15659446390, -15258118367, -10988882330, 11464417205, 11241548282, -11853007847, -8704039875, 9686073679, 9030761508, -10110429300, -7314592159, 8619977282, 7627349331, -9021989765, -6337124770, 7894945854, 6622727018, -8263759103, -5586393920, 7364416712, 5847637733, -7697974397, -4974627848, 6955694146, 5212463989, -7264507526, -4464237574, 6623346155, 4670721104, -6916803301, -4015934052, 6355022343, 4203888846, -6623671331, -3611507124, 6126776890, 3781774069, -6374710297, -3236111645, 5930801496, 3387340630, -6167553777, -2885869490, 5761059789, 3014342411, -5994712318, -2555469508, 5617763750, 2673232636, -5826457733, -2220767946, 5502173987, 2347975884, -5685651889, -1920374971, 5363724462, 2004364033, -5563541942, -1613583904, 5248405363, 1678791107, -5433992614, -1289431471, 5151408238, 1358498214, -5311205250, -968136522, 5050347899, 1034390092, -5188103100, -651001822, 4919181630, 675367496, -5068319588, -311173029, 4794949388, 313955313, -4926932490, 63946831, 4677746931, -54506908, -4772869377, 449774396, 4531291348, -456540072, -4620800601, 821279539, 4328418463, -874534691, -4399659685, 1239513585, 4074235791, -1320669401, -4087112914, 1743815092, 3784674966, -1802801233, -3714425690, 2253439513, 3351725229, -2376295944, -3268516420, 2785976518, 2807575868, -2917223463, -2603177982, 3332614234, 2031967381, -3430118449, -1644636515, 3785438545, 840494820, -3808178026, -173033220, 3980829598, -977265348, -3650584010, 2069584412, 3056745239, -3694569071, -1092109221, 4746596814, -3874684464, 1280042059]

/-- K = 40 unsigned trial `40_0.102`, `du`, over `2^24`. -/
def du40 : List ℤ :=
  [-277603, 121762, 40044, 37293, 33803, 37363, 54522, 77507, 64541, 49136, 75048, 99323, 77687, 55657, 83041, 106597, 78490, 53526, 79452, 99878, 69207, 44381, 66947, 82734, 53351, 31514, 49487, 60237, 35245, 18476, 31261, 37561, 18881, 8045, 15822, 18837, 6842, 1814, 5096, 6460]

/-- K = 40 unsigned trial `40_0.102`, `dv`, over `2^24`. -/
def dv40 : List ℤ :=
  [1229089, -1043916, -551650, 630521, 518169, -638354, -323185, 500445, 317582, -521037, -204888, 442968, 199266, -460116, -117630, 406227, 107712, -417621, -40548, 374826, 24650, -378793, 36032, 338967, -59137, -331621, 118210, 285599, -149105, -257433, 207619, 187445, -240197, -111879, 278442, -29031, -238877, 217239, -59695, -7499]

/-- K = 24 constrained trial, `du`, over `2^24`. -/
def du24 : List ℤ :=
  [-155144, 275966, 133791, 131063, 147745, -69889, -79445, -39055, -139516, -49007, 47056, 996, 80421, 99436, -2342, 24719, -7295, -87725, -25959, -44378, -59457, 19218, -32071, 12807]

/-- K = 24 constrained trial, `dv`, over `2^24`. -/
def dv24 : List ℤ :=
  [709459, -1135548, -471209, 791915, 341146, -688128, -216979, 615422, 119263, -564915, -30841, 516584, -54938, -465848, 138430, 399778, -223581, -309080, 299491, 166126, -338861, 60077, 167266, -110310]

/-- K = 24 constrained trial: `dl = 426814 / 2^24` (so `dl = 213407 / 2^23`), `aT = 11 / 50`. -/
def dl24 : ℤ := 426814

/-- The sequence of a scaled list: index `k + 1` carries entry `k`, index `0` carries `0`. -/
def trialSeqOf (l : List ℤ) (D : ℕ) : ℕ → ℝ := fun k =>
  if k = 0 then 0 else (l.getD (k - 1) 0 : ℝ) / D

/-- Finite support: the sequence vanishes from index `l.length + 1` on (the `K` of
`anchorIntercept_move` is `l.length + 1`). -/
theorem trialSeqOf_support (l : List ℤ) (D : ℕ) {k : ℕ} (hk : l.length + 1 ≤ k) :
    trialSeqOf l D k = 0 := by
  unfold trialSeqOf
  have h0 : k ≠ 0 := by omega
  have : l.getD (k - 1) 0 = 0 := List.getD_eq_default _ _ (by omega)
  rw [if_neg h0, this]
  simp

theorem len_da0_128 : da0_128.length = 128 := by decide +kernel
theorem len_dv0_128 : dv0_128.length = 128 := by decide +kernel
theorem len_da1_128 : da1_128.length = 128 := by decide +kernel
theorem len_dv1_128 : dv1_128.length = 128 := by decide +kernel
theorem len_du40 : du40.length = 40 := by decide +kernel
theorem len_dv40 : dv40.length = 40 := by decide +kernel
theorem len_du24 : du24.length = 24 := by decide +kernel
theorem len_dv24 : dv24.length = 24 := by decide +kernel


/-! ### The Chebyshev bridge and the degree-41 leaf `hT_ext` (t4b)

`barrierTrialT (trialSeqOf l D)` is the finite sum `Σ_k (l_k / D) T_{k+1}(x) / (k + 1)`.  The check
`-2 T(du40, x) ≤ 1287/10^5` on `[98749/10^6, 401/2500]` is the nonnegativity of the integer
polynomial `Q = 2^23 · 10^5 · L · (1287/10^5 + 2 T(du40, ·))`, `L = lcm(1..40)`, built by the
Chebyshev recursion `T4Instance.chebSum`, composed with `x = (98749 + 61651 w)/10^6` and checked on
`w ∈ [0, 1]` by the integer subdivision `T4Instance.checkZ`.

kcost: one kernel decision `checkZ` of depth 4 on a degree-41 integer polynomial: 9 `cellOK` calls
(Python mirror `work/tools/g3/t4/price_leaf2.py`), measured 0.19 s per call, below 2 s. -/

theorem trialT_eq_sum (l : List ℤ) (D : ℕ) (x : ℝ) :
    barrierTrialT (trialSeqOf l D) x =
      ∑ k ∈ Finset.range l.length, ((l.getD k 0 : ℝ) / D) *
        (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ) := by
  unfold barrierTrialT
  have heq (k : ℕ) : trialSeqOf l D (k + 1) = (l.getD k 0 : ℝ) / D := by simp [trialSeqOf]
  simp_rw [heq]
  apply tsum_eq_sum
  intro k hk
  have hlen : l.length ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  rw [List.getD_eq_default l 0 hlen]
  norm_num

/-- Weights `l_k · (K / (k + 1))`. -/
def weightsOf (K : ℤ) (l : List ℤ) : List ℤ :=
  (List.range l.length).map (fun k => l.getD k 0 * (K / ((k : ℤ) + 1)))

theorem weightsOf_length (K : ℤ) (l : List ℤ) : (weightsOf K l).length = l.length := by
  simp [weightsOf]

theorem weightsOf_getD (K : ℤ) (l : List ℤ) {k : ℕ} (hk : k < l.length) :
    (weightsOf K l).getD k 0 = l.getD k 0 * (K / ((k : ℤ) + 1)) := by
  simp [weightsOf, List.getD_eq_getElem?_getD, hk]

/-- The Chebyshev combination `c₀ T₀ + Σ ws_i T_{i+1}` as an integer polynomial. -/
def chebPoly (c0 : ℤ) (ws : List ℤ) : List ℤ :=
  T4Instance.chebSum (c0 :: ws) [1] [0, 1]

theorem evalZ_chebPoly (c0 : ℤ) (ws : List ℤ) (x : ℝ) :
    T4Instance.evalZ (chebPoly c0 ws) x =
      c0 + ∑ i ∈ Finset.range ws.length,
        (ws.getD i 0 : ℝ) * (Polynomial.Chebyshev.T ℝ ((i + 1 : ℕ) : ℤ)).eval x := by
  unfold chebPoly
  have h0 : T4Instance.evalZ [1] x = (Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ)).eval x := by
    simp [T4Instance.evalZ]
  have h1 : T4Instance.evalZ [0, 1] x = (Polynomial.Chebyshev.T ℝ ((0 + 1 : ℕ) : ℤ)).eval x := by
    simp [T4Instance.evalZ]
  rw [T4Instance.evalZ_chebSum (c0 :: ws) 0 [1] [0, 1] x h0 h1, List.length_cons,
    Finset.sum_range_succ']
  simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.zero_add, Nat.add_zero]
  have : (Polynomial.Chebyshev.T ℝ ((0 : ℕ) : ℤ)).eval x = 1 := by simp
  rw [this]
  simp only [mul_one]
  ring

/-- `x ↦ p (a + b x)` as an integer polynomial. -/
def compLin (a b : ℤ) : List ℤ → List ℤ
  | [] => []
  | c :: q => T4Instance.addL [c] (T4Instance.addL (T4Instance.smulL a (compLin a b q))
      (0 :: T4Instance.smulL b (compLin a b q)))

theorem evalZ_compLin (a b : ℤ) (p : List ℤ) (w : ℝ) :
    T4Instance.evalZ (compLin a b p) w = T4Instance.evalZ p ((a : ℝ) + b * w) := by
  induction p with
  | nil => simp [compLin, T4Instance.evalZ]
  | cons c q ih =>
    simp only [compLin, T4Instance.evalZ_addL, T4Instance.evalZ_smulL, T4Instance.evalZ, ih]
    ring

/-- `y ↦ N^len · p (y / N)` as an integer polynomial. -/
def scaleN (N : ℤ) : List ℤ → List ℤ
  | [] => []
  | c :: q => (c * N ^ (q.length + 1)) :: scaleN N q

theorem evalZ_scaleN {N : ℤ} (hN : (N : ℝ) ≠ 0) (p : List ℤ) (y : ℝ) :
    T4Instance.evalZ (scaleN N p) y = (N : ℝ) ^ p.length * T4Instance.evalZ p (y / N) := by
  induction p with
  | nil => simp [scaleN, T4Instance.evalZ]
  | cons c q ih =>
    simp only [scaleN, T4Instance.evalZ, ih, List.length_cons]
    push_cast
    field_simp
    ring

/-- The integer polynomial of the `hT` leaf. -/
def hTc0 : ℤ := 1287 * 2 ^ 23 * 5342931457063200

def hTws : List ℤ := weightsOf (10 ^ 5 * 5342931457063200) du40

def hTz : List ℤ := compLin 98749 61651 (scaleN (10 ^ 6) (chebPoly hTc0 hTws))

theorem hT_div : ∀ k : ℕ, k < 40 → (10 ^ 5 * 5342931457063200 : ℤ) % ((k : ℤ) + 1) = 0 := by
  decide +kernel

/-- The leaf: `Q` is nonnegative on `[0,1]` by a depth-4 integer subdivision. -/
theorem hT_check : T4Instance.checkZ hTz 4 0 0 = true := by
  decide +kernel

theorem hT_ext (τ : ℝ) (hτ : τ = 0 ∨ τ = 1) :
    ∀ x ∈ Icc (98749 / 1000000 : ℝ) (401 / 2500),
      -2 * (τ * barrierTrialT (trialSeqOf du40 (2 ^ 24)) x) ≤ 1287 / 100000 := by
  intro x hx
  rcases hτ with rfl | rfl
  · norm_num
  · simp only [one_mul]
    set N : ℤ := 10 ^ 6 with hNdef
    have hN : (N : ℝ) ≠ 0 := by rw [hNdef]; norm_num
    set w : ℝ := (x - 98749 / 1000000) / (61651 / 1000000) with hw
    have hw0 : 0 ≤ w := div_nonneg (by linarith [hx.1]) (by norm_num)
    have hw1 : w ≤ 1 := by
      rw [hw, div_le_one (by norm_num)]; linarith [hx.2]
    have hnn := T4Instance.checkZ_sound hT_check (m := 0) (s := 0) (w := w)
      (by simpa using hw0) (by simpa using hw1)
    have hlin : ((98749 : ℤ) : ℝ) + ((61651 : ℤ) : ℝ) * w = (N : ℝ) * x := by
      rw [hw, hNdef]; push_cast; field_simp; ring
    have hz : T4Instance.evalZ hTz w =
        (N : ℝ) ^ (chebPoly hTc0 hTws).length *
          T4Instance.evalZ (chebPoly hTc0 hTws) x := by
      unfold hTz
      rw [evalZ_compLin, hlin, evalZ_scaleN hN]
      congr 2
      field_simp
    rw [hz] at hnn
    have hNpos : (0 : ℝ) < (N : ℝ) ^ (chebPoly hTc0 hTws).length := by
      rw [hNdef]; positivity
    have hq : 0 ≤ T4Instance.evalZ (chebPoly hTc0 hTws) x := by
      by_contra hneg
      have := mul_neg_of_pos_of_neg hNpos (not_le.mp hneg)
      linarith
    rw [evalZ_chebPoly, hTws, weightsOf_length, len_du40] at hq
    rw [trialT_eq_sum, len_du40]
    have hdiv := hT_div
    have key : ∀ k ∈ Finset.range 40,
        ((weightsOf (10 ^ 5 * 5342931457063200) du40).getD k 0 : ℝ) *
            (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x =
          (2 ^ 23 * 10 ^ 5 * 5342931457063200 : ℝ) * 2 *
            (((du40.getD k 0 : ℝ) / ((2 ^ 24 : ℕ) : ℝ)) *
              (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval x / ((k + 1 : ℕ) : ℝ)) := by
      intro k hk
      have hk40 : k < 40 := Finset.mem_range.mp hk
      rw [weightsOf_getD _ _ (by rw [len_du40]; exact hk40)]
      have hd : ((k : ℤ) + 1) ∣ (10 ^ 5 * 5342931457063200 : ℤ) :=
        Int.dvd_of_emod_eq_zero (hdiv k hk40)
      have hne : (((k : ℤ) + 1 : ℤ) : ℝ) ≠ 0 := by push_cast; positivity
      have := Int.cast_div hd hne
      push_cast at this ⊢
      rw [this]
      field_simp
      ring
    rw [Finset.sum_congr rfl key] at hq
    rw [← Finset.mul_sum] at hq
    unfold hTc0 at hq
    push_cast at hq
    have hM : (0 : ℝ) < 2 ^ 23 * 10 ^ 5 * 5342931457063200 := by positivity
    push_cast
    nlinarith [hq, hM]

/-! ### The extension pair with a block-wise chord correction (t4b)

The chord correction `d = δ̂(t(x))/58` (`t(x) = 2x/(1+x²)`, `δ̂ = pwl 865 kt vt`, the frozen table of
`ChordTableData`) grows along the extension: `δ̂` goes from `-0.20` at `x = 98749/10^6` (`t = .1956`) to
`7.45` at `x = 401/2500` (`t = .3128`), so `d ≤ 1/50` holds only up to `x ≈ .1066`.  The window is therefore
cut into six blocks (equal width `11297665228 / 2^40`); on block `b` the field is capped by `cap_b`
(`cellT`, the retained Taylor cells of `RCover`, one cell per block) and the chord by `dJ_b`, the largest
knot value of the segments meeting `t([l,u])` (`extOv`, the check of `NearDataCert.ovOK`; the lemmas
are re-proved here so that this module does not import `NearDataCert`).  Every block satisfies
`cap_b + dJ_b/58 + 1287/10^5 + 67/2500 ≤ 0` (`τ = 1`) and `cap_b + dJ_b/58 ≤ 7/1000` (`τ = 0`), the least
slack being `0.0225` (generator: `scratch/g3/t4b/Gen.lean`, a Lean `#eval` over `cellT`).

kcost: six `cellT` checks (order 5, 76 poles each), six `extOv` checks of 865 rational comparisons
(measured 0.7 s each in `NearDataCert`), 6 x 8 rational inequalities, and one `coverFrom` on six cells;
estimated below 10 s in the kernel. -/

open CatalanMeasure.GenD.Signed.RouteI.ChordTableData (knotZ vZ kt vt kt_lt)
open CatalanMeasure.GenD.Signed.RouteI.ChordTable (pwl exists_seg pwl_le_max)

/-- The coordinate `t(x) = 2 x / (1 + x^2)` over `Q`. -/
def extTq (x : ℚ) : ℚ := 2 * x / (1 + x ^ 2)
def extKnotQ (i : ℕ) : ℚ := (knotZ i : ℚ) / 2 ^ 40
def extVQ (i : ℕ) : ℚ := (vZ i : ℚ) / 10 ^ 9

theorem extTq_real (x : ℚ) : ((extTq x : ℚ) : ℝ) = 2 * (x : ℝ) / (1 + (x : ℝ) ^ 2) := by
  unfold extTq; push_cast; rfl

theorem ext_kt_eq (i : ℕ) : kt i = (extKnotQ i : ℝ) := by
  unfold extKnotQ kt; push_cast; rfl

theorem ext_vt_eq (i : ℕ) : vt i = (extVQ i : ℝ) := by
  unfold extVQ vt; push_cast; rfl

/-- Every segment of the table meeting `t([l,u])` has both knot values `≤ dJ`. -/
def extOv (l u dJ : ℚ) : Bool :=
  (List.range 865).all fun i =>
    !(decide (extKnotQ i ≤ extTq u) && decide (extTq l ≤ extKnotQ (i + 1))) ||
      (decide (extVQ i ≤ dJ) && decide (extVQ (i + 1) ≤ dJ))

theorem extOv_sound {l u dJ : ℚ} (h : extOv l u dJ = true) :
    ∀ i, i < 865 → kt i ≤ 2 * (u : ℝ) / (1 + (u : ℝ) ^ 2) →
      2 * (l : ℝ) / (1 + (l : ℝ) ^ 2) ≤ kt (i + 1) → vt i ≤ dJ ∧ vt (i + 1) ≤ dJ := by
  intro i hi hA hB
  have h1 := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, decide_eq_true_eq,
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at h1
  rw [ext_kt_eq, ← extTq_real] at hA
  rw [ext_kt_eq, ← extTq_real] at hB
  have hA' : extKnotQ i ≤ extTq u := by exact_mod_cast hA
  have hB' : extTq l ≤ extKnotQ (i + 1) := by exact_mod_cast hB
  rcases h1 with h1 | ⟨h2, h3⟩
  · exfalso
    rcases h1 with h1 | h1
    · exact h1 hA'
    · exact h1 hB'
  · rw [ext_vt_eq, ext_vt_eq]
    exact ⟨by exact_mod_cast h2, by exact_mod_cast h3⟩

/-- `δ̂ ≤ dJ` on `[ta, tb]` when every segment meeting `[ta, tb]` has both knot values `≤ dJ`. -/
theorem ext_pwl_le {K : ℕ} (hK : 0 < K) {k v : ℕ → ℝ} {ta tb dJ : ℝ}
    (hk : ∀ i, i < K → k i < k (i + 1))
    (hov : ∀ i, i < K → k i ≤ tb → ta ≤ k (i + 1) → v i ≤ dJ ∧ v (i + 1) ≤ dJ)
    {t : ℝ} (h0 : k 0 ≤ t) (h1 : t ≤ k K) (hta : ta ≤ t) (htb : t ≤ tb) :
    pwl K k v t ≤ dJ := by
  obtain ⟨i, hi, ht⟩ := exists_seg hK h0 h1
  obtain ⟨ha, hb⟩ := hov i hi (ht.1.trans htb) (hta.trans ht.2)
  exact (pwl_le_max hk hi ht).trans (max_le ha hb)

theorem ext_tcoord_mono {l y u : ℝ} (hl : 0 < l) (hly : l ≤ y) (hyu : y ≤ u) (hu : u ≤ 1) :
    2 * l / (1 + l ^ 2) ≤ 2 * y / (1 + y ^ 2) ∧ 2 * y / (1 + y ^ 2) ≤ 2 * u / (1 + u ^ 2) := by
  have key : ∀ {a b : ℝ}, 0 < a → a ≤ b → b ≤ 1 → 2 * a / (1 + a ^ 2) ≤ 2 * b / (1 + b ^ 2) := by
    intro a b ha hab hb
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr (show a * b ≤ 1 by nlinarith)),
      mul_pos ha ha]
  exact ⟨key hl hly (hyu.trans hu), key (hl.trans_le hly) hyu hu⟩

/-- The six blocks: Taylor cell `(centre, half width)` in units of `2^-40`, field cap, chord cap `dJ`. -/
def extBlocks : List (TCell × ℚ × ℚ) := [
  ((114224506345, 5648832614, 0), (-877 : ℚ) / 10000, (1427645111 : ℚ) / 1000000000),
  ((125522171573, 5648832614, 0), (-1117 : ℚ) / 10000, (704302573 : ℚ) / 250000000),
  ((136819836801, 5648832614, 0), (-167 : ℚ) / 1250, (4147334231 : ℚ) / 1000000000),
  ((148117502029, 5648832614, 0), (-1541 : ℚ) / 10000, (5189835631 : ℚ) / 1000000000),
  ((159415167257, 5648832614, 0), (-867 : ℚ) / 5000, (319028631 : ℚ) / 50000000),
  ((170712832485, 5648832614, 0), (-479 : ℚ) / 2500, (93154629 : ℚ) / 12500000)
]

def extBlkOK (b : TCell × ℚ × ℚ) : Bool :=
  cellT (resSpecW (53 / 58 : ℚ) Pc P) D_R.toD 5 65 MGL_R b.2.1 b.1 &&
  extOv (((b.1.1 - b.1.2.1 : ℤ) : ℚ) / (TT : ℚ)) (((b.1.1 + b.1.2.1 : ℤ) : ℚ) / (TT : ℚ)) b.2.2 &&
  decide (0 < b.1.1 - b.1.2.1) && decide (b.1.1 + b.1.2.1 ≤ TT) &&
  decide (extKnotQ 0 ≤ extTq (((b.1.1 - b.1.2.1 : ℤ) : ℚ) / (TT : ℚ))) &&
  decide (extTq (((b.1.1 + b.1.2.1 : ℤ) : ℚ) / (TT : ℚ)) ≤ extKnotQ 865) &&
  decide (b.2.1 + b.2.2 / 58 + 1287 / 100000 + 67 / 2500 ≤ 0) &&
  decide (b.2.1 + b.2.2 / 58 ≤ 7 / 1000)

-- kcost: 6 blocks; per block one `cellT` (order 5, 76 poles), `extOv` (865 rational comparisons, 0.7 s measured in
-- NearDataCert), and 6 rational inequalities.  Estimated below 10 s; measured in the build log.
theorem extBlocks_ok : extBlocks.all extBlkOK = true := by decide +kernel

theorem ext_cover :
    coverFrom (401 / 2500) (qfloor ((98749 / 1000000 : ℚ) * (TT : ℚ))) (extBlocks.map (·.1)) = true := by
  decide +kernel

/-- Every point of the extension lies in a block `b`: the field is below `cap_b`, `δ̂(t(x)) ≤ dJ_b`,
and the block satisfies the margins of both pair values. -/
theorem ext_block (hZ_R : ∀ x : ℝ, -2 * finUR Pc x = ptZ D_R.toD.Z 0 x) :
    ∀ x ∈ Icc (98749 / 1000000 : ℝ) (401 / 2500), ∃ b ∈ extBlocks,
      resFieldW (((53 / 58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) x ≤ (b.2.1 : ℝ) ∧
      pwl 865 kt vt (realCoordinateInv x) ≤ (b.2.2 : ℝ) ∧
      (b.2.1 : ℝ) + b.2.2 / 58 + 1287 / 100000 + 67 / 2500 ≤ 0 ∧
      (b.2.1 : ℝ) + b.2.2 / 58 ≤ 7 / 1000 := by
  intro x hx
  have hT : (0 : ℝ) < TT := by exact_mod_cast TT_pos
  obtain ⟨c, hc, hcx⟩ := cover_spec (401 / 2500) (extBlocks.map (·.1))
    (qfloor ((98749 / 1000000 : ℚ) * (TT : ℚ))) ext_cover x
    (floor_le_of_ge (98749 / 1000000) x (by push_cast; linarith [hx.1])) (by push_cast; linarith [hx.2])
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  have hok := List.all_eq_true.mp extBlocks_ok b hb
  simp only [extBlkOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hok
  refine ⟨b, hb, ?_, ?_, ?_, ?_⟩
  · exact cellValP_sound (resFieldW (((53 / 58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P))
      (resSpecW (53 / 58 : ℚ) Pc P b.1.2.2) D_R.toD D_R_ok 5 65 MGL_R hMGL_R
      (resSpecW_sound (53 / 58 : ℚ) tailsP P_nonzero D_R.toD hZ_R b.1.2.2) b.2.1 b.1.1 b.1.2.1 h1 x
      hcx (fun pr h => by simp [resSpecW] at h)
  · obtain ⟨hxl, hxu⟩ := abs_le.mp hcx
    set l : ℚ := ((b.1.1 - b.1.2.1 : ℤ) : ℚ) / (TT : ℚ) with hl
    set u : ℚ := ((b.1.1 + b.1.2.1 : ℤ) : ℚ) / (TT : ℚ) with hu
    have hlR : (l : ℝ) = ((b.1.1 : ℝ) - b.1.2.1) / TT := by rw [hl]; push_cast; ring
    have huR : (u : ℝ) = ((b.1.1 : ℝ) + b.1.2.1) / TT := by rw [hu]; push_cast; ring
    have hlx : (l : ℝ) ≤ x := by
      rw [hlR]
      have : (b.1.1 : ℝ) / TT - (b.1.2.1 : ℝ) / TT ≤ x := by linarith
      calc _ = (b.1.1 : ℝ) / TT - (b.1.2.1 : ℝ) / TT := by ring
        _ ≤ x := this
    have hxu' : x ≤ (u : ℝ) := by
      rw [huR]
      have : x ≤ (b.1.1 : ℝ) / TT + (b.1.2.1 : ℝ) / TT := by linarith
      calc x ≤ _ := this
        _ = _ := by ring
    have hl0 : (0 : ℝ) < l := by
      rw [hlR]; apply div_pos _ hT
      have : (0 : ℝ) < ((b.1.1 - b.1.2.1 : ℤ) : ℝ) := by exact_mod_cast h3
      push_cast at this; linarith
    have hu1 : (u : ℝ) ≤ 1 := by
      rw [huR, div_le_one hT]
      have : ((b.1.1 + b.1.2.1 : ℤ) : ℝ) ≤ (TT : ℝ) := by exact_mod_cast h4
      push_cast at this; linarith
    have htm := ext_tcoord_mono hl0 hlx hxu' hu1
    have hk0 : kt 0 ≤ 2 * (l : ℝ) / (1 + (l : ℝ) ^ 2) := by
      rw [ext_kt_eq, ← extTq_real]; exact_mod_cast h5
    have hk1 : 2 * (u : ℝ) / (1 + (u : ℝ) ^ 2) ≤ kt 865 := by
      rw [ext_kt_eq, ← extTq_real]; exact_mod_cast h6
    exact ext_pwl_le (by norm_num) kt_lt (extOv_sound h2) (hk0.trans htm.1) (htm.2.trans hk1)
      htm.1 htm.2
  · have h := (Rat.cast_le (K := ℝ)).mpr h7
    push_cast at h
    linarith
  · have h := (Rat.cast_le (K := ℝ)).mpr h8
    push_cast at h
    linarith

/-- **The extension with the paired trial** (GP Lemma 7.4 on the window `[98749/10^6, 401/2500]`,
`τ ∈ {0, 1}`): the field of the K590 trial minus `2 τ T(du40, x)`, plus the chord correction
`d = δ̂(t(x))/58` of the frozen table, is at most `.0070 + τ (-.0268 - .0070)`.  The hypothesis `hd`
is the definition of the correction; the term for G4 is `ext_pair Cert590.hZ_R hτ hd` with `hd` the
`hd` of `NearDataCert.near_N0`. -/
theorem ext_pair
    (hZ_R : ∀ x : ℝ, -2 * finUR Pc x = ptZ D_R.toD.Z 0 x)
    {d : ℝ → ℝ} {τ : ℝ} (hτ : τ = 0 ∨ τ = 1)
    (hd : ∀ u, d u = pwl 865 kt vt (realCoordinateInv u) / 58) :
    ∀ x ∈ Icc (98749 / 1000000 : ℝ) (401 / 2500),
      resFieldW (((53 / 58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) x
        - 2 * (τ * barrierTrialT (trialSeqOf du40 (2 ^ 24)) x) + d x ≤
      7 / 1000 + τ * (-268 / 10000 - 7 / 1000) := by
  intro x hx
  obtain ⟨b, hb, hF, hD, hm1, hm0⟩ := ext_block hZ_R x hx
  have hdx : d x ≤ (b.2.2 : ℝ) / 58 := by rw [hd x]; linarith
  have hT := hT_ext τ hτ x hx
  rcases hτ with rfl | rfl
  · simp only [zero_mul, mul_zero, sub_zero]
    linarith
  · simp only [one_mul] at hT ⊢
    linarith

/-! ### The TrialEnd shift records (G35, t4b)

A record at `τ ∈ [0, 1]` over the K590 base record `D₀` has `p = p₀ + τ du`, `v = v₀ + τ dv` with
`du`, `dv` of finite support (`trialSeqOf du40 2^24`, `dv40`, ...).  The constructors below discharge,
field by field, everything that is linear algebra in the sequence; the numerical inputs enter as
hypotheses whose sources are named in the docstrings:

* `p_summable`, `v_summable`: finite support of `du`, `dv`;
* `norm_le`: polarisation, `‖p₀ + τ du‖² = ‖p₀‖² + 2τ⟨p₀, du⟩ + τ²‖du‖²`, so the norm cap is
  `D₀.normCap + τ cr + τ² qd` with `cr = 4⟨p₀, du⟩ + ⟨v₀, dv⟩`, `qd = 2‖du‖² + ‖dv‖²/2` (second
  population; `2⟨p₀, du⟩ + ⟨v₀, dv⟩`, `‖du‖² + ‖dv‖²/2` for the first); the inner products are finite
  weighted sums of the finite data (`T4Instance.trial_sum`, `finPart`);
* `row`, `column`: `barrierTrialT`, `barrierTrialS` are linear in the sequence (finite support),
  so the row cap is `MX₀ + ΔX` where `ΔX ≥ sup_{|x| ≤ 1} (-4τ T(du, x) - τ S(dv, x))` (`hX`: the
  polynomial sup of the leaves, `hX_ext`-type degree-41 checks) and the column cap is `MY₀ + ΔY`,
  `ΔY ≥ sup_s (2τ T(dv, s) + Cf' - Cf₀)` (`hY`, with `Cf'` the physical column field `Cf₀ + γ log (1 + s)`);
* `marked`, `near`, `budget`: the new caps `residual(τ)` (`ext_pair`, `residual_pair`), `nearCap` (`near_N0`,
  `near_N1`) and `budget` (`oldBound_budget_of_wV`, `first_budget_of_wV`) are passed through in the form
  of the corresponding structure field for the shifted sequence. -/

section Shift
open Filter Set

theorem barrierTrialT_shift (u w : ℕ → ℝ) (τ : ℝ) {K : ℕ} (hu : Summable (fun k => |u k|))
    (hw : ∀ k, K ≤ k → w k = 0) {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialT (fun k => u k + τ * w k) x = barrierTrialT u x + τ * barrierTrialT w x := by
  have hw' : Summable (fun k => |w k|) := by
    refine summable_of_ne_finset_zero (s := Finset.range K) fun k hk => ?_
    have : K ≤ k := by simpa using hk
    simp [hw k this]
  unfold barrierTrialT
  rw [← tsum_mul_left, ← (barrierTrialT_summable u hu hx).tsum_add
    ((barrierTrialT_summable w hw' hx).mul_left τ)]
  congr 1
  ext k
  ring

theorem barrierTrialS_shift (u w : ℕ → ℝ) (τ : ℝ) {K : ℕ} (hu : Summable (fun k => |u k|))
    (hw : ∀ k, K ≤ k → w k = 0) {x : ℝ} (hx : |x| ≤ 1) :
    barrierTrialS (fun k => u k + τ * w k) x = barrierTrialS u x + τ * barrierTrialS w x := by
  have hw' : Summable (fun k => |w k|) := by
    refine summable_of_ne_finset_zero (s := Finset.range K) fun k hk => ?_
    have : K ≤ k := by simpa using hk
    simp [hw k this]
  unfold barrierTrialS
  rw [← tsum_mul_left, ← (barrierTrialS_summable u hu hx).tsum_add
    ((barrierTrialS_summable w hw' hx).mul_left τ)]
  congr 1
  ext k
  ring

theorem summable_of_support {w : ℕ → ℝ} {K : ℕ} (hw : ∀ k, K ≤ k → w k = 0) :
    Summable (fun k => |w k|) := by
  refine summable_of_ne_finset_zero (s := Finset.range K) fun k hk => ?_
  have : K ≤ k := by simpa using hk
  simp [hw k this]

theorem summable_shift {u w : ℕ → ℝ} (τ : ℝ) {K : ℕ} (hu : Summable (fun k => |u k|))
    (hw : ∀ k, K ≤ k → w k = 0) : Summable (fun k => |u k + τ * w k|) := by
  have h2 : Summable (fun k => |τ * w k|) := by
    refine summable_of_support (K := K) fun k hk => ?_
    simp [hw k hk]
  exact (hu.add h2).of_nonneg_of_le (fun k => abs_nonneg _) (fun k => abs_add_le _ _)

/-- The weighted square sum is summable for a summable sequence. -/
theorem summable_wsq {u : ℕ → ℝ} (hu : Summable (fun k => |u k|)) :
    Summable (fun k : ℕ => u (k + 1) ^ 2 / ((k + 1 : ℕ) : ℝ)) := by
  have h1 : Summable (fun k : ℕ => |u (k + 1)|) := (summable_nat_add_iff 1).mpr hu
  have ht : Tendsto (fun k : ℕ => |u (k + 1)|) atTop (nhds 0) := h1.tendsto_atTop_zero
  have hev : ∀ᶠ k : ℕ in atTop, |u (k + 1)| ≤ 1 :=
    ht.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))
  refine Summable.of_norm_bounded_eventually_nat h1 ?_
  filter_upwards [hev] with k hk
  have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hkp : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le (by norm_num) hk1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hkp, abs_pow]
  calc |u (k + 1)| ^ 2 / ((k + 1 : ℕ) : ℝ) ≤ |u (k + 1)| ^ 2 := div_le_self (by positivity) hk1
    _ ≤ |u (k + 1)| := by nlinarith [abs_nonneg (u (k + 1))]

theorem normSq_smul (w : ℕ → ℝ) (τ : ℝ) :
    barrierTrialNormSq (fun k => τ * w k) = τ ^ 2 * barrierTrialNormSq w := by
  unfold barrierTrialNormSq
  rw [← tsum_mul_left]
  congr 1
  ext k
  ring

/-- Polarisation along the shift: `‖u + τ w‖² = ‖u‖² + 2τ⟨u, w⟩ + τ²‖w‖²`. -/
theorem normSq_shift {u w : ℕ → ℝ} (τ : ℝ) {K : ℕ} (hu : Summable (fun k => |u k|))
    (hw : ∀ k, K ≤ k → w k = 0) :
    barrierTrialNormSq (fun k => u k + τ * w k) =
      barrierTrialNormSq u + 2 * τ * CompletedGas.barrierInner u w + τ ^ 2 * barrierTrialNormSq w := by
  have hw' : ∀ k, K ≤ k → τ * w k = 0 := fun k hk => by simp [hw k hk]
  rw [CompletedGas.barrierTrialNormSq_add (summable_wsq hu) hw', normSq_smul,
    CompletedGas.barrierInner_smul_right]
  ring

/-- **Second-population shift record** (`p = p₀ + τ du`, `v = v₀ + τ dv`).  `Cf'` is the column field of
the new record (`hY` compares it to the base `Cf` up to `ΔY`), `ΔX` bounds the row shift. -/
def shiftSecond {P : Parameters} {W : Set ℝ} {Cf Cf' : ℕ → ℝ → ℝ} {d : ℝ → ℝ}
    {target0 residual0 nearCap0 cost0 target residual nearCap cost : ℝ} {G : ℝ → Prop}
    (D : SecondTrialBoundsEnd P W Cf d target0 residual0 nearCap0 cost0 G)
    {du dv : ℕ → ℝ} {K : ℕ} (hdu : ∀ k, K ≤ k → du k = 0) (hdv : ∀ k, K ≤ k → dv k = 0) (τ : ℝ)
    (ΔX ΔY normCap : ℝ)
    (hnorm : D.normCap + τ * (4 * CompletedGas.barrierInner D.p du + CompletedGas.barrierInner D.v dv) +
      τ ^ 2 * (2 * barrierTrialNormSq du + barrierTrialNormSq dv / 2) ≤ normCap)
    (hX : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      -(4 * (τ * barrierTrialT du x)) - τ * barrierTrialS dv x ≤ ΔX)
    (hY : ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1,
      Cf' N s + 2 * (τ * barrierTrialT dv s) ≤ Cf N s + ΔY)
    (hmarked : ∀ {N : ℕ}, 0 < N → ∀ {x : ℝ}, x ∈ Icc (-1 : ℝ) 1 → G x →
      groupedMarkedField P N x - 2 * barrierTrialT (fun k => D.p k + τ * du k) x + d x ≤
        residual + Real.log 2 / (P.n N : ℝ))
    (hnear : ∀ {N : ℕ}, 0 < N → ∀ {y : ℝ}, y ∈ Ioo (0 : ℝ) 1 → G y →
      groupedNearField P N y - (D.p 1 + τ * du 1) * y + d y ≤ nearCap + Real.log 2 / (P.n N : ℝ))
    (hbudget : ∀ {a t : ℝ}, a ∈ W → 0 ≤ a → 0 ≤ t →
      (-gC0 P + gC1 P * a - a ^ 2 + t - t ^ 2) * Real.log 2 +
        normCap + (1 - a) * (D.fieldCap + ΔX + ΔY) + (a - t) * residual + t * nearCap ≤
          -target + Real.log 2 / 2 + cost * a) :
    SecondTrialBoundsEnd P W Cf' d target residual nearCap cost G where
  p := fun k => D.p k + τ * du k
  v := fun k => D.v k + τ * dv k
  MX := D.MX + ΔX
  MY := D.MY + ΔY
  normCap := normCap
  fieldCap := D.fieldCap + ΔX + ΔY
  p_summable := summable_shift τ D.p_summable hdu
  v_summable := summable_shift τ D.v_summable hdv
  norm_le := by
    have h1 := D.norm_le
    rw [normSq_shift τ D.p_summable hdu, normSq_shift τ D.v_summable hdv]
    rw [CompletedGas.barrierInner_comm D.p, CompletedGas.barrierInner_comm D.v] at *
    nlinarith only [h1, hnorm]
  field_sum := by rw [← D.field_sum]; ring
  row := fun {ε} hε => by
    filter_upwards [D.row hε] with N hN x hx
    have hx1 : |x| ≤ 1 := by
      rcases hx with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [abs_le] <;> constructor <;> linarith
    rw [barrierTrialT_shift _ _ τ D.p_summable hdu hx1, barrierTrialS_shift _ _ τ D.v_summable hdv hx1]
    have := hN x hx
    have := hX x hx
    linarith
  column := fun {ε} hε => by
    filter_upwards [D.column hε, hY] with N hN hYN s hs
    have hs1 : |s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    rw [barrierTrialT_shift _ _ τ D.v_summable hdv hs1]
    have := hN s hs
    have := hYN s hs
    linarith
  marked := hmarked
  near := hnear
  budget := hbudget

/-- **First-population shift record** (`p = p₀ + τ du`, `v = v₀ + τ dv`, the K = 24 constrained trial). -/
def shiftFirst {P : Parameters} {W : Set ℝ} {Cf Cf' : ℕ → ℝ → ℝ} {d : ℝ → ℝ} {G : ℝ → Prop}
    {target0 cost0 target cost : ℝ}
    (D : FirstTrialBoundsEnd P W Cf d G target0 cost0)
    {du dv : ℕ → ℝ} {K : ℕ} (hdu : ∀ k, K ≤ k → du k = 0) (hdv : ∀ k, K ≤ k → dv k = 0) (τ : ℝ)
    (ΔX ΔY normCap M₁ : ℝ)
    (hnorm : D.normCap + τ * (2 * CompletedGas.barrierInner D.p du + CompletedGas.barrierInner D.v dv) +
      τ ^ 2 * (barrierTrialNormSq du + barrierTrialNormSq dv / 2) ≤ normCap)
    (hX : ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo 0 1,
      -(2 * (τ * barrierTrialT du x)) - τ * barrierTrialS dv x ≤ ΔX)
    (hY : ∀ᶠ N : ℕ in atTop, ∀ s ∈ Ioo (0 : ℝ) 1,
      Cf' N s + 2 * (τ * barrierTrialT dv s) ≤ Cf N s + ΔY)
    (hmarked : ∀ {N : ℕ}, 0 < N → ∀ {x : ℝ}, x ∈ Ioo (-1 : ℝ) 1 → x ≠ 0 → G x →
      D.lambda * paramCaseField P N x + d x ≤ M₁)
    (hbudget : ∀ a ∈ W,
      (-gC0 P + gC1 P * a - a ^ 2) * Real.log 2 +
        normCap + (1 - a) * (D.fieldCap + ΔX + ΔY) + a * M₁ ≤
          -target + Real.log 2 / 2 + cost * a) :
    FirstTrialBoundsEnd P W Cf' d G target cost where
  p := fun k => D.p k + τ * du k
  v := fun k => D.v k + τ * dv k
  lambda := D.lambda
  MX := D.MX + ΔX
  MY := D.MY + ΔY
  normCap := normCap
  fieldCap := D.fieldCap + ΔX + ΔY
  M₁ := M₁
  lambda_nonneg := D.lambda_nonneg
  p_summable := summable_shift τ D.p_summable hdu
  v_summable := summable_shift τ D.v_summable hdv
  norm_le := by
    have h1 := D.norm_le
    rw [normSq_shift τ D.p_summable hdu, normSq_shift τ D.v_summable hdv]
    rw [CompletedGas.barrierInner_comm D.p, CompletedGas.barrierInner_comm D.v] at *
    nlinarith only [h1, hnorm]
  field_sum := by rw [← D.field_sum]; ring
  row := fun {ε} hε => by
    filter_upwards [D.row hε] with N hN x hx
    have hx1 : |x| ≤ 1 := by
      rcases hx with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rw [abs_le] <;> constructor <;> linarith
    rw [barrierTrialT_shift _ _ τ D.p_summable hdu hx1, barrierTrialS_shift _ _ τ D.v_summable hdv hx1]
    have := hN x hx
    have := hX x hx
    linarith
  marked := hmarked
  column := fun {ε} hε => by
    filter_upwards [D.column hε, hY] with N hN hYN s hs
    have hs1 : |s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    rw [barrierTrialT_shift _ _ τ D.v_summable hdv hs1]
    have := hN s hs
    have := hYN s hs
    linarith
  budget := hbudget

end Shift

end
end CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance
#print axioms CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance.residual_sup_d58
#print axioms CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance.ext_pair
#print axioms CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance.trialSeqOf_support
#print axioms CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance.hT_ext
#print axioms CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance.ext_block
#print axioms CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance.shiftSecond
#print axioms CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance.shiftFirst
#print axioms CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance.normSq_shift
