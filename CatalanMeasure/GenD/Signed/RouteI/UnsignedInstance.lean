module

public import CatalanMeasure.GenD.DesignInstance.PositiveCert.RTab
public import CatalanMeasure.GenD.DesignInstance.PositiveCert.Data
public import CatalanMeasure.GenD.Cert.WLogSpec
public import CatalanMeasure.GenD.Analytic.Glue

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

/-- **The extension with the paired trial** (GP Lemma 7.4 on the window `[98749/10^6, 401/2500]`,
`τ ∈ {0, 1}`).  The built extension cap `ext_cap` (`≤ MR = -315531/5000000`) together with the
Chebyshev bound of the K = 40 term on the window (`hT`, the degree-40 leaf: `-2 T(du, x) ≤ 1287/10^5`,
float maximum `.012868`) and the node correction `d ≤ eD` (`eD ≤ 1/50`, from `ChordTable`) keeps the
paired field below `res_τ = .0070 + τ (-.0268 - .0070)`. -/
theorem ext_pair
    (hZ_R : ∀ x : ℝ, -2 * finUR Pc x = ptZ D_R.toD.Z 0 x)
    {d : ℝ → ℝ} {eD τ : ℝ} (heD : eD ≤ 1 / 50) (hτ : τ = 0 ∨ τ = 1)
    (hT : ∀ x ∈ Icc (98749 / 1000000 : ℝ) (401 / 2500),
      -2 * (τ * barrierTrialT (trialSeqOf du40 (2 ^ 24)) x) ≤ 1287 / 100000)
    (hd : ∀ x ∈ Icc (98749 / 1000000 : ℝ) (401 / 2500), d x ≤ eD) :
    ∀ x ∈ Icc (98749 / 1000000 : ℝ) (401 / 2500),
      resFieldW (((53 / 58 : ℚ) : ℚ) : ℝ) (trialSeqS Pc P) x
        - 2 * (τ * barrierTrialT (trialSeqOf du40 (2 ^ 24)) x) + d x ≤
      7 / 1000 + τ * (-268 / 10000 - 7 / 1000) := by
  intro x hx
  have h1 := ext_cap hZ_R x hx
  have h2 := hT x hx
  have h3 := hd x hx
  have hMR : (MR : ℝ) = -315531 / 5000000 := by unfold MR; norm_num
  rcases hτ with rfl | rfl
  · rw [hMR] at h1
    simp only [zero_mul, mul_zero, sub_zero]
    linarith
  · rw [hMR] at h1
    simp only [one_mul] at h2 ⊢
    linarith

end
end CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance
#print axioms CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance.residual_sup_d58
#print axioms CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance.ext_pair
#print axioms CatalanMeasure.GenD.Signed.RouteI.UnsignedInstance.trialSeqOf_support
