module

public import CatalanMeasure.Cert.FieldEval
public import CatalanMeasure.CellCert.Scaled
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import CatalanMeasure.CellCert.ScaledSeries

@[expose] public section

/-!
# D58: the near-field cap (one-variable analysis) and the first coefficient

For `y ∈ (0,1)` and `p ≥ 9/50`:
`-(53/58) log (1+y²) + (47/58) log y - p y ≤ -77/100`  (the true supremum is about `-0.7758`; so the
cap `-39/50` of `D58.nearCap` is NOT valid for the weight `(n0 - 2 g0 - 1)/n0 = 47/58`).
The proof is the monotone / antitone argument of `Parametric.near_residual_field_le_three_fourths`
with a box check `[381/500, 153/200]` evaluated by `sumLogs`.
-/

namespace CatalanMeasure.GenD.Signed

open Set
noncomputable section

/-- The one-variable near field at a supplied first-coefficient threshold. -/
def nearBase (a ell p0 y : ℝ) : ℝ :=
  -a * Real.log (1 + y ^ 2) + ell * Real.log y - p0 * y

/-- Numerator of the derivative of `nearBase`. -/
def nearNum (a ell p0 y : ℝ) : ℝ :=
  ell - p0 * y + (ell - 2 * a) * y ^ 2 - p0 * y ^ 3

theorem near_deriv {a ell p0 y : ℝ} (hy : 0 < y) :
    HasDerivAt (nearBase a ell p0) (nearNum a ell p0 y / (y * (1 + y ^ 2))) y := by
  have hd : 1 + y ^ 2 ≠ 0 := by positivity
  have hp : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (1 : ℝ)
  have hh := (((hp.log hd).const_mul (-a)).add
    ((Real.hasDerivAt_log hy.ne').const_mul ell)).sub
    ((hasDerivAt_id y).const_mul p0)
  refine hh.congr_deriv ?_
  unfold nearNum
  field_simp
  ring

theorem near_num_antitone {a ell p0 x y : ℝ} (hp0 : 0 ≤ p0) (hella : ell ≤ 2 * a)
    (hx : 0 ≤ x) (hxy : x ≤ y) : nearNum a ell p0 y ≤ nearNum a ell p0 x := by
  have h2 := pow_le_pow_left₀ hx hxy 2
  have h3 := pow_le_pow_left₀ hx hxy 3
  have hcoef : 0 ≤ 2 * a - ell := sub_nonneg.mpr hella
  have h1' := mul_le_mul_of_nonneg_left hxy hp0
  have h2' := mul_le_mul_of_nonneg_left h2 hcoef
  have h3' := mul_le_mul_of_nonneg_left h3 hp0
  unfold nearNum
  nlinarith only [h1', h2', h3']

theorem near_box_dominates {a ell p0 cap l u y : ℝ}
    (ha : 0 ≤ a) (hell : 0 ≤ ell) (hp0 : 0 ≤ p0) (hl : 0 < l)
    (hbox : -a * Real.log (1 + l ^ 2) + ell * Real.log u - p0 * l ≤ cap)
    (hy : y ∈ Icc l u) : nearBase a ell p0 y ≤ cap := by
  have hy0 : 0 < y := hl.trans_le hy.1
  have hlog1 : Real.log (1 + l ^ 2) ≤ Real.log (1 + y ^ 2) :=
    Real.log_le_log (by positivity) (by nlinarith only [hl, hy.1])
  have hlog2 : Real.log y ≤ Real.log u := Real.log_le_log hy0 hy.2
  have h1 := mul_le_mul_of_nonneg_left hlog1 ha
  have h2 := mul_le_mul_of_nonneg_left hlog2 hell
  have h3 := mul_le_mul_of_nonneg_left hy.1 hp0
  unfold nearBase
  linarith only [h1, h2, h3, hbox]

/-- A checked box and the derivative signs certify the whole positive near field. -/
theorem near_residual_field_le
    {a ell p0 cap l u p y : ℝ}
    (ha : 0 ≤ a) (hell : 0 ≤ ell) (hp0 : 0 ≤ p0) (hella : ell ≤ 2 * a)
    (hl : 0 < l) (hlu : l ≤ u) (_hu : u ≤ 1)
    (hQl : 0 ≤ ell - p0 * l + (ell - 2 * a) * l ^ 2 - p0 * l ^ 3)
    (hQu : ell - p0 * u + (ell - 2 * a) * u ^ 2 - p0 * u ^ 3 ≤ 0)
    (hbox : -a * Real.log (1 + l ^ 2) + ell * Real.log u - p0 * l ≤ cap)
    (hp : p0 ≤ p) (hy : 0 < y) (_hy1 : y ≤ 1) :
    -a * Real.log (1 + y ^ 2) + ell * Real.log y - p * y ≤ cap := by
  have hu0 : 0 < u := hl.trans_le hlu
  have hmono : MonotoneOn (nearBase a ell p0) (Ioc (0 : ℝ) l) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
    · intro x hx
      exact (near_deriv hx.1).continuousAt.continuousWithinAt
    · intro x hx
      simp only [interior_Ioc, mem_Ioo] at hx
      exact (near_deriv hx.1).differentiableAt.differentiableWithinAt
    · intro x hx
      simp only [interior_Ioc, mem_Ioo] at hx
      rw [(near_deriv hx.1).deriv]
      apply div_nonneg _ (mul_nonneg hx.1.le (by positivity))
      exact le_trans hQl (near_num_antitone hp0 hella hx.1.le hx.2.le)
  have hanti : AntitoneOn (nearBase a ell p0) (Ici u) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · intro x hx
      exact (near_deriv (hu0.trans_le hx)).continuousAt.continuousWithinAt
    · intro x hx
      simp only [interior_Ici, mem_Ioi] at hx
      exact (near_deriv (hu0.trans hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      simp only [interior_Ici, mem_Ioi] at hx
      rw [(near_deriv (hu0.trans hx)).deriv]
      apply div_nonpos_of_nonpos_of_nonneg _
        (mul_nonneg (hu0.trans hx).le (by positivity))
      exact le_trans (near_num_antitone hp0 hella hu0.le hx.le) hQu
  have hb : nearBase a ell p0 y ≤ cap := by
    by_cases ha' : y ≤ l
    · exact (hmono ⟨hy, ha'⟩ ⟨hl, le_rfl⟩ ha').trans
        (near_box_dominates ha hell hp0 hl hbox ⟨le_rfl, hlu⟩)
    · by_cases hc : u ≤ y
      · exact (hanti (by exact le_rfl) hc hc).trans
          (near_box_dominates ha hell hp0 hl hbox ⟨hlu, le_rfl⟩)
      · exact near_box_dominates ha hell hp0 hl hbox ⟨le_of_not_ge ha', le_of_not_ge hc⟩
  have hpy := mul_le_mul_of_nonneg_right hp hy.le
  unfold nearBase at hb
  linarith only [hb, hpy]

end
end CatalanMeasure.GenD.Signed

namespace CatalanMeasure.GenD.D58.Cert
open CatalanMeasure.CellCert CatalanMeasure.Cert OAI.InternalCatalan Set
noncomputable section

def nearBase58 (y : ℝ) : ℝ :=
  -(53/58:ℝ)*Real.log (1+y^2)+(47/58)*Real.log y-(9/50)*y

def nearNum58 (y : ℝ) : ℝ :=
  47/58-(9/50)*y-(59/58)*y^2-(9/50)*y^3

theorem near_deriv58 {y : ℝ} (hy : 0<y) :
    HasDerivAt nearBase58 (nearNum58 y/(y*(1+y^2))) y := by
  have hd : 1+y^2≠0 := by positivity
  have hp : HasDerivAt (fun x : ℝ => 1+x^2) (2*y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (1:ℝ)
  have hh := (((hp.log hd).const_mul (-(53/58:ℝ))).add
    ((Real.hasDerivAt_log hy.ne').const_mul (47/58:ℝ))).sub
    ((hasDerivAt_id y).const_mul (9/50:ℝ))
  refine hh.congr_deriv ?_
  unfold nearNum58
  field_simp
  ring

def nearBoxTerms58 : List LogTerm :=
  [⟨-53/58,0,1+(381/500)^2,0⟩,⟨47/58,0,153/200,0⟩]

def nearBoxOK58 : Bool :=
  match sumLogs nearBoxTerms58 with
  | some ve => decide (ve.1+ve.2-(9/50)*(381/500) ≤ -(77/100:ℚ))
  | none => false

theorem near_box58 :
    -(53/58:ℝ)*Real.log (1+(381/500:ℝ)^2)+
      (47/58)*Real.log (153/200:ℝ)-(9/50)*(381/500) ≤ -(77/100:ℝ) := by
  have hc : nearBoxOK58=true := by decide +kernel
  unfold nearBoxOK58 at hc
  split at hc
  · rename_i ve he
    have hh := sumLogs_spec he
    have hv : (nearBoxTerms58.map LogTerm.val).sum =
        -(53/58:ℝ)*Real.log (1+(381/500:ℝ)^2)+
          (47/58)*Real.log (153/200:ℝ) := by
      simp only [nearBoxTerms58,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      rw [realLogTerm (-53/58) (1+(381/500)^2) (by norm_num),
        realLogTerm (47/58) (153/200) (by norm_num)]
      norm_num
    rw [hv] at hh
    have hq : ve.1+ve.2-(9/50:ℚ)*(381/500) ≤ -(77/100:ℚ) := of_decide_eq_true hc
    have hr : ((ve.1+ve.2-(9/50:ℚ)*(381/500):ℚ):ℝ) ≤ ((-(77/100):ℚ):ℝ) := by
      exact_mod_cast hq
    push_cast at hr
    norm_num at hr
    linarith only [(abs_le.mp hh).2,hr]
  · simp at hc

theorem near_num58_antitone {x y : ℝ} (hx : 0≤x) (hxy : x≤y) :
    nearNum58 y ≤ nearNum58 x := by
  have h2 := pow_le_pow_left₀ hx hxy 2
  have h3 := pow_le_pow_left₀ hx hxy 3
  unfold nearNum58
  linarith only [hxy,h2,h3]

theorem near_box_dominates58 {y : ℝ}
    (hy : y ∈ Icc (381/500:ℝ) (153/200:ℝ)) : nearBase58 y ≤ -(77/100:ℝ) := by
  have hpos : 0<y := by linarith only [hy.1]
  have hlog1 : Real.log (1+(381/500:ℝ)^2) ≤ Real.log (1+y^2) :=
    Real.log_le_log (by positivity) (by nlinarith only [hy.1])
  have hlog2 : Real.log y ≤ Real.log (153/200:ℝ) := Real.log_le_log hpos hy.2
  have hh := near_box58
  unfold nearBase58
  linarith only [hlog1,hlog2,hy.1,hh]

/-- The near-field inequality for the design `(58,9,3,5,3)`. -/
theorem near_residual_field_le_d58 {p y : ℝ} (hp : (9/50:ℝ)≤p)
    (hy : 0<y) (_hy1 : y≤1) :
    -(53/58:ℝ)*Real.log (1+y^2)+(47/58)*Real.log y-p*y ≤ -(77/100:ℝ)  := by
  exact CatalanMeasure.GenD.Signed.near_residual_field_le
    (a := 53 / 58) (ell := 47 / 58) (p0 := 9 / 50)
    (l := 381 / 500) (u := 153 / 200)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    near_box58 hp hy _hy1

/-! ### the first coefficient `p_1 ≥ 9/50` of the witness -/

def firstQ (cs : List ℤ) (tail : List TailQ) : ℚ :=
  (cs.getD 0 0 : ℚ) / 1099511627776 + (tail.map (fun t => t.rr * t.zr - t.ri * t.zi)).sum

theorem tailSum_one (tail : List TailQ) :
    (((tail.map TailQ.toC).map (fun zr : ℂ × ℂ => zr.2 * zr.1 ^ 1)).sum).re =
      (((tail.map (fun t => t.rr * t.zr - t.ri * t.zi)).sum : ℚ) : ℝ) := by
  induction tail with
  | nil => simp
  | cons t tail ih =>
    simp only [List.map_cons, List.sum_cons, Complex.add_re] at ih ⊢
    rw [ih]
    simp [TailQ.toC, barrierComplex, Complex.mul_re]

theorem trialSeqS_one (cs : List ℤ) (tail : List TailQ) :
    trialSeqS cs tail 1 = ((firstQ cs tail : ℚ) : ℝ) := by
  have h := trialSeqS_succ cs tail 0
  rw [zero_add] at h
  rw [h, tailSum_one]
  unfold firstQ
  push_cast
  rfl

-- BEGIN GENERATED FIRSTQ (phase2-data/consts/firstq_emit.py)
-- kcost: 0.067 s estimated; first coefficient plus 56 tails, about 12 rational operations/tail.
-- END GENERATED FIRSTQ

end
end CatalanMeasure.GenD.D58.Cert

#print axioms CatalanMeasure.GenD.Signed.near_deriv
#print axioms CatalanMeasure.GenD.Signed.near_num_antitone
#print axioms CatalanMeasure.GenD.Signed.near_box_dominates
#print axioms CatalanMeasure.GenD.Signed.near_residual_field_le
#print axioms CatalanMeasure.GenD.D58.Cert.near_deriv58
#print axioms CatalanMeasure.GenD.D58.Cert.near_box58
#print axioms CatalanMeasure.GenD.D58.Cert.near_num58_antitone
#print axioms CatalanMeasure.GenD.D58.Cert.near_box_dominates58
#print axioms CatalanMeasure.GenD.D58.Cert.near_residual_field_le_d58
#print axioms CatalanMeasure.GenD.D58.Cert.tailSum_one
#print axioms CatalanMeasure.GenD.D58.Cert.trialSeqS_one
