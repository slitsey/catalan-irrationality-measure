module
public import CatalanCore.Li2.DecayCert.Simple.Assembly
public import CatalanCore.Li2.DecayCert.Compile.Regular
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Lists.Stieltjes
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Stieltjes
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Lists
/-! The link from a lattice input to the SIMPLE checks. `latticeMomentsOf` builds the moment data of a
`LatticeInput`; `simpleSourceCheck` checks a `SourceF` and its `SimpleAux` against the input with exact
arithmetic (own polynomials, Stieltjes moments, second-segment moments, antiderivatives) and checked logs;
`simpleEnc`, `simpleWLink` and `simpleALink` turn a passed check into the source enclosures and the W and
atom links the cell and penalty theorems take. -/
@[expose] public section
open MeasureTheory Set Polynomial
namespace CatalanCore.Li2.DecayCert.Simple
open CatalanCore.Li2.DecayCert CatalanCore.Li2.Decay CatalanCore.Li2.DecayCert.LatticeSimple
  CatalanCore.Zeta5.Potential CatalanCore.Li2.DecayCert.LatticeGate
noncomputable section


/-- One stored logarithm, checked against `logQ`. -/
def logEntryOK (e : LogEntry) : Bool :=
  match CatalanMeasure.GenD.Signed.LogEval.logQ 6 e.arg with
  | none => false
  | some (v,err) => decide (0<e.arg ∧ 0≤err ∧ e.bounds.1≤(boxOfQ (v-err)).1 ∧
      (boxOfQ (v+err)).2≤e.bounds.2)

theorem dec_le_of_le {a b : ℤ} (h : a≤b) : dec S a≤dec S b :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) S_real_pos.le

theorem logEntryOK_sound (e : LogEntry) (he : logEntryOK e=true) :
    Contains e.bounds (Real.log (e.arg:ℝ)) := by
  unfold logEntryOK at he
  split at he
  · cases he
  · rename_i v err hv
    simp only [decide_eq_true_eq] at he
    have hb:=CatalanMeasure.GenD.Signed.LogEval.logQ_spec hv
    have hlog:=abs_le.mp hb.2
    have hlo:=boxOfQ_sound (v-err)
    have hhi:=boxOfQ_sound (v+err)
    refine ⟨(dec_le_of_le he.2.2.1).trans (hlo.1.trans ?_),
      (show Real.log (e.arg:ℝ)≤((v+err:ℚ):ℝ) from ?_).trans (hhi.2.trans (dec_le_of_le he.2.2.2))⟩
    · push_cast; linarith [hlog.1]
    · push_cast; linarith [hlog.2]

theorem logsOK_of_entries (logs : List LogEntry) (h : logs.all logEntryOK=true) : LogsOK logs :=
  fun e he => logEntryOK_sound e (List.all_eq_true.mp h e he)

/-- A box inside another encloses whatever the first encloses. -/
theorem contains_mono (a b : FBox) (x : ℝ) (ha : Contains a x) (h1 : b.1 ≤ a.1) (h2 : a.2 ≤ b.2) :
    Contains b x := ⟨(dec_le_of_le h1).trans ha.1,ha.2.trans (dec_le_of_le h2)⟩

theorem contains_ratCast (b : FBox) (q : ℚ) (h : (b.1:ℚ) ≤ q*(S:ℚ) ∧ q*(S:ℚ) ≤ (b.2:ℚ)) :
    Contains b (q:ℝ) := by
  have hS : (0:ℚ) < (S:ℚ) := by exact_mod_cast S_pos
  unfold Contains dec
  constructor
  · rw [div_le_iff₀ S_real_pos]; exact_mod_cast h.1
  · rw [le_div_iff₀ S_real_pos]; exact_mod_cast h.2


/-! ### Exact polynomial lists -/

theorem qListPoly_cons' (a : ℚ) (l : List ℚ) : qListPoly (a::l)=C a+X*qListPoly l := by
  ext j
  cases j with
  | zero => simp [qListPoly_coeff,coeffQ]
  | succ j =>
    rw [Polynomial.coeff_add,Polynomial.coeff_X_mul,qListPoly_coeff,qListPoly_coeff]
    simp [coeffQ]

/-- Horner in the high-first order of `hornerR` evaluates the ascending exact list. -/
theorem hornerR_reverse (l : List ℚ) (x : ℝ) :
    hornerR x ((l.map (fun q : ℚ => (q:ℝ))).reverse)=((qListPoly l).map (algebraMap ℚ ℝ)).eval x := by
  unfold hornerR
  rw [List.foldl_reverse]
  induction l with
  | nil => simp [qListPoly]
  | cons a l ih =>
    simp only [List.map_cons,List.foldr_cons]
    rw [ih,qListPoly_cons',Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
    simp; ring

/-- The constant-zero antiderivative of an ascending list. -/
def qListIntegral (l : List ℚ) : List ℚ := 0 :: (List.range l.length).map (fun i => coeffQ l i/((i:ℚ)+1))

theorem coeffQ_qListIntegral (l : List ℚ) (j : ℕ) :
    coeffQ (qListIntegral l) (j+1)=coeffQ l j/((j:ℚ)+1) := by
  unfold qListIntegral coeffQ
  simp only [List.getElem?_cons_succ]
  by_cases hj : j < l.length
  · simp [List.getElem?_map,List.getElem?_range hj]
  · have : l[j]?=none := List.getElem?_eq_none (by omega)
    have hr : (List.range l.length)[j]?=none := List.getElem?_eq_none (by simp; omega)
    simp [hr,this]

theorem qListIntegral_derivative (l : List ℚ) :
    derivative (qListPoly (qListIntegral l))=qListPoly l := by
  ext j
  rw [Polynomial.coeff_derivative,qListPoly_coeff,qListPoly_coeff,coeffQ_qListIntegral]
  have : ((j:ℚ)+1) ≠ 0 := by positivity
  push_cast; field_simp

theorem qListIntegral_coeff_zero (l : List ℚ) : (qListPoly (qListIntegral l)).coeff 0=0 := by
  rw [qListPoly_coeff]; simp [qListIntegral,coeffQ]

/-- The mapped list antiderivative is the frozen `Polynomial.integral` of the mapped list. -/
theorem qListIntegral_map (l : List ℚ) :
    (qListPoly (qListIntegral l)).map (algebraMap ℚ ℝ)=((qListPoly l).map (algebraMap ℚ ℝ)).integral := by
  set P := (qListPoly (qListIntegral l)).map (algebraMap ℚ ℝ)
  set Q := ((qListPoly l).map (algebraMap ℚ ℝ)).integral
  have hd : derivative (P-Q)=0 := by
    rw [derivative_sub,Polynomial.derivative_map,qListIntegral_derivative,derivative_integral,sub_self]
  obtain ⟨c,hc⟩ : ∃ c, P-Q=C c := ⟨(P-Q).coeff 0,Polynomial.eq_C_of_derivative_eq_zero hd⟩
  have h0 : (P-Q).eval 0=0 := by
    simp only [P,Q,Polynomial.eval_sub,Polynomial.integral_eval_zero,Polynomial.eval_map,
      Polynomial.eval₂_at_zero,qListIntegral_coeff_zero,map_zero,sub_zero]
  rw [hc,Polynomial.eval_C] at h0
  rw [h0,map_zero] at hc
  exact sub_eq_zero.mp hc

theorem cqReal_real (a : ℚ) : cqReal (a,0)=((a:ℝ):ℂ) := by simp [cqReal]

/-- The moment data of a lattice input around a rational `y₀ < 0` with support radius `H` for the
second segment. -/
def latticeMomentsOf (d : LatticeInput) (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (hsh : latticeShapeCheck d=true) (y0 H : ℚ) (hy : y0 < 0) (hH : 0 ≤ H) (hsep : H < -y0)
    (h4 : |(-4:ℚ)-y0| ≤ H) (h1 : |(-1:ℚ)-y0| ≤ H) :
    LatticeMomentData d.first.measure d.second.measure (d.Y:ℝ) where
  c := fun k => (d.first.c k:ℝ)
  N := d.first.coeff.length-1
  finite_coeff := by
    intro k hk
    have : d.first.c k=0 := by
      unfold QSegment.c
      rw [List.getElem?_eq_none (by have := (datum_source_data d.data dw hd d.first (lattice_first_mem d)).2.1; omega)]
      rfl
    simp [this]
  nonneg := (datum_source_data d.data dw hd d.first (lattice_first_mem d)).2.2
  first_measure := by
    have h := latticeShapeCheck_parts d hsh
    unfold QSegment.measure
    rw [h.2.1,h.2.2.1,cqReal_real]
    push_cast; rfl
  y0 := (y0:ℝ)
  y0_neg := by exact_mod_cast hy
  supportRadius := (H:ℝ)
  supportRadius_nonneg := by exact_mod_cast hH
  separated := by have : (H:ℝ) < -(y0:ℝ) := by exact_mod_cast hsep
                  linarith
  second_support := by
    apply measure_mono_null _ (lattice_second_support d hsh)
    intro y hy'
    simp only [mem_setOf_eq] at hy' ⊢
    by_contra hc
    push_neg at hc
    obtain ⟨him,hre1,hre2⟩ := hc
    have hyre : y=((y.re:ℝ):ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hyre,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at hy'
    have h4' : |(-4:ℝ)-(y0:ℝ)| ≤ (H:ℝ) := by exact_mod_cast h4
    have h1' : |(-1:ℝ)-(y0:ℝ)| ≤ (H:ℝ) := by exact_mod_cast h1
    rw [abs_le] at h4' h1'
    have hb : |y.re-(y0:ℝ)| ≤ (H:ℝ) := abs_le.mpr ⟨by linarith [h4'.1],by linarith [h1'.2]⟩
    linarith

/-- The positive own polynomial `Σ c_{k+1}/(k+1) T_{k+1}` of a segment, over ℝ. -/
def ownPlusR (d : QSegment) : ℝ[X] :=
  ∑ k ∈ Finset.range (d.coeff.length-1),
    Polynomial.C ((d.c (k+1):ℝ)/((k+1:ℕ):ℝ))*Polynomial.Chebyshev.T ℝ ((k+1:ℕ):ℤ)

theorem ownPlus_map (d : QSegment) :
    (qListPoly (qListScale (-1) (qOwnCoeffs d))).map (algebraMap ℚ ℝ)=ownPlusR d := by
  rw [qListPoly_scale,qOwnCoeffs_spec,QSegment.ownPolyQ,ownPlusR]
  simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_neg,Polynomial.map_sum,
    Polynomial.Chebyshev.map_T]
  simp only [map_neg,map_one,Polynomial.C_neg,Polynomial.C_1,neg_mul,one_mul,neg_neg,eq_ratCast]
  apply Finset.sum_congr rfl
  intro k _
  push_cast; ring_nf

theorem ownUPoly_eq (d : LatticeInput) (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (hsh : latticeShapeCheck d=true) (y0 H : ℚ) (hy : y0 < 0) (hH : 0 ≤ H) (hsep : H < -y0)
    (h4 : |(-4:ℚ)-y0| ≤ H) (h1 : |(-1:ℚ)-y0| ≤ H) :
    ownUPoly (latticeMomentsOf d dw hd hsh y0 H hy hH hsep h4 h1)=
      (ownPlusR d.first).comp (Polynomial.C (-1)+Polynomial.C (2/(d.Y:ℝ))*Polynomial.X) := by
  unfold ownUPoly ownPlusR latticeMomentsOf
  rfl

/-- `hq1`: the Horner list of the own polynomial evaluates `ownUPoly` at `2x/Y − 1`. -/
theorem hq1_of_exact (d : LatticeInput) (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (hsh : latticeShapeCheck d=true) (y0 H : ℚ) (hy : y0 < 0) (hH : 0 ≤ H) (hsep : H < -y0)
    (h4 : |(-4:ℚ)-y0| ≤ H) (h1 : |(-1:ℚ)-y0| ≤ H) (x : ℝ) :
    hornerR (2*x/(d.Y:ℝ)-1) (((qListScale (-1) (qOwnCoeffs d.first)).map (fun q : ℚ => (q:ℝ))).reverse)=
      (ownUPoly (latticeMomentsOf d dw hd hsh y0 H hy hH hsep h4 h1)).eval x := by
  rw [hornerR_reverse,ownPlus_map,ownUPoly_eq,Polynomial.eval_comp]
  congr 1
  simp only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_X]
  ring

/-- The ascending list of `ownUPoly` in `x`. -/
def ownXList (d : LatticeInput) : List ℚ := qAffineList (qListScale (-1) (qOwnCoeffs d.first)) (-1) (2/d.Y)

/-- `hqIe`: the Horner list of the antiderivative evaluates `∫ ownUPoly`. -/
theorem hqI_of_exact (d : LatticeInput) (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (hsh : latticeShapeCheck d=true) (y0 H : ℚ) (hy : y0 < 0) (hH : 0 ≤ H) (hsep : H < -y0)
    (h4 : |(-4:ℚ)-y0| ≤ H) (h1 : |(-1:ℚ)-y0| ≤ H) (x : ℝ) :
    (((qListIntegral (ownXList d)).map (fun q : ℚ => (q:ℝ))).reverse).foldl (fun t b => x*t+b) 0=
      (ownUPoly (latticeMomentsOf d dw hd hsh y0 H hy hH hsep h4 h1)).integral.eval x := by
  have h := hornerR_reverse (qListIntegral (ownXList d)) x
  unfold hornerR at h
  rw [h,qListIntegral_map,ownXList,qAffineList_spec,Polynomial.map_comp,ownPlus_map,ownUPoly_eq]
  congr 3
  simp [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X]

theorem qListPoly_map_eval (l : List ℚ) (u : ℝ) :
    ((qListPoly l).map (algebraMap ℚ ℝ)).eval u=∑ k ∈ Finset.range l.length,(coeffQ l k:ℝ)*u^k := by
  induction l with
  | nil => simp [qListPoly]
  | cons a l ih =>
    rw [qListPoly_cons',Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,ih,
      List.length_cons,Finset.sum_range_succ']
    simp only [coeffQ,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,pow_zero,mul_one,
      pow_succ,Finset.mul_sum,eq_ratCast]
    rw [add_comm]; congr 1
    apply Finset.sum_congr rfl; intro k _; ring

/-- The Stieltjes series of the first segment about `y₀`, as an ascending list in `u`. -/
def stieltjesList (sm : List ℚ) (KA : ℕ) : List ℚ :=
  (List.range (KA+1)).map (fun k => if k=0 then 0 else coeffQ sm k/(k:ℚ))

/-- The ascending atom polynomial `P_A` in `x`: the second segment's own polynomial at
`t = 5/3 − 2x/3` plus the Stieltjes series at `u = −y₀ − x`. -/
def atomXList (d : LatticeInput) (y0 : ℚ) (sm : List ℚ) (KA : ℕ) : List ℚ :=
  qListAdd (qAffineList (qListScale (-1) (qOwnCoeffs d.second)) (5/3) (-2/3))
    (qAffineList (stieltjesList sm KA) (-y0) (-1))

theorem atomXList_eval (d : LatticeInput) (y0 : ℚ) (sm : List ℚ) (KA : ℕ) (x : ℝ) :
    hornerR x (((atomXList d y0 sm KA).map (fun q : ℚ => (q:ℝ))).reverse)=
      (ownPlusR d.second).eval (5/3-2/3*x)+∑ k ∈ Finset.range (KA+1),
        (if k=0 then 0 else (coeffQ sm k:ℝ)/(k:ℝ))*(-(y0:ℝ)-x)^k := by
  rw [hornerR_reverse,atomXList,qListPoly_add,Polynomial.map_add,Polynomial.eval_add,
    qAffineList_spec,qAffineList_spec,Polynomial.map_comp,Polynomial.map_comp,ownPlus_map,
    Polynomial.eval_comp,Polynomial.eval_comp]
  congr 1
  · congr 1; simp; ring
  · have hu : (Polynomial.map (algebraMap ℚ ℝ) (C (-y0)+C (-1)*X)).eval x= -(y0:ℝ)-x := by simp; ring
    rw [hu,qListPoly_map_eval]
    have hl : (stieltjesList sm KA).length=KA+1 := by simp [stieltjesList]
    rw [hl]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < KA+1 := Finset.mem_range.mp hk
    unfold stieltjesList coeffQ
    simp only [List.getElem?_map,List.getElem?_range hk',Option.map_some,Option.getD_some]
    split_ifs <;> push_cast <;> ring

theorem seg_first_integrable_left {Y : ℝ} (hY : 0<Y) {c : ℕ → ℝ} {N : ℕ}
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1, 0 ≤ chebF c N x) {x : ℝ} (hx : 0 < x) :
    Integrable (fun u => Real.log ‖(-(x:ℂ))-u‖) (CatalanCore.Tools.Joukowski.segMeasure (Y/2:ℂ) (Y/2:ℂ) c N) := by
  have hmeas : Measurable fun u : ℂ => Real.log ‖(-(x:ℂ))-u‖ := Real.measurable_log.comp (by fun_prop)
  rw [CatalanCore.Lai.DecayEnergy.integrable_segMeasure_iff hpos hmeas]
  apply CatalanCore.Li2.DecayCert.integrable_arc_continuous
  apply (continuous_chebF_cos c N).mul
  apply Continuous.log (by fun_prop)
  intro θ h0
  rw [norm_eq_zero] at h0
  have := congrArg Complex.re h0
  simp [Complex.cos_ofReal_re] at this
  nlinarith [Real.neg_one_le_cos θ]

/-- The second segment's potential at `−x`, `x ∈ [1, 4]`, when the segment is `[−4, −1]`. -/
theorem second_U_inside (d : QSegment) (hm : d.mid=(-5/2,0)) (hh : d.half=(3/2,0))
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1, 0 ≤ chebF (fun k => (d.c k:ℝ)) (d.coeff.length-1) x)
    (x : ℝ) (hx : x ∈ Icc (1:ℝ) 4) :
    Integrable (fun v => Real.log ‖(-(x:ℂ))-v‖) d.measure ∧
    U d.measure (-(x:ℂ))=(d.c 0:ℝ)*Real.log (4/3)+(ownPlusR d).eval (5/3-2/3*x) := by
  have hh0 : cqReal d.half ≠ 0 := by rw [hh,cqReal_real]; norm_num
  have ht : (5/3-2/3*x) ∈ Icc (-1:ℝ) 1 := ⟨by linarith [hx.2],by linarith [hx.1]⟩
  have hp := CatalanCore.Lai.DecayEnergy.potC_seg_inside (M:=cqReal d.mid) hh0 hpos ht
  have hpt : cqReal d.mid+cqReal d.half*(((5/3-2/3*x):ℝ):ℂ)= -(x:ℂ) := by
    rw [hm,hh,cqReal_real,cqReal_real]; push_cast; ring
  rw [hpt] at hp
  refine ⟨hp.1,?_⟩
  unfold QSegment.measure
  change -(CatalanCore.Decay.ComplexEnergy.potC _ _)=_
  rw [hp.2]
  have hn : ‖cqReal d.half‖=3/2 := by
    rw [hh,cqReal_real,Complex.norm_real,Real.norm_eq_abs]; norm_num
  rw [hn]
  have hl : Real.log (4/3)=Real.log 2-Real.log (3/2) := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [hl,ownPlusR,Polynomial.eval_finset_sum]
  simp only [Polynomial.eval_mul,Polynomial.eval_C]
  rw [show (∑ k ∈ Finset.range (d.coeff.length-1),(d.c (k+1):ℝ)/((k+1:ℕ):ℝ)*
      (Polynomial.Chebyshev.T ℝ ((k+1:ℕ):ℤ)).eval (5/3-2/3*x))=
      ∑ k ∈ Finset.range (d.coeff.length-1),
        (Polynomial.Chebyshev.T ℝ ((k+1:ℕ):ℤ)).eval (5/3-2/3*x)*(d.c (k+1):ℝ)/((k+1:ℕ):ℝ) from
    Finset.sum_congr rfl (fun k _ => by ring)]
  ring

/-! ### The source check -/

/-- Per-source data beside the `SourceF`: the support radius of the second segment, two log boxes, the
precision of the `U₁(y₀)` expression, the Stieltjes moments, and the stored antiderivative lists. -/
structure SimpleAux where
  H : ℚ
  lU1c : FBox
  lU2c : FBox
  terms : ℕ
  sm : List ℚ
  KA : ℕ
  qI : List FBox
  qAI : List FBox

def qIn (b : FBox) (q : ℚ) : Bool := decide ((b.1:ℚ) ≤ q*(S:ℚ) ∧ q*(S:ℚ) ≤ (b.2:ℚ))
def boxIn (inner outer : FBox) : Bool := decide (outer.1 ≤ inner.1 ∧ inner.2 ≤ outer.2)
def listIn (bs : List FBox) (qs : List ℚ) : Bool :=
  decide (bs.length=qs.length) && (List.range bs.length).all (fun i => qIn (bs.getD i boxZero) (qs.getD i 0))
def widthIn (mids : List ℤ) (w : ℤ) (qs : List ℚ) : Bool :=
  decide (mids.length=qs.length) &&
    (List.range mids.length).all (fun i => decide (|qs.getD i 0-(mids.getD i 0:ℚ)/(S:ℚ)| ≤ (w:ℚ)/(S:ℚ)))
def wQ (d : LatticeInput) (y0 : ℚ) (k : ℕ) : ℚ := arcList (realMomentList d.second y0 (k+1))/((k:ℚ)+1)
def fkQ (d : LatticeInput) : List ℚ := (List.range (d.first.coeff.length-1)).map (fun k => d.first.c (k+1)/((k:ℚ)+1))
def mpErrQ (m v : ℚ) (K : ℕ) : ℚ := m*v^(K+1)/(((K:ℚ)+1)*(1-v))
def u1y0Expr (a : SimpleAux) (d : LatticeInput) (phi : ℚ) : SE := seNeg (segConstant a.terms d.first (-phi,0))
def q1Q (d : LatticeInput) : List ℚ := qListScale (-1) (qOwnCoeffs d.first)

def simpleSourceCheck (z : ℚ) (d : LatticeInput) (s : SourceF) (logs : List LogEntry) (a : SimpleAux) : Bool :=
  decide (s.z=z ∧ s.Y=d.Y ∧ 1 < s.phi ∧ s.y0=d.first.mid.1-d.first.half.1*((s.phi+s.phi⁻¹)/2) ∧
    s.y0 < 0 ∧ 0 ≤ a.H ∧ a.H < -s.y0 ∧ |(-4:ℚ)-s.y0| ≤ a.H ∧ |(-1:ℚ)-s.y0| ≤ a.H ∧ 0 < s.MU.length ∧
    d.second.mid=(-5/2,0) ∧ d.second.half=(3/2,0) ∧ 0 < d.first.half.1 ∧
    a.sm.length=a.KA+1 ∧ 4+s.y0 < -s.y0) &&
  logs.all logEntryOK && logEntryOK ⟨|z|,s.L⟩ &&
  logEntryOK ⟨4/d.Y,a.lU1c⟩ && boxIn (boxMulF (boxOfQ (d.first.c 0)) a.lU1c) s.U1c &&
  logEntryOK ⟨4/3,a.lU2c⟩ && boxIn (boxMulF (boxOfQ (d.second.c 0)) a.lU2c) s.U2c &&
  qIn s.m1 (d.first.c 0) && qIn s.m2 (d.second.c 0) &&
  scalarLowerCheck ((s.U1y0.1:ℚ)/(S:ℚ)) (u1y0Expr a d s.phi) &&
  scalarUpperCheck (u1y0Expr a d s.phi) ((s.U1y0.2:ℚ)/(S:ℚ)) &&
  widthIn s.P1mid s.P1width (q1Q d).reverse &&
  widthIn s.PAmid s.PAwidth (atomXList d s.y0 a.sm a.KA).reverse &&
  listIn s.MU ((List.range s.MU.length).map (wQ d s.y0)) &&
  (List.range s.MU.length).all (fun k => decide (|wQ d s.y0 k| ≤
    |d.second.c 0| * (max |s.y0+4| |-1-s.y0|)^(k+1)/((k:ℚ)+1))) &&
  listIn s.firstOverK (fkQ d) &&
  stieltjesMomentFast d.first s.phi a.KA a.sm &&
  decide (2*mpErrQ (d.second.c 0) (a.H/(-s.y0)) s.MU.length ≤ (s.globalW:ℚ)/(S:ℚ)) &&
  decide (2*mpErrQ (d.first.c 0) ((max (-1-s.y0) (4+s.y0))/(-s.y0)) a.KA ≤ (s.globalA:ℚ)/(S:ℚ)) &&
  decide (a.qI=((qListIntegral (ownXList d)).reverse.map boxOfQ)) &&
  decide (a.qAI=((qListIntegral (atomXList d s.y0 a.sm a.KA)).reverse.map boxOfQ))

theorem listIn_sound (bs : List FBox) (qs : List ℚ) (h : listIn bs qs=true) :
    List.Forall₂ Contains bs (qs.map (fun q : ℚ => (q:ℝ))) := by
  simp only [listIn,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range] at h
  rw [List.forall₂_iff_get]
  refine ⟨by simp [h.1],fun i h1 h2 => ?_⟩
  have hi := h.2 i h1
  simp only [qIn,decide_eq_true_eq] at hi
  have hq : (qs.getD i 0)=qs[i]'(by rw [← h.1]; exact h1) := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem]; rfl
  have hb : (bs.getD i boxZero)=bs[i] := by rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h1]; rfl
  rw [hq,hb] at hi
  simpa using contains_ratCast _ _ hi

theorem widthIn_sound (mids : List ℤ) (w : ℤ) (qs : List ℚ) (h : widthIn mids w qs=true) :
    List.Forall₂ (fun a x => |x-dec S a| ≤ dec S w) mids (qs.map (fun q : ℚ => (q:ℝ))) := by
  simp only [widthIn,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,List.mem_range] at h
  rw [List.forall₂_iff_get]
  refine ⟨by simp [h.1],fun i h1 h2 => ?_⟩
  have hi := h.2 i h1
  have hq : (qs.getD i 0)=qs[i]'(by rw [← h.1]; exact h1) := by
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem]; rfl
  have hb : (mids.getD i 0)=mids[i] := by rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h1]; rfl
  rw [hq,hb] at hi
  simp only [List.get_eq_getElem,List.getElem_map,dec_eq_ratCast]
  exact_mod_cast hi

/-- The true values the source boxes enclose. -/
def simpleR (z : ℚ) (d : LatticeInput) (s : SourceF) (a : SimpleAux) : SourceR where
  M1 := (d.first.c 0:ℝ)
  M2 := (d.second.c 0:ℝ)
  L := Real.log |(z:ℝ)|
  U1c := (d.first.c 0:ℝ)*Real.log (4/(d.Y:ℝ))
  U2c := (d.second.c 0:ℝ)*Real.log (4/3)
  U1y0 := U d.first.measure ((s.y0:ℝ):ℂ)
  q1 := ((q1Q d).map (fun q : ℚ => (q:ℝ))).reverse
  qA := ((atomXList d s.y0 a.sm a.KA).map (fun q : ℚ => (q:ℝ))).reverse
  fk := (fkQ d).map (fun q : ℚ => (q:ℝ))
  w := fun k => (wQ d s.y0 k:ℝ)

/-- The parts of a passed source check, as propositions. -/
theorem simpleSourceCheck_parts (z : ℚ) (d : LatticeInput) (s : SourceF) (logs : List LogEntry)
    (a : SimpleAux) (h : simpleSourceCheck z d s logs a=true) :
    (s.z=z ∧ s.Y=d.Y ∧ 1 < s.phi ∧ s.y0=d.first.mid.1-d.first.half.1*((s.phi+s.phi⁻¹)/2) ∧
      s.y0 < 0 ∧ 0 ≤ a.H ∧ a.H < -s.y0 ∧ |(-4:ℚ)-s.y0| ≤ a.H ∧ |(-1:ℚ)-s.y0| ≤ a.H ∧ 0 < s.MU.length ∧
      d.second.mid=(-5/2,0) ∧ d.second.half=(3/2,0) ∧ 0 < d.first.half.1 ∧
      a.sm.length=a.KA+1 ∧ 4+s.y0 < -s.y0) ∧
    logs.all logEntryOK=true ∧ logEntryOK ⟨|z|,s.L⟩=true ∧
    logEntryOK ⟨4/d.Y,a.lU1c⟩=true ∧ boxIn (boxMulF (boxOfQ (d.first.c 0)) a.lU1c) s.U1c=true ∧
    logEntryOK ⟨4/3,a.lU2c⟩=true ∧ boxIn (boxMulF (boxOfQ (d.second.c 0)) a.lU2c) s.U2c=true ∧
    qIn s.m1 (d.first.c 0)=true ∧ qIn s.m2 (d.second.c 0)=true ∧
    scalarLowerCheck ((s.U1y0.1:ℚ)/(S:ℚ)) (u1y0Expr a d s.phi)=true ∧
    scalarUpperCheck (u1y0Expr a d s.phi) ((s.U1y0.2:ℚ)/(S:ℚ))=true ∧
    widthIn s.P1mid s.P1width (q1Q d).reverse=true ∧
    widthIn s.PAmid s.PAwidth (atomXList d s.y0 a.sm a.KA).reverse=true ∧
    listIn s.MU ((List.range s.MU.length).map (wQ d s.y0))=true ∧
    (∀ k < s.MU.length, |wQ d s.y0 k| ≤ |d.second.c 0| * (max |s.y0+4| |-1-s.y0|)^(k+1)/((k:ℚ)+1)) ∧
    listIn s.firstOverK (fkQ d)=true ∧
    stieltjesMomentFast d.first s.phi a.KA a.sm=true ∧
    2*mpErrQ (d.second.c 0) (a.H/(-s.y0)) s.MU.length ≤ (s.globalW:ℚ)/(S:ℚ) ∧
    2*mpErrQ (d.first.c 0) ((max (-1-s.y0) (4+s.y0))/(-s.y0)) a.KA ≤ (s.globalA:ℚ)/(S:ℚ) ∧
    a.qI=((qListIntegral (ownXList d)).reverse.map boxOfQ) ∧
    a.qAI=((qListIntegral (atomXList d s.y0 a.sm a.KA)).reverse.map boxOfQ) := by
  simp only [simpleSourceCheck,Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩,h7⟩,h8⟩,h9⟩,h10⟩,h11⟩,h12⟩,h13⟩,h14⟩,h15⟩,h16⟩,
    h17⟩,h18⟩,h19⟩,h20⟩,h21⟩ := h
  refine ⟨of_decide_eq_true h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,?_,h16,h17,
    of_decide_eq_true h18,of_decide_eq_true h19,of_decide_eq_true h20,of_decide_eq_true h21⟩
  intro k hk
  exact of_decide_eq_true (List.all_eq_true.mp h15 k (List.mem_range.mpr hk))

/-- The moment data a passed source check fixes. -/
def simpleMoments (z : ℚ) (d : LatticeInput) (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (hsh : latticeShapeCheck d=true) (s : SourceF) (logs : List LogEntry) (a : SimpleAux)
    (hc : simpleSourceCheck z d s logs a=true) :
    LatticeMomentData d.first.measure d.second.measure (d.Y:ℝ) :=
  have P := (simpleSourceCheck_parts z d s logs a hc).1
  latticeMomentsOf d dw hd hsh s.y0 a.H P.2.2.2.2.1 P.2.2.2.2.2.1 P.2.2.2.2.2.2.1 P.2.2.2.2.2.2.2.1
    P.2.2.2.2.2.2.2.2.1

theorem mpErr_cast (m v : ℚ) (K : ℕ) : mpErr (m:ℝ) (v:ℝ) K=((mpErrQ m v K:ℚ):ℝ) := by
  unfold mpErr mpErrQ; push_cast; ring

theorem simpleEnc (z : ℚ) (d : LatticeInput) (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (hsh : latticeShapeCheck d=true) (s : SourceF) (logs : List LogEntry) (a : SimpleAux)
    (hc : simpleSourceCheck z d s logs a=true) : SourceEnc s (simpleR z d s a) := by
  obtain ⟨P,-,hL,hl1,hb1,hl2,hb2,hm1,hm2,hlo,hhi,hP1,hPA,hMU,hwb,hfk,-,-,-,-,-⟩ :=
    simpleSourceCheck_parts z d s logs a hc
  have hsh' := latticeShapeCheck_parts d hsh
  have hpos1 := (datum_source_data d.data dw hd d.first (lattice_first_mem d)).2.2
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp only [qIn,decide_eq_true_eq] at hm1; exact contains_ratCast _ _ hm1
  · simp only [qIn,decide_eq_true_eq] at hm2; exact contains_ratCast _ _ hm2
  · have := logEntryOK_sound _ hL; simpa [simpleR] using this
  · have := boxMulF_sound _ _ _ _ (boxOfQ_sound (d.first.c 0)) (logEntryOK_sound _ hl1)
    simp only [boxIn,decide_eq_true_eq] at hb1
    have h' := contains_mono _ _ _ this hb1.1 hb1.2
    simpa [simpleR] using h'
  · have := boxMulF_sound _ _ _ _ (boxOfQ_sound (d.second.c 0)) (logEntryOK_sound _ hl2)
    simp only [boxIn,decide_eq_true_eq] at hb2
    have h' := contains_mono _ _ _ this hb2.1 hb2.2
    simpa [simpleR] using h'
  · have hv := stieltjes_seed_value a.terms d.first s.phi P.2.2.1 P.2.2.2.2.2.2.2.2.2.2.2.2.1
      (by rw [hsh'.2.1]) (by rw [hsh'.2.2.1]) hpos1
    rw [← P.2.2.2.1] at hv
    have h1 := scalarLowerCheck_sound _ _ hlo
    have h2 := scalarUpperCheck_sound _ _ hhi
    unfold u1y0Expr at h1 h2
    rw [hv] at h1 h2
    constructor
    · rw [dec_eq_ratCast]; exact h1
    · rw [dec_eq_ratCast]; exact h2
  · have := widthIn_sound _ _ _ hP1; simpa [simpleR,List.map_reverse] using this
  · have := widthIn_sound _ _ _ hPA; simpa [simpleR,List.map_reverse] using this
  · have := listIn_sound _ _ hMU; simpa [simpleR,List.map_map] using this
  · intro k hk
    have := hwb k hk
    simp only [simpleR]
    have hc : ((|wQ d s.y0 k|:ℚ):ℝ) ≤ ((|d.second.c 0| * (max |s.y0+4| |-1-s.y0|)^(k+1)/((k:ℚ)+1):ℚ):ℝ) := by
      exact_mod_cast this
    push_cast at hc ⊢
    exact hc
  · exact listIn_sound _ _ hfk


theorem wQ_moment (d : LatticeInput) (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (hsh : latticeShapeCheck d=true) (y0 : ℚ) (k : ℕ) :
    (wQ d y0 k:ℝ)=(moment d.second.measure ((y0:ℝ):ℂ) (k+1)).re/((k+1:ℕ):ℝ) := by
  have hsh' := latticeShapeCheck_parts d hsh
  have hs := datum_source_data d.data dw hd d.second (lattice_second_mem d)
  have hm := segment_real_moment d.second y0 (k+1) hs.2.1 hsh'.2.2.2.1 hsh'.2.2.2.2.1 hs.2.2
  rw [show ((y0:ℝ):ℂ)=(y0:ℂ) by push_cast; rfl,hm,wQ,arcList_eq,realMomentList_spec]
  push_cast; ring

theorem simpleWLink (z : ℚ) (d : LatticeInput) (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (hsh : latticeShapeCheck d=true) (s : SourceF) (logs : List LogEntry) (a : SimpleAux)
    (hc : simpleSourceCheck z d s logs a=true) :
    haveI := positive_source_finite d.second (datum_source_data d.data dw hd d.second (lattice_second_mem d)).2.2
    WLink s logs (simpleR z d s a) (z:ℝ) (s.theta:ℝ) (d.Y:ℝ) d.first.measure d.second.measure
      (simpleMoments z d dw hd hsh s logs a hc) s.MU.length := by
  have hall := simpleSourceCheck_parts z d s logs a hc
  obtain ⟨P,hlogs,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,hgW,-,-,-⟩ := hall
  have hsh' := latticeShapeCheck_parts d hsh
  have hpos2 := (datum_source_data d.data dw hd d.second (lattice_second_mem d)).2.2
  haveI := positive_source_finite d.second hpos2
  have hmass := positive_source_mass d.second hpos2
  refine ⟨logsOK_of_entries logs hlogs,simpleEnc z d dw hd hsh s logs a hc,
    by exact_mod_cast hsh'.1,rfl,rfl,rfl,by rw [P.2.1],?_,rfl,?_,rfl,?_,?_⟩
  · simp [simpleR,hmass]
  · intro x
    exact hq1_of_exact d dw hd hsh s.y0 a.H P.2.2.2.2.1 P.2.2.2.2.2.1 P.2.2.2.2.2.2.1 P.2.2.2.2.2.2.2.1
      P.2.2.2.2.2.2.2.2.1 x
  · intro k
    exact wQ_moment d dw hd hsh s.y0 k
  · simp only [simpleMoments,latticeMomentsOf,hmass]
    rw [show ((a.H:ℝ)/(-(s.y0:ℝ)))=((a.H/(-s.y0):ℚ):ℝ) by push_cast; ring,mpErr_cast,dec_eq_ratCast]
    exact_mod_cast hgW


def rrQ (s : SourceF) : ℚ := max (-1-s.y0) (4+s.y0)
def f2R (d : LatticeInput) (x : ℝ) : ℝ := (ownPlusR d.second).eval (5/3-2/3*x)

theorem simpleALink (z : ℚ) (d : LatticeInput) (dw : DensityWitness) (hd : datumCheck d.data dw=true)
    (hsh : latticeShapeCheck d=true) (s : SourceF) (logs : List LogEntry) (a : SimpleAux)
    (hc : simpleSourceCheck z d s logs a=true) :
    haveI := positive_source_finite d.first (datum_source_data d.data dw hd d.first (lattice_first_mem d)).2.2
    ALink s logs (simpleR z d s a) (z:ℝ) (s.rho:ℝ) (s.theta:ℝ) (d.Y:ℝ) d.first.measure d.second.measure
      (s.y0:ℝ) (rrQ s:ℝ) a.KA (f2R d) := by
  have hall := simpleSourceCheck_parts z d s logs a hc
  obtain ⟨P,hlogs,-,-,-,-,-,-,-,-,-,-,-,-,-,-,hst,-,hgA,-,-⟩ := hall
  have hsh' := latticeShapeCheck_parts d hsh
  have hpos1 := (datum_source_data d.data dw hd d.first (lattice_first_mem d)).2.2
  have hpos2 := (datum_source_data d.data dw hd d.second (lattice_second_mem d)).2.2
  haveI := positive_source_finite d.first hpos1
  have hmass := positive_source_mass d.first hpos1
  have hy : (s.y0:ℝ) < 0 := by exact_mod_cast P.2.2.2.2.1
  have h15 : (4:ℝ)+(s.y0:ℝ) < -(s.y0:ℝ) := by exact_mod_cast P.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hrr : (rrQ s:ℝ)=max (-1-(s.y0:ℝ)) (4+(s.y0:ℝ)) := by unfold rrQ; push_cast; rfl
  have hfm := (simpleMoments z d dw hd hsh s logs a hc).first_measure
  have hst' := stieltjesMomentCheck_sound d.first s.phi a.KA a.sm hpos1 (by rw [← stieltjesMomentFast_eq]; exact hst)
  rw [← P.2.2.2.1] at hst'
  refine ⟨logsOK_of_entries logs hlogs,simpleEnc z d dw hd hsh s logs a hc,
    by exact_mod_cast (hsh'.1).le,lattice_first_support d hsh,hy,?_,?_,rfl,by simp [simpleR],rfl,?_,?_,?_,?_,?_⟩
  · rw [hrr]; exact max_lt (by linarith) h15
  · rw [hrr]; exact ⟨le_max_left _ _,le_max_right _ _⟩
  · intro x hx
    rw [hfm]
    exact seg_first_integrable_left (by exact_mod_cast hsh'.1) (simpleMoments z d dw hd hsh s logs a hc).nonneg
      (by linarith [hx.1])
  · intro x hx
    exact (second_U_inside d.second P.2.2.2.2.2.2.2.2.2.2.1 P.2.2.2.2.2.2.2.2.2.2.2.1 hpos2 x hx).1
  · intro x hx
    rw [(second_U_inside d.second P.2.2.2.2.2.2.2.2.2.2.1 P.2.2.2.2.2.2.2.2.2.2.2.1 hpos2 x hx).2]
    simp [simpleR,f2R]
  · intro x hx
    simp only [simpleR]
    rw [atomXList_eval]
    unfold f2R
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : k ≤ a.KA := by have := Finset.mem_range.mp hk; omega
    by_cases h0 : k=0
    · subst h0; simp
    · rw [if_neg h0,hst'.2 k hk']
      have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast h0
      field_simp
      ring
  · rw [hmass,hrr]
    rw [show (max (-1-(s.y0:ℝ)) (4+(s.y0:ℝ)))/(-(s.y0:ℝ))=((max (-1-s.y0) (4+s.y0)/(-s.y0):ℚ):ℝ) by
      push_cast; ring,mpErr_cast,dec_eq_ratCast]
    exact_mod_cast hgA



end
end CatalanCore.Li2.DecayCert.Simple
