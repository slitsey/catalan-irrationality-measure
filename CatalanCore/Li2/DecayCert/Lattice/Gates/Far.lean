module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Moments
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open MeasureTheory Set Polynomial
open scoped BigOperators
open CatalanCore.Li2.Decay
namespace CatalanCore.Li2.DecayCert.LatticeGate

def logCoeffSE (terms : ℕ) (d : ℚ) (j : ℕ) : SE :=
  logScalarCoeff (d,0) (1,0) terms j

theorem logCoeffSE_value (terms : ℕ) (d : ℚ) (_hd : 0<d) (j : ℕ) :
    (logCoeffSE terms d j).value=logAffineCoeff ((d:ℝ):ℂ) 1 j := by
  simpa only [logCoeffSE,cqReal,Rat.cast_zero,Rat.cast_one,zero_mul,add_zero,Complex.ofReal_ratCast] using
    logScalarCoeff_value (d,0) (1,0) terms j

def inverseTailQ (d r : ℚ) (k J : ℕ) : ℚ :=
  d^(-(k:ℤ))*((1-r/d)^(-(k:ℤ))-
    ∑ j ∈ Finset.range (J+1),((k+j-1).choose j:ℚ)*(r/d)^j)

theorem inverseTailQ_cast (d r : ℚ) (k J : ℕ) :
    (inverseTailQ d r k J:ℝ)=invPowerTail (d:ℝ) (r:ℝ) k J := by
  unfold inverseTailQ invPowerTail
  push_cast
  rfl

#print axioms logCoeffSE_value
#print axioms inverseTailQ_cast
def farErrorQ (mass : ℚ) (mu : List ℚ) (y0 H p r : ℚ) (K J : ℕ) : ℚ :=
  let d := p-y0
  mass*(r/d)^(J+1)/((J+1:ℕ)*(1-r/d))+
    (∑ k ∈ Finset.range K,|coeffQ mu (k+1)/((k+1:ℕ):ℚ)| *inverseTailQ d r (k+1) J)+
    mass*(H/(d-r))^(K+1)/((K+1:ℕ)*(1-H/(d-r)))

def farModel (terms : ℕ) (mass : ℚ) (mu : List ℚ) (y0 H p r : ℚ) (K J : ℕ) : CompiledModel :=
  let d := p-y0
  ⟨(List.range (J+1)).map (fun j : ℕ =>
    seAdd (seScale (-mass) (logCoeffSE terms d j))
      (seRat (∑ k ∈ Finset.range K, coeffQ mu (k+1)/((k+1:ℕ):ℚ)*
        ((-1:ℚ)^j*((k+1+j-1).choose j:ℚ)/d^(k+1+j))))),
    seRat (farErrorQ mass mu y0 H p r K J)⟩

noncomputable def farModelCheck (d : QSegment) (mu : List ℚ)
    (y0 L Y H p r : ℚ) (K : ℕ) : Bool :=
  realSupportCheck d L Y && ordinaryMomentCheck d y0 K mu &&
    decide (0≤H ∧ 0≤r ∧ H<p-y0-r ∧ |L-y0|≤H ∧ |Y-y0|≤H)

theorem real_support_ball (σ : Measure ℂ) (L Y y0 H : ℝ)
    (hs : σ {s | s.im≠0 ∨ s.re<L ∨ Y<s.re}=0)
    (hl : |L-y0|≤H) (hy : |Y-y0|≤H) :
    σ {s | s.im≠0 ∨ H<‖s-(y0:ℂ)‖}=0 := by
  apply measure_mono_null _ hs
  intro s hbad
  by_contra hnot
  have hh : s.im=0 ∧ L≤s.re ∧ s.re≤Y := by
    simpa only [mem_setOf_eq,not_or,not_not,not_lt] using hnot
  have he : s-(y0:ℂ)=((s.re-y0:ℝ):ℂ) := by
    apply Complex.ext <;> simp [hh.1]
  have hb : ‖s-(y0:ℂ)‖≤H := by
    rw [he,Complex.norm_real,Real.norm_eq_abs]
    apply abs_le.mpr
    have hll := (abs_le.mp hl).1
    have hyy := (abs_le.mp hy).2
    constructor <;> linarith [hh.2.1,hh.2.2]
  exact hbad.elim (fun h=>h hh.1) (fun h=>not_lt_of_ge hb h)

theorem farModel_coeff (terms : ℕ) (d : QSegment) (mu : List ℚ)
    (y0 H p r : ℚ) (K J : ℕ) (hd : 0<p-y0)
    (hmass : d.measure.real univ=(d.c 0:ℝ))
    (hmu : ∀ k≤K,moment d.measure (y0:ℂ) k=(coeffQ mu k:ℂ)) :
    (farModel terms (d.c 0) mu y0 H p r K J).coeff.map ScalarExpr.value=
      mpTaylorCoeffs d.measure (y0:ℝ) (p:ℝ) K J := by
  unfold farModel mpTaylorCoeffs
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [Function.comp_def,seAdd_value,seScale_value,seRat_value]
  rw [logCoeffSE_value terms (p-y0) hd j,hmass]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [hmu (k+1) (by have := Finset.mem_range.mp hk;omega)]
  simp

theorem farModel_error (terms : ℕ) (d : QSegment) (mu : List ℚ)
    (y0 H p r : ℚ) (K J : ℕ)
    (hmass : d.measure.real univ=(d.c 0:ℝ))
    (hmu : ∀ k≤K,moment d.measure (y0:ℂ) k=(coeffQ mu k:ℂ)) :
    (farModel terms (d.c 0) mu y0 H p r K J).error.value=
      mpTaylorError d.measure (y0:ℝ) (H:ℝ) (p:ℝ) (r:ℝ) K J := by
  simp only [farModel,seRat,ScalarExpr.value,farErrorQ,mpTaylorError,mpErr,hmass]
  have hsum : (∑ k ∈ Finset.range K,
      |(moment d.measure ((y0:ℝ):ℂ) (k+1)).re/((k+1:ℕ):ℝ)| *
        invPowerTail ((p:ℝ)-(y0:ℝ)) (r:ℝ) (k+1) J)=
      ∑ k ∈ Finset.range K,|(coeffQ mu (k+1):ℝ)/((k+1:ℕ):ℝ)| *
        invPowerTail ((p:ℝ)-(y0:ℝ)) (r:ℝ) (k+1) J := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Complex.ofReal_ratCast,hmu (k+1) (by have := Finset.mem_range.mp hk;omega)]
    simp
  rw [hsum]
  push_cast
  simp only [inverseTailQ_cast,Rat.cast_sub]

#print axioms farModel_coeff
#print axioms farModel_error

theorem farModelCheck_sound (terms : ℕ) (d : QSegment) (mu : List ℚ)
    (y0 L Y H p r : ℚ) (K J : ℕ)
    (hpos : ∀ x∈Icc (-1:ℝ) 1,0≤CatalanCore.Zeta5.Potential.chebF
      (fun j : ℕ => (d.c j:ℝ)) (d.coeff.length-1) x)
    (hc : farModelCheck d mu y0 L Y H p r K=true) :
    Models (fun u=>U d.measure (((p:ℝ)+u:ℝ):ℂ))
      ((farModel terms (d.c 0) mu y0 H p r K J).coeff.map ScalarExpr.value)
      (r:ℝ) (farModel terms (d.c 0) mu y0 H p r K J).error.value := by
  have hh : realSupportCheck d L Y=true ∧ ordinaryMomentCheck d y0 K mu=true ∧
      (0≤H ∧ 0≤r ∧ H<p-y0-r ∧ |L-y0|≤H ∧ |Y-y0|≤H) := by
    simpa only [farModelCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc
  rcases hh with ⟨hs,hmc,hH,hr,hsep,hL,hY⟩
  haveI := positive_source_finite d hpos
  have hsupport := realSupportCheck_sound d L Y hs
  have hball := real_support_ball d.measure (L:ℝ) (Y:ℝ) (y0:ℝ) (H:ℝ) hsupport
    (by exact_mod_cast hL) (by exact_mod_cast hY)
  have hmu := (ordinaryMomentCheck_sound d y0 K mu hpos hmc).2
  have hmass := positive_source_mass d hpos
  rw [farModel_coeff terms d mu y0 H p r K J (by linarith) hmass hmu,
    farModel_error terms d mu y0 H p r K J hmass hmu]
  exact logPot_far_macro_model d.measure (y0:ℝ) (H:ℝ) (p:ℝ) (r:ℝ)
    (by exact_mod_cast hH) (by exact_mod_cast hr) hball (by exact_mod_cast hsep) K J

#print axioms farModelCheck_sound

end CatalanCore.Li2.DecayCert.LatticeGate
