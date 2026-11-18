module
public import CatalanCore.Li2.DecayCert.Compile
public import CatalanCore.Li2.DecayCert.Lattice.Stieltjes
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Moments
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open MeasureTheory Set Polynomial
open scoped BigOperators
open CatalanCore.Li2.Decay CatalanCore.Tools.Joukowski
namespace CatalanCore.Li2.DecayCert.LatticeGate

theorem segConstant_at_jJ (terms : ℕ) (d : QSegment) (phi : CQ)
    (hh : cqReal d.half≠0) (hphi : 1<‖cqReal phi‖)
    (hpos : ∀ x∈Icc (-1:ℝ) 1,0≤CatalanCore.Zeta5.Potential.chebF
      (fun j : ℕ => (d.c j:ℝ)) (d.coeff.length-1) x) :
    P d.measure (cqReal d.mid+cqReal d.half*jJ (cqReal phi))=(segConstant terms d phi).value := by
  have harg : (cqReal d.mid+cqReal d.half*jJ (cqReal phi)-cqReal d.mid)/cqReal d.half=
      jJ (cqReal phi) := by field_simp <;> ring
  have h := segPot_closed (d.toSegment hh) hpos
    (cqReal d.mid+cqReal d.half*jJ (cqReal phi))
    (by simpa only [QSegment.toSegment,harg] using one_lt_jc_jJ hphi)
  have hpn : cqReal phi≠0 := by intro hz;rw [hz,norm_zero] at hphi;norm_num at hphi
  rw [segConstant_value terms d phi hpn]
  simpa only [QSegment.toSegment,SegmentData.ν,QSegment.measure,harg,Gfun,jphi_jJ hphi,Complex.ofReal_ratCast] using h

theorem stieltjes_seed_value (terms : ℕ) (d : QSegment) (phi : ℚ)
    (hphi : 1<phi) (hhalf : 0<d.half.1) (hmidim : d.mid.2=0) (hhalfim : d.half.2=0)
    (hpos : ∀ x∈Icc (-1:ℝ) 1,0≤CatalanCore.Zeta5.Potential.chebF
      (fun j : ℕ => (d.c j:ℝ)) (d.coeff.length-1) x) :
    (seNeg (segConstant terms d (-phi,0))).value=
      U d.measure (((d.mid.1-d.half.1*((phi+phi⁻¹)/2):ℚ):ℝ):ℂ) := by
  have hphiR : (1:ℝ)<(phi:ℝ) := by exact_mod_cast hphi
  have hpn : 1<‖cqReal (-phi,0)‖ := by
    have he : cqReal (-phi,0)= -((phi:ℝ):ℂ) := by simp [cqReal]
    rw [he,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : (0:ℝ)<phi)]
    exact hphiR
  have hh : cqReal d.half≠0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp [cqReal] at he
    have hq : d.half.1=0 := he
    linarith
  have hpt : cqReal d.mid+cqReal d.half*jJ (cqReal (-phi,0))=
      (((d.mid.1-d.half.1*((phi+phi⁻¹)/2):ℚ):ℝ):ℂ) := by
    simp only [cqReal,hmidim,hhalfim,Rat.cast_zero,zero_mul,add_zero,jJ]
    push_cast
    simp only [inv_neg]
    ring
  have hs := segConstant_at_jJ terms d (-phi,0) hh hpn hpos
  rw [hpt] at hs
  rw [seNeg_value,← hs]
  rfl

#print axioms segConstant_at_jJ
#print axioms stieltjes_seed_value
def stieltjesErrorQ (mass y0 r : ℚ) (K : ℕ) : ℚ :=
  mass*(r/(-y0))^(K+1)/((K+1:ℕ)*(1-r/(-y0)))

def stieltjesModel (terms : ℕ) (d : QSegment) (phi : ℚ) (sm : List ℚ)
    (r : ℚ) (K : ℕ) : CompiledModel :=
  let y0 := d.mid.1-d.half.1*((phi+phi⁻¹)/2)
  ⟨(List.range (K+1)).map (fun j : ℕ=>
    if j=0 then seNeg (segConstant terms d (-phi,0)) else seRat (coeffQ sm j/(j:ℚ))),
    seRat (stieltjesErrorQ (d.c 0) y0 r K)⟩

noncomputable def stieltjesModelCheck (d : QSegment) (phi : ℚ) (sm : List ℚ)
    (Y r : ℚ) (K : ℕ) : Bool :=
  let y0 := d.mid.1-d.half.1*((phi+phi⁻¹)/2)
  realSupportCheck d 0 Y && stieltjesMomentCheck d phi K sm &&
    decide (0≤Y ∧ y0<0 ∧ 0≤r ∧ r< -y0)

theorem stieltjesModel_coeff (terms : ℕ) (d : QSegment) (phi : ℚ) (sm : List ℚ)
    (r : ℚ) (K : ℕ)
    (hphi : 1<phi) (hhalf : 0<d.half.1) (hmidim : d.mid.2=0) (hhalfim : d.half.2=0)
    (hpos : ∀ x∈Icc (-1:ℝ) 1,0≤CatalanCore.Zeta5.Potential.chebF
      (fun j : ℕ => (d.c j:ℝ)) (d.coeff.length-1) x)
    (hsm : ∀k≤K,inverseMoment d.measure
      (((d.mid.1-d.half.1*((phi+phi⁻¹)/2):ℚ):ℝ)) k=(coeffQ sm k:ℝ)) :
    (stieltjesModel terms d phi sm r K).coeff.map ScalarExpr.value=
      stieltjesCoeffs d.measure (((d.mid.1-d.half.1*((phi+phi⁻¹)/2):ℚ):ℝ)) K := by
  unfold stieltjesModel stieltjesCoeffs
  simp only [List.map_map]
  apply List.map_congr_left
  intro j hj
  by_cases hz : j=0
  · subst j
    simp only [Function.comp_def,ite_true]
    exact stieltjes_seed_value terms d phi hphi hhalf hmidim hhalfim hpos
  · simp only [Function.comp_def,hz,ite_false,seRat_value]
    rw [hsm j (by have := List.mem_range.mp hj;omega)]
    push_cast
    rfl

theorem stieltjesModel_error (terms : ℕ) (d : QSegment) (phi : ℚ) (sm : List ℚ)
    (r : ℚ) (K : ℕ) (hmass : d.measure.real univ=(d.c 0:ℝ)) :
    (stieltjesModel terms d phi sm r K).error.value=
      mpErr (d.measure.real univ)
        ((r:ℝ)/(-(((d.mid.1-d.half.1*((phi+phi⁻¹)/2):ℚ):ℝ)))) K := by
  simp only [stieltjesModel,seRat_value,stieltjesErrorQ,mpErr,hmass]
  push_cast
  rfl

theorem stieltjesModelCheck_sound (terms : ℕ) (d : QSegment) (phi : ℚ) (sm : List ℚ)
    (Y r : ℚ) (K : ℕ)
    (hpos : ∀ x∈Icc (-1:ℝ) 1,0≤CatalanCore.Zeta5.Potential.chebF
      (fun j : ℕ => (d.c j:ℝ)) (d.coeff.length-1) x)
    (hc : stieltjesModelCheck d phi sm Y r K=true) :
    let y0 := d.mid.1-d.half.1*((phi+phi⁻¹)/2)
    Models (fun u=>U d.measure (((y0:ℝ)+u:ℝ):ℂ))
      ((stieltjesModel terms d phi sm r K).coeff.map ScalarExpr.value)
      (r:ℝ) (stieltjesModel terms d phi sm r K).error.value := by
  let y0 := d.mid.1-d.half.1*((phi+phi⁻¹)/2)
  have hh : realSupportCheck d 0 Y=true ∧ stieltjesMomentCheck d phi K sm=true ∧
      (0≤Y ∧ y0<0 ∧ 0≤r ∧ r< -y0) := by
    simpa only [stieltjesModelCheck,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using hc
  rcases hh with ⟨hs,hmc,hY,hy,hr,hsep⟩
  have hg : 1<phi ∧ 0<d.half.1 ∧ sm.length=K+1 := by
    have hh := hmc
    simp only [stieltjesMomentCheck,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.1
  have hreal : d.mid.2=0 ∧ d.half.2=0 := by
    have hh := of_decide_eq_true hs
    exact ⟨hh.1,hh.2.1⟩
  have hsm := (stieltjesMomentCheck_sound d phi K sm hpos hmc).2
  haveI := positive_source_finite d hpos
  have hmass := positive_source_mass d hpos
  dsimp only
  rw [stieltjesModel_coeff terms d phi sm r K hg.1 hg.2.1 hreal.1 hreal.2 hpos hsm,
    stieltjesModel_error terms d phi sm r K hmass]
  apply logPot_stieltjes_model d.measure (y0:ℝ) (r:ℝ) (Y:ℝ)
    (by exact_mod_cast hy) (by exact_mod_cast hr) (by exact_mod_cast hY) (by exact_mod_cast hsep)
  simpa only [Rat.cast_zero] using realSupportCheck_sound d 0 Y hs

#print axioms stieltjesModel_coeff
#print axioms stieltjesModel_error
#print axioms stieltjesModelCheck_sound

end CatalanCore.Li2.DecayCert.LatticeGate
