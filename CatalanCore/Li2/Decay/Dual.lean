module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import CatalanCore.Tools.CappedDual
public import CatalanCore.Li2.Decay.Fields
public import CatalanCore.Li2.Decay.Caps
public import CatalanCore.Tools.HolderConfigurations
public import CatalanCore.Li2.Uniform.Datum
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal
namespace CatalanCore.Li2.Decay
open CatalanCore.Tools.Jets
noncomputable def circleConfiguration (n : ℕ) (x : Fin (2*n) → ℂ) (ε : ℝ) : Measure ℂ :=
  ENNReal.ofReal ((n:ℝ)⁻¹) • ∑ i, CatalanCore.Decay.ComplexEnergy.circZ (x i) ε

theorem confluent_circle_bound (n : ℕ) (hn : 0 < n) (c : ConfluentConfig (2*n))
    (ε : ℝ) (hε : 0 < ε) :
    c.redLog ≤ -(n:ℝ)^2 * I (circleConfiguration n c.x ε) -
      (2*n:ℝ)*Real.log ε+c.pairCount*(Real.log 2-2*Real.log ε) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hI (μ : Measure ℂ) : I μ= -CatalanCore.Decay.ComplexEnergy.energyC μ := by
    unfold I U P CatalanCore.Decay.ComplexEnergy.energyC CatalanCore.Decay.ComplexEnergy.potC
    rw [integral_neg]
  have he : -(n:ℝ)^2*I (circleConfiguration n c.x ε)=
      CatalanCore.Decay.ComplexEnergy.energyC (∑ i, CatalanCore.Decay.ComplexEnergy.circZ (c.x i) ε) := by
    rw [hI,circleConfiguration,CatalanCore.Tools.CappedDual.energyC_smul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hnR.le)]
    field_simp
    <;> ring
  rw [he]
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using
    CatalanCore.Tools.CappedDual.confluent_circle_sum_bound c ε hε

theorem neutral_dual_bound (μ σ : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure σ]
    (hmass : μ.real univ=σ.real univ) (R : ℝ)
    (hμ : ∀ᵐ s ∂μ, ‖s‖ ≤ R) (hσ : ∀ᵐ s ∂σ, ‖s‖ ≤ R)
    (hlog : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) ((μ+σ).prod (μ+σ)))
    (hae : ∀ᵐ p ∂((μ+σ).prod (μ+σ)), p.1 ≠ p.2) :
    -I μ ≤ I σ-2*∫ s, U σ s ∂μ := by
  rw [Measure.add_prod,Measure.prod_add,Measure.prod_add] at hlog hae
  obtain ⟨hlog0,hlog1⟩ := integrable_add_measure.mp hlog
  obtain ⟨h00,h01⟩ := integrable_add_measure.mp hlog0
  obtain ⟨h10,h11⟩ := integrable_add_measure.mp hlog1
  simp only [ae_add_measure_iff] at hae
  let m : Bool → Measure ℂ := fun b => bif b then μ else σ
  haveI : ∀ b, IsFiniteMeasure (m b) := fun b => by
    cases b
    · simpa only [m,Bool.cond_false] using (inferInstance : IsFiniteMeasure σ)
    · simpa only [m,Bool.cond_true] using (inferInstance : IsFiniteMeasure μ)
  have key := CatalanCore.Tools.neutral_log_energy_nonneg (ι := Bool) (m := m)
    (s := fun b => bif b then 1 else -1) (R := R)
    (fun b => by cases b <;> simp only [m] <;> assumption)
    (by simp [Fintype.sum_bool,m,hmass])
    (fun b c => by cases b <;> cases c <;> simp only [m] <;> assumption)
    (fun b c => by cases b <;> cases c <;> simp only [m] <;> first | exact hae.1.1 | exact hae.1.2 | exact hae.2.1 | exact hae.2.2)
  simp only [CatalanCore.Zeta5.Energy.energy,CatalanCore.Zeta5.Energy.pairInt,
    Fintype.sum_bool,m,Bool.cond_true,Bool.cond_false] at key
  have ei (ν : Measure ℂ) [IsFiniteMeasure ν]
      (hi : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) (ν.prod ν)) :
      I ν = -(∫ p : ℂ × ℂ, Real.log ‖p.1-p.2‖ ∂(ν.prod ν)) := by
    rw [integral_prod _ hi]
    unfold I U P
    rw [integral_neg]
  have ec : (∫ s, U σ s ∂μ) = -(∫ p : ℂ × ℂ, Real.log ‖p.1-p.2‖ ∂(μ.prod σ)) := by
    rw [integral_prod _ h01]
    unfold U P
    rw [integral_neg]
  have esym : (∫ p : ℂ × ℂ, Real.log ‖p.1-p.2‖ ∂(σ.prod μ)) =
      (∫ p : ℂ × ℂ, Real.log ‖p.1-p.2‖ ∂(μ.prod σ)) := by
    have hh := integral_prod_swap (μ := μ) (ν := σ) (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖)
    simpa only [Prod.fst_swap,Prod.snd_swap,norm_sub_rev] using hh
  rw [ei μ h00,ei σ h11,ec]
  linarith

open CatalanCore.Decay.ComplexEnergy
open CatalanCore.Zeta5.Energy
theorem holder_configuration_bound (n : ℕ) (hn : 0 < n)
    (c : ConfluentConfig (2*n)) (d : DualDatum) :
    c.redLog ≤ (n:ℝ)^2*I d.σ-2*n*(∑ i, U d.σ (c.x i))+
      (2*n:ℝ)*Real.log ((n:ℝ)^2)+
      c.pairCount*(Real.log 2+2*Real.log ((n:ℝ)^2))+
      4*(d.holderConstant:ℝ)*(n:ℝ)^(2-2*d.holderExponent) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  let ε := ((n:ℝ)^2)⁻¹
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hholder : ∀ u v : ℂ, |potC d.σ u-potC d.σ v| ≤
      (d.holderConstant:ℝ)*‖u-v‖^d.holderExponent := by
    intro u v
    have h := d.holder u v
    simp only [CatalanCore.Li2.Uniform.pot,integral_neg] at h
    change |(-potC d.σ u)-(-potC d.σ v)| ≤ _ at h
    rwa [show -potC d.σ u - -potC d.σ v= -(potC d.σ u-potC d.σ v) by ring,abs_neg] at h
  have hh := CatalanCore.Tools.HolderConfigurations.holder_circle_bound (n:ℝ) hnR c d.σ
    d.radius (d.holderConstant:ℝ) d.holderExponent d.radius_nonneg d.bounded d.selfIntegrable
    (CatalanCore.Li2.Uniform.datum_atomless d) hholder
    (by rw [d.mass]; push_cast; ring) ε hε
  have hlog : Real.log ε= -Real.log ((n:ℝ)^2) := Real.log_inv _
  have hpow : (n:ℝ)^2*ε^d.holderExponent=(n:ℝ)^(2-2*d.holderExponent) := by
    have he2 : (n:ℝ)^2=Real.exp (2*Real.log (n:ℝ)) := by
      rw [show (2:ℝ)=(2:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hnR]
    rw [Real.rpow_def_of_pos hε,Real.rpow_def_of_pos hnR,hlog,Real.log_pow,he2,← Real.exp_add]
    congr 1
    ring
  have herr : 4*(d.holderConstant:ℝ)*(n:ℝ)^2*ε^d.holderExponent=
      4*(d.holderConstant:ℝ)*(n:ℝ)^(2-2*d.holderExponent) := by rw [mul_assoc,hpow]
  have hI : I d.σ= -energyC d.σ := by unfold I U P energyC potC; rw [integral_neg]
  have hU : (∑ i, U d.σ (c.x i))= -(∑ i, potC d.σ (c.x i)) := by
    change (∑ i, -potC d.σ (c.x i))= _
    rw [Finset.sum_neg_distrib]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at hh
  rw [hlog] at hh
  rw [hI,hU]
  nlinarith
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.confluent_circle_bound
#print axioms CatalanCore.Li2.Decay.neutral_dual_bound
#print axioms CatalanCore.Li2.Decay.holder_configuration_bound
namespace CatalanCore.Li2.Decay
private theorem Dprod_hasDerivAt (m : ℕ) (u : ℂ)
    (hu : ∀ i ∈ Finset.Icc 1 m, u+(i:ℂ) ≠ 0) :
    HasDerivAt (Dprod m) (Dprod m u*(∑ i ∈ Finset.Icc 1 m, (u+(i:ℂ))⁻¹)) u := by
  have hi : ∀ i ∈ Finset.Icc 1 m, HasDerivAt (fun w : ℂ => w+(i:ℂ)) 1 u :=
    fun i _ => (hasDerivAt_id u).add_const (i:ℂ)
  have hd := HasDerivAt.fun_finsetProd hi
  simp only [smul_eq_mul,mul_one] at hd
  have he : (∑ i ∈ Finset.Icc 1 m, ∏ j ∈ (Finset.Icc 1 m).erase i, (u+(j:ℂ)))=
      Dprod m u*(∑ i ∈ Finset.Icc 1 m, (u+(i:ℂ))⁻¹) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hp : (∏ j ∈ (Finset.Icc 1 m).erase i, (u+(j:ℂ)))=Dprod m u/(u+(i:ℂ)) :=
      (eq_div_iff (hu i hi)).mpr (Finset.prod_erase_mul (Finset.Icc 1 m) (fun j => u+(j:ℂ)) hi)
    rw [hp,div_eq_mul_inv]
  rw [he] at hd
  change HasDerivAt (fun w : ℂ => ∏ i ∈ Finset.Icc 1 m, (w+(i:ℂ))) _ u
  exact hd

private theorem weight_hasDerivAt (n : ℕ) (u : ℂ)
    (hu : ∀ i ∈ Finset.Icc 1 (4*n), u+(i:ℂ) ≠ 0) :
    HasDerivAt (weight n) (weight n u*(3*(∑ i ∈ Finset.Icc 1 n, (u+(i:ℂ))⁻¹)-
      (∑ i ∈ Finset.Icc 1 (4*n), (u+(i:ℂ))⁻¹))) u := by
  have hnum : ∀ i ∈ Finset.Icc 1 n, u+(i:ℂ) ≠ 0 := by
    intro i hi
    apply hu i
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hi).1,by have hh := (Finset.mem_Icc.mp hi).2; omega⟩
  have hden : Dprod (4*n) u ≠ 0 := Finset.prod_ne_zero_iff.mpr hu
  have hd := ((Dprod_hasDerivAt n u hnum).pow 3).div (Dprod_hasDerivAt (4*n) u hu) hden
  convert hd using 1
  · rfl
  · simp only [weight,Pi.pow_apply,Pi.div_apply]
    norm_num only [Nat.reduceSub,Nat.cast_ofNat]
    field_simp
    <;> ring

private theorem lattice_reciprocal_sum (x m : ℕ) (hx : 1 ≤ x) :
    ‖∑ i ∈ Finset.Icc 1 m, ((x:ℂ)+(i:ℂ))⁻¹‖ ≤ (m:ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.Icc 1 m, ‖((x:ℂ)+(i:ℂ))⁻¹‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.Icc 1 m, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_inv,← Nat.cast_add,Complex.norm_natCast]
      apply inv_le_one_of_one_le₀
      exact_mod_cast (show 1 ≤ x+i by omega)
    _ = _ := by simp

private theorem latticeA_le_B (z : ℝ) (n x : ℕ) (hx : 1 ≤ x) :
    ‖latticeA z n x‖ ≤ (1+7*(n:ℝ))*‖latticeB z n x‖ := by
  have hxC : (x:ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by omega)
  have hpoles : ∀ i ∈ Finset.Icc 1 (4*n), (x:ℂ)+(i:ℂ) ≠ 0 := by
    intro i hi
    rw [← Nat.cast_add]
    exact_mod_cast (show x+i ≠ 0 by omega)
  let A := ∑ i ∈ Finset.Icc 1 n, ((x:ℂ)+(i:ℂ))⁻¹
  let B := ∑ i ∈ Finset.Icc 1 (4*n), ((x:ℂ)+(i:ℂ))⁻¹
  let Q := (x:ℂ)⁻¹+3*A-B
  have hA : ‖A‖ ≤ (n:ℝ) := lattice_reciprocal_sum x n hx
  have hB : ‖B‖ ≤ 4*(n:ℝ) := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using lattice_reciprocal_sum x (4*n) hx
  have hinv : ‖(x:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv,Complex.norm_natCast]
    apply inv_le_one_of_one_le₀
    exact_mod_cast hx
  have hQ : ‖Q‖ ≤ 1+7*(n:ℝ) := by
    have h1 := norm_sub_le ((x:ℂ)⁻¹+3*A) B
    have h2 := norm_add_le (x:ℂ)⁻¹ (3*A)
    have h3 : ‖(3:ℂ)*A‖=3*‖A‖ := by rw [norm_mul]; norm_num
    dsimp only [Q]
    rw [h3] at h2
    linarith
  have hd := (hasDerivAt_id (x:ℂ)).mul (weight_hasDerivAt n (x:ℂ) hpoles)
  have hderiv : deriv (fun u : ℂ => u*weight n u) (x:ℂ)=(x:ℂ)*weight n x*Q := by
    have hfun : (fun u : ℂ => u*weight n u)=id*weight n := rfl
    rw [hfun,hd.deriv]
    simp only [id_eq,one_mul]
    dsimp only [Q,A,B]
    field_simp
    <;> ring
  simp only [latticeA,latticeB,hderiv,norm_mul]
  calc
    _ ≤ ‖(z:ℂ)^x‖*(‖(x:ℂ)‖*‖weight n x‖*(1+7*(n:ℝ))) := by gcongr
    _ = _ := by ring
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.latticeA_le_B


namespace CatalanCore.Li2.Decay
open CatalanCore.Tools.Jets

theorem admissible_lattice_gap (F : Frame) (g : CatalanCore.Li2.Uniform.FrameGeometry F)
    (z : ℝ) (n : ℕ) (hn : 0 < n)
    (hdom : ∀ u ∈ CatalanCore.Li2.Uniform.gammaN g n,
      0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧ ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|))
    (c : AdmissibleConfig F g z n) (i j : Fin (2*n)) (hij : i ≠ j)
    (hJ : i ∈ c.Jlat ∨ j ∈ c.Jlat) (hnp : ¬c.confluence.paired i j) :
    (1/2:ℝ) ≤ ‖(c.particle i).point-(c.particle j).point‖ := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have aux : ∀ i j : Fin (2*n), i ≠ j → i ∈ c.Jlat → ¬c.confluence.paired i j →
      (1/2:ℝ) ≤ ‖(c.particle i).point-(c.particle j).point‖ := by
    intro i j hij hiJ hnp
    simp only [AdmissibleConfig.Jlat,Finset.mem_filter,Finset.mem_univ,true_and] at hiJ
    cases hei : c.particle i with
    | contour u => simp only [hei,isLattice,Bool.false_eq_true] at hiJ
    | ray x => simp only [hei,isLattice,Bool.false_eq_true] at hiJ
    | atom k => simp only [hei,isLattice,Bool.false_eq_true] at hiJ
    | lattice x =>
      have hx := (c.lattice_sites i x hei).1
      cases hej : c.particle j with
      | lattice y =>
        have hxy : x ≠ y := by
          intro hxy
          apply hnp
          apply (c.confluence.diagonal i j hij).mp
          rw [c.positions i,c.positions j]
          simp only [hei,hej,Particle.point,hxy]
        simp only [hei,hej,Particle.point]
        have he : (x:ℂ)-(y:ℂ)=((x:ℝ)-(y:ℝ):ℝ) := by push_cast <;> rfl
        rw [he,Complex.norm_real,Real.norm_eq_abs]
        rcases lt_or_gt_of_ne hxy with hxy | hyx
        · have hh : (x:ℝ)+1 ≤ (y:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hxy)
          rw [abs_of_nonpos (by linarith)]
          linarith
        · have hh : (y:ℝ)+1 ≤ (x:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hyx)
          rw [abs_of_nonneg (by linarith)]
          linarith
      | atom k =>
        simp only [hei,hej,Particle.point,sub_neg_eq_add,← Nat.cast_add,Complex.norm_natCast]
        have hxR : 1 ≤ (x:ℝ) := by exact_mod_cast hx
        push_cast
        linarith [Nat.cast_nonneg k (α := ℝ)]
      | contour u =>
        simp only [hei,hej,Particle.point]
        have hgu := hdom u (c.contour_points j u hej)
        rcases hgu.2.2 with ⟨N,hN⟩ | him
        · have hre : (1/2:ℝ) ≤ |(x:ℝ)-u.re| := by
            by_contra h
            have habs : |(x:ℝ)-u.re| < 1/2 := lt_of_not_ge h
            have hh := abs_lt.mp habs
            rw [hN] at hh
            have hNx : (N:ℝ) < (x:ℝ) := by linarith [hh.1]
            have hxN : (x:ℝ) < (N:ℝ)+1 := by linarith [hh.2]
            have hNxN : N < x := by exact_mod_cast hNx
            have hxNN : x < N+1 := by exact_mod_cast hxN
            omega
          apply hre.trans
          simpa only [Complex.sub_re,Complex.natCast_re] using Complex.abs_re_le_norm ((x:ℂ)-u)
        · have hh := Complex.abs_im_le_norm ((x:ℂ)-u)
          simp only [Complex.sub_im,Complex.natCast_im,zero_sub,abs_neg] at hh
          exact (show (1/2:ℝ) ≤ |u.im| by linarith).trans hh
      | ray y =>
        obtain ⟨hzpos,cut,hcut,hy⟩ := c.ray_points j y hej
        have hlat : F.lattice=Icc (0:ℝ) cut := by
          cases g with
          | pure hp hl hf => simp only [CatalanCore.Li2.Uniform.frameCut] at hcut; cases hcut
          | polygon p hp hl hf =>
            change some p.cut=some cut at hcut
            have he : p.cut=cut := Option.some.inj hcut
            rwa [he] at hl
        have hxl := (c.lattice_sites i x hei).2
        rw [hlat] at hxl
        have hxcut : (x:ℝ) ≤ cut*(n:ℝ) := (div_le_iff₀ hnR).mp hxl.2
        have hxf : x ≤ Nat.floor (cut*n) := by
          have hh : (x:ℝ) < (Nat.floor (cut*n):ℝ)+1 := hxcut.trans_lt (Nat.lt_floor_add_one _)
          have hh' : x < Nat.floor (cut*n)+1 := by exact_mod_cast hh
          omega
        have hxfR : (x:ℝ) ≤ (Nat.floor (cut*n):ℝ) := by exact_mod_cast hxf
        have hre : (1/2:ℝ) ≤ |(x:ℝ)-y| := by
          rw [abs_of_nonpos (by linarith)]
          linarith
        simp only [hei,hej,Particle.point]
        apply hre.trans
        simpa only [Complex.sub_re,Complex.natCast_re,Complex.ofReal_re] using
          Complex.abs_re_le_norm ((x:ℂ)-(y:ℂ))
  rcases hJ with hi | hj
  · exact aux i j hij hi hnp
  · have hnps : ¬c.confluence.paired j i := by
      intro h
      apply hnp
      rcases h with h | h
      · exact Or.inr h
      · exact Or.inl h
    simpa only [norm_sub_rev] using aux j i hij.symm hj hnps
noncomputable def AdmissibleConfig.unscaled {F g z n} (c : AdmissibleConfig F g z n) (hn : 0 < n) :
    ConfluentConfig (2*n) :=
  { x := fun i => (c.particle i).point
    pairs := c.confluence.pairs
    ordered := c.confluence.ordered
    disjoint := c.confluence.disjoint
    diagonal := by
      intro i j hij
      have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have he : c.confluence.x i=c.confluence.x j ↔ (c.particle i).point=(c.particle j).point := by
        rw [c.positions i,c.positions j,div_left_inj' hnC]
      exact he.symm.trans (c.confluence.diagonal i j hij) }

theorem unscaled_reducedVand_bound {F g z n} (c : AdmissibleConfig F g z n) (hn : 0 < n) :
    (2:ℝ)^c.confluence.pairCount*‖(c.unscaled hn).reducedVand‖ ≤
      Real.exp (c.confluence.redLog+4*(n:ℝ)^2*Real.log n) := by
  classical
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hlogn : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg hn1
  let L : Fin (2*n) → Fin (2*n) → ℝ := fun i j =>
    if (i,j) ∈ c.confluence.pairs then 0 else 2*Real.log ‖c.confluence.x i-c.confluence.x j‖
  have hscaled (i j : Fin (2*n)) :
      ‖(c.particle i).point-(c.particle j).point‖=(n:ℝ)*‖c.confluence.x i-c.confluence.x j‖ := by
    have he : (c.particle i).point-(c.particle j).point=
        (n:ℂ)*(c.confluence.x i-c.confluence.x j) := by
      rw [c.positions i,c.positions j]
      field_simp
      <;> ring
    rw [he,norm_mul,Complex.norm_natCast]
  have hexp2 (x : ℝ) (hx : 0 < x) : Real.exp (2*Real.log x)=x^2 := by
    simpa only [Nat.cast_ofNat,Real.exp_log hx] using Real.exp_nat_mul (Real.log x) 2
  have hterm (i j : Fin (2*n)) (hij : i < j) :
      (if (i,j) ∈ c.confluence.pairs then (1:ℝ) else ‖(c.particle i).point-(c.particle j).point‖^2) ≤
        Real.exp (2*Real.log n+L i j) := by
    by_cases hp : (i,j) ∈ c.confluence.pairs
    · simp only [hp,L,↓reduceIte,add_zero]
      exact Real.one_le_exp (by positivity)
    · have hne : c.confluence.x i ≠ c.confluence.x j := by
        intro he
        rcases (c.confluence.diagonal i j hij.ne).mp he with h | h
        · exact hp h
        · have hh := c.confluence.ordered (j,i) h
          exact (not_lt_of_ge hij.le) hh
      have hr : 0 < ‖c.confluence.x i-c.confluence.x j‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
      simp only [hp,L,↓reduceIte,hscaled,Real.exp_add,hexp2 _ hnR,hexp2 _ hr]
      ring_nf <;> exact le_rfl
  have hp : (∏ i : Fin (2*n), ∏ j ∈ Finset.Ioi i,
      if (i,j) ∈ c.confluence.pairs then (1:ℝ) else ‖(c.particle i).point-(c.particle j).point‖^2) ≤
      ∏ i : Fin (2*n), ∏ j ∈ Finset.Ioi i, Real.exp (2*Real.log n+L i j) := by
    apply Finset.prod_le_prod₀ (fun i hi => Finset.prod_nonneg fun j hj => by split_ifs <;> positivity)
    intro i hi
    apply Finset.prod_le_prod₀ (fun j hj => by split_ifs <;> positivity)
    intro j hj
    exact hterm i j (Finset.mem_Ioi.mp hj)
  have hpsum : (∏ i : Fin (2*n), ∏ j ∈ Finset.Ioi i, Real.exp (2*Real.log n+L i j))=
      Real.exp (∑ i : Fin (2*n), ∑ j ∈ Finset.Ioi i, (2*Real.log n+L i j)) := by
    simp only [Real.exp_sum]
  rw [hpsum] at hp
  have hconst := CatalanCore.Decay.ComplexEnergy.sum_Ioi_const (2*n) (2*Real.log (n:ℝ))
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hconst
  have heSum : (∑ i : Fin (2*n), ∑ j ∈ Finset.Ioi i, (2*Real.log n+L i j))=
      (2*(n:ℝ))*(2*(n:ℝ)-1)*Real.log n+(∑ i : Fin (2*n), ∑ j ∈ Finset.Ioi i, L i j) := by
    simp only [Finset.sum_add_distrib]
    rw [hconst]
    ring
  rw [heSum] at hp
  have hnorm : ‖(c.unscaled hn).reducedVand‖=
      ∏ i : Fin (2*n), ∏ j ∈ Finset.Ioi i,
        if (i,j) ∈ c.confluence.pairs then (1:ℝ) else ‖(c.particle i).point-(c.particle j).point‖^2 := by
    change ‖∏ i : Fin (2*n), ∏ j ∈ Finset.Ioi i,
      if (i,j) ∈ c.confluence.pairs then (1:ℂ) else ((c.particle i).point-(c.particle j).point)^2‖= _
    simp only [norm_prod,apply_ite norm,norm_one,norm_pow]
  rw [hnorm]
  apply (mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (2:ℝ)^c.confluence.pairCount)).trans
  have htwo : (2:ℝ)^c.confluence.pairCount=Real.exp ((c.confluence.pairCount:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [htwo,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change _ ≤ (∑ i : Fin (2*n), ∑ j ∈ Finset.Ioi i, L i j)+
    c.confluence.pairs.card*Real.log 2+4*(n:ℝ)^2*Real.log n
  simp only [ConfluentConfig.pairCount]
  nlinarith
noncomputable def AdmissibleConfig.latticeCount {F g z n} (c : AdmissibleConfig F g z n) (x : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => c.particle i=.lattice x)).card

theorem lattice_cap_two {F g z n} (c : AdmissibleConfig F g z n) (x : ℕ) :
    c.latticeCount x ≤ 2 := by
  classical
  unfold AdmissibleConfig.latticeCount
  by_contra hh
  have hlt : 2 < (Finset.univ.filter (fun i => c.particle i=.lattice x)).card := Nat.lt_of_not_ge hh
  obtain ⟨i,hi,j,hj,k,hk,hij,hik,hjk⟩ := Finset.two_lt_card.mp hlt
  simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi hj hk
  have heij : c.confluence.x i=c.confluence.x j := by
    rw [c.positions i,c.positions j]
    simp only [hi,hj,Particle.point]
  have heik : c.confluence.x i=c.confluence.x k := by
    rw [c.positions i,c.positions k]
    simp only [hi,hk,Particle.point]
  rcases (c.confluence.diagonal i j hij).mp heij with hp | hp <;>
    rcases (c.confluence.diagonal i k hik).mp heik with hq | hq
  · have hne : (i,j) ≠ (i,k) := by intro h; exact hjk (Prod.mk.inj h).2
    exact (c.confluence.disjoint (i,j) hp (i,k) hq hne).1 rfl
  · have hne : (i,j) ≠ (k,i) := by intro h; exact hik (Prod.mk.inj h).1
    exact (c.confluence.disjoint (i,j) hp (k,i) hq hne).2.1 rfl
  · have hne : (j,i) ≠ (i,k) := by intro h; exact hij.symm (Prod.mk.inj h).1
    exact (c.confluence.disjoint (j,i) hp (i,k) hq hne).2.2.1 rfl
  · have hne : (j,i) ≠ (k,i) := by intro h; exact hjk (Prod.mk.inj h).1
    exact (c.confluence.disjoint (j,i) hp (k,i) hq hne).2.2.2 rfl
end CatalanCore.Li2.Decay
namespace CatalanCore.Li2.Decay
open CatalanCore.Tools.Jets

theorem admissible_jet_bound (F : Frame) (g : CatalanCore.Li2.Uniform.FrameGeometry F)
    (z : ℝ) (n : ℕ) (hn : 0 < n)
    (hdom : ∀ u ∈ CatalanCore.Li2.Uniform.gammaN g n,
      0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧ ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|))
    (c : AdmissibleConfig F g z n) :
    ‖mixedJet c.Jlat
      (fun i => match c.particle i with | .lattice x => latticeA z n x | _ => 0)
      (fun i => match c.particle i with | .lattice x => latticeB z n x | _ => 0)
      (fun i => (c.particle i).point) (vandSq (2*n))‖ ≤
      (51*(n:ℝ)^2)^(2*n)*Real.exp (c.confluence.redLog+4*(n:ℝ)^2*Real.log n)*
        ∏ i ∈ c.Jlat, ‖match c.particle i with | .lattice x => latticeB z n x | _ => 0‖ := by
  classical
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  let a : Fin (2*n) → ℂ := fun i => match c.particle i with | .lattice x => latticeA z n x | _ => 0
  let b : Fin (2*n) → ℂ := fun i => match c.particle i with | .lattice x => latticeB z n x | _ => 0
  have ha : ∀ i ∈ c.Jlat, ‖a i‖ ≤ (1+7*(n:ℝ))*‖b i‖ := by
    intro i hi
    simp only [AdmissibleConfig.Jlat,Finset.mem_filter,Finset.mem_univ,true_and] at hi
    cases he : c.particle i with
    | lattice x =>
      dsimp only [a,b]
      simp only [he]
      exact latticeA_le_B z n x ((c.lattice_sites i x he).1)
    | contour u => simp only [he,isLattice,Bool.false_eq_true] at hi
    | ray x => simp only [he,isLattice,Bool.false_eq_true] at hi
    | atom j => simp only [he,isLattice,Bool.false_eq_true] at hi
  have hp : ∀ i j, (c.unscaled hn).paired i j → i ∈ c.Jlat ∧ j ∈ c.Jlat ∧ b i=b j := by
    intro i j hij
    obtain ⟨x,hi,hj⟩ := c.paired_lattice i j hij
    refine ⟨?_,?_,?_⟩
    · change i ∈ Finset.univ.filter (fun k => isLattice (c.particle k))
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simp only [hi,isLattice]
    · change j ∈ Finset.univ.filter (fun k => isLattice (c.particle k))
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      simp only [hj,isLattice]
    · simp only [b,hi,hj]
  have hg : ∀ i j, i ≠ j → (i ∈ c.Jlat ∨ j ∈ c.Jlat) → ¬(c.unscaled hn).paired i j →
      (1/2:ℝ) ≤ ‖(c.unscaled hn).x i-(c.unscaled hn).x j‖ := by
    intro i j hij hJ hnp
    exact admissible_lattice_gap F g z n hn hdom c i j hij hJ hnp
  have hj := CatalanCore.Tools.Jets.jet_configuration_bound (2*n) (c.unscaled hn) c.Jlat a b
    (1/2) (1+7*(n:ℝ)) (by norm_num) (by positivity) hg ha hp
  change ‖mixedJet c.Jlat a b (fun i => (c.particle i).point) (vandSq (2*n))‖ ≤ _ at hj
  have hcoef : (1+((2*n:ℕ):ℝ))*(1+(1+7*(n:ℝ))+2*((2*n:ℕ):ℝ)/(1/2:ℝ))=
      (1+2*(n:ℝ))*(2+15*(n:ℝ)) := by push_cast; ring
  rw [hcoef] at hj
  have hcoef' : (1+2*(n:ℝ))*(2+15*(n:ℝ)) ≤ 51*(n:ℝ)^2 := by
    calc
      _ ≤ (3*(n:ℝ))*(17*(n:ℝ)) := mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      _ = _ := by ring
  have hcard : c.Jlat.card ≤ 2*n := by
    have hh := Finset.card_le_card (Finset.subset_univ c.Jlat)
    simpa only [Finset.card_univ,Fintype.card_fin] using hh
  have hpre : ((1+2*(n:ℝ))*(2+15*(n:ℝ)))^c.Jlat.card ≤ (51*(n:ℝ)^2)^(2*n) := by
    apply (pow_le_pow_left₀ (by positivity) hcoef' c.Jlat.card).trans
    exact pow_le_pow_right₀ (by nlinarith : (1:ℝ) ≤ 51*(n:ℝ)^2) hcard
  change ‖mixedJet c.Jlat a b (fun i => (c.particle i).point) (vandSq (2*n))‖ ≤ _
  calc
    _ ≤ ((1+2*(n:ℝ))*(2+15*(n:ℝ)))^c.Jlat.card*2^(c.unscaled hn).pairCount*
      (∏ i ∈ c.Jlat, ‖b i‖)*‖(c.unscaled hn).reducedVand‖ := hj
    _ = ((1+2*(n:ℝ))*(2+15*(n:ℝ)))^c.Jlat.card*
      (2^c.confluence.pairCount*‖(c.unscaled hn).reducedVand‖)*(∏ i ∈ c.Jlat, ‖b i‖) := by
      simp only [ConfluentConfig.pairCount,AdmissibleConfig.unscaled]
      ring
    _ ≤ (51*(n:ℝ)^2)^(2*n)*Real.exp (c.confluence.redLog+4*(n:ℝ)^2*Real.log n)*
      (∏ i ∈ c.Jlat, ‖b i‖) := by
      gcongr
      exact unscaled_reducedVand_bound c hn
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.admissible_jet_bound

namespace CatalanCore.Li2.Decay
attribute [local instance] Classical.propDecidable
noncomputable def latticeSlot : Particle → ℕ
  | .lattice x => x-1
  | _ => 0
noncomputable def atomSlot : Particle → ℕ
  | .atom j => j
  | _ => 0

theorem lattice_field_sum (z : ℝ) (hz : ValidZ z) (F : Frame)
    (g : CatalanCore.Li2.Uniform.FrameGeometry F) (d : DualDatum) (θ : ℝ)
    (n : ℕ) (hn : 0 < n) (c : AdmissibleConfig F g z n) :
    (∑ i ∈ c.Jlat, pos (W z d.σ ((c.particle i).point/(n:ℂ))-θ)) ≤
      2*∑' k : ℕ, if ((k+1:ℕ):ℝ)/n ∈ lat F then
        pos (W z d.σ (((k+1:ℕ):ℂ)/n)-θ) else 0 := by
  classical
  let f : ℕ → ℝ := fun k => if ((k+1:ℕ):ℝ)/n ∈ lat F then
    pos (W z d.σ (((k+1:ℕ):ℂ)/n)-θ) else 0
  let idx : Fin (2*n) → ℕ := fun i => latticeSlot (c.particle i)
  have hf : ∀ k, 0 ≤ f k := by
    intro k
    dsimp only [f]
    split_ifs
    · exact le_max_right _ _
    · exact le_rfl
  have hsite (i) (hi : i ∈ c.Jlat) : ∃ x, c.particle i=.lattice x ∧ 1 ≤ x := by
    have hh : isLattice (c.particle i)=true := (Finset.mem_filter.mp hi).2
    cases he : c.particle i with
    | lattice x => exact ⟨x,rfl,(c.lattice_sites i x he).1⟩
    | contour u => simp only [he,isLattice,Bool.false_eq_true] at hh
    | ray x => simp only [he,isLattice,Bool.false_eq_true] at hh
    | atom j => simp only [he,isLattice,Bool.false_eq_true] at hh
  have heq : (∑ i ∈ c.Jlat, pos (W z d.σ ((c.particle i).point/(n:ℂ))-θ))=
      ∑ i ∈ c.Jlat, f (idx i) := by
    apply Finset.sum_congr rfl
    intro i hi
    obtain ⟨x,hx,hx1⟩ := hsite i hi
    have he : x-1+1=x := by omega
    have hl : (x:ℝ)/(n:ℝ) ∈ lat F := (c.lattice_sites i x hx).2
    simp only [idx,latticeSlot,hx,he,f,Particle.point,if_pos hl]
  have hcap (k : ℕ) : (c.Jlat.filter (fun i => idx i=k)).card ≤ 2 := by
    apply (Finset.card_le_card (show c.Jlat.filter (fun i => idx i=k) ⊆
      Finset.univ.filter (fun i => c.particle i=.lattice (k+1)) from ?_)).trans
      (lattice_cap_two c (k+1))
    intro i hi
    obtain ⟨x,hx,hx1⟩ := hsite i (Finset.mem_filter.mp hi).1
    have hh := (Finset.mem_filter.mp hi).2
    change latticeSlot (c.particle i)=k at hh
    simp only [hx,latticeSlot] at hh
    have he : x=k+1 := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [he] using hx⟩
  obtain ⟨R,hR,hzero⟩ := lattice_pos_compact z hz d θ
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hs : Summable f := by
    apply summable_of_ne_finset_zero (s := Finset.range (Nat.floor (R*n)+1))
    intro k hk
    have hfloor : Nat.floor (R*n)<k := by
      have hh : Nat.floor (R*n)+1 ≤ k := by simpa only [Finset.mem_range,not_lt] using hk
      omega
    have hkn : R < ((k+1:ℕ):ℝ)/n := by
      apply (lt_div_iff₀ hnR).mpr
      have hlt := Nat.lt_floor_add_one (R*(n:ℝ))
      have hh : ((Nat.floor (R*n)+1:ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast hfloor
      push_cast at hh ⊢
      linarith
    have he : (((k+1:ℕ):ℂ)/(n:ℂ))=((((k+1:ℕ):ℝ)/n:ℝ):ℂ) := by push_cast; rfl
    dsimp only [f]
    split_ifs
    · rw [he,hzero _ hkn]
    · rfl
  rw [heq]
  calc
    _ = ∑ k ∈ c.Jlat.image idx, ((c.Jlat.filter (fun i => idx i=k)).card:ℝ)*f k := by
      symm
      simpa only [Finset.sum_const,nsmul_eq_mul] using
        (Finset.sum_fiberwise_of_maps_to' (fun i hi => Finset.mem_image_of_mem idx hi) f)
    _ ≤ ∑ k ∈ c.Jlat.image idx, 2*f k := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcap k) (hf k)
    _ = 2*∑ k ∈ c.Jlat.image idx, f k := by rw [Finset.mul_sum]
    _ ≤ 2*∑' k, f k := mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun k hk => hf k)) (by norm_num)

theorem atom_field_sum (z ρ : ℝ) (F : Frame)
    (g : CatalanCore.Li2.Uniform.FrameGeometry F) (d : DualDatum) (θ : ℝ)
    (n : ℕ) (c : AdmissibleConfig F g z n) :
    (∑ i ∈ Finset.univ.filter (fun i => isAtom (c.particle i)),
      pos (A z ρ d.σ ((atomSlot (c.particle i):ℝ)/n)-θ)) ≤
      ∑ j ∈ Finset.Icc (n+1) (4*n), pos (A z ρ d.σ ((j:ℝ)/n)-θ) := by
  classical
  let J := Finset.univ.filter (fun i => isAtom (c.particle i))
  let idx : Fin (2*n) → ℕ := fun i => atomSlot (c.particle i)
  let f : ℕ → ℝ := fun j => pos (A z ρ d.σ ((j:ℝ)/n)-θ)
  have hsite (i) (hi : i ∈ J) : c.particle i=.atom (idx i) := by
    have hh : isAtom (c.particle i)=true := (Finset.mem_filter.mp hi).2
    cases he : c.particle i with
    | atom j => simp only [idx,he,atomSlot]
    | lattice x => simp only [he,isAtom,Bool.false_eq_true] at hh
    | contour u => simp only [he,isAtom,Bool.false_eq_true] at hh
    | ray x => simp only [he,isAtom,Bool.false_eq_true] at hh
  have hmap : ∀ i ∈ J, idx i ∈ Finset.Icc (n+1) (4*n) := by
    intro i hi
    exact c.atom_sites i (idx i) (hsite i hi)
  have hcap (j : ℕ) : (J.filter (fun i => idx i=j)).card ≤ 1 := by
    apply (Finset.card_le_card (show J.filter (fun i => idx i=j) ⊆
      Finset.univ.filter (fun i => c.particle i=.atom j) from ?_)).trans (c.atom_cap j)
    intro i hi
    obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [he] using hsite i hi⟩
  change (∑ i ∈ J, f (idx i)) ≤ ∑ j ∈ Finset.Icc (n+1) (4*n), f j
  calc
    _ = ∑ j ∈ Finset.Icc (n+1) (4*n), ((J.filter (fun i => idx i=j)).card:ℝ)*f j := by
      symm
      simpa only [Finset.sum_const,nsmul_eq_mul] using Finset.sum_fiberwise_of_maps_to' hmap f
    _ ≤ ∑ j ∈ Finset.Icc (n+1) (4*n), f j := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (show ((J.filter (fun i => idx i=j)).card:ℝ) ≤ 1 by exact_mod_cast hcap j) (show 0 ≤ f j from le_max_right _ _)
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.lattice_field_sum
#print axioms CatalanCore.Li2.Decay.atom_field_sum


namespace CatalanCore.Li2.Decay
noncomputable def phi0CutBound (u : ℂ) : ℝ :=
  3*((‖u‖+1)*Real.log (‖u‖+1)-‖u‖*Real.log ‖u‖-1)-
    ((u.re+4)*Real.log (u.re+4)-u.re*Real.log u.re-4)

private theorem real_log_shift (x B : ℝ) :
    (∫ t in (0:ℝ)..B, Real.log (x+t))=(x+B)*Real.log (x+B)-x*Real.log x-B := by
  rw [intervalIntegral.integral_comp_add_left,integral_log]
  simp only [add_zero,zero_add]
  ring

theorem phi0CutBound_real (x : ℝ) (hx : 0 ≤ x) : phi0CutBound (x:ℂ)=phi0 (x:ℂ) := by
  have he : (fun t : ℝ => Real.log ‖(x:ℂ)+(t:ℂ)‖)=(fun t : ℝ => Real.log (x+t)) := by
    funext t
    rw [← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,Real.log_abs]
  change phi0CutBound (x:ℂ)=3*(∫ t in (0:ℝ)..1, Real.log ‖(x:ℂ)+(t:ℂ)‖)-
    (∫ t in (0:ℝ)..4, Real.log ‖(x:ℂ)+(t:ℂ)‖)
  rw [he,real_log_shift,real_log_shift]
  simp only [phi0CutBound,Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx]

theorem continuous_phi0CutBound : Continuous phi0CutBound := by
  have hn : Continuous (fun u : ℂ => ‖u‖) := continuous_norm
  have h1 := Real.continuous_mul_log.comp (hn.add continuous_const : Continuous (fun u : ℂ => ‖u‖+1))
  have h0 := Real.continuous_mul_log.comp hn
  have h4 := Real.continuous_mul_log.comp (Complex.continuous_re.add continuous_const : Continuous (fun u : ℂ => u.re+4))
  have hr := Real.continuous_mul_log.comp Complex.continuous_re
  exact (((h1.sub h0).sub continuous_const).const_mul 3).sub ((h4.sub hr).sub continuous_const)

theorem phi0_le_cutBound (u : ℂ) (hre : 0 ≤ u.re) : phi0 u ≤ phi0CutBound u := by
  by_cases hu0 : u=0
  · subst u
    simpa only [Complex.ofReal_zero] using (phi0CutBound_real 0 (by norm_num)).ge
  have hu : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hi (B : ℝ) (hB : 0 ≤ B) : IntervalIntegrable (fun t : ℝ => Real.log ‖u+(t:ℂ)‖) volume 0 B := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.log (by fun_prop)
    intro t ht
    rw [uIcc_of_le hB] at ht
    exact (hu.trans_le (norm_le_norm_add u hre t ht.1)).ne'
  have hir (x B : ℝ) : IntervalIntegrable (fun t : ℝ => Real.log (x+t)) volume 0 B := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := x) (b := B+x)).comp_add_left x
    simpa only [sub_self,add_sub_cancel_right] using h
  have hupp := intervalIntegral.integral_mono_on (a := (0:ℝ)) (b := 1) (by norm_num)
    (hi 1 (by norm_num)) (hir ‖u‖ 1) (by
      intro t ht
      apply Real.log_le_log (hu.trans_le (norm_le_norm_add u hre t ht.1))
      have hh := norm_add_le u (t:ℂ)
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1] using hh)
  have hlow := intervalIntegral.integral_mono_on_of_le_Ioo (a := (0:ℝ)) (b := 4) (by norm_num)
    (hir u.re 4) (hi 4 (by norm_num)) (by
      intro t ht
      apply Real.log_le_log (by linarith [ht.1])
      calc
        u.re+t = (u+(t:ℂ)).re := by simp
        _ ≤ |(u+(t:ℂ)).re| := le_abs_self _
        _ ≤ ‖u+(t:ℂ)‖ := Complex.abs_re_le_norm _)
  rw [real_log_shift] at hupp hlow
  change 3*(∫ t in (0:ℝ)..1, Real.log ‖u+(t:ℂ)‖)-
    (∫ t in (0:ℝ)..4, Real.log ‖u+(t:ℂ)‖) ≤ _
  unfold phi0CutBound
  linarith

noncomputable def fieldCutBound (z : ℝ) (d : DualDatum) (u : ℂ) : ℝ :=
  phi0CutBound u+Real.log |z| *u.re-kappaRate z*|u.im|-2*U d.σ u

theorem field_le_cutBound (z : ℝ) (d : DualDatum) (u : ℂ) (hre : 0 ≤ u.re) :
    W z d.σ u ≤ fieldCutBound z d u := by
  have hh := phi0_le_cutBound u hre
  unfold W V fieldCutBound
  linarith

theorem continuous_fieldCutBound (z : ℝ) (d : DualDatum) : Continuous (fieldCutBound z d) := by
  have hU : U d.σ=CatalanCore.Li2.Uniform.pot d.σ := by
    funext u
    simp only [U,P,CatalanCore.Li2.Uniform.pot,integral_neg]
  unfold fieldCutBound
  rw [hU]
  exact (((continuous_phi0CutBound.add (continuous_const.mul Complex.continuous_re)).sub
    (continuous_const.mul Complex.continuous_im.abs)).sub
    (continuous_const.mul (CatalanCore.Li2.Uniform.datum_continuous_pot d)))

theorem fieldCutBound_real (z : ℝ) (d : DualDatum) (x : ℝ) (hx : 0 ≤ x) :
    fieldCutBound z d (x:ℂ)=W z d.σ (x:ℂ) := by
  simp only [fieldCutBound,W,V,phi0CutBound_real x hx]
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.phi0_le_cutBound
#print axioms CatalanCore.Li2.Decay.continuous_fieldCutBound

namespace CatalanCore.Li2.Decay
open CatalanCore.Li2.Uniform
open CatalanCore.Decay.CurveFamily

private theorem chain_above_one (vs : List ℂ) (hvs : ∀ v ∈ vs, 1 < v.im) :
    ∀ u ∈ piecesSet (chainPieces vs), 1 < u.im := by
  induction vs with
  | nil => simp [chainPieces,piecesSet]
  | cons a vs ih =>
    cases vs with
    | nil => simp [chainPieces,piecesSet]
    | cons b vs =>
      intro u hu
      change u ∈ piecesSet (⟨a,b-a,false⟩ :: chainPieces (b::vs)) at hu
      simp only [piecesSet,mem_iUnion] at hu
      obtain ⟨p,hp,hu⟩ := hu
      rcases List.mem_cons.mp hp with hp | hp
      · subst p
        rcases hu with ⟨t,ht,rfl⟩
        have ht' : 0 ≤ t ∧ t ≤ 1 := by simpa only [Bool.false_eq_true,↓reduceIte,mem_Icc] using ht
        have ha := hvs a (by simp)
        have hb := hvs b (by simp)
        have h1 := mul_nonneg (sub_nonneg.mpr ht'.2) (sub_nonneg.mpr ha.le)
        by_cases hz : t=0
        · simp only [Piece.zeta,hz,Complex.ofReal_zero,zero_mul,add_zero]
          exact ha
        · have htpos : 0 < t := lt_of_le_of_ne ht'.1 (Ne.symm hz)
          have h2 := mul_pos htpos (sub_pos.mpr hb)
          simp only [Piece.zeta,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
            Complex.ofReal_im,zero_mul,add_zero,Complex.sub_im]
          nlinarith
      · apply ih (fun v hv => hvs v (by simp [hv])) u
        simp only [piecesSet,mem_iUnion]
        exact ⟨p,hp,hu⟩

private theorem chain_low_start (a : ℂ) (vs : List ℂ) (ha : a.im=1)
    (hvs : ∀ v ∈ vs, 1 < v.im) (u : ℂ)
    (hu : u ∈ piecesSet (chainPieces (a::vs))) (him : u.im ≤ 1) : u=a := by
  cases vs with
  | nil => simp [chainPieces,piecesSet] at hu
  | cons b vs =>
    change u ∈ piecesSet (⟨a,b-a,false⟩ :: chainPieces (b::vs)) at hu
    simp only [piecesSet,mem_iUnion] at hu
    obtain ⟨p,hp,hu⟩ := hu
    rcases List.mem_cons.mp hp with hp | hp
    · subst p
      rcases hu with ⟨t,ht,rfl⟩
      have ht' : 0 ≤ t ∧ t ≤ 1 := by simpa only [Bool.false_eq_true,↓reduceIte,mem_Icc] using ht
      have hb := hvs b (by simp)
      have hz : t=0 := by
        by_contra hz
        have htp : 0 < t := lt_of_le_of_ne ht'.1 (Ne.symm hz)
        have hm := mul_pos htp (sub_pos.mpr hb)
        simp only [Piece.zeta,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
          Complex.ofReal_im,zero_mul,add_zero,Complex.sub_im,ha] at him
        nlinarith
      simp only [Piece.zeta,hz,Complex.ofReal_zero,zero_mul,add_zero]
    · have hh := chain_above_one (b::vs) hvs u (by simp only [piecesSet,mem_iUnion]; exact ⟨p,hp,hu⟩)
      linarith

private theorem segment_center_bound (a b w u : ℂ) (C : ℝ)
    (ha : ‖a-w‖ ≤ C) (hb : ‖b-w‖ ≤ C) (hu : u ∈ pieceSet ⟨a,b-a,false⟩) : ‖u-w‖ ≤ C := by
  have hus : u ∈ segment ℝ a b := by
    rcases hu with ⟨t,ht,rfl⟩
    rw [segment_eq_image_lineMap]
    refine ⟨t,by simpa only [Bool.false_eq_true,↓reduceIte] using ht,?_⟩
    simp only [AffineMap.lineMap_apply_module,Piece.zeta,Complex.real_smul]
    push_cast
    ring
  have hmem := (convex_closedBall w C).segment_subset
    (show a ∈ Metric.closedBall w C by simpa only [Metric.mem_closedBall,dist_eq_norm] using ha)
    (show b ∈ Metric.closedBall w C by simpa only [Metric.mem_closedBall,dist_eq_norm] using hb) hus
  simpa only [Metric.mem_closedBall,dist_eq_norm] using hmem

theorem upperModified_cut_tube (p : PolygonFrame) (n : ℕ) (hn : 0 < n)
    (hheight : 1 < (n:ℝ)*(p.vertex 1).im) (u : ℂ)
    (hu : u ∈ piecesSet (upperModified p n)) (him : u.im ≤ 1) :
    ‖u-(((n:ℝ)*p.cut:ℝ):ℂ)‖ ≤ |((p.vertex 1).re-p.cut)/(p.vertex 1).im|+2 := by
  let w : ℂ := (((n:ℝ)*p.cut:ℝ):ℂ)
  let r : ℝ := ((p.vertex 1).re-p.cut)/(p.vertex 1).im
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hcut0 := p.nonneg
  have hedge := p.edges_pos
  have hvertices (j : ℕ) (hj1 : 1 ≤ j) (hje : j ≤ p.edges) :
      1 < (n:ℝ)*(p.vertex j).im := by
    have hh : (p.vertex 1).im ≤ (p.vertex j).im := by
      rcases hj1.eq_or_lt with h | h
      · rw [← h]
      · exact (p.imag_strict 1 j h hje).le
    exact hheight.trans_le (mul_le_mul_of_nonneg_left hh hnR.le)
  have hvs : ∀ v ∈ (List.range p.edges).map (fun j => (n:ℂ)*p.vertex (j+1)), 1 < v.im := by
    intro v hv
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
    have hj' := List.mem_range.mp hj
    simpa only [Complex.mul_im,Complex.natCast_re,Complex.natCast_im,zero_mul,add_zero] using
      hvertices (j+1) (by omega) (by omega)
  have hcrossR : |crossing p n-(n:ℝ)*p.cut| ≤ 1/2 := by
    have h1 := Nat.floor_le (show 0 ≤ p.cut*(n:ℝ) by positivity)
    have h2 := Nat.lt_floor_add_one (p.cut*(n:ℝ))
    rw [abs_le]
    dsimp only [crossing]
    constructor <;> nlinarith
  have hcross : ‖(crossing p n:ℂ)-w‖ ≤ 1/2 := by
    dsimp only [w]
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    exact hcrossR
  have hcrossI : ‖((crossing p n:ℂ)+Complex.I)-w‖ ≤ 3/2 := by
    have he : ((crossing p n:ℂ)+Complex.I)-w=((crossing p n:ℂ)-w)+Complex.I := by ring
    rw [he]
    have hh := norm_add_le ((crossing p n:ℂ)-w) Complex.I
    rw [Complex.norm_I] at hh
    linarith
  have hfirst : firstAtOne p n-w=(r:ℂ)+Complex.I := by
    dsimp [firstAtOne,w,r]
    push_cast
    ring
  have hfirstnorm : ‖firstAtOne p n-w‖ ≤ |r|+1 := by
    rw [hfirst]
    have hh := norm_add_le (r:ℂ) Complex.I
    simpa only [Complex.norm_real,Real.norm_eq_abs,Complex.norm_I] using hh
  have hfirstim : (firstAtOne p n).im=1 := by
    simp only [firstAtOne,← Complex.ofReal_mul,← Complex.ofReal_sub,← Complex.ofReal_div,
      ← Complex.ofReal_add,Complex.add_im,Complex.ofReal_im,Complex.I_im,zero_add]
  change ‖u-w‖ ≤ |r|+2
  simp only [upperModified,List.cons_append,List.nil_append,chainPieces] at hu
  simp only [piecesSet,mem_iUnion] at hu
  obtain ⟨q,hq,hu⟩ := hu
  rcases List.mem_cons.mp hq with hq | hq
  · subst q
    exact segment_center_bound _ _ w u (|r|+2) (by linarith [abs_nonneg r])
      (by linarith [abs_nonneg r]) hu
  · rcases List.mem_cons.mp hq with hq | hq
    · subst q
      exact segment_center_bound _ _ w u (|r|+2) (by linarith [abs_nonneg r]) (by linarith) hu
    · rcases List.mem_append.mp hq with hq | hq
      · have he := chain_low_start (firstAtOne p n) _ hfirstim hvs u
          (by simp only [piecesSet,mem_iUnion]; exact ⟨q,hq,hu⟩) him
        rw [he]
        linarith
      · have he : q=⟨(n:ℂ)*p.vertex p.edges,Complex.I,true⟩ := List.mem_singleton.mp hq
        subst q
        rcases hu with ⟨t,ht,rfl⟩
        have ht' : 0 ≤ t := by simpa only [↓reduceIte,mem_Ici] using ht
        have hh := hvertices p.edges (by omega) le_rfl
        simp only [Piece.zeta,Complex.add_im,Complex.mul_im,Complex.natCast_re,
          Complex.natCast_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,
          Complex.I_re,zero_mul,mul_zero,add_zero,zero_add,mul_one] at him
        linarith
end CatalanCore.Li2.Decay
namespace CatalanCore.Li2.Decay
open CatalanCore.Li2.Uniform
open CatalanCore.Decay.CurveFamily

theorem gammaN_cut_tube (F : Frame) (g : CatalanCore.Li2.Uniform.FrameGeometry F)
    (cut : ℝ) (hc : frameCut g=some cut) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ u ∈ gammaN g n, |u.im| ≤ 1 →
      ‖u/(n:ℂ)-(cut:ℂ)‖ ≤ C/(n:ℝ) := by
  cases g with
  | pure hp hl hf => simp only [frameCut] at hc; cases hc
  | polygon p hp hl hf =>
    change some p.cut=some cut at hc
    have hecut : p.cut=cut := Option.some.inj hc
    subst cut
    let C := |((p.vertex 1).re-p.cut)/(p.vertex 1).im|+2
    refine ⟨C,by dsimp [C]; positivity,?_⟩
    have hipos : 0 < (p.vertex 1).im := by
      have hh := p.imag_strict 0 1 (by omega) (by have h := p.edges_pos; omega)
      rw [p.initial] at hh
      simpa only [Complex.ofReal_im] using hh
    have hev : ∀ᶠ n : ℕ in atTop, 2/(p.vertex 1).im ≤ (n:ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop _)
    filter_upwards [hev,eventually_ge_atTop (1:ℕ)] with n hn hn1
    have hn0 : 0 < n := by omega
    have hnR : 0 < (n:ℝ) := by exact_mod_cast hn0
    have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    have hheight : 1 < (n:ℝ)*(p.vertex 1).im := by
      have hh := (div_le_iff₀ hipos).mp hn
      linarith
    have hphysical : ∀ u ∈ gammaN (.polygon p hp hl hf) n, |u.im| ≤ 1 →
        ‖u-(((n:ℝ)*p.cut:ℝ):ℂ)‖ ≤ C := by
      intro u hu him
      change u ∈ piecesSet (upperModified p n) ∪ piecesSet ((upperModified p n).map Piece.conj) at hu
      rcases hu with hu | hu
      · exact upperModified_cut_tube p n hn0 hheight u hu ((le_abs_self _).trans him)
      · simp only [piecesSet,mem_iUnion] at hu
        obtain ⟨q,hq,hu⟩ := hu
        obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
        rcases hu with ⟨t,ht,rfl⟩
        let v := r.zeta t
        have ht' : t ∈ (if r.ray then Ici (0:ℝ) else Icc (0:ℝ) 1) := by
          cases hray : r.ray <;> simpa only [Piece.conj,hray,Bool.false_eq_true,↓reduceIte] using ht
        have hv : v ∈ piecesSet (upperModified p n) := by
          simp only [piecesSet,mem_iUnion]
          exact ⟨r,hr,t,ht',rfl⟩
        have himv : |v.im| ≤ 1 := by
          simpa only [v,Piece.zeta_conj,Complex.conj_im,abs_neg] using him
        have hh := upperModified_cut_tube p n hn0 hheight v hv ((le_abs_self _).trans himv)
        rw [Piece.zeta_conj]
        change ‖starRingEnd ℂ v-(((n:ℝ)*p.cut:ℝ):ℂ)‖ ≤ C
        have he : ‖starRingEnd ℂ v-(((n:ℝ)*p.cut:ℝ):ℂ)‖=
            ‖v-(((n:ℝ)*p.cut:ℝ):ℂ)‖ := by
          simpa only [map_sub,Complex.conj_ofReal] using Complex.norm_conj (v-(((n:ℝ)*p.cut:ℝ):ℂ))
        rw [he]
        exact hh
    intro u hu him
    have he : u/(n:ℂ)-(p.cut:ℂ)=(u-(((n:ℝ)*p.cut:ℝ):ℂ))/(n:ℂ) := by
      simp only [Complex.ofReal_mul,Complex.ofReal_natCast]
      field_simp
      <;> ring
    rw [he,norm_div,Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (hphysical u hu him) hnR.le

theorem field_near_cut (z : ℝ) (d : DualDatum) (cut θ : ℝ) (hc : 0 ≤ cut)
    (hθ : W z d.σ (cut:ℂ) ≤ θ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, 0 ≤ u.re → ‖u-(cut:ℂ)‖ < δ → W z d.σ u ≤ θ+ε := by
  obtain ⟨δ,hδ,hh⟩ := Metric.continuousAt_iff.mp
    (continuous_fieldCutBound z d).continuousAt ε hε
  refine ⟨δ,hδ,?_⟩
  intro u hre hu
  have hdist : dist u (cut:ℂ) < δ := by simpa only [dist_eq_norm] using hu
  have hdiff := hh hdist
  rw [Real.dist_eq,fieldCutBound_real z d cut hc] at hdiff
  have hle := field_le_cutBound z d u hre
  have hh' := (abs_lt.mp hdiff).2
  linarith
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.gammaN_cut_tube
#print axioms CatalanCore.Li2.Decay.field_near_cut

namespace CatalanCore.Li2.Decay
open CatalanCore.Li2.Uniform
open CatalanCore.Decay.CurveFamily

theorem contour_mem_free (F : Frame) (g : CatalanCore.Li2.Uniform.FrameGeometry F)
    (z : ℝ) (u : ℂ) (hu : u ∈ contourSet g) : u ∈ free F z := by
  cases g with
  | pure hp hl hf => simp only [contourSet,mem_empty_iff_false] at hu
  | polygon p hp hl hf =>
    change u ∈ F.free (if 0 < z then 1 else -1)
    rw [hf]
    exact Or.inl hu

theorem cut_mem_free (F : Frame) (g : CatalanCore.Li2.Uniform.FrameGeometry F)
    (cut : ℝ) (hc : frameCut g=some cut) (s : ℤ) : (cut:ℂ) ∈ F.free s := by
  cases g with
  | pure hp hl hf => simp only [frameCut] at hc; cases hc
  | polygon p hp hl hf =>
    change some p.cut=some cut at hc
    have he : p.cut=cut := Option.some.inj hc
    subst cut
    rw [hf]
    apply Or.inl
    apply Or.inl
    simp only [piecesSet,mem_iUnion]
    refine ⟨⟨p.vertex 0,p.vertex 1-p.vertex 0,false⟩,?_,?_⟩
    · apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨0,List.mem_range.mpr p.edges_pos,rfl⟩
    · refine ⟨0,by norm_num,?_⟩
      simp only [Piece.zeta,Complex.ofReal_zero,zero_mul,add_zero,p.initial]

theorem gammaN_field_control (z : ℝ) (F : Frame) (g : CatalanCore.Li2.Uniform.FrameGeometry F)
    (d : DualDatum) (θ : ℝ) (hF : FreeBound z F d θ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ u ∈ gammaN g n, W z d.σ (u/(n:ℂ)) ≤ θ+ε := by
  cases g with
  | pure hp hl hf => exact Filter.Eventually.of_forall (by simp [gammaN])
  | polygon p hp hl hf =>
    have hθ : W z d.σ (p.cut:ℂ) ≤ θ := hF _ (cut_mem_free F (.polygon p hp hl hf) p.cut rfl _)
    obtain ⟨δ,hδ,hnear⟩ := field_near_cut z d p.cut θ p.nonneg hθ ε hε
    obtain ⟨C,hC,htube⟩ := gammaN_cut_tube F (.polygon p hp hl hf) p.cut rfl
    have hev : ∀ᶠ n : ℕ in atTop, C/δ < (n:ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
    filter_upwards [htube,hev,gammaN_scaled_agrees F (.polygon p hp hl hf),
      gammaN_kernel_domain F (.polygon p hp hl hf),eventually_ge_atTop (1:ℕ)] with n ht hn hscaled hdom hn1
    have hn0 : 0 < n := by omega
    have hnR : 0 < (n:ℝ) := by exact_mod_cast hn0
    have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    intro u hu
    by_cases him : 1 < |u.im|
    · have hm : u ∈ {u : ℂ | u ∈ gammaN (.polygon p hp hl hf) n ∧ 1 < |u.im|} := ⟨hu,him⟩
      rw [hscaled] at hm
      obtain ⟨⟨v,hv,he⟩,_⟩ := hm
      rw [he]
      have hcancel : ((n:ℂ)*v)/(n:ℂ)=v := by field_simp
      rw [hcancel]
      exact (hF v (contour_mem_free F (.polygon p hp hl hf) z v hv)).trans (by linarith)
    · have hdist : ‖u/(n:ℂ)-(p.cut:ℂ)‖ < δ := by
        apply (ht u hu (le_of_not_gt him)).trans_lt
        apply (div_lt_iff₀ hnR).mpr
        have hh := (div_lt_iff₀ hδ).mp hn
        nlinarith
      have hre : 0 ≤ (u/(n:ℂ)).re := by
        simp only [← Complex.ofReal_natCast,Complex.div_ofReal_re]
        exact div_nonneg (hdom u hu).1 hnR.le
      exact hnear _ hre hdist

theorem ray_field_control (z : ℝ) (hz : 0 < z) (F : Frame)
    (g : CatalanCore.Li2.Uniform.FrameGeometry F) (d : DualDatum) (θ : ℝ)
    (hF : FreeBound z F d θ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ cut : ℝ, frameCut g=some cut → ∀ x : ℝ,
      (Nat.floor (cut*n):ℝ)+1/2 ≤ x → W z d.σ ((x:ℂ)/(n:ℂ)) ≤ θ+ε := by
  cases g with
  | pure hp hl hf => exact Filter.Eventually.of_forall (by simp [frameCut])
  | polygon p hp hl hf =>
    have hθ : W z d.σ (p.cut:ℂ) ≤ θ := hF _ (cut_mem_free F (.polygon p hp hl hf) p.cut rfl _)
    obtain ⟨δ,hδ,hnear⟩ := field_near_cut z d p.cut θ p.nonneg hθ ε hε
    have hev : ∀ᶠ n : ℕ in atTop, 1/δ < (n:ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
    filter_upwards [hev,eventually_ge_atTop (1:ℕ)] with n hn hn1
    have hn0 : 0 < n := by omega
    have hnR : 0 < (n:ℝ) := by exact_mod_cast hn0
    intro cut hc x hx
    change some p.cut=some cut at hc
    have hecut : p.cut=cut := Option.some.inj hc
    subst cut
    have hpoint : (x:ℂ)/(n:ℂ)=((x/(n:ℝ):ℝ):ℂ) := by
      simp only [Complex.ofReal_div,Complex.ofReal_natCast]
    rw [hpoint]
    by_cases hxc : p.cut ≤ x/(n:ℝ)
    · have hmem : ((x/(n:ℝ):ℝ):ℂ) ∈ free F z := by
        change _ ∈ F.free (if 0 < z then 1 else -1)
        rw [if_pos hz,hf]
        apply Or.inr
        change _ ∈ Complex.ofReal '' Ici p.cut
        exact ⟨x/(n:ℝ),hxc,rfl⟩
      exact (hF _ hmem).trans (by linarith)
    · have hx0 : 0 ≤ x := by have hh := Nat.cast_nonneg (Nat.floor (p.cut*n)) (α := ℝ); linarith
      have hdist : ‖((x/(n:ℝ):ℝ):ℂ)-(p.cut:ℂ)‖ < δ := by
        rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
        have h1 : -(x/(n:ℝ)-p.cut) < 1/(n:ℝ) := by
          apply (lt_div_iff₀ hnR).mpr
          have hh := Nat.lt_floor_add_one (p.cut*(n:ℝ))
          have he : x/(n:ℝ)*(n:ℝ)=x := div_mul_cancel₀ _ hnR.ne'
          nlinarith
        apply h1.trans
        apply (div_lt_iff₀ hnR).mpr
        have hh := (div_lt_iff₀ hδ).mp hn
        nlinarith
      exact hnear _ (by simpa only [Complex.ofReal_re] using div_nonneg hx0 hnR.le) hdist
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.gammaN_field_control
#print axioms CatalanCore.Li2.Decay.ray_field_control

namespace CatalanCore.Li2.Decay
attribute [local instance] Classical.propDecidable
noncomputable def particleField (z ρ : ℝ) (d : DualDatum) (n : ℕ) (p : Particle) : ℝ :=
  match p with
  | .atom j => A z ρ d.σ ((j:ℝ)/n)
  | _ => W z d.σ (p.point/(n:ℂ))

theorem configuration_field_sum (z : ℝ) (hz : ValidZ z) (F : Frame)
    (g : CatalanCore.Li2.Uniform.FrameGeometry F) (d : DualDatum) (θ ρ : ℝ)
    (hF : FreeBound z F d θ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ c : AdmissibleConfig F g z n,
      (∑ i : Fin (2*n), (particleField z ρ d n (c.particle i)-θ)) ≤
        (n:ℝ)*(2*latPenalty z F d.σ θ+atomPenalty z ρ d.σ θ+ε) := by
  let δ := ε/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hΓ := gammaN_field_control z F g d θ hF δ hδ
  have hr : ∀ᶠ n : ℕ in atTop, 0 < z → ∀ cut : ℝ, CatalanCore.Li2.Uniform.frameCut g=some cut →
      ∀ x : ℝ, (Nat.floor (cut*n):ℝ)+1/2 ≤ x →
        W z d.σ ((x:ℂ)/(n:ℂ)) ≤ θ+δ := by
    by_cases hp : 0 < z
    · exact (ray_field_control z hp F g d θ hF δ hδ).mono (fun n hn _ => hn)
    · exact Eventually.of_forall (fun n hn => (hp hn).elim)
  have hlat := (lattice_riemann z hz F g d θ).eventually
    (eventually_lt_nhds (show latPenalty z F d.σ θ < latPenalty z F d.σ θ+δ by linarith))
  have hat := (atom_riemann z ρ hz d θ).eventually
    (eventually_lt_nhds (show atomPenalty z ρ d.σ θ < atomPenalty z ρ d.σ θ+δ by linarith))
  filter_upwards [hΓ,hr,hlat,hat,eventually_ge_atTop (1:ℕ)] with n hnΓ hnr hnl hna hn1
  intro c
  have hn : 0 < n := by omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hterm (i : Fin (2*n)) : particleField z ρ d n (c.particle i)-θ ≤
      (if isLattice (c.particle i) then pos (W z d.σ ((c.particle i).point/(n:ℂ))-θ) else 0)+
      (if isAtom (c.particle i) then pos (A z ρ d.σ ((atomSlot (c.particle i):ℝ)/n)-θ) else 0)+δ := by
    cases he : c.particle i with
    | lattice x =>
      simp only [particleField,isLattice,isAtom,Particle.point,Bool.false_eq_true,↓reduceIte,add_zero]
      exact (le_max_left _ (0:ℝ)).trans (le_add_of_nonneg_right hδ.le)
    | atom j =>
      simp only [particleField,isLattice,isAtom,atomSlot,Bool.false_eq_true,↓reduceIte,zero_add]
      exact (le_max_left _ (0:ℝ)).trans (le_add_of_nonneg_right hδ.le)
    | contour u =>
      have hh := hnΓ u (c.contour_points i u he)
      simp only [particleField,isLattice,isAtom,Particle.point,Bool.false_eq_true,↓reduceIte,zero_add]
      linarith
    | ray x =>
      obtain ⟨hp,cut,hcut,hx⟩ := c.ray_points i x he
      have hh := hnr hp cut hcut x hx
      simp only [particleField,isLattice,isAtom,Particle.point,Bool.false_eq_true,↓reduceIte,zero_add]
      linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  simp only [Finset.sum_add_distrib,← Finset.sum_filter,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at hsum
  have hl := lattice_field_sum z hz F g d θ n hn c
  have ha := atom_field_sum z ρ F g d θ n c
  have hnl' : (∑' k : ℕ, if ((k+1:ℕ):ℝ)/n ∈ lat F then
      pos (W z d.σ (((k+1:ℕ):ℂ)/n)-θ) else 0) ≤
        (n:ℝ)*(latPenalty z F d.σ θ+δ) := by
    have he : (n:ℝ)*((n:ℝ)⁻¹*(∑' k : ℕ, if ((k+1:ℕ):ℝ)/n ∈ lat F then
      pos (W z d.σ (((k+1:ℕ):ℂ)/n)-θ) else 0))=
      ∑' k : ℕ, if ((k+1:ℕ):ℝ)/n ∈ lat F then pos (W z d.σ (((k+1:ℕ):ℂ)/n)-θ) else 0 := by field_simp
    nlinarith
  have hna' : (∑ j ∈ Finset.Icc (n+1) (4*n), pos (A z ρ d.σ ((j:ℝ)/n)-θ)) ≤
      (n:ℝ)*(atomPenalty z ρ d.σ θ+δ) := by
    have he : (n:ℝ)*((n:ℝ)⁻¹*(∑ j ∈ Finset.Icc (n+1) (4*n), pos (A z ρ d.σ ((j:ℝ)/n)-θ)))=
      ∑ j ∈ Finset.Icc (n+1) (4*n), pos (A z ρ d.σ ((j:ℝ)/n)-θ) := by field_simp
    nlinarith
  change (∑ i : Fin (2*n), (particleField z ρ d n (c.particle i)-θ)) ≤ _
  change (∑ i : Fin (2*n), (particleField z ρ d n (c.particle i)-θ)) ≤
    (∑ i ∈ c.Jlat, pos (W z d.σ ((c.particle i).point/(n:ℂ))-θ))+
      (∑ i ∈ Finset.univ.filter (fun i => isAtom (c.particle i)),
        pos (A z ρ d.σ ((atomSlot (c.particle i):ℝ)/n)-θ))+2*(n:ℝ)*δ at hsum
  dsimp only [δ] at *
  nlinarith
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.configuration_field_sum


namespace CatalanCore.Li2.Decay
attribute [local instance] Classical.propDecidable
noncomputable def particleAmplitude (z : ℝ) (n : ℕ) (t : ℝ) : Particle → ℂ
  | .lattice x => latticeB z n x
  | .contour u => contourDensity z n 1 u
  | .ray x => rayDensity z n x
  | .atom j => (t*atomWeight z n j:ℂ)
noncomputable def particleExternal (z ρ : ℝ) (n : ℕ) (p : Particle) : ℝ :=
  match p with
  | .atom j => omega z ((j:ℝ)/n)-ρ
  | _ => V z (p.point/(n:ℂ))
noncomputable def particlePoly (K n : ℕ) (p : Particle) : ℝ :=
  if isAtom p then 1 else (1+‖p.point/(n:ℂ)‖)^K

theorem particle_amplitude_bound (z : ℝ) (hz : ValidZ z) (F : Frame)
    (g : CatalanCore.Li2.Uniform.FrameGeometry F) (ρ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ᶠ n : ℕ in atTop,
      ∀ t : ℝ, |t| ≤ Real.exp (-ρ*(n:ℝ)) → ∀ c : AdmissibleConfig F g z n,
      ∀ i : Fin (2*n), ‖particleAmplitude z n t (c.particle i)‖ ≤
        C*(n:ℝ)^C*particlePoly K n (c.particle i)*
          Real.exp ((n:ℝ)*(particleExternal z ρ n (c.particle i)-Real.log n)) := by
  obtain ⟨Ck,hCk,hk⟩ := piece_weight_le z hz F g
  obtain ⟨Ca,hCa,ha⟩ := atom_weight_le z hz
  let C := Ck+Ca+1
  have hC : 0 < C := by dsimp [C]; linarith
  have hkC : Ck ≤ C := by dsimp [C]; linarith
  have haC : Ca ≤ C := by dsimp [C]; linarith
  let K := Nat.ceil C
  have hK : C ≤ (K:ℝ) := Nat.le_ceil C
  refine ⟨C,hC,K,?_⟩
  filter_upwards [hk,eventually_ge_atTop (1:ℕ)] with n hkn hn1
  have hn : 0 < n := by omega
  have hnR : 1 ≤ (n:ℝ) := by exact_mod_cast hn1
  have hmaj (u : ℂ) : weightMajorant z n Ck u ≤ C*(n:ℝ)^C*(1+‖u/(n:ℂ)‖)^K*
      Real.exp ((n:ℝ)*(V z (u/(n:ℂ))-Real.log n)) := by
    have hnPow : (n:ℝ)^Ck ≤ (n:ℝ)^C := Real.rpow_le_rpow_of_exponent_le hnR hkC
    have hpPow : (1+‖u/(n:ℂ)‖)^Ck ≤ (1+‖u/(n:ℂ)‖)^K := by
      simpa only [Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le (show 1 ≤ 1+‖u/(n:ℂ)‖ by linarith [norm_nonneg (u/(n:ℂ))]) (hkC.trans hK)
    unfold weightMajorant
    gcongr
  have haPref : Ca*(n:ℝ)^Ca ≤ C*(n:ℝ)^C := by
    gcongr
  intro t ht c i
  cases he : c.particle i with
  | lattice x =>
    simp only [particleAmplitude,particleExternal,particlePoly,isAtom,Particle.point,Bool.false_eq_true,↓reduceIte]
    exact (hkn.2.2 x (c.lattice_sites i x he).1).trans (hmaj (x:ℂ))
  | contour u =>
    simp only [particleAmplitude,particleExternal,particlePoly,isAtom,Particle.point,Bool.false_eq_true,↓reduceIte]
    exact (hkn.1 u (c.contour_points i u he)).trans (hmaj u)
  | ray x =>
    obtain ⟨hp,cut,hcut,hx⟩ := c.ray_points i x he
    simp only [particleAmplitude,particleExternal,particlePoly,isAtom,Particle.point,Bool.false_eq_true,↓reduceIte]
    exact (hkn.2.1 hp cut hcut x hx).trans (hmaj (x:ℂ))
  | atom j =>
    have hj := c.atom_sites i j he
    have hbound := ha n hn j hj
    have heExp : Real.exp (-ρ*(n:ℝ))*Real.exp ((n:ℝ)*(omega z ((j:ℝ)/n)-Real.log n))=
        Real.exp ((n:ℝ)*(omega z ((j:ℝ)/n)-ρ-Real.log n)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    simp only [particleAmplitude,particleExternal,particlePoly,isAtom,↓reduceIte,mul_one,
      norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_mul]
    calc
      _ ≤ Real.exp (-ρ*(n:ℝ))*(Ca*(n:ℝ)^Ca*Real.exp ((n:ℝ)*(omega z ((j:ℝ)/n)-Real.log n))) :=
        mul_le_mul ht hbound (abs_nonneg _) (Real.exp_pos _).le
      _ = Ca*(n:ℝ)^Ca*Real.exp ((n:ℝ)*(omega z ((j:ℝ)/n)-ρ-Real.log n)) := by
        calc
          _ = (Ca*(n:ℝ)^Ca)*(Real.exp (-ρ*(n:ℝ))*Real.exp ((n:ℝ)*(omega z ((j:ℝ)/n)-Real.log n))) := by ring
          _ = _ := by rw [heExp]
      _ ≤ _ := mul_le_mul_of_nonneg_right haPref (Real.exp_pos _).le
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.particle_amplitude_bound


namespace CatalanCore.Li2.Decay
attribute [local instance] Classical.propDecidable
theorem configuration_weighted_field_sum (z : ℝ) (hz : ValidZ z) (F : Frame)
    (g : CatalanCore.Li2.Uniform.FrameGeometry F) (d : DualDatum) (θ ρ : ℝ)
    (hF : FreeBound z F d θ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ c : AdmissibleConfig F g z n,
      (∑ i : Fin (2*n), (if isAtom (c.particle i) then (n:ℝ) else (n:ℝ)-1)*(particleField z ρ d n (c.particle i)-θ)) ≤
        (n:ℝ)^2*(2*latPenalty z F d.σ θ+atomPenalty z ρ d.σ θ+ε) := by
  let δ := ε/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hΓ := gammaN_field_control z F g d θ hF δ hδ
  have hr : ∀ᶠ n : ℕ in atTop, 0 < z → ∀ cut : ℝ, CatalanCore.Li2.Uniform.frameCut g=some cut →
      ∀ x : ℝ, (Nat.floor (cut*n):ℝ)+1/2 ≤ x →
        W z d.σ ((x:ℂ)/(n:ℂ)) ≤ θ+δ := by
    by_cases hp : 0 < z
    · exact (ray_field_control z hp F g d θ hF δ hδ).mono (fun n hn _ => hn)
    · exact Eventually.of_forall (fun n hn => (hp hn).elim)
  have hlat := (lattice_riemann z hz F g d θ).eventually
    (eventually_lt_nhds (show latPenalty z F d.σ θ < latPenalty z F d.σ θ+δ by linarith))
  have hat := (atom_riemann z ρ hz d θ).eventually
    (eventually_lt_nhds (show atomPenalty z ρ d.σ θ < atomPenalty z ρ d.σ θ+δ by linarith))
  filter_upwards [hΓ,hr,hlat,hat,eventually_ge_atTop (1:ℕ)] with n hnΓ hnr hnl hna hn1
  intro c
  have hn : 0 < n := by omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnn : 0 ≤ (n:ℝ)-1 := by
    have hh : (1:ℝ) ≤ n := by exact_mod_cast hn1
    linarith
  have hterm (i : Fin (2*n)) : (if isAtom (c.particle i) then (n:ℝ) else (n:ℝ)-1)*(particleField z ρ d n (c.particle i)-θ) ≤
      (n:ℝ)*((if isLattice (c.particle i) then pos (W z d.σ ((c.particle i).point/(n:ℂ))-θ) else 0)+
      (if isAtom (c.particle i) then pos (A z ρ d.σ ((atomSlot (c.particle i):ℝ)/n)-θ) else 0)+δ) := by
    cases he : c.particle i with
    | lattice x =>
      simp only [particleField,isLattice,isAtom,Particle.point,Bool.false_eq_true,↓reduceIte,add_zero]
      have hx : W z d.σ ((x:ℂ)/(n:ℂ))-θ ≤ pos (W z d.σ ((x:ℂ)/(n:ℂ))-θ) := le_max_left _ 0
      have hp : 0 ≤ pos (W z d.σ ((x:ℂ)/(n:ℂ))-θ) := le_max_right _ 0
      have hh := mul_le_mul_of_nonneg_left hx hnn
      nlinarith
    | atom j =>
      simp only [particleField,isLattice,isAtom,atomSlot,Bool.false_eq_true,↓reduceIte,zero_add]
      have hx : A z ρ d.σ ((j:ℝ)/n)-θ ≤ pos (A z ρ d.σ ((j:ℝ)/n)-θ) := le_max_left _ 0
      have hh := mul_le_mul_of_nonneg_left hx hnR.le
      nlinarith
    | contour u =>
      have hh := hnΓ u (c.contour_points i u he)
      simp only [particleField,isLattice,isAtom,Particle.point,Bool.false_eq_true,↓reduceIte,zero_add]
      have hh' := mul_le_mul_of_nonneg_left (show W z d.σ (u/(n:ℂ))-θ ≤ δ by linarith) hnn
      nlinarith
    | ray x =>
      obtain ⟨hp,cut,hcut,hx⟩ := c.ray_points i x he
      have hh := hnr hp cut hcut x hx
      simp only [particleField,isLattice,isAtom,Particle.point,Bool.false_eq_true,↓reduceIte,zero_add]
      have hh' := mul_le_mul_of_nonneg_left (show W z d.σ ((x:ℂ)/(n:ℂ))-θ ≤ δ by linarith) hnn
      nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)
  rw [← Finset.mul_sum] at hsum
  simp only [Finset.sum_add_distrib,← Finset.sum_filter,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at hsum
  have hl := lattice_field_sum z hz F g d θ n hn c
  have ha := atom_field_sum z ρ F g d θ n c
  have hnl' : (∑' k : ℕ, if ((k+1:ℕ):ℝ)/n ∈ lat F then
      pos (W z d.σ (((k+1:ℕ):ℂ)/n)-θ) else 0) ≤
        (n:ℝ)*(latPenalty z F d.σ θ+δ) := by
    have he : (n:ℝ)*((n:ℝ)⁻¹*(∑' k : ℕ, if ((k+1:ℕ):ℝ)/n ∈ lat F then
      pos (W z d.σ (((k+1:ℕ):ℂ)/n)-θ) else 0))=
      ∑' k : ℕ, if ((k+1:ℕ):ℝ)/n ∈ lat F then pos (W z d.σ (((k+1:ℕ):ℂ)/n)-θ) else 0 := by field_simp
    nlinarith
  have hna' : (∑ j ∈ Finset.Icc (n+1) (4*n), pos (A z ρ d.σ ((j:ℝ)/n)-θ)) ≤
      (n:ℝ)*(atomPenalty z ρ d.σ θ+δ) := by
    have he : (n:ℝ)*((n:ℝ)⁻¹*(∑ j ∈ Finset.Icc (n+1) (4*n), pos (A z ρ d.σ ((j:ℝ)/n)-θ)))=
      ∑ j ∈ Finset.Icc (n+1) (4*n), pos (A z ρ d.σ ((j:ℝ)/n)-θ) := by field_simp
    nlinarith
  have hupper : (∑ i ∈ c.Jlat, pos (W z d.σ ((c.particle i).point/(n:ℂ))-θ))+
      (∑ i ∈ Finset.univ.filter (fun i => isAtom (c.particle i)),
        pos (A z ρ d.σ ((atomSlot (c.particle i):ℝ)/n)-θ))+2*(n:ℝ)*δ ≤
          (n:ℝ)*(2*latPenalty z F d.σ θ+atomPenalty z ρ d.σ θ+ε) := by
    dsimp only [δ] at *
    nlinarith
  change (∑ i : Fin (2*n), (if isAtom (c.particle i) then (n:ℝ) else (n:ℝ)-1)*(particleField z ρ d n (c.particle i)-θ)) ≤
    (n:ℝ)*((∑ i ∈ c.Jlat, pos (W z d.σ ((c.particle i).point/(n:ℂ))-θ))+
      (∑ i ∈ Finset.univ.filter (fun i => isAtom (c.particle i)),
        pos (A z ρ d.σ ((atomSlot (c.particle i):ℝ)/n)-θ))+2*(n:ℝ)*δ) at hsum
  apply hsum.trans
  calc
    _ ≤ (n:ℝ)*((n:ℝ)*(2*latPenalty z F d.σ θ+atomPenalty z ρ d.σ θ+ε)) :=
      mul_le_mul_of_nonneg_left hupper hnR.le
    _ = _ := by ring
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.configuration_weighted_field_sum


namespace CatalanCore.Li2.Decay
open CatalanCore.Tools.Jets
attribute [local instance] Classical.propDecidable

theorem configWeight_le_amplitudes (F : Frame) (g : CatalanCore.Li2.Uniform.FrameGeometry F)
    (z : ℝ) (n : ℕ) (hn : 0 < n) (t : ℝ)
    (hdom : ∀ u ∈ CatalanCore.Li2.Uniform.gammaN g n,
      0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧ ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|))
    (c : AdmissibleConfig F g z n) :
    ‖configWeight z n t c‖ ≤ (51*(n:ℝ)^2)^(2*n)*
      Real.exp (c.confluence.redLog+4*(n:ℝ)^2*Real.log n)*
        ∏ i : Fin (2*n), ‖particleAmplitude z n t (c.particle i)‖ := by
  classical
  let b (i : Fin (2*n)) : ℂ := match c.particle i with | .lattice x => latticeB z n x | _ => 0
  let w (i : Fin (2*n)) : ℂ := match c.particle i with
    | .lattice _ => 1
    | .contour u => contourDensity z n 1 u
    | .ray x => rayDensity z n x
    | .atom j => (t*atomWeight z n j:ℂ)
  have hp : (∏ i ∈ c.Jlat, ‖b i‖)*(∏ i : Fin (2*n), ‖w i‖)=
      ∏ i : Fin (2*n), ‖particleAmplitude z n t (c.particle i)‖ := by
    change (∏ i ∈ Finset.univ.filter (fun i => isLattice (c.particle i)), ‖b i‖)*_= _
    rw [Finset.prod_filter,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    cases he : c.particle i <;> simp only [b,w,he,particleAmplitude,isLattice,
      Bool.false_eq_true,↓reduceIte,norm_one,one_mul,mul_one]
  have hj := admissible_jet_bound F g z n hn hdom c
  change ‖mixedJet c.Jlat _ b _ (vandSq (2*n))‖ ≤
    (51*(n:ℝ)^2)^(2*n)*Real.exp (c.confluence.redLog+4*(n:ℝ)^2*Real.log n)*(∏ i ∈ c.Jlat, ‖b i‖) at hj
  change ‖mixedJet c.Jlat _ b _ (vandSq (2*n))*(∏ i : Fin (2*n), w i)‖ ≤ _
  rw [norm_mul,norm_prod]
  calc
    _ ≤ ((51*(n:ℝ)^2)^(2*n)*Real.exp (c.confluence.redLog+4*(n:ℝ)^2*Real.log n)*
      (∏ i ∈ c.Jlat, ‖b i‖))*(∏ i : Fin (2*n), ‖w i‖) :=
        mul_le_mul_of_nonneg_right hj (Finset.prod_nonneg fun i hi => norm_nonneg _)
    _ = _ := by rw [mul_assoc,hp]

theorem particleExternal_eq_field (z ρ : ℝ) (d : DualDatum) (n : ℕ) (p : Particle) :
    particleExternal z ρ n p=particleField z ρ d n p+2*U d.σ (p.point/(n:ℂ)) := by
  cases p with
  | lattice x => simp only [particleExternal,particleField,W,Particle.point]; ring
  | contour u => simp only [particleExternal,particleField,W,Particle.point]; ring
  | ray x => simp only [particleExternal,particleField,W,Particle.point]; ring
  | atom j =>
    have he : (-(j:ℂ))/(n:ℂ)= -((((j:ℝ)/n:ℝ):ℂ)) := by push_cast; ring
    change omega z ((j:ℝ)/n)-ρ=(omega z ((j:ℝ)/n)-ρ-
      2*U d.σ (-((((j:ℝ)/n:ℝ):ℂ))))+2*U d.σ ((-(j:ℂ))/(n:ℂ))
    rw [he]
    ring
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.configWeight_le_amplitudes
#print axioms CatalanCore.Li2.Decay.particleExternal_eq_field



namespace CatalanCore.Li2.Decay
open CatalanCore.Tools.Jets
attribute [local instance] Classical.propDecidable
noncomputable def holderError (d : DualDatum) (n : ℕ) (p : ℕ) : ℝ :=
  (2*n:ℝ)*Real.log ((n:ℝ)^2)+
    p*(Real.log 2+2*Real.log ((n:ℝ)^2))+
    4*(d.holderConstant:ℝ)*(n:ℝ)^(2-2*d.holderExponent)
noncomputable def tailField (z θ : ℝ) (d : DualDatum) (n : ℕ) (p : Particle) : ℝ :=
  if isAtom p then 0 else W z d.σ (p.point/(n:ℂ))-θ
noncomputable def weightedField (z ρ θ : ℝ) (d : DualDatum) (n : ℕ) (p : Particle) : ℝ :=
  (if isAtom p then (n:ℝ) else (n:ℝ)-1)*(particleField z ρ d n p-θ)

theorem tailEnvelope_eq (z θ : ℝ) (d : DualDatum) (K n : ℕ)
    {F g} (c : AdmissibleConfig F g z n) :
    tailEnvelope z d θ K n c=(∏ i : Fin (2*n), particlePoly K n (c.particle i))*
      Real.exp (∑ i : Fin (2*n), tailField z θ d n (c.particle i)) := by
  rw [Real.exp_sum,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases he : c.particle i <;> simp only [tailEnvelope,particlePoly,tailField,isAtom,
    he,Bool.false_eq_true,↓reduceIte,Real.exp_zero,mul_one]

theorem configuration_prebound (z ρ θ C : ℝ) (hC : 0 < C) (d : DualDatum) (K n : ℕ) (hn : 0 < n)
    (F : Frame) (g : CatalanCore.Li2.Uniform.FrameGeometry F) (t : ℝ)
    (hdom : ∀ u ∈ CatalanCore.Li2.Uniform.gammaN g n,
      0 ≤ u.re ∧ 1/2 ≤ ‖u‖ ∧ ((∃ N : ℕ, u.re=(N:ℝ)+1/2) ∨ 1 ≤ |u.im|))
    (c : AdmissibleConfig F g z n)
    (hamp : ∀ i : Fin (2*n), ‖particleAmplitude z n t (c.particle i)‖ ≤
      C*(n:ℝ)^C*particlePoly K n (c.particle i)*
        Real.exp ((n:ℝ)*(particleExternal z ρ n (c.particle i)-Real.log n))) :
    ‖configWeight z n t c‖ ≤ (51*(n:ℝ)^2)^(2*n)*(C*(n:ℝ)^C)^(2*n)*
      Real.exp ((n:ℝ)^2*(I d.σ+2*θ)+2*(n:ℝ)^2*Real.log n+
        (∑ i : Fin (2*n), weightedField z ρ θ d n (c.particle i))+
        holderError d n c.confluence.pairCount)*tailEnvelope z d θ K n c := by
  classical
  let P := ∏ i : Fin (2*n), particlePoly K n (c.particle i)
  have hP : 0 ≤ P := Finset.prod_nonneg (fun i hi => by unfold particlePoly; split_ifs <;> positivity)
  have hprod := Finset.prod_le_prod₀ (fun i (_ : i ∈ Finset.univ) => norm_nonneg _) (fun i (_ : i ∈ Finset.univ) => hamp i)
  have hexp : (∏ i : Fin (2*n), Real.exp ((n:ℝ)*(particleExternal z ρ n (c.particle i)-Real.log n)))=
      Real.exp ((n:ℝ)*(∑ i : Fin (2*n), particleExternal z ρ n (c.particle i))-2*(n:ℝ)^2*Real.log n) := by
    rw [← Real.exp_sum,← Finset.mul_sum,Finset.sum_sub_distrib,Finset.sum_const]
    simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
    congr 1
    ring
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hprod
  rw [hexp] at hprod
  have hjet := configWeight_le_amplitudes F g z n hn t hdom c
  have hraw : ‖configWeight z n t c‖ ≤
      (51*(n:ℝ)^2)^(2*n)*(C*(n:ℝ)^C)^(2*n)*
        Real.exp (c.confluence.redLog+2*(n:ℝ)^2*Real.log n+
          (n:ℝ)*(∑ i : Fin (2*n), particleExternal z ρ n (c.particle i)))*P := by
    apply hjet.trans
    apply (mul_le_mul_of_nonneg_left hprod (by positivity)).trans_eq
    have he : Real.exp (c.confluence.redLog+4*(n:ℝ)^2*Real.log n)*
        Real.exp ((n:ℝ)*(∑ i : Fin (2*n), particleExternal z ρ n (c.particle i))-2*(n:ℝ)^2*Real.log n)=
        Real.exp (c.confluence.redLog+2*(n:ℝ)^2*Real.log n+
          (n:ℝ)*(∑ i : Fin (2*n), particleExternal z ρ n (c.particle i))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (51*(n:ℝ)^2)^(2*n)*(C*(n:ℝ)^C)^(2*n)*
        (Real.exp (c.confluence.redLog+4*(n:ℝ)^2*Real.log n)*
          Real.exp ((n:ℝ)*(∑ i : Fin (2*n), particleExternal z ρ n (c.particle i))-2*(n:ℝ)^2*Real.log n))*P := by
            dsimp only [P]
            rw [mul_pow]
            ring
      _ = _ := by rw [he]
  have hholder : c.confluence.redLog ≤ (n:ℝ)^2*I d.σ-
      2*n*(∑ i, U d.σ (c.confluence.x i))+holderError d n c.confluence.pairCount := by
    have hh := holder_configuration_bound n hn c.confluence d
    unfold holderError
    linarith
  have hsum : (∑ i : Fin (2*n), particleExternal z ρ n (c.particle i))=
      (∑ i : Fin (2*n), particleField z ρ d n (c.particle i))+
        2*(∑ i : Fin (2*n), U d.σ (c.confluence.x i)) := by
    simp_rw [particleExternal_eq_field z ρ d n,c.positions]
    rw [Finset.sum_add_distrib,Finset.mul_sum]
  have hfield : (n:ℝ)*(∑ i : Fin (2*n), particleField z ρ d n (c.particle i))=
      2*(n:ℝ)^2*θ+(∑ i : Fin (2*n), weightedField z ρ θ d n (c.particle i))+
        (∑ i : Fin (2*n), tailField z θ d n (c.particle i)) := by
    have hpoint (i : Fin (2*n)) : (n:ℝ)*particleField z ρ d n (c.particle i)=
        (n:ℝ)*θ+weightedField z ρ θ d n (c.particle i)+tailField z θ d n (c.particle i) := by
      cases he : c.particle i <;> simp only [particleField,weightedField,tailField,isAtom,
        he,Bool.false_eq_true,↓reduceIte,Particle.point] <;> ring
    rw [Finset.mul_sum]
    simp_rw [hpoint]
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hexponent : c.confluence.redLog+2*(n:ℝ)^2*Real.log n+
      (n:ℝ)*(∑ i : Fin (2*n), particleExternal z ρ n (c.particle i)) ≤
        (n:ℝ)^2*(I d.σ+2*θ)+2*(n:ℝ)^2*Real.log n+
          (∑ i : Fin (2*n), weightedField z ρ θ d n (c.particle i))+
          holderError d n c.confluence.pairCount+
          (∑ i : Fin (2*n), tailField z θ d n (c.particle i)) := by
    rw [hsum,mul_add,hfield]
    nlinarith
  rw [tailEnvelope_eq]
  apply hraw.trans
  calc
    _ ≤ (51*(n:ℝ)^2)^(2*n)*(C*(n:ℝ)^C)^(2*n)*
      Real.exp ((n:ℝ)^2*(I d.σ+2*θ)+2*(n:ℝ)^2*Real.log n+
        (∑ i : Fin (2*n), weightedField z ρ θ d n (c.particle i))+
        holderError d n c.confluence.pairCount+
        (∑ i : Fin (2*n), tailField z θ d n (c.particle i)))*P := by
      gcongr
    _ = _ := by rw [Real.exp_add]; ring
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.configuration_prebound


namespace CatalanCore.Li2.Decay
open CatalanCore.Tools.Jets
noncomputable def analyticError (C : ℝ) (d : DualDatum) (n : ℕ) : ℝ :=
  (2*Real.log 51+2*Real.log C+Real.log 2)*(n:ℝ)+
    (12+2*C)*(n:ℝ)*Real.log n+
    4*(d.holderConstant:ℝ)*(n:ℝ)^(2-2*d.holderExponent)

theorem analyticError_small (C : ℝ) (d : DualDatum) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, analyticError C d n ≤ ε*(n:ℝ)^2 := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n:ℝ)/(n:ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def,pow_one,one_mul,add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => (n:ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (n:ℝ)^(-(2*d.holderExponent))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by nlinarith [d.holderPos] : 0 < 2*d.holderExponent)).comp
      tendsto_natCast_atTop_atTop
  have ht := ((hinv.const_mul (2*Real.log 51+2*Real.log C+Real.log 2)).add
    (hlog.const_mul (12+2*C))).add (hpow.const_mul (4*(d.holderConstant:ℝ)))
  simp only [mul_zero,add_zero] at ht
  have hev := ht.eventually (eventually_lt_nhds hε)
  filter_upwards [hev,eventually_ge_atTop (1:ℕ)] with n hn hn1
  have hnR : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hePow : (n:ℝ)^(2-2*d.holderExponent)=(n:ℝ)^2*(n:ℝ)^(-(2*d.holderExponent)) := by
    rw [show 2-2*d.holderExponent=2+(-(2*d.holderExponent)) by ring,Real.rpow_add hnR,Real.rpow_two]
  have hh := mul_le_mul_of_nonneg_right hn.le (sq_nonneg (n:ℝ))
  unfold analyticError
  rw [hePow]
  have he : ((2*Real.log 51+2*Real.log C+Real.log 2)*(n:ℝ)⁻¹+
      (12+2*C)*(Real.log (n:ℝ)/(n:ℝ))+4*(d.holderConstant:ℝ)*(n:ℝ)^(-(2*d.holderExponent)))*(n:ℝ)^2=
      (2*Real.log 51+2*Real.log C+Real.log 2)*(n:ℝ)+
        (12+2*C)*(n:ℝ)*Real.log n+4*(d.holderConstant:ℝ)*((n:ℝ)^2*(n:ℝ)^(-(2*d.holderExponent))) := by
    field_simp
    <;> ring
  rwa [he] at hh

theorem prefactor_holder_bound (C : ℝ) (hC : 0 < C) (d : DualDatum) (n : ℕ) (hn : 0 < n)
    (c : ConfluentConfig (2*n)) :
    (51*(n:ℝ)^2)^(2*n)*(C*(n:ℝ)^C)^(2*n)*Real.exp (holderError d n c.pairCount) ≤
      Real.exp (analyticError C d n) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hp := CatalanCore.Tools.Jets.confluent_pair_card (2*n) c Finset.univ
    (fun i j hij => ⟨Finset.mem_univ _,Finset.mem_univ _⟩)
  have hp' : (c.pairCount:ℝ) ≤ (n:ℝ) := by
    simp only [Finset.card_univ,Fintype.card_fin] at hp
    exact_mod_cast (show c.pairCount ≤ n by omega)
  have hlog : 0 ≤ Real.log 2+2*Real.log ((n:ℝ)^2) := by
    have hh := Real.log_nonneg (show 1 ≤ (n:ℝ)^2 by nlinarith)
    have h2 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
    linarith
  have hcast : 2*(n:ℝ)=((2*n:ℕ):ℝ) := by push_cast; ring
  have he1 : (51*(n:ℝ)^2)^(2*n)=Real.exp ((2*(n:ℝ))*(Real.log 51+2*Real.log n)) := by
    rw [hcast,Real.exp_nat_mul,Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<51),
      show (2:ℝ)*Real.log (n:ℝ)=Real.log (n:ℝ)*2 by ring,
      ← Real.rpow_def_of_pos hnR,Real.rpow_two]
  have he2 : (C*(n:ℝ)^C)^(2*n)=Real.exp ((2*(n:ℝ))*(Real.log C+C*Real.log n)) := by
    rw [hcast,Real.exp_nat_mul,Real.exp_add,Real.exp_log hC,
      show C*Real.log (n:ℝ)=Real.log (n:ℝ)*C by ring,
      ← Real.rpow_def_of_pos hnR]
  rw [he1,he2,← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  unfold analyticError holderError
  rw [Real.log_pow]
  have hh := mul_le_mul_of_nonneg_right hp' hlog
  rw [Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh ⊢
  nlinarith
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.analyticError_small
#print axioms CatalanCore.Li2.Decay.prefactor_holder_bound



namespace CatalanCore.Li2.Decay
open CatalanCore.Tools.Jets
attribute [local instance] Classical.propDecidable

theorem capped_configuration_bound (z : ℝ) (hz : ValidZ z)
    (F : CatalanCore.Li2.Uniform.DualFrame) (g : CatalanCore.Li2.Uniform.FrameGeometry F)
    (d : CatalanCore.Li2.Uniform.DualDatum) (θ ρ : ℝ) (hρ : 0 < ρ) (hF : FreeBound z F d θ) :
    ∃ K : ℕ, ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      |t| ≤ Real.exp (-ρ*(n:ℝ)) → ∀ c : AdmissibleConfig F g z n,
      ‖configWeight z n t c‖ ≤ Real.exp ((n:ℝ)^2 *
        (I d.σ+2*θ+2*latPenalty z F d.σ θ+atomPenalty z ρ d.σ θ+ε)+
          2*(n:ℝ)^2*Real.log n)*tailEnvelope z d θ K n c := by
  obtain ⟨C,hC,K,hamp⟩ := particle_amplitude_bound z hz F g ρ
  refine ⟨K,?_⟩
  intro ε hε
  have hhalf : 0 < ε/2 := by positivity
  filter_upwards [hamp,configuration_weighted_field_sum z hz F g d θ ρ hF (ε/2) hhalf,
    analyticError_small C d (ε/2) hhalf,CatalanCore.Li2.Uniform.gammaN_kernel_domain F g,
    eventually_ge_atTop (1:ℕ)] with n hna hfield herr hdom hn1
  intro t ht c
  have hn : 0 < n := by omega
  have hpre := configuration_prebound z ρ θ C hC d K n hn F g t hdom c (hna t ht c)
  have hpref := prefactor_holder_bound C hC d n hn c.confluence
  have htail : 0 ≤ tailEnvelope z d θ K n c := by
    unfold tailEnvelope
    exact Finset.prod_nonneg fun i hi => by split_ifs <;> positivity
  have hw := hfield c
  change (∑ i : Fin (2*n), weightedField z ρ θ d n (c.particle i)) ≤
    (n:ℝ)^2*(2*latPenalty z F d.σ θ+atomPenalty z ρ d.σ θ+ε/2) at hw
  let E := (n:ℝ)^2*(I d.σ+2*θ)+2*(n:ℝ)^2*Real.log n+
    (∑ i : Fin (2*n), weightedField z ρ θ d n (c.particle i))
  calc
    _ ≤ (51*(n:ℝ)^2)^(2*n)*(C*(n:ℝ)^C)^(2*n)*
      Real.exp (E+holderError d n c.confluence.pairCount)*tailEnvelope z d θ K n c := hpre
    _ = ((51*(n:ℝ)^2)^(2*n)*(C*(n:ℝ)^C)^(2*n)*
      Real.exp (holderError d n c.confluence.pairCount))*Real.exp E*tailEnvelope z d θ K n c := by
        rw [Real.exp_add]
        ring
    _ ≤ Real.exp (analyticError C d n)*Real.exp E*tailEnvelope z d θ K n c :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpref (Real.exp_pos _).le) htail
    _ = Real.exp (analyticError C d n+E)*tailEnvelope z d θ K n c := by
      simp only [Real.exp_add]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ htail
      apply Real.exp_le_exp.mpr
      dsimp only [E]
      nlinarith
end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.capped_configuration_bound



