module
public import CatalanCore.Li2.DecayCert.Lattice.MultipoleUniform
public import CatalanCore.Li2.DecayCert.Compile.Regular
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 600000
open MeasureTheory Set Filter Topology
open scoped BigOperators
open CatalanCore.Li2.Decay
namespace CatalanCore.Li2.DecayCert

theorem inverse_binomial_tail (k J : ℕ) (hk : 0<k) (u q : ℝ)
    (hq : 0≤q ∧ q<1) (hu : |u|≤q) :
    |(1+u)^(-(k:ℤ))-
      ∑ n ∈ Finset.range (J+1),((k+n-1).choose n:ℝ)*(-u)^n|≤
      (1-q)^(-(k:ℤ))-
        ∑ n ∈ Finset.range (J+1),((k+n-1).choose n:ℝ)*q^n := by
  rcases k with _|k
  · omega
  let C : ℕ→ℝ := fun n => ((n+k).choose k:ℝ)
  let f : ℕ→ℝ := fun n => C n*(-u)^n
  let g : ℕ→ℝ := fun n => C n*q^n
  have hu1 : ‖-u‖<1 := by rw [Real.norm_eq_abs,abs_neg]; exact hu.trans_lt hq.2
  have hq1 : ‖q‖<1 := by rw [Real.norm_eq_abs,abs_of_nonneg hq.1]; exact hq.2
  have hf : HasSum f (1/(1-(-u))^(k+1)) := hasSum_choose_mul_geometric_of_norm_lt_one k hu1
  have hg : HasSum g (1/(1-q)^(k+1)) := hasSum_choose_mul_geometric_of_norm_lt_one k hq1
  have hfTail : HasSum (fun n => f (n+(J+1)))
      (1/(1-(-u))^(k+1)-∑ n ∈ Finset.range (J+1),f n) :=
    (hasSum_nat_add_iff' (J+1)).2 hf
  have hgTail : HasSum (fun n => g (n+(J+1)))
      (1/(1-q)^(k+1)-∑ n ∈ Finset.range (J+1),g n) :=
    (hasSum_nat_add_iff' (J+1)).2 hg
  have hbound (n : ℕ) : ‖f (n+(J+1))‖≤g (n+(J+1)) := by
    dsimp only [f,g]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_pow,abs_neg]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg u) hu _) (Nat.cast_nonneg _)
  have h := hfTail.norm_le_of_bounded hgTail hbound
  have hC (n : ℕ) : ((k+1+n-1).choose n:ℝ)=C n := by
    dsimp only [C]
    have hidx : k+1+n-1=n+k := by omega
    rw [hidx,Nat.choose_symm_add]
  simp only [zpow_neg,zpow_natCast,one_div,sub_neg_eq_add,Real.norm_eq_abs] at h ⊢
  simp_rw [hC]
  exact h

#print axioms inverse_binomial_tail
noncomputable def invPowerTaylor (d : ℝ) (k J : ℕ) : List ℝ :=
  (List.range (J+1)).map (fun j : ℕ =>
    (-1:ℝ)^j*((k+j-1).choose j:ℝ)/d^(k+j))

noncomputable def invPowerTail (d r : ℝ) (k J : ℕ) : ℝ :=
  d^(-(k:ℤ))*((1-r/d)^(-(k:ℤ))-
    ∑ j ∈ Finset.range (J+1),((k+j-1).choose j:ℝ)*(r/d)^j)

theorem inverse_real_taylor_model (d r : ℝ) (hd : 0<d) (hr : 0≤r) (hrt : r<d)
    (k J : ℕ) (hk : 0<k) :
    Models (fun u => (d+u)^(-(k:ℤ))) (invPowerTaylor d k J) r (invPowerTail d r k J) := by
  have hq0 : 0≤r/d := div_nonneg hr hd.le
  have hq1 : r/d<1 := (div_lt_one hd).mpr hrt
  have hnon := inverse_binomial_tail k J hk 0 (r/d) ⟨hq0,hq1⟩ (by simpa using hq0)
  have htail0 : 0≤(1-r/d)^(-(k:ℤ))-
      ∑ j ∈ Finset.range (J+1),((k+j-1).choose j:ℝ)*(r/d)^j :=
    (abs_nonneg _).trans hnon
  have hdk : 0≤d^(-(k:ℤ)) := (zpow_pos hd _).le
  refine ⟨hr,mul_nonneg hdk htail0,?_⟩
  intro u hu
  have huv : |u/d|≤r/d := by rw [abs_div,abs_of_pos hd]; exact div_le_div_of_nonneg_right hu hd.le
  have hb := inverse_binomial_tail k J hk (u/d) (r/d) ⟨hq0,hq1⟩ huv
  have he (j : ℕ) : (-1:ℝ)^j*((k+j-1).choose j:ℝ)/d^(k+j)*u^j=
      d^(-(k:ℤ))*(((k+j-1).choose j:ℝ)*(-(u/d))^j) := by
    rw [neg_pow (u/d) j]
    simp only [zpow_neg,zpow_natCast,div_pow,pow_add]
    ring
  have hpoly : evalModel (invPowerTaylor d k J) u=
      d^(-(k:ℤ))*(∑ j ∈ Finset.range (J+1),((k+j-1).choose j:ℝ)*(-(u/d))^j) := by
    rw [invPowerTaylor,evalModel_range,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j hj => he j)
  have harg : d+u=d*(1+u/d) := by field_simp <;> ring
  dsimp only []
  rw [hpoly,harg,mul_zpow,← mul_sub,abs_mul,abs_of_nonneg hdk]
  exact mul_le_mul_of_nonneg_left hb hdk

#print axioms inverse_real_taylor_model
theorem log_real_taylor_model (d r : ℝ) (hd : 0<d) (hr : 0≤r) (hrt : r<d) (J : ℕ) :
    Models (fun u => Real.log |d+u|)
      ((List.range (J+1)).map (logAffineCoeff (d:ℂ) 1)) r
      ((r/d)^(J+1)/((J+1:ℕ)*(1-r/d))) := by
  have hsep : ‖(1:ℂ)‖*r<‖(d:ℂ)‖ := by simpa [abs_of_pos hd] using hrt
  have h := logAffine_taylor_remainder (d:ℂ) 1 r hr hsep J
  simpa only [one_mul,← Complex.ofReal_add,Complex.norm_real,Real.norm_eq_abs,
    norm_one,abs_of_pos hd] using h

theorem mp_real (σ : Measure ℂ) (y0 x : ℝ) (K : ℕ) :
    mp σ (y0:ℂ) (x:ℂ) K= -σ.real univ*Real.log |x-y0|+
      ∑ k ∈ Finset.range K, (moment σ (y0:ℂ) (k+1)).re/
        (((k+1:ℕ):ℝ)*(x-y0)^(k+1)) := by
  unfold mp
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,Complex.re_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hd : (((k+1:ℕ):ℂ)*((x-y0:ℝ):ℂ)^(k+1))=
      ((((k+1:ℕ):ℝ)*(x-y0)^(k+1):ℝ):ℂ) := by push_cast; rfl
  rw [hd,Complex.div_ofReal_re]

noncomputable def mpTaylorCoeffs (σ : Measure ℂ) (y0 p : ℝ) (K J : ℕ) : List ℝ :=
  let d := p-y0
  (List.range (J+1)).map (fun j : ℕ =>
    -σ.real univ*logAffineCoeff (d:ℂ) 1 j+
      ∑ k ∈ Finset.range K,(moment σ (y0:ℂ) (k+1)).re/((k+1:ℕ):ℝ)*
        ((-1:ℝ)^j*((k+1+j-1).choose j:ℝ)/d^(k+1+j)))

noncomputable def mpTaylorError (σ : Measure ℂ) (y0 H p r : ℝ) (K J : ℕ) : ℝ :=
  let d := p-y0
  σ.real univ*(r/d)^(J+1)/((J+1:ℕ)*(1-r/d))+
    (∑ k ∈ Finset.range K, |(moment σ (y0:ℂ) (k+1)).re/((k+1:ℕ):ℝ)| *
      invPowerTail d r (k+1) J)+mpErr (σ.real univ) (H/(d-r)) K

theorem evalModel_mpTaylorCoeffs (σ : Measure ℂ) (y0 p : ℝ) (K J : ℕ) (u : ℝ) :
    evalModel (mpTaylorCoeffs σ y0 p K J) u=
      -σ.real univ*evalModel ((List.range (J+1)).map (logAffineCoeff ((p-y0:ℝ):ℂ) 1)) u+
      ∑ k ∈ Finset.range K,(moment σ (y0:ℂ) (k+1)).re/((k+1:ℕ):ℝ)*
        evalModel (invPowerTaylor (p-y0) (k+1) J) u := by
  simp only [mpTaylorCoeffs,invPowerTaylor,evalModel_range]
  simp_rw [add_mul,Finset.sum_add_distrib,Finset.sum_mul,Finset.mul_sum]
  apply congrArg₂ (·+·)
  · apply Finset.sum_congr rfl
    intro j hj
    ring
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    ring

#print axioms log_real_taylor_model
#print axioms mp_real
#print axioms evalModel_mpTaylorCoeffs
noncomputable def mpTaylorBaseError (σ : Measure ℂ) (y0 p r : ℝ) (K J : ℕ) : ℝ :=
  let d := p-y0
  σ.real univ*(r/d)^(J+1)/((J+1:ℕ)*(1-r/d))+
    ∑ k ∈ Finset.range K, |(moment σ (y0:ℂ) (k+1)).re/((k+1:ℕ):ℝ)| *
      invPowerTail d r (k+1) J

theorem finite_mp_taylor_model (σ : Measure ℂ) (y0 p r : ℝ)
    (hr : 0≤r) (hsep : r<p-y0) (K J : ℕ) :
    Models (fun u => mp σ (y0:ℂ) ((p+u:ℝ):ℂ) K)
      (mpTaylorCoeffs σ y0 p K J) r (mpTaylorBaseError σ y0 p r K J) := by
  let d := p-y0
  let m := σ.real univ
  let w : ℕ→ℝ := fun k => (moment σ (y0:ℂ) (k+1)).re/((k+1:ℕ):ℝ)
  have hd : 0<d := hr.trans_lt hsep
  have hm : 0≤m := ENNReal.toReal_nonneg
  have hlog := log_real_taylor_model d r hd hr hsep J
  have hinv (k : ℕ) := inverse_real_taylor_model d r hd hr hsep (k+1) J (by omega)
  have he0 : 0≤mpTaylorBaseError σ y0 p r K J := by
    change 0≤m*(r/d)^(J+1)/((J+1:ℕ)*(1-r/d))+
      ∑ k ∈ Finset.range K,|w k| *invPowerTail d r (k+1) J
    have hl0 := mul_nonneg hm hlog.2.1
    rw [mul_div_assoc]
    exact add_nonneg hl0 (Finset.sum_nonneg (fun k hk => mul_nonneg (abs_nonneg _) (hinv k).2.1))
  refine ⟨hr,he0,?_⟩
  intro u hu
  let L := evalModel ((List.range (J+1)).map (logAffineCoeff (d:ℂ) 1)) u
  let V : ℕ→ℝ := fun k => evalModel (invPowerTaylor d (k+1) J) u
  have hEq : mp σ (y0:ℂ) ((p+u:ℝ):ℂ) K-evalModel (mpTaylorCoeffs σ y0 p K J) u=
      -m*(Real.log |d+u|-L)+∑ k ∈ Finset.range K,w k*((d+u)^(-((k+1:ℕ):ℤ))-V k) := by
    rw [mp_real,evalModel_mpTaylorCoeffs]
    have harg : p+u-y0=d+u := by dsimp only [d]; ring
    rw [harg]
    have hs : (∑ k ∈ Finset.range K,(moment σ (y0:ℂ) (k+1)).re/
        (((k+1:ℕ):ℝ)*(d+u)^(k+1)))=
        ∑ k ∈ Finset.range K,w k*(d+u)^(-((k+1:ℕ):ℤ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [w]
      simp only [zpow_neg,zpow_natCast,div_mul_eq_div_div]
      ring
    rw [hs]
    simp_rw [mul_sub,Finset.sum_sub_distrib]
    change -m*Real.log |d+u|+(∑ k ∈ Finset.range K,w k*(d+u)^(-((k+1:ℕ):ℤ)))-
      (-m*L+∑ k ∈ Finset.range K,w k*V k)=_
    ring
  have hl : |-m*(Real.log |d+u|-L)|≤m*((r/d)^(J+1)/((J+1:ℕ)*(1-r/d))) := by
    rw [abs_mul,abs_neg,abs_of_nonneg hm]
    exact mul_le_mul_of_nonneg_left (hlog.2.2 u hu) hm
  have hi (k : ℕ) (hk : k∈Finset.range K) :
      |w k*((d+u)^(-((k+1:ℕ):ℤ))-V k)|≤|w k| *invPowerTail d r (k+1) J := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hinv k).2.2 u hu) (abs_nonneg _)
  rw [hEq]
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hi)
  have h := (abs_add_le (-m*(Real.log |d+u|-L))
    (∑ k ∈ Finset.range K,w k*((d+u)^(-((k+1:ℕ):ℤ))-V k))).trans (add_le_add hl hsum)
  exact h.trans_eq (by dsimp only [mpTaylorBaseError,d,m,w]; ring)

#print axioms finite_mp_taylor_model
/-- Actual source potential, with the finite MP Taylor tail and the shared S06 source tail. -/
theorem logPot_far_macro_model (σ : Measure ℂ) [IsFiniteMeasure σ]
    (y0 H p r : ℝ) (hH : 0≤H) (hr : 0≤r)
    (hs : σ {s | s.im ≠ 0 ∨ H<‖s-(y0:ℂ)‖}=0)
    (hsep : H<p-y0-r) (K J : ℕ) :
    Models (fun u => U σ ((p+u:ℝ):ℂ))
      (mpTaylorCoeffs σ y0 p K J) r (mpTaylorError σ y0 H p r K J) := by
  let d := p-y0
  have hrt : r<d := by dsimp only [d]; linarith
  have hbase := finite_mp_taylor_model σ y0 p r hr hrt K J
  have hball : σ {s | H<‖s-(y0:ℂ)‖}=0 :=
    measure_mono_null (by intro s hs'; exact Or.inr hs') hs
  have hdm : 0<d-r := hH.trans_lt hsep
  have hratio0 : 0≤H/(d-r) := div_nonneg hH hdm.le
  have hratiolt : H/(d-r)<1 := (div_lt_one hdm).mpr hsep
  have hE : 0≤mpErr (σ.real univ) (H/(d-r)) K := by
    unfold mpErr
    exact div_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hratio0 _))
      (mul_nonneg (by positivity) (sub_nonneg.mpr hratiolt.le))
  have herror : mpTaylorError σ y0 H p r K J=
      mpTaylorBaseError σ y0 p r K J+mpErr (σ.real univ) (H/(d-r)) K := rfl
  refine ⟨hr,?_,?_⟩
  · rw [herror]
    exact add_nonneg hbase.2.1 hE
  · intro u hu
    have hends : p-r≤p+r := by linarith
    have hsepa : H<(p-r)-y0 := by linarith
    have hp := logPot_multipole_uniform_right σ y0 H (p-r) (p+r) hH hball hsepa hends K
    have hpoint := hp (p+u) ⟨by linarith [(abs_le.mp hu).1],by linarith [(abs_le.mp hu).2]⟩
    have heq : (p-r)-y0=d-r := by dsimp only [d]; ring
    rw [heq] at hpoint
    have hfinite := hbase.2.2 u hu
    dsimp only [] at hfinite ⊢
    exact (abs_sub_le _ _ _).trans ((add_le_add hpoint hfinite).trans_eq
      (by rw [herror]; ring))

#print axioms logPot_far_macro_model
end CatalanCore.Li2.DecayCert
