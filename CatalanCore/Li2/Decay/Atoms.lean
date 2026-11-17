module
public import CatalanCore.Li2.Decay.Weight
public import CatalanCore.Li2.Port.Unified.Modular.Base.DecayMediumNodes
@[expose] public section
/-! LD10, LD11, LD26: exact residues, uniform atom growth and the zero-penalty criterion. Port factorial identities and built Stirling estimates are reused. -/
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace CatalanCore.Li2.Decay
noncomputable def residue (n j : ℕ) : ℝ :=
  (-1:ℝ)^(j-n-1)*((j-1).factorial:ℝ)^2 /
    (((j-n-1).factorial:ℝ)^3*((4*n-j).factorial:ℝ))
noncomputable def atomWeight (z : ℝ) (n j : ℕ) : ℝ := residue n j*j*z^(-(j:ℤ))
theorem residue_value (n j : ℕ) (hj : j ∈ Finset.Icc (n+1) (4*n)) :
    Dprod n (-(j:ℂ))^3 / (∏ l ∈ (Finset.Icc 1 (4*n)).erase j, (-(j:ℂ)+(l:ℂ))) = (residue n j:ℂ) := by
  have hj0 : 1 ≤ j := by have := (Finset.mem_Icc.mp hj).1; omega
  have hnj : n < j := by have := (Finset.mem_Icc.mp hj).1; omega
  have hjK : j ≤ 4*n := (Finset.mem_Icc.mp hj).2
  have hD : Dprod n (-(j:ℂ)) = (((Port.Li2.D n).eval (-(j:ℚ)) : ℚ):ℂ) := by
    rw [Port.Li2.D_eval_eq_prod]
    unfold Dprod
    push_cast
    rfl
  rw [Port.Li2.D_eval_neg_of_lt n j hnj] at hD
  push_cast at hD
  have hE : (∏ l ∈ (Finset.Icc 1 (4*n)).erase j, (-(j:ℂ)+(l:ℂ))) = (Port.Li2.eraseProd (4*n) j:ℂ) := by
    unfold Port.Li2.eraseProd
    push_cast
    apply Finset.prod_congr rfl
    intro l hl
    ring
  rw [Port.Li2.eraseProd_eq hj0 hjK] at hE
  push_cast at hE
  have hsub : j-1-n=j-n-1 := by omega
  rw [hsub] at hD
  rw [hD,hE]
  have ha : ((j-1).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j-1)
  have hb : ((j-n-1).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (j-n-1)
  have hc : ((4*n-j).factorial:ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (4*n-j)
  have hs0 : (-1:ℂ)^(j-1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hs : ((-1:ℂ)^n)^3 / (-1:ℂ)^(j-1) = (-1:ℂ)^(j-n-1) := by
    rw [div_eq_mul_inv,← inv_pow]
    norm_num only [inv_neg,inv_one]
    rw [← pow_mul,← pow_add]
    have he : n*3+(j-1)=(j-n-1)+4*n := by omega
    rw [he,pow_add,pow_mul]
    norm_num
  calc
    ((-1:ℂ)^n*(((j-1).factorial:ℂ)/((j-n-1).factorial:ℂ)))^3 /
        ((-1:ℂ)^(j-1)*((j-1).factorial:ℂ)*((4*n-j).factorial:ℂ)) =
      (((-1:ℂ)^n)^3/(-1:ℂ)^(j-1)) *
        (((j-1).factorial:ℂ)^2/(((j-n-1).factorial:ℂ)^3*((4*n-j).factorial:ℂ))) := by
          field_simp
          <;> ring
    _ = (residue n j:ℂ) := by
      rw [hs]
      simp only [residue,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,
        Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_natCast]
      ring

theorem residue_formula (n j : ℕ) (hn : 0 < n) (hj : j ∈ Finset.Icc (n+1) (4*n)) :
    Tendsto (fun u : ℂ => (u+(j:ℂ))*weight n u)
      (nhdsWithin (-(j:ℂ)) {-(j:ℂ)}ᶜ) (𝓝 (residue n j:ℂ)) := by
  let E := fun u : ℂ => ∏ l ∈ (Finset.Icc 1 (4*n)).erase j, (u+(l:ℂ))
  have hj' : j ∈ Finset.Icc 1 (4*n) := by
    have hh := Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega,hh.2⟩
  have hE0 : E (-(j:ℂ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro l hl
    have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
    have hc : (l:ℂ) ≠ (j:ℂ) := by exact_mod_cast hlj
    have he : -(j:ℂ)+(l:ℂ)=(l:ℂ)-(j:ℂ) := by ring
    rw [he]
    exact sub_ne_zero.mpr hc
  have hEc : Continuous E := by dsimp [E]; fun_prop
  have hDc : Continuous (Dprod n) := by unfold Dprod; fun_prop
  have hlim : Tendsto (fun u : ℂ => Dprod n u^3/E u)
      (nhdsWithin (-(j:ℂ)) {-(j:ℂ)}ᶜ) (𝓝 (Dprod n (-(j:ℂ))^3/E (-(j:ℂ)))) :=
    ((hDc.continuousAt.pow 3).div hEc.continuousAt hE0).tendsto.mono_left nhdsWithin_le_nhds
  have hnear : ∀ᶠ u : ℂ in nhdsWithin (-(j:ℂ)) {-(j:ℂ)}ᶜ, E u ≠ 0 :=
    (hEc.continuousAt.eventually_ne hE0).filter_mono nhdsWithin_le_nhds
  have hsame : (fun u : ℂ => (u+(j:ℂ))*weight n u) =ᶠ[nhdsWithin (-(j:ℂ)) {-(j:ℂ)}ᶜ]
      (fun u => Dprod n u^3/E u) := by
    filter_upwards [self_mem_nhdsWithin,hnear] with u hu hEu
    have hu' : u ≠ -(j:ℂ) := by simpa only [Set.mem_compl_iff,Set.mem_singleton_iff] using hu
    have huv : u+(j:ℂ) ≠ 0 := by intro hh; apply hu'; linear_combination hh
    have hprod : Dprod (4*n) u=(u+(j:ℂ))*E u := by
      unfold Dprod
      exact (Finset.mul_prod_erase _ _ hj').symm
    rw [weight,hprod]
    field_simp
  have hval := residue_value n j hj
  change Dprod n (-(j:ℂ))^3/E (-(j:ℂ))=(residue n j:ℂ) at hval
  rw [hval] at hlim
  exact hlim.congr' hsame.symm

theorem atom_penalty_zero (z ρ θ : ℝ) (d : DualDatum)
    (h : ∀ x ∈ Icc (1:ℝ) 4, omega z x-2*U d.σ (-(x:ℂ)) ≤ ρ+θ) :
    atomPenalty z ρ d.σ θ = 0 := by
  unfold atomPenalty
  calc
    (∫ x in (1:ℝ)..4, pos (A z ρ d.σ x-θ)) = ∫ _ in (1:ℝ)..4, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (1:ℝ) ≤ 4)] at hx
      have hh := h x hx
      unfold pos A
      apply max_eq_right
      linarith
    _ = 0 := by simp

theorem phi0_negative_formula (x : ℝ) :
    phi0 (-(x:ℂ)) = 2*x*Real.log x-3*(x-1)*Real.log (x-1)-
      (4-x)*Real.log (4-x)+1 := by
  have hb (b : ℝ) : (∫ y in (0:ℝ)..b, Real.log ‖-(x:ℂ)+(y:ℂ)‖) =
      (b-x)*Real.log (b-x)+x*Real.log x-b := by
    have hf : (fun y : ℝ => Real.log ‖-(x:ℂ)+(y:ℂ)‖) = (fun y => Real.log (y-x)) := by
      funext y
      have he : -(x:ℂ)+(y:ℂ)=((y-x:ℝ):ℂ) := by push_cast; ring
      rw [he,Complex.norm_real,Real.norm_eq_abs,Real.log_abs]
    rw [hf,intervalIntegral.integral_comp_sub_right,integral_log]
    simp only [zero_sub,Real.log_neg_eq_log]
    ring
  change 3*(∫ y in (0:ℝ)..1, Real.log ‖-(x:ℂ)+(y:ℂ)‖)-
    (∫ y in (0:ℝ)..4, Real.log ‖-(x:ℂ)+(y:ℂ)‖) = _
  rw [hb,hb]
  have he : 1-x=-(x-1) := by ring
  rw [he,Real.log_neg_eq_log]
  ring
private theorem scaled_xlog_div (a n : ℝ) (ha : 0 ≤ a) (hn : 0 < n) :
    n*((a/n)*Real.log (a/n))=a*Real.log a-a*Real.log n := by
  have he : n*((a/n)*Real.log (a/n))=a*Real.log (a/n) := by field_simp <;> ring
  rw [he,CatalanCore.Decay.LemmaW.mul_log_div' hn ha]
  ring
private noncomputable def atomCore (n j : ℕ) : ℝ :=
  (j.factorial:ℝ)^2/(((j-n).factorial:ℝ)^3*((4*n-j).factorial:ℝ))
private theorem atom_entropy_identity (n j : ℕ) (hn : 0 < n)
    (hj : j ∈ Finset.Icc (n+1) (4*n)) :
    (n:ℝ)*phi0 (-((j:ℂ)/(n:ℂ)))-(n:ℝ)*Real.log n =
      2*(j:ℝ)*Real.log j-3*((j-n:ℕ):ℝ)*Real.log ((j-n:ℕ):ℝ)-
        ((4*n-j:ℕ):ℝ)*Real.log ((4*n-j:ℕ):ℝ)+(n:ℝ) := by
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hnj : n ≤ j := by have hh := (Finset.mem_Icc.mp hj).1; omega
  have hjK : j ≤ 4*n := (Finset.mem_Icc.mp hj).2
  have hk : (j:ℝ)/(n:ℝ)-1=((j-n:ℕ):ℝ)/(n:ℝ) := by
    rw [Nat.cast_sub hnj]
    field_simp
  have hL : 4-(j:ℝ)/(n:ℝ)=((4*n-j:ℕ):ℝ)/(n:ℝ) := by
    rw [Nat.cast_sub hjK]
    push_cast
    field_simp
  have h0 := scaled_xlog_div (j:ℝ) n (Nat.cast_nonneg _) hnR
  have h1 := scaled_xlog_div ((j-n:ℕ):ℝ) n (Nat.cast_nonneg _) hnR
  have h2 := scaled_xlog_div ((4*n-j:ℕ):ℝ) n (Nat.cast_nonneg _) hnR
  have hp := phi0_negative_formula ((j:ℝ)/(n:ℝ))
  simp only [Complex.ofReal_div,Complex.ofReal_natCast] at hp
  rw [hp,hk,hL]
  rw [Nat.cast_sub hnj] at h1 ⊢
  rw [Nat.cast_sub hjK] at h2 ⊢
  push_cast at h2 ⊢
  nlinarith
private theorem atomCore_pos (n j : ℕ) : 0 < atomCore n j := by unfold atomCore; positivity
private theorem atomCore_log_le (n j : ℕ) (hn : 0 < n)
    (hj : j ∈ Finset.Icc (n+1) (4*n)) :
    Real.log (atomCore n j) ≤ (n:ℝ)*(phi0 (-((j:ℂ)/(n:ℂ)))-Real.log n)+Real.log j+2 := by
  have hj1 : 1 ≤ j := by have hh := (Finset.mem_Icc.mp hj).1; omega
  have hJ := CatalanCore.Zeta5.Energy.log_factorial_le hj1
  have hK := CatalanCore.Zeta5.Energy.log_factorial_ge (j-n)
  have hL := CatalanCore.Zeta5.Energy.log_factorial_ge (4*n-j)
  have he := atom_entropy_identity n j hn hj
  unfold atomCore
  rw [Real.log_div (by positivity : (j.factorial:ℝ)^2 ≠ 0)
      (by positivity : ((j-n).factorial:ℝ)^3*((4*n-j).factorial:ℝ) ≠ 0),
    Real.log_pow,Real.log_mul (by positivity : ((j-n).factorial:ℝ)^3 ≠ 0)
      (by positivity : ((4*n-j).factorial:ℝ) ≠ 0),Real.log_pow]
  have hnj : n ≤ j := by have hh := (Finset.mem_Icc.mp hj).1; omega
  have hjK : j ≤ 4*n := (Finset.mem_Icc.mp hj).2
  rw [Nat.cast_sub hnj] at hK he
  rw [Nat.cast_sub hjK] at hL he
  push_cast at hL he
  norm_num only [Nat.cast_ofNat] at *
  nlinarith
private theorem residue_mul_abs_eq (n j : ℕ) (hj : j ∈ Finset.Icc (n+1) (4*n)) :
    |residue n j*(j:ℝ)| = atomCore n j*(((j-n:ℕ):ℝ)^3/(j:ℝ)) := by
  have hj0 : j ≠ 0 := by have hh := (Finset.mem_Icc.mp hj).1; omega
  have hk0 : j-n ≠ 0 := by have hh := (Finset.mem_Icc.mp hj).1; omega
  have hjR : (j:ℝ) ≠ 0 := by exact_mod_cast hj0
  have hfj : (j.factorial:ℝ)=(j:ℝ)*((j-1).factorial:ℝ) := by exact_mod_cast (Nat.mul_factorial_pred hj0).symm
  have hfk : ((j-n).factorial:ℝ)=((j-n:ℕ):ℝ)*((j-n-1).factorial:ℝ) := by exact_mod_cast (Nat.mul_factorial_pred hk0).symm
  have ha : ((j-1).factorial:ℝ) ≠ 0 := by positivity
  have hb : ((j-n-1).factorial:ℝ) ≠ 0 := by positivity
  have hc : ((4*n-j).factorial:ℝ) ≠ 0 := by positivity
  have hkR : ((j-n:ℕ):ℝ) ≠ 0 := by exact_mod_cast hk0
  rw [abs_mul]
  simp only [residue,abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    Nat.abs_cast]
  rw [atomCore,hfj,hfk]
  field_simp
  <;> ring


private theorem atomCore_le (n j : ℕ) (hn : 0 < n) (hj : j ∈ Finset.Icc (n+1) (4*n)) :
    atomCore n j ≤ (j:ℝ)*Real.exp 2 * Real.exp ((n:ℝ)*(phi0 (-((j:ℂ)/(n:ℂ)))-Real.log n)) := by
  have hjpos : 0 < (j:ℝ) := by have hh := (Finset.mem_Icc.mp hj).1; exact_mod_cast (show 0 < j by omega)
  calc
    atomCore n j ≤ Real.exp ((n:ℝ)*(phi0 (-((j:ℂ)/(n:ℂ)))-Real.log n)+Real.log j+2) :=
      (Real.log_le_iff_le_exp (atomCore_pos n j)).mp (atomCore_log_le n j hn hj)
    _ = _ := by
      rw [Real.exp_add,Real.exp_add,Real.exp_log hjpos]
      ring
private theorem residue_mul_bound (n j : ℕ) (hn : 0 < n) (hj : j ∈ Finset.Icc (n+1) (4*n)) :
    |residue n j*(j:ℝ)| ≤ 256*Real.exp 2*(n:ℝ)^4 *
      Real.exp ((n:ℝ)*(phi0 (-((j:ℂ)/(n:ℂ)))-Real.log n)) := by
  have hj1 : 1 ≤ (j:ℝ) := by have hh := (Finset.mem_Icc.mp hj).1; exact_mod_cast (show 1 ≤ j by omega)
  have hjpos : 0 < (j:ℝ) := by linarith
  have hnj : n ≤ j := by have hh := (Finset.mem_Icc.mp hj).1; omega
  have hjK : (j:ℝ) ≤ 4*(n:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  have hk0 : 0 ≤ ((j-n:ℕ):ℝ) := Nat.cast_nonneg _
  have hkK : ((j-n:ℕ):ℝ) ≤ 4*(n:ℝ) := by rw [Nat.cast_sub hnj]; linarith [Nat.cast_nonneg n (α := ℝ)]
  have hkp : ((j-n:ℕ):ℝ)^3 ≤ (4*(n:ℝ))^3 := pow_le_pow_left₀ hk0 hkK 3
  have hpre : ((j-n:ℕ):ℝ)^3/(j:ℝ) ≤ (4*(n:ℝ))^3 := by
    apply (div_le_iff₀ hjpos).mpr
    exact hkp.trans (le_mul_of_one_le_right (by positivity) hj1)
  rw [residue_mul_abs_eq n j hj]
  calc
    atomCore n j*(((j-n:ℕ):ℝ)^3/(j:ℝ)) ≤ atomCore n j*(4*(n:ℝ))^3 :=
      mul_le_mul_of_nonneg_left hpre (atomCore_pos n j).le
    _ ≤ ((j:ℝ)*Real.exp 2 * Real.exp ((n:ℝ)*(phi0 (-((j:ℂ)/(n:ℂ)))-Real.log n)))*(4*(n:ℝ))^3 :=
      mul_le_mul_of_nonneg_right (atomCore_le n j hn hj) (by positivity)
    _ ≤ (4*(n:ℝ)*Real.exp 2 * Real.exp ((n:ℝ)*(phi0 (-((j:ℂ)/(n:ℂ)))-Real.log n)))*(4*(n:ℝ))^3 := by
      gcongr
    _ = _ := by ring
private theorem abs_zpow_eq_exp (z : ℝ) (hz : 0 < |z|) (j : ℕ) :
    |z^(-(j:ℤ))|=Real.exp (-(j:ℝ)*Real.log |z|) := by
  rw [abs_zpow,← Real.rpow_intCast,Real.rpow_def_of_pos hz]
  simp only [Int.cast_neg,Int.cast_natCast]
  congr 1
  ring

theorem atom_weight_le (z : ℝ) (hz : ValidZ z) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ j ∈ Finset.Icc (n+1) (4*n),
      |atomWeight z n j| ≤ C*(n:ℝ)^C *
        Real.exp ((n:ℝ)*(omega z ((j:ℝ)/n)-Real.log n)) := by
  let C := 256*Real.exp 2+4
  have hC : 0 < C := by dsimp [C]; positivity
  have hC4 : (4:ℝ) ≤ C := by dsimp [C]; linarith [Real.exp_pos 2]
  have hCcoef : 256*Real.exp 2 ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro n hn j hj
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have he : (n:ℝ)*(phi0 (-((j:ℂ)/(n:ℂ)))-Real.log n) + (-(j:ℝ)*Real.log |z|) =
      (n:ℝ)*(omega z ((j:ℝ)/n)-Real.log n) := by
    simp only [omega,Complex.ofReal_div,Complex.ofReal_natCast]
    field_simp
    <;> ring
  have hzexp := abs_zpow_eq_exp z hz.1 j
  have hraw : |atomWeight z n j| ≤ 256*Real.exp 2*(n:ℝ)^4 *
      Real.exp ((n:ℝ)*(omega z ((j:ℝ)/n)-Real.log n)) := by
    rw [atomWeight,abs_mul,hzexp]
    calc
      |residue n j*(j:ℝ)| *Real.exp (-(j:ℝ)*Real.log |z|) ≤
        (256*Real.exp 2*(n:ℝ)^4 * Real.exp ((n:ℝ)*(phi0 (-((j:ℂ)/(n:ℂ)))-Real.log n)))*
          Real.exp (-(j:ℝ)*Real.log |z|) := mul_le_mul_of_nonneg_right (residue_mul_bound n j hn hj) (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc,← Real.exp_add,he]
  have hp : (n:ℝ)^4 ≤ (n:ℝ)^C := by
    calc
      (n:ℝ)^(4:ℕ) = (n:ℝ)^((4:ℕ):ℝ) := (Real.rpow_natCast (n:ℝ) (4:ℕ)).symm
      _ ≤ (n:ℝ)^C := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num only [Nat.cast_ofNat]; exact hC4)
  apply hraw.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact mul_le_mul hCcoef hp (by positivity) hC.le

end CatalanCore.Li2.Decay
#print axioms CatalanCore.Li2.Decay.residue_formula
#print axioms CatalanCore.Li2.Decay.atom_penalty_zero

#print axioms CatalanCore.Li2.Decay.atomCore_log_le
#print axioms CatalanCore.Li2.Decay.residue_mul_abs_eq

#print axioms CatalanCore.Li2.Decay.atom_weight_le
