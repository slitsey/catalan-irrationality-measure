module
public import CatalanCore.Tools.Jets
public import CatalanCore.Tools.NeutralLogEnergy
public import CatalanCore.Decay.ComplexEnergy
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal NNReal
namespace CatalanCore.Tools.CappedDual
theorem occupancy_le {S J : Type*} [Fintype S] [Fintype J]
    [DecidableEq S] (site : J → S) (cap : S → ℕ) (f : S → ℝ)
    (hf : ∀ s, 0 ≤ f s)
    (hc : ∀ s, (Finset.univ.filter (fun j => site j=s)).card ≤ cap s) :
    (∑ j, f (site j)) ≤ ∑ s, (cap s:ℝ)*f s := by
  classical
  have he : (∑ s : S, ((Finset.univ.filter (fun j => site j=s)).card:ℝ)*f s)=
      ∑ j : J, f (site j) := by
    calc
      _ = ∑ s : S, ∑ j : J, if site j=s then f s else 0 := by
        simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
      _ = ∑ j : J, ∑ s : S, if site j=s then f s else 0 := Finset.sum_comm
      _ = _ := by simp
  rw [← he]
  exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (by exact_mod_cast hc s) (hf s)

theorem logPotential_upper (σ : Measure ℂ) [IsFiniteMeasure σ] (s : ℂ) (R : ℝ)
    (hR : 0 ≤ R) (hb : ∀ᵐ y ∂σ, ‖y‖ ≤ R) (hs : 1 ≤ ‖s‖+R)
    (hi : Integrable (fun y => Real.log ‖s-y‖) σ) :
    (∫ y, Real.log ‖s-y‖ ∂σ) ≤ σ.real univ*Real.log (‖s‖+R) := by
  have hh := integral_mono_ae hi (integrable_const (Real.log (‖s‖+R))) (by
    filter_upwards [hb] with y hy
    have hnorm : ‖s-y‖ ≤ ‖s‖+R := (norm_sub_le s y).trans (by linarith)
    by_cases hzero : ‖s-y‖=0
    · rw [hzero,Real.log_zero]
      exact Real.log_nonneg hs
    · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)) hnorm)
  simpa only [integral_const,smul_eq_mul] using hh
open CatalanCore.Tools.Jets

theorem sum_pairs_upper {M : ℕ} (c : ConfluentConfig M) (q : ℝ) :
    (∑ i : Fin M, ∑ j ∈ Finset.Ioi i, if (i,j) ∈ c.pairs then q else 0)=c.pairCount*q := by
  classical
  calc
    _ = ∑ i : Fin M, ∑ j : Fin M, if (i,j) ∈ c.pairs then q else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j hj hji
      apply if_neg
      intro hp
      exact hji (Finset.mem_Ioi.mpr (c.ordered (i,j) hp))
    _ = ∑ p : Fin M × Fin M, if p ∈ c.pairs then q else 0 := (Fintype.sum_prod_type (fun p : Fin M × Fin M => if p ∈ c.pairs then q else 0)).symm
    _ = c.pairCount*q := by
      rw [← Finset.sum_filter]
      have he : Finset.univ.filter (fun p : Fin M × Fin M => p ∈ c.pairs)=c.pairs := by ext p; simp
      rw [he]
      simp only [Finset.sum_const,nsmul_eq_mul,ConfluentConfig.pairCount]

theorem confluent_pair_sum_le {M : ℕ} (c : ConfluentConfig M) (L : Fin M → Fin M → ℝ)
    (q : ℝ) (hsym : ∀ i j, L i j=L j i) (hdiag : ∀ i, L i i=q)
    (hpair : ∀ i j, (i,j) ∈ c.pairs → L i j=q)
    (hother : ∀ i j, i < j → (i,j) ∉ c.pairs → Real.log ‖c.x i-c.x j‖ ≤ L i j) :
    c.redLog ≤ (∑ i, ∑ j, L i j)-(M:ℝ)*q+c.pairCount*(Real.log 2-2*q) := by
  classical
  let f : Fin M → Fin M → ℝ := fun i j => if i=j then 0 else L i j
  have hfsym : ∀ i j, f i j=f j i := by
    intro i j
    dsimp [f]
    by_cases h : i=j
    · subst j; simp
    · simp only [h,Ne.symm h,↓reduceIte,hsym]
  have hfdiag : ∀ i, f i i=0 := by intro i; simp [f]
  have hsum := CatalanCore.Decay.ComplexEnergy.sum_sym_eq f hfsym hfdiag
  have hfEq : ∀ i j, f i j=L i j-(if i=j then q else 0) := by
    intro i j
    by_cases h : i=j
    · subst j; simp [f,hdiag]
    · simp [f,h]
  have hleft : (∑ i, ∑ j, f i j)=(∑ i, ∑ j, L i j)-(M:ℝ)*q := by
    simp only [hfEq,Finset.sum_sub_distrib]
    simp
  have hright : (∑ i, ∑ j ∈ Finset.Ioi i, f i j)=∑ i, ∑ j ∈ Finset.Ioi i, L i j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact if_neg (ne_of_lt (Finset.mem_Ioi.mp hj))
  rw [hleft,hright] at hsum
  have hle : (∑ i : Fin M, ∑ j ∈ Finset.Ioi i,
      if (i,j) ∈ c.pairs then 0 else 2*Real.log ‖c.x i-c.x j‖) ≤
      (∑ i : Fin M, ∑ j ∈ Finset.Ioi i, (2*L i j-2*(if (i,j) ∈ c.pairs then q else 0))) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    by_cases hp : (i,j) ∈ c.pairs
    · simp only [hp,↓reduceIte,hpair i j hp]; linarith
    · simp only [hp,↓reduceIte,mul_zero,sub_zero]
      exact mul_le_mul_of_nonneg_left (hother i j (Finset.mem_Ioi.mp hj) hp) (by norm_num)
  simp only [Finset.sum_sub_distrib,← Finset.mul_sum] at hle
  rw [sum_pairs_upper c q] at hle
  unfold ConfluentConfig.redLog
  simp only [ConfluentConfig.pairCount] at hle ⊢
  linarith
open CatalanCore.Decay.ComplexEnergy

theorem energyC_smul (μ : Measure ℂ) (a : ℝ≥0∞) :
    energyC (a • μ)=a.toReal^2*energyC μ := by
  simp only [energyC,potC,integral_smul_measure,smul_eq_mul,integral_const_mul]
  ring

theorem circle_sum_energy {M : ℕ} (x : Fin M → ℂ) (ε : ℝ) (hε : 0 < ε) :
    energyC (∑ i, circZ (x i) ε)=
      ∑ i, ∑ j, ∫ p : ℂ × ℂ, Real.log ‖p.1-p.2‖ ∂((circZ (x i) ε).prod (circZ (x j) ε)) := by
  classical
  have hip (i j : Fin M) := integrable_circZ_circZ (x i) (x j) hε
  have hpot (s : ℂ) : potC (∑ i, circZ (x i) ε) s=∑ j, potC (circZ (x j) ε) s := by
    unfold potC
    apply integral_finsetSum_measure
    intro j hj
    exact (integrable_log_circZ (x j) hε s).congr (Filter.Eventually.of_forall fun t => by change Real.log ‖t-s‖=Real.log ‖s-t‖; rw [norm_sub_rev])
  unfold energyC
  simp_rw [hpot]
  simp only [potC]
  rw [integral_finsetSum_measure (fun i hi => integrable_finset_sum _ (fun j hj => (hip i j).integral_prod_left))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Finset.univ (fun j hj => (hip i j).integral_prod_left)]
  apply Finset.sum_congr rfl
  intro j hj
  exact (integral_prod _ (hip i j)).symm

theorem confluent_circle_sum_bound {M : ℕ} (c : ConfluentConfig M) (ε : ℝ) (hε : 0 < ε) :
    c.redLog ≤ energyC (∑ i, circZ (c.x i) ε)-(M:ℝ)*Real.log ε+
      c.pairCount*(Real.log 2-2*Real.log ε) := by
  rw [circle_sum_energy c.x ε hε]
  apply confluent_pair_sum_le c
  · intro i j
    have hh := integral_prod_swap (μ := circZ (c.x i) ε) (ν := circZ (c.x j) ε)
      (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖)
    simpa only [Prod.fst_swap,Prod.snd_swap,norm_sub_rev] using hh.symm
  · intro i
    exact pair_circZ_self (c.x i) hε (integrable_circZ_circZ _ _ hε)
  · intro i j hp
    have he : c.x i=c.x j := (c.diagonal i j (ne_of_lt (c.ordered (i,j) hp))).mpr (Or.inl hp)
    rw [he]
    exact pair_circZ_self (c.x j) hε (integrable_circZ_circZ _ _ hε)
  · intro i j hij hp
    apply pair_circZ_circZ_ge (c.x i) (c.x j) hε _ (integrable_circZ_circZ _ _ hε)
    intro he
    rcases (c.diagonal i j hij.ne).mp he with h | h
    · exact hp h
    · have hh := c.ordered (j,i) h
      exact (not_lt_of_ge hij.le) hh

theorem integrable_circle_prod_of_bounded (σ : Measure ℂ) [IsFiniteMeasure σ]
    (R : ℝ) (hb : ∀ᵐ w ∂σ, ‖w‖ ≤ R) (c : ℂ) (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) ((circZ c ε).prod σ) := by
  apply CatalanCore.Zeta5.Energy.integrable_log_prod (C := 2*Real.log (1+‖c‖+ε+R)+|Real.log ε|)
  · exact Filter.Eventually.of_forall fun w => integrable_log_circZ c hε w
  · filter_upwards [hb] with w hw
    exact integral_abs_log_circZ_le c hε w hw
end CatalanCore.Tools.CappedDual
#print axioms CatalanCore.Tools.CappedDual.occupancy_le
#print axioms CatalanCore.Tools.CappedDual.logPotential_upper
#print axioms CatalanCore.Tools.CappedDual.confluent_pair_sum_le

#print axioms CatalanCore.Tools.CappedDual.confluent_circle_sum_bound
#print axioms CatalanCore.Tools.CappedDual.energyC_smul
#print axioms CatalanCore.Tools.CappedDual.integrable_circle_prod_of_bounded
