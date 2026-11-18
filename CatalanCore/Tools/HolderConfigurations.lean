module
public import CatalanCore.Tools.CappedDual
public import CatalanCore.Tools.NeutralLogEnergy
@[expose] public section
set_option Elab.async false
open MeasureTheory Set Filter
open scoped Topology BigOperators ENNReal
open CatalanCore.Tools.Jets CatalanCore.Decay.ComplexEnergy CatalanCore.Zeta5.Energy
namespace CatalanCore.Tools.HolderConfigurations
theorem circle_pair_potential_le (σ : Measure ℂ) [IsFiniteMeasure σ]
    (R H α : ℝ) (hb : ∀ᵐ w ∂σ, ‖w‖ ≤ R)
    (hholder : ∀ u v : ℂ, |potC σ u-potC σ v| ≤ H*‖u-v‖^α)
    (c : ℂ) (ε : ℝ) (hε : 0 < ε) :
    (∫ p : ℂ × ℂ, Real.log ‖p.1-p.2‖ ∂((circZ c ε).prod σ)) ≤
      potC σ c+H*ε^α := by
  have hint := CatalanCore.Tools.CappedDual.integrable_circle_prod_of_bounded
    σ R hb c ε hε
  rw [integral_prod _ hint]
  have hi : Integrable (fun w => potC σ w) (circZ c ε) := hint.integral_prod_left
  have hh := integral_mono_ae hi (integrable_const (potC σ c+H*ε^α)) (by
    filter_upwards [ae_dist_circZ c hε] with w hw
    have h := hholder w c
    have he : ‖w-c‖=ε := by rw [norm_sub_rev]; exact hw
    rw [he] at h
    have hh := le_abs_self (potC σ w-potC σ c)
    linarith)
  simpa only [potC,integral_const,smul_eq_mul,probReal_univ,one_mul] using hh

theorem holder_circle_bound {M : ℕ} (K : ℝ) (hK : 0 < K) (c : ConfluentConfig M)
    (σ : Measure ℂ) [IsFiniteMeasure σ] (R H α : ℝ) (hR0 : 0 ≤ R)
    (hb : ∀ᵐ w ∂σ, ‖w‖ ≤ R)
    (hself : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) (σ.prod σ))
    (hatom : ∀ w : ℂ, σ {w}=0)
    (hholder : ∀ u v : ℂ, |potC σ u-potC σ v| ≤ H*‖u-v‖^α)
    (hsize : (M:ℝ)=K*σ.real univ) (ε : ℝ) (hε : 0 < ε) :
    c.redLog ≤ 2*K*(∑ i, (potC σ (c.x i)+H*ε^α))-K^2*energyC σ-
      (M:ℝ)*Real.log ε+c.pairCount*(Real.log 2-2*Real.log ε) := by
  classical
  let m : Option (Fin M) → Measure ℂ := cfgZ σ c.x ε
  let s : Option (Fin M) → ℝ := fun o => o.elim (-1) (fun _ => 1/K)
  have hR : ∀ k, ∀ᵐ w ∂(m k), ‖w‖ ≤ R+ε+∑ i, ‖c.x i‖ := by
    intro k
    cases k with
    | none =>
      filter_upwards [hb] with w hw
      have hh : 0 ≤ ∑ i, ‖c.x i‖ := Finset.sum_nonneg fun i hi => norm_nonneg _
      linarith
    | some i =>
      filter_upwards [ae_norm_circZ (c.x i) ε] with w hw
      have hh : ‖c.x i‖ ≤ ∑ j, ‖c.x j‖ := Finset.single_le_sum
        (f := fun j => ‖c.x j‖) (fun j hj => norm_nonneg _) (Finset.mem_univ i)
      rw [abs_of_pos hε] at hw
      linarith [hR0]
  have hmass : ∑ k, s k*(m k).real univ=0 := by
    rw [Fintype.sum_option]
    simp only [s,m,cfgZ,Option.elim,probReal_univ,mul_one,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
    rw [hsize]
    field_simp
    <;> ring
  have hint : ∀ k l, Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) ((m k).prod (m l)) := by
    intro k l
    cases k <;> cases l <;> simp only [m,cfgZ]
    · exact hself
    · exact integrable_log_swap (CatalanCore.Tools.CappedDual.integrable_circle_prod_of_bounded σ R hb _ ε hε)
    · exact CatalanCore.Tools.CappedDual.integrable_circle_prod_of_bounded σ R hb _ ε hε
    · exact integrable_circZ_circZ _ _ hε
  have hae : ∀ k l, ∀ᵐ p ∂((m k).prod (m l)), p.1 ≠ p.2 := by
    intro k l
    cases l with
    | none => exact ae_ne_of_noAtoms_right hatom
    | some j => exact ae_ne_of_noAtoms_right (circZ_singleton _ hε.ne')
  have hE := neg_nonneg.mp (CatalanCore.Tools.neutral_log_energy_nonneg (s := s) hR hmass hint hae)
  let L : Fin M → Fin M → ℝ := fun i j =>
    pairInt m (fun z w => Real.log ‖z-w‖) (some i) (some j)
  let Q : Fin M → ℝ := fun i => pairInt m (fun z w => Real.log ‖z-w‖) (some i) none
  have hQle : ∀ i, Q i ≤ potC σ (c.x i)+H*ε^α := by
    intro i
    exact circle_pair_potential_le σ R H α hb hholder (c.x i) ε hε
  have hnn : pairInt m (fun z w => Real.log ‖z-w‖) none none=energyC σ := by
    change (∫ p : ℂ × ℂ, Real.log ‖p.1-p.2‖ ∂(σ.prod σ))=energyC σ
    rw [integral_prod _ hself]
    rfl
  have hnS : ∀ i, pairInt m (fun z w => Real.log ‖z-w‖) none (some i)=Q i := by
    intro i
    exact pairInt_swap m (some i) none
  unfold energy at hE
  rw [Fintype.sum_option] at hE
  simp only [Fintype.sum_option,hnn,hnS,← show ∀ i j, L i j=pairInt m (fun z w => Real.log ‖z-w‖) (some i) (some j) from fun _ _ => rfl,
    ← show ∀ i, Q i=pairInt m (fun z w => Real.log ‖z-w‖) (some i) none from fun _ => rfl,s,Option.elim] at hE
  rw [Finset.sum_add_distrib] at hE
  have e1 : ∑ i, (-1:ℝ)*(1/K)*Q i= -(1/K)*∑ i, Q i := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
  have e2 : ∑ i, (1/K)*(-1:ℝ)*Q i= -(1/K)*∑ i, Q i := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring
  have e3 : ∑ i, ∑ j, (1/K)*(1/K)*L i j=(1/K)^2*∑ i, ∑ j, L i j := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; ring
  have hE' : energyC σ-2*(1/K)*∑ i, Q i+(1/K)^2*∑ i, ∑ j, L i j ≤ 0 := by
    linarith [hE,e1,e2,e3]
  have hQsum : (∑ i, Q i) ≤ ∑ i, (potC σ (c.x i)+H*ε^α) :=
    Finset.sum_le_sum fun i hi => hQle i
  have hmult := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg K) hE'
  have he : K^2*(energyC σ-2*(1/K)*∑ i, Q i+(1/K)^2*∑ i, ∑ j, L i j)=
      K^2*energyC σ-2*K*(∑ i, Q i)+(∑ i, ∑ j, L i j) := by field_simp <;> ring
  rw [he] at hmult
  have hcircle := CatalanCore.Tools.CappedDual.confluent_circle_sum_bound c ε hε
  rw [CatalanCore.Tools.CappedDual.circle_sum_energy c.x ε hε] at hcircle
  change c.redLog ≤ (∑ i, ∑ j, L i j)-(M:ℝ)*Real.log ε+
    c.pairCount*(Real.log 2-2*Real.log ε) at hcircle
  have hh := mul_le_mul_of_nonneg_left hQsum (show 0 ≤ 2*K by positivity)
  linarith
end CatalanCore.Tools.HolderConfigurations
#print axioms CatalanCore.Tools.HolderConfigurations.holder_circle_bound
