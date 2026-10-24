module
public import CatalanMeasure.Parametric.WeightedPopulationValue
public import CatalanArchive.CatalanMeasure.Parametric.TwentyParameters
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan
noncomputable section

theorem twenty_physical_one_constant {N : ℕ} (hN : 0<N) (p : ℕ) :
    populationPhysicalOneConstant twenty N p-
      (3/2:ℝ)*((p:ℝ)/(twenty.n N:ℝ))^2*Real.log 2=
    ((4/5:ℝ)-((p:ℝ)/(twenty.n N:ℝ))^2)*Real.log 2-
      ((twenty.n N:ℝ)+(p:ℝ))/(2*(twenty.n N:ℝ)^2)*Real.log 2 :=by
  have hC : 1 ≤ twenty.C N :=by rw [twenty_C];omega
  have hNR : (N:ℝ)≠0 :=by exact_mod_cast hN.ne'
  unfold populationPhysicalOneConstant populationPhysicalConstant
  rw [Nat.cast_sub hC,twenty_C]
  simp only [Parameters.n,twenty]
  push_cast
  field_simp <;> ring

theorem twenty_physical_two_constant {N : ℕ} (hN : 0<N) (p : ℕ) :
    populationPhysicalConstant twenty N p-
      (3/2:ℝ)*((p:ℝ)/(twenty.n N:ℝ))^2*Real.log 2-(1/2:ℝ)*Real.log 2=
    ((4/5:ℝ)-((p:ℝ)/(twenty.n N:ℝ))^2)*Real.log 2-
      (2*(twenty.n N:ℝ)+(p:ℝ))/(2*(twenty.n N:ℝ)^2)*Real.log 2 :=by
  have hC : 1 ≤ twenty.C N :=by rw [twenty_C];omega
  have hNR : (N:ℝ)≠0 :=by exact_mod_cast hN.ne'
  unfold populationPhysicalConstant
  rw [Nat.cast_sub hC,twenty_C]
  simp only [Parameters.n,twenty]
  push_cast
  field_simp <;> ring

theorem twenty_population_fractions {N p m : ℕ} (hN : 0<N) (hpm : p+m=twenty.n N) :
    (p:ℝ)/(twenty.n N:ℝ)+(m:ℝ)/(twenty.n N:ℝ)=1 :=by
  have hn : (twenty.n N:ℝ)≠0 :=by exact_mod_cast (n_pos twenty_admissible hN).ne'
  rw [← add_div]
  have hh : (p:ℝ)+(m:ℝ)=(twenty.n N:ℝ) :=by exact_mod_cast hpm
  rw [hh,div_self hn]

theorem twenty_physical_one_constant_le {N p m : ℕ} (hN : 0<N) (hpm : p+m=twenty.n N) :
    populationPhysicalOneConstant twenty N p-
      (3/2:ℝ)*((p:ℝ)/(twenty.n N:ℝ))^2*Real.log 2 ≤
    -(1/5:ℝ)*Real.log 2+
      (2*((m:ℝ)/(twenty.n N:ℝ))-((m:ℝ)/(twenty.n N:ℝ))^2)*Real.log 2 :=by
  rw [twenty_physical_one_constant hN]
  have hh :=twenty_population_fractions hN hpm
  have he : (4/5:ℝ)-((p:ℝ)/(twenty.n N:ℝ))^2=
      -(1/5)+2*((m:ℝ)/(twenty.n N:ℝ))-((m:ℝ)/(twenty.n N:ℝ))^2 :=by
    nlinarith only [hh]
  rw [he]
  have hnon : 0 ≤ ((twenty.n N:ℝ)+(p:ℝ))/(2*(twenty.n N:ℝ)^2)*Real.log 2 :=by
    positivity
  linarith only [hnon]

theorem twenty_physical_two_constant_le {N p m : ℕ} (hN : 0<N) (hpm : p+m=twenty.n N) :
    populationPhysicalConstant twenty N p-
      (3/2:ℝ)*((p:ℝ)/(twenty.n N:ℝ))^2*Real.log 2-(1/2:ℝ)*Real.log 2 ≤
    -(1/5:ℝ)*Real.log 2+
      (2*((m:ℝ)/(twenty.n N:ℝ))-((m:ℝ)/(twenty.n N:ℝ))^2)*Real.log 2 :=by
  rw [twenty_physical_two_constant hN]
  have hh :=twenty_population_fractions hN hpm
  have he : (4/5:ℝ)-((p:ℝ)/(twenty.n N:ℝ))^2=
      -(1/5)+2*((m:ℝ)/(twenty.n N:ℝ))-((m:ℝ)/(twenty.n N:ℝ))^2 :=by
    nlinarith only [hh]
  rw [he]
  have hnon : 0 ≤ (2*(twenty.n N:ℝ)+(p:ℝ))/(2*(twenty.n N:ℝ)^2)*Real.log 2 :=by
    positivity
  linarith only [hnon]

end
end CatalanMeasure.Parametric
