module
public import CatalanArchive.CatalanMeasure.Parametric.TwentyUniformEnergy
public import CatalanMeasure.Parametric.TwentyRestrictedWeights
@[expose] public section
namespace CatalanMeasure.Parametric
open OAI.InternalCatalan Set Finset
open scoped BigOperators
noncomputable section

/-- Common factors are cancelled jointly with the quadrature weights. -/
theorem product_weights_of_log {m : ℕ} {M B L : ℝ} (c w : Fin m → ℝ)
    (hM : 0<M) (hc : ∀ i,0<c i) (hL : 0≤L)
    (hlog : Real.log M-∑ i,Real.log (c i) ≤ B)
    (hw : ∀ i,c i*|w i| ≤ L) :
    M*(∏ i,|w i|) ≤ Real.exp B*L^m :=by
  have hcp : 0<∏ i,c i :=prod_pos (fun i _ =>hc i)
  have hclog : Real.log (∏ i,c i)=∑ i,Real.log (c i) :=
    Real.log_prod (fun i _ =>(hc i).ne')
  have hh : Real.log M ≤ B+Real.log (∏ i,c i) :=by
    rw [hclog]
    linarith only [hlog]
  have hbase :=Real.exp_le_exp.mpr hh
  rw [Real.exp_log hM,Real.exp_add,Real.exp_log hcp] at hbase
  calc
    _ ≤ (Real.exp B*(∏ i,c i))*(∏ i,|w i|) :=
      mul_le_mul_of_nonneg_right hbase (prod_nonneg (fun i _ =>abs_nonneg _))
    _ = Real.exp B*(∏ i,c i*|w i|) :=by rw [prod_mul_distrib];ring
    _ ≤ Real.exp B*(∏ _i : Fin m,L) :=by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact prod_le_prod₀ (fun i _ =>mul_nonneg (hc i).le (abs_nonneg _)) (fun i _ =>hw i)
    _ = _ :=by simp

/-- The actual restricted weights and uniform energy give the coefficient119,
    before subquadratic combinatorial factors are absorbed. -/
theorem twenty_weighted_population_product_bound {N m : ℕ} (hN : 0<N)
    (M δ : ℝ) (y : Fin m → ℝ) (k : Fin m → ℕ) (a : Fin m → Fin (18*N))
    (hcoord : ∀ j,realCoordinateInv (y j)=CatalanMeasure.chebNode (18*N) (a j))
    (hM : 0<M)
    (hlog : Real.log M-∑ j,populationCommonLog twenty N (y j) ≤
      (twenty.n N:ℝ)^2*(-twentyDualTarget+Real.log 2/2+
        (43/10)*((m:ℝ)/(twenty.n N:ℝ))+δ)) :
    M*(∏ j,|restrictedWeight twenty N (k j) (CatalanMeasure.chebNode (18*N)) (a j)|) ≤
      (54000*(N:ℝ))^m*Real.exp ((20*(N:ℝ))^2*(-twentyDualTarget+Real.log 2/2+δ)+119*N*m) :=by
  let c : Fin m → ℝ :=fun j =>|(rowCommonFactor twenty N).eval (realCoordinateInv (y j))|
  let w : Fin m → ℝ :=fun j =>restrictedWeight twenty N (k j) (CatalanMeasure.chebNode (18*N)) (a j)
  have hc : ∀ j,0<c j :=by
    intro j
    dsimp only [c]
    rw [hcoord j]
    exact abs_pos.mpr (rowCommonFactor_eval_ne_zero twenty N (CatalanMeasure.chebNode_mem (a j)).2)
  have hw : ∀ j,c j*|w j| ≤ 54000*N*(TwentyCircle.twentyCircleK:ℝ)^N :=by
    intro j
    dsimp only [c,w]
    rw [hcoord j]
    exact twenty_restrictedWeight_joint_le N (k j) (a j)
  have hK : (TwentyCircle.twentyCircleK:ℝ)^N ≤ Real.exp (33*(N:ℝ)) :=by
    calc
      _ ≤ Real.exp 33 ^N :=pow_le_pow_left₀ (by norm_num [TwentyCircle.twentyCircleK]) TwentyCircle.twentyCircleK_le_exp N
      _ = _ :=by rw [← Real.exp_nat_mul];congr 1;ring
  have hw' : ∀ j,c j*|w j| ≤ 54000*N*Real.exp (33*N) :=fun j =>
    (hw j).trans (mul_le_mul_of_nonneg_left hK (by positivity))
  have hh :=product_weights_of_log c w hM hc (by positivity) hlog hw'
  have hn : (twenty.n N:ℝ)≠0 :=by exact_mod_cast (n_pos twenty_admissible hN).ne'
  have hnu : (twenty.n N:ℝ)=20*(N:ℝ) :=by simp [Parameters.n,twenty]
  have he : (twenty.n N:ℝ)^2*(-twentyDualTarget+Real.log 2/2+
      (43/10)*((m:ℝ)/(twenty.n N:ℝ))+δ)+33*(N:ℝ)*m=
      (20*(N:ℝ))^2*(-twentyDualTarget+Real.log 2/2+δ)+119*N*m :=by
    rw [hnu] at hn ⊢
    field_simp
    ring
  calc
    _ ≤ Real.exp ((twenty.n N:ℝ)^2*(-twentyDualTarget+Real.log 2/2+
        (43/10)*((m:ℝ)/(twenty.n N:ℝ))+δ))*(54000*N*Real.exp (33*N))^m :=hh
    _ = _ :=by
      rw [mul_pow,← Real.exp_nat_mul]
      have hex : Real.exp ((twenty.n N:ℝ)^2*(-twentyDualTarget+Real.log 2/2+
          (43/10)*((m:ℝ)/(twenty.n N:ℝ))+δ))*Real.exp ((m:ℝ)*(33*N))=
          Real.exp ((20*(N:ℝ))^2*(-twentyDualTarget+Real.log 2/2+δ)+119*N*m) :=by
        rw [← Real.exp_add]
        congr 1
        convert he using 1 <;> ring
      calc
        _ = (54000*(N:ℝ))^m*(Real.exp ((twenty.n N:ℝ)^2*(-twentyDualTarget+Real.log 2/2+
            (43/10)*((m:ℝ)/(twenty.n N:ℝ))+δ))*Real.exp ((m:ℝ)*(33*N))) :=by ring
        _ = _ :=by rw [hex]

end
end CatalanMeasure.Parametric
