module
public import CatalanMeasure.GenD.Uniform.Arithmetic.CorrectedGrowth
public import CatalanCore.Uniform.Measure.Coefficient
@[expose] public section
namespace CatalanMeasure.GenD.Uniform.Arithmetic
open Polynomial CatalanMeasure.Parametric Filter
open scoped Topology
noncomputable section

def coefficientNormalizer {P : Parameters} (Z : Normalizer P) (N : ℕ) : ℕ :=
  (P.n N-P.g N)!*Z.D N

theorem coefficientNormalizer_clears {P : Parameters} (Z : Normalizer P)
    {N : ℕ} (hN : Z.N0≤N) :
    CatalanCore.Uniform.Clears (deltaPoly P N) (coefficientNormalizer Z N) := by
  constructor
  · exact Nat.mul_pos (Nat.factorial_pos _) (Nat.pos_of_ne_zero (Z.D_ne N))
  · intro k
    refine ⟨(Z.Q N).coeff k,?_⟩
    have h := congrArg (fun Q : ℚ[X] => Q.coeff k) (Z.Q_spec hN).1
    simp only [coeff_map,coeff_C_mul] at h
    unfold coefficientNormalizer
    push_cast
    linear_combination -h

/-- Factorial interpolation changes the logarithmic height only by o(N²). -/
theorem factorial_negligible (P : Parameters) (hn : 0<P.n0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, Real.log (((P.n N-P.g N)!:ℕ):ℝ)≤ε*(N:ℝ)^2 := by
  have hlim := linear_log_negligible (P.n0:ℝ) (P.n0:ℝ) (by exact_mod_cast hn) hε
  filter_upwards [hlim,eventually_gt_atTop (0:ℕ)] with N hlim hN
  have hpos : 0<P.n N := Nat.mul_pos hn hN
  have hfac := (Nat.factorial_le (Nat.sub_le (P.n N) (P.g N))).trans
    (Nat.factorial_le_pow (P.n N))
  have hl : Real.log (((P.n N-P.g N)!:ℕ):ℝ)≤Real.log ((P.n N:ℝ)^(P.n N)) := by
    apply Real.log_le_log (by exact_mod_cast Nat.factorial_pos _)
    exact_mod_cast hfac
  rw [Real.log_pow] at hl
  exact hl.trans (by simpa [Parameters.n,Nat.cast_mul] using hlim)

theorem coefficientNormalizer_growth {P : Parameters} (Z : Normalizer P) (G : ℝ)
    (hD : ∀ε:ℝ,0<ε→∀ᶠ N:ℕ in atTop,Real.log (Z.D N:ℝ)≤(G+ε)*(N:ℝ)^2)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N:ℕ in atTop, Real.log (coefficientNormalizer Z N:ℝ)≤(G+ε)*(N:ℝ)^2 := by
  filter_upwards [hD (ε/2) (by positivity),
    factorial_negligible P Z.adm.1 (show 0<ε/2 by positivity)] with N hd hf
  unfold coefficientNormalizer
  rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast (Nat.factorial_pos (P.n N-P.g N)).ne')
    (by exact_mod_cast Z.D_ne N)]
  linarith only [hd,hf]
end
end CatalanMeasure.GenD.Uniform.Arithmetic
