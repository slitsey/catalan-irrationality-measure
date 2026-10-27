module
public import CatalanMeasure.GenD.Uniform.Arithmetic.Coefficient
@[expose] public section
namespace CatalanMeasure.GenD.Uniform.Arithmetic
open Polynomial CatalanMeasure.Parametric Filter
open scoped Topology
noncomputable section

/-- A universal coarse bound, independent of any gain profile certificate.
The finite certified profile theorem may improve this constant. -/
theorem denom_growth_universal (P : Parameters) (hP : Admissible P) (lb : NullityLB P)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N:ℕ in atTop,Real.log (expDenom P (denExp P lb) N:ℝ)≤
      (TwoAdic.A2 P.n0 (P.H 1) P.b0*Real.log 2+2*(P.n0:ℝ)*(P.H 1:ℝ)+ε)*(N:ℝ)^2 := by
  let f : PL.Prof := ⟨2*(P.n0:ℝ),0,[]⟩
  have heval (x:ℝ) : f.eval x=2*(P.n0:ℝ) := by simp [f,PL.Prof.eval]
  have hH : 1<P.H 1 := by
    have hn := hP.1
    have hb := hP.2.1
    have hq := hP.2.2.1
    simp only [Parameters.H,Parameters.C,Parameters.L,Parameters.n,Parameters.b,
      Parameters.q,Parameters.g,Parameters.h,Nat.mul_one]
    omega
  have hh := denom_growth P hP lb f [] (2*(P.n0:ℝ)) 0 (by
    intro N p hN hp
    rw [heval]
    have h := safeOddLoss_le_twice P N p
    have hr : (safeOddLoss P N p:ℝ)≤2*(P.n N:ℝ) := by exact_mod_cast h
    simpa [Parameters.n,Nat.cast_mul,mul_comm,mul_left_comm,mul_assoc] using hr)
    (fun x _ => heval x) hH (by simp) (by simp) (by simp) hε
  have hi : (∫x in (1:ℝ)..(P.H 1:ℝ),f.eval x)=
      ((P.H 1:ℝ)-1)*(2*(P.n0:ℝ)) := by
    simp only [heval,intervalIntegral.integral_const,smul_eq_mul]
  simpa only [hi,PrimeGrowth.totalArea,List.map_nil,List.sum_nil,sub_zero,
    show 2*(P.n0:ℝ)+((P.H 1:ℝ)-1)*(2*(P.n0:ℝ))=2*(P.n0:ℝ)*(P.H 1:ℝ) by ring] using hh

end
end CatalanMeasure.GenD.Uniform.Arithmetic
