module
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Stieltjes
public import CatalanCore.Li2.DecayCert.Lattice.SelfEnergy
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
open CatalanCore.Li2.Decay CatalanCore.Zeta5.Potential
noncomputable section

def latticeLeftSeed (terms : ℕ) (s : QSegment) (phi : ℚ) : SE :=
  seAdd (seScale (s.c 0)
    (seSub (seSub (.log terms 2) (.log terms s.half.1)) (.log terms phi)))
    (seRat (((List.range (s.coeff.length-1)).map (fun k : ℕ =>
      s.c (k+1)*(-1:ℚ)^(k+1)*phi^(-(k+1:ℤ))/(k+1:ℚ))).sum))

theorem latticeLeftSeed_value (terms : ℕ) (s : QSegment) (phi : ℚ)
    (hphi : 1 < phi) (hhalf : 0 < s.half.1) (hm : s.mid.2=0) (hh : s.half.2=0)
    (hpos : ∀ x ∈ Icc (-1:ℝ) 1,0 ≤ chebF (fun k => (s.c k:ℝ)) (s.coeff.length-1) x) :
    (latticeLeftSeed terms s phi).value=
      U s.measure (((s.mid.1-s.half.1*((phi+phi⁻¹)/2):ℚ):ℝ):ℂ) := by
  rw [← LatticeGate.stieltjes_seed_value terms s phi hphi hhalf hm hh hpos]
  have hp : (0:ℝ) < (phi:ℝ) := by exact_mod_cast lt_trans zero_lt_one hphi
  have hφ : cqReal (-phi,0)= -((phi:ℝ):ℂ) := by simp [cqReal]
  have hn : cqReal (-phi,0) ≠ 0 := by rw [hφ]; exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hp.ne')
  rw [seNeg_value,segConstant_value terms s (-phi,0) hn]
  have hnorm : ‖cqReal s.half‖=(s.half.1:ℝ) := by
    simp only [cqReal,hh,Rat.cast_zero,zero_mul,add_zero,← Complex.ofReal_ratCast,Complex.norm_real,Real.norm_eq_abs]
    exact abs_of_pos (by exact_mod_cast hhalf)
  have hlog : Real.log ‖cqReal (-phi,0)/2‖=Real.log (phi:ℝ)-Real.log 2 := by
    rw [hφ,norm_div,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,Complex.norm_two,
      Real.log_div hp.ne' (by norm_num : (2:ℝ) ≠ 0)]
  have hterm (k : ℕ) :
      ((s.c (k+1):ℂ)*(cqReal (-phi,0))⁻¹^(k+1)/(k+1:ℕ)).re=
      ((s.c (k+1)*(-1:ℚ)^(k+1)*phi^(-(k+1:ℤ))/(k+1:ℚ):ℚ):ℝ) := by
    have hq : phi^(-(k+1:ℤ))=(phi⁻¹)^(k+1) := by
      rw [show (k+1:ℤ)=((k+1:ℕ):ℤ) by omega,zpow_neg,zpow_natCast,← inv_pow]
    have he : (((s.c (k+1)*(-1:ℚ)^(k+1)*phi^(-(k+1:ℤ))/(k+1:ℚ):ℚ):ℝ):ℂ)=
        (s.c (k+1):ℂ)*(cqReal (-phi,0))⁻¹^(k+1)/(k+1:ℕ) := by
      rw [hq,hφ]
      push_cast
      simp only [inv_neg,zpow_neg,zpow_natCast]
      rw [neg_pow ((phi:ℂ)⁻¹)]
      ring
    have hre := congrArg Complex.re he
    simpa only [Complex.ofReal_re] using hre.symm
  have hrc (q : ℚ) : (q:ℂ).re=(q:ℝ) := by rw [← Complex.ofReal_ratCast,Complex.ofReal_re]
  have hic (q : ℚ) : (q:ℂ).im=0 := by rw [← Complex.ofReal_ratCast,Complex.ofReal_im]
  rw [hnorm]
  simp only [Complex.sub_re,Complex.re_sum,hterm,Complex.mul_re,Complex.log_re,hrc,hic,zero_mul,sub_zero,hlog]
  simp only [latticeLeftSeed,seAdd_value,seScale_value,seSub_value,seRat_value,ScalarExpr.value,
    list_sum_map_range]
  push_cast
  ring
#print axioms latticeLeftSeed_value
end
end CatalanCore.Li2.DecayCert
