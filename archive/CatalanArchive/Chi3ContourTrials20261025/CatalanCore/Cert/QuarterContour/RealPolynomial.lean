module
public import CatalanCore.Cert.QuarterCompute.ModelFactors
public import CatalanCore.Cert.QuarterContour.PolynomialCompiler
public import CatalanCore.Cert.QuarterContour.LogModel
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.RealPolynomial
open CatalanCore.Cert.QuarterCompute.Polynomial
open CatalanCore.Cert.QuarterCompute.ModelFactors

noncomputable def evalReal (x : ℝ) : List ℤ → ℝ
  | [] => 0
  | c::cs => (c : ℝ)+x*evalReal x cs

theorem evalReal_add (x : ℝ) (as bs : List ℤ) :
    evalReal x (add as bs) = evalReal x as+evalReal x bs := by
  induction as generalizing bs with
  | nil => simp [add,evalReal]
  | cons a as ih =>
    cases bs with
    | nil => simp [add,evalReal]
    | cons b bs => simp only [add,evalReal,ih]; push_cast; ring

theorem evalReal_scale (x : ℝ) (a : ℤ) (cs : List ℤ) :
    evalReal x (scale a cs) = (a : ℝ)*evalReal x cs := by
  induction cs with
  | nil => simp [scale,evalReal]
  | cons c cs ih =>
    simp only [scale,List.map_cons,evalReal] at *
    rw [ih]
    push_cast
    ring

theorem evalReal_quad (x : ℝ) (a b : ℤ) (cs : List ℤ) :
    evalReal x (quad a b cs) = ((a : ℝ)*x+(b : ℝ)*x^2)*evalReal x cs := by
  cases cs with
  | nil => simp [quad,evalReal]
  | cons c cs =>
    simp only [quad,evalReal_add,evalReal,evalReal_scale]
    push_cast
    ring

theorem evalReal_compose (x : ℝ) (a b : ℤ) (cs : List ℤ) :
    evalReal x (compose a b cs) = evalReal ((a : ℝ)*x+(b : ℝ)*x^2) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [compose,evalReal_add,evalReal_quad,evalReal,ih]; ring

theorem evalReal_allCoeffs (x : ℝ) (fs : List ℤ) (ps : List Jet) :
    evalReal x (allCoeffs fs ps) =
      (ps.map (fun p => (p.2.2 : ℝ)*evalReal ((p.1 : ℝ)*x+(p.2.1 : ℝ)*x^2) fs)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [allCoeffs,evalReal_add,jetCoeffs,evalReal_scale,evalReal_compose,ih,
      List.map_cons,List.sum_cons,Int.cast_natCast]

theorem factorList_eval (S : ℕ) (hS : S ≠ 0) (t : ℝ) :
    evalReal t (factorList S) = -(360360 : ℝ)*(S : ℝ)^15*LogModel.poly 15 (t/(S : ℝ)) := by
  have hs : (S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS
  norm_num [factorList,evalReal,LogModel.poly,Finset.sum_range_succ]
  field_simp
  ring

theorem normalized_for (S : ℕ) (hS : S ≠ 0) (v : ℝ) (ps : List Jet) :
    evalReal v (allCoeffs (factorList S) ps)/(denominatorFor S : ℝ) =
      -(1/2 : ℝ)*(ps.map (fun p => ((p.2.2 : ℝ)/2^32)*
        LogModel.poly 15 (((p.1 : ℝ)*v+(p.2.1 : ℝ)*v^2)/(S : ℝ)))).sum := by
  have hs : (S : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hS
  have hd : (denominatorFor S : ℝ) = (2 : ℝ)^33*(S : ℝ)^15*360360 := by
    simp only [denominatorFor,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  induction ps with
  | nil => simp [allCoeffs,evalReal]
  | cons p ps ih =>
    simp only [allCoeffs,evalReal_add,jetCoeffs,evalReal_scale,evalReal_compose,
      List.map_cons,List.sum_cons,Int.cast_natCast]
    rw [add_div,ih,factorList_eval S hS,hd]
    field_simp
    ring

theorem normalized_allCoeffs (v : ℝ) (ps : List Jet) :
    evalReal v (allCoeffs factors ps)/(denominator : ℝ) =
      -(1/2 : ℝ)*(ps.map (fun p => ((p.2.2 : ℝ)/2^32)*
        LogModel.poly 15 (((p.1 : ℝ)*v+(p.2.1 : ℝ)*v^2)/(inputScale : ℝ)))).sum := by
  exact normalized_for inputScale (by decide) v ps
end CatalanCore.Cert.QuarterContour.RealPolynomial
#print axioms CatalanCore.Cert.QuarterContour.RealPolynomial.evalReal_allCoeffs
#print axioms CatalanCore.Cert.QuarterContour.RealPolynomial.normalized_allCoeffs