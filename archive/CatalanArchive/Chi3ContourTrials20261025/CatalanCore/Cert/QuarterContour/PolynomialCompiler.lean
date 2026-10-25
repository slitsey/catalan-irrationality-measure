module
public import CatalanCore.Cert.QuarterCompute.PolynomialOps
public import CatalanCore.Cert.QuarterContour.PackedPolynomial
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.PackedPolynomial
open CatalanCore.Cert.QuarterCompute.Polynomial

theorem eval_add (B : ℤ) (xs ys : List ℤ) : eval B (add xs ys) = eval B xs+eval B ys := by
  induction xs generalizing ys with
  | nil => simp [add,eval]
  | cons x xs ih =>
    cases ys with
    | nil => simp [add,eval]
    | cons y ys => simp only [add,eval,ih]; ring

theorem eval_scale (B a : ℤ) (cs : List ℤ) : eval B (scale a cs) = a*eval B cs := by
  induction cs with
  | nil => simp [scale,eval]
  | cons c cs ih =>
    simp only [scale,List.map_cons,eval] at *
    rw [ih]
    ring

theorem eval_quad (B a b : ℤ) (cs : List ℤ) :
    eval B (quad a b cs) = (a*B+b*B^2)*eval B cs := by
  cases cs with
  | nil => simp [quad,eval]
  | cons c cs =>
    simp only [quad,eval_add,eval,eval_scale]
    ring

theorem eval_compose (B a b : ℤ) (cs : List ℤ) :
    eval B (compose a b cs) = eval (a*B+b*B^2) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [compose,eval_add,eval_quad,eval,ih]; ring

theorem eval_allCoeffs (B : ℤ) (factors : List ℤ) (ps : List Jet) :
    eval B (allCoeffs factors ps) = packedSum factors B ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [allCoeffs,eval_add,jetCoeffs,eval_scale,eval_compose,ih,packedSum]

theorem mass_add (xs ys : List ℤ) : mass (add xs ys) ≤ mass xs+mass ys := by
  induction xs generalizing ys with
  | nil => simp [add,mass]
  | cons x xs ih =>
    cases ys with
    | nil => simp [add,mass]
    | cons y ys =>
      simp only [add,mass]
      have h := ih ys
      have ha := Int.natAbs_add_le x y
      omega

theorem mass_scale (a : ℤ) (cs : List ℤ) : mass (scale a cs) = a.natAbs*mass cs := by
  induction cs with
  | nil => simp [scale,mass]
  | cons c cs ih =>
    simp only [scale,List.map_cons,mass,Int.natAbs_mul] at *
    rw [ih,Nat.mul_add]

theorem mass_quad (a b : ℤ) (cs : List ℤ) :
    mass (quad a b cs) ≤ (a.natAbs+b.natAbs)*mass cs := by
  cases cs with
  | nil => simp [quad,mass]
  | cons c cs =>
    have h := mass_add (0::scale a (c::cs)) (0::0::scale b (c::cs))
    simpa only [quad,mass,Int.natAbs_zero,Nat.zero_add,mass_scale,Nat.add_mul] using h

theorem mass_compose (a b : ℤ) (S : ℕ) (hs : a.natAbs+b.natAbs ≤ S) (cs : List ℤ) :
    mass (compose a b cs) ≤ evalNat S cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have h1 := mass_add [c] (quad a b (compose a b cs))
    have h2 := mass_quad a b (compose a b cs)
    have h3 := Nat.mul_le_mul hs ih
    simp only [compose,evalNat,mass] at h1 ⊢
    omega

theorem mass_allCoeffs (S : ℕ) (factors : List ℤ) (ps : List Jet)
    (hs : ∀ p ∈ ps, p.1.natAbs+p.2.1.natAbs ≤ S) :
    mass (allCoeffs factors ps) ≤ sumWeights ps*evalNat S factors := by
  induction ps with
  | nil => simp [allCoeffs,mass,sumWeights]
  | cons p ps ih =>
    have h1 := mass_add (jetCoeffs factors p) (allCoeffs factors ps)
    have h2 := mass_compose p.1 p.2.1 S (hs p (by simp)) factors
    have h3 := ih (fun q hq => hs q (by simp [hq]))
    have hm : mass (jetCoeffs factors p) = p.2.2*mass (compose p.1 p.2.1 factors) := by
      simp only [jetCoeffs,mass_scale,Int.natAbs_natCast]
    rw [hm] at h1
    have h4 := Nat.mul_le_mul_left p.2.2 h2
    simp only [allCoeffs,sumWeights,Nat.add_mul]
    omega
end CatalanCore.Cert.QuarterContour.PackedPolynomial
#print axioms CatalanCore.Cert.QuarterContour.PackedPolynomial.eval_allCoeffs
#print axioms CatalanCore.Cert.QuarterContour.PackedPolynomial.mass_allCoeffs