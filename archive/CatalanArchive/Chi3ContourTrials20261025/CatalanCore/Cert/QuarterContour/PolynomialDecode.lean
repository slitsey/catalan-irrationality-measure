module
public import CatalanCore.Cert.QuarterContour.PolynomialCompiler
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.PackedPolynomial
open CatalanCore.Cert.QuarterCompute.Polynomial

theorem length_add (xs ys : List ℤ) : (add xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [add]
  | cons x xs ih =>
    cases ys with
    | nil => simp [add]
    | cons y ys => simp only [add,List.length_cons,ih]; omega

theorem length_scale (a : ℤ) (cs : List ℤ) : (scale a cs).length = cs.length := by simp [scale]

theorem length_quad (a b : ℤ) (cs : List ℤ) (hn : cs ≠ []) :
    (quad a b cs).length = cs.length+2 := by
  cases cs with
  | nil => contradiction
  | cons c cs => simp only [quad,length_add,List.length_cons,length_scale]; omega

theorem length_compose (a b : ℤ) (cs : List ℤ) :
    (compose a b cs).length = 2*cs.length-1 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => rfl
    | cons d ds =>
      have hn : compose a b (d::ds) ≠ [] := by
        intro h
        have hh := congrArg List.length h
        rw [ih] at hh
        simp only [List.length_cons,List.length_nil] at hh
        omega
      rw [compose,length_add,length_quad a b _ hn,ih]
      simp only [List.length_cons,List.length_nil]
      omega

theorem length_allCoeffs (factors : List ℤ) (ps : List Jet) (hp : ps ≠ []) :
    (allCoeffs factors ps).length = 2*factors.length-1 := by
  induction ps with
  | nil => contradiction
  | cons p ps ih =>
    rw [allCoeffs,length_add,jetCoeffs,length_scale,length_compose]
    by_cases ht : ps = []
    · subst ps; simp [allCoeffs]
    · rw [ih ht]; exact max_self _

theorem natAbs_le_mass (c : ℤ) (cs : List ℤ) (hc : c ∈ cs) : c.natAbs ≤ mass cs := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
    rcases List.mem_cons.mp hc with h | h
    · subst c; simp only [mass]; omega
    · have hh := ih h; simp only [mass]; omega

theorem small_of_mass (B : ℤ) (cs : List ℤ) (h : 2*(mass cs : ℤ) < B) : Small B cs := by
  intro c hc
  have hm : (c.natAbs : ℤ) ≤ (mass cs : ℤ) := by exact_mod_cast natAbs_le_mass c cs hc
  rw [Int.natCast_natAbs] at hm
  linarith only [hm,h]

/-- Complete logical decoding: a packed checksum plus bounds certifies all model coefficients. -/
theorem coefficients_of_checksum (B : ℤ) (hB : 0 < B) (S : ℕ)
    (factors : List ℤ) (ps : List Jet) (coeffs : List ℤ) (hp : ps ≠ [])
    (hs : ∀ p ∈ ps, p.1.natAbs+p.2.1.natAbs ≤ S)
    (hsize : 2*((sumWeights ps*evalNat S factors : ℕ) : ℤ) < B)
    (hlen : coeffs.length = 2*factors.length-1) (hc : Small B coeffs)
    (hcheck : packedSum factors B ps = eval B coeffs) : allCoeffs factors ps = coeffs := by
  apply eval_injective B hB _ _ (by rw [length_allCoeffs factors ps hp,hlen]) _ hc
    ((eval_allCoeffs B factors ps).trans hcheck)
  apply small_of_mass
  have hm : (mass (allCoeffs factors ps) : ℤ) ≤ ((sumWeights ps*evalNat S factors : ℕ) : ℤ) := by
    exact_mod_cast mass_allCoeffs S factors ps hs
  linarith only [hm,hsize]
end CatalanCore.Cert.QuarterContour.PackedPolynomial
#print axioms CatalanCore.Cert.QuarterContour.PackedPolynomial.coefficients_of_checksum