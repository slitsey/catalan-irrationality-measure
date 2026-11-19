module
public import CatalanCore.Li2.NVMod.DataSupport.PolynomialLists
public import Mathlib.FieldTheory.Finite.Basic
@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1000000
open Polynomial Finset
open scoped BigOperators
namespace CatalanCore.Li2.NVMod.PolynomialCert
noncomputable section
/-- NZ2: evaluation commutes with the determinant, with no degree hypothesis. -/
theorem eval_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ[X]) (x : ℤ) :
    M.det.eval x=(Matrix.of fun i j=> (M i j).eval x).det := by
  exact (Polynomial.evalRingHom x).map_det M
/-- NZ3: an integer polynomial with all coefficients smaller than the radix
cannot vanish at that radix unless it is zero. -/
theorem radix_zero (P : ℤ[X]) (b : ℤ) (hb : 0<b)
    (hc : ∀ j,|P.coeff j|<b) (he : P.eval b=0) : P=0 := by
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | h n ih =>
    have hz : P.coeff 0=0 := Int.eq_zero_of_abs_lt_dvd
      ((show P.IsRoot b from he).dvd_coeff_zero) (hc 0)
    by_cases hdeg : P.natDegree=0
    · rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg,hz,map_zero]
    · have hd : P.divX.natDegree<n := by
        rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one,←hn]
        omega
      have he' : P.divX.eval b=0 := by
        have hh := congrArg (fun Q : ℤ[X]=>Q.eval b) (Polynomial.divX_mul_X_add P)
        simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
          Polynomial.eval_C,hz,add_zero,he] at hh
        exact (mul_eq_zero.mp hh).resolve_right (ne_of_gt hb)
      have hi := ih P.divX.natDegree hd P.divX (fun j=>by simpa using hc (j+1)) he' rfl
      simpa only [hi,hz,zero_mul,map_zero,add_zero] using (Polynomial.divX_mul_X_add P).symm
/-- NZ3 in the balanced binary lane formulation. -/
theorem kronecker_zero (P : ℤ[X]) (B : ℕ)
    (hc : ∀ j,|P.coeff j|<(2:ℤ)^(B-1)) (he : P.eval ((2:ℤ)^B)=0) : P=0 := by
  apply radix_zero P ((2:ℤ)^B) (by positivity) _ he
  intro j
  exact (hc j).trans_le (pow_le_pow_right₀ (by norm_num) (Nat.sub_le B 1))

def residuePolynomial (p : ℕ) : ℤ[X] := ∑ j∈range (p-1),X^j
/-- The geometric polynomial vanishes at every nonzero, nonunit residue. -/
theorem residuePolynomial_root (p : ℕ) [Fact p.Prime] (r : ZMod p)
    (hr : r≠0) (h1 : r≠1) :
    ((residuePolynomial p).map (Int.castRingHom (ZMod p))).eval r=0 := by
  have hpow := ZMod.pow_card_sub_one_eq_one hr
  have hg := geom_sum_mul r (p-1)
  have hs : (∑ j∈range (p-1),r^j)*(r-1)=0 := by rw [hg,hpow,sub_self]
  have hn : r-1≠0 := sub_ne_zero.mpr h1
  have hz := (mul_eq_zero.mp hs).resolve_right hn
  simpa only [residuePolynomial,Polynomial.map_sum,Polynomial.map_pow,Polynomial.map_X,
    Polynomial.eval_finsetSum,Polynomial.eval_pow,Polynomial.eval_X] using hz
/-- NZ5: a checked integer Bezout identity gives the exact old interior conclusion. -/
theorem bezout_nonzero (F U V K : ℤ[X]) (p : ℕ) [Fact p.Prime]
    (h : U*F+V*residuePolynomial p=1+C (p:ℤ)*K)
    (r : ZMod p) (hr : r≠0) (h1 : r≠1) :
    (F.map (Int.castRingHom (ZMod p))).eval r≠0 := by
  let φ : ℤ[X]→+*ZMod p := Polynomial.eval₂RingHom (Int.castRingHom (ZMod p)) r
  have hh := congrArg φ h
  have hg : φ (residuePolynomial p)=0 := by
    change (residuePolynomial p).eval₂ (Int.castRingHom (ZMod p)) r=0
    rw [←Polynomial.eval_map]
    exact residuePolynomial_root p r hr h1
  intro hz
  have hf : φ F=0 := by
    change F.eval₂ (Int.castRingHom (ZMod p)) r=0
    rwa [←Polynomial.eval_map]
  have hp : φ (C (p:ℤ))=0 := by simp [φ]
  simp only [map_add,map_mul,map_one,hf,hg,hp,mul_zero,zero_mul,add_zero] at hh
  exact zero_ne_one hh
/-- NZ5: determinant reduction is functorial in every moment entry. -/
theorem determinant_mod {n p : ℕ} (A B : ℕ→ℤ[X])
    (h : ∀ e<2*n-1,(A e).map (Int.castRingHom (ZMod p))=
      (B e).map (Int.castRingHom (ZMod p))) :
    ((Matrix.of fun i j : Fin n=>A (i.val+j.val)).det).map (Int.castRingHom (ZMod p))=
      ((Matrix.of fun i j : Fin n=>B (i.val+j.val)).det).map (Int.castRingHom (ZMod p)) := by
  change (Polynomial.mapRingHom (Int.castRingHom (ZMod p))) _=
    (Polynomial.mapRingHom (Int.castRingHom (ZMod p))) _
  rw [RingHom.map_det,RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  exact h (i.val+j.val) (by have hi:=i.isLt;have hj:=j.isLt;omega)
#print axioms eval_det
#print axioms kronecker_zero
#print axioms bezout_nonzero
#print axioms determinant_mod
end
end CatalanCore.Li2.NVMod.PolynomialCert


