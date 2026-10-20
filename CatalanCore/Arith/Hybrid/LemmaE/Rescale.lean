module

public import CatalanCore.Arith.Hybrid.LemmaE.BlockScale
public import CatalanCore.Rect.Block
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section

/-! # Primitive monic cores and coefficient transfer under diagonal rescaling -/
open Polynomial Matrix CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid
variable {p : ℕ} [Fact p.Prime]

/-- Multiplication by a primitive Gauss-unit polynomial does not change a coefficient bound. -/
theorem GLE.mul_primitive_iff (g f : ℚ[X]) (hg : gn p g = 1) (B : ℕ) :
    GLE p B (g*f) ↔ GLE p B f := by
  rw [gle_iff_gn, gn_mul, hg, one_mul, ← gle_iff_gn]

/-- Undo a variable contraction using only coefficient integrality. -/
theorem GLE.of_comp_inv {a : ℚ} (ha : a ∈ LocRing p) (ha0 : a ≠ 0)
    {f : ℚ[X]} {B : ℕ} (h : GLE p B (f.comp (C a⁻¹ * Polynomial.X))) : GLE p B f := by
  intro i
  have hi := (LocRing p).mul_mem ((LocRing p).pow_mem ha i) (h i)
  rw [Polynomial.comp_C_mul_X_coeff] at hi
  have he : a^i * ((p : ℚ)^B * (f.coeff i * a⁻¹^i)) = (p : ℚ)^B * f.coeff i := by
    calc
      _ = ((p : ℚ)^B * f.coeff i) * (a*a⁻¹)^i := by rw [mul_pow]; ring
      _ = _ := by simp [ha0]
  rwa [he] at hi

/-- Formal substitution by `x/p^e`; this is a coefficient-estimation device. -/
noncomputable def rescaleHom (p e : ℕ) : ℚ[X] →+* ℚ[X] :=
  Polynomial.compRingHom (C (((p : ℚ)^e)⁻¹) * X)

lemma GLE.of_rescale {e B : ℕ} {f : ℚ[X]} (h : GLE p B (rescaleHom p e f)) : GLE p B f :=
  GLE.of_comp_inv ((LocRing p).pow_mem (int_mem_locRing (p : ℤ)) e)
    (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)) h

/-- Entrywise substitution commutes with the determinant. -/
lemma det_rescale {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ[X]) (e : ℕ) :
    (M.map (rescaleHom p e)).det = rescaleHom p e M.det :=
  ((rescaleHom p e).map_det M).symm

namespace LemmaE

/-- An integral monic polynomial is primitive for the Gauss norm. -/
theorem gn_eq_one_of_monic_int1 (f : ℚ[X]) (hf : Int1 p f) (hm : f.Monic) :
    gn p f = 1 := by
  apply le_antisymm hf
  have h := padic_coeff_le_gn p f f.natDegree
  rw [hm.coeff_natDegree] at h
  simpa using h

/-- A constant integral matrix plus the formal identity diagonal has primitive determinant. -/
theorem prim_det_shift {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℚ) (hR : ∀ i j, R i j ∈ LocRing p) :
    gn p (R.map C + (X : ℚ[X]) • (1 : Matrix ι ι ℚ[X])).det = 1 := by
  apply gn_eq_one_of_monic_int1
  · apply det_int1
    intro i j
    have hC : GLE p 0 (C (R i j)) := GLE.C_iff.mpr (by simpa using hR i j)
    have hX : GLE p 0 ((X : ℚ[X]) * if i=j then 1 else 0) := by
      by_cases hij : i=j <;> simp [hij, GLE.X, GLE.zero]
    have hh := hC.add hX
    exact (gle_iff_gn p 0 _).mp (by simpa [Matrix.one_apply] using hh)
  · rw [CatalanCore.Rect.det_map_C_add_X]
    exact Matrix.charpoly_monic _

/-- Uniform row/column scaling cancels a reciprocal variable substitution. -/
theorem Atil_rescale_shift {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℚ) (a : ℕ) :
    Atil p (fun _ : ι => a)
      ((R.map C + (X : ℚ[X]) • (1 : Matrix ι ι ℚ[X])).map (rescaleHom p (2*a))) =
      ((p : ℚ)^(2*a) • R).map C + (X : ℚ[X]) • 1 := by
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply Matrix.ext
  intro i j
  simp only [Atil_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, rescaleHom, Polynomial.coe_compRingHom, Polynomial.add_comp,
    Polynomial.C_comp, Polynomial.mul_comp, Polynomial.X_comp, Polynomial.one_comp,
    Polynomial.zero_comp, smul_eq_mul]
  have he : (p : ℚ)^(2*a) = (p : ℚ)^a * (p : ℚ)^a := by rw [← pow_add]; congr 1; omega
  have hpa : (p : ℚ)^a ≠ 0 := pow_ne_zero _ hp
  have hcc : C ((p : ℚ)^a) * C (((p : ℚ)^(2*a))⁻¹) * C ((p : ℚ)^a) = (1 : ℚ[X]) := by
    rw [← Polynomial.C_mul, ← Polynomial.C_mul]
    have hr : (p : ℚ)^a * ((p : ℚ)^(2*a))⁻¹ * (p : ℚ)^a = 1 := by
      rw [he]
      field_simp
    rw [hr, Polynomial.C_1]
  have hconst : C ((p : ℚ)^a) * C (R i j) * C ((p : ℚ)^a) =
      C ((p : ℚ)^(2*a) * R i j) := by
    rw [← Polynomial.C_mul, ← Polynomial.C_mul]
    congr 1
    rw [he]
    ring
  split_ifs
  · simp only [mul_one, Polynomial.one_comp]
    calc
      _ = C ((p : ℚ)^a) * C (R i j) * C ((p : ℚ)^a) +
          (C ((p : ℚ)^a) * C (((p : ℚ)^(2*a))⁻¹) * C ((p : ℚ)^a)) * X := by ring
      _ = _ := by rw [hconst, hcc]; simp
  · simpa only [mul_zero, add_zero, Polynomial.zero_comp] using hconst

/-- Monicity removes every exceptional chain-block determinant and every zero-block exclusion. -/
theorem prim_Atil_rescale {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : Matrix ι ι ℚ) (a : ℕ)
    (hR : ∀ i j, (p : ℚ)^(2*a) * R i j ∈ LocRing p) :
    gn p (Atil p (fun _ : ι => a)
      ((R.map C + (X : ℚ[X]) • (1 : Matrix ι ι ℚ[X])).map (rescaleHom p (2*a)))).det = 1 := by
  rw [Atil_rescale_shift]
  exact prim_det_shift _ hR

end LemmaE
end CatalanCore.Arith.Hybrid
#print axioms CatalanCore.Arith.Hybrid.GLE.of_comp_inv
#print axioms CatalanCore.Arith.Hybrid.LemmaE.prim_Atil_rescale
