module
public import CatalanCore.Arith.Hybrid.RankGLE
public import Mathlib.Tactic
@[expose] public section
open Polynomial CatalanCore.Basic
namespace CatalanCore.Arith.Hybrid
variable {p : ℕ} [Fact p.Prime]

/-- The R=-Mn model uses the negative of the actual formal variable.
This sign substitution has exactly zero coefficient-clearing cost. -/
theorem gle_comp_neg_X_of {B : ℕ} {f : ℚ[X]} (hf : GLE p B f) :
    GLE p B (f.comp (-X)) := by
  intro i
  have hc : (f.comp (-X)).coeff i=f.coeff i*(-1:ℚ)^i := by
    simpa using (Polynomial.comp_C_mul_X_coeff (p:=f) (r:=(-1:ℚ)) (n:=i))
  rw [hc]
  have hu : (-1:ℚ)^i∈LocRing p := by
    simpa using int_mem_locRing (ℓ:=p) ((-1:ℤ)^i)
  convert (LocRing p).mul_mem (hf i) hu using 1 <;> ring

theorem gle_comp_neg_X_iff (B : ℕ) (f : ℚ[X]) :
    GLE p B (f.comp (-X)) ↔ GLE p B f := by
  constructor
  · intro H
    have H':=gle_comp_neg_X_of H
    simpa only [Polynomial.comp_neg_X_comp_neg_X] using H'
  · exact gle_comp_neg_X_of

#print axioms gle_comp_neg_X_iff
end CatalanCore.Arith.Hybrid
