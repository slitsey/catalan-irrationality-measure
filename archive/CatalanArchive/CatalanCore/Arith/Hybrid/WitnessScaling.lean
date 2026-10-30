module
public import CatalanCore.Arith.Hybrid.AffineWitness
@[expose] public section
namespace CatalanCore.Arith.Hybrid
lemma lowWitness_mul (r A B p : ℝ) (hr : 0<r) :
    r*lowWitness A B (p/r)=
      min (r/8-p+min (5*r/4) (min (B*p) (r+p))-max r (A*p))
        (min (5*r/4) (min (B*p) (r+p))-9*r/8) := by
  have hp : r*(p/r)=p := by field_simp
  have hA : r*(A*(p/r))=A*p := by field_simp <;> ring
  have hB : r*(B*(p/r))=B*p := by field_simp <;> ring
  have h5 : r*(5/4)=5*r/4 := by ring
  have h8 : r*(1/8)=r/8 := by ring
  have h9 : r*(9/8)=9*r/8 := by ring
  simp only [lowWitness, mul_min_of_nonneg _ _ hr.le, mul_max_of_nonneg _ _ hr.le,
    mul_add, mul_sub, mul_one, hp, hA, hB, h5, h8, h9]
lemma ncWitness_mul (r A B p : ℝ) (hr : 0<r) :
    r*ncWitness A B (p/r)=min (5*r/4) (B*p)-max r (A*p)-r/8 := by
  have hA : r*(A*(p/r))=A*p := by field_simp <;> ring
  have hB : r*(B*(p/r))=B*p := by field_simp <;> ring
  have h5 : r*(5/4)=5*r/4 := by ring
  have h8 : r*(1/8)=r/8 := by ring
  simp only [ncWitness,mul_sub,mul_min_of_nonneg _ _ hr.le,mul_max_of_nonneg _ _ hr.le,
    mul_one,hA,hB,h5,h8]
end CatalanCore.Arith.Hybrid
