module
public import CatalanCore.Uniform.Content.SourceCertificate
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Content

theorem exceptionInteger_pos {m n : Nat} (basis : Int) (D : Fin m → Int)
    (den : Fin m → Fin n → Int) (hb : 0<basis) (hD : ∀ i, 0<D i)
    (hd : ∀ i j, 0<den i j) : 0<exceptionInteger basis D den := by
  apply mul_pos
  · exact mul_pos hb (Finset.prod_pos fun i _ => hD i)
  · exact Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => hd i j

/-- An actual positive integer gives a finite set of exceptional prime divisors. -/
theorem exceptionInteger_ne_zero {m n : Nat} (basis : Int) (D : Fin m → Int)
    (den : Fin m → Fin n → Int) (hb : 0<basis) (hD : ∀ i, 0<D i)
    (hd : ∀ i j, 0<den i j) : exceptionInteger basis D den≠0 :=
  ne_of_gt (exceptionInteger_pos basis D den hb hD hd)
end CatalanCore.Uniform.Content
