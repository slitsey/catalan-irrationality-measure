module
public import CatalanCore.Uniform.Content.SourceCertificate
@[expose] public section
set_option Elab.async false
namespace CatalanCore.Uniform.Content
open Matrix

def scaledRows {m n : Nat} (S : Fin m → Int) (B : Fin m → List Int) :
    Matrix (Fin m) (Fin n) Int := Matrix.diagonal S*fromRows B

/-- Keep a common large multiplier symbolic: each row tape and each multiplier
is stored once, while the checked equation remains the same integer product. -/
theorem stream_scaled_factorization {m n d r : Nat}
    (S : Fin m → Int) (B : Fin m → List Int) (V : Fin d → List Int)
    (C : Fin m → List Int) (T : Fin d → List Int)
    (hB : ∀ i, (B i).length=n) (hV : ∀ j, (V j).length=n)
    (hC : ∀ i, (C i).length=r) (hT : ∀ j, (T j).length=r)
    (hc : ∀ i j, S i*streamDot (B i) (V j)=streamDot (C i) (T j)) :
    (scaledRows S B : Matrix (Fin m) (Fin n) Int)*fromColumns V=
      (fromRows C : Matrix (Fin m) (Fin r) Int)*fromColumns T := by
  rw [scaledRows,Matrix.mul_assoc]
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply,fromRows,fromColumns]
  rw [←streamDot_eq_sum n (B i) (V j) (hB i) (hV j),
    ←streamDot_eq_sum r (C i) (T j) (hC i) (hT j)]
  exact hc i j

theorem cast_scaledRows (K : Type*) [Field K] {m n : Nat}
    (S : Fin m → Int) (B : Fin m → List Int) :
    castMatrix K (scaledRows S B : Matrix (Fin m) (Fin n) Int)=
      Matrix.diagonal (fun i => (S i : K))*castMatrix K (fromRows B) := by
  rw [scaledRows,castMatrix_mul]
  congr 1
  ext i j
  by_cases h : i=j <;> simp [castMatrix,Matrix.diagonal,h]

/-- Original rational covectors inherit the checked image rank over every
field surviving the explicit denominator, row-multiplier and basis exceptions. -/
theorem source_scaled_rank_le (K : Type*) [Field K] {m n d r : Nat}
    (nums dens B : Fin m → List Int) (D S : Fin m → Int)
    (V : Matrix (Fin n) (Fin d) Int)
    (C : Matrix (Fin m) (Fin r) Int) (T : Matrix (Fin r) (Fin d) Int)
    (hnorm : ∀ i, rowNormalization (D i) (nums i) (dens i) (B i)=true)
    (hden : ∀ i (j : Fin n), ((dens i).getD j.val 0 : K)≠0)
    (hD : ∀ i, (D i : K)≠0) (hS : ∀ i, (S i : K)≠0)
    (hfactor : scaledRows S B*V=C*T) :
    ((sourceFractions K nums dens : Matrix (Fin m) (Fin n) K)*castMatrix K V).rank≤r := by
  let A : Matrix (Fin m) (Fin n) K := sourceFractions K nums dens
  let E : Matrix (Fin m) (Fin m) K := Matrix.diagonal (fun i => (D i : K)⁻¹*(S i : K)⁻¹)
  apply row_cleared_image_rank_le K (scaledRows S B) V C T A E ?_ hfactor
  dsimp [A,E]
  rw [sourceRows_normalize K nums dens B D hnorm hden hD,cast_scaledRows]
  ext i j
  simp only [Matrix.diagonal_mul]
  rw [mul_assoc,inv_mul_cancel_left₀ (hS i)]

#print axioms source_scaled_rank_le
end CatalanCore.Uniform.Content

