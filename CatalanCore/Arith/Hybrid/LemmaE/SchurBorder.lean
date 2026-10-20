module
public import CatalanCore.Arith.Hybrid.ChainTwoBounds
@[expose] public section
open Matrix Polynomial
namespace CatalanCore.Arith.Hybrid.LemmaE
variable {p : ℕ} [Fact p.Prime] {I Z : Type} [Fintype I] [DecidableEq I]
lemma Nmat_const_one (A : Matrix I I ℚ[X]) :
    Nmat p (fun _ : I=>1) A=C ((p:ℚ)^2) • (Atil p (fun _ : I=>1) A).adjugate := by
  ext i j
  simp only [Nmat,scl,Matrix.diagonal_mul,Matrix.mul_diagonal,pow_one,
    Matrix.smul_apply,smul_eq_mul]
  rw [map_pow,pow_two]
  ring
/-- Crude bordering costs two in each new Schur incidence, independently of residue geometry. -/
theorem Tscaled_gle_right_at (b : ℕ) (A : Matrix I I ℚ[X]) (B : Matrix I Z ℚ[X])
    (C2 : Matrix Z I ℚ[X]) (D : Matrix Z Z ℚ[X])
    (hI : ∀i j,Int1 p (Atil p (fun _ : I=>1) A i j))
    (hp : gn p (Atil p (fun _ : I=>1) A).det=1)
    (z y : Z) (hC : ∀i,Int1 p (C ((p:ℚ)^2)*C2 z i))
    (hB : ∀i,GLE p b (B i y)) (hD : GLE p b (D z y)) :
    GLE p b (Tscaled (Atil p (fun _ : I=>1) A).det A B C2 D
      (Nmat p (fun _ : I=>1) A) z y) := by
  apply gle_sub
  · exact int1_mul_gle (le_of_eq hp) hD
  · have HE : C2*Nmat p (fun _ : I=>1) A*B=
        ((C ((p:ℚ)^2) • C2)*(Atil p (fun _ : I=>1) A).adjugate)*B := by
      rw [Nmat_const_one]
      simp only [Matrix.mul_smul,Matrix.smul_mul]
    rw [HE,Matrix.mul_apply]
    apply GLE.sum
    intro j _
    apply int1_mul_gle _ (hB j)
    rw [Matrix.mul_apply]
    apply Int1.sum
    intro i _
    exact (hC i).mul (adj_int1 hI i j)

theorem Tscaled_gle_right (b : ℕ) (A : Matrix I I ℚ[X]) (B : Matrix I Z ℚ[X])
    (C2 : Matrix Z I ℚ[X]) (D : Matrix Z Z ℚ[X])
    (hI : ∀i j,Int1 p (Atil p (fun _ : I=>1) A i j))
    (hp : gn p (Atil p (fun _ : I=>1) A).det=1)
    (hC : ∀z i,Int1 p (C ((p:ℚ)^2)*C2 z i))
    (hB : ∀i y,GLE p b (B i y)) (hD : ∀z y,GLE p b (D z y)) :
    ∀z y,GLE p b (Tscaled (Atil p (fun _ : I=>1) A).det A B C2 D
      (Nmat p (fun _ : I=>1) A) z y) := fun z y=>
  Tscaled_gle_right_at b A B C2 D hI hp z y (hC z) (fun i=>hB i y) (hD z y)
/-- The old crude incidence bound is the case b=2 of the uniform bound. -/
theorem Tscaled_gle_two (A : Matrix I I ℚ[X]) (B : Matrix I Z ℚ[X])
    (C2 : Matrix Z I ℚ[X]) (D : Matrix Z Z ℚ[X])
    (hI : ∀i j,Int1 p (Atil p (fun _ : I=>1) A i j))
    (hp : gn p (Atil p (fun _ : I=>1) A).det=1)
    (hC : ∀z i,Int1 p (C ((p:ℚ)^2)*C2 z i))
    (hB : ∀i y,GLE p 2 (B i y)) (hD : ∀z y,GLE p 2 (D z y)) :
    ∀z y,GLE p 2 (Tscaled (Atil p (fun _ : I=>1) A).det A B C2 D
      (Nmat p (fun _ : I=>1) A) z y) := Tscaled_gle_right 2 A B C2 D hI hp hC hB hD
lemma Tscaled_gle_left_at (b : ℕ) (A : Matrix I I ℚ[X]) (B : Matrix I Z ℚ[X])
    (C2 : Matrix Z I ℚ[X]) (D : Matrix Z Z ℚ[X])
    (hI : ∀i j,Int1 p (Atil p (fun _ : I=>1) A i j))
    (hp : gn p (Atil p (fun _ : I=>1) A).det=1)
    (z y : Z) (hC : ∀i,GLE p b (C2 z i))
    (hB : ∀i,Int1 p (C ((p:ℚ)^2)*B i y)) (hD : GLE p b (D z y)) :
    GLE p b (Tscaled (Atil p (fun _ : I=>1) A).det A B C2 D
      (Nmat p (fun _ : I=>1) A) z y) := by
  apply gle_sub
  · exact int1_mul_gle (le_of_eq hp) hD
  · have HE : C2*Nmat p (fun _ : I=>1) A*B=
        C2*((Atil p (fun _ : I=>1) A).adjugate*(C ((p:ℚ)^2) • B)) := by
      rw [Nmat_const_one]
      simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_assoc]
    rw [HE,Matrix.mul_apply]
    apply GLE.sum
    intro i _
    apply gle_mul_int1 (hC i)
    rw [Matrix.mul_apply]
    exact Int1.sum (fun j _=>(adj_int1 hI i j).mul (hB j))
lemma Nmat_int1 (A : Matrix I I ℚ[X])
    (hI : ∀i j,Int1 p (Atil p (fun _ : I=>1) A i j)) :
    ∀i j,Int1 p (Nmat p (fun _ : I=>1) A i j) := by
  intro i j
  rw [Nmat_const_one,Matrix.smul_apply,smul_eq_mul]
  apply Int1.mul _ (adj_int1 hI i j)
  rw [Int1,gn_C]
  have hh : ((p:ℚ)^2) ∈ Basic.LocRing p := by
    exact (Basic.LocRing p).pow_mem (by exact_mod_cast Basic.int_mem_locRing (ℓ:=p) (p:ℤ)) 2
  exact_mod_cast (mem_locRing_iff_padicNorm (p:=p)).mp hh
lemma Tscaled_gle_product_at (a b : ℕ) (A : Matrix I I ℚ[X]) (B : Matrix I Z ℚ[X])
    (C2 : Matrix Z I ℚ[X]) (D : Matrix Z Z ℚ[X])
    (hI : ∀i j,Int1 p (Atil p (fun _ : I=>1) A i j))
    (hp : gn p (Atil p (fun _ : I=>1) A).det=1)
    (z y : Z) (hC : ∀i,GLE p a (C2 z i)) (hB : ∀i,GLE p b (B i y))
    (hD : GLE p (a+b) (D z y)) :
    GLE p (a+b) (Tscaled (Atil p (fun _ : I=>1) A).det A B C2 D
      (Nmat p (fun _ : I=>1) A) z y) := by
  apply gle_sub
  · exact int1_mul_gle (le_of_eq hp) hD
  · rw [Matrix.mul_apply]
    apply GLE.sum
    intro j _
    apply GLE.mul _ (hB j)
    rw [Matrix.mul_apply]
    exact GLE.sum (fun i _=>gle_mul_int1 (hC i) (Nmat_int1 A hI i j))
end CatalanCore.Arith.Hybrid.LemmaE
#print axioms CatalanCore.Arith.Hybrid.LemmaE.Tscaled_gle_right
#print axioms CatalanCore.Arith.Hybrid.LemmaE.Tscaled_gle_product_at
