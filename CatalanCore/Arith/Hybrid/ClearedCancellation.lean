module
public import CatalanCore.Arith.Hybrid.ClearedPartners
@[expose] public section
open Polynomial Finset
namespace CatalanCore.Arith.Hybrid.LemmaE
variable {p : ℕ} [Fact p.Prime]

lemma Cng.int1_of_right {f g : ℚ[X]} (hc : Cng p f g) (hg : Int1 p g) : Int1 p f := by
  have he : f=(f-g)+g := by ring
  rw [he]
  exact (gn_add_le _ _).trans (max_le hc.le hg)

lemma Cng.mul_left_int {f g a : ℚ[X]} (hc : Cng p f g)
    (ha : Int1 p a) (hg : Int1 p g) : Cng p (a*f) (a*g) :=
  Cng.mul ha (hc.int1_of_right hg) (Cng.refl a) hc

lemma int1_of_mul_Cp_cng_zero {f : ℚ[X]} (hc : Cng p (C (p : ℚ)*f) 0) : Int1 p f := by
  have hn : gn p (C (p : ℚ)*f) < 1 := by simpa [Cng] using hc
  have hb := gn_le_inv_of_lt_one p hn
  rw [gn_mul, gn_C, padicNorm.padicNorm_p_of_prime] at hb
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have he : (((p : ℚ)⁻¹ : ℚ) : ℝ)=(p : ℝ)⁻¹ := by push_cast; rfl
  rw [he] at hb
  exact (mul_le_mul_iff_right₀ (inv_pos.mpr hp)).mp (by simpa [mul_comm] using hb)

section Chain
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma first_order_model_zero (f L : ι → ℚ[X]) (l gamma h : ℚ[X]) :
    0-h*(∑ i, f i*(gamma*(l-L i)))-h*(∑ i, (gamma*(L i-l))*f i)+
      (∑ i, ∑ j, f i*(gamma*(L j-L i))*f j)=0 := by
  have hl : (∑ i, f i*(gamma*(l-L i)))+(∑ i, (gamma*(L i-l))*f i)=0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i hi
    ring
  have hq : (∑ i, ∑ j, f i*(gamma*(L j-L i))*f j)=0 := by
    calc
      _ = -gamma*(∑ i, ∑ j, f i*f j*(L i-L j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [weighted_difference_sum, mul_zero]
  linear_combination -h*hl+hq

/-- Translation identifies the two partner vectors; first-order cross-chain
residues then force the cleared same-class second difference to be integral. -/
theorem same_class_delta_int1
    (D h gamma l : ℚ[X]) (L sr sc B Cc : ι → ℚ[X]) (A : ι → ι → ℚ[X])
    (hh : Int1 p h) (hg : Int1 p gamma) (hl : Int1 p l)
    (hL : ∀ i, Int1 p (L i)) (hsr : ∀ i, Int1 p (sr i)) (hsc : ∀ i, Int1 p (sc i))
    (hpartners : ∀ i, Cng p (sc i) (sr i))
    (hD : Cng p (C (p : ℚ)*D) 0)
    (hB : ∀ i, Cng p (C (p : ℚ)*B i) (gamma*(l-L i)))
    (hC : ∀ i, Cng p (C (p : ℚ)*Cc i) (gamma*(L i-l)))
    (hA : ∀ i j, Cng p (C (p : ℚ)*A i j) (gamma*(L j-L i))) :
    Int1 p (h^2*D-h*(∑ i, sr i*B i)-h*(∑ i, Cc i*sc i)+
      ∑ i, ∑ j, sr i*A i j*sc j) := by
  have iB (i) : Int1 p (gamma*(l-L i)) := hg.mul (hl.sub (hL i))
  have iC (i) : Int1 p (gamma*(L i-l)) := hg.mul ((hL i).sub hl)
  have iA (i j) : Int1 p (gamma*(L j-L i)) := hg.mul ((hL j).sub (hL i))
  have c0 : Cng p (h^2*(C (p : ℚ)*D)) 0 := by
    simpa [pow_two] using hD.mul_left_int (hh.mul hh) Int1.zero
  have c1 : Cng p (h*(∑ i, sr i*(C (p : ℚ)*B i)))
      (h*(∑ i, sr i*(gamma*(l-L i)))) := by
    apply Cng.mul_left_int _ hh
    · exact Int1.sum (fun i hi => (hsr i).mul (iB i))
    · exact Cng.sum (fun i hi => (hB i).mul_left_int (hsr i) (iB i))
  have c2 : Cng p (h*(∑ i, (C (p : ℚ)*Cc i)*sc i))
      (h*(∑ i, (gamma*(L i-l))*sr i)) := by
    apply Cng.mul_left_int _ hh
    · exact Int1.sum (fun i hi => (iC i).mul (hsr i))
    · exact Cng.sum (fun i hi => Cng.mul (iC i) (hsc i) (hC i) (hpartners i))
  have c3 : Cng p (∑ i, ∑ j, sr i*(C (p : ℚ)*A i j)*sc j)
      (∑ i, ∑ j, sr i*(gamma*(L j-L i))*sr j) := by
    apply Cng.sum
    intro i hi
    apply Cng.sum
    intro j hj
    have hc := Cng.mul (iA i j) (hsc j) (hA i j) (hpartners j)
    have hc' := hc.mul_left_int (hsr i) ((iA i j).mul (hsr j))
    simpa only [mul_assoc] using hc'
  have hc := ((c0.sub c1).sub c2).add c3
  have he : C (p : ℚ)*(h^2*D-h*(∑ i, sr i*B i)-h*(∑ i, Cc i*sc i)+
      ∑ i, ∑ j, sr i*A i j*sc j) =
      h^2*(C (p : ℚ)*D)-h*(∑ i, sr i*(C (p : ℚ)*B i))-
      h*(∑ i, (C (p : ℚ)*Cc i)*sc i)+∑ i, ∑ j, sr i*(C (p : ℚ)*A i j)*sc j := by
    simp only [mul_sub, mul_add, Finset.mul_sum]
    ring
  rw [first_order_model_zero] at hc
  apply int1_of_mul_Cp_cng_zero
  rwa [he]
end Chain
#print axioms same_class_delta_int1
end CatalanCore.Arith.Hybrid.LemmaE
