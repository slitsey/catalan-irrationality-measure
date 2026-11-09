module

public import CatalanCore.Uniform.Decay.Jet.PoleAtoms
public import CatalanCore.Uniform.Support.Datum
public import CatalanCore.Uniform.Support.SeqFamily

@[expose] public section
set_option Elab.async false
open Finset MeasureTheory Set Filter Complex
open scoped Polynomial
namespace CatalanCore.Uniform.Decay.Jet
open CatalanCore.Uniform.Support

/-! The exact atom sum is the same rational Löwner matrix used by arithmetic.
No nonzero coefficient, leading-order or reference-frame assumption is used here. -/

noncomputable def poleAtomSum (D : PoleDatum) (x y n : ℕ) : ℝ :=
  ∑ i : Fin D.n, ∑ j ∈ Finset.Icc 1 (D.w i),
    (D.coeff i j : ℝ) * poleAtom j (D.s i : ℝ) x y n

theorem summable_poleAtomSum (D : PoleDatum) (x y : ℕ) :
    Summable (poleAtomSum D x y) := by
  apply summable_sum
  intro i _
  apply summable_sum
  intro j hj
  exact (summable_poleAtom j (by have := (Finset.mem_Icc.mp hj).1; omega)
    (by exact_mod_cast (D.hs i).1) x y).mul_left (D.coeff i j : ℝ)

theorem tsum_poleAtomSum (D : PoleDatum) (x y : ℕ) :
    (∑' n : ℕ, poleAtomSum D x y n) =
      ∑ i : Fin D.n, ∑ j ∈ Finset.Icc 1 (D.w i),
        (D.coeff i j : ℝ) * ∑' n : ℕ, poleAtom j (D.s i : ℝ) x y n := by
  unfold poleAtomSum
  rw [Summable.tsum_finsetSum (fun i _ => summable_sum fun j hj =>
    (summable_poleAtom j (by have := (Finset.mem_Icc.mp hj).1; omega)
      (by exact_mod_cast (D.hs i).1) x y).mul_left _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Summable.tsum_finsetSum (fun j hj =>
    (summable_poleAtom j (by have := (Finset.mem_Icc.mp hj).1; omega)
      (by exact_mod_cast (D.hs i).1) x y).mul_left _)]
  simp only [tsum_mul_left]

theorem pole_f_sub (D : PoleDatum) {x y : ℕ} (hxy : x ≤ y) :
    ((D.f y - D.f x : ℚ) : ℝ) =
      ∑ i : Fin D.n, ∑ j ∈ Finset.Icc 1 (D.w i),
        (D.coeff i j : ℝ) * ∑ t ∈ Finset.Ico x y, polePower j (D.s i : ℝ) t := by
  have he : D.f y - D.f x = ∑ t ∈ Finset.Ico x y, D.delta t := by
    unfold PoleDatum.f
    exact (Finset.sum_Ico_eq_sub _ hxy).symm
  rw [he, Rat.cast_sum]
  simp only [PoleDatum.delta, Rat.cast_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [polePower, Rat.cast_div, Rat.cast_pow, Rat.cast_add, Rat.cast_natCast]
  ring

theorem pole_e_eq (D : PoleDatum) (x : ℕ) :
    (D.e x : ℝ) = ∑ i : Fin D.n, ∑ j ∈ Finset.Icc 1 (D.w i),
      (D.coeff i j : ℝ) * (j : ℝ) *
        ∑ t ∈ Finset.range x, polePower (j + 1) (D.s i : ℝ) t := by
  unfold PoleDatum.e PoleDatum.delta1
  simp only [Finset.sum_neg_distrib, neg_neg, Rat.cast_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [polePower, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_natCast]
  ring

theorem poleAtomSum_gram_diag (D : PoleDatum) (x : ℕ) :
    (∑' n : ℕ, poleAtomSum D x x n) = D.xi - (D.e x : ℝ) := by
  rw [tsum_poleAtomSum, pole_e_eq]
  unfold PoleDatum.xi PoleDatum.hurwitzTail
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [tsum_poleAtom_diag j (by have := (Finset.mem_Icc.mp hj).1; omega)
    (by exact_mod_cast (D.hs i).1)]
  simp only [polePower]
  ring

theorem poleAtomSum_gram_lt (D : PoleDatum) {x y : ℕ} (hxy : x < y) :
    (∑' n : ℕ, poleAtomSum D x y n) =
      (((D.f y - D.f x) / ((y : ℚ) - x) : ℚ) : ℝ) := by
  rw [tsum_poleAtomSum]
  simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_natCast]
  have he := pole_f_sub D hxy.le
  rw [Rat.cast_sub] at he
  rw [he, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(hasSum_poleAtom_lt j (by have := (Finset.mem_Icc.mp hj).1; omega)
    (by exact_mod_cast (D.hs i).1) x y hxy).tsum_eq]
  ring

theorem poleAtomSum_gram (D : PoleDatum) (x y : ℕ) :
    (∑' n : ℕ, poleAtomSum D x y n) =
      (lw D.f D.e x y : ℝ) + if x = y then D.xi else 0 := by
  rcases lt_trichotomy x y with h | h | h
  · rw [poleAtomSum_gram_lt D h]
    simp only [lw, if_neg h.ne, add_zero]
  · subst y
    rw [poleAtomSum_gram_diag]
    simp [lw]
    <;> ring
  · have he : poleAtomSum D x y = poleAtomSum D y x := by
      funext n
      unfold poleAtomSum
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [poleAtom_comm]
    rw [he, poleAtomSum_gram_lt D h]
    simp only [lw, if_neg (Ne.symm h.ne), add_zero]
    have hs : ((D.f x - D.f y) / ((x : ℚ) - y) : ℚ) =
        (D.f y - D.f x) / ((y : ℚ) - x) := by
      rw [show (D.f y - D.f x : ℚ) = -(D.f x - D.f y) by ring,
        show ((y : ℚ) - x) = -((x : ℚ) - y) by ring, neg_div_neg_eq]
    exact congrArg (fun q : ℚ => (q : ℝ)) hs


/-! The rational head split acts on any two finite derivative vectors. -/
theorem pole_split_bilinear {D : PoleDatum} (S : PoleGramSplit D) (i : Fin D.n)
    (u v : Fin (S.J + 1) → ℂ) :
    (∑ j : Fin (S.J + 1), ∑ k : Fin (S.J + 1),
      ((D.coeff i (j.val + k.val + 1) /
        ((j.val.factorial : ℚ) * k.val.factorial) : ℚ) : ℂ) * u j * v k) =
      ∑ q : Fin (S.count i), (S.weight ⟨i, q⟩ : ℂ) *
        (∑ j : Fin (S.J + 1), (S.coeff ⟨i, q⟩ j : ℂ) * u j) *
        (∑ k : Fin (S.J + 1), (S.coeff ⟨i, q⟩ k : ℂ) * v k) := by
  classical
  have hc (j k : Fin (S.J + 1)) :
      ((D.coeff i (j.val + k.val + 1) /
        ((j.val.factorial : ℚ) * k.val.factorial) : ℚ) : ℂ) =
        ∑ q : Fin (S.count i), (S.weight ⟨i, q⟩ : ℂ) *
          (S.coeff ⟨i, q⟩ j : ℂ) * (S.coeff ⟨i, q⟩ k : ℂ) := by
    have he := congrArg (fun a : ℚ => (a : ℂ)) (S.split i j k)
    push_cast at he ⊢
    exact he
  calc
    _ = ∑ j : Fin (S.J + 1), ∑ k : Fin (S.J + 1), ∑ q : Fin (S.count i),
        (S.weight ⟨i, q⟩ : ℂ) * (S.coeff ⟨i, q⟩ j : ℂ) *
          (S.coeff ⟨i, q⟩ k : ℂ) * u j * v k := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [hc, Finset.sum_mul, Finset.sum_mul]
    _ = ∑ q : Fin (S.count i), ∑ j : Fin (S.J + 1), ∑ k : Fin (S.J + 1),
        (S.weight ⟨i, q⟩ : ℂ) * (S.coeff ⟨i, q⟩ j : ℂ) *
          (S.coeff ⟨i, q⟩ k : ℂ) * u j * v k := by
      calc
        _ = ∑ j : Fin (S.J + 1), ∑ q : Fin (S.count i), ∑ k : Fin (S.J + 1),
            (S.weight ⟨i, q⟩ : ℂ) * (S.coeff ⟨i, q⟩ j : ℂ) *
              (S.coeff ⟨i, q⟩ k : ℂ) * u j * v k := by
          apply Finset.sum_congr rfl
          intro j _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring


#print axioms summable_poleAtomSum
#print axioms tsum_poleAtomSum
#print axioms pole_f_sub
#print axioms pole_e_eq
#print axioms poleAtomSum_gram
#print axioms pole_split_bilinear

end CatalanCore.Uniform.Decay.Jet
