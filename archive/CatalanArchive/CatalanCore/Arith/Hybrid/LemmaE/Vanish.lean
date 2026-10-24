module

public import CatalanArchive.CatalanCore.Arith.Hybrid.LemmaE.TDecomp

@[expose] public section

/-!
# The vanishing step: a bilinear form with scalar-diagonal adjugate

If the scaled defect row `μ` is congruent to `β e_{c}`, the scaled defect column `ν` to `β' e_{c'}`
and `adj(Ã)_{c c'} ≡ 0`, then `∑ μ adj ν ≡ 0 (mod p)`; hence the defect term of `g T` loses one
power of `p` (`LNL_gle`).  This is DQ Theorems 2.2 / 3.2 ("`(A⁻¹)(c_z, c_y) ≡ 0`").
-/

open Polynomial Finset Matrix

namespace CatalanCore.Arith.Hybrid.LemmaE

variable {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]

lemma bilin_cng (u u' v v' : ι → ℚ[X]) (W W' : Matrix ι ι ℚ[X])
    (hu : ∀ c, Int1 p (u c)) (hu' : ∀ c, Int1 p (u' c)) (hv : ∀ c, Int1 p (v c))
    (hv' : ∀ c, Int1 p (v' c)) (hW : ∀ c c', Int1 p (W c c')) (hW' : ∀ c c', Int1 p (W' c c'))
    (cu : ∀ c, Cng p (u c) (u' c)) (cv : ∀ c, Cng p (v c) (v' c))
    (cW : ∀ c c', Cng p (W c c') (W' c c')) :
    Cng p (∑ c, ∑ c', u c * W c c' * v c') (∑ c, ∑ c', u' c * W' c c' * v' c') := by
  apply Cng.sum; intro c _
  apply Cng.sum; intro c' _
  exact Cng.mul ((hu' c).mul (hW' c c')) (hv c') (Cng.mul (hu' c) (hW c c') (cu c) (cW c c'))
    (cv c')

/-- The vanishing lemma. -/
theorem bilin_vanish (u v : ι → ℚ[X]) (W : Matrix ι ι ℚ[X]) (c0 c1 : ι) (β β' : ℚ[X])
    (hu : ∀ c, Int1 p (u c)) (hv : ∀ c, Int1 p (v c)) (hW : ∀ c c', Int1 p (W c c'))
    (hβ : Int1 p β) (hβ' : Int1 p β')
    (cu : ∀ c, Cng p (u c) (if c = c0 then β else 0))
    (cv : ∀ c, Cng p (v c) (if c = c1 then β' else 0))
    (hW0 : Cng p (W c0 c1) 0) :
    Cng p (∑ c, ∑ c', u c * W c c' * v c') 0 := by
  have hu' : ∀ c, Int1 p (if c = c0 then β else 0) := fun c => by
    split_ifs
    · exact hβ
    · exact Int1.zero
  have hv' : ∀ c, Int1 p (if c = c1 then β' else 0) := fun c => by
    split_ifs
    · exact hβ'
    · exact Int1.zero
  have h := bilin_cng u (fun c => if c = c0 then β else 0) v (fun c => if c = c1 then β' else 0)
    W W hu hu' hv hv' hW hW cu cv (fun c c' => Cng.refl _)
  have e : ∑ c, ∑ c', (if c = c0 then β else 0) * W c c' * (if c' = c1 then β' else 0) =
      β * W c0 c1 * β' := by
    simp [Finset.sum_ite_eq']
  rw [e] at h
  refine h.trans ?_
  have h1 : Cng p (β * W c0 c1) (β * 0) := Cng.mul hβ (hW c0 c1) (Cng.refl β) hW0
  have h2 : Cng p (β * W c0 c1 * β') (β * 0 * β') :=
    Cng.mul (by simpa using (Int1.zero (p := p))) hβ' h1 (Cng.refl β')
  simpa using h2

lemma Nmat_apply (d : ι → ℕ) (A : Matrix ι ι ℚ[X]) (c c' : ι) :
    Nmat p d A c c' = C ((p : ℚ) ^ d c) * (Atil p d A).adjugate c c' * C ((p : ℚ) ^ d c') := by
  simp [Nmat, scl, Matrix.mul_apply, Matrix.diagonal_apply]

/-- **The defect term gains a power of `p`.** -/
theorem LNL_gle {κ : Type} [Fintype κ] (d : ι → ℕ) (A : Matrix ι ι ℚ[X])
    (L : Matrix κ ι ℚ[X]) (R : Matrix ι κ ℚ[X]) (a : ℕ) (z y : κ)
    (hvan : Cng p (∑ c, ∑ c', (C ((p : ℚ) ^ a) * L z c * C ((p : ℚ) ^ d c)) *
        (Atil p d A).adjugate c c' * (C ((p : ℚ) ^ a) * C ((p : ℚ) ^ d c') * R c' y)) 0) :
    GLE p (2 * a - 1) ((L * Nmat p d A * R) z y) := by
  set X := (L * Nmat p d A * R) z y with hX
  have hid : C ((p : ℚ) ^ (2 * a)) * X = ∑ c, ∑ c', (C ((p : ℚ) ^ a) * L z c * C ((p : ℚ) ^ d c)) *
        (Atil p d A).adjugate c c' * (C ((p : ℚ) ^ a) * C ((p : ℚ) ^ d c') * R c' y) := by
    rw [hX, Matrix.mul_apply, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Nmat_apply, two_mul, pow_add, map_mul]
    ring
  have h1 : gn p (C ((p : ℚ) ^ (2 * a)) * X) < 1 := by
    rw [hid]; unfold Cng at hvan; simpa using hvan
  have h2 := gn_le_inv_of_lt_one p h1
  rw [gn_mul, gn_C] at h2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hn : (padicNorm p ((p : ℚ) ^ (2 * a)) : ℝ) = ((p : ℝ)⁻¹) ^ (2 * a) := by
    have h := map_pow (Rat.AbsoluteValue.padic p) (p : ℚ) (2 * a)
    simp only [Rat.AbsoluteValue.padic_eq_padicNorm] at h
    have h3 : ((padicNorm p (p : ℚ) : ℚ) : ℝ) = (p : ℝ)⁻¹ := by
      rw [padicNorm.padicNorm_p_of_prime]; push_cast; simp
    rw [← h3, ← h]
  rw [hn] at h2
  rw [gle_iff_gn]
  have h4 : gn p X ≤ (p : ℝ) ^ (2 * a) * (p : ℝ)⁻¹ := by
    rw [inv_pow] at h2
    rw [inv_mul_le_iff₀ (pow_pos hp0 _)] at h2
    exact h2
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt.le)
    simpa using h4.trans (by simpa using this)
  · have : (p : ℝ) ^ (2 * a) * (p : ℝ)⁻¹ = (p : ℝ) ^ (2 * a - 1) := by
      have h5 : 2 * a = (2 * a - 1) + 1 := by omega
      conv_lhs => rw [h5, pow_succ]
      field_simp
    rwa [this] at h4

end CatalanCore.Arith.Hybrid.LemmaE
