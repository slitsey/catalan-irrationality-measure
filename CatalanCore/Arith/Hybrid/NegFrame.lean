module

public import CatalanCore.Arith.Hybrid.InstNeg
public import CatalanCore.Arith.Hybrid.DefRank

@[expose] public section

/-!
# Sign transfer of the hybrid determinant polynomial

If `Fr₂.Mn = -Fr₁.Mn` then `Fr₂.fullPoly r m = (-1)^(r+m) · (Fr₁.fullPoly r m)(-X)`; hence `GLE` and
`DefHypT` statements transfer.  Used to move the λ-like machinery (`LamData Fr 3`, the frame `mirNFrame`)
to the legacy mirror frame `mirFrame`.
-/

open Polynomial Finset CatalanCore CatalanCore.Arith CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid

lemma coeff_comp_neg_X' (f : ℚ[X]) (n : ℕ) :
    (f.comp (-(Polynomial.X : ℚ[X]))).coeff n = (-1) ^ n * f.coeff n := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.add_comp, Polynomial.coeff_add, hp, hq, Polynomial.coeff_add, mul_add]
  | monomial k a =>
    have e : (Polynomial.monomial k a).comp (-(Polynomial.X : ℚ[X])) =
        Polynomial.C (a * (-1) ^ k) * Polynomial.X ^ k := by
      rw [Polynomial.monomial_comp, neg_pow, Polynomial.C_mul, Polynomial.C_pow]
      simp [mul_assoc]
    rw [e, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_monomial]
    by_cases h : n = k
    · subst h; simp [mul_comm]
    · simp [h, Ne.symm h]

lemma GLE.neg_comp {p : ℕ} [Fact p.Prime] {B : ℕ} {f : ℚ[X]} (h : GLE p B f) (c : ℚ)
    (hc : c = 1 ∨ c = -1) : GLE p B (C c * f.comp (-(Polynomial.X : ℚ[X]))) := by
  intro i
  rw [coeff_C_mul, coeff_comp_neg_X']
  have := h i
  have e : (p : ℚ) ^ B * (c * ((-1) ^ i * f.coeff i)) = (c * (-1) ^ i) * ((p : ℚ) ^ B * f.coeff i) := by
    ring
  rw [e]
  have hu : c * (-1) ^ i = 1 ∨ c * (-1) ^ i = -1 := by
    rcases hc with rfl | rfl <;> rcases neg_one_pow_eq_or ℚ i with h | h <;> simp [h]
  rcases hu with h' | h'
  · rw [h', one_mul]; exact this
  · rw [h', neg_one_mul]; exact (LocRing p).neg_mem this

variable {Fr₁ Fr₂ : Frame}

lemma fullPoly_neg (hM : ∀ a b, Fr₂.Mn a b = -Fr₁.Mn a b) (r m : ℕ) :
    Fr₂.fullPoly r m = C ((-1 : ℚ) ^ (r + m)) * (Fr₁.fullPoly r m).comp (-(Polynomial.X : ℚ[X])) := by
  unfold Frame.fullPoly
  set M₁ : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) ℚ[X] := Matrix.of fun a b : Fin r ⊕ Fin m =>
    (match a, b with
      | Sum.inl c, Sum.inl c' => if c = c' then (Polynomial.X : ℚ[X]) else 0
      | _, _ => 0) + C (Fr₁.Mn (Frame.hybRow r m a) (Frame.hybCol r m b)) with hM₁
  set M₂ : Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) ℚ[X] := Matrix.of fun a b : Fin r ⊕ Fin m =>
    (match a, b with
      | Sum.inl c, Sum.inl c' => if c = c' then (Polynomial.X : ℚ[X]) else 0
      | _, _ => 0) + C (Fr₂.Mn (Frame.hybRow r m a) (Frame.hybCol r m b)) with hM₂
  have h1 : M₂ = -(M₁.map (fun f => f.comp (-(Polynomial.X : ℚ[X])))) := by
    refine Matrix.ext fun a b => ?_
    simp only [hM₁, hM₂, Matrix.of_apply, Matrix.neg_apply, Matrix.map_apply, hM, C_neg,
      Polynomial.add_comp, Polynomial.C_comp]
    rcases a with c | c <;> rcases b with c' | c' <;> simp <;> split_ifs <;> simp <;> ring
  have h2 : (M₁.map (fun f => f.comp (-(Polynomial.X : ℚ[X])))).det = M₁.det.comp (-X) := by
    have := RingHom.map_det (Polynomial.compRingHom (-(Polynomial.X : ℚ[X]))) M₁
    simpa using this.symm
  change M₂.det = _
  rw [h1, Matrix.det_neg, h2]
  simp [Fintype.card_sum, C_pow]
  rfl

/-- `GLE` transfers along the sign change. -/
lemma GLE.of_neg_frame (hM : ∀ a b, Fr₂.Mn a b = -Fr₁.Mn a b) {p : ℕ} [Fact p.Prime] {B r m : ℕ}
    (h : GLE p B (Fr₁.fullPoly r m)) : GLE p B (Fr₂.fullPoly r m) := by
  rw [fullPoly_neg hM]
  exact GLE.neg_comp h _ (by rcases neg_one_pow_eq_or ℚ (r + m) with h | h <;> simp [h])

/-- `DefHypT` transfers along a sign change of the instance (same `Bnd`). -/
lemma DefHypT.of_neg {I₁ : HybInst Fr₁} {I₂ : HybInst Fr₂} (hM : ∀ a b, Fr₂.Mn a b = -Fr₁.Mn a b)
    {r m : ℕ} {T δ : ℕ → ℕ} (hB : Bnd I₂ r m = Bnd I₁ r m) (h : DefHypT I₁ r m T δ) :
    DefHypT I₂ r m T δ := by
  intro p hp hb
  rw [hB] at hb
  obtain ⟨h1, h2⟩ := h p hp hb
  exact ⟨h1, fun [Fact p.Prime] => GLE.of_neg_frame hM h2⟩

end CatalanCore.Arith.Hybrid
