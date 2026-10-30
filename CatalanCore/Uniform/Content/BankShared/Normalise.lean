module

public import CatalanCore.Uniform.Content.Shape.Alt
public import CatalanCore.Uniform.Content.Shape.Reindex

@[expose] public section
set_option Elab.async false

/-! # Shared contract 2 (lane H17): normalisation transport

If `Fr.Mn = N⁻¹ * Fr0.Mn` (entrywise, fixed nonzero rational `N`) and `Fr.const = N⁻¹ * Fr0.const`,
then, for every node data `(c, xs, ys)` with `h = |ι| + |κ|`,

    det FullN Fr c xs ys X = C (N⁻¹ ^ h) * (det FullN Fr0 c xs ys X).comp (C N * X).

Transported to the family level (`PolyFamily.normScale`): scaled coefficient content and scaled
decay pass from `Fam0` to `Fam` with the SAME rates `Λ`, `D`, `c`, provided the exponent `h` and the
degree grow at most linearly in the scale. -/

namespace CatalanCore.Uniform.Content.BankShared
open Polynomial Finset CatalanCore CatalanCore.Rect CatalanCore.Uniform

section Poly

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem fullN_scale (Fr Fr0 : Frame) {N : ℚ} (hN : N ≠ 0)
    (hMn : ∀ a b, Fr.Mn a b = N⁻¹ * Fr0.Mn a b) {R : Type*} [CommRing R] [Algebra ℚ R]
    (c : ι → ℕ) (xs ys : κ → ℕ) (x : R) :
    FullN Fr c xs ys x =
      algebraMap ℚ R N⁻¹ • FullN Fr0 c xs ys (algebraMap ℚ R N * x) := by
  have hNR : algebraMap ℚ R N⁻¹ * algebraMap ℚ R N = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hN, map_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [FullN, Blk, blkA, blkB, blkC, blkD, Matrix.fromBlocks, Matrix.one_apply, hMn,
      mul_add, ← mul_assoc, hNR]
  all_goals first | rfl | (split_ifs <;> simp [hNR])

theorem fullN_comp (Fr : Frame) (c : ι → ℕ) (xs ys : κ → ℕ) (f : ℚ[X]) :
    FullN Fr c xs ys f =
      (FullN Fr c xs ys (X : ℚ[X])).map (Polynomial.compRingHom f) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [FullN, Blk, blkA, blkB, blkC, blkD, Matrix.fromBlocks, Matrix.one_apply] <;>
    split_ifs <;> simp

/-- **The normalisation identity** for a general node datum. -/
theorem normalisation_det (Fr Fr0 : Frame) {N : ℚ} (hN : N ≠ 0)
    (hMn : ∀ a b, Fr.Mn a b = N⁻¹ * Fr0.Mn a b) (c : ι → ℕ) (xs ys : κ → ℕ) :
    (FullN Fr c xs ys (X : ℚ[X])).det =
      C ((N⁻¹) ^ (Fintype.card ι + Fintype.card κ)) *
        (FullN Fr0 c xs ys (X : ℚ[X])).det.comp (C N * X) := by
  have h1 := fullN_scale Fr Fr0 hN hMn (R := ℚ[X]) c xs ys (X : ℚ[X])
  rw [h1, Matrix.det_smul, fullN_comp Fr0 c xs ys (algebraMap ℚ ℚ[X] N * X)]
  have h2 : (Polynomial.compRingHom (algebraMap ℚ ℚ[X] N * X))
      (FullN Fr0 c xs ys (X : ℚ[X])).det =
      ((FullN Fr0 c xs ys (X : ℚ[X])).map (Polynomial.compRingHom (algebraMap ℚ ℚ[X] N * X))).det := by
    simpa [RingHom.mapMatrix_apply] using
      RingHom.map_det (Polynomial.compRingHom (algebraMap ℚ ℚ[X] N * X))
        (FullN Fr0 c xs ys (X : ℚ[X]))
  rw [← h2]
  simp only [Fintype.card_sum, Polynomial.algebraMap_eq, map_pow]
  rw [Polynomial.coe_compRingHom_apply]

end Poly


/-! ### Node-family level -/

section NodeLevel

theorem normalisation_poly (Fr Fr0 : Frame) (G : NodeFamily) (i : G.Index) {N : ℚ} (hN : N ≠ 0)
    (hMn : ∀ a b, Fr.Mn a b = N⁻¹ * Fr0.Mn a b) :
    G.polynomial Fr i =
      C ((N⁻¹) ^ (i.2.card + (G i.1).k)) * (G.polynomial Fr0 i).comp (C N * X) := by
  unfold NodeFamily.polynomial
  rw [normalisation_det Fr Fr0 hN hMn]
  simp [Fintype.card_coe]

end NodeLevel

/-! ### Family level: content and decay transport -/

/-- The family with the same index data as `Fam0`, constant `c1` and members `Q1`. -/
def _root_.CatalanCore.PolyFamily.reQ (Fam0 : PolyFamily) (c1 : ℝ) (Q1 : Fam0.ι → ℚ[X]) :
    PolyFamily :=
  { Fam0 with const := c1, Q := Q1 }

/-- The family obtained from `Fam0` by the normalisation change `N`: member polynomials
`C (N⁻¹ ^ h i) * (Q0 i).comp (C N * X)` and constant `N⁻¹ * const0`. -/
noncomputable def _root_.CatalanCore.PolyFamily.normScale (Fam0 : PolyFamily) (N : ℚ)
    (h : Fam0.ι → ℕ) : PolyFamily :=
  Fam0.reQ (((N⁻¹ : ℚ) : ℝ) * Fam0.const)
    (fun i => C ((N⁻¹) ^ h i) * (Fam0.Q i).comp (C N * X))

theorem reQ_evalQ (Fam0 : PolyFamily) (N : ℚ) (h : Fam0.ι → ℕ) (c1 : ℝ) (Q1 : Fam0.ι → ℚ[X])
    (hQ : ∀ i, Q1 i = C ((N⁻¹) ^ h i) * (Fam0.Q i).comp (C N * X)) (i : Fam0.ι) (x : ℚ) :
    (Fam0.reQ c1 Q1).evalQ i x = (N⁻¹) ^ h i * Fam0.evalQ i (N * x) := by
  have : (Fam0.reQ c1 Q1).Q i = Q1 i := rfl
  simp [PolyFamily.evalQ, this, hQ i, Polynomial.eval_comp]

theorem reQ_evalR (Fam0 : PolyFamily) (N : ℚ) (h : Fam0.ι → ℕ) (c1 : ℝ) (Q1 : Fam0.ι → ℚ[X])
    (hQ : ∀ i, Q1 i = C ((N⁻¹) ^ h i) * (Fam0.Q i).comp (C N * X)) (i : Fam0.ι) (y : ℝ) :
    (Fam0.reQ c1 Q1).evalR i y = ((N⁻¹ : ℚ) : ℝ) ^ h i * Fam0.evalR i ((N : ℝ) * y) := by
  have : (Fam0.reQ c1 Q1).Q i = Q1 i := rfl
  simp [PolyFamily.evalR, this, hQ i, Polynomial.aeval_comp]

theorem affine_mul_le_sq (A K T ε : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K) (hT : 0 ≤ T) (hε : 0 < ε) :
    ∃ R : ℕ, ∀ s : ℕ, R ≤ s → (A * s + K) * T ≤ ε * (s : ℝ) ^ 2 := by
  obtain ⟨R, hR⟩ := exists_nat_ge ((A + K) * T / ε + 1)
  refine ⟨R, fun s hs => ?_⟩
  have hs' : ((A + K) * T / ε + 1 : ℝ) ≤ s := hR.trans (by exact_mod_cast hs)
  have hs1 : (1 : ℝ) ≤ s := by
    have : 0 ≤ (A + K) * T / ε := by positivity
    linarith
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have h1 : (A + K) * T ≤ ε * s := by
    have := (div_le_iff₀ hε).1 (by linarith : (A + K) * T / ε ≤ s)
    linarith
  calc (A * s + K) * T ≤ (A + K) * T * s := by nlinarith [mul_nonneg hK hT]
    _ ≤ ε * s * s := mul_le_mul_of_nonneg_right h1 hs0
    _ = ε * (s : ℝ) ^ 2 := by ring

/-- **Content transport (shared contract 2).**  Scaled coefficient content passes from `Fam0` to
the normalised family with the same rate `Λ`, if the degree and the exponent `h` grow linearly in
the scale. -/
theorem normScale_hasScaledContent (Fam0 : PolyFamily) (sc : Fam0.ι → ℕ) {Λ : ℝ} {N : ℚ}
    (hN : N ≠ 0) (h : Fam0.ι → ℕ) (c1 : ℝ) (Q1 : Fam0.ι → ℚ[X])
    (hQ : ∀ i, Q1 i = C ((N⁻¹) ^ h i) * (Fam0.Q i).comp (C N * X)) {A K : ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hdeg : ∀ i, Fam0.Adm i → (Fam0.deg i : ℝ) ≤ A * sc i + K)
    (hh : ∀ i, Fam0.Adm i → (h i : ℝ) ≤ A * sc i + K)
    (H : HasScaledContent Fam0 sc Λ) : HasScaledContent (Fam0.reQ c1 Q1) sc Λ := by
  obtain ⟨den, hpos, hint, hlog⟩ := H
  have ha0 : N.num ≠ 0 := Rat.num_ne_zero.2 hN
  have hb0 : N.den ≠ 0 := N.den_nz
  have hapos : 0 < N.num.natAbs := Int.natAbs_pos.2 ha0
  refine ⟨fun i => den i * N.den ^ Fam0.deg i * N.num.natAbs ^ h i, fun i => ?_, ?_, ?_⟩
  · have := hpos i
    positivity
  · intro i hi p q hq
    obtain ⟨z0, hz0⟩ := hint i hi (N.num * p) ((N.den : ℤ) * q) (by positivity)
    obtain ⟨s, hs, hsa⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ (N.num.natAbs : ℚ) = s * N.num := by
      rcases Int.natAbs_eq N.num with h1 | h1
      · refine ⟨1, Or.inl rfl, ?_⟩
        have : ((N.num.natAbs : ℤ) : ℚ) = (N.num : ℚ) := by exact_mod_cast h1.symm
        simpa using this
      · refine ⟨-1, Or.inr rfl, ?_⟩
        have : ((N.num.natAbs : ℤ) : ℚ) = -(N.num : ℚ) := by
          have := congrArg (fun z : ℤ => (z : ℚ)) h1
          push_cast at this ⊢
          linarith
        simpa using this
    refine ⟨z0 * (N.den : ℤ) ^ h i * s ^ h i, ?_⟩
    have hNq : N = (N.num : ℚ) / (N.den : ℚ) := (Rat.num_div_den N).symm
    have hmul : N * ((p : ℚ) / (q : ℚ)) =
        (((N.num * p : ℤ) : ℚ)) / ((((N.den : ℤ) * q : ℤ)) : ℚ) := by
      push_cast
      conv_lhs => rw [hNq]
      field_simp
    beta_reduce
    have hev := reQ_evalQ Fam0 N h c1 Q1 hQ i ((p : ℚ) / (q : ℚ))
    have hdeg_eq : (Fam0.reQ c1 Q1).deg i = Fam0.deg i := rfl
    rw [hdeg_eq, hev, hmul]
    have hqne : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
    have hane : (N.num : ℚ) ≠ 0 := by exact_mod_cast ha0
    have hbne : (N.den : ℚ) ≠ 0 := by exact_mod_cast hb0
    have hNi : N⁻¹ = (N.den : ℚ) / (N.num : ℚ) := by
      conv_lhs => rw [hNq]
      rw [inv_div]
    rw [hNi]
    have hz0' : ((N.den : ℚ) * q) ^ Fam0.deg i * (den i : ℚ) *
        Fam0.evalQ i (((N.num * p : ℤ) : ℚ) / (((N.den : ℤ) * q : ℤ) : ℚ)) = z0 := by
      have := hz0
      push_cast at this ⊢
      exact this
    set v := Fam0.evalQ i (((N.num * p : ℤ) : ℚ) / (((N.den : ℤ) * q : ℤ) : ℚ)) with hv
    push_cast
    rw [hsa]
    have hz0'' : (z0 : ℚ) = ((N.den : ℚ) * q) ^ Fam0.deg i * (den i : ℚ) * v := hz0'.symm
    rw [hz0'']
    have hs2 : ((s : ℚ)) ^ 2 = 1 := by
      rcases hs with rfl | rfl <;> norm_num
    have hcancel : (N.num : ℚ) ^ h i * ((N.num : ℚ)⁻¹) ^ h i = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hane, one_pow]
    field_simp
    linear_combination ((q : ℚ) ^ Fam0.deg i * (den i : ℚ) * (N.den : ℚ) ^ Fam0.deg i *
      (N.den : ℚ) ^ h i * (s : ℚ) ^ h i * v) * hcancel
  · intro ε hε
    obtain ⟨R1, hR1⟩ := hlog (ε / 2) (by positivity)
    set T : ℝ := Real.log (N.den : ℝ) + Real.log (N.num.natAbs : ℝ) with hT
    have hT0 : 0 ≤ T := by
      have h1 : 0 ≤ Real.log (N.den : ℝ) := Real.log_natCast_nonneg _
      have h2 : 0 ≤ Real.log (N.num.natAbs : ℝ) := Real.log_natCast_nonneg _
      linarith
    obtain ⟨R2, hR2⟩ := affine_mul_le_sq A K T (ε / 2) hA hK hT0 (by positivity)
    refine ⟨max R1 R2, fun i hi hR => ?_⟩
    have h1 := hR1 i hi ((le_max_left _ _).trans hR)
    have h2 := hR2 (sc i) ((le_max_right _ _).trans hR)
    have hden0 : (0 : ℝ) < den i := by exact_mod_cast hpos i
    have hbpos : (0 : ℝ) < N.den := by exact_mod_cast Nat.pos_of_ne_zero hb0
    have hapos' : (0 : ℝ) < N.num.natAbs := by exact_mod_cast hapos
    have hlogden : Real.log ((den i * N.den ^ Fam0.deg i * N.num.natAbs ^ h i : ℕ) : ℝ) =
        Real.log (den i) + Fam0.deg i * Real.log N.den + h i * Real.log N.num.natAbs := by
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]
    show Real.log ((den i * N.den ^ Fam0.deg i * N.num.natAbs ^ h i : ℕ) : ℝ) ≤ _
    rw [hlogden]
    have lb : (0 : ℝ) ≤ Real.log N.den := Real.log_natCast_nonneg _
    have la : (0 : ℝ) ≤ Real.log N.num.natAbs := Real.log_natCast_nonneg _
    have hd1 := hdeg i hi
    have hh1 := hh i hi
    have : (Fam0.deg i : ℝ) * Real.log N.den + h i * Real.log N.num.natAbs ≤
        (A * sc i + K) * T := by
      rw [hT]
      nlinarith [mul_le_mul_of_nonneg_right hd1 lb, mul_le_mul_of_nonneg_right hh1 la,
        mul_nonneg (by positivity : (0:ℝ) ≤ A * sc i + K) lb,
        mul_nonneg (by positivity : (0:ℝ) ≤ A * sc i + K) la]
    nlinarith

end CatalanCore.Uniform.Content.BankShared
