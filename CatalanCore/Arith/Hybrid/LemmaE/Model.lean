module

public import CatalanCore.Arith.Hybrid.LemmaE.P1Core
public import Mathlib.FieldTheory.RatFunc.Basic

@[expose] public section

/-!
# The scalar-Schur model matrix

`modelM s V W Q Qi = [[s·1 + V Qi W, V], [W, Q]]` (with `Q Qi = Qi Q = 1`) has Schur complement
`s·1`.  Its determinant is `det Q · s^{|U|}` and its inverse has `UU`-block `s⁻¹ 1`; hence
`adj(M)` vanishes off the diagonal of `UU` (`modelM_adj_UU`).  This is the exact algebra behind
DQ Lemma 3.1 ("`S̄ ≡ s₀ I`", via harmonic reflection) once `Ã ≡ modelM`.
-/

open Polynomial Matrix

namespace CatalanCore.Arith.Hybrid.LemmaE

variable {U P : Type} [Fintype U] [DecidableEq U] [Fintype P] [DecidableEq P]

/-- The model block matrix. -/
noncomputable def modelM (s : ℚ[X]) (V : Matrix U P ℚ[X]) (W : Matrix P U ℚ[X])
    (Q Qi : Matrix P P ℚ[X]) : Matrix (U ⊕ P) (U ⊕ P) ℚ[X] :=
  fromBlocks (s • (1 : Matrix U U ℚ[X]) + V * Qi * W) V W Q

theorem modelM_det (s : ℚ[X]) (V : Matrix U P ℚ[X]) (W : Matrix P U ℚ[X])
    (Q Qi : Matrix P P ℚ[X]) (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) :
    (modelM s V W Q Qi).det = Q.det * s ^ Fintype.card U := by
  letI : Invertible Q := ⟨Qi, h2, h1⟩
  have hi : ⅟Q = Qi := rfl
  unfold modelM
  rw [Matrix.det_fromBlocks₂₂, hi]
  have : s • (1 : Matrix U U ℚ[X]) + V * Qi * W - V * Qi * W = s • 1 := by abel
  rw [this, Matrix.det_smul, Matrix.det_one, mul_one]

theorem modelM_adj_UU (s : ℚ[X]) (hs : s ≠ 0) (V : Matrix U P ℚ[X]) (W : Matrix P U ℚ[X])
    (Q Qi : Matrix P P ℚ[X]) (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (u u' : U) (hne : u ≠ u') :
    (modelM s V W Q Qi).adjugate (Sum.inl u) (Sum.inl u') = 0 := by
  classical
  let K := FractionRing ℚ[X]
  let φ : ℚ[X] →+* K := algebraMap ℚ[X] K
  have hφ : Function.Injective φ := IsFractionRing.injective ℚ[X] K
  have hsK : φ s ≠ 0 := (map_ne_zero_iff φ hφ).mpr hs
  set Mk : Matrix (U ⊕ P) (U ⊕ P) K := (modelM s V W Q Qi).map φ
  set Vk := V.map φ
  set Wk := W.map φ
  set Qk := Q.map φ
  set Qik := Qi.map φ
  have hQ1 : Qk * Qik = 1 := by
    have := congrArg (fun M : Matrix P P ℚ[X] => M.map φ) h1
    simpa [Qk, Qik, Matrix.map_mul] using this
  have hQ2 : Qik * Qk = 1 := mul_eq_one_comm.mp hQ1
  set Mi : Matrix (U ⊕ P) (U ⊕ P) K :=
    fromBlocks ((φ s)⁻¹ • (1 : Matrix U U K)) (-((φ s)⁻¹ • (Vk * Qik)))
      (-((φ s)⁻¹ • (Qik * Wk))) (Qik + (φ s)⁻¹ • (Qik * Wk * Vk * Qik)) with hMi
  have hm_mul : ∀ {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a]
      [DecidableEq b] [DecidableEq c] (X : Matrix a b ℚ[X]) (Y : Matrix b c ℚ[X]),
      (X * Y).map φ = X.map φ * Y.map φ := fun X Y => by
    ext i j; simp [Matrix.mul_apply]
  have hMk : Mk = fromBlocks (φ s • (1 : Matrix U U K) + Vk * Qik * Wk) Vk Wk Qk := by
    simp only [Mk, modelM, Matrix.fromBlocks_map, Vk, Wk, Qk, Qik]
    congr 1
    rw [show ∀ X Y : Matrix U U ℚ[X], (X + Y).map φ = X.map φ + Y.map φ from
      fun X Y => φ.mapMatrix.map_add X Y, hm_mul, hm_mul]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have hMM : Mk * Mi = 1 := by
    rw [hMk, hMi, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    have hs1 : φ s • (1 : Matrix U U K) * ((φ s)⁻¹ • 1) = 1 := by
      rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hsK, one_smul]
    have e1 : ∀ {n : Type} [Fintype n] [DecidableEq n] (X : Matrix P n K), Qk * (Qik * X) = X :=
      fun X => by rw [← Matrix.mul_assoc, hQ1, Matrix.one_mul]
    have e2 : Qk * Qik = 1 := hQ1
    have hsi : (φ s)⁻¹ * φ s = 1 := inv_mul_cancel₀ hsK
    congr 1
    · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hsK, one_smul, Matrix.mul_assoc, smul_add, smul_neg, hsi]
      abel
    · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hsK, one_smul,
        Matrix.mul_assoc, smul_neg, smul_add, hsi]
      abel
    · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul, e1, one_smul, Matrix.mul_assoc]
      abel
    · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_smul, e1, e2, Matrix.mul_assoc]
      abel
  have hMM' : Mi * Mk = 1 := mul_eq_one_comm.mp hMM
  have hadj : Mk.adjugate = Mk.det • Mi := by
    have := Matrix.mul_adjugate Mk
    calc Mk.adjugate = (Mi * Mk) * Mk.adjugate := by rw [hMM', Matrix.one_mul]
      _ = Mi * (Mk * Mk.adjugate) := by rw [Matrix.mul_assoc]
      _ = Mk.det • Mi := by rw [this, Matrix.mul_smul, Matrix.mul_one]
  have hmapadj : (modelM s V W Q Qi).adjugate.map φ = Mk.adjugate := by
    have := (RingHom.map_adjugate φ (modelM s V W Q Qi))
    simpa using this
  apply hφ
  have e := congrFun (congrFun hadj (Sum.inl u)) (Sum.inl u')
  have e2 : φ ((modelM s V W Q Qi).adjugate (Sum.inl u) (Sum.inl u')) =
      Mk.adjugate (Sum.inl u) (Sum.inl u') := by
    rw [← hmapadj]; rfl
  rw [e2, e]
  simp [hMi, Matrix.one_apply, hne]

variable (p : ℕ) [Fact p.Prime]

lemma gn_X : gn p (X : ℚ[X]) = 1 := by
  have : (X : ℚ[X]) = monomial 1 1 := Polynomial.monomial_one_one_eq_X.symm
  rw [this]; simp [gn]

/-- `X - h` with `h ∈ ℤ_(p)` is primitive. -/
lemma gn_X_sub_C (h : ℚ) (hh : padicNorm p h ≤ 1) : gn p (X - C h : ℚ[X]) = 1 := by
  apply le_antisymm
  · refine (gn_sub_le _ _).trans (max_le (gn_X p).le ?_)
    rw [gn_C]; exact_mod_cast hh
  · have := padic_coeff_le_gn p (X - C h : ℚ[X]) 1
    simpa using this

/-- Primitivity of the determinant of the model. -/
lemma modelM_prim (s : ℚ[X]) (hs : gn p s = 1) (V : Matrix U P ℚ[X]) (W : Matrix P U ℚ[X])
    (Q Qi : Matrix P P ℚ[X]) (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hQ : gn p Q.det = 1) :
    gn p (modelM s V W Q Qi).det = 1 := by
  rw [modelM_det s V W Q Qi h1 h2, gn_mul, gn_pow, hs, hQ]; simp

end CatalanCore.Arith.Hybrid.LemmaE
