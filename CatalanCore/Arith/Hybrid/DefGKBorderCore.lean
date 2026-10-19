module

public import CatalanCore.Arith.Hybrid.DefGKCore

@[expose] public section

/-!
# The bordered vector-partner T-route (generic)

`tcore_vec_border`: let `F` be indexed by `ι ⊕ Option κ` (the clean block `ι`, the zone `κ`, and one
extra node `none`, the border).  The inner matrix `F₀` (indices `ι ⊕ κ`) satisfies the hypotheses of
`tcore_vec` (with integral partners `α`, `β`), and the border row / column entries are
`p^w`-integral (corner `p^{2w}`).  Then `GLE p (2 |ι| + 2 w) (det F)`.

The proof rescales the border row and column by `p^w`; the scaled matrix has the *same* clean block
`A`, so `tcore_scaled` applies with `b = 0`: the inner Schur-complement entries are those of
`tcore_vec_T`, the border ones are `Σ (p^w C) adj(Ã) (p² B)`.  Nothing is frame-specific.
-/

open Polynomial Finset Matrix CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid.LemmaE

section BorderGen

variable {p : ℕ} [Fact p.Prime]

lemma int1_iff_gle0 (f : ℚ[X]) : Int1 p f ↔ GLE p 0 f := by
  rw [gle_iff_gn]; simp [Int1]

lemma int1_Cpow_iff (w : ℕ) (f : ℚ[X]) : Int1 p (C ((p : ℚ) ^ w) * f) ↔ GLE p w f := by
  rw [int1_iff_gle0]
  unfold GLE
  simp only [coeff_C_mul, pow_zero, one_mul]

lemma gle_of_Cpow_mul {a k : ℕ} {f : ℚ[X]} (h : GLE p a (C ((p : ℚ) ^ k) * f)) :
    GLE p (a + k) f := by
  intro i
  have := h i
  simp only [coeff_C_mul] at this
  have e : (p : ℚ) ^ (a + k) * f.coeff i = (p : ℚ) ^ a * ((p : ℚ) ^ k * f.coeff i) := by ring
  rw [e]; exact this

/-- One term of `C N B` with `N = p adj p`: the factor `p²` is split between the two sides. -/
lemma term_int1 {x y a : ℚ[X]} (e1 e2 : ℕ) (he : e1 + e2 = 2)
    (hx : Int1 p (C ((p : ℚ) ^ e1) * x)) (ha : Int1 p a) (hy : Int1 p (C ((p : ℚ) ^ e2) * y)) :
    Int1 p (x * (C ((p : ℚ) ^ 1) * a * C ((p : ℚ) ^ 1)) * y) := by
  have h : C ((p : ℚ) ^ 1) * C ((p : ℚ) ^ 1) = C ((p : ℚ) ^ e1) * C ((p : ℚ) ^ e2) := by
    rw [← map_mul, ← map_mul, ← pow_add, ← pow_add, he]
  have e : x * (C ((p : ℚ) ^ 1) * a * C ((p : ℚ) ^ 1)) * y =
      (C ((p : ℚ) ^ e1) * x) * a * (C ((p : ℚ) ^ e2) * y) := by
    linear_combination (x * a * y) * h
  rw [e]
  exact (hx.mul ha).mul hy

lemma int1_Cpow (k : ℕ) : Int1 p (C ((p : ℚ) ^ k)) := by
  unfold Int1
  rw [gn_C]
  have := padicNorm.of_nat (p := p) (p ^ k)
  exact_mod_cast (by simpa using this : padicNorm p ((p : ℚ) ^ k) ≤ 1)

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma Nmat_apply_one (A : Matrix ι ι ℚ[X]) (c c' : ι) :
    Nmat p (fun _ : ι => 1) A c c' =
      C ((p : ℚ) ^ 1) * (Atil p (fun _ : ι => 1) A).adjugate c c' * C ((p : ℚ) ^ 1) := by
  simp [Nmat, scl, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul]

lemma Tscaled_apply {κ' : Type} [Fintype κ'] [DecidableEq κ'] (g : ℚ[X]) (A : Matrix ι ι ℚ[X])
    (B : Matrix ι κ' ℚ[X]) (C' : Matrix κ' ι ℚ[X]) (D : Matrix κ' κ' ℚ[X]) (N : Matrix ι ι ℚ[X])
    (z y : κ') :
    Tscaled g A B C' D N z y = g * D z y - ∑ c, ∑ c', C' z c * N c c' * B c' y := by
  simp only [Tscaled, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/-! ### Integrality of `p² B` and `p² C` from the `tcore_vec` hypotheses -/

lemma int1_Cp_Cp_mul {f : ℚ[X]} (hf : gn p f ≤ p) : Int1 p (C ((p : ℚ) ^ 1) * (C ((p : ℚ) ^ 1) * f)) := by
  have h1 := int1_Cp_mul p hf
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  exact int1_Cp_mul p (le_trans h1 hp1)

lemma pow_two_C : C ((p : ℚ) ^ 2) = C ((p : ℚ) ^ 1) * C ((p : ℚ) ^ 1) := by
  rw [← map_mul]; congr 1; ring

lemma block_int2_B (F0 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℚ[X]) (β : Matrix ι κ ℚ[X])
    (hI : ∀ i j, Int1 p (Atil p (fun _ : ι => 1) F0.toBlocks₁₁ i j))
    (hβ : ∀ c y, Int1 p (β c y))
    (hL' : ∀ c y, gn p ((F0.toBlocks₁₂ - F0.toBlocks₁₁ * β) c y) ≤ p) (c : ι) (y : κ) :
    Int1 p (C ((p : ℚ) ^ 2) * F0.toBlocks₁₂ c y) := by
  have hs : ∑ c', Atil p (fun _ : ι => 1) F0.toBlocks₁₁ c c' * β c' y =
      C ((p : ℚ) ^ 2) * ∑ c', F0.toBlocks₁₁ c c' * β c' y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Atil_apply, pow_two_C]; ring
  have e : C ((p : ℚ) ^ 2) * F0.toBlocks₁₂ c y =
      C ((p : ℚ) ^ 1) * (C ((p : ℚ) ^ 1) * (F0.toBlocks₁₂ - F0.toBlocks₁₁ * β) c y) +
      ∑ c', Atil p (fun _ : ι => 1) F0.toBlocks₁₁ c c' * β c' y := by
    rw [hs]
    simp only [Matrix.sub_apply, Matrix.mul_apply]
    rw [pow_two_C]; ring
  rw [e]
  exact (int1_Cp_Cp_mul (hL' c y)).add (Int1.sum fun c' _ => (hI c c').mul (hβ c' y))

lemma block_int2_C (F0 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℚ[X]) (α : Matrix κ ι ℚ[X])
    (hI : ∀ i j, Int1 p (Atil p (fun _ : ι => 1) F0.toBlocks₁₁ i j))
    (hα : ∀ z c, Int1 p (α z c))
    (hL : ∀ z c, gn p ((F0.toBlocks₂₁ - α * F0.toBlocks₁₁) z c) ≤ p) (z : κ) (c : ι) :
    Int1 p (C ((p : ℚ) ^ 2) * F0.toBlocks₂₁ z c) := by
  have hs : ∑ c', α z c' * Atil p (fun _ : ι => 1) F0.toBlocks₁₁ c' c =
      C ((p : ℚ) ^ 2) * ∑ c', α z c' * F0.toBlocks₁₁ c' c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Atil_apply, pow_two_C]; ring
  have e : C ((p : ℚ) ^ 2) * F0.toBlocks₂₁ z c =
      C ((p : ℚ) ^ 1) * (C ((p : ℚ) ^ 1) * (F0.toBlocks₂₁ - α * F0.toBlocks₁₁) z c) +
      ∑ c', α z c' * Atil p (fun _ : ι => 1) F0.toBlocks₁₁ c' c := by
    rw [hs]
    simp only [Matrix.sub_apply, Matrix.mul_apply]
    rw [pow_two_C]; ring
  rw [e]
  exact (int1_Cp_Cp_mul (hL z c)).add (Int1.sum fun c' _ => (hα z c').mul (hI c' c))

end BorderGen

/-! ### Rescaling the border -/

section Scale

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The scaling vector: `p^w` on the border node, `1` elsewhere. -/
noncomputable def bsc (p w : ℕ) : ι ⊕ Option κ → ℚ[X] :=
  Sum.elim (fun _ => 1) (fun o => o.elim (C ((p : ℚ) ^ w)) (fun _ => 1))

/-- `F` with the border row and column multiplied by `p^w`. -/
noncomputable def bscale (p w : ℕ) (F : Matrix (ι ⊕ Option κ) (ι ⊕ Option κ) ℚ[X]) :
    Matrix (ι ⊕ Option κ) (ι ⊕ Option κ) ℚ[X] :=
  Matrix.of fun a b => bsc p w a * F a b * bsc p w b

lemma det_bscale (p w : ℕ) (F : Matrix (ι ⊕ Option κ) (ι ⊕ Option κ) ℚ[X]) :
    (bscale p w F).det = C ((p : ℚ) ^ (w + w)) * F.det := by
  have h : bscale p w F = Matrix.diagonal (bsc p w) * F * Matrix.diagonal (bsc p w) := by
    ext a b; simp [bscale, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hp : ∏ a : ι ⊕ Option κ, bsc p w a = C ((p : ℚ) ^ w) := by
    simp [bsc, Fintype.prod_sum_type, Fintype.prod_option]
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hp, pow_add, map_mul]
  ring

end Scale

/-! ### The bordered T-route -/

section Main

variable {p : ℕ} [Fact p.Prime] {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- **Bordered vector-partner T-route.**  `F` is the inner matrix `F₀` (indices `ι ⊕ κ`) with one
extra border index `none`.  The inner hypotheses are those of `tcore_vec`, plus integral partners
`α, β`; the border row, column and diagonal entries are `p^w`-integral (corner `p^{2w}`). -/
theorem tcore_vec_border (F : Matrix (ι ⊕ Option κ) (ι ⊕ Option κ) ℚ[X])
    (F0 : Matrix (ι ⊕ κ) (ι ⊕ κ) ℚ[X])
    (hF0 : ∀ a b, F (Sum.map id some a) (Sum.map id some b) = F0 a b) (w : ℕ)
    (hI : ∀ i j, Int1 p (Atil p (fun _ : ι => 1) F0.toBlocks₁₁ i j))
    (hprim : gn p (Atil p (fun _ : ι => 1) F0.toBlocks₁₁).det = 1)
    (α : Matrix κ ι ℚ[X]) (β : Matrix ι κ ℚ[X])
    (hα : ∀ z c, Int1 p (α z c)) (hβ : ∀ c y, Int1 p (β c y))
    (hL : ∀ z c, gn p ((F0.toBlocks₂₁ - α * F0.toBlocks₁₁) z c) ≤ p)
    (hL' : ∀ c y, gn p ((F0.toBlocks₁₂ - F0.toBlocks₁₁ * β) c y) ≤ p)
    (hΔ : ∀ z y, Int1 p ((F0.toBlocks₂₂ - α * F0.toBlocks₁₂ - F0.toBlocks₂₁ * β +
      α * F0.toBlocks₁₁ * β) z y))
    (hr : ∀ c, Int1 p (C ((p : ℚ) ^ w) * F (Sum.inr none) (Sum.inl c)))
    (hc : ∀ c, Int1 p (C ((p : ℚ) ^ w) * F (Sum.inl c) (Sum.inr none)))
    (hrd : ∀ y, Int1 p (C ((p : ℚ) ^ w) * F (Sum.inr none) (Sum.inr (some y))))
    (hcd : ∀ z, Int1 p (C ((p : ℚ) ^ w) * F (Sum.inr (some z)) (Sum.inr none)))
    (hdd : Int1 p (C ((p : ℚ) ^ (w + w)) * F (Sum.inr none) (Sum.inr none))) :
    GLE p (2 * Fintype.card ι + (w + w)) F.det := by
  classical
  set A := F0.toBlocks₁₁ with hAdef
  set F' := bscale p w F with hF'
  have hA : F.toBlocks₁₁ = A := by
    refine Matrix.ext fun c c' => ?_; exact hF0 (Sum.inl c) (Sum.inl c')
  have hA' : F'.toBlocks₁₁ = A := by
    rw [← hA]; refine Matrix.ext fun c c' => ?_; simp [hF', bscale, bsc, Matrix.toBlocks₁₁]
  -- the entries of the rescaled matrix
  have e21n : ∀ c, F'.toBlocks₂₁ none c = C ((p : ℚ) ^ w) * F (Sum.inr none) (Sum.inl c) := by
    intro c; simp [hF', bscale, bsc, Matrix.toBlocks₂₁]
  have e21s : ∀ z c, F'.toBlocks₂₁ (some z) c = F0.toBlocks₂₁ z c := by
    intro z c; simp [hF', bscale, bsc, Matrix.toBlocks₂₁]; exact hF0 (Sum.inr z) (Sum.inl c)
  have e12n : ∀ c, F'.toBlocks₁₂ c none = F (Sum.inl c) (Sum.inr none) * C ((p : ℚ) ^ w) := by
    intro c; simp [hF', bscale, bsc, Matrix.toBlocks₁₂]
  have e12s : ∀ c y, F'.toBlocks₁₂ c (some y) = F0.toBlocks₁₂ c y := by
    intro c y; simp [hF', bscale, bsc, Matrix.toBlocks₁₂]; exact hF0 (Sum.inl c) (Sum.inr y)
  have e22nn : F'.toBlocks₂₂ none none =
      C ((p : ℚ) ^ (w + w)) * F (Sum.inr none) (Sum.inr none) := by
    simp [hF', bscale, bsc, Matrix.toBlocks₂₂, pow_add]; ring
  have e22ns : ∀ y, F'.toBlocks₂₂ none (some y) =
      C ((p : ℚ) ^ w) * F (Sum.inr none) (Sum.inr (some y)) := by
    intro y; simp [hF', bscale, bsc, Matrix.toBlocks₂₂]
  have e22sn : ∀ z, F'.toBlocks₂₂ (some z) none =
      F (Sum.inr (some z)) (Sum.inr none) * C ((p : ℚ) ^ w) := by
    intro z; simp [hF', bscale, bsc, Matrix.toBlocks₂₂]
  have e22ss : ∀ z y, F'.toBlocks₂₂ (some z) (some y) = F0.toBlocks₂₂ z y := by
    intro z y; simp [hF', bscale, bsc, Matrix.toBlocks₂₂]; exact hF0 (Sum.inr z) (Sum.inr y)
  have hB2 := block_int2_B F0 β hI hβ hL'
  have hC2 := block_int2_C F0 α hI hα hL
  have hadj : ∀ i j, Int1 p ((Atil p (fun _ : ι => 1) A).adjugate i j) := adj_int1 hI
  have hg : Int1 p (Atil p (fun _ : ι => 1) A).det := by unfold Int1; rw [hprim]
  have hT : ∀ z y : Option κ, GLE p 0 (Tscaled (Atil p (fun _ : ι => 1) F'.toBlocks₁₁).det
      F'.toBlocks₁₁ F'.toBlocks₁₂ F'.toBlocks₂₁ F'.toBlocks₂₂
      (Nmat p (fun _ : ι => 1) F'.toBlocks₁₁) z y) := by
    intro z y
    rw [hA']
    rw [Tscaled_apply, ← int1_iff_gle0]
    simp only [Nmat_apply_one]
    rcases z with _ | z <;> rcases y with _ | y
    · -- corner
      refine Int1.sub ?_ (Int1.sum fun c _ => Int1.sum fun c' _ => ?_)
      · rw [e22nn]; exact hg.mul hdd
      · rw [e21n, e12n]
        refine term_int1 0 2 (by omega) (by simpa using hr c) (hadj c c') ?_
        exact (int1_Cpow 2).mul (by rw [mul_comm]; exact hc c')
    · -- border row
      refine Int1.sub ?_ (Int1.sum fun c _ => Int1.sum fun c' _ => ?_)
      · rw [e22ns]; exact hg.mul (hrd y)
      · rw [e21n, e12s]
        exact term_int1 0 2 (by omega) (by simpa using hr c) (hadj c c') (hB2 c' y)
    · -- border column
      refine Int1.sub ?_ (Int1.sum fun c _ => Int1.sum fun c' _ => ?_)
      · rw [e22sn]; exact hg.mul (by rw [mul_comm]; exact hcd z)
      · rw [e21s, e12n]
        exact term_int1 2 0 (by omega) (hC2 z c) (hadj c c') (by simpa [mul_comm] using hc c')
    · -- inner block
      have := tcore_vec_T F0 hI hprim α β hL hL' hΔ z y
      rw [Tscaled_apply, ← int1_iff_gle0] at this
      simp only [Nmat_apply_one] at this
      simpa only [e22ss, e21s, e12s] using this
  have key := tcore_scaled p F' (fun _ : ι => 1) (Atil p (fun _ : ι => 1) A)
    (by rw [hA']; exact hI) hI (by rw [hA']; exact fun i j => Cng.refl _) hprim 0 hT
  rw [det_bscale] at key
  have := gle_of_Cpow_mul key
  simpa using this

end Main

end CatalanCore.Arith.Hybrid.LemmaE
