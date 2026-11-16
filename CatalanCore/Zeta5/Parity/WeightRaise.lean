module

public import CatalanCore.Zeta5.Frames.WeightLemma

@[expose] public section

/-!
# ZC26: raising retained radical directions by a half-weight

Generic form of the "one full unit per direction" step of UNIFORM-PARITY-GAIN.

A Gram matrix `G` over `ℚ[X]` has row weights `w i = ν i + θ i` with `ν i ∈ ℤ` and
`θ i ∈ {0, 1/2}` (`θ i = 1/2` for the odd-`ℓ` rows).  After the paid integral scaling
`Gn i j = p^{-ν i - ν j} G i j` (the "normalised" Gram matrix) one has `GV (Gn i j) (θ i + θ j)`.
Let `Ĉ` be a `p`-adic unit change of basis that mixes only rows of equal `θ`, and let `R` be a set of
retained rows (all with `θ = 0`).  If the new Gram matrix `M = Ĉ Gn Ĉᵀ` has `GV (M i j) 1` for
`i ∈ R` and every even `j` (the retained radical rows are orthogonal to every even row to order `1`),
then the weight of every retained row may be raised by `1/2`, and
`v_p^G (det G) ≥ 2 ∑ w + |R|`.

* `GV_one_of_half`: integrality, `GV ≥ 1/2` upgrades to `GV ≥ 1` (valuations are integers).
* `zc26_core`: the weighted determinant bound for given entry bounds of `M`.
* `zc26_entries`: the entry bounds of `M` for the raised weights from the retained rows' vanishing.
* `zc26_weight_raise`: the two combined.
-/

open Finset Polynomial

namespace Apery

variable {p : ℕ} [hp : Fact p.Prime]

/-- Valuations are integers: a Gauss valuation bound `1/2` is a bound `1`. -/
lemma GV_one_of_half {f : ℚ[X]} (h : GV p f (1 / 2)) : GV p f 1 := by
  intro n
  rcases h n with h0 | h0
  · exact Or.inl h0
  · right
    have h1 : (1 : ℚ) / 2 ≤ ((padicValRat p (f.coeff n) : ℤ) : ℚ) := h0
    have h2 : (0 : ℤ) < padicValRat p (f.coeff n) := by
      have : (0 : ℚ) < ((padicValRat p (f.coeff n) : ℤ) : ℚ) := by linarith
      exact_mod_cast this
    have h3 : (1 : ℤ) ≤ padicValRat p (f.coeff n) := h2
    exact_mod_cast h3

section core
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The normalised Gram matrix `Gn i j = p^{-ν i - ν j} G i j`. -/
noncomputable def normGram (ν : ι → ℤ) (G : Matrix ι ι ℚ[X]) : Matrix ι ι ℚ[X] :=
  Matrix.of fun i j => C ((p : ℚ) ^ (-ν i - ν j)) * G i j

/-- The raised weights `θ' = θ + 1/2` on the retained rows. -/
noncomputable def raisedθ (θ : ι → ℚ) (R : Finset ι) (i : ι) : ℚ :=
  θ i + if i ∈ R then 1 / 2 else 0

/-- **ZC26, core.**  Bounds for the conjugated normalised Gram matrix give the determinant bound
`2 ∑ (ν + θ') = 2 ∑ (ν + θ) + |R|`. -/
theorem zc26_core (G : Matrix ι ι ℚ[X]) (ν : ι → ℤ) (θ : ι → ℚ) (R : Finset ι)
    (Cm : Matrix ι ι ℚ) (hdet : Cm.det ≠ 0) (hunit : padicValRat p Cm.det = 0)
    (hM : ∀ i j, GV p ((Cm.map (C : ℚ →+* ℚ[X]) * normGram (p := p) ν G *
        (Cm.map (C : ℚ →+* ℚ[X])).transpose) i j) (raisedθ θ R i + raisedθ θ R j)) :
    GV p G.det (2 * ∑ i, ((ν i : ℚ) + θ i) + R.card) := by
  classical
  set Dm : Matrix ι ι ℚ[X] := Matrix.diagonal fun i => C ((p : ℚ) ^ ν i) with hDm
  set Di : Matrix ι ι ℚ[X] := Matrix.diagonal fun i => C ((p : ℚ) ^ (-ν i)) with hDi
  set Cm' : Matrix ι ι ℚ[X] := Cm.map (C : ℚ →+* ℚ[X]) with hCm'
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  -- the rational change of basis `Cr = D Ĉ D⁻¹`
  set Cr : Matrix ι ι ℚ := Matrix.diagonal (fun i => (p : ℚ) ^ ν i) * Cm *
      Matrix.diagonal (fun i => (p : ℚ) ^ (-ν i)) with hCr
  have hdetCr : Cr.det = Cm.det := by
    have hprod : (∏ i, (p : ℚ) ^ ν i) * ∏ i, (p : ℚ) ^ (-ν i) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun i _ => by rw [← zpow_add₀ hp0]; simp
    rw [hCr, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
    linear_combination Cm.det * hprod
  have hCr' : Cr.map (C : ℚ →+* ℚ[X]) = Dm * Cm' * Di := by
    refine Matrix.ext fun i j => ?_
    simp only [hCr, hDm, hDi, hCm', Matrix.map_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp [map_mul]
  have hDiG : Di * G * Di = normGram (p := p) ν G := by
    refine Matrix.ext fun i j => ?_
    simp only [hDi, normGram, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [show -ν i - ν j = -ν i + -ν j by ring, zpow_add₀ hp0, C_mul]; ring
  have hconj : Cr.map (C : ℚ →+* ℚ[X]) * G * (Cr.map (C : ℚ →+* ℚ[X])).transpose =
      Dm * (Cm' * normGram (p := p) ν G * Cm'.transpose) * Dm := by
    rw [hCr', Matrix.transpose_mul, Matrix.transpose_mul, hDm, hDi, Matrix.diagonal_transpose,
      Matrix.diagonal_transpose, ← hDm, ← hDi, ← hDiG]
    simp only [Matrix.mul_assoc]
  refine (?_ : GV p G.det (2 * ∑ i, (((ν i : ℚ) + raisedθ θ R i)))).mono (le_of_eq ?_)
  · refine zc10_weight G Cr (by rw [hdetCr]; exact hdet) (by rw [hdetCr]; exact hunit)
      (fun i => (ν i : ℚ) + raisedθ θ R i) (fun i j => ?_)
    rw [hconj]
    have : (Dm * (Cm' * normGram (p := p) ν G * Cm'.transpose) * Dm) i j =
        C ((p : ℚ) ^ (ν i + ν j)) * (Cm' * normGram (p := p) ν G * Cm'.transpose) i j := by
      simp only [hDm, Matrix.mul_diagonal, Matrix.diagonal_mul]
      rw [zpow_add₀ hp0, C_mul]; ring
    rw [this]
    have h1 := GV.C_mul (VG.primePow (p := p) (ν i + ν j)) (hM i j)
    refine h1.mono (le_of_eq ?_)
    push_cast; ring
  · have : ∑ i, raisedθ θ R i = ∑ i, θ i + R.card * (1 / 2) := by
      simp only [raisedθ, Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_const,
        Finset.univ_inter, nsmul_eq_mul]
    simp only [Finset.sum_add_distrib, this]
    ring

/-- Conjugation by a `p`-integral change of basis that mixes only rows of equal `θ` keeps the base
bound `θ i + θ j`. -/
theorem conj_base (Gn : Matrix ι ι ℚ[X]) (θ : ι → ℚ) (Cm : Matrix ι ι ℚ)
    (hint : ∀ i j, VG p (Cm i j) 0) (hblk : ∀ i j, θ i ≠ θ j → Cm i j = 0)
    (hbase : ∀ i j, GV p (Gn i j) (θ i + θ j)) (i j : ι) :
    GV p ((Cm.map (C : ℚ →+* ℚ[X]) * Gn * (Cm.map (C : ℚ →+* ℚ[X])).transpose) i j)
      (θ i + θ j) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  refine GV.sum _ fun t _ => GV.sum _ fun s _ => ?_
  by_cases h1 : Cm i s = 0
  · simp [h1]; exact GV.zero _
  by_cases h2 : Cm j t = 0
  · simp [h2]; exact GV.zero _
  have hs : θ s = θ i := by
    by_contra h; exact h1 (hblk i s (Ne.symm h))
  have ht : θ t = θ j := by
    by_contra h; exact h2 (hblk j t (Ne.symm h))
  have := ((GV.C (hint i s)).mul (hbase s t)).mul (GV.C (hint j t))
  refine this.mono (le_of_eq ?_)
  rw [hs, ht]; ring

/-- **ZC26, entries.**  The retained rows `R` (all even, `θ = 0`) are orthogonal to order `1` to
every even row.  Then all entries of the conjugated matrix satisfy the raised weights. -/
theorem zc26_entries (G : Matrix ι ι ℚ[X]) (ν : ι → ℤ) (θ : ι → ℚ) (R : Finset ι)
    (hθ : ∀ i, θ i = 0 ∨ θ i = 1 / 2)
    (hbase : ∀ i j, GV p (normGram (p := p) ν G i j) (θ i + θ j))
    (hsym : ∀ i j, G i j = G j i)
    (Cm : Matrix ι ι ℚ) (hint : ∀ i j, VG p (Cm i j) 0) (hblk : ∀ i j, θ i ≠ θ j → Cm i j = 0)
    (hR : ∀ i ∈ R, θ i = 0)
    (hret : ∀ i ∈ R, ∀ j, θ j = 0 → GV p ((Cm.map (C : ℚ →+* ℚ[X]) * normGram (p := p) ν G *
        (Cm.map (C : ℚ →+* ℚ[X])).transpose) i j) 1) (i j : ι) :
    GV p ((Cm.map (C : ℚ →+* ℚ[X]) * normGram (p := p) ν G *
        (Cm.map (C : ℚ →+* ℚ[X])).transpose) i j) (raisedθ θ R i + raisedθ θ R j) := by
  classical
  set Gn := normGram (p := p) ν G with hGn
  set M := Cm.map (C : ℚ →+* ℚ[X]) * Gn * (Cm.map (C : ℚ →+* ℚ[X])).transpose with hM
  have hbase' := conj_base Gn θ Cm hint hblk hbase
  have hGsym : ∀ i j, Gn i j = Gn j i := fun i j => by
    simp only [hGn, normGram, Matrix.of_apply]; rw [hsym i j]; ring_nf
  have hMsym : ∀ i j, M i j = M j i := fun i j => by
    have : M.transpose = M := by
      rw [hM, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
      have : Gn.transpose = Gn := Matrix.ext fun a b => (hGsym b a)
      rw [this, Matrix.mul_assoc]
    have h2 := congrFun (congrFun this j) i
    simpa using h2
  -- strict vanishing against any row `j` (even or odd)
  have hret' : ∀ i ∈ R, ∀ j, GV p (M i j) 1 := by
    intro i hi j
    rcases hθ j with h0 | h0
    · exact hret i hi j h0
    · have := hbase' i j
      rw [hR i hi, h0, zero_add] at this
      exact GV_one_of_half this
  have h12 : ∀ j, raisedθ θ R j ≤ θ j + 1 / 2 := fun j => by
    unfold raisedθ; split_ifs <;> linarith
  by_cases hi : i ∈ R
  · have hr := hret' i hi j
    have hθi : raisedθ θ R i = 1 / 2 := by
      unfold raisedθ; rw [if_pos hi, hR i hi]; ring
    have : raisedθ θ R j ≤ 1 / 2 + 1 / 2 := by
      have := h12 j; rcases hθ j with h | h <;> linarith
    refine hr.mono ?_
    rw [hθi]
    by_cases hj : j ∈ R
    · have : raisedθ θ R j = 1 / 2 := by unfold raisedθ; rw [if_pos hj, hR j hj]; ring
      linarith
    · have : raisedθ θ R j = θ j := by unfold raisedθ; rw [if_neg hj]; ring
      rcases hθ j with h | h <;> linarith
  · by_cases hj : j ∈ R
    · rw [hMsym]
      have hr := hret' j hj i
      have hθj : raisedθ θ R j = 1 / 2 := by
        unfold raisedθ; rw [if_pos hj, hR j hj]; ring
      have hθi : raisedθ θ R i = θ i := by unfold raisedθ; rw [if_neg hi]; ring
      refine hr.mono ?_
      rw [hθj, hθi]
      rcases hθ i with h | h <;> linarith
    · have hθi : raisedθ θ R i = θ i := by unfold raisedθ; rw [if_neg hi]; ring
      have hθj : raisedθ θ R j = θ j := by unfold raisedθ; rw [if_neg hj]; ring
      rw [hθi, hθj]; exact hbase' i j

/-- **ZC26.**  If the normalised Gram matrix has the base weights `θ` (`0` on even rows, `1/2` on odd
rows), a `p`-unit change of basis `Cm` mixes only rows of equal `θ`, and the retained even rows `R`
are orthogonal to order `1` to every even row, then
`v_p^G (det G) ≥ 2 ∑ (ν + θ) + |R|`: one unit per retained direction. -/
theorem zc26_weight_raise (G : Matrix ι ι ℚ[X]) (ν : ι → ℤ) (θ : ι → ℚ) (R : Finset ι)
    (hθ : ∀ i, θ i = 0 ∨ θ i = 1 / 2)
    (hbase : ∀ i j, GV p (normGram (p := p) ν G i j) (θ i + θ j))
    (hsym : ∀ i j, G i j = G j i)
    (Cm : Matrix ι ι ℚ) (hdet : Cm.det ≠ 0) (hunit : padicValRat p Cm.det = 0)
    (hint : ∀ i j, VG p (Cm i j) 0) (hblk : ∀ i j, θ i ≠ θ j → Cm i j = 0)
    (hR : ∀ i ∈ R, θ i = 0)
    (hret : ∀ i ∈ R, ∀ j, θ j = 0 → GV p ((Cm.map (C : ℚ →+* ℚ[X]) * normGram (p := p) ν G *
        (Cm.map (C : ℚ →+* ℚ[X])).transpose) i j) 1) :
    GV p G.det (2 * ∑ i, ((ν i : ℚ) + θ i) + R.card) :=
  zc26_core G ν θ R Cm hdet hunit
    (fun i j => zc26_entries G ν θ R hθ hbase hsym Cm hint hblk hR hret i j)

end core
end Apery
