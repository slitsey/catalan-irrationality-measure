module

public import CatalanCore.NT.Saalschutz
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Prime.Factorial

@[expose] public section

/-!
# The Hankel determinant of `λ(D_a(x)³ x^{i+j})` (Lemma W, algebraic proof)

`λ(x^e) = e B_{e−1}` (Mathlib's `bernoulli`, `B₁ = −1/2`), `D_a(x) = ∏_{i<a}(x − i)`, `a = 2c + 1`.

**Theorem** (`wilson_hankel`).
`det[λ(D_a³ x^{i+j})]_{i,j<K} = (−1)^{cK + ⌊K/2⌋} ∏_{n<⌈K/2⌉} h⁺_n ∏_{n<⌊K/2⌋} h⁻_n`
with
`h⁺_n = n! (c+n)!³ (2c+1+n)!³ (n+3c+1)! / ((2n+3c+1)! (2n+3c+2)!)`,
`h⁻_n = n! (c+1+n)!³ (2c+1+n)!³ (n+3c+2)! / ((2n+3c+2)! (2n+3c+3)!)`.

The proof is finite algebra (note `N9-LAI-WILSON-ALG-2026-11-20.md`): the functional `λ` satisfies
`λ(f(x+1) − f(x)) = f''(0)` and `λ(g(−x)) = −λ(g) − g''(0)`; these give an even centred functional `N`,
a Pearson equation, the discrete Beta evaluation `N[f_j e_k]`, the total mass, and (with
Pfaff–Saalschütz, `CatalanCore.NT.Saalschutz`) the orthogonal polynomials and their norms.
-/

open Polynomial Finset

namespace CatalanCore.Lai.Wilson

open CatalanCore.NT

/-! ## Part A. Pochhammer symbols -/

theorem poch_eq_prod (x : ℚ) (n : ℕ) : poch x n = ∏ i ∈ range n, (x + i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [poch_succ, prod_range_succ, ih]

theorem poch_add (x : ℚ) (m n : ℕ) : poch x (m + n) = poch x m * poch (x + m) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, poch_succ, ih, poch_succ]
    push_cast
    ring

theorem poch_ne_zero {x : ℚ} (hx : 0 < x) (k : ℕ) : poch x k ≠ 0 := (poch_pos hx k).ne'

theorem poch_nat (x : ℚ) (a : ℕ) (hx : x = a + 1) (m : ℕ) :
    poch x m = ((a + m).factorial : ℚ) / (a.factorial : ℚ) := by
  have ha : (a.factorial : ℚ) ≠ 0 := by positivity
  induction m with
  | zero => simp [ha]
  | succ m ih =>
    rw [poch_succ, ih, hx, ← add_assoc, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem poch_one_eq (n : ℕ) : poch 1 n = (n.factorial : ℚ) := by
  have := poch_nat 1 0 (by norm_num) n
  simpa using this

theorem poch_reflect (x : ℚ) (n : ℕ) : poch (1 - x - n) n = (-1) ^ n * poch x n := by
  rw [poch_eq_prod, poch_eq_prod, ← prod_range_reflect (fun i : ℕ => (1 - x - (n : ℚ) + (i : ℚ))) n]
  have : ∀ i ∈ range n, (1 - x - (n : ℚ) + ((n - 1 - i : ℕ) : ℚ)) = -(x + i) := by
    intro i hi
    have hi' : i < n := mem_range.1 hi
    have h1 : ((n - 1 - i : ℕ) : ℚ) = (n : ℚ) - 1 - i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      simp
    rw [h1]; ring
  rw [prod_congr rfl this, prod_neg]
  simp

theorem poch_neg_self (n : ℕ) : poch (-(n : ℚ)) n = (-1) ^ n * (n.factorial : ℚ) := by
  have := poch_reflect 1 n
  rw [poch_one_eq] at this
  have h : (1 : ℚ) - 1 - n = -(n : ℚ) := by ring
  rwa [h] at this

theorem poch_neg_zero {j n : ℕ} (h : j < n) : poch (-(j : ℚ)) n = 0 := by
  rw [poch_eq_prod]
  exact prod_eq_zero (mem_range.2 h) (by ring)

/-! ## Part B. The generic Wilson sum, from Pfaff–Saalschütz -/

/-- Coefficients of the Wilson polynomial in the basis `e_k`. -/
def qG (σ τ : ℚ) (n k : ℕ) : ℚ :=
  poch (-(n : ℚ)) k * poch (n + σ + τ - 1) k / ((k.factorial : ℚ) * poch σ k * poch τ k ^ 2)

/-- The discrete Beta pairing, normalised. -/
def bil (σ τ : ℚ) (j k : ℕ) : ℚ :=
  poch σ (j + k) * poch σ j ^ 2 * poch τ k ^ 2 / poch (σ + τ) (j + k)

theorem qG_bil {σ τ : ℚ} (hσ : 0 < σ) (hτ : 0 < τ) (n j k : ℕ) :
    qG σ τ n k * bil σ τ j k =
      poch σ j ^ 3 / poch (σ + τ) j * saalTerm (n + σ + τ - 1) (σ + j) σ n k := by
  unfold qG bil saalTerm
  have e1 : 1 + (n + σ + τ - 1) + (σ + j) - σ - n = σ + τ + j := by ring
  rw [e1, poch_add σ j k, poch_add (σ + τ) j k]
  have e2 : (σ + τ) + (j : ℚ) = σ + τ + j := rfl
  have p1 := poch_pos hσ k
  have p2 := poch_pos hτ k
  have p3 : 0 < poch (σ + τ) j := poch_pos (by linarith) j
  have p4 : 0 < poch (σ + τ + j) k := poch_pos (by positivity) k
  have p5 : 0 < poch (σ + j) k := poch_pos (by positivity) k
  have p6 : 0 < poch σ j := poch_pos hσ j
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem W_eq {σ τ : ℚ} (hσ : 0 < σ) (hτ : 0 < τ) (h1 : 1 < σ + τ) (n j : ℕ) :
    ∑ k ∈ range (n + 1), qG σ τ n k * bil σ τ j k =
      poch σ j ^ 3 / poch (σ + τ) j * saalRhs (n + σ + τ - 1) (σ + j) σ n := by
  simp_rw [qG_bil hσ hτ, ← mul_sum]
  congr 1
  exact saalschutz (n + σ + τ - 1) (σ + j) σ n hσ (by
    have : (0 : ℚ) ≤ j := Nat.cast_nonneg j
    linarith)

theorem W_vanish {σ τ : ℚ} (hσ : 0 < σ) (hτ : 0 < τ) (h1 : 1 < σ + τ) {n j : ℕ} (hj : j < n) :
    ∑ k ∈ range (n + 1), qG σ τ n k * bil σ τ j k = 0 := by
  rw [W_eq hσ hτ h1]
  unfold saalRhs
  have : σ - (σ + j) = -(j : ℚ) := by ring
  rw [this, poch_neg_zero hj]
  simp

/-- The norm of the Wilson polynomial, generic form. -/
def wNorm (σ τ : ℚ) (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * poch σ n ^ 3 * poch τ n ^ 3 /
    (poch (σ + τ) n * poch (n + σ + τ - 1) n * poch (n + σ + τ) n)

theorem qG_diag_ne {σ τ : ℚ} (hσ : 0 < σ) (hτ : 0 < τ) (h1 : 1 < σ + τ) (n : ℕ) :
    qG σ τ n n ≠ 0 := by
  unfold qG
  rw [poch_neg_self]
  have : 0 < poch (n + σ + τ - 1) n := poch_pos (by
    have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    linarith) n
  have := poch_pos hσ n
  have := poch_pos hτ n
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have : ((-1 : ℚ) ^ n) ≠ 0 := by simp
  positivity

theorem W_diag {σ τ : ℚ} (hσ : 0 < σ) (hτ : 0 < τ) (h1 : 1 < σ + τ) (n : ℕ) :
    ∑ k ∈ range (n + 1), qG σ τ n k * bil σ τ n k = qG σ τ n n * wNorm σ τ n := by
  rw [W_eq hσ hτ h1]
  unfold saalRhs wNorm qG
  have e1 : σ - (n + σ + τ - 1) = 1 - τ - n := by ring
  have e2 : σ - (σ + n) = -(n : ℚ) := by ring
  have e3 : σ - (n + σ + τ - 1) - (σ + n) = 1 - (n + σ + τ) - n := by ring
  rw [e3, e1, e2, poch_reflect, poch_reflect, poch_neg_self]
  have hn0 : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have p1 := poch_pos hσ n
  have p2 := poch_pos hτ n
  have p3 : 0 < poch (σ + τ) n := poch_pos (by linarith) n
  have p4 : 0 < poch (n + σ + τ) n := poch_pos (by linarith) n
  have p5 : 0 < poch (n + σ + τ - 1) n := poch_pos (by linarith) n
  have hf : (n.factorial : ℚ) ≠ 0 := by positivity
  rcases neg_one_pow_eq_or ℚ n with h | h <;> rw [h] <;> field_simp

/-! ## Part C. The functional `λ` and its axioms -/

/-- The three properties of `λ` that the algebraic proof uses:
`λ(f(x+1) − f(x)) = f''(0)`, `λ(g(−x)) = −λ(g) − g''(0)`, `λ(x³) = 1/2`. -/
structure LamAx (lam : ℚ[X] →ₗ[ℚ] ℚ) : Prop where
  shift : ∀ f : ℚ[X], lam (f.comp (X + 1) - f) = 2 * f.coeff 2
  refl : ∀ g : ℚ[X], lam (g.comp (-X)) = -lam g - 2 * g.coeff 2
  cube : lam (X ^ 3) = 1 / 2

variable {lam : ℚ[X] →ₗ[ℚ] ℚ}

/-- Second derivative at the integer `j`. -/
noncomputable def dd (g : ℚ[X]) (j : ℕ) : ℚ := 2 * (g.comp (X + C (j : ℚ))).coeff 2

theorem lam_succ_shift (h : LamAx lam) (f : ℚ[X]) :
    lam (f.comp (X + 1)) = lam f + 2 * f.coeff 2 := by
  have := h.shift f
  rw [map_sub] at this
  linarith

theorem lam_shift (h : LamAx lam) (g : ℚ[X]) (m : ℕ) :
    lam (g.comp (X + C (m : ℚ))) = lam g + ∑ j ∈ range m, dd g j := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : g.comp (X + C ((m + 1 : ℕ) : ℚ)) = (g.comp (X + C (m : ℚ))).comp (X + 1) := by
      rw [comp_assoc]
      congr 1
      simp only [add_comp, X_comp, C_comp, Nat.cast_add, Nat.cast_one, C_add, C_1]
      ring
    rw [h1, lam_succ_shift h, ih, sum_range_succ]
    unfold dd
    ring

theorem lam_reflect (h : LamAx lam) (g : ℚ[X]) (N : ℕ) :
    lam (g.comp (C (N : ℚ) - X)) = -lam g - ∑ j ∈ range (N + 1), dd g j := by
  have h1 : g.comp (C (N : ℚ) - X) = (g.comp (X + C (N : ℚ))).comp (-X) := by
    rw [comp_assoc]
    congr 1
    simp only [add_comp, X_comp, C_comp]
    ring
  rw [h1, h.refl, lam_shift h, sum_range_succ]
  unfold dd
  ring

/-! ## Part D. The centred functional `N` -/

/-- `D_a(x) = ∏_{i<a} (x − i)`. -/
noncomputable def Dp (a : ℕ) : ℚ[X] := ∏ i ∈ range a, (X - C (i : ℚ))

theorem Dp_succ (a : ℕ) : Dp (a + 1) = Dp a * (X - C (a : ℚ)) := prod_range_succ _ _

theorem Dp_comp_succ (a : ℕ) : (Dp (a + 1)).comp (X + 1) = (X + 1) * Dp a := by
  unfold Dp
  rw [prod_range_succ', Polynomial.mul_comp, Polynomial.prod_comp]
  have : ∀ i ∈ range a, (X - C ((i + 1 : ℕ) : ℚ)).comp (X + 1) = X - C (i : ℚ) := by
    intro i _
    simp only [sub_comp, X_comp, C_comp]
    simp only [Nat.cast_add, Nat.cast_one, C_add, C_1]
    ring
  rw [prod_congr rfl this]
  simp only [X_comp, Nat.cast_zero, map_zero, sub_zero]
  ring

theorem Dp_comp_refl (n : ℕ) :
    (Dp (n + 1)).comp (C (n : ℚ) - X) = (-1) ^ (n + 1) * Dp (n + 1) := by
  unfold Dp
  rw [Polynomial.prod_comp]
  have h1 : ∀ i ∈ range (n + 1), (X - C (i : ℚ)).comp (C (n : ℚ) - X) =
      -1 * (X - C ((n + 1 - 1 - i : ℕ) : ℚ)) := by
    intro i hi
    have hi' : i < n + 1 := mem_range.1 hi
    have : (((n + 1 - 1 - i : ℕ)) : ℚ) = (n : ℚ) - i := by
      rw [Nat.add_sub_cancel, Nat.cast_sub (by omega)]
    rw [this]
    simp only [sub_comp, X_comp, C_comp, map_sub]
    ring
  rw [prod_congr rfl h1, prod_mul_distrib, prod_const, card_range]
  congr 1
  rw [prod_range_reflect (fun i : ℕ => (X - C (i : ℚ))) (n + 1)]

theorem Dp_dvd {a j : ℕ} (hj : j < a) : (X - C (j : ℚ)) ∣ Dp a :=
  dvd_prod_of_mem _ (mem_range.2 hj)

theorem X_dvd_Dp_comp {a j : ℕ} (hj : j < a) : X ∣ (Dp a).comp (X + C (j : ℚ)) := by
  obtain ⟨q, hq⟩ := Dp_dvd hj
  refine ⟨q.comp (X + C (j : ℚ)), ?_⟩
  rw [hq, Polynomial.mul_comp]
  simp only [sub_comp, X_comp, C_comp]
  ring

theorem coeff_two_of_cube {P : ℚ[X]} (h : X ^ 3 ∣ P) : P.coeff 2 = 0 := by
  obtain ⟨q, rfl⟩ := h
  rw [coeff_X_pow_mul']
  simp

theorem dd_zero_of_dvd {a : ℕ} {j : ℕ} (hj : j < a) (g : ℚ[X]) :
    dd (Dp a ^ 3 * g) j = 0 := by
  unfold dd
  have h1 : X ^ 3 ∣ ((Dp a ^ 3 * g).comp (X + C (j : ℚ))) := by
    rw [Polynomial.mul_comp, Polynomial.pow_comp]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (X_dvd_Dp_comp hj) 3) _
  rw [coeff_two_of_cube h1]
  simp

/-- Linear map `g ↦ g.comp q`. -/
noncomputable def compL (q : ℚ[X]) : ℚ[X] →ₗ[ℚ] ℚ[X] := (aeval q).toLinearMap

theorem compL_apply (q g : ℚ[X]) : compL q g = g.comp q := rfl

/-- The centred functional `N_c[g] = (−1)^c λ(D_{2c+1}³ g(x − c))`. -/
noncomputable def Nf (lam : ℚ[X] →ₗ[ℚ] ℚ) (c : ℕ) : ℚ[X] →ₗ[ℚ] ℚ :=
  ((-1 : ℚ) ^ c) • (lam ∘ₗ (LinearMap.mulLeft ℚ (Dp (2 * c + 1) ^ 3)) ∘ₗ compL (X - C (c : ℚ)))

theorem Nf_apply (lam : ℚ[X] →ₗ[ℚ] ℚ) (c : ℕ) (g : ℚ[X]) :
    Nf lam c g = (-1) ^ c * lam (Dp (2 * c + 1) ^ 3 * g.comp (X - C (c : ℚ))) := by
  simp [Nf, compL_apply]

/-- **Lemma E** (evenness). -/
theorem Nf_even (h : LamAx lam) (c : ℕ) (g : ℚ[X]) : Nf lam c (g.comp (-X)) = Nf lam c g := by
  rw [Nf_apply, Nf_apply]
  congr 1
  set G : ℚ[X] := Dp (2 * c + 1) ^ 3 * g.comp (X - C (c : ℚ)) with hGdef
  have hD : (Dp (2 * c + 1)).comp (C ((2 * c : ℕ) : ℚ) - X) = -Dp (2 * c + 1) := by
    rw [Dp_comp_refl (2 * c)]
    have : (-1 : ℚ[X]) ^ (2 * c + 1) = -1 := by
      rw [pow_succ, pow_mul]; simp
    rw [this]; ring
  have hG : G.comp (C ((2 * c : ℕ) : ℚ) - X) =
      -(Dp (2 * c + 1) ^ 3 * (g.comp (-X)).comp (X - C (c : ℚ))) := by
    rw [hGdef, Polynomial.mul_comp, Polynomial.pow_comp, hD, comp_assoc, comp_assoc]
    have e1 : (X - C (c : ℚ)).comp (C ((2 * c : ℕ) : ℚ) - X) = -(X - C (c : ℚ)) := by
      simp only [sub_comp, X_comp, C_comp, Nat.cast_mul, Nat.cast_ofNat, map_mul, map_ofNat]
      ring
    have e2 : (-X).comp (X - C (c : ℚ)) = -(X - C (c : ℚ)) := by simp
    rw [e1, e2]
    ring
  have hr := lam_reflect h G (2 * c)
  have hz : ∑ j ∈ range (2 * c + 1), dd G j = 0 :=
    sum_eq_zero fun j hj => dd_zero_of_dvd (mem_range.1 hj) _
  rw [hz, hG, map_neg] at hr
  linarith

theorem Nf_parity_odd (h : LamAx lam) (c : ℕ) (P : ℚ[X]) (hP : P.comp (-X) = -P) :
    Nf lam c P = 0 := by
  have := Nf_even h c P
  rw [hP, map_neg] at this
  linarith

/-- **Lemma P** (Pearson equation), with `s = c + 1`. -/
theorem Nf_pearson (h : LamAx lam) (c : ℕ) (g : ℚ[X]) :
    Nf lam c ((X + C ((c : ℚ) + 1)) ^ 3 * g.comp (X + 1)) =
      Nf lam c ((X - C ((c : ℚ) + 1)) ^ 3 * g) := by
  rw [Nf_apply, Nf_apply]
  set ψ : ℚ[X] := g.comp (X - C (c : ℚ)) with hψ
  have e1 : (X + C ((c : ℚ) + 1)).comp (X - C (c : ℚ)) = X + 1 := by
    simp only [add_comp, X_comp, C_comp, sub_comp]
    rw [C_add, C_1]; ring
  have e2 : (X + 1).comp (X - C (c : ℚ)) = (X - C (c : ℚ)).comp (X + 1) := by
    simp only [add_comp, sub_comp, X_comp, C_comp, one_comp]; ring
  have e3 : (X - C ((c : ℚ) + 1)).comp (X - C (c : ℚ)) = X - C (((2 * c + 1 : ℕ)) : ℚ) := by
    simp only [sub_comp, X_comp, C_comp]
    push_cast
    simp only [C_add, C_mul, C_1, map_ofNat]
    ring
  have hA : ((X + C ((c : ℚ) + 1)) ^ 3 * g.comp (X + 1)).comp (X - C (c : ℚ)) =
      (X + 1) ^ 3 * ψ.comp (X + 1) := by
    rw [hψ, Polynomial.mul_comp, Polynomial.pow_comp, comp_assoc, comp_assoc, e1, e2]
  have hB : ((X - C ((c : ℚ) + 1)) ^ 3 * g).comp (X - C (c : ℚ)) =
      (X - C (((2 * c + 1 : ℕ)) : ℚ)) ^ 3 * ψ := by
    rw [hψ, Polynomial.mul_comp, Polynomial.pow_comp, e3]
  set f : ℚ[X] := Dp (2 * c + 1 + 1) ^ 3 * ψ with hf
  have hfdiv : X ^ 3 ∣ f := by
    have h0 : X ∣ Dp (2 * c + 1 + 1) := by
      have := Dp_dvd (a := 2 * c + 1 + 1) (j := 0) (by omega)
      simpa using this
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd h0 3) _
  have hfc : f.comp (X + 1) =
      ((X + 1) * Dp (2 * c + 1)) ^ 3 * ψ.comp (X + 1) := by
    rw [hf, Polynomial.mul_comp, Polynomial.pow_comp, Dp_comp_succ]
  have hf2 : f = (Dp (2 * c + 1) * (X - C (((2 * c + 1 : ℕ)) : ℚ))) ^ 3 * ψ := by
    rw [hf, Dp_succ]
  have hdiff : f.comp (X + 1) - f =
      Dp (2 * c + 1) ^ 3 * ((X + 1) ^ 3 * ψ.comp (X + 1)) -
        Dp (2 * c + 1) ^ 3 * ((X - C (((2 * c + 1 : ℕ)) : ℚ)) ^ 3 * ψ) := by
    rw [hfc]
    conv_lhs => rw [hf2]
    ring
  have hz := h.shift f
  rw [coeff_two_of_cube hfdiv, hdiff, map_sub] at hz
  rw [hA, hB]
  have : lam (Dp (2 * c + 1) ^ 3 * ((X + 1) ^ 3 * ψ.comp (X + 1))) =
      lam (Dp (2 * c + 1) ^ 3 * ((X - C (((2 * c + 1 : ℕ)) : ℚ)) ^ 3 * ψ)) := by
    linarith
  rw [this]

/-! ## Part E. The families `(z+a)_n`, `(a−z)_n`, `e_n^{(a)}(z) = ∏ ((a+i)² − z²)` -/

noncomputable def rp (a : ℚ) (n : ℕ) : ℚ[X] := ∏ i ∈ range n, (X + C (a + i))
noncomputable def rn (a : ℚ) (n : ℕ) : ℚ[X] := ∏ i ∈ range n, (C (a + i) - X)
noncomputable def ee (a : ℚ) (n : ℕ) : ℚ[X] := ∏ i ∈ range n, (C ((a + i) ^ 2) - X ^ 2)

@[simp] theorem rp_zero (a : ℚ) : rp a 0 = 1 := by simp [rp]
@[simp] theorem rn_zero (a : ℚ) : rn a 0 = 1 := by simp [rn]
@[simp] theorem ee_zero (a : ℚ) : ee a 0 = 1 := by simp [ee]

theorem rp_succ (a : ℚ) (n : ℕ) : rp a (n + 1) = rp a n * (X + C (a + n)) := prod_range_succ _ _
theorem ee_succ (a : ℚ) (n : ℕ) :
    ee a (n + 1) = ee a n * (C ((a + n) ^ 2) - X ^ 2) := prod_range_succ _ _

theorem rp_succ' (a : ℚ) (n : ℕ) : rp a (n + 1) = (X + C a) * rp (a + 1) n := by
  unfold rp
  rw [prod_range_succ', mul_comm]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  congr 2
  ring

theorem ee_succ' (a : ℚ) (n : ℕ) :
    ee a (n + 1) = (C (a ^ 2) - X ^ 2) * ee (a + 1) n := by
  unfold ee
  rw [prod_range_succ', mul_comm]
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  congr 3
  ring

theorem rp_X (a : ℚ) (n : ℕ) : (X + C a) * rp (a + 1) n = rp a n * (X + C (a + n)) := by
  rw [← rp_succ', rp_succ]

theorem rp_mul_rn (a : ℚ) (n : ℕ) : rp a n * rn a n = ee a n := by
  unfold rp rn ee
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [C_pow]
  ring

theorem rp_comp_one (a : ℚ) (n : ℕ) : (rp a n).comp (X + 1) = rp (a + 1) n := by
  unfold rp
  rw [Polynomial.prod_comp]
  refine prod_congr rfl fun i _ => ?_
  simp only [add_comp, X_comp, C_comp, one_comp]
  rw [show a + 1 + (i : ℚ) = (a + i) + 1 by ring]
  simp only [C_add, C_1]
  ring

theorem rn_comp_one (a : ℚ) (n : ℕ) : (rn (a + 1) n).comp (X + 1) = rn a n := by
  unfold rn
  rw [Polynomial.prod_comp]
  refine prod_congr rfl fun i _ => ?_
  simp only [sub_comp, add_comp, X_comp, C_comp, one_comp]
  rw [show a + 1 + (i : ℚ) = (a + i) + 1 by ring]
  simp only [C_add, C_1]
  ring

theorem rp_comp_neg (a : ℚ) (n : ℕ) : (rp a n).comp (-X) = rn a n := by
  unfold rp rn
  rw [Polynomial.prod_comp]
  refine prod_congr rfl fun i _ => ?_
  simp only [add_comp, X_comp, C_comp, neg_comp]
  ring

theorem rn_comp_neg (a : ℚ) (n : ℕ) : (rn a n).comp (-X) = rp a n := by
  unfold rp rn
  rw [Polynomial.prod_comp]
  refine prod_congr rfl fun i _ => ?_
  simp only [sub_comp, X_comp, C_comp, neg_comp]
  ring

theorem ee_comp_neg (a : ℚ) (n : ℕ) : (ee a n).comp (-X) = ee a n := by
  unfold ee
  rw [Polynomial.prod_comp]
  refine prod_congr rfl fun i _ => ?_
  simp only [sub_comp, X_comp, C_comp, neg_comp, pow_comp]
  ring

theorem Nf_Cmul (lam : ℚ[X] →ₗ[ℚ] ℚ) (c : ℕ) (a : ℚ) (p : ℚ[X]) :
    Nf lam c (C a * p) = a * Nf lam c p := by
  rw [C_mul', map_smul, smul_eq_mul]

/-- The key vanishing relation `(★)`. -/
theorem Nf_star (h : LamAx lam) (c : ℕ) (s : ℚ) (hs : s = (c : ℚ) + 1) (j k : ℕ) :
    Nf lam c (ee 0 j * ee s k *
      (C (3 * s + j + k) * X ^ 2 + C (2 * s * j * (s + k) + s ^ 2 * (s + j + k)))) = 0 := by
  set g : ℚ[X] := rp 0 j * rn (0 + 1) j * rp s k * rn (s + 1) k with hg
  set g1 : ℚ[X] := rp (0 + 1) j * rn 0 j * rp (s + 1) k * rn s k with hg1
  have hgc : g.comp (X + 1) = g1 := by
    rw [hg, hg1]
    simp only [Polynomial.mul_comp, rp_comp_one, rn_comp_one]
  set T : ℚ[X] := (X + C s) ^ 3 * g1 with hT
  have hT0 : Nf lam c T = 0 := by
    have hp := Nf_pearson h c g
    rw [← hs, hgc] at hp
    have hneg : (X - C s) ^ 3 * g = -(T.comp (-X)) := by
      rw [hT, Polynomial.mul_comp, Polynomial.pow_comp, hg1]
      simp only [Polynomial.mul_comp, rp_comp_neg, rn_comp_neg, add_comp, X_comp, C_comp,
        neg_comp, hg]
      ring
    rw [hneg] at hp
    have h2 : Nf lam c T = Nf lam c (-(T.comp (-X))) := hp
    rw [map_neg, Nf_even h] at h2
    linarith
  set F : ℚ[X] := ee 0 j * ee s k with hF
  set P : ℚ[X] := (X + C s) ^ 2 * (X + C (s + k)) * (X + C (j : ℚ)) with hP
  set Q : ℚ[X] := C (3 * s + j + k) * X ^ 2 +
    C (2 * s * j * (s + k) + s ^ 2 * (s + j + k)) with hQ
  have hA1 : X * rp (0 + 1) j = rp 0 j * (X + C (j : ℚ)) := by
    have := rp_X 0 j
    simpa using this
  have hA2 : (X + C s) * rp (s + 1) k = rp s k * (X + C (s + k)) := rp_X s k
  have hXT : X * T = P * F := by
    rw [hT, hg1, hP, hF, ← rp_mul_rn 0 j, ← rp_mul_rn s k]
    linear_combination ((X + C s) ^ 2 * rn 0 j * rn s k * ((X + C s) * rp (s + 1) k)) * hA1 +
      ((X + C s) ^ 2 * rn 0 j * rn s k * (rp 0 j * (X + C (j : ℚ)))) * hA2
  have hFe : F.comp (-X) = F := by
    rw [hF, Polynomial.mul_comp, ee_comp_neg, ee_comp_neg]
  have hXT' : (-X) * T.comp (-X) = P.comp (-X) * F := by
    have := congrArg (fun p : ℚ[X] => p.comp (-X)) hXT
    simp only [Polynomial.mul_comp, X_comp] at this
    rw [hFe] at this
    exact this
  have hPQ : P - P.comp (-X) = X * (2 * Q) := by
    rw [hP, hQ]
    simp only [Polynomial.mul_comp, pow_comp, add_comp, X_comp, C_comp]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  have hsum : T + T.comp (-X) = 2 * (F * Q) := by
    apply mul_left_cancel₀ (X_ne_zero : (X : ℚ[X]) ≠ 0)
    calc X * (T + T.comp (-X)) = X * T - (-X) * T.comp (-X) := by ring
      _ = P * F - P.comp (-X) * F := by rw [hXT, hXT']
      _ = (P - P.comp (-X)) * F := by ring
      _ = X * (2 * (F * Q)) := by rw [hPQ]; ring
  have hN := congrArg (Nf lam c) hsum
  rw [map_add, Nf_even h, hT0, two_mul, map_add] at hN
  linarith

/-- Recursion in `k` for `N[f_j e_k]` (Lemma B, step 3). -/
theorem Nf_ee_step_k (h : LamAx lam) (c : ℕ) (s : ℚ) (hs : s = (c : ℚ) + 1) (j k : ℕ) :
    (3 * s + j + k) * Nf lam c (ee 0 j * ee s (k + 1)) =
      (s + j + k) * (2 * s + k) ^ 2 * Nf lam c (ee 0 j * ee s k) := by
  have h0 := Nf_star h c s hs j k
  have e : ee 0 j * ee s k * (C (3 * s + j + k) * X ^ 2 +
      C (2 * s * j * (s + k) + s ^ 2 * (s + j + k))) =
      C (3 * s + j + k) * (C ((s + k) ^ 2) * (ee 0 j * ee s k) - ee 0 j * ee s (k + 1)) +
        C (2 * s * j * (s + k) + s ^ 2 * (s + j + k)) * (ee 0 j * ee s k) := by
    rw [ee_succ]; ring
  rw [e, map_add, Nf_Cmul, Nf_Cmul, map_sub, Nf_Cmul] at h0
  linear_combination (-1 : ℚ) * h0

/-- Recursion in `j` at `k = 0` (Lemma B, step 3). -/
theorem Nf_ee_step_j (h : LamAx lam) (c : ℕ) (s : ℚ) (hs : s = (c : ℚ) + 1) (j : ℕ) :
    (3 * s + j) * Nf lam c (ee 0 (j + 1)) = (s + j) ^ 3 * Nf lam c (ee 0 j) := by
  have h0 := Nf_star h c s hs j 0
  have e : ee 0 j * ee s 0 * (C (3 * s + j + ((0 : ℕ) : ℚ)) * X ^ 2 +
      C (2 * s * j * (s + ((0 : ℕ) : ℚ)) + s ^ 2 * (s + j + ((0 : ℕ) : ℚ)))) =
      C (3 * s + j + ((0 : ℕ) : ℚ)) * (C (((0 : ℚ) + j) ^ 2) * ee 0 j - ee 0 (j + 1)) +
        C (2 * s * j * (s + ((0 : ℕ) : ℚ)) + s ^ 2 * (s + j + ((0 : ℕ) : ℚ))) * ee 0 j := by
    rw [ee_zero, ee_succ]; ring
  rw [e, map_add, Nf_Cmul, Nf_Cmul, map_sub, Nf_Cmul] at h0
  linear_combination (-1 : ℚ) * h0

theorem Nf_ee_zero (h : LamAx lam) (c : ℕ) (s : ℚ) (hs : s = (c : ℚ) + 1) (j : ℕ) :
    Nf lam c (ee 0 j) = Nf lam c 1 * (poch s j ^ 3 / poch (3 * s) j) := by
  have hs0 : 0 < s := by rw [hs]; positivity
  induction j with
  | zero => simp
  | succ j ih =>
    have hst := Nf_ee_step_j h c s hs j
    have h3 : (3 * s + j) ≠ 0 := by positivity
    have hp : poch (3 * s) j ≠ 0 := poch_ne_zero (by positivity) j
    have : Nf lam c (ee 0 (j + 1)) = (s + j) ^ 3 / (3 * s + j) * Nf lam c (ee 0 j) := by
      rw [div_mul_eq_mul_div, eq_div_iff h3]
      linarith
    rw [this, ih, poch_succ, poch_succ]
    field_simp

/-- **Lemma B** (discrete Beta evaluation). -/
theorem Nf_ee_ee (h : LamAx lam) (c : ℕ) (s : ℚ) (hs : s = (c : ℚ) + 1) (j k : ℕ) :
    Nf lam c (ee 0 j * ee s k) = Nf lam c 1 *
      (poch s (j + k) * poch s j ^ 2 * poch (2 * s) k ^ 2 / poch (3 * s) (j + k)) := by
  have hs0 : 0 < s := by rw [hs]; positivity
  induction k with
  | zero =>
    rw [ee_zero, mul_one, Nf_ee_zero h c s hs]
    simp only [add_zero, poch_zero, one_pow, mul_one]
    ring
  | succ k ih =>
    have hst := Nf_ee_step_k h c s hs j k
    have h3 : (3 * s + j + k) ≠ 0 := by positivity
    have hp : poch (3 * s) (j + k) ≠ 0 := poch_ne_zero (by positivity) _
    have : Nf lam c (ee 0 j * ee s (k + 1)) =
        (s + j + k) * (2 * s + k) ^ 2 / (3 * s + j + k) * Nf lam c (ee 0 j * ee s k) := by
      rw [div_mul_eq_mul_div, eq_div_iff h3]
      linarith
    rw [this, ih, ← add_assoc, poch_succ, poch_succ, poch_succ]
    push_cast
    field_simp
    ring

/-- **Lemma M, step 1**: `N_{c+1}[g] = N_c[(s² − z²)³ g]` with `s = c + 1`. -/
theorem Nf_succ (h : LamAx lam) (c : ℕ) (g : ℚ[X]) :
    Nf lam (c + 1) g = Nf lam c ((C (((c : ℚ) + 1) ^ 2) - X ^ 2) ^ 3 * g) := by
  rw [Nf_apply, Nf_apply]
  have hD : Dp (2 * (c + 1) + 1) = Dp (2 * c + 1 + 1 + 1) := by
    rw [show 2 * (c + 1) + 1 = 2 * c + 1 + 1 + 1 by ring]
  set G : ℚ[X] := Dp (2 * (c + 1) + 1) ^ 3 * g.comp (X - C (((c + 1 : ℕ)) : ℚ)) with hG
  have hGdiv : X ^ 3 ∣ G := by
    have h0 : X ∣ Dp (2 * (c + 1) + 1) := by
      have := Dp_dvd (a := 2 * (c + 1) + 1) (j := 0) (by omega)
      simpa using this
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd h0 3) _
  have hsh := lam_succ_shift h G
  rw [coeff_two_of_cube hGdiv] at hsh
  have e1 : (X - C (((c + 1 : ℕ)) : ℚ)).comp (X + 1) = X - C (c : ℚ) := by
    simp only [sub_comp, X_comp, C_comp]
    push_cast
    simp only [C_add, C_1]
    ring
  have hGc : G.comp (X + 1) = ((X + 1) * (Dp (2 * c + 1) * (X - C (((2 * c + 1 : ℕ)) : ℚ)))) ^ 3 *
      g.comp (X - C (c : ℚ)) := by
    rw [hG, Polynomial.mul_comp, Polynomial.pow_comp, hD, Dp_comp_succ, comp_assoc, e1, Dp_succ]
  have e2 : (C (((c : ℚ) + 1) ^ 2) - X ^ 2).comp (X - C (c : ℚ)) =
      -((X + 1) * (X - C (((2 * c + 1 : ℕ)) : ℚ))) := by
    simp only [sub_comp, pow_comp, X_comp, C_comp]
    push_cast
    simp only [C_add, C_mul, C_1, C_pow, map_ofNat]
    ring
  have hR : Dp (2 * c + 1) ^ 3 * ((C (((c : ℚ) + 1) ^ 2) - X ^ 2) ^ 3 * g).comp (X - C (c : ℚ)) =
      -(G.comp (X + 1)) := by
    rw [hGc, Polynomial.mul_comp, Polynomial.pow_comp, e2]
    ring
  rw [hR, map_neg]
  rw [pow_succ]
  have : lam (G.comp (X + 1)) = lam G := by linarith
  rw [this]
  ring

theorem Nf_one_zero (h : LamAx lam) : Nf lam 0 1 = 1 / 2 := by
  rw [Nf_apply]
  simp [Dp, h.cube]

/-- **Lemma M, step 2**: the ratio `N_{c+1}[1] / N_c[1]`. -/
theorem Nf_one_succ (h : LamAx lam) (c : ℕ) :
    Nf lam (c + 1) 1 = Nf lam c 1 *
      (8 * ((c : ℚ) + 1) ^ 5 * (2 * ((c : ℚ) + 1) + 1) ^ 3 /
        (3 * (3 * ((c : ℚ) + 1) + 1) * (3 * ((c : ℚ) + 1) + 2))) := by
  set s : ℚ := (c : ℚ) + 1 with hs
  have hs' : s = (c : ℚ) + 1 := rfl
  have hs0 : 0 < s := by rw [hs]; positivity
  rw [Nf_succ h c 1, mul_one]
  have hid : (C (s ^ 2) - X ^ 2 : ℚ[X]) ^ 3 =
      ee s 3 - C (6 * s + 5) * ee s 2 + C ((2 * s + 1) ^ 2) * ee s 1 := by
    simp only [ee_succ, ee_zero, one_mul, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, map_add,
      map_pow, map_mul, map_one, map_ofNat, add_zero]
    ring
  have e1 := Nf_ee_ee h c s hs' 0 1
  have e2 := Nf_ee_ee h c s hs' 0 2
  have e3 := Nf_ee_ee h c s hs' 0 3
  simp only [ee_zero, one_mul, zero_add] at e1 e2 e3
  rw [hid, map_add, map_sub, Nf_Cmul, Nf_Cmul, e1, e2, e3]
  simp only [poch_succ, poch_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  have h1 : (3 * s + 1) ≠ 0 := by positivity
  have h2 : (3 * s + 2) ≠ 0 := by positivity
  have h3 : (3 * s) ≠ 0 := by positivity
  field_simp
  ring

/-- **Lemma M**: the total mass. -/
theorem Nf_one_closed (h : LamAx lam) (c : ℕ) :
    Nf lam c 1 = ((2 * c + 1).factorial : ℚ) ^ 3 * (c.factorial : ℚ) ^ 3 /
      ((3 * c + 2).factorial : ℚ) := by
  induction c with
  | zero =>
    rw [Nf_one_zero h]
    norm_num [Nat.factorial]
  | succ c ih =>
    rw [Nf_one_succ h, ih]
    have f1 : ((2 * (c + 1) + 1).factorial : ℚ) =
        (2 * c + 3) * (2 * c + 2) * ((2 * c + 1).factorial : ℚ) := by
      rw [show 2 * (c + 1) + 1 = (2 * c + 1) + 1 + 1 by ring, Nat.factorial_succ,
        Nat.factorial_succ]
      push_cast; ring
    have f2 : ((c + 1).factorial : ℚ) = ((c : ℚ) + 1) * (c.factorial : ℚ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have f3 : ((3 * (c + 1) + 2).factorial : ℚ) =
        (3 * c + 5) * (3 * c + 4) * (3 * c + 3) * ((3 * c + 2).factorial : ℚ) := by
      rw [show 3 * (c + 1) + 2 = (3 * c + 2) + 1 + 1 + 1 by ring, Nat.factorial_succ,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast; ring
    rw [f1, f2, f3]
    have hc : (c.factorial : ℚ) ≠ 0 := by positivity
    have hc1 : ((2 * c + 1).factorial : ℚ) ≠ 0 := by positivity
    have hc2 : ((3 * c + 2).factorial : ℚ) ≠ 0 := by positivity
    have hq : (0 : ℚ) ≤ c := Nat.cast_nonneg c
    field_simp
    ring

/-! ## Part F. Degrees and leading coefficients of the families `ee` -/

theorem fac_natDegree (b : ℚ) : (C b - X ^ 2 : ℚ[X]).natDegree = 2 := by
  rw [← neg_sub, natDegree_neg, natDegree_X_pow_sub_C]

theorem fac_leadingCoeff (b : ℚ) : (C b - X ^ 2 : ℚ[X]).leadingCoeff = -1 := by
  rw [← neg_sub, leadingCoeff_neg, leadingCoeff_X_pow_sub_C (by norm_num)]

theorem fac_ne_zero (b : ℚ) : (C b - X ^ 2 : ℚ[X]) ≠ 0 := by
  intro h
  have := fac_natDegree b
  rw [h] at this
  simp at this

theorem ee_natDegree (a : ℚ) (n : ℕ) : (ee a n).natDegree = 2 * n := by
  unfold ee
  rw [natDegree_prod _ _ (fun i _ => fac_ne_zero _),
    sum_congr rfl (fun (i : ℕ) _ => fac_natDegree ((a + (i : ℚ)) ^ 2))]
  simp [mul_comm]

theorem ee_leadingCoeff (a : ℚ) (n : ℕ) : (ee a n).leadingCoeff = (-1) ^ n := by
  unfold ee
  rw [leadingCoeff_prod, prod_congr rfl (fun (i : ℕ) _ => fac_leadingCoeff ((a + (i : ℚ)) ^ 2))]
  simp

theorem ee_coeff_top (a : ℚ) (n : ℕ) : (ee a n).coeff (2 * n) = (-1) ^ n := by
  have := ee_leadingCoeff a n
  rw [leadingCoeff, ee_natDegree] at this
  exact this

/-! ## Part G. The Wilson polynomials and their orthogonality -/

theorem sum_comp' {ι : Type*} (t : Finset ι) (f : ι → ℚ[X]) (q : ℚ[X]) :
    (∑ i ∈ t, f i).comp q = ∑ i ∈ t, (f i).comp q :=
  map_sum (compRingHom q) _ _

/-- The Wilson polynomial `Σ_k q_{nk} e_k`. -/
noncomputable def wp (s σ τ : ℚ) (n : ℕ) : ℚ[X] := ∑ k ∈ range (n + 1), C (qG σ τ n k) * ee s k

theorem wp_comp_neg (s σ τ : ℚ) (n : ℕ) : (wp s σ τ n).comp (-X) = wp s σ τ n := by
  unfold wp
  rw [sum_comp']
  refine sum_congr rfl fun k _ => ?_
  rw [Polynomial.mul_comp, C_comp, ee_comp_neg]

theorem wp_natDegree_le (s σ τ : ℚ) (n : ℕ) : (wp s σ τ n).natDegree ≤ 2 * n := by
  unfold wp
  refine natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hk)
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [ee_natDegree]
  omega

theorem wp_coeff_top (s σ τ : ℚ) (n : ℕ) :
    (wp s σ τ n).coeff (2 * n) = qG σ τ n n * (-1) ^ n := by
  unfold wp
  rw [finset_sum_coeff, sum_eq_single n]
  · rw [coeff_C_mul, ee_coeff_top]
  · intro k hk hkn
    have hk' : k < n := lt_of_le_of_ne (Nat.lt_succ_iff.1 (mem_range.1 hk)) hkn
    rw [coeff_C_mul]
    have : (ee s k).coeff (2 * n) = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [ee_natDegree]; omega
    rw [this, mul_zero]
  · intro hn
    exact absurd (mem_range.2 (Nat.lt_succ_self n)) hn

/-- Pairing a Wilson polynomial with a test polynomial. -/
theorem Nf_wp_mul (c : ℕ) (s σ τ : ℚ) (n : ℕ) (φ : ℚ[X]) (A : ℚ) (J : ℕ)
    (hb : ∀ k, Nf lam c (ee s k * φ) = A * bil σ τ J k) :
    Nf lam c (wp s σ τ n * φ) = A * ∑ k ∈ range (n + 1), qG σ τ n k * bil σ τ J k := by
  unfold wp
  rw [sum_mul, map_sum, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [mul_assoc, Nf_Cmul, hb]
  ring

theorem bil_even (s : ℚ) (J k : ℕ) :
    bil s (2 * s) J k = poch s (J + k) * poch s J ^ 2 * poch (2 * s) k ^ 2 / poch (3 * s) (J + k) := by
  unfold bil
  rw [show s + 2 * s = 3 * s by ring]

theorem bil_odd {s : ℚ} (hs : 0 < s) (j k : ℕ) :
    poch s (j + 1 + k) * poch s (j + 1) ^ 2 * poch (2 * s) k ^ 2 / poch (3 * s) (j + 1 + k) =
      s ^ 2 / 3 * bil (s + 1) (2 * s) j k := by
  unfold bil
  have e1 : poch s (j + 1 + k) = s * poch (s + 1) (j + k) := by
    rw [show j + 1 + k = (j + k) + 1 by ring, poch_succ']
  have e2 : poch s (j + 1) = s * poch (s + 1) j := poch_succ' s j
  have e3 : poch (3 * s) (j + 1 + k) = 3 * s * poch (3 * s + 1) (j + k) := by
    rw [show j + 1 + k = (j + k) + 1 by ring, poch_succ']
  rw [e1, e2, e3, show s + 1 + 2 * s = 3 * s + 1 by ring]
  have : 0 < poch (3 * s + 1) (j + k) := poch_pos (by positivity) _
  field_simp

/-- Even block: orthogonality below the diagonal. -/
theorem Nf_wpE_vanish (h : LamAx lam) (c : ℕ) (s : ℚ) (hs : s = (c : ℚ) + 1) {n J : ℕ}
    (hJ : J < n) : Nf lam c (wp s s (2 * s) n * ee 0 J) = 0 := by
  have hs0 : 0 < s := by rw [hs]; positivity
  have hb : ∀ k, Nf lam c (ee s k * ee 0 J) = Nf lam c 1 * bil s (2 * s) J k := by
    intro k
    rw [mul_comm, Nf_ee_ee h c s hs, bil_even]
  rw [Nf_wp_mul c s s (2 * s) n _ _ J hb,
    W_vanish hs0 (by positivity) (by linarith) hJ, mul_zero]

/-- Even block: the diagonal value. -/
theorem Nf_wpE_diag (h : LamAx lam) (c : ℕ) (s : ℚ) (hs : s = (c : ℚ) + 1) (n : ℕ) :
    Nf lam c (wp s s (2 * s) n * ee 0 n) =
      Nf lam c 1 * (qG s (2 * s) n n * wNorm s (2 * s) n) := by
  have hs0 : 0 < s := by rw [hs]; positivity
  have hb : ∀ k, Nf lam c (ee s k * ee 0 n) = Nf lam c 1 * bil s (2 * s) n k := by
    intro k
    rw [mul_comm, Nf_ee_ee h c s hs, bil_even]
  rw [Nf_wp_mul c s s (2 * s) n _ _ n hb, W_diag hs0 (by positivity) (by linarith)]

/-- Odd block: orthogonality below the diagonal. -/
theorem Nf_wpO_vanish (h : LamAx lam) (c : ℕ) (s : ℚ) (hs : s = (c : ℚ) + 1) {n j : ℕ}
    (hj : j < n) : Nf lam c (wp s (s + 1) (2 * s) n * ee 0 (j + 1)) = 0 := by
  have hs0 : 0 < s := by rw [hs]; positivity
  have hb : ∀ k, Nf lam c (ee s k * ee 0 (j + 1)) =
      (s ^ 2 / 3 * Nf lam c 1) * bil (s + 1) (2 * s) j k := by
    intro k
    rw [mul_comm, Nf_ee_ee h c s hs, bil_odd hs0]
    ring
  rw [Nf_wp_mul c s (s + 1) (2 * s) n _ _ j hb,
    W_vanish (by linarith) (by positivity) (by linarith) hj, mul_zero]

/-- Odd block: the diagonal value. -/
theorem Nf_wpO_diag (h : LamAx lam) (c : ℕ) (s : ℚ) (hs : s = (c : ℚ) + 1) (n : ℕ) :
    Nf lam c (wp s (s + 1) (2 * s) n * ee 0 (n + 1)) =
      (s ^ 2 / 3 * Nf lam c 1) * (qG (s + 1) (2 * s) n n * wNorm (s + 1) (2 * s) n) := by
  have hs0 : 0 < s := by rw [hs]; positivity
  have hb : ∀ k, Nf lam c (ee s k * ee 0 (n + 1)) =
      (s ^ 2 / 3 * Nf lam c 1) * bil (s + 1) (2 * s) n k := by
    intro k
    rw [mul_comm, Nf_ee_ee h c s hs, bil_odd hs0]
    ring
  rw [Nf_wp_mul c s (s + 1) (2 * s) n _ _ n hb,
    W_diag (by linarith) (by positivity) (by linarith)]

/-! ## Part H. Gram matrices and triangular determinants -/

theorem eq_sum_fin' {N : ℕ} (f : ℚ[X]) (hf : f.natDegree < N) :
    f = ∑ i : Fin N, C (f.coeff i) * X ^ (i : ℕ) := by
  conv_lhs => rw [as_sum_range' f N hf]
  rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i) N]
  refine sum_congr rfl fun i _ => ?_
  rw [C_mul_X_pow_eq_monomial]

theorem L_mul_eq' {N : ℕ} (L : ℚ[X] →ₗ[ℚ] ℚ) (f g : ℚ[X]) (hf : f.natDegree < N)
    (hg : g.natDegree < N) :
    L (f * g) = ∑ i : Fin N, ∑ j : Fin N, f.coeff i * g.coeff j * L (X ^ ((i : ℕ) + j)) := by
  conv_lhs => rw [eq_sum_fin' f hf, eq_sum_fin' g hg]
  rw [sum_mul]
  simp_rw [mul_sum, map_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have : C (f.coeff i) * X ^ (i : ℕ) * (C (g.coeff j) * X ^ (j : ℕ)) =
      (f.coeff i * g.coeff j) • (X ^ ((i : ℕ) + j) : ℚ[X]) := by
    rw [smul_eq_C_mul, C_mul, pow_add]; ring
  rw [this, map_smul, smul_eq_mul]

/-- The Gram matrix of two triangular families is `A H Bᵀ` (`A`, `B` coefficient matrices). -/
theorem det_gram_tri {K : ℕ} (L : ℚ[X] →ₗ[ℚ] ℚ) (p q : ℕ → ℚ[X])
    (hp : ∀ i < K, (p i).natDegree ≤ i) (hq : ∀ i < K, (q i).natDegree ≤ i) :
    (Matrix.of fun i j : Fin K => L (p i * q j)).det =
      (Matrix.of fun i j : Fin K => L (X ^ ((i : ℕ) + j))).det *
        (∏ i : Fin K, (p i).coeff i) * ∏ i : Fin K, (q i).coeff i := by
  set A : Matrix (Fin K) (Fin K) ℚ := Matrix.of fun i j => (p i).coeff j with hA
  set B : Matrix (Fin K) (Fin K) ℚ := Matrix.of fun i j => (q i).coeff j with hB
  set H : Matrix (Fin K) (Fin K) ℚ := Matrix.of fun i j => L (X ^ ((i : ℕ) + j)) with hH
  have hG : (Matrix.of fun i j : Fin K => L (p i * q j)) = A * H * B.transpose := by
    ext x y
    rw [Matrix.of_apply, L_mul_eq' L _ _ (lt_of_le_of_lt (hp x x.2) x.2)
      (lt_of_le_of_lt (hq y y.2) y.2), Matrix.mul_apply]
    simp_rw [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp [hA, hB, hH]
    ring
  have hAd : A.det = ∏ i : Fin K, (p i).coeff i := by
    rw [Matrix.det_of_lowerTriangular A]
    · rfl
    · intro i j hij
      have : i < j := hij
      simp only [hA, Matrix.of_apply]
      apply coeff_eq_zero_of_natDegree_lt
      exact lt_of_le_of_lt (hp i i.2) this
  have hBd : B.det = ∏ i : Fin K, (q i).coeff i := by
    rw [Matrix.det_of_lowerTriangular B]
    · rfl
    · intro i j hij
      have : i < j := hij
      simp only [hB, Matrix.of_apply]
      apply coeff_eq_zero_of_natDegree_lt
      exact lt_of_le_of_lt (hq i i.2) this
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hAd, hBd]
  ring

/-- Orthogonality makes the Gram matrix triangular: the Hankel determinant is a ratio of products. -/
theorem hankel_det_of_orth {K : ℕ} (L : ℚ[X] →ₗ[ℚ] ℚ) (p q : ℕ → ℚ[X])
    (hp : ∀ i < K, (p i).natDegree ≤ i) (hq : ∀ i < K, (q i).natDegree ≤ i)
    (horth : ∀ i < K, ∀ k < i, L (p i * q k) = 0) :
    (Matrix.of fun i j : Fin K => L (X ^ ((i : ℕ) + j))).det *
        (∏ i : Fin K, (p i).coeff i) * ∏ i : Fin K, (q i).coeff i =
      ∏ i : Fin K, L (p i * q i) := by
  rw [← det_gram_tri L p q hp hq]
  rw [Matrix.det_of_upperTriangular]
  · rfl
  · intro i j hij
    have : j < i := hij
    simp only [Matrix.of_apply]
    exact horth i i.2 j this

/-! ## Part I. The orthogonal family and the Hankel determinant of `N_c` -/

/-- `s = c + 1`. -/
noncomputable abbrev sc (c : ℕ) : ℚ := (c : ℚ) + 1

theorem sc_pos (c : ℕ) : 0 < sc c := by unfold sc; positivity
theorem sc_ge (c : ℕ) : 1 ≤ sc c := by
  unfold sc
  have : (0 : ℚ) ≤ c := Nat.cast_nonneg c
  linarith

/-- The monic-up-to-constants orthogonal family (even index: Wilson at `(s, 2s)`; odd index:
`z` times Wilson at `(s+1, 2s)`). -/
noncomputable def pSeq (c i : ℕ) : ℚ[X] :=
  if i % 2 = 0 then wp (sc c) (sc c) (2 * sc c) (i / 2)
  else X * wp (sc c) (sc c + 1) (2 * sc c) (i / 2)

/-- The test family (`f_n` at even index, `z f¹_n` at odd index). -/
noncomputable def qSeq (c i : ℕ) : ℚ[X] :=
  if i % 2 = 0 then ee 0 (i / 2) else X * ee 1 (i / 2)

theorem pSeq_even (c n : ℕ) : pSeq c (2 * n) = wp (sc c) (sc c) (2 * sc c) n := by
  unfold pSeq
  rw [if_pos (by omega), show 2 * n / 2 = n by omega]

theorem pSeq_odd (c n : ℕ) : pSeq c (2 * n + 1) = X * wp (sc c) (sc c + 1) (2 * sc c) n := by
  unfold pSeq
  rw [if_neg (by omega), show (2 * n + 1) / 2 = n by omega]

theorem qSeq_even (c n : ℕ) : qSeq c (2 * n) = ee 0 n := by
  unfold qSeq
  rw [if_pos (by omega), show 2 * n / 2 = n by omega]

theorem qSeq_odd (c n : ℕ) : qSeq c (2 * n + 1) = X * ee 1 n := by
  unfold qSeq
  rw [if_neg (by omega), show (2 * n + 1) / 2 = n by omega]

theorem pSeq_natDegree (c i : ℕ) : (pSeq c i).natDegree ≤ i := by
  rcases Nat.even_or_odd' i with ⟨n, rfl | rfl⟩
  · rw [pSeq_even]; exact wp_natDegree_le _ _ _ _
  · rw [pSeq_odd]
    refine (natDegree_mul_le).trans ?_
    have := wp_natDegree_le (sc c) (sc c + 1) (2 * sc c) n
    have h2 : (X : ℚ[X]).natDegree ≤ 1 := natDegree_X_le
    omega

theorem qSeq_natDegree (c i : ℕ) : (qSeq c i).natDegree ≤ i := by
  rcases Nat.even_or_odd' i with ⟨n, rfl | rfl⟩
  · rw [qSeq_even, ee_natDegree]
  · rw [qSeq_odd]
    refine (natDegree_mul_le).trans ?_
    have := ee_natDegree 1 n
    have h2 : (X : ℚ[X]).natDegree ≤ 1 := natDegree_X_le
    omega

/-- Diagonal coefficient product. -/
noncomputable def dg (c i : ℕ) : ℚ :=
  if i % 2 = 0 then qG (sc c) (2 * sc c) (i / 2) (i / 2)
  else qG (sc c + 1) (2 * sc c) (i / 2) (i / 2)

theorem dg_even (c n : ℕ) : dg c (2 * n) = qG (sc c) (2 * sc c) n n := by
  unfold dg
  rw [if_pos (by omega), show 2 * n / 2 = n by omega]

theorem dg_odd (c n : ℕ) : dg c (2 * n + 1) = qG (sc c + 1) (2 * sc c) n n := by
  unfold dg
  rw [if_neg (by omega), show (2 * n + 1) / 2 = n by omega]

theorem dg_ne_zero (c i : ℕ) : dg c i ≠ 0 := by
  have hs := sc_pos c
  have h1 := sc_ge c
  rcases Nat.even_or_odd' i with ⟨n, rfl | rfl⟩
  · rw [dg_even]; exact qG_diag_ne hs (by positivity) (by linarith) n
  · rw [dg_odd]; exact qG_diag_ne (by linarith) (by positivity) (by linarith) n

theorem coeff_pq (c i : ℕ) : (pSeq c i).coeff i * (qSeq c i).coeff i = dg c i := by
  rcases Nat.even_or_odd' i with ⟨n, rfl | rfl⟩
  · rw [pSeq_even, qSeq_even, dg_even, wp_coeff_top, ee_coeff_top]
    rcases neg_one_pow_eq_or ℚ n with h | h <;> rw [h] <;> ring
  · rw [pSeq_odd, qSeq_odd, dg_odd, coeff_X_mul, coeff_X_mul, wp_coeff_top, ee_coeff_top]
    rcases neg_one_pow_eq_or ℚ n with h | h <;> rw [h] <;> ring

/-- Orthogonality of `pSeq` against `qSeq` below the diagonal. -/
theorem orth (h : LamAx lam) (c : ℕ) {i k : ℕ} (hk : k < i) :
    Nf lam c (pSeq c i * qSeq c k) = 0 := by
  have hs := sc_pos c
  rcases Nat.even_or_odd' i with ⟨a, rfl | rfl⟩ <;> rcases Nat.even_or_odd' k with ⟨b, rfl | rfl⟩
  · rw [pSeq_even, qSeq_even]
    exact Nf_wpE_vanish h c (sc c) rfl (by omega)
  · rw [pSeq_even, qSeq_odd]
    apply Nf_parity_odd h
    simp only [Polynomial.mul_comp, X_comp, wp_comp_neg, ee_comp_neg]
    ring
  · rw [pSeq_odd, qSeq_even]
    apply Nf_parity_odd h
    simp only [Polynomial.mul_comp, X_comp, wp_comp_neg, ee_comp_neg]
    ring
  · rw [pSeq_odd, qSeq_odd]
    have e : X * wp (sc c) (sc c + 1) (2 * sc c) a * (X * ee 1 b) =
        -(wp (sc c) (sc c + 1) (2 * sc c) a * ee 0 (b + 1)) := by
      have := ee_succ' (0 : ℚ) b
      simp only [zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, map_zero,
        zero_sub] at this
      rw [this]; ring
    rw [e, map_neg, Nf_wpO_vanish h c (sc c) rfl (by omega), neg_zero]

/-- The weights `ν_i`: ratios of the diagonal Gram entries to the leading-coefficient products. -/
noncomputable def nuW (lam : ℚ[X] →ₗ[ℚ] ℚ) (c i : ℕ) : ℚ :=
  if i % 2 = 0 then Nf lam c 1 * wNorm (sc c) (2 * sc c) (i / 2)
  else -(sc c ^ 2 / 3 * Nf lam c 1 * wNorm (sc c + 1) (2 * sc c) (i / 2))

theorem diag (h : LamAx lam) (c i : ℕ) : Nf lam c (pSeq c i * qSeq c i) = dg c i * nuW lam c i := by
  rcases Nat.even_or_odd' i with ⟨n, rfl | rfl⟩
  · rw [pSeq_even, qSeq_even, dg_even, nuW, if_pos (by omega), show 2 * n / 2 = n by omega,
      Nf_wpE_diag h c (sc c) rfl]
    ring
  · rw [pSeq_odd, qSeq_odd, dg_odd, nuW, if_neg (by omega), show (2 * n + 1) / 2 = n by omega]
    have e : X * wp (sc c) (sc c + 1) (2 * sc c) n * (X * ee 1 n) =
        -(wp (sc c) (sc c + 1) (2 * sc c) n * ee 0 (n + 1)) := by
      have := ee_succ' (0 : ℚ) n
      simp only [zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, map_zero,
        zero_sub] at this
      rw [this]; ring
    rw [e, map_neg, Nf_wpO_diag h c (sc c) rfl]
    ring

/-- The Hankel determinant of `N_c` is `∏ ν_i`. -/
theorem det_Nf_hankel (h : LamAx lam) (c K : ℕ) :
    (Matrix.of fun i j : Fin K => Nf lam c (X ^ ((i : ℕ) + j))).det = ∏ i ∈ range K, nuW lam c i := by
  have key := hankel_det_of_orth (Nf lam c) (pSeq c) (qSeq c) (K := K)
    (fun i _ => pSeq_natDegree c i) (fun i _ => qSeq_natDegree c i)
    (fun i _ k hk => orth h c hk)
  rw [mul_assoc, ← prod_mul_distrib] at key
  simp_rw [coeff_pq, diag h] at key
  rw [prod_mul_distrib, Fin.prod_univ_eq_prod_range (fun i => dg c i) K,
    Fin.prod_univ_eq_prod_range (fun i => nuW lam c i) K] at key
  have hne : ∏ i ∈ range K, dg c i ≠ 0 := prod_ne_zero_iff.2 fun i _ => dg_ne_zero c i
  apply mul_right_cancel₀ hne
  rw [key]
  ring

/-! ## Part J. Closed forms -/

/-- `h⁺_n = n! (c+n)!³ (2c+1+n)!³ (n+3c+1)! / ((2n+3c+1)! (2n+3c+2)!)`. -/
noncomputable def hPlus (c n : ℕ) : ℚ :=
  (n.factorial : ℚ) * ((c + n).factorial : ℚ) ^ 3 * ((2 * c + 1 + n).factorial : ℚ) ^ 3 *
    ((n + 3 * c + 1).factorial : ℚ) /
      (((2 * n + 3 * c + 1).factorial : ℚ) * ((2 * n + 3 * c + 2).factorial : ℚ))

/-- `h⁻_n = n! (c+1+n)!³ (2c+1+n)!³ (n+3c+2)! / ((2n+3c+2)! (2n+3c+3)!)`. -/
noncomputable def hMinus (c n : ℕ) : ℚ :=
  (n.factorial : ℚ) * ((c + 1 + n).factorial : ℚ) ^ 3 * ((2 * c + 1 + n).factorial : ℚ) ^ 3 *
    ((n + 3 * c + 2).factorial : ℚ) /
      (((2 * n + 3 * c + 2).factorial : ℚ) * ((2 * n + 3 * c + 3).factorial : ℚ))

theorem hPlus_eq (c n : ℕ) :
    ((2 * c + 1).factorial : ℚ) ^ 3 * (c.factorial : ℚ) ^ 3 / ((3 * c + 2).factorial : ℚ) *
      wNorm (sc c) (2 * sc c) n = hPlus c n := by
  unfold wNorm hPlus sc
  have p1 : poch ((c : ℚ) + 1) n = ((c + n).factorial : ℚ) / (c.factorial : ℚ) :=
    poch_nat _ c rfl n
  have p2 : poch (2 * ((c : ℚ) + 1)) n =
      ((2 * c + 1 + n).factorial : ℚ) / ((2 * c + 1).factorial : ℚ) :=
    poch_nat _ (2 * c + 1) (by push_cast; ring) n
  have p3 : poch (((c : ℚ) + 1) + 2 * ((c : ℚ) + 1)) n =
      ((3 * c + 2 + n).factorial : ℚ) / ((3 * c + 2).factorial : ℚ) :=
    poch_nat _ (3 * c + 2) (by push_cast; ring) n
  have p4 : poch ((n : ℚ) + ((c : ℚ) + 1) + 2 * ((c : ℚ) + 1) - 1) n =
      ((n + 3 * c + 1 + n).factorial : ℚ) / ((n + 3 * c + 1).factorial : ℚ) :=
    poch_nat _ (n + 3 * c + 1) (by push_cast; ring) n
  have p5 : poch ((n : ℚ) + ((c : ℚ) + 1) + 2 * ((c : ℚ) + 1)) n =
      ((n + 3 * c + 2 + n).factorial : ℚ) / ((n + 3 * c + 2).factorial : ℚ) :=
    poch_nat _ (n + 3 * c + 2) (by push_cast; ring) n
  rw [p1, p2, p3, p4, p5, show 3 * c + 2 + n = n + 3 * c + 2 by ring,
    show n + 3 * c + 1 + n = 2 * n + 3 * c + 1 by ring,
    show n + 3 * c + 2 + n = 2 * n + 3 * c + 2 by ring]
  field_simp

theorem hMinus_eq (c n : ℕ) :
    sc c ^ 2 / 3 * (((2 * c + 1).factorial : ℚ) ^ 3 * (c.factorial : ℚ) ^ 3 /
      ((3 * c + 2).factorial : ℚ)) * wNorm (sc c + 1) (2 * sc c) n = hMinus c n := by
  unfold wNorm hMinus sc
  have p1 : poch ((c : ℚ) + 1 + 1) n = ((c + 1 + n).factorial : ℚ) / ((c + 1).factorial : ℚ) :=
    poch_nat _ (c + 1) (by push_cast; ring) n
  have p2 : poch (2 * ((c : ℚ) + 1)) n =
      ((2 * c + 1 + n).factorial : ℚ) / ((2 * c + 1).factorial : ℚ) :=
    poch_nat _ (2 * c + 1) (by push_cast; ring) n
  have p3 : poch (((c : ℚ) + 1 + 1) + 2 * ((c : ℚ) + 1)) n =
      ((3 * c + 3 + n).factorial : ℚ) / ((3 * c + 3).factorial : ℚ) :=
    poch_nat _ (3 * c + 3) (by push_cast; ring) n
  have p4 : poch ((n : ℚ) + ((c : ℚ) + 1 + 1) + 2 * ((c : ℚ) + 1) - 1) n =
      ((n + 3 * c + 2 + n).factorial : ℚ) / ((n + 3 * c + 2).factorial : ℚ) :=
    poch_nat _ (n + 3 * c + 2) (by push_cast; ring) n
  have p5 : poch ((n : ℚ) + ((c : ℚ) + 1 + 1) + 2 * ((c : ℚ) + 1)) n =
      ((n + 3 * c + 3 + n).factorial : ℚ) / ((n + 3 * c + 3).factorial : ℚ) :=
    poch_nat _ (n + 3 * c + 3) (by push_cast; ring) n
  have f1 : ((3 * c + 3).factorial : ℚ) = (3 * c + 3) * ((3 * c + 2).factorial : ℚ) := by
    rw [show 3 * c + 3 = (3 * c + 2) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  have f2 : ((c + 1).factorial : ℚ) = ((c : ℚ) + 1) * (c.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f3 : ((n + 3 * c + 3).factorial : ℚ) = (n + 3 * c + 3) * ((n + 3 * c + 2).factorial : ℚ) := by
    rw [show n + 3 * c + 3 = (n + 3 * c + 2) + 1 by ring, Nat.factorial_succ]; push_cast; ring
  rw [p1, p2, p3, p4, p5, show 3 * c + 3 + n = n + 3 * c + 3 by ring,
    show n + 3 * c + 2 + n = 2 * n + 3 * c + 2 by ring,
    show n + 3 * c + 3 + n = 2 * n + 3 * c + 3 by ring, f1, f2, f3]
  have hq : (0 : ℚ) ≤ c := Nat.cast_nonneg c
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  field_simp

theorem nuW_even (h : LamAx lam) (c n : ℕ) : nuW lam c (2 * n) = hPlus c n := by
  unfold nuW
  rw [if_pos (by omega), show 2 * n / 2 = n by omega, Nf_one_closed h, hPlus_eq]

theorem nuW_odd (h : LamAx lam) (c n : ℕ) : nuW lam c (2 * n + 1) = -hMinus c n := by
  unfold nuW
  rw [if_neg (by omega), show (2 * n + 1) / 2 = n by omega, Nf_one_closed h, hMinus_eq]

/-- The product of the weights. -/
theorem prod_nuW (h : LamAx lam) (c K : ℕ) :
    ∏ i ∈ range K, nuW lam c i =
      (-1) ^ (K / 2) * (∏ n ∈ range ((K + 1) / 2), hPlus c n) * ∏ n ∈ range (K / 2), hMinus c n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [prod_range_succ, ih]
    rcases Nat.even_or_odd' K with ⟨m, rfl | rfl⟩
    · have e1 : 2 * m / 2 = m := by omega
      have e2 : (2 * m + 1) / 2 = m := by omega
      have e3 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      simp only [e1, e2, e3]
      rw [nuW_even h, prod_range_succ (fun n => hPlus c n) m]
      ring
    · have e2 : (2 * m + 1) / 2 = m := by omega
      have e3 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      have e4 : (2 * m + 1 + 1 + 1) / 2 = m + 1 := by omega
      simp only [e2, e3, e4]
      rw [nuW_odd h, prod_range_succ (fun n => hMinus c n) m]
      ring

/-! ## Part K. The Hankel determinant of `λ(D_a³ x^{i+j})`, abstract form -/

theorem wilson_hankel_of_ax (h : LamAx lam) (c K : ℕ) :
    (Matrix.of fun i j : Fin K => lam (Dp (2 * c + 1) ^ 3 * X ^ ((i : ℕ) + j))).det =
      (-1) ^ (c * K + K / 2) * (∏ n ∈ range ((K + 1) / 2), hPlus c n) *
        ∏ n ∈ range (K / 2), hMinus c n := by
  set P : ℕ → ℚ[X] := fun i => (X + C (c : ℚ)) ^ i with hPdef
  have hPd : ∀ i, (P i).natDegree = i := by
    intro i
    simp only [hPdef, natDegree_pow, natDegree_X_add_C, mul_one]
  have hPc : ∀ i, (P i).coeff i = 1 := by
    intro i
    simp only [hPdef, coeff_X_add_C_pow]
    simp
  have hcomp : ∀ i j : ℕ, (P i * P j).comp (X - C (c : ℚ)) = X ^ (i + j) := by
    intro i j
    simp only [hPdef, Polynomial.mul_comp, Polynomial.pow_comp, add_comp, X_comp, C_comp, sub_add_cancel,
      pow_add]
  have hM : (Matrix.of fun i j : Fin K => lam (Dp (2 * c + 1) ^ 3 * X ^ ((i : ℕ) + j))) =
      ((-1 : ℚ) ^ c) • (Matrix.of fun i j : Fin K => Nf lam c (P i * P j)) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Nf_apply, hcomp, ← mul_assoc]
    rcases neg_one_pow_eq_or ℚ c with h1 | h1 <;> rw [h1] <;> ring
  rw [hM, Matrix.det_smul, Fintype.card_fin,
    det_gram_tri (Nf lam c) P P (K := K) (fun i _ => (hPd i).le) (fun i _ => (hPd i).le)]
  simp only [hPc, prod_const_one, mul_one]
  rw [det_Nf_hankel h, prod_nuW h, ← pow_mul, pow_add]
  ring

/-! ## Part L. The Bernoulli functional `λ(x^e) = e B_{e−1}` -/

/-- `λ(x^e) = e · B_{e−1}` with Mathlib's `bernoulli` (`B₁ = −1/2`). -/
noncomputable def lamB : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun e : ℕ => ((e : ℚ) * bernoulli (e - 1)) • (LinearMap.id : ℚ →ₗ[ℚ] ℚ)

theorem lamB_monomial (e : ℕ) (a : ℚ) : lamB (monomial e a) = a * ((e : ℚ) * bernoulli (e - 1)) := by
  simp [lamB, Polynomial.lsum_apply, sum_monomial_index]
  ring

theorem lamB_X_pow (e : ℕ) : lamB (X ^ e) = (e : ℚ) * bernoulli (e - 1) := by
  rw [X_pow_eq_monomial, lamB_monomial]
  ring

theorem lamB_C_mul (a : ℚ) (p : ℚ[X]) : lamB (C a * p) = a * lamB p := by
  rw [C_mul', map_smul, smul_eq_mul]

/-- `Σ_{i<d} C(d,i) · i · B_{i−1} = 2 [d = 2]`. -/
theorem sum_choose_bernoulli (d : ℕ) :
    ∑ i ∈ range d, (d.choose i : ℚ) * ((i : ℚ) * bernoulli (i - 1)) = if d = 2 then 2 else 0 := by
  cases d with
  | zero => simp
  | succ d =>
    rw [sum_range_succ']
    have h1 : ∀ i ∈ range d, ((d + 1).choose (i + 1) : ℚ) * (((i + 1 : ℕ) : ℚ) * bernoulli (i + 1 - 1)) =
        ((d + 1 : ℕ) : ℚ) * ((d.choose i : ℚ) * bernoulli i) := by
      intro i _
      have := Nat.add_one_mul_choose_eq d i
      have h2 : ((d + 1 : ℕ) : ℚ) * (d.choose i : ℚ) = ((d + 1).choose (i + 1) : ℚ) * ((i + 1 : ℕ) : ℚ) := by
        exact_mod_cast this
      rw [Nat.add_sub_cancel]
      linear_combination (-(bernoulli i)) * h2
    rw [sum_congr rfl h1, ← mul_sum, sum_bernoulli]
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    by_cases hd : d = 1
    · subst hd; norm_num
    · rw [if_neg hd, if_neg (by omega)]; simp

theorem lamB_shift (f : ℚ[X]) : lamB (f.comp (X + 1) - f) = 2 * f.coeff 2 := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_comp, coeff_add]
    have : (p.comp (X + 1) + q.comp (X + 1)) - (p + q) = (p.comp (X + 1) - p) + (q.comp (X + 1) - q) := by
      ring
    rw [this, map_add, hp, hq]; ring
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [mul_comp, C_comp, pow_comp, X_comp]
    have : C a * (X + 1) ^ n - C a * X ^ n = C a * ((X + 1) ^ n - X ^ n) := by ring
    rw [this, lamB_C_mul]
    have h2 : ((X + 1 : ℚ[X]) ^ n - X ^ n) = ∑ i ∈ range n, (n.choose i : ℚ) • (X : ℚ[X]) ^ i := by
      have := one_add_X_pow_sub_X_pow (S := ℚ) n
      rw [add_comm (1 : ℚ[X]) X] at this
      rw [this]
      refine sum_congr rfl fun i _ => ?_
      rw [← Nat.cast_smul_eq_nsmul ℚ]
    rw [h2, map_sum]
    simp_rw [map_smul, lamB_X_pow, smul_eq_mul]
    rw [sum_choose_bernoulli, coeff_C_mul, coeff_X_pow]
    rcases eq_or_ne n 2 with hn | hn
    · subst hn; simp; ring
    · have hn' : (2 : ℕ) ≠ n := fun h => hn h.symm
      simp [hn, hn']

theorem bern_sign (n : ℕ) :
    ((-1 : ℚ) ^ n) * ((n : ℚ) * bernoulli (n - 1)) =
      -((n : ℚ) * bernoulli (n - 1)) - 2 * (if 2 = n then 1 else 0) := by
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow]
    by_cases h0 : n = 0
    · subst h0; simp
    · by_cases h2 : n = 2
      · subst h2; norm_num [bernoulli_one]
      · have h3 : Odd (n - 1) := by
          obtain ⟨k, hk⟩ := he
          exact ⟨k - 1, by omega⟩
        have h4 : 1 < n - 1 := by
          obtain ⟨k, hk⟩ := he
          omega
        rw [bernoulli_eq_zero_of_odd h3 h4, if_neg (Ne.symm h2)]
        simp
  · rw [ho.neg_one_pow, if_neg (by rintro rfl; exact absurd ho (by decide))]
    ring

theorem lamB_refl (g : ℚ[X]) : lamB (g.comp (-X)) = -lamB g - 2 * g.coeff 2 := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [add_comp, coeff_add, map_add, map_add, hp, hq]; ring
  | monomial n a =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [mul_comp, C_comp, pow_comp, X_comp]
    have : (-X : ℚ[X]) ^ n = C ((-1 : ℚ) ^ n) * X ^ n := by
      rw [neg_pow, C_pow, C_neg, C_1]
    rw [this, ← mul_assoc, ← C_mul, lamB_C_mul, lamB_C_mul, lamB_X_pow, coeff_C_mul, coeff_X_pow]
    have hb := bern_sign n
    by_cases hn : n = 2
    · subst hn; norm_num [bernoulli_one] at hb ⊢
      linarith
    · have hn' : ¬ (2 : ℕ) = n := fun h => hn h.symm
      simp only [if_neg hn', mul_zero, sub_zero] at hb ⊢
      linear_combination a * hb

theorem lamB_ax : LamAx lamB where
  shift := lamB_shift
  refl := lamB_refl
  cube := by
    rw [lamB_X_pow]
    norm_num [bernoulli_two]

/-! ## Part M. The theorem and its corollaries -/

/-- **Theorem W-ALG.** For `a = 2c + 1`, `λ(x^e) = e B_{e−1}`:
`det[λ(D_a³ x^{i+j})]_{i,j<K} = (−1)^{cK + ⌊K/2⌋} ∏_{n<⌈K/2⌉} h⁺_n ∏_{n<⌊K/2⌋} h⁻_n`. -/
theorem wilson_hankel (c K : ℕ) :
    (Matrix.of fun i j : Fin K => lamB (Dp (2 * c + 1) ^ 3 * X ^ ((i : ℕ) + j))).det =
      (-1) ^ (c * K + K / 2) * (∏ n ∈ range ((K + 1) / 2), hPlus c n) *
        ∏ n ∈ range (K / 2), hMinus c n :=
  wilson_hankel_of_ax lamB_ax c K

/-- The same in terms of the moments `λ(D_a³ x^e)`. -/
theorem wilson_hankel_moments (c K : ℕ) :
    (Matrix.of fun i j : Fin K =>
        lamB (Dp (2 * c + 1) ^ 3 * X ^ ((i : ℕ) + j))).det ≠ 0 := by
  rw [wilson_hankel]
  have h1 : ∀ n, 0 < hPlus c n := fun n => by unfold hPlus; positivity
  have h2 : ∀ n, 0 < hMinus c n := fun n => by unfold hMinus; positivity
  have a1 : 0 < ∏ n ∈ range ((K + 1) / 2), hPlus c n := prod_pos fun n _ => h1 n
  have a2 : 0 < ∏ n ∈ range (K / 2), hMinus c n := prod_pos fun n _ => h2 n
  have : ((-1 : ℚ) ^ (c * K + K / 2)) ≠ 0 := by simp
  positivity

/-- The `p`-adic unit predicate. -/
def PUnit' (p : ℕ) (q : ℚ) : Prop := q ≠ 0 ∧ padicValRat p q = 0

theorem PUnit'.mul {p : ℕ} [Fact p.Prime] {a b : ℚ} (ha : PUnit' p a) (hb : PUnit' p b) :
    PUnit' p (a * b) := by
  refine ⟨mul_ne_zero ha.1 hb.1, ?_⟩
  rw [padicValRat.mul ha.1 hb.1, ha.2, hb.2]; simp

theorem PUnit'.div {p : ℕ} [Fact p.Prime] {a b : ℚ} (ha : PUnit' p a) (hb : PUnit' p b) :
    PUnit' p (a / b) := by
  refine ⟨div_ne_zero ha.1 hb.1, ?_⟩
  rw [padicValRat.div ha.1 hb.1, ha.2, hb.2]; simp

theorem PUnit'.pow {p : ℕ} [Fact p.Prime] {a : ℚ} (ha : PUnit' p a) (n : ℕ) : PUnit' p (a ^ n) := by
  induction n with
  | zero => exact ⟨by simp, by simp⟩
  | succ n ih => rw [pow_succ]; exact ih.mul ha

theorem PUnit'.fact {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : m < p) : PUnit' p (m.factorial : ℚ) := by
  refine ⟨by positivity, ?_⟩
  rw [padicValRat.of_nat]
  have : ¬ p ∣ m.factorial := fun hd => by
    have := (Nat.Prime.dvd_factorial (Fact.out : p.Prime)).1 hd
    omega
  simp [padicValNat.eq_zero_of_not_dvd this]

theorem hPlus_unit {p : ℕ} [Fact p.Prime] {c n : ℕ} (hp : 2 * n + 3 * c + 2 < p) :
    PUnit' p (hPlus c n) := by
  unfold hPlus
  refine PUnit'.div ?_ ?_
  · exact (((PUnit'.fact (by omega)).mul ((PUnit'.fact (by omega)).pow 3)).mul
      ((PUnit'.fact (by omega)).pow 3)).mul (PUnit'.fact (by omega))
  · exact (PUnit'.fact (by omega)).mul (PUnit'.fact (by omega))

theorem hMinus_unit {p : ℕ} [Fact p.Prime] {c n : ℕ} (hp : 2 * n + 3 * c + 3 < p) :
    PUnit' p (hMinus c n) := by
  unfold hMinus
  refine PUnit'.div ?_ ?_
  · exact (((PUnit'.fact (by omega)).mul ((PUnit'.fact (by omega)).pow 3)).mul
      ((PUnit'.fact (by omega)).pow 3)).mul (PUnit'.fact (by omega))
  · exact (PUnit'.fact (by omega)).mul (PUnit'.fact (by omega))

/-- **Corollary.** For a prime `p > K + 3c + 1` the determinant is a `p`-adic unit. -/
theorem wilson_hankel_padic_unit {p : ℕ} [Fact p.Prime] (c K : ℕ) (hp : K + 3 * c + 1 < p) :
    PUnit' p (Matrix.of fun i j : Fin K =>
        lamB (Dp (2 * c + 1) ^ 3 * X ^ ((i : ℕ) + j))).det := by
  rw [wilson_hankel]
  have hm1 : PUnit' p (-1 : ℚ) := ⟨by norm_num, by simp⟩
  have hs : PUnit' p ((-1 : ℚ) ^ (c * K + K / 2)) := hm1.pow _
  have hA : PUnit' p (∏ n ∈ range ((K + 1) / 2), hPlus c n) := by
    refine prod_induction _ (PUnit' p) (fun a b ha hb => ha.mul hb) ⟨one_ne_zero, by simp⟩ ?_
    intro n hn
    have := mem_range.1 hn
    exact hPlus_unit (by omega)
  have hB : PUnit' p (∏ n ∈ range (K / 2), hMinus c n) := by
    refine prod_induction _ (PUnit' p) (fun a b ha hb => ha.mul hb) ⟨one_ne_zero, by simp⟩ ?_
    intro n hn
    have := mem_range.1 hn
    exact hMinus_unit (by omega)
  exact (hs.mul hA).mul hB

theorem wilson_hankel_padicNorm {p : ℕ} [Fact p.Prime] (c K : ℕ) (hp : K + 3 * c + 1 < p) :
    padicNorm p (Matrix.of fun i j : Fin K =>
        lamB (Dp (2 * c + 1) ^ 3 * X ^ ((i : ℕ) + j))).det = 1 := by
  have h := wilson_hankel_padic_unit (p := p) c K hp
  rw [padicNorm.eq_zpow_of_nonzero h.1, h.2]
  simp

/-- The sign-twisted Hankel determinant equals the plain one: `D A D` with `D = diag((−1)^i)`. -/
theorem hankel_sign_twist {R : Type*} [CommRing R] (K : ℕ) (h : ℕ → R) :
    (Matrix.of fun i j : Fin K => (-1 : R) ^ ((i : ℕ) + j) * h ((i : ℕ) + j)).det =
      (Matrix.of fun i j : Fin K => h ((i : ℕ) + j)).det := by
  set D : Matrix (Fin K) (Fin K) R := Matrix.diagonal fun i => (-1 : R) ^ (i : ℕ) with hD
  have hM : (Matrix.of fun i j : Fin K => (-1 : R) ^ ((i : ℕ) + j) * h ((i : ℕ) + j)) =
      D * (Matrix.of fun i j : Fin K => h ((i : ℕ) + j)) * D := by
    ext i j
    simp only [hD, Matrix.of_apply, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
      ite_mul, zero_mul, sum_ite_eq, sum_ite_eq', Finset.mem_univ, if_true, pow_add]
    ring
  have hd : D.det * D.det = 1 := by
    rw [hD, Matrix.det_diagonal, ← prod_mul_distrib]
    refine prod_eq_one fun i _ => ?_
    rw [← pow_add, ← two_mul, pow_mul]; simp
  rw [hM, Matrix.det_mul, Matrix.det_mul]
  linear_combination (Matrix.of fun i j : Fin K => h ((i : ℕ) + j)).det * hd

/-- The twisted determinant, in the form `φ(−x)` used downstream. -/
theorem wilson_hankel_twist (c K : ℕ) :
    (Matrix.of fun i j : Fin K =>
        (-1 : ℚ) ^ ((i : ℕ) + j) * lamB (Dp (2 * c + 1) ^ 3 * X ^ ((i : ℕ) + j))).det =
      (-1) ^ (c * K + K / 2) * (∏ n ∈ range ((K + 1) / 2), hPlus c n) *
        ∏ n ∈ range (K / 2), hMinus c n := by
  rw [hankel_sign_twist K (fun e => lamB (Dp (2 * c + 1) ^ 3 * X ^ e)), wilson_hankel]

/-- Regression instance: `c = 0`, `K = 2`: `det [[λ(x³), λ(x⁴)], [λ(x⁴), λ(x⁵)]] = −1/12`. -/
theorem wilson_hankel_c0_K2 :
    (Matrix.of fun i j : Fin 2 => lamB (Dp 1 ^ 3 * X ^ ((i : ℕ) + j))).det = -1 / 12 := by
  rw [show (1 : ℕ) = 2 * 0 + 1 from rfl, wilson_hankel]
  norm_num [hPlus, hMinus, Nat.factorial]

end CatalanCore.Lai.Wilson
