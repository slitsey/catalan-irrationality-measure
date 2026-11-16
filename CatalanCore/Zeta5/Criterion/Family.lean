module

public import CatalanCore.Zeta5.Port.Source
public import CatalanCore.Zeta5.Criterion.RelNorm
public import CatalanCore.Zeta5.Criterion.Nearby

@[expose] public section

/-!
# Fauzan's family as a `PolyFamily`, and nearby non-vanishing (ledger ZA12, ZA13)

* `zeta5Family` (ZA12): `ι = ℕ`, `Q n = F_{40 n}` (the polynomial `F_K = S_K Δ_K` of
  `CatalanCore.Zeta5.Port.Construction`), `deg n = 37 n = h`, every `n` admissible, constant
  `ζ(5) = Apery.zeta5`.  The scale is `K = 40 n` (`zeta5Scale`).  The integral normaliser
  `m_{K,M}` is *not* part of `Q`: the content side supplies it as the `den` of
  `HasScaledContent zeta5Family zeta5Scale Λ` (so `Q n = F n` carries the pure decay `D`).
* The pencil `G_n(x) = Gmat n + (x - ζ(5)) Mmat n` of real matrices (`Mmat` = matrix of
  `X`-coefficients; all entries of `G_n` are affine in `X`).
* `RhoBound ρ` (ZR10 in quadratic-form form): `|vᵀ M v| ≤ e^{ρ K} vᵀ G v` for all large `n`.
* `zeta5_nearbyNV` (ZA13 instance): `RhoBound ρ ⇒ HasNearbyNV zeta5Family zeta5Scale ρ`, from
  `G_posDef` (ZA03) and `det_pencil_bounds` (ZA14).
-/

open Polynomial Matrix Apery CatalanCore CatalanCore.Uniform

namespace CatalanCore.Zeta5

/-- **ZA12.** Fauzan's family: `Q n = F_{40 n}`, degree `37 n`, constant `ζ(5)`. -/
noncomputable def zeta5Family : PolyFamily where
  const := Apery.zeta5
  ι := ℕ
  deg := fun n => 37 * n
  Adm := fun _ => True
  Q := fun n => Apery.F n

/-- The scale `K = 40 n`. -/
def zeta5Scale (n : ℕ) : ℕ := 40 * n

/-- The Gram matrix `G_{40n}(ζ(5))`. -/
noncomputable def Gmat (n : ℕ) : Matrix (Fin (37 * n)) (Fin (37 * n)) ℝ :=
  (Apery.G n).map (aeval Apery.zeta5)

/-- The matrix of `X`-coefficients of `G_{40n}(X)`, as a real matrix. -/
noncomputable def Mmat (n : ℕ) : Matrix (Fin (37 * n)) (Fin (37 * n)) ℝ :=
  Matrix.of fun i j => (((Apery.G n i j).coeff 1 : ℚ) : ℝ)

/-- **ZR10 (interface, quadratic-form form of `‖B_K‖ ≤ e^{ρ K}`)**: for all large `n` and all
`v`, `|vᵀ M_n v| ≤ exp(ρ · 40 n) · vᵀ G_n v`. -/
def RhoBound (ρ : ℝ) : Prop :=
  ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → ∀ v : Fin (37 * n) → ℝ,
    |v ⬝ᵥ (Mmat n *ᵥ v)| ≤ Real.exp (ρ * (40 * n : ℕ)) * (v ⬝ᵥ (Gmat n *ᵥ v))

lemma aeval_affine (p : ℚ[X]) (hp : p.natDegree ≤ 1) (x ξ : ℝ) :
    aeval x p = aeval ξ p + (x - ξ) * ((p.coeff 1 : ℚ) : ℝ) := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hp]
  simp only [map_add, map_mul, aeval_C, aeval_X, coeff_add, coeff_C_mul, coeff_X_one,
    coeff_C_succ, mul_one, add_zero]
  simp only [eq_ratCast]
  ring

lemma Mmat_symm (n : ℕ) : (Mmat n)ᵀ = Mmat n := by
  ext i j
  simp only [Mmat, Matrix.transpose_apply, Matrix.of_apply, Apery.G]
  rw [Nat.add_comm (j : ℕ) i]

lemma map_eval_G (n : ℕ) (x : ℝ) :
    (Apery.G n).map (aeval x) = Gmat n + (x - Apery.zeta5) • Mmat n := by
  ext i j
  simp only [Gmat, Mmat, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul]
  exact aeval_affine _ (natDegree_G_le n i j) x Apery.zeta5

lemma aeval_F_eq (n : ℕ) (x : ℝ) :
    aeval x (Apery.F n) = (S n : ℝ) * ((Apery.G n).map (aeval x)).det := by
  have hdet : aeval x (Δ n) = ((G n).map (aeval x)).det := by
    have := RingHom.map_det (aeval x : ℚ[X] →ₐ[ℚ] ℝ).toRingHom (G n)
    simpa [Δ, RingHom.mapMatrix_apply] using this
  unfold Apery.F
  rw [map_mul, aeval_C, hdet]
  simp [eq_ratCast]

/-- **ZA14 consequence for the family** (the form of ZR11): if `|x - ζ| · e^{ρ K} · 37 n ≤ 1/2`
and `RhoBound` holds at `n`, then `0 < F_n(x) ≤ 2 F_n(ζ)`. -/
theorem F_pencil_bounds (n : ℕ) (ρ : ℝ)
    (hρ : ∀ v : Fin (37 * n) → ℝ,
      |v ⬝ᵥ (Mmat n *ᵥ v)| ≤ Real.exp (ρ * (40 * n : ℕ)) * (v ⬝ᵥ (Gmat n *ᵥ v)))
    (x : ℝ)
    (hx : |x - Apery.zeta5| * Real.exp (ρ * (40 * n : ℕ)) * ((37 * n : ℕ) : ℝ) ≤ 1 / 2) :
    0 < aeval x (Apery.F n) ∧ aeval x (Apery.F n) ≤ 2 * aeval Apery.zeta5 (Apery.F n) := by
  have hb := det_pencil_bounds (Gmat n) (Mmat n) (G_posDef n) (Mmat_symm n)
    (Real.exp (ρ * (40 * n : ℕ))) (x - Apery.zeta5) hρ hx
  rw [← map_eval_G] at hb
  have hS : (0 : ℝ) < (S n : ℝ) := by exact_mod_cast S_pos n
  rw [aeval_F_eq n x, aeval_F_eq n Apery.zeta5]
  have hz : (Apery.G n).map (aeval Apery.zeta5) = Gmat n := rfl
  rw [hz]
  refine ⟨mul_pos hS hb.1, ?_⟩
  nlinarith [hb.2]

/-- Elementary: `74 n ≤ exp (40 ε n)` once `n ≥ 74 / (800 ε²)`. -/
lemma linear_le_exp (ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : 74 / (800 * ε ^ 2) ≤ n) :
    (74 : ℝ) * n ≤ Real.exp (40 * ε * n) := by
  have hy : 0 ≤ 40 * ε * n := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hy
  have h1 : 74 ≤ 800 * ε ^ 2 * (n : ℝ) := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 800 * ε ^ 2)).mp hn
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_right h1 hn0]

/-- The scale threshold after which the window `|x - ζ| ≤ e^{-(ρ+ε)K}` is inside the radius of
`F_pencil_bounds`. -/
noncomputable def winN (ε : ℝ) : ℕ := ⌈74 / (800 * ε ^ 2)⌉₊ + 1

/-- The window estimate: `|δ| ≤ exp(-(ρ+ε) 40 n)` and `n ≥ winN ε` give
`|δ| · e^{ρ 40 n} · 37 n ≤ 1/2`. -/
lemma window_bound (ρ ε : ℝ) (hε : 0 < ε) (n : ℕ) (hn : winN ε ≤ n) (δ : ℝ)
    (hδ : |δ| ≤ Real.exp (-(ρ + ε) * ((40 * n : ℕ) : ℝ))) :
    |δ| * Real.exp (ρ * (40 * n : ℕ)) * ((37 * n : ℕ) : ℝ) ≤ 1 / 2 := by
  have hnc : 74 / (800 * ε ^ 2) ≤ (n : ℝ) := by
    have h1 : ⌈74 / (800 * ε ^ 2)⌉₊ ≤ n := by unfold winN at hn; omega
    exact (Nat.le_ceil _).trans (by exact_mod_cast h1)
  have hlin := linear_le_exp ε hε n hnc
  have hexp1 : Real.exp (-(ρ + ε) * ((40 * n : ℕ) : ℝ)) * Real.exp (ρ * (40 * n : ℕ)) =
      Real.exp (-(40 * ε * n)) := by
    rw [← Real.exp_add]; push_cast; congr 1; ring
  have hpos := Real.exp_pos (ρ * (40 * n : ℕ))
  have h2 : |δ| * Real.exp (ρ * (40 * n : ℕ)) ≤ Real.exp (-(40 * ε * n)) := by
    rw [← hexp1]; exact mul_le_mul_of_nonneg_right hδ hpos.le
  have h3 : Real.exp (-(40 * ε * n)) * (74 * n) ≤ 1 := by
    rw [Real.exp_neg]
    have := Real.exp_pos (40 * ε * n)
    rw [inv_mul_le_iff₀ this]; linarith
  have h4 : ((37 * n : ℕ) : ℝ) = 37 * n := by push_cast; ring
  rw [h4]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ 37 * n)]

/-- **ZA13 (instance).**  Positive definiteness of the Gram matrix and the relative-norm bound
give non-vanishing of `F_n` near `ζ(5)`. -/
theorem zeta5_nearbyNV {ρ : ℝ} (hρ : RhoBound ρ) :
    HasNearbyNV zeta5Family zeta5Scale ρ := by
  obtain ⟨N0, hN0⟩ := hρ
  intro ε hε
  refine ⟨40 * (N0 + winN ε), fun (n : ℕ) _ hr x hx => ?_⟩
  have hn : N0 + winN ε ≤ n := by unfold zeta5Scale at hr; omega
  have hnN0 : N0 ≤ n := le_trans (Nat.le_add_right _ _) hn
  have hnw : winN ε ≤ n := le_trans (Nat.le_add_left _ _) hn
  have hx0 : |Apery.zeta5 - (x : ℝ)| ≤ Real.exp (-(ρ + ε) * ((zeta5Scale n : ℕ) : ℝ)) := hx
  have hx' : |(x : ℝ) - Apery.zeta5| ≤ Real.exp (-(ρ + ε) * ((40 * n : ℕ) : ℝ)) := by
    rw [abs_sub_comm]; exact hx0
  have hprod := window_bound ρ ε hε n hnw _ hx'
  have hb := F_pencil_bounds n ρ (hN0 n hnN0) (x : ℝ) hprod
  have hcast : ((zeta5Family.evalQ n x : ℚ) : ℝ) = aeval (x : ℝ) (Apery.F n) :=
    (CatalanCore.Measure.evalR_cast zeta5Family n x).symm
  intro h0
  have : ((zeta5Family.evalQ n x : ℚ) : ℝ) = 0 := by rw [h0]; simp
  rw [hcast] at this
  exact hb.1.ne' this

end CatalanCore.Zeta5
