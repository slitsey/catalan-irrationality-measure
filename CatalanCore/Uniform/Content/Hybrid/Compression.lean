module

public import CatalanCore.Uniform.Content.Hybrid.Leading
public import CatalanCore.Uniform.Content.Hybrid.LoadKernel

@[expose] public section

/-!
# Compression of the cross matrix to the loads, and the local Loewner orthogonality

* `compress_entry` : for a left kernel vector `u` supported in the row fiber `ρ` and a right
  kernel vector `v` supported in the column fiber `σ`, the compressed Loewner cross entry is
  `Σ u_k (Lc_l - Lr_k)/(β_l - α_k) v_l = ω(load u, load v)/(σ - ρ)`, where
  `load u = (Σ u, Σ Lr·u)` (mass/pole load).  For `σ = ρ` both sides are `·/0 = 0`: this is the
  zero same-fiber block.
* `omega_load_eq_zero` : the displacement identity `(t_i - s_j) K_ij = Lr_i - Lc_j` on a fiber, with
  `u K = 0`, `K v = 0` there, forces `ω(load u, load v) = 0` (the left and right load spaces are
  alternating-orthogonal).
* `LeadingData.nextRed_eq_loadMat` : under the residue-fiber hypotheses the actual `M_next mod p`
  IS the load matrix of `LoadKernel`, over `𝔽_p(X)`.
-/

open Polynomial CatalanCore.Basic CatalanCore.Arith.Hybrid Finset

namespace CatalanCore.Uniform.Content.Hybrid

section Field

variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- Mass/pole load of a vector. -/
def load (Lw u : ι → F) : F × F := (∑ k, u k, ∑ k, Lw k * u k)

lemma omega_load (Lr Lc u v : ι → F) :
    omegaL (load Lr u) (load Lc v) = ∑ k, ∑ l, u k * v l * (Lc l - Lr k) := by
  rw [omegaL_apply]
  simp only [load, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem compress_entry (u v α β Lr Lc : ι → F) (ρ σ : F)
    (hu : ∀ k, u k ≠ 0 → α k = ρ) (hv : ∀ l, v l ≠ 0 → β l = σ) :
    ∑ k, ∑ l, u k * ((Lc l - Lr k) / (β l - α k)) * v l =
      omegaL (load Lr u) (load Lc v) / (σ - ρ) := by
  have hterm : ∀ k l, u k * ((Lc l - Lr k) / (β l - α k)) * v l =
      u k * v l * (Lc l - Lr k) / (σ - ρ) := by
    intro k l
    by_cases h1 : u k = 0
    · simp [h1]
    by_cases h2 : v l = 0
    · simp [h2]
    rw [hu k h1, hv l h2]; ring
  simp_rw [hterm, ← Finset.sum_div]
  rw [omega_load]

theorem omega_load_eq_zero (Kb : ι → ι → F) (α β t sd Lr Lc : ι → F) (ρ : F)
    (hdisp : ∀ i j, α i = ρ → β j = ρ → (t i - sd j) * Kb i j = Lr i - Lc j)
    (u v : ι → F) (hus : ∀ k, u k ≠ 0 → α k = ρ) (hvs : ∀ l, v l ≠ 0 → β l = ρ)
    (hu : ∀ j, β j = ρ → ∑ k, u k * Kb k j = 0) (hv : ∀ i, α i = ρ → ∑ l, Kb i l * v l = 0) :
    omegaL (load Lr u) (load Lc v) = 0 := by
  have hterm : ∀ k l, u k * v l * (Lc l - Lr k) =
      -(u k * t k * (Kb k l * v l)) + (sd l * v l) * (u k * Kb k l) := by
    intro k l
    by_cases h1 : u k = 0
    · simp [h1]
    by_cases h2 : v l = 0
    · simp [h2]
    have := hdisp k l (hus k h1) (hvs l h2)
    linear_combination (u k * v l) * this
  rw [omega_load]
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have h1 : ∑ k, ∑ l, u k * t k * (Kb k l * v l) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.mul_sum]
    by_cases h : u k = 0
    · simp [h]
    · rw [hv k (hus k h), mul_zero]
  have h2 : ∑ k, ∑ l, (sd l * v l) * (u k * Kb k l) = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← Finset.mul_sum]
    by_cases h : v l = 0
    · simp [h]
    · rw [hu l (hvs l h), mul_zero]
  rw [h1, h2, neg_zero, add_zero]

end Field

/-! ### Load matrices under a field homomorphism -/

lemma loadMat_map {F F' : Type*} [Field F] [Field F'] [DecidableEq F] [DecidableEq F']
    {R S : Type*} [Fintype R] [Fintype S] [DecidableEq R] [DecidableEq S]
    (f : F →+* F') (α : R → F) (x : R → F × F) (β : S → F) (y : S → F × F) :
    (loadMat α x β y).map f =
      loadMat (fun r => f (α r)) (fun r => ((f (x r).1, f (x r).2) : F' × F'))
        (fun c => f (β c)) (fun c => ((f (y c).1, f (y c).2) : F' × F')) := by
  ext r c
  simp only [loadMat, Matrix.map_apply, Matrix.of_apply, omegaL_apply, map_div₀, map_sub,
    map_mul]

/-! ### The actual next matrix is a load matrix -/

variable {p : ℕ} [Fact p.Prime]

/-- The constants `𝔽_p → 𝔽_p(X)` as a ring homomorphism. -/
noncomputable def rfH (p : ℕ) [Fact p.Prime] : ZMod p →+* RatFunc (ZMod p) :=
  (algebraMap (ZMod p)[X] (RatFunc (ZMod p))).comp Polynomial.C

lemma rfH_apply (a : ZMod p) : rfH p a = rfC p a := rfl

lemma rfH_injective : Function.Injective (rfH p) :=
  (RatFunc.algebraMap_injective (ZMod p)).comp Polynomial.C_injective

namespace LeadingData

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : Matrix ι ι ℚ[X]}

/-- Row loads of the exact left kernel vectors (rows of `L` in `s`), modulo `p`. -/
noncomputable def rowLoad (D : LeadingData p Φ) (Lr : ι → ZMod p) (i : D.s) : ZMod p × ZMod p :=
  load Lr (fun k => redQ p (D.L i k))

/-- Column loads of the exact right kernel vectors (columns of `P` in `s`), modulo `p`. -/
noncomputable def colLoad (D : LeadingData p Φ) (Lc : ι → ZMod p) (j : D.s) : ZMod p × ZMod p :=
  load Lc (fun l => redQ p (D.P l j))

/-- **Compression.** If `Cr mod p` is the Loewner cross matrix of the residues and pole loads
(zero on same-residue pairs automatically), and the exact kernel vectors are fiber-supported
modulo `p`, then `M_next mod p` is the image of the load matrix over `𝔽_p`. -/
theorem nextRed_eq_loadMat (D : LeadingData p Φ) (α β Lr Lc : ι → ZMod p)
    (hCr : ∀ i j, phiP p (D.Cr i j) = rfC p ((Lc j - Lr i) / (β j - α i)))
    (ρ σ : D.s → ZMod p)
    (hu : ∀ (i : D.s) k, redQ p (D.L i k) ≠ 0 → α k = ρ i)
    (hv : ∀ (j : D.s) l, redQ p (D.P l j) ≠ 0 → β l = σ j) :
    D.nextRed = (loadMat ρ (D.rowLoad Lr) σ (D.colLoad Lc)).map (rfH p) := by
  ext i j
  have he : D.nextRed i j = rfH p (∑ k, ∑ l, redQ p (D.L i k) *
      ((Lc l - Lr k) / (β l - α k)) * redQ p (D.P l j)) := by
    simp only [nextRed, next, nextFull, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
      map_sum, map_mul, phiP_C, hCr, ← rfH_apply]
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  rw [he, compress_entry _ _ α β Lr Lc (ρ i) (σ j) (hu i) (hv j)]
  rfl

end LeadingData

end CatalanCore.Uniform.Content.Hybrid
