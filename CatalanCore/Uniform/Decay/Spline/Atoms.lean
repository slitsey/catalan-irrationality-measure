module

public import CatalanCore.Uniform.Decay.Spline.Midpoint

@[expose] public section

/-!
# The midpoint atoms as a `Fin K`-indexed atomic measure (lane D, package D2)

`K = n * N`; atom `k` is cell `j` of piece `i` under `finProdFinEquiv`.  Basic facts used by the
bridge: reindexing of sums, exact mass, presentation total variation, radius, conjugation symmetry,
and `Irho = ∑ wt · Usig`.
-/

namespace CatalanCore.Uniform.Decay.Spline

open Finset intervalIntegral CatalanLambda.Decay

variable {n : ℕ}

/-- Atom positions, indexed by `Fin (n * N)`. -/
noncomputable def cK (A B : Fin n → ℂ) (N : ℕ) (k : Fin (n * N)) : ℂ :=
  cAt A B N (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- Atom weights, indexed by `Fin (n * N)`. -/
noncomputable def wK (f : Fin n → ℝ → ℝ) (N : ℕ) (k : Fin (n * N)) : ℝ :=
  wAt f N (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

theorem sum_K {N : ℕ} {M : Type*} [AddCommMonoid M] (g : Fin n × Fin N → M) :
    ∑ k : Fin (n * N), g (finProdFinEquiv.symm k) = ∑ i, ∑ j, g (i, j) := by
  rw [Equiv.sum_comp finProdFinEquiv.symm g, Fintype.sum_prod_type]

theorem usig_K (A B : Fin n → ℂ) (f : Fin n → ℝ → ℝ) (N : ℕ) (ρ : ℝ) (z : ℂ) :
    Usig ρ (cK A B N) (wK f N) z
      = ∑ i, ∑ j : Fin N, wAt f N i j * krho ρ z (cAt A B N i j) := by
  unfold Usig cK wK
  exact sum_K (fun x : Fin n × Fin N => wAt f N x.1 x.2 * krho ρ z (cAt A B N x.1 x.2))

theorem sum_wK (f : Fin n → ℝ → ℝ) (hf : ∀ i, Continuous (f i)) {N : ℕ} (hN : 0 < N) :
    ∑ k, wK f N k = ∑ i, ∫ t in (0 : ℝ)..1, f i t := by
  unfold wK
  rw [sum_K (fun x : Fin n × Fin N => wAt f N x.1 x.2)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact sum_cells (hf i) hN

theorem abs_sum_wK_le (f : Fin n → ℝ → ℝ) (hf : ∀ i, Continuous (f i)) {N : ℕ} (hN : 0 < N) :
    ∑ k, |wK f N k| ≤ ∑ i, ∫ t in (0 : ℝ)..1, |f i t| := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold wK
  rw [sum_K (fun x : Fin n × Fin N => |wAt f N x.1 x.2|)]
  refine Finset.sum_le_sum (fun i _ => ?_)
  rw [← sum_cells (hf i).abs hN]
  refine Finset.sum_le_sum (fun j _ => ?_)
  unfold wAt
  have hab : ((j : ℝ) / N) ≤ ((j : ℝ) + 1) / N :=
    div_le_div_of_nonneg_right (by linarith) hN'.le
  exact intervalIntegral.abs_integral_le_integral_abs hab

theorem norm_pt_le (A B : Fin n → ℂ) {Rc : ℝ} (hA : ∀ i, ‖A i‖ ≤ Rc) (hB : ∀ i, ‖B i‖ ≤ Rc)
    (i : Fin n) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : ‖pt A B i t‖ ≤ Rc := by
  have e : pt A B i t = ((1 - t : ℝ) : ℂ) * A i + (t : ℂ) * B i := by unfold pt; push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 1 - t), abs_of_nonneg h0]
  nlinarith [hA i, hB i, norm_nonneg (A i), norm_nonneg (B i)]

theorem norm_cK_le (A B : Fin n → ℂ) {Rc : ℝ} (hA : ∀ i, ‖A i‖ ≤ Rc) (hB : ∀ i, ‖B i‖ ≤ Rc)
    {N : ℕ} (hN : 0 < N) (k : Fin (n * N)) : ‖cK A B N k‖ ≤ Rc := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold cK cAt
  set j := (finProdFinEquiv.symm k).2
  have hj : (j : ℝ) + 1 ≤ N := by exact_mod_cast j.2
  refine norm_pt_le A B hA hB _ (by positivity) ?_
  rw [div_le_one hN']; linarith

/-! ### Conjugation symmetry -/

theorem krho_conj_left (ρ : ℝ) (s w : ℂ) :
    krho ρ ((starRingEnd ℂ) s) w = krho ρ s ((starRingEnd ℂ) w) := by
  unfold krho
  have : (starRingEnd ℂ) s - w = (starRingEnd ℂ) (s - (starRingEnd ℂ) w) := by simp
  rw [this, Complex.norm_conj]

theorem Usig_conj_of_involution {K : ℕ} (ρ : ℝ) (c : Fin K → ℂ) (m : Fin K → ℝ) (σ : Fin K → Fin K)
    (hinv : Function.Involutive σ) (hc : ∀ k, c (σ k) = (starRingEnd ℂ) (c k))
    (hm : ∀ k, m (σ k) = m k) (s : ℂ) :
    Usig ρ c m ((starRingEnd ℂ) s) = Usig ρ c m s := by
  unfold Usig
  have h : ∀ k, m k * krho ρ ((starRingEnd ℂ) s) (c k) = m (σ k) * krho ρ s (c (σ k)) := by
    intro k
    rw [hm, hc, krho_conj_left]
  simp_rw [h]
  exact Equiv.sum_comp (Function.Involutive.toPerm σ hinv) (fun j => m j * krho ρ s (c j))

theorem Irho_eq_sum {K : ℕ} (ρ : ℝ) (c : Fin K → ℂ) (m : Fin K → ℝ) :
    Irho ρ c m = ∑ k, m k * Usig ρ c m (c k) := by
  unfold Irho Usig
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

theorem pt_conj (A B : Fin n → ℂ) (τ : Fin n → Fin n)
    (hA : ∀ i, A (τ i) = (starRingEnd ℂ) (A i)) (hB : ∀ i, B (τ i) = (starRingEnd ℂ) (B i))
    (i : Fin n) (t : ℝ) : pt A B (τ i) t = (starRingEnd ℂ) (pt A B i t) := by
  unfold pt
  rw [hA, hB]
  simp [map_add, map_mul, map_sub, Complex.conj_ofReal]

/-- Conjugation symmetry of the atoms from a symmetry of the pieces. -/
theorem atoms_conj_symm (A B : Fin n → ℂ) (f : Fin n → ℝ → ℝ) (τ : Fin n → Fin n)
    (hτ : Function.Involutive τ) (hA : ∀ i, A (τ i) = (starRingEnd ℂ) (A i))
    (hB : ∀ i, B (τ i) = (starRingEnd ℂ) (B i)) (hf : ∀ i, f (τ i) = f i) (N : ℕ) :
    ∃ σ : Fin (n * N) → Fin (n * N), Function.Involutive σ ∧
      (∀ k, cK A B N (σ k) = (starRingEnd ℂ) (cK A B N k)) ∧ (∀ k, wK f N (σ k) = wK f N k) := by
  have hτ' : ∀ i, τ (τ i) = i := hτ
  refine ⟨fun k => finProdFinEquiv (τ (finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2),
    ?_, ?_, ?_⟩
  · intro k
    simp only [Equiv.symm_apply_apply, hτ', Prod.mk.eta, Equiv.apply_symm_apply]
  · intro k
    unfold cK cAt
    simp only [Equiv.symm_apply_apply]
    exact pt_conj A B τ hA hB _ _
  · intro k
    unfold wK wAt
    simp [hf]

end CatalanCore.Uniform.Decay.Spline
