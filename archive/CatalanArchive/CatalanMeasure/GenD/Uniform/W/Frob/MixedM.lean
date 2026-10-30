module
public import CatalanMeasure.GenD.Uniform.W.Families
public import CatalanMeasure.GenD.Uniform.W.Combine
@[expose] public section
set_option Elab.async false

/-!
# Theorem M (mixed 3-dimensional construction) as a Theorem W instance

UNIFIED-COUNTING-THEOREM, Theorem U with `k = 2`, `k2 = 1`, `n_C = 2`, `n_mix = 2`.  The matrix
`Γ_J(τ^i)[4]` (`J = 1,2`; `i = 0,1`) is the fixed rational matrix `gammaQ`, of
determinant `-1291/96`.  Hence `rank Γ = 2` for every prime `p ∉ {2, 3, 1291}`
(`gammaQ_rank`, one fixed minor via `rat_minor_rank`) and

  `ν ≥ min(gN, (n-g)N - 2p - 1) - (H - 3p - h)_+`   (`theorem_M_bound`).

The atom map `ι` (the construction `Hplus(Λ_s)Λ(τ) + Δ S(y) Λ'(τ)`), its injectivity and the raw
killing are the instance data of `MixedMData`: they come from G2 (tiling index ↔ G row,
`RawKilled`) and are hypotheses here.
-/

namespace CatalanMeasure.GenD.Uniform.W
open Module Matrix CatalanMeasure.Parametric CatalanMeasure.GenD
noncomputable section

/-- The rational matrix `[Γ_J(τ^i)[4]]`, rows `J = 1,2`, columns `τ^0, τ^1`. -/
def gammaQ : Matrix (Fin 2) (Fin 2) ℚ := !![-43/24, 49/24; 1/24, 179/24]

theorem gammaQ_det : gammaQ.det = -1291 / 96 := by
  rw [Matrix.det_fin_two]
  simp [gammaQ]
  norm_num

theorem gammaQ_den (i j : Fin 2) : (gammaQ i j).den = 24 := by
  fin_cases i <;> fin_cases j <;> simp [gammaQ] <;> decide +kernel

theorem gammaQ_det_num : (gammaQ.det).num = -1291 := by
  rw [gammaQ_det]
  decide +kernel

section
variable {p : ℕ} [Fact p.Prime]

theorem gammaQ_rank (h2 : p ≠ 2) (h3 : p ≠ 3) (h1291 : p ≠ 1291) :
    2 ≤ (residueMat p gammaQ).rank := by
  have hp := Fact.out (p := p.Prime)
  refine rat_minor_rank gammaQ (fun i => i) (fun j => j) ?_ ?_
  · intro i j
    rw [gammaQ_den, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have h24 : p ∣ 2 ^ 3 * 3 := by norm_num; exact hd
    rcases (Nat.Prime.dvd_mul hp).mp h24 with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h)
  · show ¬ (p : ℤ) ∣ (gammaQ.det).num
    rw [gammaQ_det_num]
    intro hd
    have : p ∣ 1291 := by
      have := Int.natCast_dvd.mp hd
      simpa using this
    exact h1291 ((Nat.prime_dvd_prime_iff_eq hp (by decide +kernel : Nat.Prime 1291)).mp this)

end

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Instance data of Theorem M: the conditions `α, β, Γ` (with `Γ` the residue of `gammaQ`),
the dimension `m` of the free polynomial space, and the atom map on `Π ⊗ V`. -/
structure MixedMData (P : Parameters) (N p : ℕ) [Fact p.Prime] (m : ℕ) where
  α : (Fin 3 → ZMod p) →ₗ[ZMod p] (Fin 2 → ZMod p)
  β : (Fin 3 → ZMod p) →ₗ[ZMod p] (Fin 2 → ZMod p)
  Γ : (Fin 2 → ZMod p) →ₗ[ZMod p] (Fin 2 → ZMod p)
  hΓ : Γ = (residueMat p gammaQ).mulVecLin
  ι : ∀ V : Submodule (ZMod p) ((Fin 3 → ZMod p) × (Fin 2 → ZMod p)),
    (Fin m → V) →ₗ[ZMod p] (Fin (P.n N) → ZMod p)
  inj : ∀ V, V ≤ LinearMap.ker (mixedMap α β Γ) →
    Function.Injective ((LinearMap.fst (ZMod p) (Fin 3 → ZMod p) (Fin 2 → ZMod p)).comp
      V.subtype) → Function.Injective (ι V)
  killed : ∀ V, V ≤ LinearMap.ker (mixedMap α β Γ) → ∀ x, RawKilled P N p (ι V x)

/-- **Theorem M, abstract count.** For `p ∉ {2,3,1291}`, `ν ≥ m`. -/
theorem theorem_M_nullity (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp1291 : p ≠ 1291)
    (hH : P.H N < p ^ 2) {m : ℕ} (D : MixedMData P N p m) : m ≤ nullity P N p := by
  have h := w_mixed hp2 hH D.α D.β D.Γ D.ι D.inj D.killed
  have hr : finrank (ZMod p) (LinearMap.range D.Γ) = (residueMat p gammaQ).rank := by
    rw [D.hΓ]
    rfl
  have h2 := gammaQ_rank (p := p) hp2 hp3 hp1291
  rw [hr, Module.finrank_fin_fun] at h
  have e : 3 - 2 - (2 - (residueMat p gammaQ).rank) = 1 := by omega
  rw [e, Nat.mul_one] at h
  exact h

/-- The closed form of Theorem M:
`min(gN, (n-g)N - 2p - 1) - (H - 3p - h)_+` (natural subtraction is the positive part). -/
def mCount (P : Parameters) (N p : ℕ) : ℕ :=
  min (P.g N) (P.n N - P.g N - 2 * p - 1) - (P.H N - 3 * p - P.h N)

/-- **Theorem M.** -/
theorem theorem_M_bound (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp1291 : p ≠ 1291)
    (hH : P.H N < p ^ 2) (D : MixedMData P N p (mCount P N p)) :
    mCount P N p ≤ nullity P N p :=
  theorem_M_nullity hp2 hp3 hp1291 hH D

/-- Banking for Theorem M on a window `App` where the data exists. -/
def theoremMLB (P : Parameters) (App : ℕ → ℕ → Prop)
    (h : ∀ N p : ℕ, 0 < N → ∀ hp : p.Prime, p ≠ 2 → P.H N < p ^ 2 → App N p →
      p ≠ 3 ∧ p ≠ 1291 ∧
      haveI : Fact p.Prime := ⟨hp⟩
      Nonempty (MixedMData P N p (mCount P N p))) : NullityLB P :=
  NullityLB.ofWindow P App (mCount P) fun N p hN hp hp2 hH hA => by
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨h3, h1, ⟨D⟩⟩ := h N p hN hp hp2 hH hA
    exact theorem_M_bound hp2 h3 h1 hH D

end
end CatalanMeasure.GenD.Uniform.W
