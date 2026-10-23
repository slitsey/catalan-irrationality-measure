module
public import CatalanCore.Arith.Hybrid.QuadraticResponseReindex
public import CatalanCore.Arith.Hybrid.UniformEntries
@[expose] public section
open Finset Matrix
namespace CatalanCore.Arith.Hybrid

section Generic
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- **Source completion** (generic algebra of `response_long_eq`).  If `Q` carries the commutator
identity and the border `b` the source identity of a Loewner source `(t, f, n, l)`, the inverse
quadratic response of the completed matrix on the vector `u` extended by `A - B l` equals the
response of `Q` on `u`, where `g = Q⁻¹ b`, `A = l - ∑ g f`, `B = 1 - ∑ g`, `u = A - B f`. -/
theorem response_source_completion (Q : Matrix ι ι K) (b t f : ι → K) (n l d : K)
    (hcomm : ∀ i j, n * (t i - t j) * Q i j = f j - f i)
    (hsource : ∀ i, n * t i * b i = l - f i)
    (hQ : IsUnit Q.det) (hC : IsUnit (sourceCompletion Q b d).det) :
    quadraticResponse (sourceCompletion Q b d)
        (Sum.elim (fun i => (l - ∑ k, (Q⁻¹ *ᵥ b) k * f k) - (1 - ∑ k, (Q⁻¹ *ᵥ b) k) * f i)
          (fun _ => (l - ∑ k, (Q⁻¹ *ᵥ b) k * f k) - (1 - ∑ k, (Q⁻¹ *ᵥ b) k) * l)) =
      quadraticResponse Q
        (fun i => (l - ∑ k, (Q⁻¹ *ᵥ b) k * f k) - (1 - ∑ k, (Q⁻¹ *ᵥ b) k) * f i) := by
  have hg : ∀ i, ∑ j, Q i j * (Q⁻¹ *ᵥ b) j = b i := by
    intro i
    have : Q *ᵥ (Q⁻¹ *ᵥ b) = b := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hQ, Matrix.one_mulVec]
    exact congrFun this i
  obtain ⟨hv, -⟩ := loewner_source_moment Q (Q⁻¹ *ᵥ b) b f t n l hg hcomm hsource
  have hs := loewner_source_extra (Q⁻¹ *ᵥ b) b f t n l hsource
  exact completion_quadraticResponse Q b _ (fun j => n * t j * (Q⁻¹ *ᵥ b) j) d _ hQ hC hv hs

end Generic
section Pole
open ChainClasses
variable {p o N : ℕ} [Fact p.Prime] {Fr : Frame}

/-- Exact commutator identity of the pole model: for nodes `a, b` with `b - a = m p`,
`n m poleScaledEntry a b = p (P b - P a)`. -/
theorem pole_comm (hn : Fr.norm ≠ 0) (a b : ℕ) (m : ℤ) (hm : (b:ℤ) - a = m * p) :
    Fr.norm * (m:ℚ) * poleScaledEntry Fr p o a b =
      (p:ℚ) * polePrefix Fr p o b - (p:ℚ) * polePrefix Fr p o a := by
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hmq : (b:ℚ) - a = m * p := by exact_mod_cast hm
  rcases lt_trichotomy a b with h | rfl | h
  · rw [poleScaledEntry_ordered h]
    have hm0 : (m:ℚ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hmq
      have : (a:ℚ) < b := by exact_mod_cast h
      linarith
    rw [hmq]; field_simp
  · have : (m:ℚ) = 0 := by
      have : (m:ℚ) * p = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hp0
    rw [this]; ring
  · rw [poleScaledEntry_symm a b, poleScaledEntry_ordered h]
    have hm0 : (m:ℚ) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hmq
      have : (b:ℚ) < a := by exact_mod_cast h
      linarith
    have : (a:ℚ) - b = -(m*p) := by linarith
    rw [this]
    field_simp
    ring

/-- `p · P(a)` is `p`-integral for `a < N`, `4N < p²`. -/
theorem p_polePrefix_mem (hL : LamData Fr o) (hN : 4 * N < p * p) {a : ℕ} (ha : a < N) :
    (p:ℚ) * polePrefix Fr p o a ∈ S p := by
  unfold polePrefix
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ ?_
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  have h1 := good_Delta_uniform hL hN hk'.1 (by omega)
  have h2 := (Good.natCast (ℓ := p) p).mul (good_regularDelta (p := p) (o:ℤ) (k:ℤ))
  have h3 := h1.sub h2
  unfold poleDelta
  rw [mul_sub]
  simpa using h3.mem

end Pole

#print axioms response_source_completion
end CatalanCore.Arith.Hybrid
