module

public import CatalanCore.Uniform.Content.UFMember.FullJ
public import CatalanCore.Arith.Hybrid.SchurDisplacement

@[expose] public section

/-!
# UF member package: the displacement form of the border Schur complement

The scaled lift satisfies the Loewner commutator relations exactly over `ℤ_(p)[X]`:

  `norm · (b - a) · p² Mn(a, b) = p² F(b) - p² F(a)`,  `F(a) = Σ_{0<k≤a} Δ_k`

(the core diagonal `X` is multiplied by `0`).  So the accepted `schur_displacement` applies to the
lift, and the cleared border Schur complement is a rank-two Cauchy-like matrix
(`sLift_displacement`):

  `g · norm · (y - z) · Sch_{zy} = α_z β'_y - β_z α'_y`,   `g = det Q`,

with ONE-NODE moments `α_z = g - (S' adj Q 1)_z`, `β_z = g P_z - (S' adj Q P)_z` (border rows) and
`α'_y`, `β'_y` (border columns).

`JBlockCauchy.of_moments` then reduces the remaining obligation (S7) on `J × J` to a statement
about these moments: `p² ∣ α_z β'_y - β_z α'_y` with quotient `≡ g · m_z m'_y (h(y) - h(z))`,
`h(t) = Σ_{c ∈ Ret} v(c)/(c - t)` (the derived frame).  The `J`-block of `W` is then
`p · Hc` with `Hc ≡ (m_z/norm) m'_y Σ_{c∈Ret} v(c)/((c-z)(c-y))` (`loewner_of_loads`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Rect CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.UFMember

/-- The prefix `F(a) = Σ_{0<k≤a} Δ_k`. -/
def Fp (Fr : Frame) (a : ℕ) : ℚ := ∑ k ∈ Ioc 0 a, Fr.Delta k

/-- The Loewner commutator relation of the frame entries. -/
theorem norm_mul_Mn (Fr : Frame) (a b : ℕ) :
    Fr.norm * ((b : ℚ) - a) * Fr.Mn a b = Fp Fr b - Fp Fr a := by
  have hn : Fr.norm ≠ 0 := Fr.hnorm.ne'
  rcases lt_trichotomy a b with h | rfl | h
  · have hs : Fp Fr b = Fp Fr a + ∑ k ∈ Ioc a b, Fr.Delta k := by
      unfold Fp
      rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le a) h.le]
    have hba : ((b : ℚ) - a) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h.ne')
    rw [Frame.Mn, if_neg h.ne, max_eq_right h.le, min_eq_left h.le, hs]
    field_simp
    ring
  · simp
  · have hs : Fp Fr a = Fp Fr b + ∑ k ∈ Ioc b a, Fr.Delta k := by
      unfold Fp
      rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le b) h.le]
    have hab : ((a : ℚ) - b) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h.ne')
    rw [Frame.Mn, if_neg h.ne', max_eq_left h.le, min_eq_right h.le, hs]
    field_simp
    ring

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- `p² F(a)` is `p`-integral below `N`. -/
theorem sq_Fp_mem (D : PoleData Fr p N) {a : ℕ} (ha : a < N) :
    (p : ℚ) ^ 2 * Fp Fr a ∈ LocRing p := by
  have h : (p : ℚ) * Fp Fr a ∈ LocRing p := by
    unfold Fp
    rw [Finset.mul_sum]
    exact Subring.sum_mem _ fun k hk => by
      obtain ⟨hk1, hk2⟩ := Finset.mem_Ioc.1 hk
      exact D.delta_mem k (by omega) (by omega)
  have e : (p : ℚ) ^ 2 * Fp Fr a = (p : ℚ) * ((p : ℚ) * Fp Fr a) := by ring
  rw [e]
  exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (p : ℤ)) h

/-- The lifted prefix value `p² F(a)` (junk `0` above `N`). -/
noncomputable def PF (p : ℕ) [Fact p.Prime] (Fr : Frame) (a : ℕ) : (LocRing p)[X] :=
  Polynomial.C (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fp Fr a))

/-- The lifted norm. -/
noncomputable def nL (p : ℕ) [Fact p.Prime] (Fr : Frame) : (LocRing p)[X] :=
  Polynomial.C (Hybrid.liftQ p Fr.norm)

/-- A node value in `ℤ_(p)[X]`. -/
noncomputable def nd (p : ℕ) [Fact p.Prime] (a : ℕ) : (LocRing p)[X] :=
  Polynomial.C ((a : ℕ) : LocRing p)

/-- The commutator relation for one constant entry of the lift. -/
theorem const_commutator (D : PoleData Fr p N) {a b : ℕ} (ha : a < N) (hb : b < N)
    (h2 : (p : ℚ) ^ 2 * Fr.Mn a b ∈ LocRing p) :
    nL p Fr * (nd p b - nd p a) * Polynomial.C (⟨(p : ℚ) ^ 2 * Fr.Mn a b, h2⟩ : LocRing p) =
      PF p Fr b - PF p Fr a := by
  have hn : Fr.norm ∈ LocRing p := D.norm_mem
  unfold nL nd PF
  rw [← C_sub, ← C_mul, ← C_mul, ← C_sub]
  congr 1
  apply Subtype.ext
  push_cast
  rw [Hybrid.liftQ_val (show Fr.norm ∈ S p from hn),
    Hybrid.liftQ_val (show (p : ℚ) ^ 2 * Fp Fr b ∈ S p from sq_Fp_mem D hb),
    Hybrid.liftQ_val (show (p : ℚ) ^ 2 * Fp Fr a ∈ S p from sq_Fp_mem D ha)]
  have := norm_mul_Mn Fr a b
  linear_combination (p : ℚ) ^ 2 * this

/-- **Displacement identity of the scaled border Schur complement.** -/
theorem sLift_displacement (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
    (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N) (z y : κ) :
    let A := sLift c xs ys (hint_of_poleData D hN hc hx hy)
    let g := A.toBlocks₁₁.det
    let Nq := A.toBlocks₁₁.adjugate
    g * (nL p Fr * (nd p (ys y) - nd p (xs z))) *
        (g • A.toBlocks₂₂ - A.toBlocks₂₁ * Nq * A.toBlocks₁₂) z y =
      (g - ∑ i, A.toBlocks₂₁ z i * ∑ k, Nq i k) *
          (g * PF p Fr (ys y) - ∑ j, (∑ k, PF p Fr (c k) * Nq k j) * A.toBlocks₁₂ j y) -
        (g * PF p Fr (xs z) - ∑ i, A.toBlocks₂₁ z i * ∑ k, Nq i k * PF p Fr (c k)) *
          (g - ∑ j, (∑ k, Nq k j) * A.toBlocks₁₂ j y) := by
  intro A g Nq
  have hint := hint_of_poleData D hN hc hx hy
  have hQ : ∀ i j, nL p Fr * (nd p (c j) - nd p (c i)) * A.toBlocks₁₁ i j =
      PF p Fr (c j) - PF p Fr (c i) := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · have e : A.toBlocks₁₁ i j = Polynomial.C (sConst c xs ys hint (Sum.inl i) (Sum.inl j)) := by
        simp [A, sLift, Matrix.toBlocks₁₁, Matrix.one_apply_ne hij]
      rw [e]
      exact const_commutator D (hc i) (hc j) _
  have hB : ∀ i j, nL p Fr * (nd p (ys j) - nd p (c i)) * A.toBlocks₁₂ i j =
      PF p Fr (ys j) - PF p Fr (c i) := by
    intro i j
    have e : A.toBlocks₁₂ i j = Polynomial.C (sConst c xs ys hint (Sum.inl i) (Sum.inr j)) := by
      simp [A, sLift, Matrix.toBlocks₁₂]
    rw [e]
    exact const_commutator D (hc i) (hy j) _
  have hC : ∀ i j, nL p Fr * (nd p (c j) - nd p (xs i)) * A.toBlocks₂₁ i j =
      PF p Fr (c j) - PF p Fr (xs i) := by
    intro i j
    have e : A.toBlocks₂₁ i j = Polynomial.C (sConst c xs ys hint (Sum.inr i) (Sum.inl j)) := by
      simp [A, sLift, Matrix.toBlocks₂₁]
    rw [e]
    exact const_commutator D (hx i) (hc j) _
  have hD : ∀ i j, nL p Fr * (nd p (ys j) - nd p (xs i)) * A.toBlocks₂₂ i j =
      PF p Fr (ys j) - PF p Fr (xs i) := by
    intro i j
    have e : A.toBlocks₂₂ i j = Polynomial.C (sConst c xs ys hint (Sum.inr i) (Sum.inr j)) := by
      simp [A, sLift, Matrix.toBlocks₂₂]
    rw [e]
    exact const_commutator D (hx i) (hy j) _
  have h := schur_displacement A.toBlocks₁₁ Nq A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂ g
    (nL p Fr) (Matrix.mul_adjugate _) (Matrix.adjugate_mul _) (fun i => nd p (c i))
    (fun i => PF p Fr (c i)) (fun i => nd p (xs i)) (fun i => PF p Fr (xs i))
    (fun j => nd p (ys j)) (fun j => PF p Fr (ys j)) hQ hB hC hD z y
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact h

end CatalanCore.Uniform.Content.UFMember
