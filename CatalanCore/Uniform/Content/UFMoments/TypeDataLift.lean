module

public import CatalanCore.Uniform.Content.UFMoments.TypeDataShift

@[expose] public section

/-!
# UF moments: `TypeData` for shifted nodes of the scaled lift

`typeData_of_shift`: for the scaled lift `A`, a representative node `t₀` with Loewner border vector
`σ₀`, and a node `t₀ + Δ` with Loewner border vector `σ`, a chain equivalence
`e` with `c(e⁻¹ i) = c(i) + Δ` and nonsingular windows `(a, a + Δ]` at `t₀` and its chain give
`TypeData` (with `κ₁ = (F(t₀+Δ) - F(t₀))/norm`), once the residue of `κ₁` has the Cauchy form
`hres` (step identity, frame-specific).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMoments

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

section
variable (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
  (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)

theorem sConst_eq_liftQ (u v : ι ⊕ κ) :
    sConst c xs ys (hint_of_poleData D hN hc hx hy) u v =
      Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn (rowNode c xs u) (colNode c ys v)) := by
  apply Subtype.ext
  rw [Hybrid.liftQ_val (hint_of_poleData D hN hc hx hy u v)]
  rfl

theorem sLift_core_entry (a b : ι) :
    (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ a b =
      Polynomial.C (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn (c a) (c b))) +
        (if a = b then (X : (LocRing p)[X]) else 0) := by
  have h := sConst_eq_liftQ D hN c xs ys hc hx hy (Sum.inl a) (Sum.inl b)
  simp only [rowNode, colNode, Sum.elim_inl] at h
  by_cases hab : a = b
  · subst hab
    simp [sLift, Matrix.toBlocks₁₁, h]
  · simp [sLift, Matrix.toBlocks₁₁, h, hab, Matrix.one_apply_ne hab]

theorem sLift_row_entry (z : κ) (a : ι) :
    (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₂₁ z a =
      Polynomial.C (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn (xs z) (c a))) := by
  have h := sConst_eq_liftQ D hN c xs ys hc hx hy (Sum.inr z) (Sum.inl a)
  simp only [rowNode, colNode, Sum.elim_inl, Sum.elim_inr] at h
  simp [sLift, Matrix.toBlocks₂₁, h]

theorem sLift_col_entry (a : ι) (y : κ) :
    (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₂ a y =
      Polynomial.C (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn (ys y) (c a))) := by
  have h := sConst_eq_liftQ D hN c xs ys hc hx hy (Sum.inl a) (Sum.inr y)
  simp only [rowNode, colNode, Sum.elim_inl, Sum.elim_inr] at h
  rw [frame_Mn_symm Fr (ys y)]
  simp [sLift, Matrix.toBlocks₁₂, h]

/-- **`TypeData` of a shifted node.** -/
theorem typeData_of_shift (hR : RegRed D) (t0 Δ : ℕ) (σ0 σ : ι → (LocRing p)[X])
    (hσ0 : ∀ a, σ0 a = Polynomial.C (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn t0 (c a))))
    (hσ : ∀ a, σ a = Polynomial.C (Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn (t0 + Δ) (c a))))
    (e : {a // colOf (p := p) c a = ((t0 + Δ : ℕ) : ZMod p)} ≃
      {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)})
    (hce : ∀ i, c (e.symm i).1 = c i.1 + Δ)
    (hwc : ∀ i : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, NoSingWin D (c i.1) Δ)
    (hwt : NoSingWin D t0 Δ) (hbt : t0 + Δ < N)
    (K0 : RatFunc (ZMod p)) (W : ZMod p → RatFunc (ZMod p))
    (hres : rfH p (red p (Fp Fr (t0 + Δ) - Fp Fr t0)) * (rfH p (red p Fr.norm))⁻¹ =
      K0 + ∑ c' : ZMod p, W c' * rfH p (c' - ((t0 + Δ : ℕ) : ZMod p))⁻¹) :
    TypeData Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ t0 σ0 K0 W
      (t0 + Δ) σ := by
  have hbc : ∀ i : {a // colOf (p := p) c a = ((t0 : ℕ) : ZMod p)}, c i.1 + Δ < N := by
    intro i; rw [← hce i]; exact hc _
  refine ⟨e, _, ?_, ?_, ?_, ellL_kappa D t0 Δ hbt hwt, ?_⟩
  · intro i j
    have hij : ((e.symm i).1 = (e.symm j).1) ↔ (i.1 = j.1) := by
      constructor
      · intro h; exact congrArg Subtype.val (e.symm.injective (Subtype.ext h))
      · intro h; rw [Subtype.ext h]
    have hcol : ((c i.1 : ℕ) : ZMod p) = ((c j.1 : ℕ) : ZMod p) := i.2.trans j.2.symm
    obtain ⟨x, hx'⟩ := loewner_entry_shift D hR hN (c i.1) (c j.1) Δ hcol (hbc i) (hbc j)
      (hwc i) (hwc j)
    refine ⟨x, ?_⟩
    rw [sLift_core_entry D hN c xs ys hc hx hy, sLift_core_entry D hN c xs ys hc hx hy, hce, hce,
      map_add, map_add, hx']
    by_cases h : i.1 = j.1
    · rw [if_pos (hij.2 h), if_pos h]; ring
    · rw [if_neg (fun h' => h (hij.1 h')), if_neg h]; ring
  · intro i
    have hcol : ((t0 : ℕ) : ZMod p) = ((c i.1 : ℕ) : ZMod p) := i.2.symm
    obtain ⟨x, hx'⟩ := loewner_entry_shift D hR hN t0 (c i.1) Δ hcol hbt (hbc i) hwt (hwc i)
    exact ⟨x, by rw [hσ, hσ0, hce, hx']⟩
  · intro i
    rw [hce]
    exact ellL_shift D hR (c i.1) t0 Δ i.2 (hbc i) hbt (hwc i) hwt
  · rw [res_kappa D t0 Δ hbt hwt]
    exact hres

end

end CatalanCore.Uniform.Content.UFMoments
