module

public import CatalanCore.Uniform.Content.Sweep.Classes

@[expose] public section

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep.Gen

/-!
# The pivot block `Q` of the sweep is invertible (lane H, wave H2b; ledger P204)

`PLANE2-P1-ROW` §1: `Q = p³ H[𝒫_r, 𝒫_c]` is congruent modulo `p` to the direct sum over the residues `ω`
of the class matrices `B^h_{o(ω)}`.  The pivot index set is `Ω = Fin p × (Fin κ ⊕ Fin k')`: the pair
`(ω, a)` is the pivot row of period `rowPer (o ω) a` and the pivot column of period `colPer (o ω) a` in the
residue class `ω`, where `o ω = oc p κ π ω` is the orientation of `ω`.

* `Qp`: the pivot block over `R` (entries `Qent ξ`).
* `Qp_congr`, `Qp_noncong`: the entries of the same residue are the class matrix entries (F1), the
  others are divisible by `p` (F2).
* `isUnit_det_Qp`: `det Qp` is a unit of `R` under `UnitProp` and `PRad` (`∀ x, IsUnit (1 + p x)`),
  hence `Qp` has an inverse (`Qp_mul_inv`, `Qp_inv_mul`).
-/
namespace CatalanCore.Uniform.Content.Sweep

section Piv

/-- The pivot index: a residue class `ω` and a period slot. -/
abbrev PivIdx (p κ k' : ℕ) := Fin p × (Fin κ ⊕ Fin k')

variable (p κ k' π : ℕ)

/-- The node of the pivot row `(ω, a)`. -/
def rowNode (x : PivIdx p κ k') : ℕ := rowPer κ k' (oc p κ π x.1) x.2 * p + x.1
/-- The node of the pivot column `(ω, a)`. -/
def colNode (x : PivIdx p κ k') : ℕ := colPer κ k' (oc p κ π x.1) x.2 * p + x.1

variable {p κ k' π}

theorem oc_le (ω : ℕ) : oc p κ π ω ≤ 1 := by
  rcases oc_cases p κ π ω with h | h <;> omega

theorem rowNode_mod (x : PivIdx p κ k') : rowNode p κ k' π x % p = x.1 := by
  unfold rowNode; rw [node_mod x.1.2]

theorem colNode_mod (x : PivIdx p κ k') : colNode p κ k' π x % p = x.1 := by
  unfold colNode; rw [node_mod x.1.2]

theorem rowNode_div (hp0 : 0 < p) (x : PivIdx p κ k') :
    rowNode p κ k' π x / p = rowPer κ k' (oc p κ π x.1) x.2 := by
  unfold rowNode; rw [node_div hp0 x.1.2]

theorem colNode_div (hp0 : 0 < p) (x : PivIdx p κ k') :
    colNode p κ k' π x / p = colPer κ k' (oc p κ π x.1) x.2 := by
  unfold colNode; rw [node_div hp0 x.1.2]

theorem rowPer_injective (o : ℕ) : Function.Injective (rowPer κ k' o) := by
  intro a b hab
  rcases a with a | i <;> rcases b with b | j <;> simp [rowPer] at hab
  · exact congrArg Sum.inl (Fin.ext hab)
  · have := a.2; omega
  · have := b.2; omega
  · exact congrArg Sum.inr (Fin.ext (by omega))

theorem rowPer_lt (o : ℕ) (ho : o ≤ 1) (a : Fin κ ⊕ Fin k') : rowPer κ k' o a < κ + 2 * k' :=
  ((mem_Cper (κ := κ) (k' := k')).1 (rowPer_mem κ k' o ho a)).1

theorem colPer_lt (o : ℕ) (ho : o ≤ 1) (a : Fin κ ⊕ Fin k') : colPer κ k' o a < κ + 2 * k' :=
  ((mem_Cper (κ := κ) (k' := k')).1 (colPer_mem κ k' o ho a)).1

theorem rowNode_lt {N : ℕ} (hH : (κ + 2 * k') * p ≤ N) (x : PivIdx p κ k') : rowNode p κ k' π x < N := by
  unfold rowNode
  have h1 := rowPer_lt (κ := κ) (k' := k') _ (oc_le (π := π) (κ := κ) (p := p) x.1) x.2
  have h2 := x.1.2
  nlinarith

theorem colNode_lt {N : ℕ} (hH : (κ + 2 * k') * p ≤ N) (x : PivIdx p κ k') : colNode p κ k' π x < N := by
  unfold colNode
  have h1 := colPer_lt (κ := κ) (k' := k') _ (oc_le (π := π) (κ := κ) (p := p) x.1) x.2
  have h2 := x.1.2
  nlinarith

theorem colNode_injective (hp0 : 0 < p) : Function.Injective (colNode p κ k' π) := by
  intro x y h
  have h1 : x.1 = y.1 := by
    apply Fin.ext
    have := congrArg (· % p) h
    simp only [colNode_mod] at this
    exact this
  have h2 := congrArg (· / p) h
  simp only [colNode_div hp0] at h2
  rw [← h1] at h2
  have := colPer_injective κ k' _ h2
  exact Prod.ext h1 this

theorem rowNode_injective (hp0 : 0 < p) : Function.Injective (rowNode p κ k' π) := by
  intro x y h
  have h1 : x.1 = y.1 := by
    apply Fin.ext
    have := congrArg (· % p) h
    simp only [rowNode_mod] at this
    exact this
  have h2 := congrArg (· / p) h
  simp only [rowNode_div hp0] at h2
  rw [← h1] at h2
  have := rowPer_injective _ h2
  exact Prod.ext h1 this

end Piv

section QMat

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R] (κ k' π : ℕ)

/-- The pivot block `Q = p³ H[𝒫_r, 𝒫_c]` over `R`. -/
noncomputable def Qp (ξ : R) : Matrix (PivIdx p κ k') (PivIdx p κ k') R :=
  Matrix.of fun x y => Qent (p := p) v u ξ (rowNode p κ k' π x) (colNode p κ k' π y)

variable {κ k' π}

/-- Entries of the same residue are the class matrix entries, modulo `p`. -/
theorem Qp_congr (hodd : p % 2 = 1) (hp5 : 5 ≤ p) (hN : 2 * N < p * p)
    (hH : (κ + 2 * k') * p ≤ N) (ξ : R) {x y : PivIdx p κ k'} (hxy : x.1 = y.1) :
    (p : R) ∣ Qp (p := p) v u κ k' π ξ x y -
      BclR (p := p) v u κ k' ξ (half p u x.1) (oc p κ π x.1) x.2 y.2 := by
  have hp0 : 0 < p := hp.out.pos
  have h := F1 v u hodd hp5 hN ξ (rowNode_lt (π := π) hH x) (colNode_lt (π := π) hH y)
    (by rw [rowNode_mod, colNode_mod, hxy])
  have e1 : half p u (rowNode p κ k' π x) = half p u x.1 := by
    unfold rowNode; rw [half_node hp0 _ _ x.1.2]
  rw [e1, rowNode_div hp0, colNode_div hp0, ← hxy] at h
  exact (dvd_pow_self (p : R) (two_ne_zero)).trans h

/-- Entries of different residues are divisible by `p`. -/
theorem Qp_noncong (hodd : p % 2 = 1) (hp5 : 5 ≤ p) (hN : 2 * N < p * p)
    (hH : (κ + 2 * k') * p ≤ N) (ξ : R) {x y : PivIdx p κ k'} (hxy : x.1 ≠ y.1) :
    (p : R) ∣ Qp (p := p) v u κ k' π ξ x y := by
  have h := F2 v u hodd hp5 hN ξ (rowNode_lt (π := π) hH x) (colNode_lt (π := π) hH y)
    (by rw [rowNode_mod, colNode_mod]; exact fun h => hxy (Fin.ext h))
  have h1 : (p : R) ∣ Qent (p := p) v u ξ (rowNode p κ k' π x) (colNode p κ k' π y) -
      (p : R) * (sigR (p := p) v u (cell p u (colNode p κ k' π y)) - sigR (p := p) v u (cell p u (rowNode p κ k' π x))) *
        toR p ((((colNode p κ k' π y : ℕ) : ℚ) - (rowNode p κ k' π x : ℕ))⁻¹) :=
    (dvd_pow_self (p : R) (two_ne_zero)).trans h
  have h2 : (p : R) ∣ (p : R) * (sigR (p := p) v u (cell p u (colNode p κ k' π y)) -
      sigR (p := p) v u (cell p u (rowNode p κ k' π x))) *
        toR p ((((colNode p κ k' π y : ℕ) : ℚ) - (rowNode p κ k' π x : ℕ))⁻¹) :=
    Dvd.dvd.mul_right (dvd_mul_right (p : R) _) _
  have := dvd_add h1 h2
  simpa [Qp] using this

omit [Algebra (LocRing p) R] hp in
theorem det_sub_one_dvd {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n R)
    (h : ∀ i j, (p : R) ∣ M i j - (1 : Matrix n n R) i j) : (p : R) ∣ M.det - 1 := by
  set f := Ideal.Quotient.mk (Ideal.span {(p : R)}) with hf
  have hM : f.mapMatrix M = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    have : f (M i j) = f ((1 : Matrix n n R) i j) := by
      rw [hf, Ideal.Quotient.eq, Ideal.mem_span_singleton]; exact h i j
    rw [this]
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply, hij]
  have h1 : f M.det = 1 := by
    rw [RingHom.map_det, hM, Matrix.det_one]
  have : M.det - 1 ∈ Ideal.span {(p : R)} := by
    rw [← Ideal.Quotient.eq]
    rw [hf] at h1
    rw [h1, map_one]
  exact Ideal.mem_span_singleton.1 this
end QMat

section QInv

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) {N : ℕ}
  {R : Type*} [CommRing R] [Algebra (LocRing p) R] (κ k' π : ℕ) (ξ : R)

/-- The block inverse `W`: `W((ω,b),(ω',c)) = [ω = ω'] (B^{h(ω)}_{o(ω)})⁻¹(b,c)`. -/
noncomputable def Wp : Matrix (PivIdx p κ k') (PivIdx p κ k') R :=
  Matrix.of fun y z =>
    if y.1 = z.1 then ((BclR (p := p) v u κ k' ξ (half p u y.1) (oc p κ π y.1))⁻¹) y.2 z.2 else 0

/-- The inverse of the pivot block. -/
noncomputable def Zp : Matrix (PivIdx p κ k') (PivIdx p κ k') R := (Qp (p := p) v u κ k' π ξ)⁻¹

variable {κ k' π ξ}

theorem Qp_mul_Wp (hU : UnitDet p v u κ k' ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N) (x z : PivIdx p κ k') :
    (p : R) ∣ (Qp (p := p) v u κ k' π ξ * Wp (p := p) v u κ k' π ξ) x z - (1 : Matrix (PivIdx p κ k') (PivIdx p κ k') R) x z := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single z.1]
  swap
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    simp [Wp, ha]
  swap
  · intro h; exact absurd (Finset.mem_univ _) h
  by_cases hxz : x.1 = z.1
  · obtain ⟨x1, x2⟩ := x
    obtain ⟨z1, z2⟩ := z
    simp only at hxz
    subst hxz
    have hh : half p u (x1 : ℕ) ≤ 1 := half_le_one' _
    have hdet := hU _ _ hh (oc_le (π := π) (κ := κ) (p := p) x1)
    have hmul := Matrix.mul_nonsing_inv _ hdet
    have e1 : ∑ b, Qp (p := p) v u κ k' π ξ (x1, x2) (x1, b) * Wp (p := p) v u κ k' π ξ (x1, b) (x1, z2) -
        (1 : Matrix (PivIdx p κ k') (PivIdx p κ k') R) (x1, x2) (x1, z2) =
        ∑ b, (Qp (p := p) v u κ k' π ξ (x1, x2) (x1, b) -
            BclR (p := p) v u κ k' ξ (half p u x1) (oc p κ π x1) x2 b) *
          ((BclR (p := p) v u κ k' ξ (half p u x1) (oc p κ π x1))⁻¹) b z2 := by
      have := congrFun (congrFun hmul x2) z2
      rw [Matrix.mul_apply] at this
      have h1 : (1 : Matrix (PivIdx p κ k') (PivIdx p κ k') R) (x1, x2) (x1, z2) =
          (1 : Matrix (Fin κ ⊕ Fin k') (Fin κ ⊕ Fin k') R) x2 z2 := by
        simp [Matrix.one_apply]
      have hW : ∀ b, Wp (p := p) v u κ k' π ξ (x1, b) (x1, z2) =
          ((BclR (p := p) v u κ k' ξ (half p u x1) (oc p κ π x1))⁻¹) b z2 := fun b => by simp [Wp]
      rw [h1, ← this]
      simp only [hW, sub_mul, Finset.sum_sub_distrib]
    rw [e1]
    refine Finset.dvd_sum fun b _ => ?_
    exact Dvd.dvd.mul_right (Qp_congr v u hodd hp5 hN hH ξ (x := (x1, x2)) (y := (x1, b)) rfl) _
  · have h1 : (1 : Matrix (PivIdx p κ k') (PivIdx p κ k') R) x z = 0 := by
      rw [Matrix.one_apply, if_neg]
      intro h; exact hxz (by rw [h])
    rw [h1, sub_zero]
    refine Finset.dvd_sum fun b _ => ?_
    exact Dvd.dvd.mul_right (Qp_noncong v u hodd hp5 hN hH ξ (x := x) (y := (z.1, b)) hxz) _

theorem isUnit_det_Qp (hU : UnitDet p v u κ k' ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) :
    IsUnit (Qp (p := p) v u κ k' π ξ).det := by
  have h := det_sub_one_dvd _ (Qp_mul_Wp (p := p) (π := π) v u hU hpv hodd hp5 hN hH)
  obtain ⟨c, hc⟩ := h
  have : (Qp (p := p) v u κ k' π ξ * Wp (p := p) v u κ k' π ξ).det = 1 + (p : R) * c := by
    rw [← hc]; ring
  rw [Matrix.det_mul] at this
  have hu1 := hRad c
  rw [← this] at hu1
  exact isUnit_of_mul_isUnit_left hu1

theorem Qp_mul_Zp (hU : UnitDet p v u κ k' ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) :
    Qp (p := p) v u κ k' π ξ * Zp (p := p) v u κ k' π ξ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_det_Qp (p := p) v u hU hpv hodd hp5 hN hH hRad)

theorem Zp_mul_Qp (hU : UnitDet p v u κ k' ξ) (hpv : ¬ (p : ℤ) ∣ v) (hodd : p % 2 = 1) (hp5 : 5 ≤ p)
    (hN : 2 * N < p * p) (hH : (κ + 2 * k') * p ≤ N)
    (hRad : ∀ x : R, IsUnit (1 + (p : R) * x)) :
    Zp (p := p) v u κ k' π ξ * Qp (p := p) v u κ k' π ξ = 1 :=
  Matrix.nonsing_inv_mul _ (isUnit_det_Qp (p := p) v u hU hpv hodd hp5 hN hH hRad)

end QInv

end CatalanCore.Uniform.Content.Sweep

#print axioms CatalanCore.Uniform.Content.Sweep.isUnit_det_Qp
