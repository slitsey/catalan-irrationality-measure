module

public import CatalanCore.Rect.CharZeroNV.Geometry

@[expose] public section

/-! # Right and left Loewner kernels use the same interpolation space -/

open Polynomial Finset Matrix
open CatalanCore.Arith.Hybrid.FiniteFieldCorank

namespace CatalanCore.Rect.CharZeroNV

variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]
  {D A : K[X]} {r m : ℕ}

namespace NodeGeometry

noncomputable def weights (G : NodeGeometry (K := K) r m)
    (v : G.rows → K) (x : K) : K :=
  if hx : x ∈ G.cols then v (G.equiv.symm ⟨x, hx⟩) else 0

@[simp] lemma weights_equiv (G : NodeGeometry (K := K) r m) (v : G.rows → K) (j : G.rows) :
    G.weights v (G.equiv j).val = v j := by
  simp [weights]

theorem row_eq_mulVec (G : NodeGeometry (K := K) r m)
    (f tau : K → K) (v : G.rows → K) (i : G.rows) :
    loewnerRow G.cols f tau (G.weights v) i.val = (loewnerMatrix G f tau *ᵥ v) i := by
  calc
    _ = ∑ b : G.cols, loewnerEntry f tau i.val b.val * G.weights v b.val := by
      exact (Finset.sum_coe_sort G.cols
        (fun b : K => loewnerEntry f tau i.val b * G.weights v b)).symm
    _ = ∑ j : G.rows, loewnerEntry f tau i.val (G.equiv j).val * v j := by
      rw [← Equiv.sum_comp G.equiv]
      simp
    _ = _ := rfl

theorem kernel_interpolates (G : NodeGeometry (K := K) r m)
    (data : IncrementData D A) (f tau : K → K)
    (hf : ∀ i : ℕ, f (i : K) = data.f i) (ht : ∀ i : ℕ, tau (i : K) = data.tau i)
    (v : G.rows → K) (hv : loewnerMatrix G f tau *ᵥ v = 0) :
    Interpolates data (r + 2 * m) r
      (numerator G.cols (fun b => G.weights v b * f b)) (numerator G.cols (G.weights v)) where
  value i hi := by
    rw [← hf]
    by_cases hb : (i : K) ∈ G.cols
    · exact kernel_value_inside G.cols f (G.weights v) (i : K) hb
    · have ha : (i : K) ∈ G.rows := (G.mem_union hi).resolve_right hb
      apply kernel_value_outside G.cols f tau (G.weights v) (i : K) hb
      rw [G.row_eq_mulVec f tau v ⟨(i : K), ha⟩, hv]
      rfl
  jet i hi := by
    rw [← hf, ← ht]
    have hcommon := G.common_mem ⟨i, hi⟩
    apply kernel_jet G.cols f tau (G.weights v) (i : K) hcommon.2
    rw [G.row_eq_mulVec f tau v ⟨(i : K), hcommon.1⟩, hv]
    rfl

end NodeGeometry

theorem pair_value_on_union (G : NodeGeometry (K := K) r m)
    (data : IncrementData D A) (f : K → K) (hf : ∀ i : ℕ, f (i : K) = data.f i)
    (P : pairSpace data (r + 2 * m) r (r + m - 1))
    (x : K) (hx : x ∈ G.rows ∪ G.cols) : P.val.2.eval x = f x * P.val.1.eval x := by
  rw [G.union_eq] at hx
  obtain ⟨i, hi, rfl⟩ := mem_natNodes.mp hx
  rw [hf]
  exact P.property.2.2.value i hi

theorem pair_jet_on_inter (G : NodeGeometry (K := K) r m)
    (data : IncrementData D A) (f tau : K → K)
    (hf : ∀ i : ℕ, f (i : K) = data.f i) (ht : ∀ i : ℕ, tau (i : K) = data.tau i)
    (P : pairSpace data (r + 2 * m) r (r + m - 1))
    (x : K) (hx : x ∈ G.rows ∧ x ∈ G.cols) :
    P.val.2.derivative.eval x = f x * P.val.1.derivative.eval x + tau x * P.val.1.eval x := by
  obtain ⟨i, hi, rfl⟩ := G.mem_inter hx
  rw [hf, ht]
  exact P.property.2.2.jet i hi

noncomputable def rightCoords (G : NodeGeometry (K := K) r m) (data : IncrementData D A) :
    pairSpace data (r + 2 * m) r (r + m - 1) →ₗ[K] (G.rows → K) where
  toFun P j := P.val.1.eval (G.equiv j).val / (punctured G.cols (G.equiv j).val).eval (G.equiv j).val
  map_add' := by intros; ext i; simp [add_div]
  map_smul' := by intros; ext i; simp [smul_eq_mul, mul_div_assoc]

noncomputable def leftCoords (G : NodeGeometry (K := K) r m) (data : IncrementData D A) :
    pairSpace data (r + 2 * m) r (r + m - 1) →ₗ[K] (G.rows → K) where
  toFun P i := P.val.1.eval i.val / (punctured G.rows i.val).eval i.val
  map_add' := by intros; ext i; simp [add_div]
  map_smul' := by intros; ext i; simp [smul_eq_mul, mul_div_assoc]

theorem rightCoords_onto_kernel (G : NodeGeometry (K := K) r m)
    (data : IncrementData D A) (f tau : K → K)
    (hf : ∀ i : ℕ, f (i : K) = data.f i) (ht : ∀ i : ℕ, tau (i : K) = data.tau i)
    (v : G.rows → K) (hv : loewnerMatrix G f tau *ᵥ v = 0) :
    ∃ P, rightCoords G data P = v := by
  let p := numerator G.cols (G.weights v)
  let q := numerator G.cols (fun b => G.weights v b * f b)
  have hp : p.natDegree ≤ r + m - 1 := by
    simpa [G.card_cols] using natDegree_numerator_le G.cols (G.weights v)
  have hq : q.natDegree ≤ r + m - 1 := by
    simpa [G.card_cols] using natDegree_numerator_le G.cols (fun b => G.weights v b * f b)
  let P : pairSpace data (r + 2 * m) r (r + m - 1) :=
    ⟨(p, q), hp, hq, G.kernel_interpolates data f tau hf ht v hv⟩
  refine ⟨P, ?_⟩
  ext j
  change p.eval (G.equiv j).val / (punctured G.cols (G.equiv j).val).eval (G.equiv j).val = v j
  rw [show p.eval (G.equiv j).val =
      G.weights v (G.equiv j).val * (punctured G.cols (G.equiv j).val).eval (G.equiv j).val from
    eval_numerator_punctured G.cols (G.weights v) (G.equiv j).property]
  rw [G.weights_equiv]
  exact mul_div_cancel_right₀ _ (punctured_eval_ne_zero _ _)

theorem leftCoords_in_kernel (G : NodeGeometry (K := K) r m)
    (data : IncrementData D A) (f tau : K → K)
    (hf : ∀ i : ℕ, f (i : K) = data.f i) (ht : ∀ i : ℕ, tau (i : K) = data.tau i)
    (hr : 1 ≤ r) (P : pairSpace data (r + 2 * m) r (r + m - 1)) :
    (loewnerMatrix G f tau).transpose *ᵥ leftCoords G data P = 0 := by
  ext i
  have hrow : loewnerRow G.rows f tau
      (fun a => P.val.1.eval a / (punctured G.rows a).eval a) (G.equiv i).val = 0 := by
    apply pair_gives_kernel_row G.rows (by rw [G.card_rows]; omega) f tau P.val.1 P.val.2
    · simpa [G.card_rows] using P.property.1
    · simpa [G.card_rows] using P.property.2.1
    · intro b hb
      exact pair_value_on_union G data f hf P b (mem_union.mpr (Or.inl hb))
    · exact pair_value_on_union G data f hf P _ (mem_union.mpr (Or.inr (G.equiv i).property))
    · intro ha
      exact pair_jet_on_inter G data f tau hf ht P _ ⟨ha, (G.equiv i).property⟩
  calc
    ((loewnerMatrix G f tau).transpose *ᵥ leftCoords G data P) i =
        ∑ j : G.rows, loewnerEntry f tau (G.equiv i).val j.val *
          (P.val.1.eval j.val / (punctured G.rows j.val).eval j.val) := by
      apply Finset.sum_congr rfl
      intro j _
      change loewnerEntry f tau j.val (G.equiv i).val * _ = _
      exact congrArg (fun z : K => z * (P.val.1.eval j.val / (punctured G.rows j.val).eval j.val))
        (loewnerEntry_symm f tau j.val (G.equiv i).val)
    _ = loewnerRow G.rows f tau
        (fun a => P.val.1.eval a / (punctured G.rows a).eval a) (G.equiv i).val :=
      Finset.sum_coe_sort G.rows (fun a : K => loewnerEntry f tau (G.equiv i).val a *
        (P.val.1.eval a / (punctured G.rows a).eval a))
    _ = 0 := hrow

theorem rightCoords_common (G : NodeGeometry (K := K) r m) (data : IncrementData D A)
    (P : pairSpace data (r + 2 * m) r (r + m - 1)) (i : Fin r) :
    rightCoords G data P (G.common i) =
      ((punctured G.cols (i.val : K)).eval (i.val : K))⁻¹ * commonEval data r m P i := by
  change P.val.1.eval (G.equiv (G.common i)).val / _ = _
  have halign : (G.equiv (G.common i)).val = (i.val : K) := G.align i (G.common_mem i).1
  rw [halign]
  exact div_eq_inv_mul _ _

theorem leftCoords_common (G : NodeGeometry (K := K) r m) (data : IncrementData D A)
    (P : pairSpace data (r + 2 * m) r (r + m - 1)) (i : Fin r) :
    leftCoords G data P (G.common i) =
      ((punctured G.rows (i.val : K)).eval (i.val : K))⁻¹ * commonEval data r m P i := by
  change P.val.1.eval (i.val : K) / _ = _
  exact div_eq_inv_mul _ _

end CatalanCore.Rect.CharZeroNV
