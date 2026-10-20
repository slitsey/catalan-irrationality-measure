module

public import CatalanCore.Rect.CharZeroNV.Support
public import CatalanCore.Rect.CharZeroNV.Dimension

@[expose] public section

/-! # The shared finite-dimensional interpolation space

The common-node evaluation map detects this space. It is the coordinate map
used by the existing principal-deletion selector.
-/

open Polynomial Finset Module

namespace CatalanCore.Rect.CharZeroNV

variable {K : Type*} [Field K] [CharZero K] {D A : K[X]}

noncomputable def pairSpace (data : IncrementData D A) (N r d : ℕ) :
    Submodule K (K[X] × K[X]) where
  carrier := {v | v.1.natDegree ≤ d ∧ v.2.natDegree ≤ d ∧
    Interpolates data N r v.2 v.1}
  zero_mem' := by simp; exact ⟨by intros; simp, by intros; simp⟩
  add_mem' := by
    rintro v w ⟨hpv, hqv, hv⟩ ⟨hpw, hqw, hw⟩
    refine ⟨(natDegree_add_le _ _).trans (max_le hpv hpw),
      (natDegree_add_le _ _).trans (max_le hqv hqw), ?_, ?_⟩
    · intro i hi
      simp only [Prod.fst_add, Prod.snd_add, eval_add, hv.value i hi, hw.value i hi]
      ring
    · intro i hi
      simp only [Prod.fst_add, Prod.snd_add, derivative_add, eval_add,
        hv.jet i hi, hw.jet i hi]
      ring
  smul_mem' := by
    rintro c v ⟨hp, hq, hv⟩
    refine ⟨(natDegree_smul_le _ _).trans hp, (natDegree_smul_le _ _).trans hq, ?_, ?_⟩
    · intro i hi
      change (c • v.2).eval (i : K) = data.f i * (c • v.1).eval (i : K)
      simp only [eval_smul, smul_eq_mul, hv.value i hi]
      ring
    · intro i hi
      change (c • v.2).derivative.eval (i : K) =
        data.f i * (c • v.1).derivative.eval (i : K) + data.tau i * (c • v.1).eval (i : K)
      simp only [derivative_smul, eval_smul,
        smul_eq_mul, hv.jet i hi]
      ring

noncomputable def pairP (data : IncrementData D A) (N r d : ℕ) :
    pairSpace data N r d →ₗ[K] K[X] :=
  (LinearMap.fst K K[X] K[X]).comp (pairSpace data N r d).subtype

noncomputable def pairQ (data : IncrementData D A) (N r d : ℕ) :
    pairSpace data N r d →ₗ[K] K[X] :=
  (LinearMap.snd K K[X] K[X]).comp (pairSpace data N r d).subtype

theorem pairP_injective (data : IncrementData D A) (N r d : ℕ) (hd : d < N) :
    Function.Injective (pairP data N r d) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hp : v.val.1 = 0 := hv
  have hq : v.val.2 = 0 := by
    apply eq_zero_of_hermite_roots (natNodes N) ∅ (by simp)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := mem_natNodes.mp hx
      simpa [hp] using v.property.2.2.value i hi
    · simp
    · simpa only [card_natNodes, card_empty, add_zero] using v.property.2.1.trans_lt hd
  exact Subtype.ext (Prod.ext hp hq)

noncomputable def commonEval (data : IncrementData D A) (r m : ℕ) :
    pairSpace data (r + 2 * m) r (r + m - 1) →ₗ[K] (Fin r → K) where
  toFun v i := v.val.1.eval (i : ℕ)
  map_add' := by intros; ext i; simp
  map_smul' := by intros; ext i; simp

theorem commonEval_injective (data : IncrementData D A) (hpole : IsolatedIntegerPole D A)
    (hD : D.natDegree ≤ 3) (hA : A.natDegree ≤ 1) (r m : ℕ) (hr : 1 ≤ r) :
    Function.Injective (commonEval data r m) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hp := pair_eq_zero_of_common_values data hpole hD hA r m hr
    v.val.2 v.val.1 v.property.2.1 v.property.1 v.property.2.2 (by
      intro i hi
      exact congrFun hv ⟨i, hi⟩)
  exact pairP_injective data (r + 2 * m) r (r + m - 1) (by omega)
    (show pairP data _ _ _ v = pairP data _ _ _ 0 by
      change v.val.1 = 0
      exact hp)

theorem pairSpace_finrank_le_one (data : IncrementData D A)
    (hpole : IsolatedIntegerPole D A) (hD : D.natDegree ≤ 3) (hA : A.natDegree ≤ 1)
    (r m : ℕ) (hr : 1 ≤ r) (hn : 2 ≤ r + m) :
    finrank K (pairSpace data (r + 2 * m) r (r + m - 1)) ≤ 1 := by
  apply finrank_interpolation_le_one data hpole hD hA r m hr hn
    (pairP data _ _ _) (pairQ data _ _ _)
    (pairP_injective data _ _ _ (by omega))
  · exact fun v => v.property.1
  · exact fun v => v.property.2.1
  · exact fun v => v.property.2.2

end CatalanCore.Rect.CharZeroNV
