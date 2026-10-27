module
public import CatalanCore.Uniform.NV.KernelCoordinates
public import CatalanCore.Uniform.NV.Corank
@[expose] public section
open Polynomial Finset Matrix Module
open CatalanCore.Arith.Hybrid.FiniteFieldCorank
open CatalanCore.Rect.CharZeroNV
namespace CatalanCore.Uniform.NV
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]
namespace NodeGeometry
variable (G : NodeGeometry (K := K))

theorem rightCoords_in_kernel (f tau : K → K) (hn : 1 ≤ G.rows.card) (P : G.pairs f tau) :
    G.matrix f tau *ᵥ G.rightCoords f tau P = 0 := by
  funext a
  rw [← G.row_eq]
  have he : loewnerRow G.cols f tau (G.kernelWeights (G.rightCoords f tau P)) a.val =
      loewnerRow G.cols f tau (fun b => P.val.1.eval b/(punctured G.cols b).eval b) a.val := by
    unfold loewnerRow
    apply Finset.sum_congr rfl
    intro b hb
    simp [kernelWeights,rightCoords,hb]
  rw [he]
  apply pair_gives_kernel_row G.cols (by rw [G.card_cols];exact hn) f tau P.val.1 P.val.2
  · simpa [G.card_cols] using P.property.1
  · simpa [G.card_cols] using P.property.2.1
  · intro b hb
    exact P.property.2.2.value b (mem_union.mpr (Or.inr hb))
  · exact P.property.2.2.value a.val (mem_union.mpr (Or.inl a.property))
  · intro hb
    exact P.property.2.2.jet a.val (mem_inter.mpr ⟨a.property,hb⟩)

theorem rightCoords_injective (f tau : K → K) (hn : 1 ≤ G.rows.card) :
    Function.Injective (G.rightCoords f tau) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro P hP
  have hp : P.val.1 = 0 := by
    apply eq_zero_of_hermite_roots G.cols ∅ (by simp)
    · intro b hb
      have he := congrFun hP (G.equiv.symm ⟨b,hb⟩)
      change P.val.1.eval (G.equiv (G.equiv.symm ⟨b,hb⟩)).val / _ = 0 at he
      simp only [Equiv.apply_symm_apply] at he
      simpa only [div_eq_zero_iff,punctured_eval_ne_zero G.cols b,or_false] using he
    · simp
    · have hd := P.property.1
      rw [G.card_cols]
      simp only [card_empty,add_zero]
      omega
  have hq : P.val.2 = 0 := by
    apply eq_zero_of_hermite_roots G.cols ∅ (by simp)
    · intro b hb
      simpa [hp] using P.property.2.2.value b (mem_union.mpr (Or.inr hb))
    · simp
    · have hd := P.property.2.1
      rw [G.card_cols]
      simp only [card_empty,add_zero]
      omega
  exact Subtype.ext (Prod.ext hp hq)

noncomputable def rightKernelMap (f tau : K → K) (hn : 1 ≤ G.rows.card) :
    G.pairs f tau →ₗ[K] LinearMap.ker (G.matrix f tau).mulVecLin :=
  (G.rightCoords f tau).codRestrict _ (fun P => by
    change G.matrix f tau *ᵥ G.rightCoords f tau P = 0
    exact G.rightCoords_in_kernel f tau hn P)

noncomputable def rightKernelEquiv (f tau : K → K) (hn : 1 ≤ G.rows.card) :
    G.pairs f tau ≃ₗ[K] LinearMap.ker (G.matrix f tau).mulVecLin :=
  LinearEquiv.ofBijective (G.rightKernelMap f tau hn) ⟨by
    intro P Q h
    apply G.rightCoords_injective f tau hn
    exact congrArg Subtype.val h, by
    intro v
    obtain ⟨P,hP⟩ := G.rightCoords_onto_kernel f tau v.val v.property
    exact ⟨P,Subtype.ext hP⟩⟩

theorem pairSpace_finrank_eq_corank (f tau : K → K) (hn : 1 ≤ G.rows.card) :
    finrank K (G.pairs f tau) = finrank K (LinearMap.ker (G.matrix f tau).mulVecLin) :=
  (G.rightKernelEquiv f tau hn).finrank_eq
end NodeGeometry

/-- The step-component bound for the actual Loewner matrix kernel. -/
theorem step_component_corank (G : NodeGeometry (K := K))
    (L d c m : ℕ) (D A : K[X]) (f tau : K → K)
    (data : StepData L D A f tau) (a : K) (pole : IsolatedStepPole (L:K) a D A)
    (hd : 2 ≤ d) (hD : D.natDegree ≤ d) (hA : A.natDegree ≤ d-2)
    (Z C : Finset ℕ) (hCZ : C ⊆ Z) (hC : C.card = c) (hZ : Z.card = c+2*m)
    (hunion : G.rows ∪ G.cols = fieldNodes Z) (hinter : G.rows ∩ G.cols = fieldNodes C)
    (hrows : G.rows.card = c+m) (hn : 1 ≤ c+m) :
    finrank K (LinearMap.ker (G.matrix f tau).mulVecLin) ≤
      (d+componentCount Z L+componentCount C L-2)/2 := by
  rw [← G.pairSpace_finrank_eq_corank f tau (by omega)]
  change finrank K (pairSpace (G.rows ∪ G.cols) (G.rows ∩ G.cols) f tau (G.rows.card-1)) ≤ _
  rw [hunion,hinter,hrows]
  apply step_pairSpace_finrank_bound L d (c+m) D A f tau data a pole hd hD hA Z C hCZ hn
  omega
end CatalanCore.Uniform.NV
