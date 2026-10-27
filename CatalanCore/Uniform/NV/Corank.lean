module
public import CatalanCore.Uniform.NV.Antidifference
public import CatalanCore.Uniform.NV.Dimension
@[expose] public section
open Polynomial Finset Module
namespace CatalanCore.Uniform.NV
variable {K : Type*} [Field K] [CharZero K] [DecidableEq K]

/-- Exact cleared increments and their first jets on the actual natural nodes. -/
structure StepData (L : ℕ) (D A : K[X]) (f tau : K → K) : Prop where
  value : ∀ a : ℕ, D.eval (a:K)*(f ((a:K)+(L:K))-f (a:K)) = A.eval (a:K)
  jet : ∀ a : ℕ, D.derivative.eval (a:K)*(f ((a:K)+(L:K))-f (a:K)) +
    D.eval (a:K)*(tau ((a:K)+(L:K))-tau (a:K)) = A.derivative.eval (a:K)

theorem stepDefect_roots (L : ℕ) (D A p q : K[X]) (f tau : K → K)
    (data : StepData L D A f tau) (Z C : Finset ℕ) (hCZ : C ⊆ Z)
    (h : Hermite (fieldNodes Z) (fieldNodes C) f tau p q) :
    (∀ a ∈ stepEdges Z L, (stepDefect (L:K) D A q p).eval (a:K) = 0) ∧
    (∀ a ∈ stepEdges C L, (stepDefect (L:K) D A q p).derivative.eval (a:K) = 0) := by
  have hmem (S : Finset ℕ) {a : ℕ} (ha : a ∈ S) : (a:K) ∈ fieldNodes S :=
    Finset.mem_image.mpr ⟨a,ha,rfl⟩
  constructor
  · intro a ha
    obtain ⟨ha,hb⟩ := mem_stepEdges.mp ha
    apply stepDefect_eval_zero (L:K) D A q p (a:K) (f (a:K)) (f ((a:K)+(L:K)))
    · exact h.value _ (hmem Z ha)
    · simpa only [Nat.cast_add] using h.value _ (hmem Z hb)
    · exact data.value a
  · intro a ha
    obtain ⟨ha,hb⟩ := mem_stepEdges.mp ha
    apply stepDefect_derivative_eval_zero (L:K) D A q p (a:K)
      (f (a:K)) (f ((a:K)+(L:K))) (tau (a:K)) (tau ((a:K)+(L:K)))
    · exact h.value _ (hmem Z (by
        exact hCZ ha))
    · simpa only [Nat.cast_add] using h.value _ (hmem Z (hCZ hb))
    · exact h.jet _ (hmem C ha)
    · simpa only [Nat.cast_add] using h.jet _ (hmem C hb)
    · exact data.value a
    · exact data.jet a

/-- Root counting excludes every polynomial pair below the stated degree. -/
theorem no_short_step_pair (L d t : ℕ) (D A p q : K[X]) (f tau : K → K)
    (data : StepData L D A f tau) (a : K) (pole : IsolatedStepPole (L:K) a D A)
    (hd : 2 ≤ d) (hD : D.natDegree ≤ d) (hA : A.natDegree ≤ d-2)
    (Z C : Finset ℕ) (hCZ : C ⊆ Z)
    (h : Hermite (fieldNodes Z) (fieldNodes C) f tau p q)
    (hp : p.natDegree ≤ t) (hq : q.natDegree ≤ t)
    (hsize : 2*t+d-2 < Z.card-componentCount Z L+(C.card-componentCount C L)) : p = 0 := by
  by_contra hp0
  have hW := stepDefect_ne_zero pole q p hp0
  have hroots := stepDefect_roots L D A p q f tau data Z C hCZ h
  have hlo := degree_ge_step_roots Z C hCZ L (stepDefect (L:K) D A q p) hW hroots.1 hroots.2
  have hhi := natDegree_stepDefect_le (L:K) D A q p d t hd hD hA hq hp
  omega

noncomputable def pairQ (Z C : Finset K) (f tau : K → K) (d : ℕ) :
    pairSpace Z C f tau d →ₗ[K] K[X] :=
  (LinearMap.snd K K[X] K[X]).comp (pairSpace Z C f tau d).subtype

/-- The full step-component corank estimate for the actual Hermite source space.
The only source assumptions are cleared increment identities, pole data, geometry
and polynomial degree bounds. -/
theorem step_pairSpace_finrank_le (L d n : ℕ) (D A : K[X]) (f tau : K → K)
    (data : StepData L D A f tau) (a : K) (pole : IsolatedStepPole (L:K) a D A)
    (hd : 2 ≤ d) (hD : D.natDegree ≤ d) (hA : A.natDegree ≤ d-2)
    (Z C : Finset ℕ) (hCZ : C ⊆ Z) (hn : 1 ≤ n) (hcard : Z.card+C.card = 2*n)
    (hs : (d+componentCount Z L+componentCount C L-2)/2 < n) :
    finrank K (pairSpace (fieldNodes Z) (fieldNodes C) f tau (n-1)) ≤
      (d+componentCount Z L+componentCount C L-2)/2 := by
  let s := (d+componentCount Z L+componentCount C L-2)/2
  let P := pairSpace (fieldNodes Z) (fieldNodes C) f tau (n-1)
  let p := pairP (fieldNodes Z) (fieldNodes C) f tau (n-1)
  let q := pairQ (fieldNodes Z) (fieldNodes C) f tau (n-1)
  have hZ : n ≤ Z.card := by have := Finset.card_le_card hCZ;omega
  have hi : Function.Injective p := pairP_injective _ _ _ _ _ (by rw [card_fieldNodes];omega)
  apply finrank_le_of_no_short_pairs p q n s hs
  · exact fun v => v.property.1
  · exact fun v => v.property.2.1
  · intro v hp hq
    exact Subtype.ext (Prod.ext hp hq)
  · intro v w
    exact cross_product_eq_zero (fieldNodes Z) (fieldNodes C) (fieldNodes_mono hCZ)
      f tau (n-1) (by simp only [card_fieldNodes];omega)
      v.val.1 v.val.2 w.val.1 w.val.2 v.property.1 v.property.2.1
      w.property.1 w.property.2.1 v.property.2.2 w.property.2.2
  · intro v hp hq
    have hp0 : v.val.1 = 0 := no_short_step_pair L d (n-s-1) D A v.val.1 v.val.2 f tau
      data a pole hd hD hA Z C hCZ v.property.2.2 hp hq (by
        have hG := card_edges_add_components Z L
        have hH := card_edges_add_components C L
        dsimp [s] at *
        omega)
    exact hi (show p v = p 0 from (by change v.val.1 = 0; exact hp0))

/-- Full bound, including the range where the component bound exceeds n. -/
theorem step_pairSpace_finrank_bound (L d n : ℕ) (D A : K[X]) (f tau : K → K)
    (data : StepData L D A f tau) (a : K) (pole : IsolatedStepPole (L:K) a D A)
    (hd : 2 ≤ d) (hD : D.natDegree ≤ d) (hA : A.natDegree ≤ d-2)
    (Z C : Finset ℕ) (hCZ : C ⊆ Z) (hn : 1 ≤ n) (hcard : Z.card+C.card = 2*n) :
    finrank K (pairSpace (fieldNodes Z) (fieldNodes C) f tau (n-1)) ≤
      (d+componentCount Z L+componentCount C L-2)/2 := by
  by_cases hs : (d+componentCount Z L+componentCount C L-2)/2 < n
  · exact step_pairSpace_finrank_le L d n D A f tau data a pole hd hD hA Z C hCZ hn hcard hs
  · have hZ : n ≤ Z.card := by have := Finset.card_le_card hCZ;omega
    have hbound := finrank_le_of_bounded_coordinate
      (pairP (fieldNodes Z) (fieldNodes C) f tau (n-1)) n hn
      (fun v => v.property.1)
      (pairP_injective _ _ _ _ _ (by rw [card_fieldNodes];omega))
    exact hbound.trans (by omega)
end CatalanCore.Uniform.NV




