module
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Prod
public import Lean.Elab.Tactic.Omega
@[expose] public section
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 50

namespace CatalanMeasure.GenD.Uniform.Prefix
variable {K M V : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup V] [Module K V]

/-- The original coefficient-window equations, with empty and zero windows allowed. -/
def windowSpace {p : Nat} (A : M →ₗ[K] (Fin p → V)) (lo hi : Nat) : Submodule K M where
  carrier := {x | ∀ i : Fin p, lo ≤ i.val → i.val < hi → A x i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hli hih; simp [hx i hli hih, hy i hli hih]
  smul_mem' := by intro a x hx i hli hih; simp [hx i hli hih]

/-- A prefix equation with a low-degree auxiliary value, in the same p frame.
Every auxiliary coordinate is retained; the next theorem proves it is unique. -/
def prefixGraph {p : Nat} (A : M →ₗ[K] (Fin p → V)) (lo hi : Nat)
    (hhi : hi ≤ p) : Submodule K (M × (Fin lo → V)) where
  carrier := {xg | ∀ i : Fin hi, A xg.1 ⟨i.val, lt_of_lt_of_le i.is_lt hhi⟩ =
    if h : i.val < lo then xg.2 ⟨i.val,h⟩ else 0}
  zero_mem' := by intro i; split <;> simp
  add_mem' := by
    intro x y hx hy i
    by_cases h : i.val < lo
    · simpa [h, hx i, hy i] using congrArg₂ (fun a b : V => a+b) (hx i) (hy i)
    · simp [h, hx i, hy i]
  smul_mem' := by
    intro a x hx i
    by_cases h : i.val < lo <;> simp [h, hx i]

/-- Exact unique-graph reduction from an ordinary coefficient window to prefixes.
This includes lo=0, lo=hi, hi=p, p=0 and arbitrary characteristic. It cannot add
nullity: projection onto the original coordinates is the inverse equivalence. -/
noncomputable def windowGraphEquiv {p : Nat} (A : M →ₗ[K] (Fin p → V))
    (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ p) :
    windowSpace A lo hi ≃ₗ[K] prefixGraph A lo hi hhi where
  toFun x := ⟨(x.val, fun j => A x.val ⟨j.val, lt_of_lt_of_le j.is_lt (hlo.trans hhi)⟩), by
    intro i
    by_cases h : i.val < lo
    · simp [h]
    · simp only [dif_neg h]
      exact x.property _ (Nat.le_of_not_gt h) i.is_lt⟩
  invFun xg := ⟨xg.val.1, by
    intro i hli hih
    have h := xg.property ⟨i.val,hih⟩
    simpa [show ¬ i.val < lo by omega] using h⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv xg := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext j
      have h := xg.property ⟨j.val,lt_of_lt_of_le j.is_lt hlo⟩
      simpa only [dif_pos j.is_lt] using h
  map_add' x y := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext j; simp
  map_smul' a x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext j; simp

@[simp] theorem windowGraphEquiv_fst {p : Nat} (A : M →ₗ[K] (Fin p → V))
    (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ p) (x : windowSpace A lo hi) :
    (windowGraphEquiv A lo hi hlo hhi x).val.1 = x.val := rfl

#print axioms windowGraphEquiv
end CatalanMeasure.GenD.Uniform.Prefix