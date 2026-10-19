module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic.Module

/-!
# The telescoping lemma for `[N_s, T]` (package H4, ingredient of `(Comm)`)

`N_s = Σ_{y=1}^{s} c_y c_yᵀ`.  If `T c_y = l(y) c_{y-1} + d(y) c_y + r(y) c_{y+1} + (element of W)` and
`Tᵀ c_y ⬝ x = r(y-1) c_{y-1}⬝x + d(y) c_y⬝x + l(y+1) c_{y+1}⬝x` (the row chain, paired with `x`
killing the `W_X` part), for `1 ≤ y ≤ s`, with `l(1) = r(0) = 0`, then
`[N_s, T] x ≡ l(s+1)(c_{s+1}⬝x) c_s - r(s)(c_s⬝x) c_{s+1}  (mod W)`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore

variable {F : Type*} [Field F] {K : ℕ}

lemma vecMulVec_mulVec' (u v w : Fin K → F) : Matrix.vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec, Matrix.of_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `N_s = Σ_{y=1}^{s} c_y c_yᵀ`. -/
def Nsum (c : ℕ → Fin K → F) (s : ℕ) : Matrix (Fin K) (Fin K) F :=
  ∑ y ∈ Finset.Icc 1 s, Matrix.vecMulVec (c y) (c y)

lemma Nsum_succ (c : ℕ → Fin K → F) (s : ℕ) :
    Nsum c (s + 1) = Nsum c s + Matrix.vecMulVec (c (s + 1)) (c (s + 1)) := by
  unfold Nsum
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma Nsum_mulVec_succ (c : ℕ → Fin K → F) (s : ℕ) (y : Fin K → F) :
    Nsum c (s + 1) *ᵥ y = Nsum c s *ᵥ y + (c (s + 1) ⬝ᵥ y) • c (s + 1) := by
  rw [Nsum_succ, Matrix.add_mulVec, vecMulVec_mulVec']

theorem telescope (c : ℕ → Fin K → F) (T : Matrix (Fin K) (Fin K) F) (l d r : ℕ → F)
    (Wsub : Submodule F (Fin K → F)) (x : Fin K → F) (hl1 : l 1 = 0) (hr0 : r 0 = 0) :
    ∀ s : ℕ,
      (∀ y, 1 ≤ y → y ≤ s → T *ᵥ c y - l y • c (y - 1) - d y • c y - r y • c (y + 1) ∈ Wsub) →
      (∀ y, 1 ≤ y → y ≤ s → (Tᵀ *ᵥ c y) ⬝ᵥ x =
        r (y - 1) * (c (y - 1) ⬝ᵥ x) + d y * (c y ⬝ᵥ x) + l (y + 1) * (c (y + 1) ⬝ᵥ x)) →
      (Nsum c s *ᵥ (T *ᵥ x) - T *ᵥ (Nsum c s *ᵥ x)) -
        ((l (s + 1) * (c (s + 1) ⬝ᵥ x)) • c s - (r s * (c s ⬝ᵥ x)) • c (s + 1)) ∈ Wsub := by
  intro s
  induction s with
  | zero =>
    intro _ _
    simp [Nsum, hl1, hr0]
  | succ s ih =>
    intro hCC hRC
    have ih' := ih (fun y h1 h2 => hCC y h1 (by omega)) (fun y h1 h2 => hRC y h1 (by omega))
    have hc := hCC (s + 1) (by omega) le_rfl
    have hr := hRC (s + 1) (by omega) le_rfl
    simp only [Nat.add_sub_cancel] at hc hr
    have e1 : c (s + 1) ⬝ᵥ (T *ᵥ x) = (Tᵀ *ᵥ c (s + 1)) ⬝ᵥ x := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    set w := T *ᵥ c (s + 1) - l (s + 1) • c s - d (s + 1) • c (s + 1) - r (s + 1) • c (s + 2)
      with hw
    have hTc : T *ᵥ c (s + 1) = w + l (s + 1) • c s + d (s + 1) • c (s + 1)
        + r (s + 1) • c (s + 2) := by rw [hw]; abel
    have key : (Nsum c (s + 1) *ᵥ (T *ᵥ x) - T *ᵥ (Nsum c (s + 1) *ᵥ x)) -
        ((l (s + 1 + 1) * (c (s + 1 + 1) ⬝ᵥ x)) • c (s + 1) -
          (r (s + 1) * (c (s + 1) ⬝ᵥ x)) • c (s + 1 + 1)) =
        ((Nsum c s *ᵥ (T *ᵥ x) - T *ᵥ (Nsum c s *ᵥ x)) -
          ((l (s + 1) * (c (s + 1) ⬝ᵥ x)) • c s - (r s * (c s ⬝ᵥ x)) • c (s + 1))) -
        (c (s + 1) ⬝ᵥ x) • w := by
      rw [Nsum_mulVec_succ, Nsum_mulVec_succ, Matrix.mulVec_add, Matrix.mulVec_smul, e1, hr, hTc]
      module
    rw [key]
    exact Submodule.sub_mem _ ih' (Submodule.smul_mem _ _ hc)

end CatalanCore
