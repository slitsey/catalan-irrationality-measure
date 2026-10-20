module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Generic double-sum energy bounds (ENERGYDEDUP)

The shared part of the hybrid `I_ρ` certificates (λ and `L(2,χ₋₃)`): atoms are integer triples
`(x, y, w)`, a pair energy `Jr` with exact integer row sums `iRow`, and `iTotL B A` the integer total
of `A` against `B`.  `sum2_le_gen` bounds any double sum dominated by `Jr` over the atom lists.
-/

open Real

namespace CatalanCore.Decay.EnergyGen

abbrev Pt := ℤ × ℤ × ℕ

/-- Integer total of `A` against `B`: `∑_{p ∈ A} w_p · iRow p B`. -/
def iTotL (iRow : Pt → List Pt → ℤ) (B : List Pt) : List Pt → ℤ
  | [] => 0
  | p :: ps => (p.2.2 : ℤ) * iRow p B + iTotL iRow B ps

section
variable {Jr : Pt → Pt → ℝ} {iRow : Pt → List Pt → ℤ}
  (hrow : ∀ (p : Pt) (l : List Pt),
    (l.map (Jr p)).sum = -((p.2.2 : ℝ) * (iRow p l : ℝ)) / 2 ^ 129)

include hrow in
lemma totL (B : List Pt) : ∀ A : List Pt,
    (A.map (fun p => (B.map (Jr p)).sum)).sum = -(iTotL iRow B A : ℝ) / 2 ^ 129 := by
  intro A
  induction A with
  | nil => simp [iTotL]
  | cons p ps ih =>
    rw [List.map_cons, List.sum_cons, ih, hrow]
    simp only [iTotL]
    push_cast
    ring

include hrow in
/-- A double sum dominated termwise by `Jr` over the atom lists `A`, `B` is `≤ -X / 2^129`
where `X = iTotL B A`. -/
theorem sum2_le_gen {K1 K2 : ℕ} (f : Fin K1 → Fin K2 → ℝ) (A B : List Pt)
    (pa : Fin K1 → Pt) (pb : Fin K2 → Pt)
    (hA : ∀ g : Pt → ℝ, ∑ k, g (pa k) = (A.map g).sum)
    (hB : ∀ g : Pt → ℝ, ∑ l, g (pb l) = (B.map g).sum)
    (hle : ∀ k l, f k l ≤ Jr (pa k) (pb l)) (X : ℤ) (hX : iTotL iRow B A = X) :
    ∑ k, ∑ l, f k l ≤ -(X : ℝ) / 2 ^ 129 := by
  have h1 : ∑ k, ∑ l, f k l ≤ ∑ k, ∑ l, Jr (pa k) (pb l) :=
    Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun l _ => hle k l))
  have h2 : ∑ k, ∑ l, Jr (pa k) (pb l) = -(iTotL iRow B A : ℝ) / 2 ^ 129 := by
    simp_rw [hB (Jr (pa _))]
    rw [hA (fun p => (B.map (Jr p)).sum), totL hrow]
  rw [hX] at h2
  exact h1.trans h2.le

end

end CatalanCore.Decay.EnergyGen
