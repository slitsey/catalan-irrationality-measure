module
public import CatalanMeasure.GenD.Uniform.W.Lucas.LB
public import CatalanMeasure.GenD.Uniform.W.Lucas.CellA
@[expose] public section
set_option Elab.async false

/-!
# Theorem A: the nullity lower bound `aLB`

`aLB P hP` is the design-generic Lucas bound of the cell `cellA` (window `S = 35`).
-/

namespace CatalanMeasure.GenD.Uniform.W.Lucas
open CatalanMeasure.GenD CatalanMeasure.Parametric
noncomputable section

/-- **Theorem A** as a nullity lower bound (design-generic). -/
def aLB (P : Parameters) (hP : Admissible P) : NullityLB P := aCellLB cellA cellA_affine P hP

theorem aLB_kap (P : Parameters) (hP : Admissible P) (N p : ℕ) :
    (aLB P hP).kap N p = (aCellLB cellA cellA_affine P hP).kap N p := rfl

theorem ZmB_pos (Ub Jb : ℕ) : 0 < ZmB Ub Jb := by
  unfold ZmB
  have h : ∀ (l : List ℕ) (a : ℕ), 0 < a → (∀ x ∈ l, 0 < x) → 0 < l.foldl Nat.lcm a := by
    intro l
    induction l with
    | nil => intro a ha _; exact ha
    | cons y l ih =>
      intro a ha hl
      exact ih _ (Nat.lcm_pos ha (hl y (List.mem_cons_self))) (fun x hx => hl x (List.mem_cons_of_mem _ hx))
  refine h _ 2 (by norm_num) ?_
  intro x hx
  simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨u, _, J, _, h | h⟩ := hx <;> rw [h] <;> exact Rat.den_pos _

theorem ACell.modulus_pos (c : ACell) (h : c.y c.ky ≠ 0) : 0 < c.modulus := by
  unfold ACell.modulus
  exact Nat.mul_pos (ZmB_pos _ _) (Int.natAbs_pos.mpr h)

/-- A prime above the modulus is coprime to it. -/
theorem ACell.coprime_of_gt (c : ACell) (h : c.y c.ky ≠ 0) {p : ℕ} (hp : p.Prime)
    (hlt : c.modulus < p) : Nat.Coprime p c.modulus := by
  rw [Nat.coprime_comm, Nat.Coprime]
  rw [← Nat.coprime_iff_gcd_eq_one]
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  have := Nat.le_of_dvd (c.modulus_pos h) hd
  omega

end
end CatalanMeasure.GenD.Uniform.W.Lucas
