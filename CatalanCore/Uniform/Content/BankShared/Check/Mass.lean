module

public import CatalanCore.Uniform.Content.BankShared.Check.Bank

@[expose] public section
set_option Elab.async false

/-! # The class check with precomputed template masses (lane C1L)

`classOK D a` (D1, D6) evaluates the mass of every template once per unit `c` and per member `a`.  For a bank with
long templates the masses can be proved once each (`T.mass α0 = m`, in the module of the template) and supplied as a
list `ms`; `classOK_of_masses` turns `classOK` into `classOKM`, which reads the masses from `ms` and is the same
Boolean test otherwise.  Nothing about the check changes. -/

namespace CatalanCore.Uniform.Content.BankShared.Check

/-- The supplied mass of the class `j` (`0` when missing). -/
def massOf (ms : List (ℕ × ℚ)) (j : ℕ) : ℚ :=
  match ms.find? (fun x => x.1 == j) with
  | some x => x.2
  | none => 0

/-- `classMass` with the supplied masses. -/
def classMassM (D : BankData) (ms : List (ℕ × ℚ)) (a c : ℕ) : ℚ :=
  match jOf D.q a c with
  | some j => match findT j D.tmpls with
    | some _ => massOf ms j
    | none => 0
  | none => 0

/-- `classOK` with the supplied masses. -/
def classOKM (D : BankData) (ms : List (ℕ × ℚ)) (a : ℕ) : Bool :=
  decide (0 < a) && decide (a < D.q) && decide (Nat.gcd a D.q = 1) &&
    unitAll D.M (fun c => match jOf D.q a c with
      | some j => (findT j D.tmpls).isSome
      | none => false) D.M &&
    decide (unitSum D.M (classMassM D ms a) D.M = D.Λ * unitCount D.M D.M)

theorem classMass_eq_M (D : BankData) (ms : List (ℕ × ℚ))
    (hm : ∀ x ∈ D.tmpls, x.2.mass D.α0 = massOf ms x.1) (a : ℕ) :
    classMass D a = classMassM D ms a := by
  funext c
  unfold classMass classMassM
  cases hj : jOf D.q a c with
  | none => rfl
  | some j =>
    try dsimp only
    cases h : findT j D.tmpls with
    | none => rfl
    | some T => exact hm (j, T) (findT_mem j D.tmpls h)

/-- **Masses supplied**: `classOK D a = classOKM D ms a` when every template's mass is the supplied one. -/
theorem classOK_of_masses (D : BankData) (ms : List (ℕ × ℚ))
    (hm : ∀ x ∈ D.tmpls, x.2.mass D.α0 = massOf ms x.1) (a : ℕ) : classOK D a = classOKM D ms a := by
  unfold classOK classOKM
  rw [classMass_eq_M D ms hm a]
  rfl

end CatalanCore.Uniform.Content.BankShared.Check
