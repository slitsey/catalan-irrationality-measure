module
public import CatalanCore.Cert.QuarterCompute.ModelDefs
@[expose] public section
namespace CatalanCore.Cert.QuarterCompute.Model
open CatalanCore.Cert.QuarterCompute.Polynomial

theorem inputsOK_append (S : Nat) (m : Params) (ps qs : List Pt) (js ks : List Jet)
    (hlen : ps.length = js.length) :
    inputsOK S m (ps++qs) (js++ks) = (inputsOK S m ps js && inputsOK S m qs ks) := by
  induction ps generalizing js with
  | nil => cases js with
    | nil => rfl
    | cons j js => contradiction
  | cons p ps ih =>
    cases js with
    | nil => contradiction
    | cons j js =>
      simp only [List.cons_append,inputsOK]
      rw [ih js (Nat.succ.inj hlen)]
      exact (Bool.and_assoc _ _ _).symm

theorem baseSum_append (m : Params) (xs ys : List Pt) :
    baseSum m (xs++ys) = baseSum m xs+baseSum m ys := by
  induction xs with
  | nil => exact (Int.zero_add _).symm
  | cons p ps ih =>
    change (p.2.2 : Int)*logUpS (centreArg m p)+baseSum m (ps++ys) =
      ((p.2.2 : Int)*logUpS (centreArg m p)+baseSum m ps)+baseSum m ys
    rw [ih]
    exact (Int.add_assoc _ _ _).symm

theorem errorSum_append (S : Nat) (xs ys : List Jet) :
    errorSum S (xs++ys) = errorSum S xs+errorSum S ys := by
  induction xs with
  | nil => exact (Nat.zero_add _).symm
  | cons p ps ih =>
    change errorCeil S p+errorSum S (ps++ys) = (errorCeil S p+errorSum S ps)+errorSum S ys
    rw [ih]
    exact (Nat.add_assoc _ _ _).symm
end CatalanCore.Cert.QuarterCompute.Model
namespace CatalanCore.Cert.QuarterCompute.Polynomial

theorem packedSum_append (factors : List Int) (B : Int) (xs ys : List Jet) :
    packedSum factors B (xs++ys) = packedSum factors B xs+packedSum factors B ys := by
  induction xs with
  | nil => exact (Int.zero_add _).symm
  | cons p ps ih =>
    change (p.2.2 : Int)*eval (p.1*B+p.2.1*B^2) factors+packedSum factors B (ps++ys) =
      ((p.2.2 : Int)*eval (p.1*B+p.2.1*B^2) factors+packedSum factors B ps)+packedSum factors B ys
    rw [ih]
    exact (Int.add_assoc _ _ _).symm
end CatalanCore.Cert.QuarterCompute.Polynomial