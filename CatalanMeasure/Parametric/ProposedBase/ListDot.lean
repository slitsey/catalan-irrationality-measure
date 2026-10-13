module
public import CatalanMeasure.Parametric.ProposedBase.Definitions
@[expose] public section
namespace CatalanMeasure.Parametric.ProposedBase
open Finset

def intDot : List ℤ → List ℤ → ℤ
  | x::xs,y::ys =>x*y+intDot xs ys
  | _,_ =>0

theorem intDot_eq_sum_fin {n : ℕ} (xs ys : List ℤ) (hx : xs.length≤n) (hy : ys.length≤n) :
    intDot xs ys=∑ i : Fin n,xs.getD i.val 0*ys.getD i.val 0 := by
  induction n generalizing xs ys with
  | zero =>
    have hx' : xs=[] := List.length_eq_zero_iff.mp (by omega)
    have hy' : ys=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    subst ys
    simp [intDot]
  | succ n ih =>
    cases xs with
    | nil =>simp [intDot]
    | cons x xs =>
      cases ys with
      | nil =>simp [intDot]
      | cons y ys =>
        have hx' : xs.length≤n := by simp only [List.length_cons] at hx;omega
        have hy' : ys.length≤n := by simp only [List.length_cons] at hy;omega
        rw [Fin.sum_univ_succ]
        simp only [intDot,List.getD_cons_zero,List.getD_cons_succ,Fin.val_zero,Fin.val_succ]
        rw [ih xs ys hx' hy']

end CatalanMeasure.Parametric.ProposedBase
