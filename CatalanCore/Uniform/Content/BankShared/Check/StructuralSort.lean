module

public import Mathlib.Data.List.Sort

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1200000

/-! Structural sorting for kernel computations, with exact equality to core sorting.
No order laws, distinctness or inhabited element assumptions are needed. -/
namespace CatalanCore.Uniform.Content.BankShared.Check
universe u

def mergeFuel {α : Type u} (le : α → α → Bool) : ℕ → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | n+1, x::xs, y::ys =>
    if le x y then x::mergeFuel le n xs (y::ys) else y::mergeFuel le n (x::xs) ys

theorem mergeFuel_eq_merge {α : Type u} (le : α → α → Bool) (fuel : ℕ) (xs ys : List α)
    (h : xs.length+ys.length≤fuel) : mergeFuel le fuel xs ys=List.merge xs ys le := by
  induction fuel generalizing xs ys with
  | zero =>
      have hx : xs=[] := List.length_eq_zero_iff.mp (by omega)
      have hy : ys=[] := List.length_eq_zero_iff.mp (by omega)
      subst xs;subst ys;simp [mergeFuel]
  | succ n ih =>
      cases xs with
      | nil => simp [mergeFuel]
      | cons x xs =>
          cases ys with
          | nil => simp [mergeFuel]
          | cons y ys =>
              simp only [mergeFuel,List.cons_merge_cons]
              split <;> congr 1 <;> apply ih <;>
                simp only [List.length_cons] at h ⊢ <;> omega

def sortFuel {α : Type u} (le : α → α → Bool) : ℕ → List α → List α
  | 0, xs => xs
  | _+1, [] => []
  | _+1, [x] => [x]
  | n+1, x::y::xs =>
    let all := x::y::xs
    let k := (all.length+1)/2
    let l := all.take k
    let r := all.drop k
    mergeFuel le (l.length+r.length) (sortFuel le n l) (sortFuel le n r)

theorem sortFuel_eq_mergeSort {α : Type u} (le : α → α → Bool) (fuel : ℕ) (xs : List α)
    (h : xs.length≤fuel) : sortFuel le fuel xs=xs.mergeSort le := by
  induction fuel generalizing xs with
  | zero =>
      have hx : xs=[] := List.length_eq_zero_iff.mp (by omega)
      subst xs;simp [sortFuel]
  | succ n ih =>
      cases xs with
      | nil => simp [sortFuel]
      | cons x xs =>
          cases xs with
          | nil => simp [sortFuel]
          | cons y xs =>
              have hl : ((x::y::xs).take (((x::y::xs).length+1)/2)).length≤n := by
                simp only [List.length_take,List.length_cons] at h ⊢
                omega
              have hr : ((x::y::xs).drop (((x::y::xs).length+1)/2)).length≤n := by
                simp only [List.length_drop,List.length_cons] at h ⊢
                omega
              rw [sortFuel,ih _ hl,ih _ hr]
              rw [mergeFuel_eq_merge le _ _ _ (by simp only [List.length_mergeSort];exact le_rfl)]
              have hb1 : ((x::y::xs).drop (((x::y::xs).length+1)/2)).length≤
                  ((x::y::xs).take (((x::y::xs).length+1)/2)).length := by
                simp only [List.length_take,List.length_drop,List.length_cons]
                omega
              have hb2 : ((x::y::xs).take (((x::y::xs).length+1)/2)).length≤
                  ((x::y::xs).drop (((x::y::xs).length+1)/2)).length+1 := by
                simp only [List.length_take,List.length_drop,List.length_cons]
                omega
              rw [←List.mergeSort_append _ _ hb1 hb2,List.take_append_drop]


end CatalanCore.Uniform.Content.BankShared.Check
#print axioms CatalanCore.Uniform.Content.BankShared.Check.mergeFuel_eq_merge
#print axioms CatalanCore.Uniform.Content.BankShared.Check.sortFuel_eq_mergeSort
