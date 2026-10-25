module
public import CatalanCore.Cert.QuarterCompute.Polynomial
public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.PackedPolynomial
open CatalanCore.Cert.QuarterCompute.Polynomial

def Small (B : ℤ) (cs : List ℤ) : Prop := ∀ c ∈ cs, 2*|c| < B

/-- A single large-radix equality determines every bounded signed coefficient. -/
theorem eval_injective (B : ℤ) (hB : 0 < B) (xs ys : List ℤ)
    (hlen : xs.length = ys.length) (hx : Small B xs) (hy : Small B ys)
    (he : eval B xs = eval B ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      have hxx := hx x (by simp)
      have hyy := hy y (by simp)
      simp only [eval] at he
      have hd : B ∣ x-y := by
        refine ⟨eval B ys-eval B xs, ?_⟩
        nlinarith [he]
      have hab : |x-y| < B := (abs_sub x y).trans_lt (by linarith)
      have hab' : (x-y).natAbs < B.natAbs := by
        rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs, Int.natCast_natAbs,
          abs_of_pos hB]
        exact hab
      have hxy : x = y := sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hab')
      have htail : eval B xs = eval B ys := by
        have hm : B*eval B xs = B*eval B ys := by omega
        exact mul_left_cancel₀ (ne_of_gt hB) hm
      have heq : xs = ys := ih ys (Nat.succ.inj hlen)
        (fun c hc => hx c (by simp [hc])) (fun c hc => hy c (by simp [hc])) htail
      exact congrArg₂ List.cons hxy heq
end CatalanCore.Cert.QuarterContour.PackedPolynomial
#print axioms CatalanCore.Cert.QuarterContour.PackedPolynomial.eval_injective