module
public import CatalanCore.Uniform.Content.RankCertificate
public import Mathlib.Algebra.BigOperators.Fin
@[expose] public section
set_option Elab.async false
set_option profiler true
namespace CatalanCore.Uniform.Content
open Matrix

def streamDot : List Int → List Int → Int
  | a::as,b::bs => a*b+streamDot as bs
  | _,_ => 0

theorem streamDot_eq_sum (n : Nat) (a b : List Int) (ha : a.length=n) (hb : b.length=n) :
    streamDot a b=∑ i : Fin n, a.getD i.val 0*b.getD i.val 0 := by
  induction n generalizing a b with
  | zero => simp only [List.length_eq_zero_iff.mp ha,List.length_eq_zero_iff.mp hb,streamDot,Fin.sum_univ_zero]
  | succ n ih =>
    cases a with
    | nil => simp at ha
    | cons x xs =>
      cases b with
      | nil => simp at hb
      | cons y ys =>
        simp only [List.length_cons,Nat.succ.injEq] at ha hb
        rw [Fin.sum_univ_succ]
        simpa only [streamDot,List.getD_cons_zero,List.getD_cons_succ,Fin.val_zero,Fin.val_succ]
          using congrArg (fun z => x*y+z) (ih xs ys ha hb)

def fromRows {m n : Nat} (a : Fin m → List Int) : Matrix (Fin m) (Fin n) Int :=
  fun i j => (a i).getD j.val 0
def fromColumns {m n : Nat} (a : Fin n → List Int) : Matrix (Fin m) (Fin n) Int :=
  fun i j => (a j).getD i.val 0

/-- Zip the actual coefficient tapes instead of repeatedly indexing every
coefficient in a flattened list. The checked identity is exactly matrix product. -/
theorem stream_factorization {m n d r : Nat}
    (B : Fin m → List Int) (V : Fin d → List Int)
    (C : Fin m → List Int) (T : Fin d → List Int)
    (hB : ∀ i, (B i).length=n) (hV : ∀ j, (V j).length=n)
    (hC : ∀ i, (C i).length=r) (hT : ∀ j, (T j).length=r)
    (hc : ∀ i j, streamDot (B i) (V j)=streamDot (C i) (T j)) :
    (fromRows B : Matrix (Fin m) (Fin n) Int)*fromColumns V=
      (fromRows C : Matrix (Fin m) (Fin r) Int)*fromColumns T := by
  ext i j
  change (∑ k : Fin n, (B i).getD k.val 0*(V j).getD k.val 0)=
    ∑ k : Fin r, (C i).getD k.val 0*(T j).getD k.val 0
  rw [←streamDot_eq_sum n (B i) (V j) (hB i) (hV j),
    ←streamDot_eq_sum r (C i) (T j) (hC i) (hT j)]
  exact hc i j

/-- A scaled left inverse uses the same streaming checker, without expanding
finite sums over repeatedly indexed literal matrices. -/
theorem stream_left_inverse {n d : Nat} (L : Fin d → List Int) (V : Fin d → List Int)
    (hL : ∀ i, (L i).length=n) (hV : ∀ j, (V j).length=n) (s : Int)
    (hc : ∀ i j, streamDot (L i) (V j)=if i=j then s else 0) :
    (fromRows L : Matrix (Fin d) (Fin n) Int)*fromColumns V=s • (1 : Matrix (Fin d) (Fin d) Int) := by
  ext i j
  change (∑ k : Fin n, (L i).getD k.val 0*(V j).getD k.val 0)=_
  rw [←streamDot_eq_sum n (L i) (V j) (hL i) (hV j),hc i j]
  by_cases h : i=j <;> simp [h,Matrix.one_apply,Matrix.smul_apply,smul_eq_mul]

#print axioms stream_factorization
end CatalanCore.Uniform.Content

