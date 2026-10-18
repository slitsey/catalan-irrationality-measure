module

public import CatalanCore.Linalg.Krylov
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# `ℓ`-adic units of `ℚ` and reduction mod `ℓ`

`Rl l` is the subring of `ℓ`-integral rationals (denominator prime to `ℓ`), `phi l : Rl l →+* ZMod l`
is reduction, and `LU l q` says `q` is a unit of `Rl l`.  A Krylov determinant that is an `ℓ`-unit
reduces to a nonzero element of `ZMod l`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.ThmA

variable (l : ℕ) [hl : Fact l.Prime]

/-- The `ℓ`-integral rationals. -/
def Rl : Subring ℚ where
  carrier := {q | ¬ l ∣ q.den}
  zero_mem' := by simpa using hl.out.not_dvd_one
  one_mem' := by simpa using hl.out.not_dvd_one
  add_mem' := by
    intro a b ha hb hab
    rcases (Nat.Prime.dvd_mul hl.out).1 (hab.trans (Rat.add_den_dvd a b)) with h | h
    · exact ha h
    · exact hb h
  mul_mem' := by
    intro a b ha hb hab
    rcases (Nat.Prime.dvd_mul hl.out).1 (hab.trans (Rat.mul_den_dvd a b)) with h | h
    · exact ha h
    · exact hb h
  neg_mem' := by intro a ha; simpa using ha

lemma mem_Rl {q : ℚ} : q ∈ Rl l ↔ ¬ l ∣ q.den := Iff.rfl

lemma den_cast_ne {q : ℚ} (h : q ∈ Rl l) : (q.den : ZMod l) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; exact h

/-- Reduction mod `ℓ`. -/
def phi : Rl l →+* ZMod l where
  toFun q := ((q : ℚ) : ZMod l)
  map_one' := by simp
  map_zero' := by simp
  map_mul' a b := Rat.cast_mul_of_ne_zero (den_cast_ne l a.2) (den_cast_ne l b.2)
  map_add' a b := Rat.cast_add_of_ne_zero (den_cast_ne l a.2) (den_cast_ne l b.2)

lemma phi_apply (q : Rl l) : phi l q = ((q : ℚ) : ZMod l) := rfl

/-- `q` is a unit of `Rl l`. -/
def LU (q : ℚ) : Prop := q ≠ 0 ∧ q ∈ Rl l ∧ q⁻¹ ∈ Rl l

variable {l}

lemma LU.mul {a b : ℚ} (ha : LU l a) (hb : LU l b) : LU l (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, (Rl l).mul_mem ha.2.1 hb.2.1, by
    rw [mul_inv]; exact (Rl l).mul_mem ha.2.2 hb.2.2⟩

lemma LU.inv {a : ℚ} (ha : LU l a) : LU l a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.2, by rw [inv_inv]; exact ha.2.1⟩

lemma LU.div {a b : ℚ} (ha : LU l a) (hb : LU l b) : LU l (a / b) := by
  rw [div_eq_mul_inv]; exact ha.mul hb.inv

lemma LU.neg {a : ℚ} (ha : LU l a) : LU l (-a) :=
  ⟨neg_ne_zero.2 ha.1, (Rl l).neg_mem ha.2.1, by rw [inv_neg]; exact (Rl l).neg_mem ha.2.2⟩

lemma LU.one : LU l 1 := ⟨one_ne_zero, (Rl l).one_mem, by simpa using (Rl l).one_mem⟩

lemma LU.pow {a : ℚ} (ha : LU l a) (n : ℕ) : LU l (a ^ n) := by
  induction n with
  | zero => simpa using LU.one
  | succ n ih => rw [pow_succ]; exact ih.mul ha

lemma LU.prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, LU l (f i)) :
    LU l (∏ i ∈ s, f i) :=
  Finset.prod_induction f (LU l) (fun _ _ => LU.mul) LU.one h

lemma LU_natCast {n : ℕ} (h0 : 0 < n) (hn : ¬ l ∣ n) : LU l (n : ℚ) := by
  refine ⟨by exact_mod_cast h0.ne', ?_, ?_⟩
  · rw [mem_Rl]; simpa using hl.out.not_dvd_one
  · rw [mem_Rl]; simpa [Rat.inv_natCast_den, h0.ne'] using hn

lemma LU_natCast_lt {n : ℕ} (h0 : 0 < n) (hn : n < l) : LU l (n : ℚ) :=
  LU_natCast h0 fun hd => absurd (Nat.le_of_dvd h0 hd) (by omega)

lemma LU_intCast_lt {z : ℤ} (h0 : z ≠ 0) (hz : z.natAbs < l) : LU l (z : ℚ) := by
  rcases Int.natAbs_eq z with h | h
  · have := LU_natCast_lt (l := l) (n := z.natAbs) (by omega) hz
    rw [h]; simpa using this
  · have := (LU_natCast_lt (l := l) (n := z.natAbs) (by omega) hz).neg
    rw [h]; simpa using this

/-- Reduction of an `ℓ`-unit Krylov determinant is nonzero. -/
theorem kdet_phi_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) (Rl l)) (v : Fin n → Rl l)
    (h : LU l (kdet (A.map (Rl l).subtype) ((Rl l).subtype ∘ v))) :
    kdet (A.map (phi l)) (phi l ∘ v) ≠ 0 := by
  have hd : ((kdet A v : Rl l) : ℚ) = kdet (A.map (Rl l).subtype) ((Rl l).subtype ∘ v) :=
    kdet_map (Rl l).subtype A v
  rw [← kdet_map (phi l) A v]
  have hd' : LU l ((kdet A v : Rl l) : ℚ) := by rw [hd]; exact h
  set d : Rl l := kdet A v
  let e : Rl l := ⟨((d : ℚ))⁻¹, hd'.2.2⟩
  have hde : d * e = 1 := Subtype.ext (mul_inv_cancel₀ hd'.1)
  have := congrArg (phi l) hde
  rw [map_mul, map_one] at this
  exact left_ne_zero_of_mul_eq_one this

end CatalanCore.ThmA
