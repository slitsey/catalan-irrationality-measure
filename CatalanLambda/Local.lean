import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic

open Finset Matrix

namespace CatalanLambda

section Local
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- The ring of `ℓ`-integral rationals `ℤ_(ℓ)`. -/
def S : Subring ℚ where
  carrier := {q | ¬ ℓ ∣ q.den}
  mul_mem' := by
    intro a b ha hb h
    rcases (Nat.Prime.dvd_mul hℓ.out).1 (h.trans (Rat.mul_den_dvd a b)) with h | h
    · exact ha h
    · exact hb h
  one_mem' := by
    show ¬ ℓ ∣ (1:ℚ).den
    rw [Rat.den_one]; exact fun h => hℓ.out.ne_one (Nat.dvd_one.1 h)
  add_mem' := by
    intro a b ha hb h
    rcases (Nat.Prime.dvd_mul hℓ.out).1 (h.trans (Rat.add_den_dvd a b)) with h | h
    · exact ha h
    · exact hb h
  zero_mem' := by
    show ¬ ℓ ∣ (0:ℚ).den
    rw [Rat.den_zero]; exact fun h => hℓ.out.ne_one (Nat.dvd_one.1 h)
  neg_mem' := by intro a ha; simpa [Rat.neg_den] using ha

variable {ℓ}

lemma mem_S {q : ℚ} : q ∈ S ℓ ↔ ¬ ℓ ∣ q.den := Iff.rfl

lemma den_ne {q : ℚ} (hq : q ∈ S ℓ) : (q.den : ZMod ℓ) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]; exact hq

/-- Reduction mod `ℓ` of a rational (meaningful on `S ℓ`). -/
noncomputable def red (ℓ : ℕ) [Fact ℓ.Prime] (q : ℚ) : ZMod ℓ := (q : ZMod ℓ)

/-- `x` is `ℓ`-integral and reduces to `y`. -/
def Good (ℓ : ℕ) [Fact ℓ.Prime] (x : ℚ) (y : ZMod ℓ) : Prop := x ∈ S ℓ ∧ red ℓ x = y

lemma Good.mem {x : ℚ} {y : ZMod ℓ} (h : Good ℓ x y) : x ∈ S ℓ := h.1
lemma Good.eq {x : ℚ} {y : ZMod ℓ} (h : Good ℓ x y) : red ℓ x = y := h.2

lemma Good.add {x x' : ℚ} {y y' : ZMod ℓ} (h : Good ℓ x y) (h' : Good ℓ x' y') :
    Good ℓ (x + x') (y + y') :=
  ⟨(S ℓ).add_mem h.1 h'.1, by
    rw [← h.2, ← h'.2]; exact Rat.cast_add_of_ne_zero (den_ne h.1) (den_ne h'.1)⟩

lemma Good.mul {x x' : ℚ} {y y' : ZMod ℓ} (h : Good ℓ x y) (h' : Good ℓ x' y') :
    Good ℓ (x * x') (y * y') :=
  ⟨(S ℓ).mul_mem h.1 h'.1, by
    rw [← h.2, ← h'.2]; exact Rat.cast_mul_of_ne_zero (den_ne h.1) (den_ne h'.1)⟩

lemma Good.neg {x : ℚ} {y : ZMod ℓ} (h : Good ℓ x y) : Good ℓ (-x) (-y) :=
  ⟨(S ℓ).neg_mem h.1, by rw [← h.2]; simp [red]⟩

lemma Good.sub {x x' : ℚ} {y y' : ZMod ℓ} (h : Good ℓ x y) (h' : Good ℓ x' y') :
    Good ℓ (x - x') (y - y') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]; exact h.add h'.neg

lemma Good.zero : Good ℓ 0 0 := ⟨(S ℓ).zero_mem, by simp [red]⟩
lemma Good.one : Good ℓ 1 1 := ⟨(S ℓ).one_mem, by simp [red]⟩

lemma Good.natCast (n : ℕ) : Good ℓ (n : ℚ) (n : ZMod ℓ) :=
  ⟨natCast_mem (S ℓ) n, by simp [red]⟩

lemma Good.intCast (n : ℤ) : Good ℓ (n : ℚ) (n : ZMod ℓ) :=
  ⟨intCast_mem (S ℓ) n, by simp [red]⟩

lemma Good.ofNat (n : ℕ) [n.AtLeastTwo] : Good ℓ (OfNat.ofNat n : ℚ) (OfNat.ofNat n : ZMod ℓ) := by
  rw [← Nat.cast_ofNat (R := ℚ) (n := n), ← Nat.cast_ofNat (R := ZMod ℓ) (n := n)]
  exact Good.natCast _

lemma Good.inv {x : ℚ} {y : ZMod ℓ} (h : Good ℓ x y) (hy : y ≠ 0) :
    Good ℓ x⁻¹ y⁻¹ := by
  have hx0 : x ≠ 0 := by
    rintro rfl; apply hy; rw [← h.2]; simp [red]
  have hmem : x⁻¹ ∈ S ℓ := by
    show ¬ ℓ ∣ (x⁻¹).den
    rw [Rat.den_inv_of_ne_zero hx0]
    intro hd
    apply hy
    rw [← h.2, red, Rat.cast_def]
    have : (x.num : ZMod ℓ) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact Int.natCast_dvd.2 hd
    rw [this]; simp
  refine ⟨hmem, ?_⟩
  have h1 : Good ℓ (x * x⁻¹) 1 := by
    rw [mul_inv_cancel₀ hx0]; exact Good.one
  have h2 : red ℓ (x * x⁻¹) = y * red ℓ x⁻¹ := (h.mul ⟨hmem, rfl⟩).2
  rw [h1.2] at h2
  exact eq_inv_of_mul_eq_one_right h2.symm

lemma Good.div {x z : ℚ} {y w : ZMod ℓ} (h : Good ℓ x y) (h' : Good ℓ z w) (hw : w ≠ 0) :
    Good ℓ (x / z) (y / w) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]; exact h.mul (h'.inv hw)

lemma Good.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (g : ι → ZMod ℓ)
    (h : ∀ i ∈ s, Good ℓ (f i) (g i)) : Good ℓ (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Good.zero (ℓ := ℓ))
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma Good.congr {x : ℚ} {y y' : ZMod ℓ} (h : Good ℓ x y) (e : y = y') : Good ℓ x y' := e ▸ h
lemma Good.congr' {x x' : ℚ} {y : ZMod ℓ} (h : Good ℓ x y) (e : x = x') : Good ℓ x' y := e ▸ h

/-- Reduction commutes with determinants of `ℓ`-integral matrices. -/
lemma red_det {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι ℚ)
    (y : Matrix ι ι (ZMod ℓ)) (hN : ∀ i j, Good ℓ (N i j) (y i j)) :
    Good ℓ N.det y.det := by
  let ψ : S ℓ →+* ZMod ℓ :=
    { toFun := fun q => red ℓ q.1
      map_one' := Good.one.2
      map_mul' := fun a b => ((show Good ℓ a.1 (red ℓ a.1) from ⟨a.2, rfl⟩).mul ((show Good ℓ b.1 (red ℓ b.1) from ⟨b.2, rfl⟩))).2
      map_zero' := Good.zero.2
      map_add' := fun a b => ((show Good ℓ a.1 (red ℓ a.1) from ⟨a.2, rfl⟩).add ((show Good ℓ b.1 (red ℓ b.1) from ⟨b.2, rfl⟩))).2 }
  let N' : Matrix ι ι (S ℓ) := Matrix.of fun i j => ⟨N i j, (hN i j).1⟩
  have h1 : N'.map (S ℓ).subtype = N := by ext i j; rfl
  have h2 : ψ.mapMatrix N' = y := by ext i j; exact (hN i j).2
  have h3 : N.det = ((N'.det : S ℓ) : ℚ) := by
    rw [← h1]; exact (RingHom.map_det (S ℓ).subtype N').symm
  refine ⟨?_, ?_⟩
  · rw [h3]; exact (N'.det).2
  · rw [h3, ← h2]; exact RingHom.map_det ψ N'

end Local

end CatalanLambda
