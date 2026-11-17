module

public import CatalanCore.Li2.Content.Rate
public import CatalanCore.Li2.Port.Unified.Modular.Base.Valuation
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Data.Int.Order.Units
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-! Local rational-parameter prime cases and valuations, rows C0/C1. -/
open Polynomial Finset Filter
open scoped Topology BigOperators
open CatalanCore.Li2.Port

namespace CatalanCore.Li2.Content

def lam (a b : ℤ) : ℚ := (a : ℚ) / b

def v (p : ℕ) (a : ℤ) : ℚ := padicValRat p (a : ℚ)

def L (p n : ℕ) : ℚ := Nat.log p (7 * n - 2)

def phi (n k : ℕ) : ℚ := max ((k : ℚ) - n + 1) 0

def S (n : ℕ) : ℚ := ∑ i ∈ range (2 * n), phi n (2 * i)

noncomputable def exceptional (a b : ℤ) : Finset ℕ :=
  (a * b * (b - a)).natAbs.primeFactors


theorem prime_cases (p : ℕ) [Fact p.Prime] (a b : ℤ)
    (hab : IsCoprime a b) (ha : a ≠ 0) (hb : b ≠ 0) (hba : b - a ≠ 0) :
    ((p : ℤ) ∣ a ∧ ¬ (p : ℤ) ∣ b ∧ ¬ (p : ℤ) ∣ b - a ∧
      v p b = 0 ∧ v p (b - a) = 0) ∨
    ((p : ℤ) ∣ b ∧ ¬ (p : ℤ) ∣ a ∧ ¬ (p : ℤ) ∣ b - a ∧
      v p a = 0 ∧ v p (b - a) = 0) ∨
    ((p : ℤ) ∣ b - a ∧ ¬ (p : ℤ) ∣ a ∧ ¬ (p : ℤ) ∣ b ∧
      v p a = 0 ∧ v p b = 0) ∨
    (¬ (p : ℤ) ∣ a ∧ ¬ (p : ℤ) ∣ b ∧ ¬ (p : ℤ) ∣ b - a ∧
      v p a = 0 ∧ v p b = 0 ∧ v p (b - a) = 0) := by
  have hprime : p.Prime := Fact.out
  have hnu : ¬ IsUnit (p : ℤ) := by
    intro h
    exact hprime.ne_one (by simpa using Int.isUnit_iff_natAbs_eq.mp h)
  have hz (z : ℤ) (h : ¬ (p : ℤ) ∣ z) : v p z = 0 := by
    change (padicValRat p (z : ℚ) : ℚ) = 0
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd h]
    norm_num
  by_cases hpa : (p : ℤ) ∣ a
  · have hpb : ¬ (p : ℤ) ∣ b := fun h => hnu (hab.isUnit_of_dvd' hpa h)
    have hpba : ¬ (p : ℤ) ∣ b - a := by
      intro h
      apply hpb
      simpa only [sub_add_cancel] using dvd_add h hpa
    exact Or.inl ⟨hpa, hpb, hpba, hz b hpb, hz (b - a) hpba⟩
  · by_cases hpb : (p : ℤ) ∣ b
    · have hpba : ¬ (p : ℤ) ∣ b - a := by
        intro h
        apply hpa
        simpa only [sub_sub_cancel] using dvd_sub hpb h
      exact Or.inr (Or.inl ⟨hpb, hpa, hpba, hz a hpa, hz (b - a) hpba⟩)
    · by_cases hpba : (p : ℤ) ∣ b - a
      · exact Or.inr (Or.inr (Or.inl ⟨hpba, hpa, hpb, hz a hpa, hz b hpb⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hpa, hpb, hpba, hz a hpa, hz b hpb,
          hz (b - a) hpba⟩))

theorem parameter_valuations (p : ℕ) [Fact p.Prime] (a b : ℤ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hba : b - a ≠ 0) :
    (padicValRat p (lam a b) : ℚ) = v p a - v p b ∧
    (padicValRat p (lam a b)⁻¹ : ℚ) = v p b - v p a ∧
    (padicValRat p (lam a b / (1 - lam a b)) : ℚ) = v p a - v p (b - a) := by
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hbaq : ((b - a : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hba
  have hdiff : (b : ℚ) - (a : ℚ) ≠ 0 := by exact_mod_cast hba
  have hfirst : (padicValRat p (lam a b) : ℚ) = v p a - v p b := by
    dsimp [lam, v]
    rw [padicValRat.div haq hbq]
    push_cast <;> rfl
  have hr : lam a b / (1 - lam a b) = (a : ℚ) / ((b - a : ℤ) : ℚ) := by
    dsimp [lam]
    push_cast
    field_simp [hbq, hdiff] <;> ring
  refine ⟨hfirst, ?_, ?_⟩
  · rw [padicValRat.inv]
    push_cast
    rw [hfirst]
    ring
  · rw [hr]
    dsimp [v]
    rw [padicValRat.div haq hbaq]
    push_cast <;> rfl

theorem parameter_units (p : ℕ) [Fact p.Prime] (a b : ℤ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hba : b - a ≠ 0)
    (hp : ¬ (p : ℤ) ∣ a * b * (b - a)) :
    CatalanCore.Li2.Port.Li2.VG p (lam a b) 0 ∧
      CatalanCore.Li2.Port.Li2.VG p (lam a b)⁻¹ 0 ∧
      CatalanCore.Li2.Port.Li2.VG p (lam a b / (1 - lam a b)) 0 ∧
      ((lam a b ≠ 0 ∧ padicValRat p (lam a b) = 0) ∧
        (1 - lam a b ≠ 0 ∧ padicValRat p (1 - lam a b) = 0)) := by
  have hpa : ¬ (p : ℤ) ∣ a := by
    intro h
    exact hp (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h b) (b - a))
  have hpb : ¬ (p : ℤ) ∣ b := by
    intro h
    exact hp (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h a) (b - a))
  have hpba : ¬ (p : ℤ) ∣ b - a := by
    intro h
    exact hp (dvd_mul_of_dvd_right h (a * b))
  have hz (z : ℤ) (h : ¬ (p : ℤ) ∣ z) : padicValRat p (z : ℚ) = 0 := by
    rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd h]
    rfl
  have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  have hbaq : ((b - a : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hba
  have hl0 : lam a b ≠ 0 := div_ne_zero haq hbq
  have hlv : padicValRat p (lam a b) = 0 := by
    dsimp [lam]
    rw [padicValRat.div haq hbq, hz a hpa, hz b hpb]
    rfl
  have h1eq : 1 - lam a b = ((b - a : ℤ) : ℚ) / (b : ℚ) := by
    dsimp [lam]
    push_cast
    field_simp [hbq] <;> ring
  have h1ne : 1 - lam a b ≠ 0 := by
    rw [h1eq]
    exact div_ne_zero hbaq hbq
  have h1v : padicValRat p (1 - lam a b) = 0 := by
    rw [h1eq, padicValRat.div hbaq hbq, hz (b - a) hpba, hz b hpb]
    rfl
  have hiv : padicValRat p (lam a b)⁻¹ = 0 := by
    rw [padicValRat.inv, hlv]
    rfl
  have hrv : padicValRat p (lam a b / (1 - lam a b)) = 0 := by
    rw [padicValRat.div hl0 h1ne, hlv, h1v]
    rfl
  have hVG (x : ℚ) (h : padicValRat p x = 0) :
      CatalanCore.Li2.Port.Li2.VG p x 0 := by
    right
    rw [h]
    norm_num
  exact ⟨hVG _ hlv, hVG _ hiv, hVG _ hrv, ⟨hl0, hlv⟩, ⟨h1ne, h1v⟩⟩

end CatalanCore.Li2.Content

#print axioms CatalanCore.Li2.Content.prime_cases
#print axioms CatalanCore.Li2.Content.parameter_valuations
#print axioms CatalanCore.Li2.Content.parameter_units
