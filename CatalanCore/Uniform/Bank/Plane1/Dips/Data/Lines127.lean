module

public import CatalanCore.Uniform.Bank.Plane1.Dips.Bridge

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! # Dip frame (1, -2, 1): the lines and bridges of the used catalogue (wave R1b; ledger R01-R03)

The dip lines (`DipLine`) and the max-bridges (`DipBridge`) that the head certificates of the frame use, and for each
bridge **the membership theorem for every `p`** (`DipBridge.Member ρ`, `ρ = 1, 2`): the window, class and plane facts imply
the conditions of the line of one of the configurations that occur in the window (omega over the finite list). -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.F127
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Uniform
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.KTerm
  CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanCore.Uniform.Bank.Plane1 CatalanCore.Measure CatalanFrames.P6 CatalanCore.Uniform.Bank.Plane1.Dips

def ln16 : DipLine := ⟨1, 2, 2, 2, 0, 3, 1, [1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2], [1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2], 38, 0, 14, 21⟩

def ln19 : DipLine := ⟨1, 1, 2, 3, 0, 1, 2, [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 2, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 0, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], 40, 0, 16, 21⟩

def ln22 : DipLine := ⟨1, 1, 1, 0, 1, 2, 3, [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2], [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2], 26, 0, 4, 12⟩

def ln24 : DipLine := ⟨1, 1, 1, 0, 2, 1, 3, [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2], [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 1, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 1, 2, 2], 38, 0, 13, 19⟩

def ln25 : DipLine := ⟨1, 1, 1, 2, 0, 1, 3, [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 0, 2, 1, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 0, 2, 1, 2, 2], 38, 0, 13, 19⟩

def ln27 : DipLine := ⟨1, 1, 1, 2, 0, 3, 1, [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2], [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 0, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 0, 2, 2, 2, 2], 24, 0, 4, 12⟩

def ln28 : DipLine := ⟨1, 1, 1, 2, 3, 0, 1, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2], [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2, 2], 24, 0, 4, 12⟩

def ln29 : DipLine := ⟨1, 0, 1, 3, 0, 1, 2, [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 0, 2, 2, 2, 2, 2, 2, 2, 2], 12, 2, 0, 5⟩

def ln61 : DipLine := ⟨2, 1, 1, 1, 2, 0, 3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 1, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 1, 2, 2], 38, 0, 10, 19⟩

def ln63 : DipLine := ⟨2, 1, 1, 2, 1, 3, 0, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 0, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 0, 2, 2, 2, 2], 12, 9, 0, 8⟩

def lx0 : DipLine := ⟨1, 2, 2, 2, 3, 0, 1, [2, 2, 0, 1, 2, 2, 1, 1, 1, 1, 2, 2, 0, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 1, 0, 2, 2, 1, 1, 1, 1, 2, 2, 2, 0, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2], 40, 0, 16, 28⟩

/-- The bridge at the type boundary `p / r = 1/2`. -/
def br15 : DipBridge := ⟨1, 9999, 20000, 10001, 20000, [ln16, ln19, lx0]⟩

theorem br15_member (ρ : ℕ) : br15.Member ρ := by
  intro hρ1 hρ2 r p m kv hf hc
  obtain ⟨hr, hr0, hp, ⟨hm1, hm2⟩, hm3, ⟨jA, eA, jA0, jA3, kA0, kAp⟩, ⟨jB, eB, jB0, jB2, kB0, kBp⟩⟩ := hf
  have jB1 : jB = 1 := by omega
  subst jB1
  have jAc : jA = 1 ∨ jA = 2 := by omega
  rcases jAc with rfl | rfl <;>
  simp only [DipBridge.toBranch, br15, ln16, ln19, lx0, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, DipLine.classCond, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] at hc <;>
  simp only [br15, ln16, ln19, lx0, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, DipLine.conds, DipLine.classCond, DipLine.chainCond, DipLine.lVec, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] <;>
  by_cases hsm : kv 1 < 30 <;>
  first
  | omega
  | (have hc4 : kv 1 = 4 ∨ kv 1 = 5 ∨ kv 1 = 6 ∨ kv 1 = 7 ∨ kv 1 = 8 ∨ kv 1 = 9 ∨ kv 1 = 10 ∨ kv 1 = 11 ∨ kv 1 = 12 ∨ kv 1 = 13 ∨ kv 1 = 14 ∨ kv 1 = 15 ∨ kv 1 = 16 ∨ kv 1 = 17 ∨ kv 1 = 18 ∨ kv 1 = 19 ∨ kv 1 = 20 ∨ kv 1 = 21 ∨ kv 1 = 22 ∨ kv 1 = 23 ∨ kv 1 = 24 ∨ kv 1 = 25 ∨ kv 1 = 26 ∨ kv 1 = 27 ∨ kv 1 = 28 ∨ kv 1 = 29 := by omega
     rcases hc4 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega)

/-- The bridge at the type boundary `p / r = 7/12`. -/
def br18 : DipBridge := ⟨1, 23331, 40000, 70007, 120000, [ln19, ln22]⟩

theorem br18_member (ρ : ℕ) : br18.Member ρ := by
  intro hρ1 hρ2 r p m kv hf hc
  obtain ⟨hr, hr0, hp, ⟨hm1, hm2⟩, hm3, ⟨jA, eA, jA0, jA3, kA0, kAp⟩, ⟨jB, eB, jB0, jB2, kB0, kBp⟩⟩ := hf
  have jB1 : jB = 1 := by omega
  subst jB1
  have jAc : jA = 1 ∨ jA = 2 := by omega
  rcases jAc with rfl | rfl <;>
  simp only [DipBridge.toBranch, br18, ln19, ln22, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, DipLine.classCond, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] at hc <;>
  simp only [br18, ln19, ln22, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, DipLine.conds, DipLine.classCond, DipLine.chainCond, DipLine.lVec, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] <;>
  by_cases hsm : kv 1 < 30 <;>
  first
  | omega
  | (have hc4 : kv 1 = 4 ∨ kv 1 = 5 ∨ kv 1 = 6 ∨ kv 1 = 7 ∨ kv 1 = 8 ∨ kv 1 = 9 ∨ kv 1 = 10 ∨ kv 1 = 11 ∨ kv 1 = 12 ∨ kv 1 = 13 ∨ kv 1 = 14 ∨ kv 1 = 15 ∨ kv 1 = 16 ∨ kv 1 = 17 ∨ kv 1 = 18 ∨ kv 1 = 19 ∨ kv 1 = 20 ∨ kv 1 = 21 ∨ kv 1 = 22 ∨ kv 1 = 23 ∨ kv 1 = 24 ∨ kv 1 = 25 ∨ kv 1 = 26 ∨ kv 1 = 27 ∨ kv 1 = 28 ∨ kv 1 = 29 := by omega
     rcases hc4 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega)

/-- The bridge at the type boundary `p / r = 2/3`. -/
def br21 : DipBridge := ⟨1, 3333, 5000, 10001, 15000, [ln24, ln22]⟩

theorem br21_member (ρ : ℕ) : br21.Member ρ := by
  intro hρ1 hρ2 r p m kv hf hc
  obtain ⟨hr, hr0, hp, ⟨hm1, hm2⟩, hm3, ⟨jA, eA, jA0, jA3, kA0, kAp⟩, ⟨jB, eB, jB0, jB2, kB0, kBp⟩⟩ := hf
  have jB1 : jB = 1 := by omega
  subst jB1
  have jAc : jA = 1 ∨ jA = 2 := by omega
  rcases jAc with rfl | rfl <;>
  simp only [DipBridge.toBranch, br21, ln24, ln22, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, DipLine.classCond, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] at hc <;>
  simp only [br21, ln24, ln22, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, DipLine.conds, DipLine.classCond, DipLine.chainCond, DipLine.lVec, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] <;>
  by_cases hsm : kv 1 < 30 <;>
  first
  | omega
  | (have hc4 : kv 1 = 4 ∨ kv 1 = 5 ∨ kv 1 = 6 ∨ kv 1 = 7 ∨ kv 1 = 8 ∨ kv 1 = 9 ∨ kv 1 = 10 ∨ kv 1 = 11 ∨ kv 1 = 12 ∨ kv 1 = 13 ∨ kv 1 = 14 ∨ kv 1 = 15 ∨ kv 1 = 16 ∨ kv 1 = 17 ∨ kv 1 = 18 ∨ kv 1 = 19 ∨ kv 1 = 20 ∨ kv 1 = 21 ∨ kv 1 = 22 ∨ kv 1 = 23 ∨ kv 1 = 24 ∨ kv 1 = 25 ∨ kv 1 = 26 ∨ kv 1 = 27 ∨ kv 1 = 28 ∨ kv 1 = 29 := by omega
     rcases hc4 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega)

/-- The bridge at the type boundary `p / r = 3/4`. -/
def br23 : DipBridge := ⟨1, 29997, 40000, 30003, 40000, [ln24, ln25]⟩

theorem br23_member (ρ : ℕ) : br23.Member ρ := by
  intro hρ1 hρ2 r p m kv hf hc
  obtain ⟨hr, hr0, hp, ⟨hm1, hm2⟩, hm3, ⟨jA, eA, jA0, jA3, kA0, kAp⟩, ⟨jB, eB, jB0, jB2, kB0, kBp⟩⟩ := hf
  have jB1 : jB = 1 := by omega
  subst jB1
  have jAc : jA = 1 ∨ jA = 2 := by omega
  rcases jAc with rfl | rfl <;>
  simp only [DipBridge.toBranch, br23, ln24, ln25, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, DipLine.classCond, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] at hc <;>
  simp only [br23, ln24, ln25, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, DipLine.conds, DipLine.classCond, DipLine.chainCond, DipLine.lVec, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] <;>
  by_cases hsm : kv 1 < 30 <;>
  first
  | omega
  | (have hc4 : kv 1 = 4 ∨ kv 1 = 5 ∨ kv 1 = 6 ∨ kv 1 = 7 ∨ kv 1 = 8 ∨ kv 1 = 9 ∨ kv 1 = 10 ∨ kv 1 = 11 ∨ kv 1 = 12 ∨ kv 1 = 13 ∨ kv 1 = 14 ∨ kv 1 = 15 ∨ kv 1 = 16 ∨ kv 1 = 17 ∨ kv 1 = 18 ∨ kv 1 = 19 ∨ kv 1 = 20 ∨ kv 1 = 21 ∨ kv 1 = 22 ∨ kv 1 = 23 ∨ kv 1 = 24 ∨ kv 1 = 25 ∨ kv 1 = 26 ∨ kv 1 = 27 ∨ kv 1 = 28 ∨ kv 1 = 29 := by omega
     rcases hc4 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega)

/-- The bridge at the type boundary `p / r = 7/9`. -/
def br24 : DipBridge := ⟨1, 7777, 10000, 70007, 90000, [ln25, ln27]⟩

theorem br24_member (ρ : ℕ) : br24.Member ρ := by
  intro hρ1 hρ2 r p m kv hf hc
  obtain ⟨hr, hr0, hp, ⟨hm1, hm2⟩, hm3, ⟨jA, eA, jA0, jA3, kA0, kAp⟩, ⟨jB, eB, jB0, jB2, kB0, kBp⟩⟩ := hf
  have jB1 : jB = 1 := by omega
  subst jB1
  have jAc : jA = 1 ∨ jA = 2 := by omega
  rcases jAc with rfl | rfl <;>
  simp only [DipBridge.toBranch, br24, ln25, ln27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, DipLine.classCond, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] at hc <;>
  simp only [br24, ln25, ln27, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, DipLine.conds, DipLine.classCond, DipLine.chainCond, DipLine.lVec, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] <;>
  by_cases hsm : kv 1 < 30 <;>
  first
  | omega
  | (have hc4 : kv 1 = 4 ∨ kv 1 = 5 ∨ kv 1 = 6 ∨ kv 1 = 7 ∨ kv 1 = 8 ∨ kv 1 = 9 ∨ kv 1 = 10 ∨ kv 1 = 11 ∨ kv 1 = 12 ∨ kv 1 = 13 ∨ kv 1 = 14 ∨ kv 1 = 15 ∨ kv 1 = 16 ∨ kv 1 = 17 ∨ kv 1 = 18 ∨ kv 1 = 19 ∨ kv 1 = 20 ∨ kv 1 = 21 ∨ kv 1 = 22 ∨ kv 1 = 23 ∨ kv 1 = 24 ∨ kv 1 = 25 ∨ kv 1 = 26 ∨ kv 1 = 27 ∨ kv 1 = 28 ∨ kv 1 = 29 := by omega
     rcases hc4 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega)

/-- The bridge at the type boundary `p / r = 7/8`. -/
def br26 : DipBridge := ⟨1, 69993, 80000, 70007, 80000, [ln28, ln27]⟩

theorem br26_member (ρ : ℕ) : br26.Member ρ := by
  intro hρ1 hρ2 r p m kv hf hc
  obtain ⟨hr, hr0, hp, ⟨hm1, hm2⟩, hm3, ⟨jA, eA, jA0, jA3, kA0, kAp⟩, ⟨jB, eB, jB0, jB2, kB0, kBp⟩⟩ := hf
  have jB1 : jB = 1 := by omega
  subst jB1
  have jAc : jA = 1 ∨ jA = 2 := by omega
  rcases jAc with rfl | rfl <;>
  simp only [DipBridge.toBranch, br26, ln28, ln27, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, DipLine.classCond, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] at hc <;>
  simp only [br26, ln28, ln27, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, DipLine.conds, DipLine.classCond, DipLine.chainCond, DipLine.lVec, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] <;>
  by_cases hsm : kv 1 < 30 <;>
  first
  | omega
  | (have hc4 : kv 1 = 4 ∨ kv 1 = 5 ∨ kv 1 = 6 ∨ kv 1 = 7 ∨ kv 1 = 8 ∨ kv 1 = 9 ∨ kv 1 = 10 ∨ kv 1 = 11 ∨ kv 1 = 12 ∨ kv 1 = 13 ∨ kv 1 = 14 ∨ kv 1 = 15 ∨ kv 1 = 16 ∨ kv 1 = 17 ∨ kv 1 = 18 ∨ kv 1 = 19 ∨ kv 1 = 20 ∨ kv 1 = 21 ∨ kv 1 = 22 ∨ kv 1 = 23 ∨ kv 1 = 24 ∨ kv 1 = 25 ∨ kv 1 = 26 ∨ kv 1 = 27 ∨ kv 1 = 28 ∨ kv 1 = 29 := by omega
     rcases hc4 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega)

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.F127
