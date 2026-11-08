module

public import CatalanCore.Uniform.Bank.Plane1.Dips.Bridge

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

/-! # Dip frame (2, -1, -1): the lines and bridges of the used catalogue (wave R1b; ledger R01-R03)

The dip lines (`DipLine`) and the max-bridges (`DipBridge`) that the head certificates of the frame use, and for each
bridge **the membership theorem for every `p`** (`DipBridge.Member ρ`, `ρ = 1, 2`): the window, class and plane facts imply
the conditions of the line of one of the configurations that occur in the window (omega over the finite list). -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.F227
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Uniform
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.KTerm
  CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanCore.Uniform.Bank.Plane1 CatalanCore.Measure CatalanFrames.P6 CatalanCore.Uniform.Bank.Plane1.Dips

def ln27 : DipLine := ⟨1, 1, 1, 0, 2, 1, 3, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 1, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 1, 2, 2], 38, 0, 9, 19⟩

def ln29 : DipLine := ⟨1, 1, 1, 2, 0, 3, 1, [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2], [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 0, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 0, 2, 2, 2, 2], 12, 8, 0, 8⟩

def ln59 : DipLine := ⟨2, 2, 2, 2, 1, 3, 0, [1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2], [1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2], 38, 0, 15, 21⟩

def ln60 : DipLine := ⟨2, 2, 2, 2, 3, 1, 0, [0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 2, 0, 2, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2], [0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 2, 0, 2, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2], 52, 0, 30, 29⟩

def ln63 : DipLine := ⟨2, 1, 2, 3, 1, 0, 2, [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 2, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 0, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], 40, 0, 18, 21⟩

def ln64 : DipLine := ⟨2, 1, 1, 1, 0, 2, 3, [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2], [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2], 26, 0, 6, 12⟩

def ln66 : DipLine := ⟨2, 1, 1, 1, 2, 0, 3, [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2], [0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 1, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 1, 2, 2], 38, 0, 16, 19⟩

def ln67 : DipLine := ⟨2, 1, 1, 2, 1, 0, 3, [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 0, 2, 1, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 0, 2, 1, 2, 2], 38, 0, 16, 19⟩

def ln69 : DipLine := ⟨2, 1, 1, 2, 1, 3, 0, [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2], [0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 0, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 0, 2, 2, 2, 2], 24, 0, 6, 12⟩

def ln72 : DipLine := ⟨2, 1, 1, 2, 3, 1, 0, [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2], [0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2, 2], 24, 0, 6, 12⟩

def ln73 : DipLine := ⟨2, 0, 1, 3, 1, 0, 2, [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2], [2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 0, 2, 2, 2, 2, 2, 2, 2, 2], 12, 0, 0, 5⟩

/-- The bridge at the type boundary `p / r = 7/15`. -/
def br50 : DipBridge := ⟨2, 23331, 50000, 70007, 150000, [ln60, ln59]⟩

theorem br50_member (ρ : ℕ) : br50.Member ρ := by
  intro hρ1 hρ2 r p m kv hf hc
  obtain ⟨hr, hr0, hp, ⟨hm1, hm2⟩, hm3, ⟨jA, eA, jA0, jA3, kA0, kAp⟩, ⟨jB, eB, jB0, jB2, kB0, kBp⟩⟩ := hf
  have jB1 : jB = 1 := by omega
  subst jB1
  have jAc : jA = 1 ∨ jA = 2 := by omega
  rcases jAc with rfl | rfl <;>
  simp only [DipBridge.toBranch, br50, ln60, ln59, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, DipLine.classCond, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] at hc <;>
  simp only [br50, ln60, ln59, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, DipLine.conds, DipLine.classCond, DipLine.chainCond, DipLine.lVec, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] <;>
  by_cases hsm : kv 1 < 30 <;>
  first
  | omega
  | (have hc4 : kv 1 = 4 ∨ kv 1 = 5 ∨ kv 1 = 6 ∨ kv 1 = 7 ∨ kv 1 = 8 ∨ kv 1 = 9 ∨ kv 1 = 10 ∨ kv 1 = 11 ∨ kv 1 = 12 ∨ kv 1 = 13 ∨ kv 1 = 14 ∨ kv 1 = 15 ∨ kv 1 = 16 ∨ kv 1 = 17 ∨ kv 1 = 18 ∨ kv 1 = 19 ∨ kv 1 = 20 ∨ kv 1 = 21 ∨ kv 1 = 22 ∨ kv 1 = 23 ∨ kv 1 = 24 ∨ kv 1 = 25 ∨ kv 1 = 26 ∨ kv 1 = 27 ∨ kv 1 = 28 ∨ kv 1 = 29 := by omega
     rcases hc4 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega)

/-- The bridge at the type boundary `p / r = 7/12`. -/
def br54 : DipBridge := ⟨2, 23331, 40000, 70007, 120000, [ln63, ln64]⟩

theorem br54_member (ρ : ℕ) : br54.Member ρ := by
  intro hρ1 hρ2 r p m kv hf hc
  obtain ⟨hr, hr0, hp, ⟨hm1, hm2⟩, hm3, ⟨jA, eA, jA0, jA3, kA0, kAp⟩, ⟨jB, eB, jB0, jB2, kB0, kBp⟩⟩ := hf
  have jB1 : jB = 1 := by omega
  subst jB1
  have jAc : jA = 1 ∨ jA = 2 := by omega
  rcases jAc with rfl | rfl <;>
  simp only [DipBridge.toBranch, br54, ln63, ln64, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, DipLine.classCond, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] at hc <;>
  simp only [br54, ln63, ln64, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, DipLine.conds, DipLine.classCond, DipLine.chainCond, DipLine.lVec, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] <;>
  by_cases hsm : kv 1 < 30 <;>
  first
  | omega
  | (have hc4 : kv 1 = 4 ∨ kv 1 = 5 ∨ kv 1 = 6 ∨ kv 1 = 7 ∨ kv 1 = 8 ∨ kv 1 = 9 ∨ kv 1 = 10 ∨ kv 1 = 11 ∨ kv 1 = 12 ∨ kv 1 = 13 ∨ kv 1 = 14 ∨ kv 1 = 15 ∨ kv 1 = 16 ∨ kv 1 = 17 ∨ kv 1 = 18 ∨ kv 1 = 19 ∨ kv 1 = 20 ∨ kv 1 = 21 ∨ kv 1 = 22 ∨ kv 1 = 23 ∨ kv 1 = 24 ∨ kv 1 = 25 ∨ kv 1 = 26 ∨ kv 1 = 27 ∨ kv 1 = 28 ∨ kv 1 = 29 := by omega
     rcases hc4 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega)

/-- The bridge at the type boundary `p / r = 3/5`. -/
def br55 : DipBridge := ⟨2, 29997, 50000, 30003, 50000, [ln64, ln66]⟩

theorem br55_member (ρ : ℕ) : br55.Member ρ := by
  intro hρ1 hρ2 r p m kv hf hc
  obtain ⟨hr, hr0, hp, ⟨hm1, hm2⟩, hm3, ⟨jA, eA, jA0, jA3, kA0, kAp⟩, ⟨jB, eB, jB0, jB2, kB0, kBp⟩⟩ := hf
  have jB1 : jB = 1 := by omega
  subst jB1
  have jAc : jA = 1 ∨ jA = 2 := by omega
  rcases jAc with rfl | rfl <;>
  simp only [DipBridge.toBranch, br55, ln64, ln66, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, DipLine.classCond, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] at hc <;>
  simp only [br55, ln64, ln66, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, DipLine.conds, DipLine.classCond, DipLine.chainCond, DipLine.lVec, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] <;>
  by_cases hsm : kv 1 < 30 <;>
  first
  | omega
  | (have hc4 : kv 1 = 4 ∨ kv 1 = 5 ∨ kv 1 = 6 ∨ kv 1 = 7 ∨ kv 1 = 8 ∨ kv 1 = 9 ∨ kv 1 = 10 ∨ kv 1 = 11 ∨ kv 1 = 12 ∨ kv 1 = 13 ∨ kv 1 = 14 ∨ kv 1 = 15 ∨ kv 1 = 16 ∨ kv 1 = 17 ∨ kv 1 = 18 ∨ kv 1 = 19 ∨ kv 1 = 20 ∨ kv 1 = 21 ∨ kv 1 = 22 ∨ kv 1 = 23 ∨ kv 1 = 24 ∨ kv 1 = 25 ∨ kv 1 = 26 ∨ kv 1 = 27 ∨ kv 1 = 28 ∨ kv 1 = 29 := by omega
     rcases hc4 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega)

/-- The bridge at the type boundary `p / r = 2/3`. -/
def br57 : DipBridge := ⟨2, 3333, 5000, 10001, 15000, [ln67, ln66]⟩

theorem br57_member (ρ : ℕ) : br57.Member ρ := by
  intro hρ1 hρ2 r p m kv hf hc
  obtain ⟨hr, hr0, hp, ⟨hm1, hm2⟩, hm3, ⟨jA, eA, jA0, jA3, kA0, kAp⟩, ⟨jB, eB, jB0, jB2, kB0, kBp⟩⟩ := hf
  have jB1 : jB = 1 := by omega
  subst jB1
  have jAc : jA = 1 ∨ jA = 2 := by omega
  rcases jAc with rfl | rfl <;>
  simp only [DipBridge.toBranch, br57, ln67, ln66, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, DipLine.classCond, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] at hc <;>
  simp only [br57, ln67, ln66, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, DipLine.conds, DipLine.classCond, DipLine.chainCond, DipLine.lVec, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] <;>
  by_cases hsm : kv 1 < 30 <;>
  first
  | omega
  | (have hc4 : kv 1 = 4 ∨ kv 1 = 5 ∨ kv 1 = 6 ∨ kv 1 = 7 ∨ kv 1 = 8 ∨ kv 1 = 9 ∨ kv 1 = 10 ∨ kv 1 = 11 ∨ kv 1 = 12 ∨ kv 1 = 13 ∨ kv 1 = 14 ∨ kv 1 = 15 ∨ kv 1 = 16 ∨ kv 1 = 17 ∨ kv 1 = 18 ∨ kv 1 = 19 ∨ kv 1 = 20 ∨ kv 1 = 21 ∨ kv 1 = 22 ∨ kv 1 = 23 ∨ kv 1 = 24 ∨ kv 1 = 25 ∨ kv 1 = 26 ∨ kv 1 = 27 ∨ kv 1 = 28 ∨ kv 1 = 29 := by omega
     rcases hc4 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega)

/-- The bridge at the type boundary `p / r = 7/10`. -/
def br58 : DipBridge := ⟨2, 69993, 100000, 70007, 100000, [ln67, ln69]⟩

theorem br58_member (ρ : ℕ) : br58.Member ρ := by
  intro hρ1 hρ2 r p m kv hf hc
  obtain ⟨hr, hr0, hp, ⟨hm1, hm2⟩, hm3, ⟨jA, eA, jA0, jA3, kA0, kAp⟩, ⟨jB, eB, jB0, jB2, kB0, kBp⟩⟩ := hf
  have jB1 : jB = 1 := by omega
  subst jB1
  have jAc : jA = 1 ∨ jA = 2 := by omega
  rcases jAc with rfl | rfl <;>
  simp only [DipBridge.toBranch, br58, ln67, ln69, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, DipLine.classCond, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] at hc <;>
  simp only [br58, ln67, ln69, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, DipLine.conds, DipLine.classCond, DipLine.chainCond, DipLine.lVec, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] <;>
  by_cases hsm : kv 1 < 30 <;>
  first
  | omega
  | (have hc4 : kv 1 = 4 ∨ kv 1 = 5 ∨ kv 1 = 6 ∨ kv 1 = 7 ∨ kv 1 = 8 ∨ kv 1 = 9 ∨ kv 1 = 10 ∨ kv 1 = 11 ∨ kv 1 = 12 ∨ kv 1 = 13 ∨ kv 1 = 14 ∨ kv 1 = 15 ∨ kv 1 = 16 ∨ kv 1 = 17 ∨ kv 1 = 18 ∨ kv 1 = 19 ∨ kv 1 = 20 ∨ kv 1 = 21 ∨ kv 1 = 22 ∨ kv 1 = 23 ∨ kv 1 = 24 ∨ kv 1 = 25 ∨ kv 1 = 26 ∨ kv 1 = 27 ∨ kv 1 = 28 ∨ kv 1 = 29 := by omega
     rcases hc4 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega)

/-- The bridge at the type boundary `p / r = 7/9`. -/
def br60 : DipBridge := ⟨2, 7777, 10000, 70007, 90000, [ln69, ln72]⟩

theorem br60_member (ρ : ℕ) : br60.Member ρ := by
  intro hρ1 hρ2 r p m kv hf hc
  obtain ⟨hr, hr0, hp, ⟨hm1, hm2⟩, hm3, ⟨jA, eA, jA0, jA3, kA0, kAp⟩, ⟨jB, eB, jB0, jB2, kB0, kBp⟩⟩ := hf
  have jB1 : jB = 1 := by omega
  subst jB1
  have jAc : jA = 1 ∨ jA = 2 := by omega
  rcases jAc with rfl | rfl <;>
  simp only [DipBridge.toBranch, br60, ln69, ln72, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, DipLine.classCond, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] at hc <;>
  simp only [br60, ln69, ln72, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, forall_eq_or_imp, forall_eq, DipLine.conds, DipLine.classCond, DipLine.chainCond, DipLine.lVec, KCond.Holds, KCond.L, dot, zero_add, ↓reduceIte, Bool.false_eq_true, ite_true, ite_false, Nat.reduceEqDiff, zero_mul, add_zero] <;>
  by_cases hsm : kv 1 < 30 <;>
  first
  | omega
  | (have hc4 : kv 1 = 4 ∨ kv 1 = 5 ∨ kv 1 = 6 ∨ kv 1 = 7 ∨ kv 1 = 8 ∨ kv 1 = 9 ∨ kv 1 = 10 ∨ kv 1 = 11 ∨ kv 1 = 12 ∨ kv 1 = 13 ∨ kv 1 = 14 ∨ kv 1 = 15 ∨ kv 1 = 16 ∨ kv 1 = 17 ∨ kv 1 = 18 ∨ kv 1 = 19 ∨ kv 1 = 20 ∨ kv 1 = 21 ∨ kv 1 = 22 ∨ kv 1 = 23 ∨ kv 1 = 24 ∨ kv 1 = 25 ∨ kv 1 = 26 ∨ kv 1 = 27 ∨ kv 1 = 28 ∨ kv 1 = 29 := by omega
     rcases hc4 with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> omega)

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.F227
