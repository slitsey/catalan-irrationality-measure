import CatalanCore.Uniform.Content.BankShared.Inst.Sevenths
import CatalanFrames.Fifths.Instance
set_option Elab.async false

/-! # Audit of the generic two-term instance (lane C6L)

* genericity: at `q = 5` the generic table and instance recover the fifths instance facts of
  `CatalanFrames.Fifths.Instance` (same `Φ`, `L`, norm, bad primes `{2, 3, 5}`, levels, small-prime clearer
  `small5`, first root on every good prime power, `ArithmeticInfo _ 5 2`, `LevelFacts` with `p ≥ 7`,
  `badLog = log 30`, `cOf ≤ 2`);
* the sevenths instance for all six members;
* `#print axioms` of every exported theorem. -/

namespace CatalanCore.Uniform.Content.BankShared.Inst.Audit
open CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.BankShared.Inst
  CatalanFrames.HybCommon CatalanFrames.HybGen
open CatalanFrames.Fifths (ShiftData fifthsCD fifthsInst fifths_kq_att badPrimes small5 fifths_badLog)
open CatalanCore.Uniform.Bank.Sevenths (seventhsFrameAt)

theorem badQ_five : badQ 5 = {2, 3, 5} := by
  ext b
  simp only [mem_badQ, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    interval_cases b
    · exact absurd h2 (by norm_num)
    · exact absurd h2 (by norm_num)
    · simp
    · simp
    · exact absurd h2 (by norm_num)
    · simp
  · rintro (rfl | rfl | rfl) <;> norm_num

theorem smallQ_five (h : ℕ) : smallQ 5 h = small5 h := by
  unfold smallQ small5
  rw [badQ_five, Finset.prod_insert (by decide : (2 : ℕ) ∉ ({3, 5} : Finset ℕ)),
    Finset.prod_insert (by decide : (3 : ℕ) ∉ ({5} : Finset ℕ)), Finset.prod_singleton]
  ring

section Fifths
variable {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u)

/-! ### `q = 5`: the generic instance recovers the fifths instance -/

example : (twoTermCD T).Phi = (fifthsCD T).Phi := rfl
example : (twoTermCD T).L = (fifthsCD T).L := rfl
example : (twoTermCD T).normN = (fifthsCD T).normN := rfl
example : (twoTermCD T).bad = (fifthsCD T).bad := badQ_five
example : (twoTermInst T).lev = (fifthsInst T).lev := rfl
example (h : ℕ) : (twoTermCD T).small h = (fifthsCD T).small h := smallQ_five h

/-- The first root `poleIndex 5 (5 - u)` is `firstRoot u` on every good prime power. -/
example {Q : ℕ} (hQ : IsPrimePow Q) (hb : ∀ p ∈ (twoTermCD T).bad, ¬ p ∣ Q) :
    (twoTermCD T).kq Q = (fifthsCD T).kq Q :=
  kq_eq_of_att (twoTermCD T) (fifthsCD T) (fun _ => rfl) badQ_five (twoTerm_kq_att T) (fifths_kq_att T) hQ hb

/-- `fifths_arithmetic`: `ArithmeticInfo _ 5 2`. -/
example : ArithmeticInfo (twoTermInst T) 5 2 :=
  twoTerm_arithmetic_small T (by norm_num) (by have := T.hu0; omega) (by norm_num)

/-- `fifths_levels`: good primes `p ≥ 7`. -/
example : LevelFacts (twoTermInst T) (fun p => 7 ≤ p) (fun Q c => c < (twoTermInst T).cd.kq Q) :=
  levelFacts_mono (twoTerm_levels T) (fun _ _ h => by omega)

/-- `fifths_badLog`. -/
example : badLog (twoTermInst T) = Real.log 30 := by
  rw [← fifths_badLog T]
  exact congrArg (fun s : Finset ℕ => ∑ b ∈ s, Real.log (b : ℝ)) badQ_five

/-- `fifths_cOf_le`. -/
example (p : ℕ) : cOf (twoTermInst T) p ≤ 2 := twoTerm_cOf_le_prime T (by norm_num) p

end Fifths

/-! ### `q = 7`: the six sevenths members -/

example (a : Fin 6) : Nonempty (HybInst (seventhsFrameAt a)) := ⟨seventhsInst a⟩
example (a : Fin 6) (r m : ℕ) : (seventhsInst a).DiagOK r m := inferInstance
example (a : Fin 6) : LevelFacts (seventhsInst a) (fun p => 7 < p) (fun Q c => c < (seventhsInst a).cd.kq Q) :=
  seventhsInst_levels a
example : ArithmeticInfo (seventhsInst 3) 7 2 := seventhsInst_arithmetic 3 (by decide)
example : ¬ ArithmeticInfo (seventhsInst 5) 7 2 := seventhsInst_not_arithmetic 5 (by decide) 7 2

end CatalanCore.Uniform.Content.BankShared.Inst.Audit

set_option pp.fullNames true
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.rootClass_spec_cop
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.rootClass_unique_cop
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.ttRoot_spec
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.ttRoot_att
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.ttRoot_le
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.smallQ_poly
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.tt_ebd_cubic
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.shift_toTwoTerm
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.shift_ofTwoTerm
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.smallQ_ok
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.twoTermCD
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.twoTermInst
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.twoTerm_levels
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.twoTerm_kq_eq
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.twoTerm_arithmetic
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.twoTerm_arithmetic_small
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.twoTerm_not_arithmetic
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.twoTerm_norm
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.twoTerm_hP
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.twoTerm_hkq
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.kq_eq_of_att
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.seventhsShift
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.seventhsInst_levels
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.seventhsInst_hP
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.seventhsInst_hkq
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.seventhsInst_arithmetic
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.seventhsInst_catValid_bank
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.seventhsInst_catValid_bankUF
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.seventhsInst_not_arithmetic
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.seventhsFive_not_arithmetic
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.Audit.badQ_five
#print axioms CatalanCore.Uniform.Content.BankShared.Inst.Audit.smallQ_five
