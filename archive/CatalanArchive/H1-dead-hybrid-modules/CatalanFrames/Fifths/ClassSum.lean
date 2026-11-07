module
public import CatalanFrames.Fifths.Instance
public import CatalanFrames.Fifths.Covers
public import CatalanFrames.Fifths.ClassDictionary
public import CatalanFrames.HybGen.TableSum
@[expose] public section
open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.HybGen
namespace CatalanFrames.Fifths
noncomputable def tableFor (j : ℕ) : List Piece :=
  if j=1 then table1 else if j=2 then table2 else if j=3 then table3 else table4
noncomputable def classPrice (j : ℕ) : ℝ := (9/4*(1/68)+listInt (tableFor j))/8
lemma classIndex_bounds {u : ℕ} (hu0 : 1≤u) (hu1 : u<5) :
    ∀ c∈unitClasses,1≤classIndex u c.val ∧ classIndex u c.val≤4 := by
  interval_cases u <;> decide +kernel
private lemma unitClasses_sum (g : ZMod 30 → ℝ) :
    (∑ c∈unitClasses,g c) = g 1+g 7+g 11+g 13+g 17+g 19+g 23+g 29 := by
  unfold unitClasses
  rw [Finset.sum_insert (by decide : (1 : ZMod 30)∉({7,11,13,17,19,23,29} : Finset (ZMod 30))),
    Finset.sum_insert (by decide : (7 : ZMod 30)∉({11,13,17,19,23,29} : Finset (ZMod 30))),
    Finset.sum_insert (by decide : (11 : ZMod 30)∉({13,17,19,23,29} : Finset (ZMod 30))),
    Finset.sum_insert (by decide : (13 : ZMod 30)∉({17,19,23,29} : Finset (ZMod 30))),
    Finset.sum_insert (by decide : (17 : ZMod 30)∉({19,23,29} : Finset (ZMod 30))),
    Finset.sum_insert (by decide : (19 : ZMod 30)∉({23,29} : Finset (ZMod 30))),
    Finset.sum_insert (by decide : (23 : ZMod 30)∉({29} : Finset (ZMod 30))),Finset.sum_singleton]
  ring
/-- Compute only the small residue permutation, with the summand abstract.
This prevents closed table definitions from entering the finite residue reduction. -/
lemma classIndex_sum (f : ℕ → ℝ) {u : ℕ} (hu0 : 1≤u) (hu1 : u<5) :
    (∑ c∈unitClasses,f (classIndex u c.val))=2*(f 1+f 2+f 3+f 4) := by
  rw [unitClasses_sum]
  interval_cases u <;> norm_num [classIndex,ZMod.val_ofNat,ZMod.val_one_eq_one_mod] <;> ring
lemma classPrice_sum {u : ℕ} (hu0 : 1≤u) (hu1 : u<5) :
    (∑ c∈unitClasses,classPrice (classIndex u c.val))=(fifthsPrice : ℝ) := by
  rw [classIndex_sum classPrice hu0 hu1]
  change 2*((9/4*(1/68)+listInt table1)/8+(9/4*(1/68)+listInt table2)/8+
    (9/4*(1/68)+listInt table3)/8+(9/4*(1/68)+listInt table4)/8)=(fifthsPrice : ℝ)
  nlinarith only [finite_price_eq]
lemma tableFor_chain {j : ℕ} (hj1 : 1≤j) (hj4 : j≤4) : Chain (1/68) (tableFor j) := by
  have h : j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
  rcases h with rfl|rfl|rfl|rfl
  · simpa [tableFor] using table1_chain
  · simpa [tableFor] using table2_chain
  · simpa [tableFor] using table3_chain
  · simpa [tableFor] using table4_chain
lemma tableFor_end {j : ℕ} (hj1 : 1≤j) (hj4 : j≤4) : lastEnd (1/68) (tableFor j)=7 := by
  have h : j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
  rcases h with rfl|rfl|rfl|rfl
  · simpa [tableFor] using table1_end
  · simpa [tableFor] using table2_end
  · simpa [tableFor] using table3_end
  · simpa [tableFor] using table4_end
lemma tableFor_covers {Fr : Frame} {I : HybInst Fr} {M : ℕ} {c : ZMod M} {j r m : ℕ}
    (LF : LevelFacts I (fun p => 7≤p) (fun q c => c<I.cd.kq q))
    (hj1 : 1≤j) (hj4 : j≤4) (hb : Band7 I M c j)
    (hm1 : r≤8*m) (hm2 : 8*m≤r+9) (hr : 400≤r) :
    ∀ P∈tableFor j,Covers c (WGm I r m) r P := by
  have h : j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
  rcases h with rfl|rfl|rfl|rfl
  · simpa [tableFor] using table1_covers (T := LF) (hband := hb) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · simpa [tableFor] using table2_covers (T := LF) (hband := hb) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · simpa [tableFor] using table3_covers (T := LF) (hband := hb) (hm1 := hm1) (hm2 := hm2) (hr := hr)
  · simpa [tableFor] using table4_covers (T := LF) (hband := hb) (hm1 := hm1) (hm2 := hm2) (hr := hr)
lemma floor_seven (r : ℕ) : ⌊(7 : ℝ)*r⌋₊=7*r := by
  have h : (7 : ℝ)*r=((7*r : ℕ) : ℝ) := by push_cast;ring
  rw [h,Nat.floor_natCast]
variable {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u)
lemma fifths_band (c : ZMod 30) (hc : c∈unitClasses) :
    Band7 (fifthsInst T) 30 c (classIndex u c.val) := by
  intro p hp hpc
  have hp7 := prime_class_ge_seven hp (by rw [hpc];exact hc)
  have he := firstRoot_class_formula T.hu0 T.hu1 hp c hc hpc
  change 7≤p ∧ classIndex u c.val*p+1≤5*firstRoot u p ∧
    5*firstRoot u p≤classIndex u c.val*p+4
  have hu0 := T.hu0
  have hu1 := T.hu1
  exact ⟨hp7,by omega,by omega⟩
theorem fifths_class_bound {c : ZMod 30} (hc : c∈unitClasses) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ r : ℕ in atTop,∀ m : ℕ,r≤8*m → 8*m≤r+9 →
      clsSum 30 c (WGm (fifthsInst T) r m) 0 (7*r) ≤
        (r : ℝ)^2*(classPrice (classIndex u c.val)+ε) := by
  have hj := classIndex_bounds T.hu0 T.hu1 c hc
  have h := class_sum_of_tables (unitClasses_unit c hc) (fifthsInst T)
    (tableFor (classIndex u c.val)) (tableFor_chain hj.1 hj.2) (by
      intro r m h1 h2 hr P hP
      exact tableFor_covers (fifths_levels T) hj.1 hj.2 (fifths_band T c hc) h1 h2 hr P hP) hε
  filter_upwards [h] with r hr m h1 h2
  have hh := hr m h1 h2
  rw [tableFor_end hj.1 hj.2,floor_seven,show Nat.totient 30=8 by decide] at hh
  simpa [classPrice] using hh
/-- Eight unit classes, each pole multiplier twice; exact finite-prefix price. -/
theorem fifths_class_sum {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ r : ℕ in atTop,∀ m : ℕ,r≤8*m → 8*m≤r+9 →
      (∑ c∈unitClasses,clsSum 30 c (WGm (fifthsInst T) r m) 0 (7*r)) ≤
        (r : ℝ)^2*((fifthsPrice : ℝ)+ε) := by
  have hall : ∀ c∈unitClasses,∀ᶠ r : ℕ in atTop,∀ m : ℕ,r≤8*m → 8*m≤r+9 →
      clsSum 30 c (WGm (fifthsInst T) r m) 0 (7*r) ≤
        (r : ℝ)^2*(classPrice (classIndex u c.val)+ε/8) :=
    fun c hc => fifths_class_bound T hc (by positivity)
  filter_upwards [(Filter.eventually_all_finset unitClasses).2 hall] with r hr m h1 h2
  calc (∑ c∈unitClasses,clsSum 30 c (WGm (fifthsInst T) r m) 0 (7*r)) ≤
        ∑ c∈unitClasses,(r : ℝ)^2*(classPrice (classIndex u c.val)+ε/8) :=
          Finset.sum_le_sum fun c hc => hr c hc m h1 h2
    _ = (r : ℝ)^2*((fifthsPrice : ℝ)+ε) := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,
        classPrice_sum T.hu0 T.hu1,unitClasses_card]
      simp only [Nat.cast_ofNat]
      ring
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.classIndex_sum
#print axioms CatalanFrames.Fifths.classPrice_sum
#print axioms CatalanFrames.Fifths.fifths_band
#print axioms CatalanFrames.Fifths.fifths_class_sum
