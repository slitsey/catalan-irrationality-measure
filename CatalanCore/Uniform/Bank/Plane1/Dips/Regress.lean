module

public import CatalanCore.Uniform.Bank.Plane1.Dips.Member

@[expose] public section
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

/-! # Regression instance of the member dual theorem (wave R0)

`member_crude`: with no pivots and the constant dual `ρ = γ = 1`, `Wd ≤ 2` (`Wd_le_two`), so `member_gle` gives
`GLE p (2 (r + m) + 2 |I|) (commonMinorPoly Fr r m s)` for every member, `|I| = r - |s|`: the crude level `D1` with the
debit of the catalogue.  This instantiates `HybPiv` (all hypotheses are satisfiable) and the whole chain
`entry_gle → restrict_gle → member_gle` on a statement already known from the plane catalogue (price `2 (r + m)`).  No data. -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset Polynomial CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect

section Crude

variable {ι : Type} [DecidableEq ι] {p : ℕ} {Fr : Frame}

theorem w0_le_two (U V : ℕ) : w0 p Fr U V ≤ 2 := by
  unfold w0
  split_ifs <;> omega

theorem Wd_le_two (G : GData ι) (Vr Vc : ι → ℚ) (x y : ι) : Wd p Fr G Vr Vc x y ≤ 2 := by
  unfold Wd
  have := w0_le_two (p := p) (Fr := Fr)
  split_ifs <;> first | omega | exact max_le (max_le (this _ _) (this _ _)) (max_le (this _ _) (this _ _))

end Crude

section Member

variable {p : ℕ} [hp : Fact p.Prime] {Fr : Frame} {r m : ℕ}

/-- **Regression: the crude member bound** `2 (r + m) + 2 |I|` from the unpivoted constant dual. -/
theorem member_crude (hden : ∀ i, (Fr.μ i).den ≤ 3) (h5 : 5 ≤ p) (hnorm : Fr.norm = 1)
    (hN : 3 * (r + 2 * m) < p * p) (hm : 2 * m < p) (s : Finset (Fin r)) :
    GLE p (2 * (r + m) + 2 * (r - s.card)) (commonMinorPoly Fr r m s) := by
  have hP : HybPiv r m p Fr (fun _ => (none : Option (Fin r))) (fun _ => none) (fun _ => 0) (fun _ => 0)
      (fun i => Vp p Fr (r + 2 * i.1)) (fun i => Vp p Fr (r + 2 * i.1 + 1)) :=
    { h3 := by omega
      hnorm := hnorm
      v_mem := fun t ht => Vp_mem_Q hden (by omega)
      u_mem := fun t ht => Up_mem_Q hden (by omega)
      square_free := fun U V hU hV hne => diff_not_sq_of_lt (by omega) (by omega) hne
      hm := hm
      rowP := fun i c h => by simp at h
      rowN := fun i _ => rfl
      colP := fun i c h => by simp at h
      colN := fun i _ => rfl
      lR_mem := fun i => (LocRing p).zero_mem
      lC_mem := fun i => (LocRing p).zero_mem }
  refine member_gle hP s (fun _ => 1) (fun _ => 1) (fun _ => zero_le_one) (fun _ => zero_le_one)
    (fun x y => ?_) ?_
  · have := Wd_le_two (p := p) (Fr := Fr) (hfData r m (fun _ => none) (fun _ => none) (fun _ => 0) (fun _ => 0))
      (hfVr r m p Fr (fun i => Vp p Fr (r + 2 * i.1))) (hfVr r m p Fr (fun i => Vp p Fr (r + 2 * i.1 + 1))) x y
    have h2 : ((Wd p Fr (hfData r m (fun _ => none) (fun _ => none) (fun _ => 0) (fun _ => 0))
      (hfVr r m p Fr (fun i => Vp p Fr (r + 2 * i.1))) (hfVr r m p Fr (fun i => Vp p Fr (r + 2 * i.1 + 1))) x y : ℕ) : ℚ) ≤ 2 := by
      exact_mod_cast this
    linarith
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    have : ((r - s.card : ℕ) : ℚ) = ((2 * (r - s.card) : ℕ) : ℚ) / 2 := by push_cast; ring
    push_cast
    linarith

end Member

#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Wd_le_two
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.member_crude

end CatalanCore.Uniform.Bank.Plane1.Dips
