module
public import Mathlib.NumberTheory.Padics.RingHoms
@[expose] public section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
namespace CatalanCore.Li2.NVMod

def ratUnitCheck (p : ℕ) (x : ℚ) : Bool := x.num%p != 0 && x.den%p != 0

theorem padic_int_unit_of_not_dvd (p : ℕ) [Fact p.Prime] (z : ℤ) (hz : ¬(p:ℤ)∣z) :
    ‖(z:Padic p)‖=1 := by
  apply le_antisymm (Padic.norm_int_le_one z)
  apply le_of_not_gt
  intro hlt
  exact hz (Padic.norm_intCast_lt_one_iff.mp hlt)

theorem ratUnitCheck_sound (p : ℕ) [Fact p.Prime] (q : ℚ)
    (h : ratUnitCheck p q=true) : ‖(q:Padic p)‖=1 := by
  have hh : q.num%(p:ℤ)≠0 ∧ q.den%p≠0 := by simpa [ratUnitCheck] using h
  have hn : ¬(p:ℤ)∣q.num := fun hd=>hh.1 (Int.emod_eq_zero_of_dvd hd)
  have hd : ¬(p:ℤ)∣(q.den:ℤ) := by
    intro hdiv
    have hnat : p∣q.den := by exact_mod_cast hdiv
    exact hh.2 (Nat.mod_eq_zero_of_dvd hnat)
  have hnum := padic_int_unit_of_not_dvd p q.num hn
  have hden : ‖(q.den:Padic p)‖=1 := by
    simpa only [Int.cast_natCast] using padic_int_unit_of_not_dvd p (q.den:ℤ) hd
  have he : (q:Padic p)=(q.num:Padic p)/(q.den:Padic p) := by
    simpa only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast] using
      congrArg (fun r : ℚ=>(r:Padic p)) (Rat.num_div_den q).symm
  rw [he,norm_div,hnum,hden,div_self one_ne_zero]

#print axioms ratUnitCheck_sound
end CatalanCore.Li2.NVMod
