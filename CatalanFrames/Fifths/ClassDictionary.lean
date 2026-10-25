module
public import CatalanFrames.Fifths.Window
public import CatalanFrames.Fifths.Roots
@[expose] public section
open Finset
namespace CatalanFrames.Fifths

theorem prime_class_ge_seven {p : ℕ} (hp : p.Prime)
    (hpc : (p : ZMod 30) ∈ unitClasses) : 7 ≤ p := by
  by_contra h
  have hs : ∀ k : Fin 7,k.val.Prime → (k.val : ZMod 30)∉unitClasses := by decide +kernel
  exact hs ⟨p,by omega⟩ hp hpc

theorem cls_mem_of_bad {p : ℕ} (hp : p.Prime) (hb : p ∉ ({2,3,5} : Finset ℕ)) :
    (p : ZMod 30) ∈ unitClasses := by
  have h2 : p%2 ≠ 0 := by
    intro h
    have hd : 2 ∣ p := Nat.dvd_of_mod_eq_zero h
    have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
    exact hb (by simp [← he])
  have h3 : p%3 ≠ 0 := by
    intro h
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    have he := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
    exact hb (by simp [← he])
  have h5 : p%5 ≠ 0 := by
    intro h
    have hd : 5 ∣ p := Nat.dvd_of_mod_eq_zero h
    have he := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) hp).mp hd
    exact hb (by simp [← he])
  have h2q : (p%30)%2 ≠ 0 := by
    simpa only [Nat.mod_mod_of_dvd p (by decide : 2∣30)] using h2
  have h3q : (p%30)%3 ≠ 0 := by
    simpa only [Nat.mod_mod_of_dvd p (by decide : 3∣30)] using h3
  have h5q : (p%30)%5 ≠ 0 := by
    simpa only [Nat.mod_mod_of_dvd p (by decide : 5∣30)] using h5
  have hs : ∀ k : Fin 30,k.val%2≠0 → k.val%3≠0 → k.val%5≠0 →
      (k.val : ZMod 30)∈unitClasses := by decide +kernel
  rw [←ZMod.natCast_mod p 30]
  exact hs ⟨p%30,Nat.mod_lt p (by decide)⟩ h2q h3q h5q

/-- Every pole multiplier occurs twice among the eight admissible residue classes. -/
theorem classIndex_count {u j : ℕ} (hu0 : 1 ≤ u) (hu1 : u < 5)
    (hj0 : 1 ≤ j) (hj1 : j < 5) :
    (unitClasses.filter (fun c => classIndex u c.val = j)).card = 2 := by
  interval_cases u <;> interval_cases j <;> decide +kernel

/-- Transfer the exact modular dictionary to the actual prime in a unit class. -/
theorem firstRoot_class_formula {u p : ℕ} (hu0 : 1 ≤ u) (hu1 : u < 5)
    (hp : p.Prime) (c : ZMod 30) (hc : c ∈ unitClasses) (hpc : (p : ZMod 30) = c) :
    5*firstRoot u p = classIndex u c.val*p+u := by
  have hcv : c.val < 30 := ZMod.val_lt c
  have hcast : ((c.val : ℕ) : ZMod 30) = c := ZMod.natCast_zmod_val c
  have hmod : p%30 = c.val := by
    have hh := (ZMod.natCast_eq_natCast_iff' p c.val 30).mp (hpc.trans hcast.symm)
    simpa only [Nat.mod_eq_of_lt hcv] using hh
  have hp5 : p%5 = c.val%5 := by omega
  have hall : ∀ d ∈ unitClasses, d.val%5 ≠ 0 := by decide +kernel
  have hu5 : p%5 ≠ 0 := by rw [hp5];exact hall c hc
  have hp7 := prime_class_ge_seven hp (by rw [hpc];exact hc)
  have hh := (firstRoot_spec hu0 hu1 (by omega : 5 ≤ p) hu5).1
  have hj : classIndex u p = classIndex u c.val := by simp only [classIndex,hp5]
  simpa only [hj] using hh
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.cls_mem_of_bad
#print axioms CatalanFrames.Fifths.classIndex_count
#print axioms CatalanFrames.Fifths.firstRoot_class_formula
