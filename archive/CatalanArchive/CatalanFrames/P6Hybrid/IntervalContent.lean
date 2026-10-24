module
public import CatalanArchive.CatalanFrames.P6Hybrid.PoleIntervals
@[expose] public section
open Finset Polynomial Matrix CatalanCore CatalanCore.Rect CatalanCore.Arith.Hybrid
namespace CatalanFrames.P6Hybrid
open ChainClasses

def p6WitnessLeft (r p j : ℕ) : ℕ := max r ((j*p+4)/6+1)
def p6WitnessRight (r m p k : ℕ) : ℕ := min (r+2*m) (k*p/6)

theorem p6_interval_minor_gle {r m p c j k : ℕ} [Fact p.Prime]
    (hp : 5≤p) (hN : 3*(r+2*m)<p*p) (hpm : 2*m<p)
    (hc : c=1 ∨ c=5) (hpc : p%6=c)
    (hgap : ∀a:ℤ,(j:ℤ)<a→a<k→¬p6PoleMask c a)
    (hab : p6WitnessLeft r p j≤p6WitnessRight r m p k)
    (s : Finset (Fin r)) :
    GLE p (2*r+(2*m-(p6WitnessRight r m p k-p6WitnessLeft r p j)))
      (commonMinorPoly CatalanFrames.P6.p6Frame r m s) := by
  let a:=p6WitnessLeft r p j
  let b:=p6WitnessRight r m p k
  have hla : r≤a := le_max_left _ _
  have hrb : b≤r+2*m := min_le_left _ _
  have hcut : ∀x y:ℕ,a≤x→x<b→a≤y→y<b→
      NoCut (Cut p r (p6Singular p)) (min (x:ℤ) y) (max (x:ℤ) y) := by
    intro x y hx hxb hy hyb
    apply p6_cut_between (by omega) (by omega) (by omega)
    intro t hlt htu
    apply p6_no_pole_between (by omega) hc hpc hgap
    · have ha : (j*p+4)/6+1≤a := le_max_right _ _
      have H:=Nat.mod_add_div (j*p+4) 6
      have H':=Nat.mod_lt (j*p+4) (by omega : 0<6)
      push_cast at H H'
      omega
    · have hb : b≤k*p/6 := min_le_right _ _
      have H:=Nat.mod_add_div (k*p) 6
      have H':=Nat.mod_lt (k*p) (by omega : 0<6)
      push_cast at H H'
      omega
  let w:=witnessTable p r m a b
  have H:=commonMinorPoly_periodic_gle (p6PoleData hp (by simpa only [pow_two] using hN)) (by omega) (by omega)
    (le_refl (r+2*m)) w (fun i j=>witnessWeight_le_two _ _ _ _ _)
    (by
      intro i j hij
      have hh : a≤r+2*i.val ∧ r+2*i.val<b ∧ a≤r+2*j.val+1 ∧ r+2*j.val+1<b := by
        by_contra hno
        simp only [w,witnessTable,witnessWeight,if_neg hno] at hij
        split_ifs at hij <;> omega
      exact hcut _ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2)
    (by
      intro i j hij heq
      simp only [w,witnessTable,witnessWeight,heq,ite_true] at hij
      split_ifs at hij <;> omega) s
  apply H.mono
  have HW:=witness_assignment_high hla hab hrb hpm
  dsimp only [w,a,b] at HW ⊢
  omega
end CatalanFrames.P6Hybrid
