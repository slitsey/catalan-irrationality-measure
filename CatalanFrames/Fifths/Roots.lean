module
public import CatalanFrames.HybGen.NatRoots
@[expose] public section
namespace CatalanFrames.Fifths

/-- Multiplier j in 5*kq = j*q+u, for the four unit residue classes. -/
def classIndex (u q : ℕ) : ℕ :=
  if q%5=1 then 5-u else if q%5=2 then (5-(3*u)%5)%5
  else if q%5=3 then (5-(2*u)%5)%5 else u

def firstRoot (u q : ℕ) : ℕ := (classIndex u q*q+u)/5

theorem firstRoot_spec {u q : ℕ} (hu0 : 1 ≤ u) (hu1 : u < 5) (hq : 5 ≤ q)
    (hunit : q%5 ≠ 0) :
    5*firstRoot u q = classIndex u q*q+u ∧ 0 < firstRoot u q ∧ firstRoot u q < q ∧
      1 ≤ classIndex u q ∧ classIndex u q ≤ 4 := by
  have hqmod : q%5=1 ∨ q%5=2 ∨ q%5=3 ∨ q%5=4 := by omega
  interval_cases u <;> rcases hqmod with h|h|h|h <;>
    simp [firstRoot, classIndex, h] <;> omega

theorem classIndex_unique {u q t : ℕ} (hu0 : 1 ≤ u) (hu1 : u < 5)
    (hunit : q%5 ≠ 0) (ht0 : 1 ≤ t) (ht1 : t < 5) (hd : 5 ∣ t*q+u) :
    t = classIndex u q := by
  have hmod : (t*q+u)%5=0 := Nat.mod_eq_zero_of_dvd hd
  have hqmod : q%5=1 ∨ q%5=2 ∨ q%5=3 ∨ q%5=4 := by omega
  interval_cases u <;> interval_cases t <;> rcases hqmod with h|h|h|h <;>
    simp [classIndex, h] <;> omega

/-- Uniform first-root lower bound for every prime power, including all four offsets. -/
theorem firstRoot_le_of_dvd {u p n k : ℕ} (hp : p.Prime) (hn : 0 < n)
    (hu0 : 1 ≤ u) (hu1 : u < 5) (hq : 5 ≤ p^n) (hunit : p^n%5 ≠ 0)
    (hpu : ¬ p ∣ u) (hk : 0 < k) (hd : p^n ∣ k*(5*k-u)) :
    firstRoot u (p^n) ≤ k ∧ p^n ≤ 5*k := by
  have hs := firstRoot_spec hu0 hu1 hq hunit
  rcases HybGen.primePower_split hp hpu (by omega : u ≤ 5*k) hd with hc|hc
  · have hpk : p^n ≤ k := Nat.le_of_dvd hk hc
    constructor <;> omega
  · have hpos : 0 < 5*k-u := by omega
    have hqk : p^n ≤ 5*k-u := Nat.le_of_dvd hpos hc
    refine ⟨?_, by omega⟩
    obtain ⟨t,ht⟩ := hc
    have ht0 : 1 ≤ t := by nlinarith
    rcases Nat.lt_or_ge t 5 with ht1|ht1
    · have hd5 : 5 ∣ t*(p^n)+u := by
        refine ⟨k, ?_⟩
        have hu : 5*k-u+u=5*k := by omega
        nlinarith
      have he := classIndex_unique hu0 hu1 hunit ht0 ht1 hd5
      rw [he] at ht
      nlinarith [hs.1, Nat.sub_add_cancel (show u ≤ 5*k by omega)]
    · have hmul : (p^n)*5 ≤ (p^n)*t := Nat.mul_le_mul_left _ ht1
      omega
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.firstRoot_spec
#print axioms CatalanFrames.Fifths.classIndex_unique
#print axioms CatalanFrames.Fifths.firstRoot_le_of_dvd
