module

public import CatalanFrames.P6Hybrid.Data3

/-!
# P6 valuation-one entries

Distinct middle nodes have an integral kernel entry before any scaling.
The defining interval misses both singular indices. This is the extra entry fact
needed by the generic asymmetric valuation-one determinant argument.
-/

@[expose] public section

open Finset CatalanCore CatalanFrames.P6 CatalanFrames.P6.NV

namespace CatalanFrames.P6Hybrid

variable {ℓ t : ℕ} [Fact ℓ.Prime]

/-- Unlike a diagonal middle entry, a distinct middle entry is already integral. -/
lemma midmid_off_mem (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t) {a b : ℕ}
    (ha : 2 * t + 1 ≤ a) (hb : b ≤ 3 * t) (hab : a < b) :
    p6Frame.Mn a b ∈ S ℓ := by
  have g36 : Good ℓ (1 / 36 : ℚ) (1 / 36) :=
    Good.one.div (Good.ofNat 36) (n36_ne hl ht)
  have gs := Good.sum (ℓ := ℓ) (Ioc a b) (fun k => p6Frame.Delta k)
    (fun k => Tri (finv ℓ) t k) fun k hk => by
      have hk := Finset.mem_Ioc.1 hk
      exact delta_good hl ht (by omega) (by omega) (by omega)
  have hne : (b : ZMod ℓ) - a ≠ 0 :=
    sub_ne_zero.2 (natCast_ne_natCast (p := ℓ) (by omega) (by omega) hab.ne')
  have gd : Good ℓ (1 / ((b : ℚ) - a)) (1 / ((b : ZMod ℓ) - a)) :=
    Good.one.div ((Good.natCast b).sub (Good.natCast a)) hne
  have g := (g36.mul gd).mul gs
  rw [Mn_off hab]
  exact (g.congr' (by ring)).mem

/-- Symmetric form, reusable for arbitrary middle-node common cores. -/
lemma midmid_ne_mem (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t) {a b : ℕ}
    (ha : 2 * t + 1 ≤ a) (ha' : a < 3 * t + 1)
    (hb : 2 * t + 1 ≤ b) (hb' : b < 3 * t + 1) (hab : a ≠ b) :
    p6Frame.Mn a b ∈ S ℓ := by
  rcases lt_or_gt_of_ne hab with h | h
  · exact midmid_off_mem hl ht ha (by omega) h
  · rw [Mn_comm]
    exact midmid_off_mem hl ht hb (by omega) h

/-- The single row factor already kills distinct middle entries. -/
lemma midmid_ne_ell_good (hl : ℓ = 6 * t + 1) (ht : 1 ≤ t) {a b : ℕ}
    (ha : 2 * t + 1 ≤ a) (ha' : a < 3 * t + 1)
    (hb : 2 * t + 1 ≤ b) (hb' : b < 3 * t + 1) (hab : a ≠ b) :
    Good ℓ ((ℓ : ℚ) * p6Frame.Mn a b) 0 :=
  (good_red (midmid_ne_mem hl ht ha ha' hb hb' hab)).ell_mul

end CatalanFrames.P6Hybrid
