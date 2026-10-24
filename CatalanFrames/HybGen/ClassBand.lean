module

public import CatalanFrames.HybGen.TropM
public import CatalanCore.Arith.Hybrid.PieceTools
public import CatalanCore.Arith.Hybrid.Pieces

@[expose] public section

/-!
# Class bands and the generic cover constructor

`BandP I d j ulo uhi p`: the prime `p` is `≥ 5` and `j p + ulo ≤ d · kq p ≤ j p + uhi`, a linear
dictionary for the first singular index `kq` (no division, no residues).  `Band` says it holds for
the primes of a residue class `c` modulo `M`.  `covers_mkM` is the generic-modulus form of
`P6Hybrid.covers_mk`: it turns the integer inequality on a piece into `Covers`.
-/

open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon

namespace CatalanFrames.HybGen

variable {Fr : Frame}

/-- Linear dictionary for `kq p`. -/
def BandP (I : HybInst Fr) (d j ulo uhi p : ℕ) : Prop :=
  5 ≤ p ∧ j * p + ulo ≤ d * I.cd.kq p ∧ d * I.cd.kq p ≤ j * p + uhi

/-- The primes of the class `c` (mod `M`) satisfy the dictionary. -/
def Band (I : HybInst Fr) (M : ℕ) (c : ZMod M) (d j ulo uhi : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → (p : ZMod M) = c → BandP I d j ulo uhi p

/-- Generic cover constructor: `P` is the information extracted from the class. -/
lemma covers_mkM {M : ℕ} (c : ZMod M) (P : ℕ → Prop)
    (hP : ∀ p : ℕ, p.Prime → (p : ZMod M) = c → P p)
    (wf : ℕ → ℕ) (r sn sd tn td : ℕ) (A B E D : ℤ) (hD : 0 < D)
    (h : ∀ p : ℕ, sn * r / sd < p → p ≤ tn * r / td → p.Prime → P p →
      D * (wf p : ℤ) ≤ A * r + B * p + E) :
    Covers c (fun p => (wf p : ℝ)) r (mkPiece sn sd tn td A B E D) := by
  intro p hs ht hp hpc
  rw [floor_mk_s] at hs
  rw [floor_mk_t] at ht
  exact real_of_int_bound D A B E hD (h p hs ht hp (hP p hp hpc))

/-- Good primes of the thirds frames are `1, 5 (mod 6)`. -/
lemma cls_mem_of_bad {p : ℕ} (hp : p.Prime) (hb : p ∉ ({2, 3} : Finset ℕ)) :
    (p : ZMod 6) ∈ ({1, 5} : Finset (ZMod 6)) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  have h2 : ¬ 2 ∣ p := fun h => hb (Or.inl ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm)
  have h3 : ¬ 3 ∣ p := fun h => hb (Or.inr ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm)
  have hq : p % 6 = 1 ∨ p % 6 = 5 := by omega
  rw [← ZMod.natCast_mod p 6]
  rcases hq with h | h <;> rw [h] <;> simp <;> decide

end CatalanFrames.HybGen

#print axioms CatalanFrames.HybGen.covers_mkM
#print axioms CatalanFrames.HybGen.cls_mem_of_bad
