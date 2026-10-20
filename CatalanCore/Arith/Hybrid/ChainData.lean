module

public import CatalanCore.Arith.Hybrid.ChainClasses
public import CatalanCore.Arith.Hybrid.UniformEntries

@[expose] public section

/-! # Cumulative leading data on translated core chains

Both the first- and second-order node data are cumulative sums supported at
singular nodes.  The same finite-sum argument therefore transports both.
-/

open Finset CatalanCore

namespace CatalanCore.Arith.Hybrid.ChainClasses

variable {K : Type*} [AddCommGroup K]

/-- Integer-indexed cumulative, including the empty cumulative below zero. -/
def cumulative (s : Finset ℕ) (v : ℕ → K) (n : ℤ) : K :=
  ∑ t ∈ s, if (t : ℤ) ≤ n then v t else 0

theorem prefix_eq {s : Finset ℕ} {v : ℕ → K} {sing : ℤ → Prop} {a b : ℤ}
    (hab : a ≤ b) (hs : ∀ t ∈ s, sing t) (h : NoCut sing a b) :
    cumulative s v a = cumulative s v b := by
  apply Finset.sum_congr rfl
  intro t ht
  by_cases hta : (t : ℤ) ≤ a
  · simp [hta, hta.trans hab]
  · have htb : ¬ (t : ℤ) ≤ b := by
      intro htb
      exact h t (by omega) htb (hs t ht)
    simp [hta, htb]

theorem prefix_nat (s : Finset ℕ) (v : ℕ → K) (n : ℕ) :
    cumulative s v n = ∑ t ∈ s, if t ≤ n then v t else 0 := by
  simp only [cumulative, Nat.cast_le]

theorem prefix_chain_eq {s : Finset ℕ} {v : ℕ → K} {p r a b i : ℤ}
    {sing : ℤ → Prop} (hab : a ≤ b) (hs : ∀ t ∈ s, sing t)
    (hperiod : ∀ t j : ℤ, sing (t + j * p) ↔ sing t)
    (h : NoCut (Cut p r sing) a b) :
    cumulative s v (a - i * p) = cumulative s v (b - i * p) :=
  prefix_eq (by omega) hs (noCut_translate hperiod h)

theorem singularNodes_singular {p o N t : ℕ} (ho : o ≤ 3)
    (ht : t ∈ singularNodes p o N) : Singular p o t := by
  obtain ⟨hI, hsing⟩ := Finset.mem_filter.mp ht
  have ht1 := (Finset.mem_Ico.mp hI).1
  rcases hsing with h | h
  · exact Or.inl (by exact_mod_cast h)
  · apply Or.inr
    have hc : ((4 * t - o : ℕ) : ℤ) = 4 * (t : ℤ) - o := by
      rw [Nat.cast_sub (by omega : o ≤ 4 * t)]; push_cast; ring
    rw [← hc]
    exact_mod_cast h

variable {p : ℕ} [Fact p.Prime]

/-- Both cumulative residue tables are transported by the same class geometry. -/
theorem uniform_prefix_chain_eq {o N : ℕ} (ho : o ≤ 3) {r a b i : ℤ} (hab : a ≤ b)
    (h : NoCut (Cut p r (Singular p o)) a b) (v : ℕ → ZMod p) :
    cumulative (singularNodes p o N) v (a - i * (p : ℤ)) =
      cumulative (singularNodes p o N) v (b - i * (p : ℤ)) :=
  prefix_chain_eq hab (fun _ ht => singularNodes_singular ho ht)
    (singular_periodic p o) h

end CatalanCore.Arith.Hybrid.ChainClasses
