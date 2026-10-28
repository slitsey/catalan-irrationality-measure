module

public import CatalanCore.Uniform.Content.UFFamily.Empty

@[expose] public section

/-!
# UF families with non-empty fibers: the fiber of a border node (lane H, H11)

The core is `range r` (`c` enumerates it).  A border node `v ≥ r` has the core nodes
`v - j p` (`j₀ ≤ j < j₀ + n`) in its residue fiber.  With `A = ⌊v/p⌋`, `B = ⌊(q v - o)/p⌋`
their floor pairs are `(A - j, B - q j)`, so the joint type of `v` is `famType q A B j₀ n`,
a function of four small integers.  `fiberList_range` is the `FiberList` of such a fiber for every
`(r, p, v)` satisfying six affine inequalities; `fiberList_empty` of `UFFamily` is the case `n = 0`.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.UFFamily

namespace CatalanCore.Uniform.Content.UFFamily2

/-- The joint type of a node with `A = ⌊v/p⌋`, `B = ⌊(q v - o)/p⌋` whose fiber is the core nodes
`v - j p`, `j₀ ≤ j < j₀ + n`. -/
def famType (q A B j0 n : ℕ) : JType where
  nodes := (List.range n).map fun i => (A - (j0 + i), B - q * (j0 + i))
  zone := (A, B)

theorem famType_len (q A B j0 n : ℕ) : (famType q A B j0 n).nodes.length = n := by
  simp [famType]

theorem famType_node (q A B j0 n : ℕ) {i : ℕ} (hi : i < n) :
    (famType q A B j0 n).node i = (A - (j0 + i), B - q * (j0 + i)) := by
  simp [famType, JType.node, List.getD_eq_getElem?_getD, hi]

variable {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `⌊(v - j p)/p⌋ = ⌊v/p⌋ - j`. -/
theorem div_fib {v j : ℕ} (hp : 0 < p) (h : j * p ≤ v) : (v - j * p) / p = v / p - j := by
  rw [mul_comm]; exact Nat.sub_mul_div v p j

/-- `⌊(q (v - j p) - o)/p⌋ = ⌊(q v - o)/p⌋ - q j` when `o ≤ q (v - j p)`. -/
theorem div_fib2 {q o v j : ℕ} (hp : 0 < p) (h : o ≤ q * (v - j * p)) (hj : j * p ≤ v) :
    (q * (v - j * p) - o) / p = (q * v - o) / p - q * j := by
  have e : q * (v - j * p) - o = (q * v - o) - (q * j) * p := by
    have h1 : q * (v - j * p) = q * v - q * (j * p) := Nat.mul_sub q v (j * p)
    have h2 : q * (j * p) ≤ q * v := Nat.mul_le_mul_left q hj
    rw [h1, ← mul_assoc] at *
    omega
  rw [e, show q * j * p = p * (q * j) by ring]; exact Nat.sub_mul_div (q * v - o) p (q * j)

/-- **The fiber of a border node.**  The core is `range r` (`c` is an injective enumeration of it);
the fiber of `v ≥ r` is `{v - j p : j₀ ≤ j < j₀ + n}` with all these `≥ 1`. -/
noncomputable def fiberList_range (q o r v j0 n A B : ℕ) (c : ι → ℕ) (hcr : ∀ a, c a < r)
    (hcov : ∀ x, x < r → ∃ a, c a = x) (hcinj : Function.Injective c) (hrv : r ≤ v) (hqo : o ≤ q)
    (hj0 : 1 ≤ j0) (hlo : v - j0 * p < r) (hlo' : ∀ j, 1 ≤ j → j < j0 → r ≤ v - j * p)
    (hhi : v < (j0 + n) * p) (hhi' : n = 0 ∨ (j0 + n - 1) * p < v) (hA : v / p = A)
    (hB : (q * v - o) / p = B) : FiberList p q o c v (famType q A B j0 n) := by
  subst hA hB
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hjp : ∀ i, i < n → (j0 + i) * p < v := by
    intro i hi
    rcases hhi' with h0 | h1
    · omega
    · exact lt_of_le_of_lt (Nat.mul_le_mul_right p (by omega)) h1
  have hxr : ∀ i, i < n → v - (j0 + i) * p < r := by
    intro i hi
    have : (j0 + i) * p ≥ j0 * p := Nat.mul_le_mul_right p (by omega)
    omega
  let g : Fin (famType q (v / p) ((q * v - o) / p) j0 n).nodes.length → ι := fun i =>
    Classical.choose (hcov (v - (j0 + i.1) * p) (hxr i.1 (by simpa [famType_len] using i.2)))
  have hg : ∀ i : Fin (famType q (v / p) ((q * v - o) / p) j0 n).nodes.length,
      c (g i) = v - (j0 + i.1) * p := fun i =>
    Classical.choose_spec (hcov (v - (j0 + i.1) * p) (hxr i.1 (by simpa [famType_len] using i.2)))
  have hlen : ∀ i : Fin (famType q (v / p) ((q * v - o) / p) j0 n).nodes.length, i.1 < n :=
    fun i => by simpa [famType_len] using i.2
  refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i k hik
    have h1 := hg i
    have h2 := hg k
    rw [hik] at h1
    have h3 : v - (j0 + i.1) * p = v - (j0 + k.1) * p := h1.symm.trans h2
    have hi := hjp i.1 (hlen i)
    have hk := hjp k.1 (hlen k)
    have : (j0 + i.1) * p = (j0 + k.1) * p := by omega
    have := Nat.eq_of_mul_eq_mul_right hp this
    exact Fin.ext (by omega)
  · intro i
    rw [hg i]
    have hle : (j0 + i.1) * p ≤ v := (hjp i.1 (hlen i)).le
    rw [Nat.cast_sub hle, Nat.cast_mul, ZMod.natCast_self, mul_zero, sub_zero]
  · intro a ha
    have hxa := hcr a
    have h1 := (ZMod.natCast_eq_natCast_iff' _ _ p).1 ha
    have hdv : p ∣ v - c a := (Nat.modEq_iff_dvd' (by omega)).1 h1
    obtain ⟨j', hj'⟩ := hdv
    -- v - c a = p * j'
    have hj1 : 1 ≤ j' := by
      rcases Nat.eq_zero_or_pos j' with h | h
      · rw [h] at hj'; omega
      · exact h
    have hca : c a = v - j' * p := by rw [mul_comm]; omega
    have hjle : j' * p ≤ v := by rw [mul_comm]; omega
    have hge : j0 ≤ j' := by
      by_contra hc
      push Not at hc
      have := hlo' j' hj1 hc
      omega
    have hlt : j' < j0 + n := by
      by_contra hc
      push Not at hc
      have : (j0 + n) * p ≤ j' * p := Nat.mul_le_mul_right p hc
      omega
    refine ⟨⟨j' - j0, by simpa [famType_len] using (by omega : j' - j0 < n)⟩, hcinj ?_⟩
    rw [hg, hca]
    simp only
    have : j0 + (j' - j0) = j' := by omega
    rw [this]
  · intro i
    rw [hg i]
    have := hjp i.1 (hlen i)
    have h0 : 0 < (j0 + i.1) * p := Nat.mul_pos (by omega) hp
    omega
  · intro i
    have hi := hlen i
    rw [famType_node q _ _ j0 n hi, hg i]
    have hle : (j0 + i.1) * p ≤ v := (hjp i.1 hi).le
    have hpos : 1 ≤ v - (j0 + i.1) * p := by have := hjp i.1 hi; omega
    have hqc : o ≤ q * (v - (j0 + i.1) * p) :=
      le_trans hqo (Nat.le_mul_of_pos_right q hpos)
    rw [div_fib hp hle, div_fib2 hp hqc hle]
  · rfl

end CatalanCore.Uniform.Content.UFFamily2
