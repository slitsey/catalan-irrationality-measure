module
public import CatalanCore.Arith.Hybrid.Values
public import Mathlib.Data.Int.CardIntervalMod
@[expose] public section

/-!
# The sawtooth dual certificate (thirds table T, range `q < 2m`)

For every odd modulus `q` and every `r`, `m` and every level function, the residue-class potentials

* row potential `3/2, 1/2, 1` and column potential `1/2, 3/2, 1` on the class `ρ` according as
  `x_ρ < y_ρ`, `x_ρ > y_ρ`, `x_ρ = y_ρ`, where `x_ρ` (`y_ρ`) is the number of `X'`-nodes
  `r + 2i` (`Y'`-nodes `r + 2i + 1`) in `ρ`,

are feasible for `wt lev q` with no further hypothesis, of value `2(r+m) - (1/2) Σ_ρ |x_ρ - y_ρ|`.
For odd `q`, `Σ_ρ |x_ρ - y_ρ| ≥ 2 min(m mod q, q - m mod q)` (the two arcs of length `m mod q` shifted
by `(q-1)/2`), so
`tropVal (HW lev q r m) ≤ 2 (r+m) - min (m mod q) (q - m mod q)`   (`= 2(r+m) - q ‖m/q‖`).
-/

open Finset

namespace CatalanCore.Uniform.Content.Layers
open CatalanCore.Arith.Hybrid

section Saw
variable (q r m : ℕ)

/-- Number of `X'`-nodes in the class `ρ`. -/
def sawX (ρ : ℕ) : ℕ := ((range m).filter (fun i => (r + 2 * i) % q = ρ)).card
/-- Number of `Y'`-nodes in the class `ρ`. -/
def sawY (ρ : ℕ) : ℕ := ((range m).filter (fun i => (r + 2 * i + 1) % q = ρ)).card

/-- Row potential of the class `ρ`. -/
def sawRow (ρ : ℕ) : ℚ :=
  if sawX q r m ρ < sawY q r m ρ then 3 / 2 else if sawY q r m ρ < sawX q r m ρ then 1 / 2 else 1
/-- Column potential of the class `ρ`. -/
def sawCol (ρ : ℕ) : ℚ :=
  if sawX q r m ρ < sawY q r m ρ then 1 / 2 else if sawY q r m ρ < sawX q r m ρ then 3 / 2 else 1

lemma sawRow_ge (ρ : ℕ) : 1 / 2 ≤ sawRow q r m ρ := by
  unfold sawRow; split_ifs <;> norm_num
lemma sawCol_ge (ρ : ℕ) : 1 / 2 ≤ sawCol q r m ρ := by
  unfold sawCol; split_ifs <;> norm_num
lemma sawRow_add_sawCol (ρ : ℕ) : sawRow q r m ρ + sawCol q r m ρ = 2 := by
  unfold sawRow sawCol; split_ifs <;> norm_num

/-- **Feasibility, no hypothesis.** -/
lemma saw_feasible (lev : ℕ → ℕ → ℕ) (hq : 0 < q) (A B : ℕ) :
    (wt lev q A B : ℚ) ≤ sawRow q r m (A % q) + sawCol q r m (B % q) := by
  by_cases hAB : A % q = B % q
  · rw [hAB, sawRow_add_sawCol]
    exact_mod_cast wt_le_two lev q A B
  · have hne : A ≠ B := fun h => hAB (by rw [h])
    have hc : ¬ (q : ℤ) ∣ (A : ℤ) - B := by
      intro hd
      exact hAB ((Nat.modEq_iff_dvd.mpr hd).symm)
    have h1 : (wt lev q A B : ℚ) ≤ 1 := by exact_mod_cast wt_le_one_of_noncong hne hc
    have := sawRow_ge q r m (A % q)
    have := sawCol_ge q r m (B % q)
    linarith

/-- Fibre-wise summation over the residue classes. -/
lemma sum_fiber (g : ℕ → ℕ) (hg : ∀ i, g i < q) (f : ℕ → ℚ) :
    ∑ i ∈ range m, f (g i) =
      ∑ ρ ∈ range q, (((range m).filter (fun i => g i = ρ)).card : ℚ) * f ρ := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := range m) (t := range q) (g := g)
    (fun i _ => mem_range.mpr (hg i))]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [Finset.sum_congr rfl (g := fun _ => f ρ) (fun i hi => by rw [(Finset.mem_filter.mp hi).2])]
  simp

/-- The imbalance. -/
noncomputable def sawD : ℚ := ∑ ρ ∈ range q, |(sawX q r m ρ : ℚ) - sawY q r m ρ|

lemma saw_potVal (hq : 0 < q) :
    potVal (fun A => sawRow q r m (A % q)) (fun A => sawCol q r m (A % q)) r m =
      2 * (r + m) - sawD q r m / 2 := by
  unfold potVal
  beta_reduce
  have hC : ∑ c ∈ range r, (sawRow q r m (c % q) + sawCol q r m (c % q)) = 2 * r := by
    rw [Finset.sum_congr rfl (g := fun _ => (2 : ℚ)) (fun c _ => sawRow_add_sawCol q r m _)]
    simp; ring
  have hX : ∑ i ∈ range m, sawRow q r m ((r + 2 * i) % q) =
      ∑ ρ ∈ range q, (sawX q r m ρ : ℚ) * sawRow q r m ρ :=
    sum_fiber q m (fun i => (r + 2 * i) % q) (fun i => Nat.mod_lt _ hq) (sawRow q r m)
  have hY : ∑ i ∈ range m, sawCol q r m ((r + 2 * i + 1) % q) =
      ∑ ρ ∈ range q, (sawY q r m ρ : ℚ) * sawCol q r m ρ :=
    sum_fiber q m (fun i => (r + 2 * i + 1) % q) (fun i => Nat.mod_lt _ hq) (sawCol q r m)
  have e1 : ∑ ρ ∈ range q, (sawX q r m ρ : ℚ) = m := by
    have := sum_fiber q m (fun i => (r + 2 * i) % q) (fun i => Nat.mod_lt _ hq) (fun _ => (1 : ℚ))
    simpa [sawX] using this.symm
  have e2 : ∑ ρ ∈ range q, (sawY q r m ρ : ℚ) = m := by
    have := sum_fiber q m (fun i => (r + 2 * i + 1) % q) (fun i => Nat.mod_lt _ hq)
      (fun _ => (1 : ℚ))
    simpa [sawY] using this.symm
  have key : ∀ ρ ∈ range q,
      (sawX q r m ρ : ℚ) * sawRow q r m ρ + (sawY q r m ρ : ℚ) * sawCol q r m ρ =
        ((sawX q r m ρ : ℚ) + sawY q r m ρ) - (1 / 2) * |(sawX q r m ρ : ℚ) - sawY q r m ρ| := by
    intro ρ _
    unfold sawRow sawCol
    rcases lt_trichotomy (sawX q r m ρ) (sawY q r m ρ) with h | h | h
    · have h' : (sawX q r m ρ : ℚ) < sawY q r m ρ := by exact_mod_cast h
      rw [if_pos h, if_pos h, abs_of_neg (by linarith)]; ring
    · rw [h]; simp [lt_irrefl]
    · have h' : (sawY q r m ρ : ℚ) < sawX q r m ρ := by exact_mod_cast h
      rw [if_neg (by omega), if_pos h, if_neg (by omega), if_pos h, abs_of_pos (by linarith)]
      ring
  rw [hC, Finset.sum_add_distrib, hX, hY, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl key, Finset.sum_sub_distrib, Finset.sum_add_distrib, e1, e2,
    ← Finset.mul_sum]
  unfold sawD
  ring

/-- **The sawtooth certificate**, valid for every modulus `q ≥ 1`, with the exact imbalance. -/
theorem trop_saw (lev : ℕ → ℕ → ℕ) (hq : 0 < q) :
    (tropVal (HW lev q r m) : ℚ) ≤ 2 * (r + m) - sawD q r m / 2 := by
  rw [← saw_potVal q r m hq]
  apply trop_HW_le
  intro a b
  exact saw_feasible q r m lev hq _ _

end Saw

end CatalanCore.Uniform.Content.Layers
