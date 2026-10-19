module

public import CatalanCore.Bordered.Z1.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.LinearCombination

/-!
# Z1.2 (part 2): scalar ratio identities for `Λ₁, Λ₂, ρ, X′`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered.Z1

/-- Shift identity for a descending product. -/
lemma prod_shift (c y : ℚ) (n : ℕ) :
    (∏ i ∈ range n, (y - 1 - c - i)) * (y - c) = (∏ i ∈ range n, (y - c - i)) * (y - c - n) := by
  have h1 : (∏ i ∈ range n, (y - c - i)) * (y - c - n) = ∏ i ∈ range (n + 1), (y - c - i) := by
    rw [prod_range_succ]
  have h2 : ∏ i ∈ range (n + 1), (y - c - i) = (∏ i ∈ range n, (y - c - ((i + 1 : ℕ) : ℚ))) * (y - c - ((0 : ℕ) : ℚ)) :=
    prod_range_succ' (fun i : ℕ => y - c - (i : ℚ)) n
  rw [h1, h2]
  congr 1
  · apply prod_congr rfl; intro i _; push_cast; ring
  · simp

lemma PiX_mul_PiY (s m j : ℕ) :
    PiX s m j * PiY s m j = ∏ i ∈ range (2 * m), ((j : ℚ) - ((s + 1 : ℕ) : ℚ) - i) := by
  induction m with
  | zero => simp [PiX, PiY]
  | succ m ih =>
    have e : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    rw [e, prod_range_succ, prod_range_succ, ← ih]
    simp only [PiX, PiY, prod_range_succ]
    push_cast
    ring

lemma PiXY_shift (s m k : ℕ) :
    PiX s m (k + 1) * PiY s m (k + 1) * ((s : ℚ) - k - 1) =
      PiX s m (k + 2) * PiY s m (k + 2) * ((s : ℚ) + 2 * m - k - 1) := by
  rw [PiX_mul_PiY, PiX_mul_PiY]
  have h := prod_shift ((s + 1 : ℕ) : ℚ) ((k : ℚ) + 2) (2 * m)
  push_cast at h ⊢
  have e3 : ∀ i : ℕ, ((k : ℚ) + 1 - (s + 1) - i) = ((k : ℚ) + 2 - 1 - (s + 1) - i) := fun i => by ring
  simp only [e3]
  linear_combination (-1 : ℚ) * h

lemma PiX_ne (s m j : ℕ) (hj : j ≤ s) : PiX s m j ≠ 0 := by
  unfold PiX
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  have : (j : ℚ) ≤ s := by exact_mod_cast hj
  push_cast
  intro h
  have : (0 : ℚ) ≤ 2 * i := by positivity
  linarith

lemma omegaP_ne (s j : ℕ) : omegaP s j ≠ 0 := by
  unfold omegaP
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_) ?_ <;> exact_mod_cast Nat.factorial_ne_zero _

lemma omegaP_succ (s j : ℕ) (hj : 1 ≤ j) (hjs : j < s) :
    omegaP s (j + 1) * ((s : ℚ) - j) = -(j : ℚ) * omegaP s j := by
  obtain ⟨t, rfl⟩ : ∃ t, j = t + 1 := ⟨j - 1, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, s = t + 2 + u := ⟨s - (t + 2), by omega⟩
  have e1 : t + 2 + u - (t + 1 + 1) = u := by omega
  have e2 : t + 2 + u - (t + 1) = u + 1 := by omega
  simp only [omegaP, e1, e2, Nat.add_sub_cancel, Nat.factorial_succ, pow_succ]
  push_cast
  ring

lemma poch_succ (θ : ℚ) (K j : ℕ) : poch θ K (j + 1) * (θ + j) = poch θ K j * (θ + j + K) := by
  have h1 : poch θ K j * (θ + j + K) = ∏ a ∈ range (K + 1), (θ + ((j + a : ℕ) : ℚ)) := by
    rw [prod_range_succ]; unfold poch; push_cast; ring
  have h2 : ∏ a ∈ range (K + 1), (θ + ((j + a : ℕ) : ℚ)) =
      (∏ a ∈ range K, (θ + ((j + (a + 1) : ℕ) : ℚ))) * (θ + ((j + 0 : ℕ) : ℚ)) :=
    prod_range_succ' (fun a : ℕ => θ + ((j + a : ℕ) : ℚ)) K
  rw [h1, h2]
  unfold poch
  congr 1
  all_goals first | (apply prod_congr rfl; intro i _; push_cast; ring) | (push_cast; ring)

lemma Zp_shift (s m : ℕ) (x : ℚ) :
    Zp s m (x + 1) * (x + s + 1) = Zp s m x * (x + s + 1 + 2 * m) := by
  have h1 : Zp s m x * (x + s + 1 + 2 * m) = ∏ i ∈ range (2 * m + 1), (x + ((s + 1 + i : ℕ) : ℚ)) := by
    rw [prod_range_succ]; unfold Zp; push_cast; ring
  have h2 : ∏ i ∈ range (2 * m + 1), (x + ((s + 1 + i : ℕ) : ℚ)) =
      (∏ i ∈ range (2 * m), (x + ((s + 1 + (i + 1) : ℕ) : ℚ))) * (x + ((s + 1 + 0 : ℕ) : ℚ)) :=
    prod_range_succ' (fun i : ℕ => x + ((s + 1 + i : ℕ) : ℚ)) (2 * m)
  rw [h1, h2]
  unfold Zp
  congr 1
  all_goals first | (apply prod_congr rfl; intro i _; push_cast; ring) | (push_cast; ring)

/-- Node weights: `c_a (K-1-a)² = c_{a+1} (a+1)²`. -/
lemma rho_ratio (s m a : ℕ) (θ : ℚ) (ha : a + 1 < s + m) :
    rho s m θ a * ((θ + a + 1) * (θ + a + 1 + s + 2 * m) * (((s + m : ℕ) : ℚ) - 1 - a) ^ 2) =
      rho s m θ (a + 1) * ((θ + a + 1) * (((a : ℚ) + 1) ^ 2) * (θ + a + 1 + s)) := by
  obtain ⟨d, hd⟩ : ∃ d, s + m = a + d + 2 := ⟨s + m - a - 2, by omega⟩
  have e1 : s + m - 1 - a = d + 1 := by omega
  have e2 : s + m - 1 - (a + 1) = d := by omega
  have hz := Zp_shift s m (θ + a)
  simp only [rho, qc, Algebra.algebraMap_self, RingHom.id_apply, e1, e2]
  have e3 : θ + ((a + 1 : ℕ) : ℚ) = θ + a + 1 := by push_cast; ring
  rw [e3]
  have e4 : (((s + m : ℕ) : ℚ) - 1 - a) = (d : ℚ) + 1 := by rw [hd]; push_cast; ring
  rw [e4]
  have f1 : ((d + 1).factorial : ℚ) = ((d : ℚ) + 1) * d.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f2 : ((a + 1).factorial : ℚ) = ((a : ℚ) + 1) * a.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have fa : (a.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have fd : (d.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have ha1 : (a : ℚ) + 1 ≠ 0 := by positivity
  have hd1 : (d : ℚ) + 1 ≠ 0 := by positivity
  push_cast
  rw [f1, f2]
  field_simp
  linear_combination (-(θ + a + 1)) * hz

end CatalanCore.Bordered.Z1
