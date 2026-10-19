module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Harmonic reflection modulo `p` (DQ Lemma 3.1, steps 2-4)

`Gs f n = ∑_{j<n} f(j+1)` in `ZMod p`.  For `f = inv` (harmonic numbers) and `f = inv²`
(`H2`), `∑_{j<p-1} f(j+1) = 0` (power sums over the field) and the reflection
`H_{p-1-n} = H_n`, `H2_{p-1-n} = -H2_n` follows from `f(-x) = ± f(x)`.
These are the two congruences behind the scalar Schur complement `S̄ = s₀ I`.
-/

open Finset

namespace CatalanCore.Arith.Hybrid.LemmaE

variable (p : ℕ) [Fact p.Prime]

/-- `∑_{j<n} f(j+1)` in `ZMod p`. -/
def Gs (f : ZMod p → ZMod p) (n : ℕ) : ZMod p := ∑ j ∈ range n, f ((j + 1 : ℕ) : ZMod p)

lemma sum_range_cast (f : ZMod p → ZMod p) :
    ∑ k ∈ range p, f ((k : ℕ) : ZMod p) = ∑ x : ZMod p, f x := by
  have himg : (range p).image (fun k : ℕ => (k : ZMod p)) = Finset.univ := by
    ext x
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_univ, iff_true]
    exact ⟨x.val, ZMod.val_lt x, ZMod.natCast_zmod_val x⟩
  have hinj : Set.InjOn (fun k : ℕ => (k : ZMod p)) (range p : Finset ℕ) := by
    intro a ha b hb hab
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    have := congrArg ZMod.val hab
    simpa [ZMod.val_cast_of_lt ha', ZMod.val_cast_of_lt hb'] using this
  rw [← himg, Finset.sum_image hinj]

lemma sum_range_pow (i : ℕ) (hi : i < p - 1) : ∑ k ∈ range p, ((k : ℕ) : ZMod p) ^ i = 0 := by
  rw [sum_range_cast p (fun x => x ^ i)]
  exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) i (by rwa [ZMod.card])

lemma inv_eq_pow' (x : ZMod p) (hx : x ≠ 0) : x⁻¹ = x ^ (p - 2) := by
  have h1 : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
  have hp2 := (Fact.out : p.Prime).two_le
  have : x * x ^ (p - 2) = 1 := by
    rw [← pow_succ']; rwa [show p - 2 + 1 = p - 1 by omega]
  exact inv_eq_of_mul_eq_one_right this

lemma inv_sq_eq_pow (x : ZMod p) (hx : x ≠ 0) (hp : 3 ≤ p) : (x⁻¹) ^ 2 = x ^ (p - 3) := by
  have h1 : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
  have : x ^ (p - 3) * x ^ 2 = 1 := by
    rw [← pow_add]; rwa [show p - 3 + 2 = p - 1 by omega]
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  rw [inv_pow]
  exact inv_eq_of_mul_eq_one_right (by rw [mul_comm]; exact this)

lemma cast_succ_ne_zero {j : ℕ} (hj : j + 1 < p) : (((j + 1 : ℕ)) : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd (Nat.succ_pos j) h) (by omega)

lemma sum_shift (g : ℕ → ZMod p) (hg : g 0 = 0) (hp : 1 ≤ p) :
    ∑ k ∈ range p, g k = ∑ j ∈ range (p - 1), g (j + 1) := by
  have hr : range p = range ((p - 1) + 1) := by rw [Nat.sub_add_cancel hp]
  rw [hr, Finset.sum_range_succ', hg, add_zero]

/-- Total harmonic sum: `H_{p-1} = 0`. -/
lemma Gs_inv_top (hp : 3 ≤ p) : Gs p (fun x => x⁻¹) (p - 1) = 0 := by
  have h := sum_range_pow p (p - 2) (by omega)
  rw [sum_shift p (fun k => ((k : ℕ) : ZMod p) ^ (p - 2)) (by simp [show p - 2 ≠ 0 by omega])
    (by omega)] at h
  rw [← h]
  unfold Gs
  refine Finset.sum_congr rfl fun j hj => ?_
  exact inv_eq_pow' p _ (cast_succ_ne_zero p (by have := Finset.mem_range.mp hj; omega))

/-- Total `H2` sum: `H2_{p-1} = 0` for `p ≥ 5`. -/
lemma Gs_inv_sq_top (hp : 5 ≤ p) : Gs p (fun x => (x⁻¹) ^ 2) (p - 1) = 0 := by
  have h := sum_range_pow p (p - 3) (by omega)
  rw [sum_shift p (fun k => ((k : ℕ) : ZMod p) ^ (p - 3)) (by simp [show p - 3 ≠ 0 by omega])
    (by omega)] at h
  rw [← h]
  unfold Gs
  refine Finset.sum_congr rfl fun j hj => ?_
  exact inv_sq_eq_pow p _ (cast_succ_ne_zero p (by have := Finset.mem_range.mp hj; omega))
    (by omega)

/-- **Reflection.**  If `f(-x) = ε f(x)` and the total sum vanishes, then
`G_{p-1-n} = -ε G_n`. -/
lemma Gs_refl (f : ZMod p → ZMod p) (ε : ZMod p) (hf : ∀ x, f (-x) = ε * f x)
    (htop : Gs p f (p - 1) = 0) {n : ℕ} (hn : n ≤ p - 1) :
    Gs p f (p - 1 - n) = -ε * Gs p f n := by
  have hsplit : Gs p f (p - 1) = Gs p f (p - 1 - n) +
      ∑ j ∈ range n, f ((((p - 1 - n) + j + 1 : ℕ)) : ZMod p) := by
    unfold Gs
    have := Finset.sum_range_add (fun x : ℕ => f ((x + 1 : ℕ) : ZMod p)) (p - 1 - n) n
    rw [show p - 1 - n + n = p - 1 by omega] at this
    rw [this]
  have hterm : ∀ j ∈ range n, f ((((p - 1 - n) + j + 1 : ℕ)) : ZMod p) =
      ε * f ((((n - 1 - j) + 1 : ℕ)) : ZMod p) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have h1 : ((((p - 1 - n) + j + 1 : ℕ)) : ZMod p) = -((((n - 1 - j) + 1 : ℕ)) : ZMod p) := by
      apply eq_neg_of_add_eq_zero_left
      have : ((p - 1 - n) + j + 1) + ((n - 1 - j) + 1) = p := by omega
      rw [← Nat.cast_add, this]
      exact ZMod.natCast_self p
    rw [h1, hf]
  have hsum : ∑ j ∈ range n, f ((((p - 1 - n) + j + 1 : ℕ)) : ZMod p) = ε * Gs p f n := by
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    congr 1
    exact Finset.sum_range_reflect (fun j : ℕ => f ((j + 1 : ℕ) : ZMod p)) n
  rw [hsum, htop] at hsplit
  linear_combination -hsplit

lemma H_refl (hp : 3 ≤ p) {n : ℕ} (hn : n ≤ p - 1) :
    Gs p (fun x => x⁻¹) (p - 1 - n) = Gs p (fun x => x⁻¹) n := by
  have := Gs_refl p (fun x => x⁻¹) (-1) (fun x => by simp [inv_neg]) (Gs_inv_top p hp) hn
  simpa using this

lemma H2_refl (hp : 5 ≤ p) {n : ℕ} (hn : n ≤ p - 1) :
    Gs p (fun x => (x⁻¹) ^ 2) (p - 1 - n) = -Gs p (fun x => (x⁻¹) ^ 2) n := by
  have := Gs_refl p (fun x => (x⁻¹) ^ 2) 1 (fun x => by simp [inv_neg]) (Gs_inv_sq_top p hp) hn
  simpa using this

/-- Tail sums: `∑_{c=K}^{p-1} f(c-u) = G_{p-1-u} - G_{K-1-u}` for `u < K ≤ p`. -/
lemma tail_sum (f : ZMod p → ZMod p) {K u : ℕ} (hu : u < K) (hK : K ≤ p) :
    ∑ c ∈ Ico K p, f (((c : ℕ) : ZMod p) - u) = Gs p f (p - 1 - u) - Gs p f (K - 1 - u) := by
  have e1 : ∑ c ∈ Ico K p, f (((c : ℕ) : ZMod p) - u) =
      ∑ j ∈ range (p - K), f ((((K - 1 - u) + j + 1 : ℕ)) : ZMod p) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    apply sub_eq_of_eq_add
    have : (K - 1 - u + j + 1) + u = K + j := by omega
    rw [← Nat.cast_add, this]
  have e2 := Finset.sum_range_add (fun x : ℕ => f ((x + 1 : ℕ) : ZMod p)) (K - 1 - u) (p - K)
  rw [show K - 1 - u + (p - K) = p - 1 - u by omega] at e2
  unfold Gs
  rw [e1]
  rw [e2]; ring

/-- **Off-diagonal scalar Schur identity** (DQ Lemma 3.1, steps 2-3):
`φ(u) - φ(w) + ∑_{c=K}^{p-1} (1/(c-w) - 1/(c-u)) = 0` with `φ(n) = H_n + H_{K-1} - H_{K-1-n}`. -/
theorem schur_offdiag (hp : 3 ≤ p) {K u w : ℕ} (hK : K ≤ p - 1) (hu : u < K) (hw : w < K) :
    (Gs p (fun x => x⁻¹) u + Gs p (fun x => x⁻¹) (K - 1) - Gs p (fun x => x⁻¹) (K - 1 - u)) -
      (Gs p (fun x => x⁻¹) w + Gs p (fun x => x⁻¹) (K - 1) - Gs p (fun x => x⁻¹) (K - 1 - w)) +
      ∑ c ∈ Ico K p, ((((c : ℕ) : ZMod p) - w)⁻¹ - (((c : ℕ) : ZMod p) - u)⁻¹) = 0 := by
  rw [Finset.sum_sub_distrib, tail_sum p (fun x => x⁻¹) hw (by omega),
    tail_sum p (fun x => x⁻¹) hu (by omega), H_refl p hp (by omega : u ≤ p - 1),
    H_refl p hp (by omega : w ≤ p - 1)]
  ring

/-- **Diagonal scalar Schur identity** (DQ Lemma 3.1, step 4):
`H2_u - H2_{K-1} + H2_{K-1-u} + ∑_{c=K}^{p-1} 1/(c-u)² = -H2_{K-1}`. -/
theorem schur_diag (hp : 5 ≤ p) {K u : ℕ} (hK : K ≤ p - 1) (hu : u < K) :
    Gs p (fun x => (x⁻¹) ^ 2) u - Gs p (fun x => (x⁻¹) ^ 2) (K - 1) +
      Gs p (fun x => (x⁻¹) ^ 2) (K - 1 - u) +
      ∑ c ∈ Ico K p, ((((c : ℕ) : ZMod p) - u)⁻¹) ^ 2 = -Gs p (fun x => (x⁻¹) ^ 2) (K - 1) := by
  rw [tail_sum p (fun x => (x⁻¹) ^ 2) hu (by omega), H2_refl p hp (by omega : u ≤ p - 1)]
  ring

/-! ### Partial sums of `1/(k(4k-1))` and `1/(16k²) - 1/(4k-1)²` modulo `p` -/

/-- Block of consecutive terms: `∑_{j<n} f(K-1-j) = G_{K-1} - G_{K-1-n}` for `n ≤ K-1`. -/
lemma sum_range_Kminus (f : ZMod p → ZMod p) {K n : ℕ} (hn : n ≤ K - 1) :
    ∑ j ∈ range n, f ((((K - 1 - j : ℕ)) : ZMod p)) + 0 = Gs p f (K - 1) - Gs p f (K - 1 - n) := by
  have e2 := Finset.sum_range_add (fun x : ℕ => f ((x + 1 : ℕ) : ZMod p)) (K - 1 - n) n
  rw [show K - 1 - n + n = K - 1 by omega] at e2
  have e3 := Finset.sum_range_reflect (fun j : ℕ => f (((K - 1 - n + j + 1 : ℕ)) : ZMod p)) n
  unfold Gs
  rw [e2, add_zero]
  have : ∑ j ∈ range n, f ((((K - 1 - j : ℕ)) : ZMod p)) =
      ∑ j ∈ range n, f (((K - 1 - n + (n - 1 - j) + 1 : ℕ)) : ZMod p) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have := Finset.mem_range.mp hj
    congr 2
    omega
  rw [this, e3]
  ring

variable {p}

/-- `4K ≡ 1`. -/
lemma four_K (K : ℕ) (hK : ((4 * K - 1 : ℕ) : ZMod p) = 0) (hK1 : 1 ≤ K) :
    4 * (K : ZMod p) = 1 := by
  have : (4 * K - 1 : ℕ) + 1 = 4 * K := by omega
  have h2 : (((4 * K - 1 : ℕ) + 1 : ℕ) : ZMod p) = 1 := by push_cast; rw [hK]; simp
  rw [this] at h2
  push_cast at h2
  exact h2

lemma term_mod (hp : 3 ≤ p) {K k : ℕ} (hK4 : 4 * (K : ZMod p) = 1) (hk1 : 1 ≤ k) (hkK : k < K)
    (hKp : K < p) :
    (((k : ℕ) : ZMod p) * (((4 * k - 1 : ℕ)) : ZMod p))⁻¹ =
      -(((K - k : ℕ)) : ZMod p)⁻¹ - ((k : ℕ) : ZMod p)⁻¹ := by
  have hk0 : ((k : ℕ) : ZMod p) ≠ 0 := by
    intro h; rw [ZMod.natCast_eq_zero_iff] at h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hKk : (((K - k : ℕ)) : ZMod p) ≠ 0 := by
    intro h; rw [ZMod.natCast_eq_zero_iff] at h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have e1 : (((4 * k - 1 : ℕ)) : ZMod p) = 4 * (k : ZMod p) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : (((K - k : ℕ)) : ZMod p) = (K : ZMod p) - k := by
    rw [Nat.cast_sub hkK.le]
  rw [e2] at hKk
  have e1' : (((4 * k - 1 : ℕ)) : ZMod p) = -4 * ((K : ZMod p) - k) := by
    rw [e1]; linear_combination hK4
  have h4 : (4 : ZMod p) ≠ 0 := by intro h; rw [h] at hK4; simp at hK4
  rw [e1', e2]
  field_simp
  linear_combination hK4

lemma psi_term_mod (hp : 3 ≤ p) {K k : ℕ} (hK4 : 4 * (K : ZMod p) = 1) (hk1 : 1 ≤ k) (hkK : k < K)
    (hKp : K < p) :
    16 * ((16 * ((k : ℕ) : ZMod p) ^ 2)⁻¹ - ((((4 * k - 1 : ℕ)) : ZMod p) ^ 2)⁻¹) =
      (((k : ℕ) : ZMod p)⁻¹) ^ 2 - ((((K - k : ℕ)) : ZMod p)⁻¹) ^ 2 := by
  have hk0 : ((k : ℕ) : ZMod p) ≠ 0 := by
    intro h; rw [ZMod.natCast_eq_zero_iff] at h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hKk : (((K - k : ℕ)) : ZMod p) ≠ 0 := by
    intro h; rw [ZMod.natCast_eq_zero_iff] at h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have e1 : (((4 * k - 1 : ℕ)) : ZMod p) = 4 * (k : ZMod p) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e2 : (((K - k : ℕ)) : ZMod p) = (K : ZMod p) - k := by
    rw [Nat.cast_sub hkK.le]
  rw [e2] at hKk ⊢
  have e1' : (((4 * k - 1 : ℕ)) : ZMod p) = -4 * ((K : ZMod p) - k) := by
    rw [e1]; linear_combination hK4
  have h4 : (4 : ZMod p) ≠ 0 := by intro h; rw [h] at hK4; simp at hK4
  have h16 : (16 : ZMod p) ≠ 0 := by
    have : (16 : ZMod p) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h4 h4
  rw [e1']
  field_simp
  ring

/-- `∑_{k≤n} 1/(k(4k-1)) ≡ -(φ(n))` with `φ(n) = H_n + H_{K-1} - H_{K-1-n}`. -/
theorem Fz_eq (hp : 3 ≤ p) {K n : ℕ} (hK4 : 4 * (K : ZMod p) = 1) (hKp : K < p)
    (hn : n ≤ K - 1) :
    ∑ j ∈ range n, ((((j + 1 : ℕ)) : ZMod p) * (((4 * (j + 1) - 1 : ℕ)) : ZMod p))⁻¹ =
      -(Gs p (fun x => x⁻¹) (K - 1) - Gs p (fun x => x⁻¹) (K - 1 - n)) -
        Gs p (fun x => x⁻¹) n := by
  have h1 : ∀ j ∈ range n, ((((j + 1 : ℕ)) : ZMod p) * (((4 * (j + 1) - 1 : ℕ)) : ZMod p))⁻¹ =
      -((((K - 1 - j : ℕ)) : ZMod p))⁻¹ - ((((j + 1 : ℕ)) : ZMod p))⁻¹ := by
    intro j hj
    have := Finset.mem_range.mp hj
    have := term_mod hp hK4 (k := j + 1) (by omega) (by omega) hKp
    rw [this, show K - (j + 1) = K - 1 - j by omega]
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have := sum_range_Kminus p (fun x => x⁻¹) hn
  rw [add_zero] at this
  rw [this]
  rfl

/-- `16 ∑_{k≤n} (1/(16k²) - 1/(4k-1)²) ≡ H2_n - H2_{K-1} + H2_{K-1-n}`. -/
theorem Psi_eq (hp : 3 ≤ p) {K n : ℕ} (hK4 : 4 * (K : ZMod p) = 1) (hKp : K < p)
    (hn : n ≤ K - 1) :
    16 * ∑ j ∈ range n, ((16 * (((j + 1 : ℕ)) : ZMod p) ^ 2)⁻¹ -
        ((((4 * (j + 1) - 1 : ℕ)) : ZMod p) ^ 2)⁻¹) =
      Gs p (fun x => (x⁻¹) ^ 2) n - Gs p (fun x => (x⁻¹) ^ 2) (K - 1) +
        Gs p (fun x => (x⁻¹) ^ 2) (K - 1 - n) := by
  rw [Finset.mul_sum]
  have h1 : ∀ j ∈ range n, 16 * ((16 * (((j + 1 : ℕ)) : ZMod p) ^ 2)⁻¹ -
        ((((4 * (j + 1) - 1 : ℕ)) : ZMod p) ^ 2)⁻¹) =
      ((((j + 1 : ℕ)) : ZMod p)⁻¹) ^ 2 - (((((K - 1 - j : ℕ)) : ZMod p))⁻¹) ^ 2 := by
    intro j hj
    have := Finset.mem_range.mp hj
    have := psi_term_mod hp hK4 (k := j + 1) (by omega) (by omega) hKp
    rw [this, show K - (j + 1) = K - 1 - j by omega]
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib]
  have := sum_range_Kminus p (fun x => (x⁻¹) ^ 2) hn
  rw [add_zero] at this
  rw [this]
  unfold Gs
  ring

end CatalanCore.Arith.Hybrid.LemmaE
