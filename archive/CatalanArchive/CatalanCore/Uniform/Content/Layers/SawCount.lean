module
public import CatalanCore.Uniform.Content.Layers.Sawtooth
@[expose] public section

/-!
# The imbalance of the sawtooth certificate

For odd `q = 2h' + 1` and `b = m mod q`, writing the class of `r + 2t` (`t < q`), the `X'` count is
`m/q + [t < b]` and the `Y'` count is `m/q + [(t + h') mod q < b]`.  The unbalanced `t` contain two
disjoint intervals of length `min b (q - b)`, so `Σ_ρ |x_ρ - y_ρ| ≥ 2 min b (q - b)`.
-/

open Finset

namespace CatalanCore.Uniform.Content.Layers
open CatalanCore.Arith.Hybrid
variable {q r m : ℕ}

lemma coprime_two_of_odd (hq : q % 2 = 1) : Nat.Coprime q 2 := by
  have : Nat.Coprime 2 q := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  exact this.symm

lemma sawX_eq (hq : q % 2 = 1) (t : ℕ) :
    sawX q r m ((r + 2 * t) % q) = m / q + if t % q < m % q then 1 else 0 := by
  have hq0 : 0 < q := by omega
  have hfil : (range m).filter (fun i => (r + 2 * i) % q = (r + 2 * t) % q) =
      (range m).filter (fun i => i ≡ t [MOD q]) := by
    apply Finset.filter_congr
    intro i _
    constructor
    · intro h
      have h1 : r + 2 * i ≡ r + 2 * t [MOD q] := h
      have h2 : 2 * i ≡ 2 * t [MOD q] := Nat.ModEq.add_left_cancel' r h1
      exact Nat.ModEq.cancel_left_of_coprime (coprime_two_of_odd hq) h2
    · intro h
      exact ((h.mul_left 2).add_left r)
  unfold sawX
  rw [hfil, ← Nat.count_eq_card_filter_range]
  exact Nat.count_modEq_card m hq0 t

lemma sawY_eq (hq : q % 2 = 1) (t : ℕ) :
    sawY q r m ((r + 2 * t) % q) = m / q + if (t + (q - 1) / 2) % q < m % q then 1 else 0 := by
  have hq0 : 0 < q := by omega
  have hfil : (range m).filter (fun i => (r + 2 * i + 1) % q = (r + 2 * t) % q) =
      (range m).filter (fun i => i ≡ t + (q - 1) / 2 [MOD q]) := by
    apply Finset.filter_congr
    intro i _
    constructor
    · intro h
      have h1 : r + (2 * i + 1) ≡ r + 2 * t [MOD q] := by
        have : r + (2 * i + 1) = r + 2 * i + 1 := by ring
        rw [this]; exact h
      have h3 : 2 * i + 1 ≡ 2 * t [MOD q] := Nat.ModEq.add_left_cancel' r h1
      have a1 : 2 * i + q ≡ 2 * i [MOD q] := Nat.add_modEq_right
      have a2 : (2 * i + 1) + (q - 1) ≡ 2 * t + (q - 1) [MOD q] := h3.add_right _
      have e : (2 * i + 1) + (q - 1) = 2 * i + q := by omega
      rw [e] at a2
      have a3 : 2 * i ≡ 2 * t + (q - 1) [MOD q] := a1.symm.trans a2
      have e2 : 2 * t + (q - 1) = 2 * (t + (q - 1) / 2) := by omega
      rw [e2] at a3
      exact Nat.ModEq.cancel_left_of_coprime (coprime_two_of_odd hq) a3
    · intro h
      have b1 : 2 * i ≡ 2 * (t + (q - 1) / 2) [MOD q] := h.mul_left 2
      have b2 : 2 * i + 1 ≡ 2 * (t + (q - 1) / 2) + 1 [MOD q] := b1.add_right 1
      have e : 2 * (t + (q - 1) / 2) + 1 = 2 * t + q := by omega
      rw [e] at b2
      have b3 : 2 * i + 1 ≡ 2 * t [MOD q] := b2.trans Nat.add_modEq_right
      have b4 : r + (2 * i + 1) ≡ r + 2 * t [MOD q] := b3.add_left r
      have : r + (2 * i + 1) = r + 2 * i + 1 := by ring
      rw [this] at b4
      exact b4
  unfold sawY
  rw [hfil, ← Nat.count_eq_card_filter_range]
  exact Nat.count_modEq_card m hq0 _

lemma mod_of_between {n : ℕ} (h1 : q ≤ n) (h2 : n < 2 * q) : n % q = n - q := by
  rw [Nat.mod_eq_sub_mod h1]
  exact Nat.mod_eq_of_lt (by omega)

/-- Unbalanced shifts give a lower bound on the imbalance. -/
lemma sawD_ge_card (hq : q % 2 = 1) (T : Finset ℕ)
    (hT : ∀ t ∈ T, t < q ∧ ((t < m % q) ↔ ¬ ((t + (q - 1) / 2) % q < m % q))) :
    (T.card : ℚ) ≤ sawD q r m := by
  have hq0 : 0 < q := by omega
  have hinj : Set.InjOn (fun t => (r + 2 * t) % q) (T : Set ℕ) := by
    intro t ht t' ht' h
    have h1 : r + 2 * t ≡ r + 2 * t' [MOD q] := h
    have h2 : 2 * t ≡ 2 * t' [MOD q] := Nat.ModEq.add_left_cancel' r h1
    have h3 : t ≡ t' [MOD q] := Nat.ModEq.cancel_left_of_coprime (coprime_two_of_odd hq) h2
    have a := (hT t ht).1
    have b := (hT t' ht').1
    have h4 : t % q = t' % q := h3
    rwa [Nat.mod_eq_of_lt a, Nat.mod_eq_of_lt b] at h4
  have hsub : T.image (fun t => (r + 2 * t) % q) ⊆ range q := by
    intro ρ hρ
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hρ
    exact mem_range.mpr (Nat.mod_lt _ hq0)
  unfold sawD
  calc (T.card : ℚ) = ((T.image (fun t => (r + 2 * t) % q)).card : ℚ) := by
        rw [Finset.card_image_of_injOn hinj]
    _ = ∑ ρ ∈ T.image (fun t => (r + 2 * t) % q), (1 : ℚ) := by simp
    _ ≤ ∑ ρ ∈ T.image (fun t => (r + 2 * t) % q), |(sawX q r m ρ : ℚ) - sawY q r m ρ| := by
        apply Finset.sum_le_sum
        intro ρ hρ
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hρ
        obtain ⟨htq, hiff⟩ := hT t ht
        rw [sawX_eq hq, sawY_eq hq, Nat.mod_eq_of_lt htq]
        by_cases hP : t < m % q
        · have hQ : ¬ ((t + (q - 1) / 2) % q < m % q) := hiff.mp hP
          rw [if_pos hP, if_neg hQ]
          simp
        · have hQ : (t + (q - 1) / 2) % q < m % q := by
            by_contra hn; exact hP (hiff.mpr hn)
          rw [if_neg hP, if_pos hQ]
          simp
    _ ≤ ∑ ρ ∈ range q, |(sawX q r m ρ : ℚ) - sawY q r m ρ| := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro _ _ _; exact abs_nonneg _

/-- `q ‖m/q‖` for the integer pair `(m, q)`. -/
def sawM (q m : ℕ) : ℕ := min (m % q) (q - m % q)

/-- **The imbalance of the sawtooth certificate**: `Σ_ρ |x_ρ - y_ρ| ≥ 2 min (m mod q) (q - m mod q)`. -/
theorem sawD_ge (hq : q % 2 = 1) :
    (2 * (sawM q m : ℚ)) ≤ sawD q r m := by
  have hq0 : 0 < q := by omega
  unfold sawM
  have hb : m % q < q := Nat.mod_lt _ hq0
  set b := m % q with hbdef
  set h' := (q - 1) / 2 with hh'
  have hqh : q = 2 * h' + 1 := by omega
  by_cases hcase : b ≤ h'
  · -- two disjoint arcs of length b
    have hmin : min b (q - b) = b := by apply min_eq_left; omega
    let T : Finset ℕ := Ico 0 b ∪ Ico (h' + 1) (h' + 1 + b)
    have hdis : Disjoint (Ico 0 b) (Ico (h' + 1) (h' + 1 + b)) := by
      rw [Finset.disjoint_left]; intro t h1 h2
      have := mem_Ico.mp h1; have := mem_Ico.mp h2; omega
    have hcard : T.card = 2 * b := by
      simp only [T]
      rw [card_union_of_disjoint hdis]; simp; omega
    have := sawD_ge_card (r := r) (m := m) hq T (by
      intro t ht
      simp only [T, mem_union, mem_Ico] at ht
      rcases ht with ht | ht
      · refine ⟨by omega, ?_⟩
        have e : (t + h') % q = t + h' := Nat.mod_eq_of_lt (by omega)
        rw [e]; constructor <;> intro _ <;> omega
      · refine ⟨by omega, ?_⟩
        have e : (t + h') % q = t + h' - q := mod_of_between (by omega) (by omega)
        rw [e]; constructor <;> intro _ <;> omega)
    rw [hcard] at this
    rw [hmin]; exact_mod_cast this
  · -- two disjoint arcs of length q - b
    have hmin : min b (q - b) = q - b := by apply min_eq_right; omega
    let T : Finset ℕ := Ico b q ∪ Ico (b - h') (q - h')
    have hdis : Disjoint (Ico b q) (Ico (b - h') (q - h')) := by
      rw [Finset.disjoint_left]; intro t h1 h2
      have := mem_Ico.mp h1; have := mem_Ico.mp h2; omega
    have hcard : T.card = 2 * (q - b) := by
      simp only [T]
      rw [card_union_of_disjoint hdis]; simp; omega
    have := sawD_ge_card (r := r) (m := m) hq T (by
      intro t ht
      simp only [T, mem_union, mem_Ico] at ht
      rcases ht with ht | ht
      · refine ⟨by omega, ?_⟩
        have e : (t + h') % q = t + h' - q := mod_of_between (by omega) (by omega)
        rw [e]; constructor <;> intro _ <;> omega
      · refine ⟨by omega, ?_⟩
        have e : (t + h') % q = t + h' := Nat.mod_eq_of_lt (by omega)
        rw [e]; constructor <;> intro _ <;> omega)
    rw [hcard] at this
    rw [hmin]; exact_mod_cast this

/-- **Sawtooth bound, closed form** (`= 2(r+m) - q ‖m/q‖`), odd modulus, no other hypothesis. -/
theorem trop_saw_closed (lev : ℕ → ℕ → ℕ) (hq : q % 2 = 1) :
    tropVal (HW lev q r m) + sawM q m ≤ 2 * (r + m) := by
  have hq0 : 0 < q := by omega
  have h1 := trop_saw q r m lev hq0
  have h2 := sawD_ge (r := r) (m := m) hq
  have : ((tropVal (HW lev q r m) + sawM q m : ℕ) : ℚ) ≤ ((2 * (r + m) : ℕ) : ℚ) := by
    push_cast
    linarith
  exact_mod_cast this

end CatalanCore.Uniform.Content.Layers
