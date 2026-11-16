module

public import CatalanCore.Zeta5.Frames.OuterExt

@[expose] public section

/-!
# ZC19, discrete part: `γ_p^ext` as a class-count formula

For `ExtHyp p n` (`p ≥ 101` prime, `K/3 < p ≤ K`, `K = 40 n`) the exponent
`γ_p^ext = 2 ∑ w` of `zc18_ext` is
`Z₀ + ∑_{a=1}^{m} L_a (L_a + 6 ℓ_N(a) - ℓ_K(a) - 5)` with `Z₀` the zero-class part (`O(1)`).
-/

open Finset

namespace CatalanCore.Zeta5.CostOut

open Apery

/-- Pointwise: `(T + ε - 3δ)(T + ε + 3δ - ℓ - 5)` with `ℓ = 2q + lo + h`, `ε, δ, h ∈ {0,1}`. -/
lemma ord_term (T q lo ε δ h : ℚ) (hε : ε = 0 ∨ ε = 1) (hδ : δ = 0 ∨ δ = 1) (hh : h = 0 ∨ h = 1) :
    (T + ε - 3 * δ) * (T + ε + 3 * δ - (2 * q + lo + h) - 5)
      = T * (T - 2 * q - lo - 5)
        + δ * ((T - 3) * (T + 3 - 2 * q - lo - 5) - T * (T - 2 * q - lo - 5))
        + h * (T * (T - 2 * q - lo - 6) - T * (T - 2 * q - lo - 5))
        + δ * h * ((T - 3) * (T + 3 - 2 * q - lo - 6) - (T - 3) * (T + 3 - 2 * q - lo - 5)
          - T * (T - 2 * q - lo - 6) + T * (T - 2 * q - lo - 5))
        + ε * (2 * T - 2 * q - lo - 4) - ε * h := by
  rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl <;> rcases hh with rfl | rfl <;> ring

/-- The ordinary-class sum. -/
lemma ord_sum {m : ℕ} (T q lo : ℚ) (ε δ h : Fin m → ℚ) (hε : ∀ i, ε i = 0 ∨ ε i = 1)
    (hδ : ∀ i, δ i = 0 ∨ δ i = 1) (hh : ∀ i, h i = 0 ∨ h i = 1) :
    ∑ i, (T + ε i - 3 * δ i) * (T + ε i + 3 * δ i - (2 * q + lo + h i) - 5)
      = m * (T * (T - 2 * q - lo - 5))
        + (∑ i, δ i) * ((T - 3) * (T + 3 - 2 * q - lo - 5) - T * (T - 2 * q - lo - 5))
        + (∑ i, h i) * (T * (T - 2 * q - lo - 6) - T * (T - 2 * q - lo - 5))
        + (∑ i, δ i * h i) * ((T - 3) * (T + 3 - 2 * q - lo - 6) - (T - 3) * (T + 3 - 2 * q - lo - 5)
          - T * (T - 2 * q - lo - 6) + T * (T - 2 * q - lo - 5))
        + (∑ i, ε i) * (2 * T - 2 * q - lo - 4) - ∑ i, ε i * h i := by
  rw [Finset.sum_congr rfl fun i _ => ord_term T q lo (ε i) (δ i) (h i) (hε i) (hδ i) (hh i)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring


/-- Counting an interval of ordinary classes `a = j + 1`, `lo ≤ a ≤ hi`, among `1 ≤ a ≤ m`. -/
lemma cnt_interval (m lo hi : ℕ) (hlo : 1 ≤ lo) :
    ∑ i : Fin m, (if lo ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ hi then (1 : ℚ) else 0)
      = ((min hi m + 1 - lo : ℕ) : ℚ) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if lo ≤ j + 1 ∧ j + 1 ≤ hi then (1 : ℚ) else 0) m,
    Finset.sum_boole]
  have : (range m).filter (fun j => lo ≤ j + 1 ∧ j + 1 ≤ hi) = Ico (lo - 1) (min hi m) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Nat.card_Ico]
  congr 1
  omega

/-- Abstract top-count: if the extras go to `h`-classes first, `∑ ε h = min (∑ ε) (∑ h)`. -/
lemma top_count {m : ℕ} (ε h : Fin m → ℕ) (hε : ∀ i, ε i = 0 ∨ ε i = 1)
    (hh : ∀ i, h i = 0 ∨ h i = 1)
    (htop : ∀ i k, ε i = 1 → ε k = 0 → h k = 1 → h i = 1) :
    ∑ i, ε i * h i = min (∑ i, ε i) (∑ i, h i) := by
  have hle1 : ∑ i, ε i * h i ≤ ∑ i, ε i := Finset.sum_le_sum fun i _ => by
    rcases hh i with h0 | h0 <;> simp [h0]
  have hle2 : ∑ i, ε i * h i ≤ ∑ i, h i := Finset.sum_le_sum fun i _ => by
    rcases hε i with h0 | h0 <;> simp [h0]
  by_cases hall : ∀ k, h k = 1 → ε k = 1
  · have : ∑ i, ε i * h i = ∑ i, h i := Finset.sum_congr rfl fun i _ => by
      rcases hh i with h0 | h0
      · simp [h0]
      · simp [h0, hall i h0]
    omega
  · push Not at hall
    obtain ⟨k, hk1, hk0⟩ := hall
    have hk0' : ε k = 0 := by rcases hε k with h0 | h0 <;> omega
    have : ∑ i, ε i * h i = ∑ i, ε i := Finset.sum_congr rfl fun i _ => by
      rcases hε i with h0 | h0
      · simp [h0]
      · simp [h0, htop i k h0 hk0' hk1]
    omega


lemma ind_mul (A B : Prop) [Decidable A] [Decidable B] :
    (if A then (1 : ℚ) else 0) * (if B then (1 : ℚ) else 0) = if A ∧ B then (1 : ℚ) else 0 := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

lemma cnt_le (m N : ℕ) :
    ∑ i : Fin m, (if (i : ℕ) + 1 ≤ N then (1 : ℚ) else 0) = ((min N m : ℕ) : ℚ) := by
  have := cnt_interval m 1 N le_rfl
  simp only [true_and, show ∀ i : ℕ, 1 ≤ i + 1 from fun i => by omega] at this
  rw [this]
  simp

lemma cnt_ge (m lo : ℕ) (hlo : 1 ≤ lo) :
    ∑ i : Fin m, (if lo ≤ (i : ℕ) + 1 then (1 : ℚ) else 0) = ((m + 1 - lo : ℕ) : ℚ) := by
  have := cnt_interval m lo m hlo
  have e : ∀ i : Fin m, (lo ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ m) ↔ lo ≤ (i : ℕ) + 1 :=
    fun i => ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩
  simp only [e] at this
  rw [this]; congr 1; omega

/-- `ε_i` (an extra row at the ordinary class `i + 1`). -/
noncomputable def epsN (p n : ℕ) (i : Fin (p / 2)) : ℕ := by
  classical exact if i.succ ∈ extEps p n then 1 else 0

lemma epsN_01 (p n : ℕ) (i : Fin (p / 2)) : epsN p n i = 0 ∨ epsN p n i = 1 := by
  unfold epsN; split_ifs <;> simp

namespace ExtHyp
variable {p n : ℕ} (H : ExtHyp p n)
include H

lemma sum_epsN : ∑ i : Fin (p / 2), epsN p n i = extE p n := by
  obtain ⟨hsub, hcard, hprop⟩ := H.eps_spec
  classical
  have h0 : (0 : Fin (p / 2 + 1)) ∉ extEps p n := fun h0 =>
    (Finset.mem_erase.mp (hsub h0)).1 rfl
  have h1 : ∑ a : Fin (p / 2 + 1), (if a ∈ extEps p n then 1 else 0) = extE p n := by
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
    simpa using hcard
  rw [Fin.sum_univ_succ, if_neg h0, zero_add] at h1
  unfold epsN
  convert h1 using 2

end ExtHyp

/-- `δ_i = [i + 1 ≤ N]`. -/
def dN (n : ℕ) {m : ℕ} (i : Fin m) : ℕ := if (i : ℕ) + 1 ≤ 3 * n then 1 else 0

/-- `lo = 0` if `v ≤ m`, else `1`. -/
def loN (p n : ℕ) : ℕ := if 40 * n % p ≤ p / 2 then 0 else 1

/-- `h_i`: the classes with the larger `ℓ_K`. -/
def hN (p n : ℕ) (i : Fin (p / 2)) : ℕ :=
  if 40 * n % p ≤ p / 2 then (if (i : ℕ) + 1 ≤ 40 * n % p then 1 else 0)
  else (if p - 40 * n % p ≤ (i : ℕ) + 1 then 1 else 0)

lemma dN_01 (n : ℕ) {m : ℕ} (i : Fin m) : dN n i = 0 ∨ dN n i = 1 := by
  unfold dN; split_ifs <;> simp

lemma hN_01 (p n : ℕ) (i : Fin (p / 2)) : hN p n i = 0 ∨ hN p n i = 1 := by
  unfold hN; split_ifs <;> simp

namespace ExtHyp
variable {p n : ℕ} (H : ExtHyp p n)
include H

lemma lK_ord (i : Fin (p / 2)) :
    lK p n ((i : ℕ) + 1) = 2 * (40 * n / p) + loN p n + hN p n i := by
  have h1 : 1 ≤ (i : ℕ) + 1 := by omega
  have h2 : (i : ℕ) + 1 ≤ p / 2 := by have := i.isLt; omega
  rw [H.lK_eq h1 h2]
  have hp := H.p_odd
  have hv := Nat.mod_lt (40 * n) (show 0 < p by have := H.h101; omega)
  unfold aCnt loN hN
  split_ifs <;> omega

lemma lN_ord (i : Fin (p / 2)) : lN p n ((i : ℕ) + 1) = dN n i := by
  have h1 : 1 ≤ (i : ℕ) + 1 := by omega
  have h2 : (i : ℕ) + 1 ≤ p / 2 := by have := i.isLt; omega
  rw [H.lN_eq h1 h2]
  unfold dN; rfl

lemma extL_cast (i : Fin (p / 2)) :
    ((extL p n i.succ : ℕ) : ℚ) = (extT p n : ℚ) + (epsN p n i : ℚ) - 3 * (dN n i : ℚ) := by
  have h := H.extL_spec i.succ (Fin.succ_ne_zero i)
  rw [show ((i.succ : Fin (p / 2 + 1)) : ℕ) = (i : ℕ) + 1 from Fin.val_succ i, lN_ord H i] at h
  have h' : extL p n i.succ + 3 * dN n i = extT p n + epsN p n i := by
    rw [h]; unfold epsN; split_ifs <;> rfl
  have h'' : ((extL p n i.succ : ℕ) : ℚ) + 3 * (dN n i : ℚ) = (extT p n : ℚ) + (epsN p n i : ℚ) := by
    exact_mod_cast h'
  linarith

lemma htop (i k : Fin (p / 2)) (hi : epsN p n i = 1) (hk : epsN p n k = 0) (hhk : hN p n k = 1) :
    hN p n i = 1 := by
  obtain ⟨hsub, hcard, hprop⟩ := H.eps_spec
  have hi' : i.succ ∈ extEps p n := by
    unfold epsN at hi; split_ifs at hi with h; exact h
  have hk' : k.succ ∉ extEps p n := by
    unfold epsN at hk; split_ifs at hk with h; exact h
  have key := hprop i.succ hi' k.succ (Finset.mem_erase.mpr ⟨Fin.succ_ne_zero k, Finset.mem_univ _⟩) hk'
  unfold extKey at key
  rw [show ((i.succ : Fin (p / 2 + 1)) : ℕ) = (i : ℕ) + 1 from Fin.val_succ i,
    show ((k.succ : Fin (p / 2 + 1)) : ℕ) = (k : ℕ) + 1 from Fin.val_succ k,
    lK_ord H i, lK_ord H k] at key
  have h3 := dN_01 n i
  have h4 := dN_01 n k
  have h5 := hN_01 p n i
  have : dN n i ≤ 1 := by omega
  unfold dN at *
  split_ifs at key <;> omega

lemma sum_dN : ∑ i : Fin (p / 2), (dN n i : ℚ) = ((min (3 * n) (p / 2) : ℕ) : ℚ) := by
  rw [← cnt_le (p / 2) (3 * n)]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold dN; split_ifs <;> simp

/-- The number of `h`-classes. -/
def nHn (p n : ℕ) : ℕ :=
  if 40 * n % p ≤ p / 2 then min (40 * n % p) (p / 2) else p / 2 + 1 - (p - 40 * n % p)

/-- The number of removed `h`-classes. -/
def nNHn (p n : ℕ) : ℕ :=
  if 40 * n % p ≤ p / 2 then min (min (3 * n) (40 * n % p)) (p / 2)
  else min (3 * n) (p / 2) + 1 - (p - 40 * n % p)

lemma sum_hN : ∑ i : Fin (p / 2), (hN p n i : ℚ) = (nHn p n : ℚ) := by
  have hv := Nat.mod_lt (40 * n) (show 0 < p by have := H.h101; omega)
  unfold nHn
  by_cases hA : 40 * n % p ≤ p / 2
  · rw [if_pos hA, ← cnt_le (p / 2) (40 * n % p)]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold hN; rw [if_pos hA]; split_ifs <;> simp
  · rw [if_neg hA, ← cnt_ge (p / 2) (p - 40 * n % p) (by omega)]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold hN; rw [if_neg hA]; split_ifs <;> simp

lemma sum_dh : ∑ i : Fin (p / 2), (dN n i : ℚ) * (hN p n i : ℚ) = (nNHn p n : ℚ) := by
  have hv := Nat.mod_lt (40 * n) (show 0 < p by have := H.h101; omega)
  unfold nNHn
  by_cases hA : 40 * n % p ≤ p / 2
  · rw [if_pos hA, ← cnt_le (p / 2) (min (3 * n) (40 * n % p))]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold hN dN; rw [if_pos hA]
    by_cases h1 : (i : ℕ) + 1 ≤ 3 * n <;> by_cases h2 : (i : ℕ) + 1 ≤ 40 * n % p <;>
      simp [h1, h2, le_min_iff]
  · rw [if_neg hA, ← cnt_interval (p / 2) (p - 40 * n % p) (3 * n) (by omega)]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold hN dN; rw [if_neg hA]
    by_cases h1 : (i : ℕ) + 1 ≤ 3 * n <;> by_cases h2 : p - 40 * n % p ≤ (i : ℕ) + 1 <;>
      simp [h1, h2]

lemma sum_eps_h : ∑ i : Fin (p / 2), (epsN p n i : ℚ) * (hN p n i : ℚ)
    = ((min (extE p n) (nHn p n) : ℕ) : ℚ) := by
  have := top_count (epsN p n) (hN p n) (epsN_01 p n) (hN_01 p n) (fun i k => htop H i k)
  have h1 : ∑ i : Fin (p / 2), hN p n i = nHn p n := by
    exact_mod_cast (sum_hN H)
  rw [sum_epsN H, h1] at this
  exact_mod_cast this

/-- **The ordinary-class sum in closed form.** -/
theorem ord_class_sum :
    ∑ i : Fin (p / 2), ((extL p n i.succ : ℕ) : ℚ) *
        (((extL p n i.succ : ℕ) : ℚ) + 6 * (lN p n ((i : ℕ) + 1) : ℚ) - (lK p n ((i : ℕ) + 1) : ℚ) - 5)
      = ((p / 2 : ℕ) : ℚ) * ((extT p n : ℚ) * ((extT p n : ℚ) - 2 * ((40 * n / p : ℕ) : ℚ)
            - (loN p n : ℚ) - 5))
        + ((min (3 * n) (p / 2) : ℕ) : ℚ) *
          (((extT p n : ℚ) - 3) * ((extT p n : ℚ) + 3 - 2 * ((40 * n / p : ℕ) : ℚ) - (loN p n : ℚ) - 5)
            - (extT p n : ℚ) * ((extT p n : ℚ) - 2 * ((40 * n / p : ℕ) : ℚ) - (loN p n : ℚ) - 5))
        + (nHn p n : ℚ) *
          ((extT p n : ℚ) * ((extT p n : ℚ) - 2 * ((40 * n / p : ℕ) : ℚ) - (loN p n : ℚ) - 6)
            - (extT p n : ℚ) * ((extT p n : ℚ) - 2 * ((40 * n / p : ℕ) : ℚ) - (loN p n : ℚ) - 5))
        + (nNHn p n : ℚ) *
          (((extT p n : ℚ) - 3) * ((extT p n : ℚ) + 3 - 2 * ((40 * n / p : ℕ) : ℚ) - (loN p n : ℚ) - 6)
            - ((extT p n : ℚ) - 3) * ((extT p n : ℚ) + 3 - 2 * ((40 * n / p : ℕ) : ℚ) - (loN p n : ℚ) - 5)
            - (extT p n : ℚ) * ((extT p n : ℚ) - 2 * ((40 * n / p : ℕ) : ℚ) - (loN p n : ℚ) - 6)
            + (extT p n : ℚ) * ((extT p n : ℚ) - 2 * ((40 * n / p : ℕ) : ℚ) - (loN p n : ℚ) - 5))
        + (extE p n : ℚ) * (2 * (extT p n : ℚ) - 2 * ((40 * n / p : ℕ) : ℚ) - (loN p n : ℚ) - 4)
        - ((min (extE p n) (nHn p n) : ℕ) : ℚ) := by
  have key : ∀ i : Fin (p / 2),
      ((extL p n i.succ : ℕ) : ℚ) *
        (((extL p n i.succ : ℕ) : ℚ) + 6 * (lN p n ((i : ℕ) + 1) : ℚ) - (lK p n ((i : ℕ) + 1) : ℚ) - 5)
      = ((extT p n : ℚ) + (epsN p n i : ℚ) - 3 * (dN n i : ℚ)) *
        ((extT p n : ℚ) + (epsN p n i : ℚ) + 3 * (dN n i : ℚ) -
          (2 * ((40 * n / p : ℕ) : ℚ) + (loN p n : ℚ) + (hN p n i : ℚ)) - 5) := by
    intro i
    rw [extL_cast H i, lN_ord H i, lK_ord H i]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun i _ => key i]
  rw [ord_sum (extT p n : ℚ) ((40 * n / p : ℕ) : ℚ) (loN p n : ℚ) (fun i => (epsN p n i : ℚ))
    (fun i => (dN n i : ℚ)) (fun i => (hN p n i : ℚ))
    (fun i => by rcases epsN_01 p n i with h | h <;> simp [h])
    (fun i => by rcases dN_01 n i with h | h <;> simp [h])
    (fun i => by rcases hN_01 p n i with h | h <;> simp [h])]
  rw [sum_dN H, sum_hN H, sum_dh H, sum_eps_h H]
  have hE : ∑ i : Fin (p / 2), (epsN p n i : ℚ) = (extE p n : ℚ) := by
    exact_mod_cast sum_epsN H
  rw [hE]

lemma sum_fin_cast (L : ℕ) : ∑ j : Fin L, ((j : ℕ) : ℚ) = (L : ℚ) * ((L : ℚ) - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => (j : ℚ)) L]
  have := Finset.sum_range_id_mul_two L
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h; simp
  · have h2 : ((∑ i ∈ range L, i : ℕ) : ℚ) * 2 = (L : ℚ) * ((L - 1 : ℕ) : ℚ) := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at h2
    push_cast at h2 ⊢
    linarith

lemma Bse_ord (i : Fin (p / 2)) :
    Bse p (40 * n) (3 * n) ((i.succ : Fin (p / 2 + 1)) : ℕ)
      = 6 * (lN p n ((i : ℕ) + 1) : ℚ) - (lK p n ((i : ℕ) + 1) : ℚ) := by
  unfold Bse lN lK
  rw [show ((i.succ : Fin (p / 2 + 1)) : ℕ) = (i : ℕ) + 1 from Fin.val_succ i]
  simp

lemma class_weight (i : Fin (p / 2)) :
    2 * ∑ j : Fin (extL p n i.succ), winner H.m_pos (extL p n) (Bse p (40 * n) (3 * n)) ⟨i.succ, j⟩
      = ((extL p n i.succ : ℕ) : ℚ) * (((extL p n i.succ : ℕ) : ℚ) + 6 * (lN p n ((i : ℕ) + 1) : ℚ)
        - (lK p n ((i : ℕ) + 1) : ℚ) - 5) := by
  have hw : ∀ j : Fin (extL p n i.succ),
      winner H.m_pos (extL p n) (Bse p (40 * n) (3 * n)) ⟨i.succ, j⟩
        = ((j : ℕ) : ℚ) + (6 * (lN p n ((i : ℕ) + 1) : ℚ) - (lK p n ((i : ℕ) + 1) : ℚ) - 4) / 2 := by
    intro j
    unfold winner
    rw [if_neg (Fin.succ_ne_zero i), Bse_ord H i]
  rw [Finset.sum_congr rfl fun j _ => hw j, Finset.sum_add_distrib, sum_fin_cast H]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The zero-class part of `γ_p^ext`. -/
noncomputable def zeroPart : ℚ :=
  2 * ∑ j : Fin (extL p n 0), winner H.m_pos (extL p n) (Bse p (40 * n) (3 * n)) ⟨0, j⟩

theorem gammaExt_split :
    2 * ∑ s : (Σ a : Fin (p / 2 + 1), Fin (extL p n a)),
        winner H.m_pos (extL p n) (Bse p (40 * n) (3 * n)) s
      = zeroPart H + ∑ i : Fin (p / 2), ((extL p n i.succ : ℕ) : ℚ) *
        (((extL p n i.succ : ℕ) : ℚ) + 6 * (lN p n ((i : ℕ) + 1) : ℚ)
          - (lK p n ((i : ℕ) + 1) : ℚ) - 5) := by
  rw [Fintype.sum_sigma, Fin.sum_univ_succ, mul_add]
  unfold zeroPart
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => class_weight H i

lemma q_bounds : 1 ≤ 40 * n / p ∧ 40 * n / p ≤ 2 := by
  have hp0 : 0 < p := by have := H.h101; omega
  constructor
  · exact (Nat.le_div_iff_mul_le hp0).mpr (by have := H.hpK; omega)
  · have : 40 * n / p < 3 := (Nat.div_lt_iff_lt_mul hp0).mpr (by have := H.hout; omega)
    omega

lemma lK_bounds (a : Fin (p / 2 + 1)) (ha : a ≠ 0) :
    2 ≤ lK p n a ∧ lK p n a ≤ 6 := by
  have h1 : 1 ≤ (a : ℕ) := Nat.one_le_iff_ne_zero.mpr (fun h => ha (Fin.ext h))
  have h2 : (a : ℕ) ≤ p / 2 := Nat.lt_succ_iff.mp a.isLt
  rw [H.lK_eq h1 h2]
  have := q_bounds H
  unfold aCnt
  split_ifs <;> omega

lemma topw_bounds (a : Fin (p / 2 + 1)) (ha : a ≠ 0) :
    -3 ≤ topw (extL p n) (Bse p (40 * n) (3 * n)) a ∧
      topw (extL p n) (Bse p (40 * n) (3 * n)) a ≤ 4 + 3 := by
  rw [H.topw_eq a ha]
  have hT1 := H.T_ge2
  have hT2 := H.T_le6
  have := lK_bounds H a ha
  have hT1' : (2 : ℚ) ≤ extT p n := by exact_mod_cast hT1
  have hT2' : (extT p n : ℚ) ≤ 6 := by exact_mod_cast hT2
  have hl1 : (2 : ℚ) ≤ lK p n a := by exact_mod_cast this.1
  have hl2 : (lK p n a : ℚ) ≤ 6 := by exact_mod_cast this.2
  have hε0 : (0 : ℚ) ≤ (if a ∈ extEps p n then 1 else 0) := by split_ifs <;> norm_num
  have hε1 : (if a ∈ extEps p n then (1 : ℚ) else 0) ≤ 1 := by split_ifs <;> norm_num
  constructor <;> linarith

lemma tmin_bounds :
    -3 ≤ tmin H.m_pos (extL p n) (Bse p (40 * n) (3 * n)) ∧
      tmin H.m_pos (extL p n) (Bse p (40 * n) (3 * n)) ≤ 4 := by
  constructor
  · unfold tmin
    refine Finset.le_inf' _ _ fun a ha => ?_
    exact (topw_bounds H a (Finset.mem_erase.mp ha).1).1
  · have hm := H.m_pos
    have h1 : (⟨1, by omega⟩ : Fin (p / 2 + 1)) ≠ 0 := by
      intro h
      have h' := congrArg Fin.val h
      simp at h'
    refine (tmin_le H.m_pos (extL p n) (Bse p (40 * n) (3 * n)) h1).trans ?_
    rw [H.topw_eq _ h1]
    have hT2 := H.T_le6
    have := lK_bounds H _ h1
    have hT2' : (extT p n : ℚ) ≤ 6 := by exact_mod_cast hT2
    have hl1 : (2 : ℚ) ≤ lK p n ((⟨1, by omega⟩ : Fin (p / 2 + 1)) : ℕ) := by exact_mod_cast this.1
    have hε1 : (if (⟨1, by omega⟩ : Fin (p / 2 + 1)) ∈ extEps p n then (1 : ℚ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    linarith

lemma zero_weight_bound (j : Fin (extL p n 0)) :
    |winner H.m_pos (extL p n) (Bse p (40 * n) (3 * n)) ⟨0, j⟩| ≤ 4 := by
  have hq := q_bounds H
  have hp0 : 0 < p := by have := H.h101; omega
  haveI : Fact p.Prime := ⟨H.prime⟩
  have hb : Bse p (40 * n) (3 * n) 0 = 5 - 2 * ((40 * n / p : ℕ) : ℚ) := by
    unfold Bse
    have h3 : 3 * n / p = 0 := Nat.div_eq_of_lt (by have := H.hout; omega)
    simp only [ite_true, Nat.cast_zero, Int.cast_zero, SX_zero, h3]
    push_cast; ring
  unfold winner
  simp only [ite_true]
  rw [hb]
  have hq' : ((40 * n / p : ℕ) : ℚ) ≤ 2 := by exact_mod_cast hq.2
  have hj : (0 : ℚ) ≤ ((j : ℕ) : ℚ) := Nat.cast_nonneg _
  have ht := tmin_bounds H
  rw [abs_le]
  constructor
  · refine le_min ?_ ?_ <;> linarith [ht.1]
  · exact (min_le_right _ _).trans ht.2

lemma zeroPart_bound : |zeroPart H| ≤ 64 := by
  unfold zeroPart
  have hL : extL p n 0 = 8 := H.extL_zero
  have hs : |∑ j : Fin (extL p n 0),
      winner H.m_pos (extL p n) (Bse p (40 * n) (3 * n)) ⟨0, j⟩| ≤ 32 := by
    calc _ ≤ ∑ j : Fin (extL p n 0), |winner H.m_pos (extL p n) (Bse p (40 * n) (3 * n)) ⟨0, j⟩| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin (extL p n 0), (4 : ℚ) := Finset.sum_le_sum fun j _ => zero_weight_bound H j
      _ = 32 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hL]
          norm_num
  rw [abs_mul]
  norm_num
  linarith

end ExtHyp

end CatalanCore.Zeta5.CostOut
