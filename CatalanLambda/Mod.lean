import CatalanLambda.Cauchy
import CatalanLambda.Local
import CatalanLambda.Defs

open Finset Matrix

namespace CatalanLambda

section Mod
variable {ℓ : ℕ} [Fact ℓ.Prime] {K : ℕ}

/-- `4 K = ℓ + 1` gives `4 K = 1` mod `ℓ`. -/
lemma four_K (hlK : ℓ + 1 = 4 * K) : 4 * (K : ZMod ℓ) = 1 := by
  have : ((ℓ + 1 : ℕ) : ZMod ℓ) = ((4 * K : ℕ) : ZMod ℓ) := by rw [hlK]
  simpa using this.symm

lemma four_ne (hlK : ℓ + 1 = 4 * K) : (4 : ZMod ℓ) ≠ 0 := by
  intro h
  have := four_K (ℓ := ℓ) hlK
  rw [h, zero_mul] at this
  exact zero_ne_one this

lemma N_cast (hKl : K ≤ ℓ) : ((ℓ - K : ℕ) : ZMod ℓ) = -(K : ZMod ℓ) := by
  have : ((ℓ - K + K : ℕ) : ZMod ℓ) = 0 := by
    rw [Nat.sub_add_cancel hKl]; simp
  push_cast at this
  linear_combination this

/-- Nonvanishing of `k` and `4k-1` for `1 ≤ k < ℓ`, `k ≠ K`. -/
lemma k_ne (hlK : ℓ + 1 = 4 * K) {k : ℕ} (hk0 : 0 < k) (hkl : k < ℓ) (hkK : k ≠ K) :
    (k : ZMod ℓ) ≠ 0 ∧ (4 * (k : ZMod ℓ) - 1) ≠ 0 := by
  refine ⟨natCast_ne_zero' hk0 hkl, ?_⟩
  have hK : K < ℓ := by omega
  have h1 : 4 * (k : ZMod ℓ) - 1 = 4 * ((k : ZMod ℓ) - K) := by
    linear_combination (four_K hlK)
  rw [h1]
  refine mul_ne_zero (four_ne hlK) ?_
  intro h
  exact natCast_ne_natCast hkl hK hkK (sub_eq_zero.1 h)

/-- harmonic-type sum `U n = ∑_{j=1}^{ℓ-K} 1/(n+j)`. -/
noncomputable def U (ℓ K n : ℕ) [Fact ℓ.Prime] : ZMod ℓ :=
  ∑ t ∈ range (ℓ - K), 1 / (((n : ℕ) : ZMod ℓ) + 1 + (t : ℕ))

noncomputable def G (ℓ K a b : ℕ) [Fact ℓ.Prime] : ZMod ℓ :=
  ∑ t ∈ range (ℓ - K), 1 / ((((a : ℕ) : ZMod ℓ) + 1 + (t : ℕ)) * (((b : ℕ) : ZMod ℓ) + 1 + (t : ℕ)))

lemma U_tel (n : ℕ) :
    U ℓ K n - U ℓ K (n + 1) =
      1 / ((n : ZMod ℓ) + 1) - 1 / ((n : ZMod ℓ) + 1 + ((ℓ - K : ℕ) : ZMod ℓ)) := by
  have h := Finset.sum_range_sub' (fun t : ℕ => (1 : ZMod ℓ) / ((n : ZMod ℓ) + 1 + t)) (ℓ - K)
  simp only [U]
  rw [← Finset.sum_sub_distrib]
  have e : ∀ t ∈ range (ℓ - K), 1 / ((n : ZMod ℓ) + 1 + (t : ℕ)) - 1 / ((((n + 1 : ℕ)) : ZMod ℓ) + 1 + (t : ℕ)) =
      1 / ((n : ZMod ℓ) + 1 + (t : ℕ)) - 1 / ((n : ZMod ℓ) + 1 + ((t + 1 : ℕ) : ZMod ℓ)) := by
    intro t _; push_cast; ring_nf
  rw [Finset.sum_congr rfl e, h]; simp

lemma G_tel (n : ℕ) :
    G ℓ K n n - G ℓ K (n + 1) (n + 1) =
      1 / ((n : ZMod ℓ) + 1) ^ 2 - 1 / ((n : ZMod ℓ) + 1 + ((ℓ - K : ℕ) : ZMod ℓ)) ^ 2 := by
  have h := Finset.sum_range_sub' (fun t : ℕ => (1 : ZMod ℓ) / ((n : ZMod ℓ) + 1 + t) ^ 2) (ℓ - K)
  simp only [G]
  rw [← Finset.sum_sub_distrib]
  have e : ∀ t ∈ range (ℓ - K), 1 / ((((n : ℕ) : ZMod ℓ) + 1 + (t : ℕ)) * (((n : ℕ) : ZMod ℓ) + 1 + (t : ℕ))) -
      1 / ((((n + 1 : ℕ) : ZMod ℓ) + 1 + (t : ℕ)) * (((n + 1 : ℕ) : ZMod ℓ) + 1 + (t : ℕ))) =
      1 / ((n : ZMod ℓ) + 1 + (t : ℕ)) ^ 2 - 1 / ((n : ZMod ℓ) + 1 + ((t + 1 : ℕ) : ZMod ℓ)) ^ 2 := by
    intro t _; push_cast; ring_nf
  rw [Finset.sum_congr rfl e, h]; simp

lemma K_eq (hlK : ℓ + 1 = 4 * K) : (K : ZMod ℓ) = 1 / 4 := by
  have h4 := four_ne (ℓ := ℓ) hlK
  field_simp
  linear_combination four_K hlK

lemma term_aux {F : Type*} [Field F] (x : F) (h4 : (4 : F) ≠ 0) (hx : x ≠ 0)
    (hy : 4 * x - 1 ≠ 0) :
    1 / (4 * x * (4 * x - 1)) = (1 / 4) * (-(1 / x - 1 / (x + -(1 / 4)))) := by
  have e : x + -(1 / 4) = (4 * x - 1) / 4 := by field_simp; ring
  rw [e]
  field_simp
  ring

lemma term_id (hlK : ℓ + 1 = 4 * K) {n : ℕ} (hn : n + 1 < K) :
    (1 : ZMod ℓ) / (4 * ((n + 1 : ℕ) : ZMod ℓ) * (4 * ((n + 1 : ℕ) : ZMod ℓ) - 1)) =
      (1 / 4) * (U ℓ K (n + 1) - U ℓ K n) := by
  have hKl : K ≤ ℓ := by omega
  have hk := k_ne hlK (k := n + 1) (by omega) (by omega) (by omega)
  have hU := U_tel (ℓ := ℓ) (K := K) n
  rw [N_cast hKl] at hU
  have h4 := four_ne (ℓ := ℓ) hlK
  have hKe := K_eq hlK
  push_cast at hk ⊢
  obtain ⟨hx, hy⟩ := hk
  have hz : (n : ZMod ℓ) + 1 - K ≠ 0 := by
    intro h
    apply hy
    rw [hKe] at h
    have h14 : (4 : ZMod ℓ) * (1 / 4) = 1 := by field_simp
    linear_combination 4 * h + h14
  have : U ℓ K (n + 1) - U ℓ K n = -(1 / ((n : ZMod ℓ) + 1) - 1 / ((n : ZMod ℓ) + 1 + -(K : ZMod ℓ))) := by
    rw [← hU]; ring
  rw [this]
  rw [hKe] at hz ⊢
  exact term_aux _ h4 hx hy

lemma sumT (hlK : ℓ + 1 = 4 * K) {a b : ℕ} (hab : a ≤ b) (hb : b < K) :
    ∑ k ∈ Ioc a b, (1 : ZMod ℓ) / (4 * (k : ZMod ℓ) * (4 * (k : ZMod ℓ) - 1)) =
      (1 / 4) * (U ℓ K b - U ℓ K a) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ih (by omega), term_id hlK hb]
    ring

lemma G_off (hlK : ℓ + 1 = 4 * K) {a b : ℕ} (ha : a < K) (hb : b < K) :
    ((b : ZMod ℓ) - a) * G ℓ K a b = U ℓ K a - U ℓ K b := by
  have hne : ∀ c t : ℕ, c < K → t < ℓ - K → ((c : ZMod ℓ) + 1 + (t : ℕ)) ≠ 0 := by
    intro c t hc ht
    have := natCast_ne_zero' (p := ℓ) (a := c + 1 + t) (by omega) (by omega)
    simpa using this
  simp only [G, U]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.1 ht
  have h1 := hne a t ha ht'
  have h2 := hne b t hb ht'
  field_simp
  ring

lemma diag_aux {F : Type*} [Field F] (x : F) (h4 : (4 : F) ≠ 0) (hx : x ≠ 0)
    (hy : 4 * x - 1 ≠ 0) :
    1 / (16 * x ^ 2) - 1 / (4 * x - 1) ^ 2 = (1 / 16) * (1 / x ^ 2 - 1 / (x + -(1 / 4)) ^ 2) := by
  have e : x + -(1 / 4) = (4 * x - 1) / 4 := by field_simp; ring
  rw [e, div_pow, one_div_div]
  have hy2 : (4 * x - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hy
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have h16 : (16 : F) ≠ 0 := by
    have : (16 : F) = 4 * 4 := by norm_num
    rw [this]; exact mul_ne_zero h4 h4
  field_simp
  ring

/-- the diagonal constant `c` -/
noncomputable def cc (ℓ K : ℕ) [Fact ℓ.Prime] : ZMod ℓ := -(G ℓ K 0 0)

lemma diag_eq (hlK : ℓ + 1 = 4 * K) {a : ℕ} (ha : a < K) :
    -(∑ k ∈ Icc 1 a, (1 / (16 * (k : ZMod ℓ) ^ 2) - 1 / (4 * (k : ZMod ℓ) - 1) ^ 2)) =
      (cc ℓ K + G ℓ K a a) / 16 := by
  induction a with
  | zero => simp [cc]
  | succ n ih =>
    have hKl : K ≤ ℓ := by omega
    rw [Finset.sum_Icc_succ_top (by omega), neg_add, ih (by omega)]
    have hk := k_ne hlK (k := n + 1) (by omega) (by omega) (by omega)
    have hT := G_tel (ℓ := ℓ) (K := K) n
    rw [N_cast hKl] at hT
    have h4 := four_ne (ℓ := ℓ) hlK
    have hKe := K_eq hlK
    push_cast at hk ⊢
    obtain ⟨hx, hy⟩ := hk
    rw [diag_aux _ h4 hx hy]
    have : G ℓ K (n + 1) (n + 1) = G ℓ K n n - (1 / ((n : ZMod ℓ) + 1) ^ 2 -
        1 / ((n : ZMod ℓ) + 1 + -(K : ZMod ℓ)) ^ 2) := by rw [← hT]; ring
    rw [this, hKe]
    ring

end Mod
end CatalanLambda
