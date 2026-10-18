module

public import CatalanLambda.Assembly

@[expose] public section

/-!
# Mirror constant `λ' = G/2 + 5π²/96`: nonvanishing, part 1 (definitions, mod-ℓ identities, entries)

`ℓ ≡ 1 (mod 4)`, `K = (ℓ+3)/4` (so `4K - 3 = ℓ`).
-/

open Finset Matrix

namespace CatalanLambda.Mirror

/-- Entries of the mirror matrix `N₀`, indexed by naturals. -/
noncomputable def N0n (a b : ℕ) : ℚ :=
  if a = b then ∑ k ∈ Icc 1 a, (1 / (16 * (k : ℚ) ^ 2) - 1 / (4 * (k : ℚ) - 3) ^ 2)
  else (3 / (16 * (((max a b : ℕ) : ℚ) - ((min a b : ℕ) : ℚ)))) *
    ∑ k ∈ Ioc (min a b) (max a b), 1 / ((k : ℚ) * (4 * (k : ℚ) - 3))

/-- The `h × h` rational matrix `N₀`. -/
noncomputable def N0 (h : ℕ) : Matrix (Fin h) (Fin h) ℚ := Matrix.of fun a b => N0n a b

/-- `P̄_h(r) = det (r I + N₀)`. -/
noncomputable def Pbar (h : ℕ) (r : ℚ) : ℚ := (r • (1 : Matrix (Fin h) (Fin h) ℚ) + N0 h).det

section Mod
variable {ℓ : ℕ} [Fact ℓ.Prime] {K : ℕ}

lemma four_K (hlK : ℓ + 3 = 4 * K) : 4 * (K : ZMod ℓ) = 3 := by
  have : ((ℓ + 3 : ℕ) : ZMod ℓ) = ((4 * K : ℕ) : ZMod ℓ) := by rw [hlK]
  simpa using this.symm

lemma three_ne (hlK : ℓ + 3 = 4 * K) : (3 : ZMod ℓ) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : ZMod ℓ) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  have h1 := Nat.le_of_dvd (by norm_num) h'
  have hp := (Fact.out : ℓ.Prime).two_le
  have : ℓ = 2 ∨ ℓ = 3 := by omega
  rcases this with h2 | h3 <;> omega

lemma four_ne (hlK : ℓ + 3 = 4 * K) : (4 : ZMod ℓ) ≠ 0 := by
  intro h
  have h1 := four_K (ℓ := ℓ) hlK
  rw [h, zero_mul] at h1
  exact three_ne hlK h1.symm

lemma sixteen_ne (hlK : ℓ + 3 = 4 * K) : (16 : ZMod ℓ) ≠ 0 := by
  have h4 := four_ne hlK
  have : (16 : ZMod ℓ) = 4 * 4 := by norm_num
  rw [this]; exact mul_ne_zero h4 h4

lemma K_eq (hlK : ℓ + 3 = 4 * K) : (K : ZMod ℓ) = 3 / 4 := by
  have h4 := four_ne (ℓ := ℓ) hlK
  field_simp
  linear_combination four_K hlK

/-- Nonvanishing of `k` and `4k-3` for `1 ≤ k < ℓ`, `k ≠ K`. -/
lemma k_ne (hlK : ℓ + 3 = 4 * K) {k : ℕ} (hk0 : 0 < k) (hkl : k < ℓ) (hkK : k ≠ K) :
    (k : ZMod ℓ) ≠ 0 ∧ (4 * (k : ZMod ℓ) - 3) ≠ 0 := by
  refine ⟨natCast_ne_zero' hk0 hkl, ?_⟩
  have hK : K < ℓ := by omega
  have h1 : 4 * (k : ZMod ℓ) - 3 = 4 * ((k : ZMod ℓ) - K) := by
    linear_combination (four_K hlK)
  rw [h1]
  refine mul_ne_zero (four_ne hlK) ?_
  intro h
  exact natCast_ne_natCast hkl hK hkK (sub_eq_zero.1 h)

lemma term_id (hlK : ℓ + 3 = 4 * K) {n : ℕ} (hn : n + 1 < K) :
    (3 : ZMod ℓ) / (((n + 1 : ℕ) : ZMod ℓ) * (4 * ((n + 1 : ℕ) : ZMod ℓ) - 3)) =
      U ℓ K (n + 1) - U ℓ K n := by
  have hKl : K ≤ ℓ := by omega
  have hk := k_ne hlK (k := n + 1) (by omega) (by omega) (by omega)
  have hU := U_tel (ℓ := ℓ) (K := K) n
  rw [N_cast hKl] at hU
  have h4 := four_ne (ℓ := ℓ) hlK
  push_cast at hk ⊢
  obtain ⟨hx, hy⟩ := hk
  have h3 : (3 : ZMod ℓ) = 4 * K := (four_K hlK).symm
  have hz : (n : ZMod ℓ) + 1 - K ≠ 0 := by
    intro h
    apply hy
    linear_combination 4 * h - h3
  have : U ℓ K (n + 1) - U ℓ K n = -(1 / ((n : ZMod ℓ) + 1) - 1 / ((n : ZMod ℓ) + 1 + -(K : ZMod ℓ))) := by
    rw [← hU]; ring
  rw [this]
  have hy' : 4 * ((n : ZMod ℓ) + 1) - 3 = 4 * ((n : ZMod ℓ) + 1 - K) := by rw [h3]; ring
  rw [hy'] at hy ⊢
  have e : (n : ZMod ℓ) + 1 + -(K : ZMod ℓ) = (n : ZMod ℓ) + 1 - K := by ring
  rw [e]
  rw [h3]
  field_simp
  ring

lemma sumT (hlK : ℓ + 3 = 4 * K) {a b : ℕ} (hab : a ≤ b) (hb : b < K) :
    ∑ k ∈ Ioc a b, (3 : ZMod ℓ) / ((k : ZMod ℓ) * (4 * (k : ZMod ℓ) - 3)) =
      U ℓ K b - U ℓ K a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab, ih (by omega), term_id hlK hb]
    ring

lemma G_off (hlK : ℓ + 3 = 4 * K) {a b : ℕ} (ha : a < K) (hb : b < K) :
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

lemma diag_eq (hlK : ℓ + 3 = 4 * K) {a : ℕ} (ha : a < K) :
    (∑ k ∈ Icc 1 a, (1 / (16 * (k : ZMod ℓ) ^ 2) - 1 / (4 * (k : ZMod ℓ) - 3) ^ 2)) =
      (-cc ℓ K - G ℓ K a a) / 16 := by
  induction a with
  | zero => simp [cc]
  | succ n ih =>
    have hKl : K ≤ ℓ := by omega
    rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
    have hk := k_ne hlK (k := n + 1) (by omega) (by omega) (by omega)
    have hT := G_tel (ℓ := ℓ) (K := K) n
    rw [N_cast hKl] at hT
    have h4 := four_ne (ℓ := ℓ) hlK
    have h16 := sixteen_ne hlK
    push_cast at hk ⊢
    obtain ⟨hx, hy⟩ := hk
    have h3 : (3 : ZMod ℓ) = 4 * K := (four_K hlK).symm
    have hy' : 4 * ((n : ZMod ℓ) + 1) - 3 = 4 * ((n : ZMod ℓ) + 1 - K) := by rw [h3]; ring
    have hz : (n : ZMod ℓ) + 1 - K ≠ 0 := by
      intro h; apply hy; rw [hy', h, mul_zero]
    have : G ℓ K (n + 1) (n + 1) = G ℓ K n n - (1 / ((n : ZMod ℓ) + 1) ^ 2 -
        1 / ((n : ZMod ℓ) + 1 + -(K : ZMod ℓ)) ^ 2) := by rw [← hT]; ring
    rw [this, hy']
    have e : (n : ZMod ℓ) + 1 + -(K : ZMod ℓ) = (n : ZMod ℓ) + 1 - K := by ring
    rw [e]
    field_simp
    ring

end Mod

section Entries
variable {ℓ : ℕ} [Fact ℓ.Prime] {K : ℕ}

lemma N0n_lt {a b : ℕ} (h : a < b) :
    N0n a b = (1 / (16 * ((b : ℚ) - (a : ℚ)))) *
      ∑ k ∈ Ioc a b, 3 / ((k : ℚ) * (4 * (k : ℚ) - 3)) := by
  unfold N0n
  rw [if_neg h.ne, min_eq_left h.le, max_eq_right h.le]
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

end Entries

end CatalanLambda.Mirror
