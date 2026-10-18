module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import CatalanLambda.Cert.Tables

@[expose] public section

/-!
# Verified rational (scaled integer) bounds for `Real.log`

* `tabUp j`, `tabLo j` : 64-bit slots of the packed literals `TUP`, `TLO`; scale `2^64`,
  bracketing `log (1 + j/256)` for `j ≤ 256` (proved by `decide +kernel` on the atanh series).
* `logUpS N`, `logLoS N` : integers (scale `2^64`) bounding `log (N / 2^80)` from above/below,
  by `log q = e log 2 + log f`, `f ∈ [1,2)`, tangent/secant bounds `log x ≤ x - 1`, `1 - 1/x ≤ log x`.
-/

open Real

namespace CatalanLambda.Cert

def tabUp (j : ℕ) : ℕ := (TUP >>> (64 * j)) % 2 ^ 64
def tabLo (j : ℕ) : ℕ := (TLO >>> (64 * j)) % 2 ^ 64

/-! ### atanh series partial sums and tails -/

def atS {α : Type _} [Field α] (x : α) : ℕ → α
  | 0 => 0
  | n + 1 => atS x n + 2 * x ^ (2 * n + 1) / (2 * (n : α) + 1)

def atT {α : Type _} [Field α] (x : α) (n : ℕ) : α :=
  2 * x ^ (2 * n + 1) / ((2 * (n : α) + 1) * (1 - x ^ 2))

lemma atS_cast (q : ℚ) (n : ℕ) : ((atS q n : ℚ) : ℝ) = atS (q : ℝ) n := by
  induction n with
  | zero => simp [atS]
  | succ n ih => simp [atS, ih]

lemma atT_cast (q : ℚ) (n : ℕ) : ((atT q n : ℚ) : ℝ) = atT (q : ℝ) n := by
  simp [atT]

lemma atS_eq_sum (x : ℝ) (n : ℕ) :
    atS x n = ∑ k ∈ Finset.range n, 2 * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1) := by
  induction n with
  | zero => simp [atS]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; simp [atS]; ring

lemma log_atanh_bounds {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    atS x n ≤ log (1 + x) - log (1 - x) ∧
      log (1 + x) - log (1 - x) ≤ atS x n + atT x n := by
  have hx : |x| < 1 := by rwa [abs_of_nonneg h0]
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one hx
  set f : ℕ → ℝ := fun k => 2 * (1 / (2 * (k : ℝ) + 1)) * x ^ (2 * k + 1) with hf
  have hfn : ∀ k, 0 ≤ f k := fun k => by simp only [hf]; positivity
  rw [atS_eq_sum]
  constructor
  · exact sum_le_hasSum (Finset.range n) (fun k _ => hfn k) hs
  · have ht := (hasSum_nat_add_iff' n).mpr hs
    have hx2 : x ^ 2 < 1 := by nlinarith
    have hg : HasSum (fun k : ℕ => (2 * x ^ (2 * n + 1) / (2 * (n : ℝ) + 1)) * (x ^ 2) ^ k)
        ((2 * x ^ (2 * n + 1) / (2 * (n : ℝ) + 1)) * (1 - x ^ 2)⁻¹) :=
      (hasSum_geometric_of_lt_one (by positivity) hx2).mul_left _
    have hle : ∀ k, f (k + n) ≤ (2 * x ^ (2 * n + 1) / (2 * (n : ℝ) + 1)) * (x ^ 2) ^ k := by
      intro k
      simp only [hf]
      have e1 : x ^ (2 * (k + n) + 1) = x ^ (2 * n + 1) * (x ^ 2) ^ k := by
        rw [← pow_mul, ← pow_add]; congr 1; ring
      rw [e1]
      have hp : 0 ≤ x ^ (2 * n + 1) * (x ^ 2) ^ k := by positivity
      have hd : 1 / (2 * ((k + n : ℕ) : ℝ) + 1) ≤ 1 / (2 * (n : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast; nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      calc 2 * (1 / (2 * ((k + n : ℕ) : ℝ) + 1)) * (x ^ (2 * n + 1) * (x ^ 2) ^ k)
          ≤ 2 * (1 / (2 * (n : ℝ) + 1)) * (x ^ (2 * n + 1) * (x ^ 2) ^ k) := by gcongr
        _ = 2 * x ^ (2 * n + 1) / (2 * (n : ℝ) + 1) * (x ^ 2) ^ k := by ring
    have := hasSum_le hle ht hg
    unfold atT
    have e2 : (2 * x ^ (2 * n + 1) / (2 * (n : ℝ) + 1)) * (1 - x ^ 2)⁻¹
        = 2 * x ^ (2 * n + 1) / ((2 * (n : ℝ) + 1) * (1 - x ^ 2)) := by
      field_simp
    rw [e2] at this
    linarith

def tabCheck (j : ℕ) : Bool :=
  decide ((tabLo j : ℚ) / 2 ^ 64 ≤ atS ((j : ℚ) / (512 + j)) 25 ∧
    atS ((j : ℚ) / (512 + j)) 25 + atT ((j : ℚ) / (512 + j)) 25 ≤ (tabUp j : ℚ) / 2 ^ 64)

theorem tab_ok : ∀ j < 257, tabCheck j = true := by decide +kernel

lemma tab_bounds {j : ℕ} (hj : j ≤ 256) :
    (tabLo j : ℝ) / 2 ^ 64 ≤ log (1 + (j : ℝ) / 256) ∧
      log (1 + (j : ℝ) / 256) ≤ (tabUp j : ℝ) / 2 ^ 64 := by
  have h := tab_ok j (by omega)
  simp only [tabCheck, decide_eq_true_eq] at h
  obtain ⟨hl, hu⟩ := h
  have hx0 : (0 : ℝ) ≤ (j : ℝ) / (512 + j) := by positivity
  have hx1 : (j : ℝ) / (512 + j) < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  obtain ⟨b1, b2⟩ := log_atanh_bounds hx0 hx1 25
  have e : log (1 + (j : ℝ) / 256) = log (1 + (j : ℝ) / (512 + j)) - log (1 - (j : ℝ) / (512 + j)) := by
    rw [← Real.log_div]
    · congr 1; field_simp; ring
    · have : (0 : ℝ) < 1 + (j : ℝ) / (512 + j) := by positivity
      exact this.ne'
    · have : (0 : ℝ) < 1 - (j : ℝ) / (512 + j) := by linarith
      exact this.ne'
  rw [e]
  have c1 : ((tabLo j : ℚ) / 2 ^ 64 : ℚ) ≤ atS ((j : ℚ) / (512 + j)) 25 := hl
  have c2 := hu
  have d1 := (Rat.cast_le (K := ℝ)).mpr c1
  have d2 := (Rat.cast_le (K := ℝ)).mpr c2
  rw [Rat.cast_add, atS_cast, atT_cast] at d2
  rw [atS_cast] at d1
  push_cast at d1 d2
  constructor <;> linarith

/-! ### log of `N / 2^80` -/

def logUpS (N : ℕ) : ℤ :=
  let L := Nat.log2 N
  let m := (N <<< 8) >>> L
  let e : ℤ := ((L : ℤ) - 80) * (if 80 ≤ L then (tabUp 256 : ℤ) else (tabLo 256 : ℤ))
  let R : ℤ := (((N <<< 72) + (m <<< L) - 1) / (m <<< L) : ℕ)
  e + (tabUp (m - 256) : ℤ) + R - 2 ^ 64

def logLoS (N : ℕ) : ℤ :=
  let L := Nat.log2 N
  let m := (N <<< 8) >>> L
  let e : ℤ := ((L : ℤ) - 80) * (if 80 ≤ L then (tabLo 256 : ℤ) else (tabUp 256 : ℤ))
  let c : ℤ := ((((m + 1) <<< (L + 56)) + N - 1) / N : ℕ)
  e + (tabLo (m - 256 + 1) : ℤ) + 2 ^ 64 - c

lemma ceil_div_ge (a b : ℕ) (hb : 0 < b) : a ≤ (a + b - 1) / b * b := by
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  have : b * ((a + b - 1) / b) = (a + b - 1) / b * b := Nat.mul_comm _ _
  omega

lemma log2_facts {N : ℕ} (hN : 0 < N) :
    2 ^ N.log2 ≤ N ∧ N < 2 ^ (N.log2 + 1) := ⟨Nat.log2_self_le hN.ne', Nat.lt_log2_self⟩

lemma m_facts {N : ℕ} (hN : 0 < N) :
    256 ≤ (N <<< 8) >>> N.log2 ∧ (N <<< 8) >>> N.log2 < 512 ∧
      ((N <<< 8) >>> N.log2) * 2 ^ N.log2 ≤ 256 * N ∧
      256 * N < (((N <<< 8) >>> N.log2) + 1) * 2 ^ N.log2 := by
  obtain ⟨h1, h2⟩ := log2_facts hN
  have hp : 0 < 2 ^ N.log2 := by positivity
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have e : N * 2 ^ 8 = 256 * N := by ring
  rw [e]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.le_div_iff_mul_le hp]; nlinarith
  · rw [Nat.div_lt_iff_lt_mul hp]; rw [pow_succ] at h2; nlinarith
  · exact Nat.div_mul_le_self _ _
  · have := Nat.lt_mul_div_succ (256 * N) hp
    rw [Nat.add_mul, Nat.one_mul]
    nlinarith [this, Nat.div_add_mod (256 * N) (2 ^ N.log2)]

lemma log_N_decomp {N : ℕ} (hN : 0 < N) :
    Real.log ((N : ℝ) / 2 ^ 80) =
      ((N.log2 : ℝ) - 80) * Real.log 2 + Real.log ((N : ℝ) / 2 ^ N.log2) := by
  have h1 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.log_div h1.ne' (by positivity), Real.log_div h1.ne' (by positivity),
    Real.log_pow, Real.log_pow]
  push_cast; ring

lemma log2_bounds : (tabLo 256 : ℝ) / 2 ^ 64 ≤ Real.log 2 ∧ Real.log 2 ≤ (tabUp 256 : ℝ) / 2 ^ 64 := by
  have h := tab_bounds (le_refl 256)
  have e : (1 : ℝ) + ((256 : ℕ) : ℝ) / 256 = 2 := by norm_num
  rw [e] at h
  exact h

theorem logUpS_spec {N : ℕ} (hN : 0 < N) :
    Real.log ((N : ℝ) / 2 ^ 80) ≤ (logUpS N : ℝ) / 2 ^ 64 := by
  obtain ⟨hm1, hm2, hm3, hm4⟩ := m_facts hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [log_N_decomp hN]
  unfold logUpS
  simp only []
  generalize hL : N.log2 = L at *
  generalize hm : (N <<< 8) >>> L = m at *
  have hmr : (256 : ℝ) ≤ m := by exact_mod_cast hm1
  have hpL : (0 : ℝ) < 2 ^ L := by positivity
  have hmL : (m : ℝ) * 2 ^ L ≤ 256 * N := by exact_mod_cast hm3
  have hb : 0 < m <<< L := by
    rw [Nat.shiftLeft_eq]; positivity
  have hceil := ceil_div_ge (N <<< 72) (m <<< L) hb
  generalize hR : ((N <<< 72) + (m <<< L) - 1) / (m <<< L) = R at *
  have hRr : (N : ℝ) * 2 ^ 72 ≤ R * (m * 2 ^ L) := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq] at hceil
    exact_mod_cast hceil
  have hf0 : (m : ℝ) / 256 = 1 + ((m - 256 : ℕ) : ℝ) / 256 := by
    rw [Nat.cast_sub hm1]; push_cast; ring
  have hi : m - 256 ≤ 256 := by omega
  obtain ⟨_, hTup⟩ := tab_bounds hi
  rw [← hf0] at hTup
  obtain ⟨hl2, hu2⟩ := log2_bounds
  have hf0pos : (0 : ℝ) < (m : ℝ) / 256 := by positivity
  have hfpos : (0 : ℝ) < (N : ℝ) / 2 ^ L := by positivity
  have hsplit : Real.log ((N : ℝ) / 2 ^ L) = Real.log ((m : ℝ) / 256) +
      Real.log (((N : ℝ) / 2 ^ L) / ((m : ℝ) / 256)) := by
    rw [← Real.log_mul hf0pos.ne' (by positivity)]; congr 1; field_simp
  have htan := Real.log_le_sub_one_of_pos (x := ((N : ℝ) / 2 ^ L) / ((m : ℝ) / 256))
    (by positivity)
  have hA : (0 : ℝ) < 2 ^ 64 := by positivity
  have hratio : (((N : ℝ) / 2 ^ L) / ((m : ℝ) / 256)) ≤ R / 2 ^ 64 := by
    have : (((N : ℝ) / 2 ^ L) / ((m : ℝ) / 256)) = (N * 2 ^ 72) / (m * 2 ^ L) / 2 ^ 64 := by
      field_simp; ring
    rw [this]
    apply div_le_div_of_nonneg_right _ hA.le
    rw [div_le_iff₀ (by positivity)]; exact hRr
  by_cases h80 : 80 ≤ L
  · rw [if_pos h80]
    have h0 : (0 : ℝ) ≤ (L : ℝ) - 80 := by
      have : (80 : ℝ) ≤ L := by exact_mod_cast h80
      linarith
    have := mul_le_mul_of_nonneg_left hu2 h0
    push_cast
    rw [hsplit, le_div_iff₀ hA]
    linarith
  · rw [if_neg h80]
    have h0 : (L : ℝ) - 80 ≤ 0 := by
      have : (L : ℝ) < 80 := by exact_mod_cast (not_le.mp h80)
      linarith
    have := mul_le_mul_of_nonpos_left hl2 h0
    push_cast
    rw [hsplit, le_div_iff₀ hA]
    linarith

theorem logLoS_spec {N : ℕ} (hN : 0 < N) :
    (logLoS N : ℝ) / 2 ^ 64 ≤ Real.log ((N : ℝ) / 2 ^ 80) := by
  obtain ⟨hm1, hm2, hm3, hm4⟩ := m_facts hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [log_N_decomp hN]
  unfold logLoS
  simp only []
  generalize hL : N.log2 = L at *
  generalize hm : (N <<< 8) >>> L = m at *
  have hmr : (256 : ℝ) ≤ m := by exact_mod_cast hm1
  have hpL : (0 : ℝ) < 2 ^ L := by positivity
  have hmL : 256 * (N : ℝ) < ((m : ℝ) + 1) * 2 ^ L := by exact_mod_cast hm4
  have hceil := ceil_div_ge (((m + 1) <<< (L + 56))) N hN
  generalize hc : (((m + 1) <<< (L + 56)) + N - 1) / N = c at *
  have hcr : (((m : ℝ) + 1) * 2 ^ (L + 56)) ≤ c * N := by
    rw [Nat.shiftLeft_eq] at hceil
    exact_mod_cast hceil
  have hf1 : ((m : ℝ) + 1) / 256 = 1 + ((m - 256 + 1 : ℕ) : ℝ) / 256 := by
    rw [Nat.cast_add, Nat.cast_sub hm1]; push_cast; ring
  have hi : m - 256 + 1 ≤ 256 := by omega
  obtain ⟨hTlo, _⟩ := tab_bounds hi
  rw [← hf1] at hTlo
  obtain ⟨hl2, hu2⟩ := log2_bounds
  have hf1pos : (0 : ℝ) < ((m : ℝ) + 1) / 256 := by positivity
  have hfpos : (0 : ℝ) < (N : ℝ) / 2 ^ L := by positivity
  have hsplit : Real.log ((N : ℝ) / 2 ^ L) = Real.log (((m : ℝ) + 1) / 256) +
      Real.log (((N : ℝ) / 2 ^ L) / (((m : ℝ) + 1) / 256)) := by
    rw [← Real.log_mul hf1pos.ne' (by positivity)]; congr 1; field_simp
  have htan := Real.one_sub_inv_le_log_of_pos
    (x := ((N : ℝ) / 2 ^ L) / (((m : ℝ) + 1) / 256)) (by positivity)
  have hA : (0 : ℝ) < 2 ^ 64 := by positivity
  have hratio : ((((N : ℝ) / 2 ^ L) / (((m : ℝ) + 1) / 256))⁻¹) ≤ c / 2 ^ 64 := by
    have : ((((N : ℝ) / 2 ^ L) / (((m : ℝ) + 1) / 256))⁻¹) =
        (((m : ℝ) + 1) * 2 ^ (L + 56)) / N / 2 ^ 64 := by
      field_simp; ring
    rw [this]
    apply div_le_div_of_nonneg_right _ hA.le
    rw [div_le_iff₀ hNr]; exact hcr
  by_cases h80 : 80 ≤ L
  · rw [if_pos h80]
    have h0 : (0 : ℝ) ≤ (L : ℝ) - 80 := by
      have : (80 : ℝ) ≤ L := by exact_mod_cast h80
      linarith
    have := mul_le_mul_of_nonneg_left hl2 h0
    push_cast
    rw [hsplit, div_le_iff₀ hA]
    linarith
  · rw [if_neg h80]
    have h0 : (L : ℝ) - 80 ≤ 0 := by
      have : (L : ℝ) < 80 := by exact_mod_cast (not_le.mp h80)
      linarith
    have := mul_le_mul_of_nonpos_left hu2 h0
    push_cast
    rw [hsplit, div_le_iff₀ hA]
    linarith

end CatalanLambda.Cert
