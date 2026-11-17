module

public import CatalanCore.Lai.ContentL12
public import CatalanCore.Lai.ClassCount
public import CatalanCore.Lai.ContentTables
public import CatalanCore.Lai.ContentFinal
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

@[expose] public section

/-!
# `CatalanCore.Lai.ContentBridge`: the integer law versus the 22 affine pieces (`BridgeStmt`, F2)

Paper: `N9-LAI-CONTENT-EXACT-2026-11-16.md`, Theorem C01 (steps 1-3: class masses, greedy shape, the affine
pieces) and Assembly ("finite class counts replaced by masses change each `v_p` by `O(n/p)`").

For a prime `p` with `√(8n) < p < 3n` (`Rng`), `Wlaw n p = Σ pot2 - ν_p + x₁ + x₂` is the exact lower bound of
Theorems L1/L2.  This module proves `BridgeStmt`: for `t = r₆/p` in the piece `j` of Theorem C01,
`p c₀(q) + n c₁(q) - 1000 (q² + 1) ≤ Wlaw n p` (`q = q₆`).  The proof compares with `p · c01Num` instead of
computing the 22 pieces:

* `sum_pot2_split`, `sum_classes`, `T_cl`: `Σ pot2 = Σ_c sz_c HL(λ, σ_c) + d λ` (`HL l σ = μ² + (σ - 5) μ`);
* `nuP_closed`, `nuP_real`: `ν_p = 9n²/p - 3n + p θ (1 - θ)` exactly;
* `rel_a`, `rel_b`, `sz_int`, `d_add_N_le`, `kk_range`, `HL_pred`, `NL_pred`, `two_T`: the greedy sum in terms of
  the level `λ_c = q₆ + (q₆ mod 3) - 3`, for both values `k = 1, 2` of Lemma T;
* `mass_A..D`, `scaled_Num`: `2 p · c01Num (q mod 6) q (r/p) = cNum - 2ν` (integer `cNum` from the scaled masses);
* `x_k1`, `x_k2`, `x_part`, `HL_bound`, `W_ge`: `cNum - 2ν - 214 q² ≤ 2 Wlaw`;
* `piece_closed`, `bridge_proof`: the closed-left piece identity (the only boundary point is `t = 0`, because the
  lower ends are `a/b` with `b ≤ 7 < p`) and `BridgeStmt`.
-/


set_option linter.deprecated false

open Finset MvPolynomial CatalanCore.Basic CatalanCore.Content
open scoped Nat

namespace CatalanCore.Lai

section Closed

/-- `Σ_{i<m} (2i - 4 + σ) = m² + (σ - 5) m`. -/
theorem sum_aff (m σ : ℕ) :
    ∑ i ∈ Finset.range m, (2 * (i : ℤ) - 4 + σ) = (m : ℤ) * m + ((σ : ℤ) - 5) * m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- the potentials sum to the greedy sum: `Σ_x pot2 = Σ_s (μ_s² + (σ_s - 5) μ_s) + d λ`. -/
theorem sum_pot2_split (n p : ℕ) :
    ∑ x : LIdx n p, pot2 n p x =
      ∑ s ∈ range p, ((mu n p s : ℤ) * mu n p s + ((sig n p s : ℤ) - 5) * mu n p s) +
        (dcnt n p : ℤ) * lam n p := by
  unfold LIdx
  rw [Fintype.sum_sum_type, Fintype.sum_sigma]
  congr 1
  · rw [← Fin.sum_univ_eq_sum_range
      (fun s => ((mu n p s : ℤ) * mu n p s + ((sig n p s : ℤ) - 5) * mu n p s)) p]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [pot2]
    rw [Fin.sum_univ_eq_sum_range (fun i => 2 * (i : ℤ) - 4 + (sig n p r : ℤ)) (mu n p r)]
    exact sum_aff _ _
  · simp [pot2]

/-- Sum over the residues as a sum over the four classes. -/
theorem sum_classes {M : Type*} [AddCommMonoid M] {n p : ℕ} (h : Rng n p) (F : ℕ → M) :
    ∑ s ∈ range p, F (sig n p s) =
      szA n p • F 0 + szB n p • F 3 + szC n p • F 2 + szD n p • F 5 := by
  classical
  have hmaps : ∀ s ∈ range p, sig n p s ∈ ({0, 2, 3, 5} : Finset ℕ) := by
    intro s _
    rcases sig_cases n p s with ⟨_, _, c⟩ | ⟨_, _, c⟩ | ⟨_, _, c⟩ | ⟨_, _, c⟩ <;> simp [c]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have e : ∀ σ : ℕ, ∑ s ∈ (range p).filter (fun s => sig n p s = σ), F (sig n p s) =
      ((range p).filter (fun s => sig n p s = σ)).card • F σ := by
    intro σ
    rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.1 hs).2]), Finset.sum_const]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton, e]
  simp [card_sig_zero h, card_sig_two h, card_sig_three h, card_sig_five h]
  abel

/-- `2 Σ_{i<N} ⌊i/p⌋ = p q (q - 1) + 2 q r` with `N = q p + r`. -/
theorem sum_div_range (p : ℕ) (hp : 0 < p) (N : ℕ) :
    2 * ((∑ i ∈ range N, (i / p : ℕ) : ℕ) : ℤ) =
      (p : ℤ) * ((N / p : ℕ) : ℤ) * (((N / p : ℕ) : ℤ) - 1) + 2 * ((N / p : ℕ) : ℤ) * ((N % p : ℕ) : ℤ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Nat.cast_add, mul_add, ih]
    have h1 := Nat.div_add_mod N p
    have h2 := Nat.mod_lt N hp
    by_cases hc : N % p + 1 = p
    · have hN1 : N + 1 = (N / p + 1) * p := by nlinarith
      have hd : (N + 1) / p = N / p + 1 := Nat.div_eq_of_eq_mul_left hp hN1
      have hm : (N + 1) % p = 0 := by rw [hN1]; exact Nat.mul_mod_left _ _
      rw [hd, hm]
      have hcz : ((N % p : ℕ) : ℤ) + 1 = p := by exact_mod_cast hc
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
      linear_combination 2 * ((N / p : ℕ) : ℤ) * hcz
    · have hlt : N % p + 1 < p := by omega
      have hd : (N + 1) / p = N / p := by
        apply Nat.div_eq_of_lt_le
        · exact le_trans (Nat.div_mul_le_self N p) (Nat.le_succ N)
        · nlinarith
      have hm : (N + 1) % p = N % p + 1 := by
        have : N + 1 = p * (N / p) + (N % p + 1) := by omega
        rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      rw [hd, hm]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

theorem padicValNat_prod_sq (p : ℕ) [Fact p.Prime] (m : ℕ) :
    padicValNat p (∏ i ∈ range m, (i ! : ℕ) ^ 2) = ∑ i ∈ range m, 2 * padicValNat p (i !) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (∏ i ∈ range m, (i ! : ℕ) ^ 2) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (Nat.factorial_ne_zero i)
    have h2 : ((m ! : ℕ) ^ 2) ≠ 0 := pow_ne_zero _ (Nat.factorial_ne_zero m)
    rw [Finset.prod_range_succ, Finset.sum_range_succ, padicValNat.mul h1 h2, ih,
      padicValNat.pow (m !) 2]

theorem padicValNat_fact_lt (p : ℕ) [Fact p.Prime] {i : ℕ} (hi : i < p ^ 2) :
    padicValNat p (i !) = i / p := by
  have hb : Nat.log p i < 2 := by
    by_cases h0 : i = 0
    · simp [h0]
    · exact Nat.log_lt_of_lt_pow h0 hi
  rw [padicValNat_factorial hb]
  simp

/-- `ν_p = Σ_{i<3n} 2 ⌊i/p⌋` for `8n < p²`. -/
theorem nuP_eq {n p : ℕ} [Fact p.Prime] (h8 : 8 * n < p ^ 2) :
    (nuP n p : ℤ) = ∑ i ∈ range (3 * n), 2 * ((i / p : ℕ) : ℤ) := by
  unfold nuP
  rw [padicValNat_prod_sq, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have : i < p ^ 2 := by have := Finset.mem_range.1 hi; omega
  rw [padicValNat_fact_lt p this]
  simp only [Nat.cast_mul, Nat.cast_ofNat]

/-- the closed form of `ν_p`. -/
theorem nuP_closed {n p : ℕ} [hp : Fact p.Prime] (h8 : 8 * n < p ^ 2) :
    (nuP n p : ℤ) = (p : ℤ) * ((3 * n / p : ℕ) : ℤ) * (((3 * n / p : ℕ) : ℤ) - 1) +
      2 * ((3 * n / p : ℕ) : ℤ) * ((3 * n % p : ℕ) : ℤ) := by
  have := sum_div_range p hp.out.pos (3 * n)
  rw [Nat.cast_sum] at this
  rw [nuP_eq h8, ← Finset.mul_sum]
  exact this


section Rel

variable {n p : ℕ}

/-- `q₂ = ⌊q₆/3⌋` and `3 r₂ = (q₆ mod 3) p + r₆`. -/
theorem rel_a (h : Rng n p) :
    q2 n p = q6 n p / 3 ∧ 3 * r2 n p = (q6 n p % 3) * p + r6 n p := by
  have hp := h.p5
  have a6 := qr6 n p (by omega)
  have a2 := qr2 n p (by omega)
  have b6 := r6_lt n p (by omega)
  have b2 := r2_lt n p (by omega)
  have a6' : (6 * n : ℤ) = (q6 n p : ℤ) * p + r6 n p := by exact_mod_cast a6
  have a2' : (2 * n : ℤ) = (q2 n p : ℤ) * p + r2 n p := by exact_mod_cast a2
  have key : ((q6 n p : ℤ) - 3 * q2 n p) * p = 3 * r2 n p - r6 n p := by nlinarith
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (by omega : 0 < p)
  have b6' : (r6 n p : ℤ) < p := by exact_mod_cast b6
  have b2' : (r2 n p : ℤ) < p := by exact_mod_cast b2
  have r6n : (0 : ℤ) ≤ (r6 n p : ℤ) := Nat.cast_nonneg _
  have r2n : (0 : ℤ) ≤ (r2 n p : ℤ) := Nat.cast_nonneg _
  have hlo : (0 : ℤ) ≤ (q6 n p : ℤ) - 3 * q2 n p := by
    by_contra hc
    push_neg at hc
    have h1 : (q6 n p : ℤ) - 3 * q2 n p ≤ -1 := by omega
    nlinarith
  have hhi : (q6 n p : ℤ) - 3 * q2 n p ≤ 2 := by
    by_contra hc
    push_neg at hc
    have h1 : 3 ≤ (q6 n p : ℤ) - 3 * q2 n p := by omega
    nlinarith
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ, (q6 n p : ℤ) = 3 * q2 n p + ρ :=
    ⟨((q6 n p : ℤ) - 3 * q2 n p).toNat, by omega⟩
  have hρ2 : ρ ≤ 2 := by omega
  have hq3 : q6 n p % 3 = ρ := by omega
  refine ⟨by omega, ?_⟩
  rw [hq3]
  have : (ρ : ℤ) * p = 3 * r2 n p - r6 n p := by rw [hρ] at key; nlinarith
  zify
  linarith

/-- `ℤ`-forms of the class sizes. -/
theorem sz_int (h : Rng n p) :
    (szA n p : ℤ) = min ((r6 n p : ℤ) + 1) ((p : ℤ) - r2 n p) ∧
    (szB n p : ℤ) = max 0 ((r6 n p : ℤ) + 1 - ((p : ℤ) - r2 n p)) ∧
    (szC n p : ℤ) = max 0 (((p : ℤ) - r2 n p) - ((r6 n p : ℤ) + 1)) ∧
    (szD n p : ℤ) = (p : ℤ) - max ((r6 n p : ℤ) + 1) ((p : ℤ) - r2 n p) := by
  have hp := h.p5
  have b6 := r6_lt n p (by omega)
  have b2 := r2_lt n p (by omega)
  unfold szA szB szC szD
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- `|N| + d ≤ p`: at most one index of each tie residue sits at the level `λ`. -/
theorem d_add_N_le (h : Rng n p) : (dcnt n p : ℤ) + (Ncnt n p : ℤ) ≤ p := by
  have hp := h.p5
  have hn := h.n2
  have h0 := lam_ge_zero h
  have h1 := lam_le_top h
  obtain ⟨hs1, hs2⟩ := lam_spec n p (by omega) (by omega)
  have hlt := hs2 (lam n p - 1) (by omega)
  have f1 := cnt_formula h (lam n p) (by omega) h1
  have f0 := cnt_formula h (lam n p - 1) (by omega) (by omega)
  have hsum : ∑ s ∈ range p, mu n p s = cnt n p (lam n p - 1) := rfl
  have hd : dcnt n p = 3 * n - cnt n p (lam n p - 1) := by unfold dcnt; rw [hsum]
  have b2 := r2_lt n p (by omega)
  have hN := Ncnt_eq h
  have hz := sz_int h
  have hs := sz_sum h
  have b6 := r6_lt n p (by omega)
  -- cnt(λ) - cnt(λ-1) is `p - r₂` (λ even) or `r₂` (λ odd)
  by_cases hpar : lam n p % 2 = 0
  · have e1 : ((lam n p + 4) / 2).toNat = ((lam n p - 1 + 4) / 2).toNat + 1 := by omega
    have e2 : ((lam n p + 1) / 2).toNat = ((lam n p - 1 + 1) / 2).toNat := by omega
    rw [e1, e2] at f1
    have hdn : (dcnt n p : ℤ) ≤ (p : ℤ) - r2 n p := by
      have : dcnt n p + cnt n p (lam n p - 1) ≤ cnt n p (lam n p) := by omega
      rw [f1, f0] at this
      have hp2 : r2 n p ≤ p := by omega
      zify [hp2] at this
      nlinarith
    rw [hN, if_pos hpar]
    have : (szB n p : ℤ) + szD n p = r2 n p := by
      rw [hz.2.1, hz.2.2.2]; omega
    push_cast
    omega
  · have hodd : lam n p % 2 = 1 := by omega
    have e1 : ((lam n p + 4) / 2).toNat = ((lam n p - 1 + 4) / 2).toNat := by omega
    have e2 : ((lam n p + 1) / 2).toNat = ((lam n p - 1 + 1) / 2).toNat + 1 := by omega
    rw [e1, e2] at f1
    have hdn : (dcnt n p : ℤ) ≤ r2 n p := by
      have : dcnt n p + cnt n p (lam n p - 1) ≤ cnt n p (lam n p) := by omega
      rw [f1, f0] at this
      zify at this
      nlinarith
    rw [hN, if_neg hpar]
    have : (szA n p : ℤ) + szC n p = (p : ℤ) - r2 n p := by
      rw [hz.1, hz.2.2.1]; omega
    push_cast
    omega

/-- `k = 2q₆ - 3q₂ - 2 - λ ∈ {1, 2}` (Lemma T). -/
theorem kk_range (h : Rng n p) :
    1 ≤ 2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 2 - lam n p ∧
      2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 2 - lam n p ≤ 2 := by
  have hp := h.p5
  have hT := lemmaT h
  have hdN := d_add_N_le h
  have hd0 : (0 : ℤ) ≤ dcnt n p := Nat.cast_nonneg _
  have hN0 : (0 : ℤ) ≤ Ncnt n p := Nat.cast_nonneg _
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (by omega : 0 < p)
  set k : ℤ := 2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 2 - lam n p with hk
  have h1 : 1 ≤ k := by
    by_contra hc
    push_neg at hc
    have : k ≤ 0 := by omega
    nlinarith
  have h2 : k ≤ 2 := by
    by_contra hc
    push_neg at hc
    have : 3 ≤ k := by omega
    have hp3 : (5 : ℤ) ≤ p := by exact_mod_cast hp
    nlinarith
  exact ⟨h1, h2⟩

end Rel

section TCl

variable {n p : ℕ}

/-- number of indices of class `σ` at level `l`. -/
def muL (l σ : ℤ) : ℤ := (l + 4 + (if (l - σ) % 2 = 0 then 0 else 1) - σ) / 2

/-- `Σ_{i<μ} (2i - 4 + σ)` with `μ = muL l σ`. -/
def HL (l σ : ℤ) : ℤ := muL l σ * muL l σ + (σ - 5) * muL l σ

/-- `|N|` at level `l`: the classes of the other parity. -/
def NL (n p : ℕ) (l : ℤ) : ℤ :=
  if l % 2 = 0 then (szB n p : ℤ) + szD n p else (szA n p : ℤ) + szC n p

theorem mu_eq (h : Rng n p) {s : ℕ} (hs : s < p) :
    (mu n p s : ℤ) = muL (lam n p) (sig n p s) := by
  have := (lemmaS h).2.2.1 s hs
  unfold muL
  split_ifs at this ⊢ <;> omega

/-- the greedy sum in closed form. -/
theorem T_cl (h : Rng n p) :
    ∑ x : LIdx n p, pot2 n p x =
      (szA n p : ℤ) * HL (lam n p) 0 + (szB n p : ℤ) * HL (lam n p) 3 +
        (szC n p : ℤ) * HL (lam n p) 2 + (szD n p : ℤ) * HL (lam n p) 5 +
        (dcnt n p : ℤ) * lam n p := by
  rw [sum_pot2_split]
  congr 1
  have e : ∀ s ∈ range p, ((mu n p s : ℤ) * mu n p s + ((sig n p s : ℤ) - 5) * mu n p s) =
      HL (lam n p) (sig n p s : ℤ) := by
    intro s hs
    rw [mu_eq h (Finset.mem_range.1 hs)]
    rfl
  rw [Finset.sum_congr rfl e]
  have := sum_classes h (fun σ : ℕ => HL (lam n p) (σ : ℤ))
  rw [this]
  simp only [nsmul_eq_mul, Nat.cast_zero, Nat.cast_ofNat]

theorem HL_pred (l σ : ℤ) :
    HL (l - 1) σ = if (l - σ) % 2 = 0 then HL l σ else HL l σ - (l - 1) := by
  unfold HL muL
  by_cases hp : (l - σ) % 2 = 0
  · have h1 : ¬ ((l - 1 - σ) % 2 = 0) := by omega
    rw [if_neg h1, if_pos hp, if_pos hp]
    have e : (l - 1 + 4 + 1 - σ) / 2 = (l + 4 + 0 - σ) / 2 := by omega
    rw [e]
  · have h1 : (l - 1 - σ) % 2 = 0 := by omega
    rw [if_pos h1, if_neg hp, if_neg hp]
    have e : (l - 1 + 4 + 0 - σ) / 2 = (l + 4 + 1 - σ) / 2 - 1 := by omega
    have e2 : 2 * ((l + 4 + 1 - σ) / 2) = l + 5 - σ := by omega
    rw [e]
    nlinarith

theorem NL_pred (h : Rng n p) (l : ℤ) : NL n p (l - 1) = (p : ℤ) - NL n p l := by
  have hs := sz_sum h
  have : (szA n p : ℤ) + szB n p + szC n p + szD n p = p := by exact_mod_cast hs
  unfold NL
  by_cases hp : l % 2 = 0
  · have : ¬ ((l - 1) % 2 = 0) := by omega
    rw [if_neg this, if_pos hp]; linarith
  · have : (l - 1) % 2 = 0 := by omega
    rw [if_pos this, if_neg hp]; linarith

/-- **Two times the greedy sum**, in terms of the level `λ_c = q₆ + ρ - 3` (`ρ = q₆ mod 3`), valid for
both values `k = 1, 2` of Lemma T. -/
theorem two_T (h : Rng n p) :
    2 * ∑ x : LIdx n p, pot2 n p x =
      2 * ((szA n p : ℤ) * HL ((q6 n p : ℤ) + (q6 n p % 3 : ℕ) - 3) 0 +
        (szB n p : ℤ) * HL ((q6 n p : ℤ) + (q6 n p % 3 : ℕ) - 3) 3 +
        (szC n p : ℤ) * HL ((q6 n p : ℤ) + (q6 n p % 3 : ℕ) - 3) 2 +
        (szD n p : ℤ) * HL ((q6 n p : ℤ) + (q6 n p % 3 : ℕ) - 3) 5) +
      ((p : ℤ) - NL n p ((q6 n p : ℤ) + (q6 n p % 3 : ℕ) - 3) - 2) *
        (((q6 n p : ℤ) + (q6 n p % 3 : ℕ) - 3) - ((2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 2 - lam n p) - 1)) := by
  obtain ⟨hk1, hk2⟩ := kk_range h
  have ha := (rel_a h).1
  have hT := lemmaT h
  have hN := Ncnt_eq h
  have hlc : lam n p = (q6 n p : ℤ) + (q6 n p % 3 : ℕ) - 2 - (2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 2 - lam n p) := by
    have : (q6 n p : ℤ) = 3 * (q2 n p : ℤ) + (q6 n p % 3 : ℕ) := by omega
    omega
  rw [T_cl h]
  set k : ℤ := 2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 2 - lam n p with hk
  set lc : ℤ := (q6 n p : ℤ) + (q6 n p % 3 : ℕ) - 3 with hlc'
  have hNl : (Ncnt n p : ℤ) = NL n p (lam n p) := by
    rw [hN]; unfold NL; split_ifs <;> push_cast <;> rfl
  have hk' : k = 1 ∨ k = 2 := by omega
  rcases hk' with h1 | h2
  · have hlam : lam n p = lc := by rw [hlc']; omega
    rw [h1] at hT
    rw [hlam] at hNl ⊢
    have hd : 2 * (dcnt n p : ℤ) = p - NL n p lc - 2 := by rw [← hNl] at *; linarith
    rw [h1]
    nlinarith
  · have hlam : lam n p = lc - 1 := by rw [hlc']; omega
    rw [h2] at hT
    rw [hlam] at hNl ⊢
    rw [NL_pred h] at hNl
    have hd : 2 * (dcnt n p : ℤ) = p + NL n p lc - 2 := by
      have : 2 * (dcnt n p : ℤ) + ((p : ℤ) - NL n p lc) + 2 = 2 * p := by rw [← hNl]; linarith
      linarith
    have e0 := HL_pred lc 0
    have e2 := HL_pred lc 2
    have e3 := HL_pred lc 3
    have e5 := HL_pred lc 5
    rw [h2]
    unfold NL at *
    by_cases hp : lc % 2 = 0
    · simp only [hp, if_true] at e0 e2 e3 e5 hd ⊢
      have n0 : ((lc - 0) % 2 = 0) := by omega
      have n2 : ((lc - 2) % 2 = 0) := by omega
      have n3 : ¬ ((lc - 3) % 2 = 0) := by omega
      have n5 : ¬ ((lc - 5) % 2 = 0) := by omega
      simp only [n0, n2, n3, n5, if_true, if_false] at e0 e2 e3 e5
      rw [e0, e2, e3, e5]
      linear_combination (lc - 1) * hd
    · simp only [hp, if_false] at e0 e2 e3 e5 hd ⊢
      have n0 : ¬ ((lc - 0) % 2 = 0) := by omega
      have n2 : ¬ ((lc - 2) % 2 = 0) := by omega
      have n3 : ((lc - 3) % 2 = 0) := by omega
      have n5 : ((lc - 5) % 2 = 0) := by omega
      simp only [n0, n2, n3, n5, if_true, if_false] at e0 e2 e3 e5
      rw [e0, e2, e3, e5]
      linear_combination (lc - 1) * hd

end TCl

section RealPart

variable {n p : ℕ}

theorem rel_b (h : Rng n p) :
    3 * n / p = q6 n p / 2 ∧ 2 * (3 * n % p) = (q6 n p % 2) * p + r6 n p := by
  have hp := h.p5
  have a6 := qr6 n p (by omega)
  have b6 := r6_lt n p (by omega)
  have a3 := Nat.div_add_mod (3 * n) p
  have b3 := Nat.mod_lt (3 * n) (by omega : 0 < p)
  generalize 3 * n / p = q3 at a3 ⊢
  generalize 3 * n % p = r3 at a3 b3 ⊢
  have a6' : (6 * n : ℤ) = (q6 n p : ℤ) * p + r6 n p := by exact_mod_cast a6
  have a3' : (3 * n : ℤ) = p * (q3 : ℤ) + (r3 : ℤ) := by exact_mod_cast a3.symm
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (by omega : 0 < p)
  have b6' : (r6 n p : ℤ) < p := by exact_mod_cast b6
  have b3' : (r3 : ℤ) < p := by exact_mod_cast b3
  have r6n : (0 : ℤ) ≤ (r6 n p : ℤ) := Nat.cast_nonneg _
  have r3n : (0 : ℤ) ≤ (r3 : ℤ) := Nat.cast_nonneg _
  have key : ((q6 n p : ℤ) - 2 * (q3 : ℤ)) * p = 2 * (r3 : ℤ) - r6 n p := by nlinarith
  have hlo : (0 : ℤ) ≤ (q6 n p : ℤ) - 2 * (q3 : ℤ) := by
    by_contra hc
    push_neg at hc
    have h1 : (q6 n p : ℤ) - 2 * (q3 : ℤ) ≤ -1 := by omega
    nlinarith
  have hhi : (q6 n p : ℤ) - 2 * (q3 : ℤ) ≤ 1 := by
    by_contra hc
    push_neg at hc
    have h1 : 2 ≤ (q6 n p : ℤ) - 2 * (q3 : ℤ) := by omega
    nlinarith
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (q6 n p : ℤ) = 2 * (q3 : ℤ) + b :=
    ⟨((q6 n p : ℤ) - 2 * (q3 : ℤ)).toNat, by omega⟩
  have hb1 : b ≤ 1 := by omega
  have hq2 : q6 n p % 2 = b := by omega
  refine ⟨by omega, ?_⟩
  rw [hq2]
  have : (b : ℤ) * p = 2 * (r3 : ℤ) - r6 n p := by rw [hb] at key; nlinarith
  have h2 : (2 * r3 : ℤ) = (b : ℤ) * p + r6 n p := by linarith
  exact_mod_cast h2

/-- `ν_p = 9n²/p - 3n + p θ (1 - θ)`, `θ = ((q₆ mod 2) + r₆/p)/2`. -/
theorem nuP_real [hp : Fact p.Prime] (h : Rng n p) :
    (nuP n p : ℝ) = 9 * (n : ℝ) ^ 2 / p - 3 * n +
      p * ((((q6 n p % 2 : ℕ) : ℝ) + (r6 n p : ℝ) / p) / 2) *
        (1 - (((q6 n p % 2 : ℕ) : ℝ) + (r6 n p : ℝ) / p) / 2) := by
  have hc := nuP_closed (hp := hp) h.h8
  obtain ⟨e1, e2⟩ := rel_b h
  have hP : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have a3 := Nat.div_add_mod (3 * n) p
  generalize 3 * n / p = q3 at hc a3 e1
  generalize 3 * n % p = r3 at hc a3 e2
  have hc' : (nuP n p : ℝ) = (p : ℝ) * (q3 : ℝ) * ((q3 : ℝ) - 1) + 2 * (q3 : ℝ) * (r3 : ℝ) := by
    have := congrArg (Int.cast : ℤ → ℝ) hc
    push_cast at this
    linarith
  have a3' : (3 * n : ℝ) = p * (q3 : ℝ) + (r3 : ℝ) := by exact_mod_cast a3.symm
  have e2' : 2 * (r3 : ℝ) = ((q6 n p % 2 : ℕ) : ℝ) * p + (r6 n p : ℝ) := by exact_mod_cast e2
  have hθ : ((((q6 n p % 2 : ℕ) : ℝ) + (r6 n p : ℝ) / p) / 2) = (r3 : ℝ) / p := by
    field_simp
    linarith
  rw [hθ, hc']
  have hn : (n : ℝ) = (p * (q3 : ℝ) + (r3 : ℝ)) / 3 := by linarith
  rw [hn]
  field_simp
  ring

theorem muL_real (l σ : ℤ) :
    ((muL l σ : ℤ) : ℝ) = ((l : ℝ) + 4 + (if (l - σ) % 2 = 0 then 0 else 1) - σ) / 2 := by
  have : 2 * muL l σ = l + 4 + (if (l - σ) % 2 = 0 then 0 else 1) - σ := by
    unfold muL; split_ifs <;> omega
  have h2 : (2 : ℝ) * (muL l σ : ℝ) = (l : ℝ) + 4 + (if (l - σ) % 2 = 0 then 0 else 1) - σ := by
    have := congrArg (Int.cast : ℤ → ℝ) this
    push_cast at this
    split_ifs at this ⊢ <;> linarith
  linarith

end RealPart

section Mass

theorem cond_iff {P R R2 ρ : ℕ} (hP : 0 < P) (h3 : 3 * R2 = ρ * P + R) :
    ((R : ℝ) / P < (3 - (ρ : ℝ)) / 4) ↔ ((R : ℤ) < (P : ℤ) - R2) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have h3' : (3 : ℝ) * R2 = ρ * P + R := by exact_mod_cast h3
  rw [div_lt_iff₀ hP0]
  constructor
  · intro h
    have : (R : ℝ) < P - R2 := by nlinarith
    exact_mod_cast this
  · intro h
    have : (R : ℝ) < P - R2 := by exact_mod_cast h
    nlinarith

theorem mass_A {P R R2 ρ : ℕ} (hP : 0 < P) (h3 : 3 * R2 = ρ * P + R) :
    (P : ℝ) * (if (R : ℝ) / P < (3 - (ρ : ℝ)) / 4 then (R : ℝ) / P
      else 1 - ((ρ : ℝ) + (R : ℝ) / P) / 3) = ((min (R : ℤ) ((P : ℤ) - R2) : ℤ) : ℝ) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have h3' : (3 : ℝ) * R2 = ρ * P + R := by exact_mod_cast h3
  have hPR : (P : ℝ) * ((R : ℝ) / P) = R := by field_simp
  by_cases hc : (R : ℝ) / P < (3 - (ρ : ℝ)) / 4
  · have hc' := (cond_iff hP h3).1 hc
    rw [if_pos hc, min_eq_left hc'.le, hPR]; push_cast; rfl
  · have hc' : ¬ ((R : ℤ) < P - R2) := fun h => hc ((cond_iff hP h3).2 h)
    rw [if_neg hc, min_eq_right (not_lt.1 hc')]
    push_cast
    have : (P : ℝ) * (1 - ((ρ : ℝ) + (R : ℝ) / P) / 3) = P - R2 := by
      field_simp; nlinarith
    exact this

theorem mass_B {P R R2 ρ : ℕ} (hP : 0 < P) (h3 : 3 * R2 = ρ * P + R) :
    (P : ℝ) * (if (R : ℝ) / P < (3 - (ρ : ℝ)) / 4 then 0
      else (R : ℝ) / P - (1 - ((ρ : ℝ) + (R : ℝ) / P) / 3)) =
      ((max 0 ((R : ℤ) - ((P : ℤ) - R2)) : ℤ) : ℝ) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have h3' : (3 : ℝ) * R2 = ρ * P + R := by exact_mod_cast h3
  by_cases hc : (R : ℝ) / P < (3 - (ρ : ℝ)) / 4
  · have hc' := (cond_iff hP h3).1 hc
    rw [if_pos hc, max_eq_left (by omega)]; simp
  · have hc' : ¬ ((R : ℤ) < P - R2) := fun h => hc ((cond_iff hP h3).2 h)
    rw [if_neg hc, max_eq_right (by omega)]
    push_cast
    field_simp
    nlinarith

theorem mass_C {P R R2 ρ : ℕ} (hP : 0 < P) (h3 : 3 * R2 = ρ * P + R) :
    (P : ℝ) * (if (R : ℝ) / P < (3 - (ρ : ℝ)) / 4 then
        (1 - ((ρ : ℝ) + (R : ℝ) / P) / 3) - (R : ℝ) / P else 0) =
      ((max 0 (((P : ℤ) - R2) - (R : ℤ)) : ℤ) : ℝ) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have h3' : (3 : ℝ) * R2 = ρ * P + R := by exact_mod_cast h3
  by_cases hc : (R : ℝ) / P < (3 - (ρ : ℝ)) / 4
  · have hc' := (cond_iff hP h3).1 hc
    rw [if_pos hc, max_eq_right (by omega)]
    push_cast
    field_simp
    nlinarith
  · have hc' : ¬ ((R : ℤ) < P - R2) := fun h => hc ((cond_iff hP h3).2 h)
    rw [if_neg hc, max_eq_left (by omega)]; simp

theorem mass_D {P R R2 ρ : ℕ} (hP : 0 < P) (h3 : 3 * R2 = ρ * P + R) :
    (P : ℝ) * (if (R : ℝ) / P < (3 - (ρ : ℝ)) / 4 then ((ρ : ℝ) + (R : ℝ) / P) / 3
      else 1 - (R : ℝ) / P) = (((P : ℤ) - max (R : ℤ) ((P : ℤ) - R2) : ℤ) : ℝ) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have h3' : (3 : ℝ) * R2 = ρ * P + R := by exact_mod_cast h3
  by_cases hc : (R : ℝ) / P < (3 - (ρ : ℝ)) / 4
  · have hc' := (cond_iff hP h3).1 hc
    rw [if_pos hc, max_eq_right hc'.le]
    push_cast
    field_simp
    nlinarith
  · have hc' : ¬ ((R : ℤ) < P - R2) := fun h => hc ((cond_iff hP h3).2 h)
    rw [if_neg hc, max_eq_left (by omega)]
    push_cast
    field_simp

end Mass

section Scaled2

/-- the scaled class counts (`p` times the masses of `c01Num`). -/
def cA (P R R2 : ℤ) : ℤ := min R (P - R2)
def cB (P R R2 : ℤ) : ℤ := max 0 (R - (P - R2))
def cC (P R R2 : ℤ) : ℤ := max 0 ((P - R2) - R)
def cD (P R R2 : ℤ) : ℤ := P - max R (P - R2)
def cNN (P R R2 lc : ℤ) : ℤ :=
  if lc % 2 = 0 then cB P R R2 + cD P R R2 else cA P R R2 + cC P R R2
def cDif (P R R2 lc : ℤ) : ℤ :=
  if lc % 2 = 0 then cA P R R2 - cC P R R2 else cB P R R2 - cD P R R2
/-- twice `p · c01Num` plus twice `ν`, as an integer. -/
def cNum (P R R2 lc : ℤ) : ℤ :=
  2 * (cA P R R2 * HL lc 0 + cB P R R2 * HL lc 3 + cC P R R2 * HL lc 2 + cD P R R2 * HL lc 5) +
    (P - cNN P R R2 lc) * lc + |cDif P R R2 lc| + max (|cDif P R R2 lc| - 2 * cNN P R R2 lc) 0

theorem abs_div_scale {P : ℝ} (hP : 0 < P) (a c : ℝ) : |a / P - c / P| = |a - c| / P := by
  rw [← sub_div, abs_div, abs_of_pos hP]

theorem max_div_scale {P : ℝ} (hP : 0 < P) (u b : ℝ) :
    max (u / P / 2 - b / P) 0 = max (u - 2 * b) 0 / (2 * P) := by
  have h2 : u / P / 2 - b / P = (u - 2 * b) / (2 * P) := by field_simp
  have h3 : max (u - 2 * b) 0 / (2 * P) = max ((u - 2 * b) / (2 * P)) (0 / (2 * P)) :=
    (max_div_div_right (by positivity : (0 : ℝ) ≤ 2 * P) (u - 2 * b) 0).symm
  rw [h2, h3, zero_div]

theorem HL_real (l σ : ℤ) :
    ((HL l σ : ℤ) : ℝ) = (((l : ℝ) + 4 + (if (l - σ) % 2 = 0 then 0 else 1) - σ) / 2) ^ 2 +
      ((σ : ℝ) - 5) * (((l : ℝ) + 4 + (if (l - σ) % 2 = 0 then 0 else 1) - σ) / 2) := by
  unfold HL
  push_cast
  rw [muL_real]
  ring

theorem cNum_even (P R R2 lc : ℤ) (hp : lc % 2 = 0) :
    ((cNum P R R2 lc : ℤ) : ℝ) =
      2 * (((cA P R R2 : ℤ) : ℝ) * ((((lc : ℝ) + 4 + 0 - 0) / 2) ^ 2 + ((0 : ℝ) - 5) * (((lc : ℝ) + 4 + 0 - 0) / 2)) +
           ((cB P R R2 : ℤ) : ℝ) * ((((lc : ℝ) + 4 + 1 - 3) / 2) ^ 2 + ((3 : ℝ) - 5) * (((lc : ℝ) + 4 + 1 - 3) / 2)) +
           ((cC P R R2 : ℤ) : ℝ) * ((((lc : ℝ) + 4 + 0 - 2) / 2) ^ 2 + ((2 : ℝ) - 5) * (((lc : ℝ) + 4 + 0 - 2) / 2)) +
           ((cD P R R2 : ℤ) : ℝ) * ((((lc : ℝ) + 4 + 1 - 5) / 2) ^ 2 + ((5 : ℝ) - 5) * (((lc : ℝ) + 4 + 1 - 5) / 2))) +
      ((P : ℝ) - (((cB P R R2 : ℤ) : ℝ) + ((cD P R R2 : ℤ) : ℝ))) * lc +
      |((cA P R R2 : ℤ) : ℝ) - ((cC P R R2 : ℤ) : ℝ)| +
      max (|((cA P R R2 : ℤ) : ℝ) - ((cC P R R2 : ℤ) : ℝ)| -
        2 * (((cB P R R2 : ℤ) : ℝ) + ((cD P R R2 : ℤ) : ℝ))) 0 := by
  have e0 : (lc - 0) % 2 = 0 := by omega
  have e2 : (lc - 2) % 2 = 0 := by omega
  have e3 : ¬ ((lc - 3) % 2 = 0) := by omega
  have e5 : ¬ ((lc - 5) % 2 = 0) := by omega
  unfold cNum cNN cDif
  simp only [hp, if_true]
  push_cast
  rw [HL_real lc 0, HL_real lc 3, HL_real lc 2, HL_real lc 5]
  simp only [e0, e2, e3, e5, if_true, if_false]
  push_cast
  ring

theorem cNum_odd (P R R2 lc : ℤ) (hp : ¬ (lc % 2 = 0)) :
    ((cNum P R R2 lc : ℤ) : ℝ) =
      2 * (((cA P R R2 : ℤ) : ℝ) * ((((lc : ℝ) + 4 + 1 - 0) / 2) ^ 2 + ((0 : ℝ) - 5) * (((lc : ℝ) + 4 + 1 - 0) / 2)) +
           ((cB P R R2 : ℤ) : ℝ) * ((((lc : ℝ) + 4 + 0 - 3) / 2) ^ 2 + ((3 : ℝ) - 5) * (((lc : ℝ) + 4 + 0 - 3) / 2)) +
           ((cC P R R2 : ℤ) : ℝ) * ((((lc : ℝ) + 4 + 1 - 2) / 2) ^ 2 + ((2 : ℝ) - 5) * (((lc : ℝ) + 4 + 1 - 2) / 2)) +
           ((cD P R R2 : ℤ) : ℝ) * ((((lc : ℝ) + 4 + 0 - 5) / 2) ^ 2 + ((5 : ℝ) - 5) * (((lc : ℝ) + 4 + 0 - 5) / 2))) +
      ((P : ℝ) - (((cA P R R2 : ℤ) : ℝ) + ((cC P R R2 : ℤ) : ℝ))) * lc +
      |((cB P R R2 : ℤ) : ℝ) - ((cD P R R2 : ℤ) : ℝ)| +
      max (|((cB P R R2 : ℤ) : ℝ) - ((cD P R R2 : ℤ) : ℝ)| -
        2 * (((cA P R R2 : ℤ) : ℝ) + ((cC P R R2 : ℤ) : ℝ))) 0 := by
  have e0 : ¬ ((lc - 0) % 2 = 0) := by omega
  have e2 : ¬ ((lc - 2) % 2 = 0) := by omega
  have e3 : (lc - 3) % 2 = 0 := by omega
  have e5 : (lc - 5) % 2 = 0 := by omega
  unfold cNum cNN cDif
  simp only [hp, if_false]
  push_cast
  rw [HL_real lc 0, HL_real lc 3, HL_real lc 2, HL_real lc 5]
  simp only [e0, e2, e3, e5, if_true, if_false]
  push_cast
  ring

theorem scaled_Num {Q P R R2 : ℕ} (hP : 0 < P) (hR : R < P) (hR2 : R2 < P)
    (h3 : 3 * R2 = (Q % 3) * P + R) :
    2 * ((P : ℝ) * c01Num (Q % 6) (Q : ℝ) ((R : ℝ) / P)) =
      ((cNum P R R2 ((Q : ℤ) + ((Q % 3 : ℕ) : ℤ) - 3) : ℤ) : ℝ) -
        2 * (9 * (((Q : ℝ) * P + R) / 6) ^ 2 / P - 3 * (((Q : ℝ) * P + R) / 6) +
          P * ((((Q % 2 : ℕ) : ℝ) + (R : ℝ) / P) / 2) *
            (1 - (((Q % 2 : ℕ) : ℝ) + (R : ℝ) / P) / 2)) := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  generalize hρ : Q % 3 = ρ at h3 ⊢
  have hr3 : (Q % 6) % 3 = ρ := by omega
  have hr2 : (Q % 6) % 2 = Q % 2 := by omega
  have eA : (if (R : ℝ) / P < (3 - (ρ : ℝ)) / 4 then (R : ℝ) / P
      else 1 - ((ρ : ℝ) + (R : ℝ) / P) / 3) = ((cA P R R2 : ℤ) : ℝ) / P := by
    rw [eq_div_iff hP0.ne', mul_comm]; exact mass_A hP h3
  have eB : (if (R : ℝ) / P < (3 - (ρ : ℝ)) / 4 then 0
      else (R : ℝ) / P - (1 - ((ρ : ℝ) + (R : ℝ) / P) / 3)) = ((cB P R R2 : ℤ) : ℝ) / P := by
    rw [eq_div_iff hP0.ne', mul_comm]; exact mass_B hP h3
  have eC : (if (R : ℝ) / P < (3 - (ρ : ℝ)) / 4 then
      (1 - ((ρ : ℝ) + (R : ℝ) / P) / 3) - (R : ℝ) / P else 0) = ((cC P R R2 : ℤ) : ℝ) / P := by
    rw [eq_div_iff hP0.ne', mul_comm]; exact mass_C hP h3
  have eD : (if (R : ℝ) / P < (3 - (ρ : ℝ)) / 4 then ((ρ : ℝ) + (R : ℝ) / P) / 3
      else 1 - (R : ℝ) / P) = ((cD P R R2 : ℤ) : ℝ) / P := by
    rw [eq_div_iff hP0.ne', mul_comm]; exact mass_D hP h3
  unfold c01Num
  simp only [hr3, hr2, eA, eB, eC, eD]
  by_cases hpar : ((Q : ℤ) + (ρ : ℤ) - 3) % 2 = 0
  · have hc : (Q % 6 + ρ) % 2 = 1 := by omega
    rw [cNum_even _ _ _ _ hpar]
    simp only [hc, if_true]
    generalize hAA : ((cA P R R2 : ℤ) : ℝ) = A
    generalize hBB : ((cB P R R2 : ℤ) : ℝ) = B
    generalize hCC : ((cC P R R2 : ℤ) : ℝ) = C
    generalize hDD : ((cD P R R2 : ℤ) : ℝ) = D
    rw [abs_div_scale hP0]
    have hbd : B / P + D / P = (B + D) / P := (add_div _ _ _).symm
    simp only [sub_zero, zero_mul, add_zero, zero_add, one_mul]
    rw [hbd, max_div_scale hP0]
    push_cast
    field_simp
    ring
  · have hc : ¬ ((Q % 6 + ρ) % 2 = 1) := by omega
    rw [cNum_odd _ _ _ _ hpar]
    simp only [hc, if_false]
    generalize hAA : ((cA P R R2 : ℤ) : ℝ) = A
    generalize hBB : ((cB P R R2 : ℤ) : ℝ) = B
    generalize hCC : ((cC P R R2 : ℤ) : ℝ) = C
    generalize hDD : ((cD P R R2 : ℤ) : ℝ) = D
    rw [abs_div_scale hP0]
    have hac : A / P + C / P = (A + C) / P := (add_div _ _ _).symm
    simp only [sub_zero, zero_mul, add_zero, zero_add, one_mul, sub_self]
    rw [hac, max_div_scale hP0]
    push_cast
    field_simp
    ring

end Scaled2

section Ineq

variable {n p : ℕ}

theorem HL_bound {lc Q σ : ℤ} (hQ : 2 ≤ Q) (hl0 : 0 ≤ lc) (hlQ : lc + 1 ≤ Q) (hσ0 : 0 ≤ σ) (hσ5 : σ ≤ 5) :
    |HL lc σ| ≤ 12 * Q ^ 2 := by
  have h2 : 2 * muL lc σ = lc + 4 + (if (lc - σ) % 2 = 0 then 0 else 1) - σ := by
    unfold muL; split_ifs <;> omega
  have hm0 : 0 ≤ muL lc σ := by split_ifs at h2 <;> omega
  have hm1 : muL lc σ ≤ Q + 2 := by split_ifs at h2 <;> omega
  unfold HL
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hm0 hm0]

theorem mul_lb {δ h B : ℤ} (hδ : |δ| ≤ 1) (hh : |h| ≤ B) : -B ≤ δ * h := by
  have h1 : |δ * h| ≤ B := by
    rw [abs_mul]
    calc |δ| * |h| ≤ 1 * |h| := mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
      _ ≤ B := by linarith
  exact (abs_le.1 h1).1

/-- abstract `x`-part, `k = 1`. -/
theorem x_k1 (X Y N d cX cY cN p : ℤ) (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hcX : |X - cX| ≤ 1)
    (hcY : |Y - cY| ≤ 1) (hcN : |N - cN| ≤ 1) (hs : X + Y + N = p) (hcs : cX + cY + cN = p)
    (hT : 2 * d + N + 2 = p) :
    |cX - cY| + max (|cX - cY| - 2 * cN) 0 - 10 ≤
      2 * (max 0 (min (d - min X Y) (max X Y - d)) +
        max 0 (max 0 (min (d - min X Y) (max X Y - d)) - N)) := by
  rw [abs_le] at hcX hcY hcN
  simp only [abs_eq_max_neg]
  omega

/-- abstract `x`-part, `k = 2`. -/
theorem x_k2 (X Y N d cX cY cN p : ℤ) (hcX0 : 0 ≤ cX) (hcY0 : 0 ≤ cY) (hcN0 : 0 ≤ cN)
    (hdN : d + N ≤ p) (hT : 2 * d + N + 2 = 2 * p)
    (hc : |cX + cY - N| ≤ 2) :
    |cX - cY| + max (|cX - cY| - 2 * cN) 0 - 10 ≤
      2 * (max 0 (min (d - min X Y) (max X Y - d)) +
        max 0 (max 0 (min (d - min X Y) (max X Y - d)) - N)) := by
  rw [abs_le] at hc
  have hN2 : N ≤ 2 := by omega
  simp only [abs_eq_max_neg]
  omega

theorem x_part (h : Rng n p) :
    |cDif p (r6 n p) (r2 n p) ((q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3)| +
        max (|cDif p (r6 n p) (r2 n p) ((q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3)| -
          2 * cNN p (r6 n p) (r2 n p) ((q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3)) 0 - 10 ≤
      2 * (xone n p + xtwo n p) := by
  obtain ⟨hk1, hk2⟩ := kk_range h
  have hz := sz_int h
  have hT := lemmaT h
  have hN := Ncnt_eq h
  have hdN := d_add_N_le h
  have hs := sz_sum h
  have hp := h.p5
  have b6 := r6_lt n p (by omega)
  have b2 := r2_lt n p (by omega)
  have hlam0 := (lemmaS h).1
  have hq := h.q6_ge
  have ha := (rel_a h).1
  have hρ : (q6 n p : ℤ) = 3 * (q2 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) := by omega
  generalize hρ' : (q6 n p % 3 : ℕ) = ρ at *
  have hxt : xtwo n p = max 0 (xone n p - Ncnt n p) := rfl
  have hxe : lam n p % 2 = 0 → xone n p =
      max 0 (min ((dcnt n p : ℤ) - min (szA n p : ℤ) (szC n p : ℤ))
        (max (szA n p : ℤ) (szC n p : ℤ) - dcnt n p)) := by
    intro hpar; unfold xone tieZ tieW; simp only [hpar, if_true]; push_cast; rfl
  have hxo : ¬ (lam n p % 2 = 0) → xone n p =
      max 0 (min ((dcnt n p : ℤ) - min (szB n p : ℤ) (szD n p : ℤ))
        (max (szB n p : ℤ) (szD n p : ℤ) - dcnt n p)) := by
    intro hpar; unfold xone tieZ tieW; simp only [hpar, if_false]; push_cast; rfl
  have hNe : lam n p % 2 = 0 → (Ncnt n p : ℤ) = (szB n p : ℤ) + szD n p := by
    intro hpar; rw [hN, if_pos hpar]; push_cast; rfl
  have hNo : ¬ (lam n p % 2 = 0) → (Ncnt n p : ℤ) = (szA n p : ℤ) + szC n p := by
    intro hpar; rw [hN, if_neg hpar]; push_cast; rfl
  have hsz : (szA n p : ℤ) + szB n p + szC n p + szD n p = p := by exact_mod_cast hs
  have hdN' : (dcnt n p : ℤ) + Ncnt n p ≤ p := hdN
  have hb6 : (r6 n p : ℤ) < p := by exact_mod_cast b6
  have hb2 : (r2 n p : ℤ) < p := by exact_mod_cast b2
  have hr6 : (0 : ℤ) ≤ r6 n p := Nat.cast_nonneg _
  have hr2 : (0 : ℤ) ≤ r2 n p := Nat.cast_nonneg _
  have hdiffA : |(szA n p : ℤ) - cA p (r6 n p) (r2 n p)| ≤ 1 := by
    obtain ⟨e1, e2, e3, e4⟩ := hz; unfold cA; rw [abs_le]; omega
  have hdiffB : |(szB n p : ℤ) - cB p (r6 n p) (r2 n p)| ≤ 1 := by
    obtain ⟨e1, e2, e3, e4⟩ := hz; unfold cB; rw [abs_le]; omega
  have hdiffC : |(szC n p : ℤ) - cC p (r6 n p) (r2 n p)| ≤ 1 := by
    obtain ⟨e1, e2, e3, e4⟩ := hz; unfold cC; rw [abs_le]; omega
  have hdiffD : |(szD n p : ℤ) - cD p (r6 n p) (r2 n p)| ≤ 1 := by
    obtain ⟨e1, e2, e3, e4⟩ := hz; unfold cD; rw [abs_le]; omega
  have hcA0 : 0 ≤ cA p (r6 n p) (r2 n p) := by unfold cA; omega
  have hcB0 : 0 ≤ cB p (r6 n p) (r2 n p) := by unfold cB; omega
  have hcC0 : 0 ≤ cC p (r6 n p) (r2 n p) := by unfold cC; omega
  have hcD0 : 0 ≤ cD p (r6 n p) (r2 n p) := by unfold cD; omega
  have hcsum : cA p (r6 n p) (r2 n p) + cB p (r6 n p) (r2 n p) + cC p (r6 n p) (r2 n p) +
      cD p (r6 n p) (r2 n p) = p := by unfold cA cB cC cD; omega
  have hNBD : |((szB n p : ℤ) + szD n p) - (cB p (r6 n p) (r2 n p) + cD p (r6 n p) (r2 n p))| ≤ 1 := by
    obtain ⟨e1, e2, e3, e4⟩ := hz; unfold cB cD; rw [abs_le]; omega
  have hNAC : |((szA n p : ℤ) + szC n p) - (cA p (r6 n p) (r2 n p) + cC p (r6 n p) (r2 n p))| ≤ 1 := by
    obtain ⟨e1, e2, e3, e4⟩ := hz; unfold cA cC; rw [abs_le]; omega
  have hlamk : lam n p = (q6 n p : ℤ) + ρ - 2 - (2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 2 - lam n p) := by omega
  set k : ℤ := 2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 2 - lam n p with hk
  have hk' : k = 1 ∨ k = 2 := by omega
  rw [hxt]
  rcases hk' with h1 | h2
  · have hT' : 2 * (dcnt n p : ℤ) + Ncnt n p + 2 = p := by rw [h1] at hT; linarith
    have hlam : lam n p = (q6 n p : ℤ) + ρ - 3 := by omega
    by_cases hpar : lam n p % 2 = 0
    · have hlc : ((q6 n p : ℤ) + ρ - 3) % 2 = 0 := by omega
      simp only [cDif, cNN, hlc, if_true]
      rw [hxe hpar]
      try rw [hNe hpar]
      have := x_k1 (szA n p) (szC n p) ((szB n p : ℤ) + szD n p) (dcnt n p)
        (cA p (r6 n p) (r2 n p)) (cC p (r6 n p) (r2 n p))
        (cB p (r6 n p) (r2 n p) + cD p (r6 n p) (r2 n p)) p (by positivity) (by positivity)
        hdiffA hdiffC hNBD (by linarith [hsz, hNe hpar]) (by linarith [hcsum]) (by rw [← hNe hpar]; exact hT')
      try rw [hNe hpar] at this
      exact this
    · have hlc : ¬ (((q6 n p : ℤ) + ρ - 3) % 2 = 0) := by omega
      simp only [cDif, cNN, hlc, if_false]
      rw [hxo hpar]
      try rw [hNo hpar]
      have := x_k1 (szB n p) (szD n p) ((szA n p : ℤ) + szC n p) (dcnt n p)
        (cB p (r6 n p) (r2 n p)) (cD p (r6 n p) (r2 n p))
        (cA p (r6 n p) (r2 n p) + cC p (r6 n p) (r2 n p)) p (by positivity) (by positivity)
        hdiffB hdiffD hNAC (by linarith [hsz, hNo hpar]) (by linarith [hcsum]) (by rw [← hNo hpar]; exact hT')
      try rw [hNo hpar] at this
      exact this
  · have hT' : 2 * (dcnt n p : ℤ) + Ncnt n p + 2 = 2 * p := by rw [h2] at hT; linarith
    by_cases hpar : lam n p % 2 = 0
    · have hlc : ¬ (((q6 n p : ℤ) + ρ - 3) % 2 = 0) := by omega
      simp only [cDif, cNN, hlc, if_false]
      rw [hxe hpar]
      try rw [hNe hpar]
      have := x_k2 (szA n p) (szC n p) ((szB n p : ℤ) + szD n p) (dcnt n p)
        (cB p (r6 n p) (r2 n p)) (cD p (r6 n p) (r2 n p))
        (cA p (r6 n p) (r2 n p) + cC p (r6 n p) (r2 n p)) p hcB0 hcD0 (add_nonneg hcA0 hcC0)
        (by rw [← hNe hpar]; exact hdN') (by rw [← hNe hpar]; exact hT')
        (by rw [abs_sub_comm]; exact le_trans hNBD (by norm_num))
      try rw [hNe hpar] at this
      exact this
    · have hlc : ((q6 n p : ℤ) + ρ - 3) % 2 = 0 := by omega
      simp only [cDif, cNN, hlc, if_true]
      rw [hxo hpar]
      try rw [hNo hpar]
      have := x_k2 (szB n p) (szD n p) ((szA n p : ℤ) + szC n p) (dcnt n p)
        (cA p (r6 n p) (r2 n p)) (cC p (r6 n p) (r2 n p))
        (cB p (r6 n p) (r2 n p) + cD p (r6 n p) (r2 n p)) p hcA0 hcC0 (add_nonneg hcB0 hcD0)
        (by rw [← hNo hpar]; exact hdN') (by rw [← hNo hpar]; exact hT')
        (by rw [abs_sub_comm]; exact le_trans hNAC (by norm_num))
      try rw [hNo hpar] at this
      exact this

end Ineq

section WGe

variable {n p : ℕ}

set_option maxHeartbeats 1600000 in
/-- **The integer comparison**: `cNum - 2ν - 214 q² ≤ 2 W`. -/
theorem W_ge (h : Rng n p) :
    cNum p (r6 n p) (r2 n p) ((q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3) - 2 * (nuP n p : ℤ) -
        214 * (q6 n p : ℤ) ^ 2 ≤ 2 * Wlaw n p := by
  have e := two_T h
  have hx := x_part h
  obtain ⟨hk1, hk2⟩ := kk_range h
  have hz := sz_int h
  have hT := lemmaT h
  have hN := Ncnt_eq h
  have hdN := d_add_N_le h
  have hs := sz_sum h
  have hp := h.p5
  have b6 := r6_lt n p (by omega)
  have b2 := r2_lt n p (by omega)
  have hlam0 := (lemmaS h).1
  have hq := h.q6_ge
  have ha := (rel_a h).1
  have hρ : (q6 n p : ℤ) = 3 * (q2 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) := by omega
  have hQ : (2 : ℤ) ≤ (q6 n p : ℤ) := by exact_mod_cast hq
  have hlc0 : (0 : ℤ) ≤ (q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3 := by omega
  have hlcQ : (q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3 + 1 ≤ (q6 n p : ℤ) := by omega
  have hb6 : (r6 n p : ℤ) < p := by exact_mod_cast b6
  have hb2 : (r2 n p : ℤ) < p := by exact_mod_cast b2
  have hr6 : (0 : ℤ) ≤ r6 n p := Nat.cast_nonneg _
  have hr2 : (0 : ℤ) ≤ r2 n p := Nat.cast_nonneg _
  have hdiffA : |(szA n p : ℤ) - cA p (r6 n p) (r2 n p)| ≤ 1 := by
    obtain ⟨e1, e2, e3, e4⟩ := hz; unfold cA; rw [abs_le]; omega
  have hdiffB : |(szB n p : ℤ) - cB p (r6 n p) (r2 n p)| ≤ 1 := by
    obtain ⟨e1, e2, e3, e4⟩ := hz; unfold cB; rw [abs_le]; omega
  have hdiffC : |(szC n p : ℤ) - cC p (r6 n p) (r2 n p)| ≤ 1 := by
    obtain ⟨e1, e2, e3, e4⟩ := hz; unfold cC; rw [abs_le]; omega
  have hdiffD : |(szD n p : ℤ) - cD p (r6 n p) (r2 n p)| ≤ 1 := by
    obtain ⟨e1, e2, e3, e4⟩ := hz; unfold cD; rw [abs_le]; omega
  have hHL0 := HL_bound (σ := 0) hQ hlc0 hlcQ (by norm_num) (by norm_num)
  have hHL3 := HL_bound (σ := 3) hQ hlc0 hlcQ (by norm_num) (by norm_num)
  have hHL2 := HL_bound (σ := 2) hQ hlc0 hlcQ (by norm_num) (by norm_num)
  have hHL5 := HL_bound (σ := 5) hQ hlc0 hlcQ (by norm_num) (by norm_num)
  have m0 := mul_lb hdiffA hHL0
  have m3 := mul_lb hdiffB hHL3
  have m2 := mul_lb hdiffC hHL2
  have m5 := mul_lb hdiffD hHL5
  -- cNN versus NL
  have hNL : |cNN p (r6 n p) (r2 n p) ((q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3) -
      NL n p ((q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3)| ≤ 1 := by
    obtain ⟨e1, e2, e3, e4⟩ := hz
    unfold cNN NL cA cB cC cD
    split_ifs <;> rw [abs_le] <;> omega
  rw [abs_le] at hNL
  have hlcnn : (-3) * ((q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3) ≤
      (cNN p (r6 n p) (r2 n p) ((q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3) -
        NL n p ((q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3) - 2) *
        ((q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3) := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ cNN p (r6 n p) (r2 n p) ((q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3) -
        NL n p ((q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3) + 1 by omega) hlc0]
  -- the `k` term
  have hkt : 0 ≤ -(((2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 2 - lam n p) - 1) *
      ((p : ℤ) - NL n p ((q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3) - 2)) := by
    rcases (show (2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 2 - lam n p) = 1 ∨
        (2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 2 - lam n p) = 2 by omega) with hk | hk
    · rw [hk]; simp
    · rw [hk]
      have hT' : 2 * (dcnt n p : ℤ) + Ncnt n p + 2 = 2 * p := by rw [hk] at hT; linarith
      have hNl : (Ncnt n p : ℤ) = NL n p (lam n p) := by
        rw [hN]; unfold NL; split_ifs <;> push_cast <;> rfl
      have hlam : lam n p = ((q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3) - 1 := by omega
      rw [hlam, NL_pred h] at hNl
      have hN2 : (Ncnt n p : ℤ) ≤ 2 := by omega
      nlinarith
  set lc : ℤ := (q6 n p : ℤ) + ((q6 n p % 3 : ℕ) : ℤ) - 3 with hlc
  set kk : ℤ := 2 * (q6 n p : ℤ) - 3 * (q2 n p : ℤ) - 2 - lam n p with hkk
  have hbr : ((p : ℤ) - NL n p lc - 2) * (lc - (kk - 1)) -
      ((p : ℤ) - cNN p (r6 n p) (r2 n p) lc) * lc =
      (cNN p (r6 n p) (r2 n p) lc - NL n p lc - 2) * lc - (kk - 1) * ((p : ℤ) - NL n p lc - 2) := by
    ring
  have hsum : -(48 * (q6 n p : ℤ) ^ 2) ≤
      ((szA n p : ℤ) * HL lc 0 + (szB n p : ℤ) * HL lc 3 + (szC n p : ℤ) * HL lc 2 +
          (szD n p : ℤ) * HL lc 5) -
        (cA p (r6 n p) (r2 n p) * HL lc 0 + cB p (r6 n p) (r2 n p) * HL lc 3 +
          cC p (r6 n p) (r2 n p) * HL lc 2 + cD p (r6 n p) (r2 n p) * HL lc 5) := by
    have := m0; have := m3; have := m2; have := m5
    nlinarith
  have hq2 : (4 : ℤ) ≤ (q6 n p : ℤ) ^ 2 := by nlinarith
  have hq3 : 2 * (q6 n p : ℤ) ≤ (q6 n p : ℤ) ^ 2 := by nlinarith
  unfold Wlaw cNum
  linarith [e, hx, hbr, hsum, hlcnn, hkt, hlcQ, hq3, hQ]

end WGe

section FinalBridge

theorem no_boundary {p a b R : ℕ} (hp : p.Prime) (h8 : 8 ≤ p) (hb : 0 < b) (hb7 : b ≤ 7) (ha : 0 < a)
    (hR : R < p) (h : b * R = a * p) : False := by
  have hd : p ∣ b * R := ⟨a, by rw [h]; ring⟩
  rcases (Nat.Prime.dvd_mul hp).1 hd with h1 | h1
  · have := Nat.le_of_dvd hb h1
    omega
  · have h0 := Nat.eq_zero_of_dvd_of_lt h1 hR
    subst h0
    have : a * p = 0 := by simpa using h.symm
    have hp0 := hp.pos
    rcases Nat.mul_eq_zero.1 this with h2 | h2 <;> omega

theorem lo_cases {j : ℕ} (hj : j < 22) :
    (c01Piece j).lo = 0 ∨ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ b ≤ 7 ∧ (c01Piece j).lo = (a : ℝ) / b := by
  interval_cases j
  · left; simp only [c01Piece]
  · right; exact ⟨3, 4, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · right; exact ⟨6, 7, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · left; simp only [c01Piece]
  · right; exact ⟨1, 2, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · right; exact ⟨5, 7, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · left; simp only [c01Piece]
  · right; exact ⟨1, 4, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · right; exact ⟨2, 5, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · right; exact ⟨4, 7, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · right; exact ⟨2, 3, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · left; simp only [c01Piece]
  · right; exact ⟨1, 3, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · right; exact ⟨3, 7, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · right; exact ⟨3, 5, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · right; exact ⟨3, 4, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · left; simp only [c01Piece]
  · right; exact ⟨2, 7, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · right; exact ⟨1, 2, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · left; simp only [c01Piece]
  · right; exact ⟨1, 7, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩
  · right; exact ⟨1, 4, by norm_num, by norm_num, by norm_num, by simp only [c01Piece]; norm_num⟩

theorem c01_at_zero {j : ℕ} (hj : j < 22) (h0 : (c01Piece j).lo = 0) (q : ℝ) :
    c01Num (c01Piece j).r q 0 =
      ((c01Piece j).a + (c01Piece j).b * q + q ^ 2 / 2) + ((c01Piece j).g - 3 * q) * ((q + 0) / 6) := by
  interval_cases j <;> simp only [c01Piece] at h0 ⊢ <;> (try norm_num at h0) <;>
    (simp only [c01Num, abs_eq_max_neg, max_def]; norm_num
     first | ring | (split_ifs <;> first | (exfalso; linarith) | ring))

theorem piece_closed {j : ℕ} (hj : j < 22) {p R : ℕ} (hp : p.Prime) (h8 : 8 ≤ p) (hR : R < p) (q : ℝ)
    (h1 : (c01Piece j).lo * (p : ℝ) ≤ R) (h2 : (R : ℝ) < (c01Piece j).hi * p) :
    c01Num (c01Piece j).r q ((R : ℝ) / p) =
      ((c01Piece j).a + (c01Piece j).b * q + q ^ 2 / 2) +
        ((c01Piece j).g - 3 * q) * ((q + (R : ℝ) / p) / 6) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  by_cases hlt : (c01Piece j).lo * (p : ℝ) < R
  · have h1' : (c01Piece j).lo < (R : ℝ) / p := by rwa [lt_div_iff₀ hp0]
    have h2' : (R : ℝ) / p < (c01Piece j).hi := by rwa [div_lt_iff₀ hp0]
    exact c01_piece_ident j hj q _ h1' h2'
  · have heq : (R : ℝ) = (c01Piece j).lo * p := le_antisymm (not_lt.1 hlt) h1
    rcases lo_cases hj with h0 | ⟨a, b, ha, hb, hb7, hlo⟩
    · have hR0 : (R : ℝ) = 0 := by rw [heq, h0]; ring
      have hR0' : R = 0 := by exact_mod_cast hR0
      subst hR0'
      have := c01_at_zero hj h0 q
      simpa using this
    · exfalso
      rw [hlo] at heq
      have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
      have : (b : ℝ) * R = a * p := by rw [heq]; field_simp
      exact no_boundary hp h8 hb hb7 ha hR (by exact_mod_cast this)

theorem bridge_proof : BridgeStmt := by
  intro n p j hpr hn h hj hres hl hu
  haveI : Fact p.Prime := ⟨hpr⟩
  have hp9 : 8 ≤ p := by
    have h8 := h.h8
    by_contra hc
    push_neg at hc
    have : p ^ 2 ≤ 49 := by nlinarith
    omega
  have hP : 0 < p := hpr.pos
  have hR := r6_lt n p hP
  have hR2 := r2_lt n p hP
  have h3 := (rel_a h).2
  have hs := scaled_Num hP hR hR2 h3
  have hν := nuP_real h
  have hW := W_ge h
  have hq6 := qr6 n p hP
  have hn6 : (n : ℝ) = ((q6 n p : ℝ) * p + r6 n p) / 6 := by
    have : (6 * n : ℝ) = (q6 n p : ℝ) * p + r6 n p := by exact_mod_cast hq6
    linarith
  have hP0 : (0 : ℝ) < p := by exact_mod_cast hP
  have hWr := (Int.cast_le (R := ℝ)).2 hW
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_ofNat] at hWr
  rw [hn6] at hν
  have hmain : 2 * ((p : ℝ) * c01Num (q6 n p % 6) (q6 n p : ℝ) ((r6 n p : ℝ) / p)) ≤
      2 * (Wlaw n p : ℝ) + 214 * (q6 n p : ℝ) ^ 2 := by
    rw [hs]
    linarith
  have hpc := piece_closed hj hpr hp9 hR (q6 n p : ℝ) hl hu
  rw [hres, hpc] at hmain
  have hexp : (p : ℝ) * (((c01Piece j).a + (c01Piece j).b * (q6 n p : ℝ) + (q6 n p : ℝ) ^ 2 / 2) +
      ((c01Piece j).g - 3 * (q6 n p : ℝ)) * (((q6 n p : ℝ) + (r6 n p : ℝ) / p) / 6)) =
      (p : ℝ) * ((c01Piece j).a + (c01Piece j).b * (q6 n p : ℝ) + (q6 n p : ℝ) ^ 2 / 2) +
      (n : ℝ) * ((c01Piece j).g - 3 * (q6 n p : ℝ)) := by
    rw [hn6]; field_simp
  have hq0 : (0 : ℝ) ≤ (q6 n p : ℝ) ^ 2 := sq_nonneg _
  nlinarith [hexp, hmain, hq0]

end FinalBridge

end Closed

end CatalanCore.Lai

#print axioms CatalanCore.Lai.sum_pot2_split
#print axioms CatalanCore.Lai.nuP_real
#print axioms CatalanCore.Lai.two_T
#print axioms CatalanCore.Lai.scaled_Num
#print axioms CatalanCore.Lai.x_part
#print axioms CatalanCore.Lai.W_ge
#print axioms CatalanCore.Lai.piece_closed
#print axioms CatalanCore.Lai.bridge_proof
