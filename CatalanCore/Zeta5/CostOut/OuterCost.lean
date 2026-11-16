module

public import CatalanCore.Zeta5.CostOut.OuterInt
public import CatalanCore.Zeta5.Sum.OuterBridge

@[expose] public section

/-!
# ZC20: the outer cost `w(K,p) = K T₀(p/K) + O(1)` for `K/3 < p ≤ 2h`

`K = 40 n`, `h = 37 n`. With `wOut n p = -v_p(S_K) - γ_p^out` (`γ_p^out = gammaOut` for `p ≤ K` and `0`
for `p > K`):

* `pEx_eq` : `p · Ex(K/p) = pExZ n p` (the closed `x T₀(1/x)` of `Sum.OuterDefs` at `x = K/p`, an integer);
* `zc20_outer` : `|wOut n p - K · T₀(p/K)| ≤ 10`, with `T₀ = Sum.T0` (the paper's `T₀`, with its
  `z`-integrals), for every prime `p` with `K/3 < p ≤ 2h`, every `n ≥ 1`.
-/

open Finset

set_option linter.unusedSimpArgs false

namespace CatalanCore.Zeta5.CostOut

open CatalanCore.Zeta5.Sum CatalanCore.Zeta5.Profile

/-- `P · (a min + b max + c max + d (1/2 - max))` in the four-region form. -/
lemma pIint_gen (P t u a b c d : ℚ) (hP : 0 < P) (x : ℚ) (htri : tri x = t / P)
    (hal : al * x = u / P) :
    P * (a * min (tri x) (al * x) + b * max 0 (tri x - al * x) + c * max 0 (al * x - tri x)
        + d * (1 / 2 - max (tri x) (al * x)))
      = a * min t u + b * max 0 (t - u) + c * max 0 (u - t) + d * (P / 2 - max t u) := by
  rw [htri, hal]
  have h1 : P * min (t / P) (u / P) = min t u := by
    rw [mul_min_of_nonneg _ _ hP.le]
    congr 1 <;> field_simp
  have h2 : P * max (t / P) (u / P) = max t u := by
    rw [mul_max_of_nonneg _ _ hP.le]
    congr 1 <;> field_simp
  have h3 : P * max 0 (t / P - u / P) = max 0 (t - u) := by
    rw [mul_max_of_nonneg _ _ hP.le]
    congr 1
    · simp
    · field_simp
  have h4 : P * max 0 (u / P - t / P) = max 0 (u - t) := by
    rw [mul_max_of_nonneg _ _ hP.le]
    congr 1
    · simp
    · field_simp
  linear_combination a * h1 + b * h3 + c * h4 - d * h2

lemma Sq_vals :
    Sq 3 1 = -1 / 2 ∧ Sq 3 0 = -7 / 2 ∧ Sq 2 1 = 0 ∧ Sq 2 0 = 0 ∧ Sq 4 1 = -1 ∧ Sq 4 0 = -7 ∧
    Sq 5 1 = -2 ∧ Sq 5 0 = -21 / 2 ∧ Sq 6 1 = -3 ∧ Sq 6 0 = -14 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [Sq, wrowQ, List.range_succ]

lemma Nq_vals :
    Nq 3 1 = 1 ∧ Nq 3 0 = 2 ∧ Nq 2 1 = 1 ∧ Nq 2 0 = 2 ∧ Nq 4 1 = 2 ∧ Nq 4 0 = 2 ∧
    Nq 5 1 = 2 ∧ Nq 5 0 = 2 ∧ Nq 6 1 = 3 ∧ Nq 6 0 = 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [Nq, wrowQ, List.range_succ]


/-- `⌊K/p⌋`, `{K/p}` and the four affine facts at `x = K/p`. -/
lemma x_facts {n p : ℕ} (h0 : 0 < p) :
    ⌊(40 * n : ℚ) / p⌋ = ((40 * n / p : ℕ) : ℤ) ∧
    Int.fract ((40 * n : ℚ) / p) = ((40 * n % p : ℕ) : ℚ) / p := by
  have hp0 : (0 : ℚ) < p := by exact_mod_cast h0
  have hxq : ((40 * n : ℕ) : ℚ) = (40 * n : ℚ) := by push_cast; ring
  have hfl : ⌊(40 * n : ℚ) / p⌋ = ((40 * n / p : ℕ) : ℤ) := by
    have := Rat.floor_natCast_div_natCast (40 * n) p
    rw [hxq] at this
    rw [this]; push_cast; rfl
  refine ⟨hfl, ?_⟩
  rw [Int.fract, hfl]
  have hd := Nat.div_add_mod (40 * n) p
  have hd' : ((p : ℚ) * ((40 * n / p : ℕ) : ℚ) + ((40 * n % p : ℕ) : ℚ)) = 40 * n := by
    have := congrArg (fun m : ℕ => (m : ℚ)) hd
    simp only [Nat.cast_add, Nat.cast_mul] at this
    rw [this]; push_cast; ring
  simp only [Int.cast_natCast]
  field_simp
  linarith


/-- **The closed form is an integer.** `p · Ex(K/p) = pExZ n p`. -/
theorem pEx_eq {n p : ℕ} (hn : 1 ≤ n) (h1 : 40 * n < 3 * p) (hodd : p % 2 = 1) :
    (p : ℚ) * Ex ((40 * n : ℚ) / p) = (pExZ n p : ℚ) := by
  have hp0n : 0 < p := by omega
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp0n
  obtain ⟨hfl, hfr⟩ := x_facts (n := n) hp0n
  have hd := Nat.div_add_mod (40 * n) p
  have hvlt := Nat.mod_lt (40 * n) hp0n
  have hxp : ((40 * n : ℚ) / p) * p = 40 * n := by field_simp
  obtain ⟨q, hq⟩ : ∃ q, q = 40 * n / p := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = 40 * n % p := ⟨_, rfl⟩
  rw [← hq] at hfl hd
  rw [← hv] at hfr hd hvlt
  unfold pExZ
  simp only [← hq, ← hv]
  generalize (40 * n : ℚ) / p = x at hfl hfr hxp ⊢
  have e_lam : (p : ℚ) * (lam * x) = 37 * n := by
    unfold lam; linear_combination (37 / 40 : ℚ) * hxp
  have e_al : (p : ℚ) * (al * x) = 3 * n := by
    unfold al; linear_combination (3 / 40 : ℚ) * hxp
  have e_2lam : (p : ℚ) * (2 * lam * x) = 74 * n := by
    unfold lam; linear_combination (37 / 20 : ℚ) * hxp
  have e_52 : (p : ℚ) * ((1 + 4 * al) * x - 2) = 52 * n - 2 * p := by
    unfold al; linear_combination (13 / 10 : ℚ) * hxp
  have hal : al * x = (3 * n) / p := by
    field_simp; linear_combination e_al
  have hrx : (p : ℚ) * rx x = min (37 * (n : ℚ)) (max 0 (52 * (n : ℚ) - 2 * (p : ℚ))) := by
    unfold rx
    rw [mul_min_of_nonneg _ _ hp0.le, mul_max_of_nonneg _ _ hp0.le, e_lam, e_52, mul_zero]
  have hs : ∀ j : ℚ, (p : ℚ) * max 0 (2 * lam * x - j) = max 0 (74 * n - j * p) := by
    intro j
    rw [mul_max_of_nonneg _ _ hp0.le, mul_zero, mul_sub, e_2lam, mul_comm (p : ℚ) j]
  have hfloor : (p : ℚ) * (2 * lam * x * (⌊x⌋ : ℚ)) = 74 * n * q := by
    rw [hfl]; simp only [Int.cast_natCast]
    linear_combination (q : ℚ) * e_2lam
  have hmain : (p : ℚ) * Ex x = -((p : ℚ) * Gx x) + min ((p : ℚ) * rx x) ((p : ℚ) * Zx x)
      - (p : ℚ) * (2 * lam * x * (⌊x⌋ : ℚ)) + (p : ℚ) * max 0 (2 * lam * x - 1)
      + (p : ℚ) * max 0 (2 * lam * x - 2) + (p : ℚ) * max 0 (2 * lam * x - 3)
      + (p : ℚ) * max 0 (2 * lam * x - 4) + (p : ℚ) * max 0 (2 * lam * x - 5) := by
    rw [← mul_min_of_nonneg _ _ hp0.le]
    unfold Ex
    ring
  rw [hmain, hrx, hfloor, hs 1, hs 2, hs 3, hs 4, hs 5]
  by_cases hge : 40 * n ≤ p
  · simp only [hge, ite_true]
    have hnot : ¬ 1 < x := by
      intro h
      have h40 : (40 * n : ℚ) ≤ p := by exact_mod_cast hge
      nlinarith [mul_lt_mul_of_pos_right h hp0]
    rw [show Gx x = 0 by simp [Gx, hnot], show Zx x = lam * x by simp [Zx, hnot], e_lam]
    push_cast [rPart, scalarPart]
    rw [min_comm (min _ _) _]
    simp only [one_mul, mul_zero, neg_zero, zero_add]
    ring
  · simp only [hge, ite_false]
    have hlt : p < 40 * n := by omega
    have hx1 : 1 < x := by
      have h40 : (p : ℚ) < 40 * n := by exact_mod_cast hlt
      by_contra hc
      push Not at hc
      nlinarith [mul_le_mul_of_nonneg_right hc hp0.le]
    rw [show Gx x = 2 * Iint x by simp [Gx, hx1], show Zx x = Zint x by simp [Zx, hx1]]
    have hq12 : q = 1 ∨ q = 2 := by
      have hq1 : 1 ≤ q := by
        by_contra hc
        have : q = 0 := by omega
        subst this
        omega
      have hq3 : q < 3 := by
        by_contra hc
        have h3 : 3 ≤ q := by omega
        have : p * 3 ≤ p * q := Nat.mul_le_mul_left p h3
        omega
      omega
    obtain ⟨t, ht⟩ : ∃ t : ℚ, t = min (v : ℚ) ((p : ℚ) - v) := ⟨_, rfl⟩
    have htri : tri x = t / p := by
      unfold tri
      rw [hfr, ht, ← min_div_div_right hp0.le]
      congr 1
      field_simp
    have hI : (p : ℚ) * Iint x = Sq (lA x) 1 * min t (3 * n) + Sq (lA x) 0 * max 0 (t - 3 * n)
        + Sq (lB x) 1 * max 0 (3 * n - t) + Sq (lB x) 0 * ((p : ℚ) / 2 - max t (3 * n)) := by
      simp only [Iint, Rat.cast_id]
      exact pIint_gen p t (3 * n) _ _ _ _ hp0 x htri hal
    have hZ : (p : ℚ) * Zint x = Nq (lA x) 1 * min t (3 * n) + Nq (lA x) 0 * max 0 (t - 3 * n)
        + Nq (lB x) 1 * max 0 (3 * n - t) + Nq (lB x) 0 * ((p : ℚ) / 2 - max t (3 * n)) := by
      simp only [Zint, Rat.cast_id]
      exact pIint_gen p t (3 * n) _ _ _ _ hp0 x htri hal
    have hlA : lA x = 2 * q + 1 := by
      unfold lA; rw [hfl]; omega
    have hlB : lB x = if 2 * v < p then 2 * q else 2 * q + 2 := by
      unfold lB
      rw [hfl, hfr]
      by_cases hh : 2 * v < p
      · have : (v : ℚ) / p < 1 / 2 := by
          rw [div_lt_iff₀ hp0]
          have : (2 * v : ℚ) < p := by exact_mod_cast hh
          linarith
        simp only [this, hh, ite_true]; omega
      · have : ¬ ((v : ℚ) / p < 1 / 2) := by
          rw [not_lt, le_div_iff₀ hp0]
          have : (p : ℚ) ≤ 2 * v := by exact_mod_cast (by omega : p ≤ 2 * v)
          linarith
        simp only [this, hh, ite_false]; omega
    obtain ⟨s31, s30, s21, s20, s41, s40, s51, s50, s61, s60⟩ := Sq_vals
    obtain ⟨n31, n30, n21, n20, n41, n40, n51, n50, n61, n60⟩ := Nq_vals
    have hrQ : ((rPart n p : ℤ) : ℚ) = min (37 * (n : ℚ)) (max 0 (52 * (n : ℚ) - 2 * (p : ℚ))) := by
      push_cast [rPart]; rfl
    rcases hq12 with rfl | rfl <;> by_cases hh : 2 * v < p
    · have hlA' : lA x = 3 := by rw [hlA]
      have hlB' : lB x = 2 := by simp only [hlB, hh, ite_true]
      rw [hlA', hlB', s31, s30, s21, s20] at hI
      rw [hlA', hlB', n31, n30, n21, n20] at hZ
      have hZ2 : (p : ℚ) * Zint x = (min t (3 * (n : ℚ))) + 2 * (max 0 (t - 3 * (n : ℚ))) + (max 0 (3 * (n : ℚ) - t)) + (p : ℚ) - 2 * (max t (3 * (n : ℚ))) := by rw [hZ]; ring
      have hhZ : (2 * (v : ℤ) < (p : ℤ)) := by
        exact_mod_cast hh
      simp only [inPart, Nat.cast_one, Nat.cast_ofNat, hhZ, ite_true, ite_false, show (2:ℤ) ≠ 1 from by norm_num]
      push_cast [scalarPart]
      rw [← ht, hrQ, hZ2, show (p : ℚ) * (2 * Iint x) = 2 * ((p : ℚ) * Iint x) by ring, hI]
      ring_nf
    · have hlA' : lA x = 3 := by rw [hlA]
      have hlB' : lB x = 4 := by simp only [hlB, hh, ite_false]
      rw [hlA', hlB', s31, s30, s41, s40] at hI
      rw [hlA', hlB', n31, n30, n41, n40] at hZ
      have hZ2 : (p : ℚ) * Zint x = (min t (3 * (n : ℚ))) + 2 * (max 0 (t - 3 * (n : ℚ))) + 2 * (max 0 (3 * (n : ℚ) - t)) + (p : ℚ) - 2 * (max t (3 * (n : ℚ))) := by rw [hZ]; ring
      have hhZ : ¬ (2 * (v : ℤ) < (p : ℤ)) := by
        intro hc; exact hh (by exact_mod_cast hc)
      simp only [inPart, Nat.cast_one, Nat.cast_ofNat, hhZ, ite_true, ite_false, show (2:ℤ) ≠ 1 from by norm_num]
      push_cast [scalarPart]
      rw [← ht, hrQ, hZ2, show (p : ℚ) * (2 * Iint x) = 2 * ((p : ℚ) * Iint x) by ring, hI]
      ring_nf
    · have hlA' : lA x = 5 := by rw [hlA]
      have hlB' : lB x = 4 := by simp only [hlB, hh, ite_true]
      rw [hlA', hlB', s51, s50, s41, s40] at hI
      rw [hlA', hlB', n51, n50, n41, n40] at hZ
      have hZ2 : (p : ℚ) * Zint x = 2 * (min t (3 * (n : ℚ))) + 2 * (max 0 (t - 3 * (n : ℚ))) + 2 * (max 0 (3 * (n : ℚ) - t)) + (p : ℚ) - 2 * (max t (3 * (n : ℚ))) := by rw [hZ]; ring
      have hhZ : (2 * (v : ℤ) < (p : ℤ)) := by
        exact_mod_cast hh
      simp only [inPart, Nat.cast_one, Nat.cast_ofNat, hhZ, ite_true, ite_false, show (2:ℤ) ≠ 1 from by norm_num]
      push_cast [scalarPart]
      rw [← ht, hrQ, hZ2, show (p : ℚ) * (2 * Iint x) = 2 * ((p : ℚ) * Iint x) by ring, hI]
      ring_nf
    · have hlA' : lA x = 5 := by rw [hlA]
      have hlB' : lB x = 6 := by simp only [hlB, hh, ite_false]
      rw [hlA', hlB', s51, s50, s61, s60] at hI
      rw [hlA', hlB', n51, n50, n61, n60] at hZ
      have hZ2 : (p : ℚ) * Zint x = 2 * (min t (3 * (n : ℚ))) + 2 * (max 0 (t - 3 * (n : ℚ))) + 3 * (max 0 (3 * (n : ℚ) - t)) + (p : ℚ) - 2 * (max t (3 * (n : ℚ))) := by rw [hZ]; ring
      have hhZ : ¬ (2 * (v : ℤ) < (p : ℤ)) := by
        intro hc; exact hh (by exact_mod_cast hc)
      simp only [inPart, Nat.cast_one, Nat.cast_ofNat, hhZ, ite_true, ite_false, show (2:ℤ) ≠ 1 from by norm_num]
      push_cast [scalarPart]
      rw [← ht, hrQ, hZ2, show (p : ℚ) * (2 * Iint x) = 2 * ((p : ℚ) * Iint x) by ring, hI]
      ring_nf

/-- The signed outer exponent `w(K,p) = -v_p(S_K) - γ_p^out` of CONTENT-THEOREM (C6)
(`γ_p^out = gammaOut` for `p ≤ K`, and `0` for `p > K`, `zc14_big`). -/
noncomputable def wOut (n p : ℕ) : ℤ :=
  -Apery.vSK n p - (if p ≤ 40 * n then Apery.gammaOut n p else 0)

theorem wOut_eq {n p : ℕ} [Fact p.Prime] (hn : 1 ≤ n) (h1 : 40 * n < 3 * p) :
    wOut n p = wOutZ n p := by
  unfold wOut wOutZ
  rw [vSK_outer hn h1]

/-- **ZC20.** For every `n ≥ 1` and every prime `p` with `K/3 < p ≤ 2h` (`K = 40 n`, `h = 37 n`):
`|w(K,p) - K · T₀(p/K)| ≤ 10`, where `T₀ = Sum.T0` is the paper's outer rate. -/
theorem zc20_outer {n p : ℕ} [hp : Fact p.Prime] (hn : 1 ≤ n) (h1 : 40 * n < 3 * p)
    (h2 : p ≤ 2 * (37 * n)) :
    |(wOut n p : ℝ) - (40 * n : ℝ) * T0 ((p : ℝ) / (40 * n))| ≤ 10 := by
  have hodd : p % 2 = 1 := by
    have := Apery.prime_odd_of_ge hp.out (by omega)
    omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hK0 : (0 : ℝ) < 40 * n := by positivity
  have hx0 : (0 : ℝ) < (40 * n : ℝ) / p := by positivity
  have hx3 : (40 * n : ℝ) / p < 3 := by
    rw [div_lt_iff₀ hp0]
    exact_mod_cast (by omega : 40 * n < 3 * p)
  have hT := T0_inv hx0 hx3
  have hinv : (1 : ℝ) / ((40 * n : ℝ) / p) = (p : ℝ) / (40 * n) := by
    field_simp
  rw [hinv] at hT
  have hEx : (p : ℝ) * Ex ((40 * n : ℝ) / p) = (pExZ n p : ℝ) := by
    have h := pEx_eq hn h1 hodd
    have h' := congrArg (fun r : ℚ => (r : ℝ)) h
    simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast] at h'
    rw [Ex_cast] at h'
    push_cast at h'
    exact h'
  have hK : (40 * n : ℝ) * T0 ((p : ℝ) / (40 * n)) = (pExZ n p : ℝ) := by
    rw [hT, ← hEx]
    field_simp
  rw [hK, wOut_eq hn h1]
  have hb := outer_int_bound hn hodd h1 (by omega)
  rw [abs_le]
  constructor
  · have : (-10 : ℝ) ≤ ((wOutZ n p - pExZ n p : ℤ) : ℝ) := by exact_mod_cast hb.1
    push_cast at this; linarith
  · have : ((wOutZ n p - pExZ n p : ℤ) : ℝ) ≤ 3 := by exact_mod_cast hb.2
    push_cast at this; linarith


/-- **ZC20 in the form `band_error_bound` consumes** (`Sum.PrimeBounds`): with `K = 40 n`,
`f p = w(K,p) - K T₀(p/K)` is bounded by `10` on the primes of `(K/3, 2h]`. -/
theorem zc20_band {n : ℕ} (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (h1 : (40 * n : ℝ) / 3 < p)
    (h2 : (p : ℝ) ≤ 2 * (37 * n)) :
    |(wOut n p : ℝ) - (40 * n : ℝ) * T0 ((p : ℝ) / (40 * n))| ≤ 10 := by
  have : Fact p.Prime := ⟨hp⟩
  refine zc20_outer hn ?_ ?_
  · have : (40 * n : ℝ) < 3 * p := by linarith
    exact_mod_cast this
  · exact_mod_cast h2

end CatalanCore.Zeta5.CostOut

#print axioms CatalanCore.Zeta5.CostOut.zc20_outer
#print axioms CatalanCore.Zeta5.CostOut.zc20_band
#print axioms CatalanCore.Zeta5.CostOut.pEx_eq
#print axioms CatalanCore.Zeta5.CostOut.outer_int_bound
