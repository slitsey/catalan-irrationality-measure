module

public import CatalanLambda.GrowthFinal
public import CatalanLambda.PNTAP
public import Mathlib.NumberTheory.Chebyshev

@[expose] public section

/-!
# Primes `≡ 3 (mod 4)` in a window `(aL, bL]` avoiding a given modulus

From `pnt_mod4_three` and Mathlib's `Chebyshev.psi_sub_theta_le` we get the lower bound
`θ(N; 4, 3) ≥ (1/2 - ε) N` eventually, hence: for `b > a + 2` and `q` large, there is a prime
`ℓ ≡ 3 (mod 4)` in `(a log q, b log q]` with `ℓ ∤ q`.
-/

open Filter Topology

namespace CatalanLambda.Measure

/-- `∑_{n ≤ N, n ≡ 3 (4)} Λ n`. -/
noncomputable def Psi3 (N : ℕ) : ℝ :=
  ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % 4 = 3), ArithmeticFunction.vonMangoldt n

lemma th3_ge {N : ℕ} (hN : 1 ≤ N) : Psi3 N - 2 * √(N : ℝ) * Real.log N ≤ th 3 N := by
  have h1 := Chebyshev.psi_sub_theta_le (x := (N : ℝ)) (by exact_mod_cast hN)
  rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast] at h1
  unfold Psi3
  rw [← Finset.sum_filter_add_sum_filter_not _ Nat.Prime]
  have e1 : ∑ n ∈ ((Finset.range (N + 1)).filter (fun n => n % 4 = 3)).filter Nat.Prime,
      ArithmeticFunction.vonMangoldt n = th 3 N := by
    unfold th
    have : ((Finset.range (N + 1)).filter (fun n => n % 4 = 3)).filter Nat.Prime
        = (Finset.range (N + 1)).filter (fun n => n.Prime ∧ n % 4 = 3) := by
      ext n; simp only [Finset.mem_filter]; tauto
    rw [this]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hp : n.Prime := (Finset.mem_filter.1 hn).2.1
    exact ArithmeticFunction.vonMangoldt_apply_prime hp
  have e2 : ∑ n ∈ ((Finset.range (N + 1)).filter (fun n => n % 4 = 3)).filter (fun n => ¬ n.Prime),
      ArithmeticFunction.vonMangoldt n
      ≤ ∑ n ∈ Finset.Ioc 0 N with ¬ n.Prime, ArithmeticFunction.vonMangoldt n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc] at hn ⊢
      refine ⟨⟨?_, by omega⟩, hn.2⟩
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0; omega
      · exact h0
    · intro n _ _; exact ArithmeticFunction.vonMangoldt_nonneg
  rw [e1]
  linarith

/-- `2 √N log N ≤ ε N` eventually. -/
lemma sqrt_log_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 2 * √(N : ℝ) * Real.log N ≤ ε * N := by
  filter_upwards [eventually_ge_atTop (⌈(8 / ε) ^ 4⌉₊ + 1)] with N hN
  have hN1 : (8 / ε) ^ 4 < N := by
    have : (⌈(8 / ε) ^ 4⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    have := Nat.le_ceil ((8 / ε) ^ 4)
    linarith
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN1
  set s := √(N : ℝ) with hs
  set u := √s with hu
  have hs0 : 0 < s := Real.sqrt_pos.2 hNpos
  have hu0 : 0 < u := Real.sqrt_pos.2 hs0
  have hsu : s = u ^ 2 := (Real.sq_sqrt hs0.le).symm
  have hNs : (N : ℝ) = s ^ 2 := (Real.sq_sqrt hNpos.le).symm
  have hN4 : (N : ℝ) = u ^ 4 := by rw [hNs, hsu]; ring
  have hlog : Real.log N ≤ 4 * u := by
    rw [hN4, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hu0
    push_cast; linarith
  have hu8 : 8 / ε ≤ u := by
    by_contra hc
    push Not at hc
    have : u ^ 4 < (8 / ε) ^ 4 := pow_lt_pow_left₀ hc hu0.le (by norm_num)
    linarith
  have hu8' : 8 ≤ ε * u := by
    have := (div_le_iff₀ hε).1 hu8
    linarith
  calc 2 * s * Real.log N ≤ 2 * s * (4 * u) := by gcongr
    _ = 8 * u ^ 3 := by rw [hsu]; ring
    _ ≤ ε * u ^ 4 := by nlinarith [pow_pos hu0 3]
    _ = ε * N := by rw [hN4]

lemma Psi3_lower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (1 / 2 - ε) * N ≤ Psi3 N := by
  have h1 := pnt_mod4_three.comp (tendsto_add_atTop_nat 1)
  have h2 := (tendsto_order.1 h1).1 (1 / 2 - ε) (by linarith)
  filter_upwards [h2, eventually_gt_atTop 0] with N hN hN0
  simp only [Function.comp, Nat.cast_add, Nat.cast_one] at hN
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have := (lt_div_iff₀ hpos).1 hN
  have hnn : 0 ≤ Psi3 N := Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
  have hP : Psi3 N = ∑ n ∈ (Finset.range (N + 1)).filter (fun n => n % 4 = 3),
      ArithmeticFunction.vonMangoldt n := rfl
  rw [← hP] at this
  rcases le_or_gt 0 (1 / 2 - ε) with hc | hc
  · nlinarith
  · nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)]

lemma th3_lower {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (1 / 2 - ε) * N ≤ th 3 N := by
  filter_upwards [Psi3_lower (half_pos hε), sqrt_log_small (half_pos hε), eventually_ge_atTop 1]
    with N h1 h2 h3
  have := th3_ge h3
  linarith

lemma th3_upper' {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, th 3 N ≤ (1 / 2 + ε) * N :=
  th_upper 3 (Or.inr rfl) ε hε

lemma th_diff (X Y : ℕ) (hXY : X ≤ Y) :
    th 3 Y - th 3 X = ∑ n ∈ (Finset.Ico (X + 1) (Y + 1)).filter (fun n => n.Prime ∧ n % 4 = 3),
      Real.log n := by
  unfold th
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    Finset.sum_Ico_eq_sub _ (by omega : X + 1 ≤ Y + 1)]

/-- **Prime in a window.**  For `b > a + 2` and `q` large there is a prime `ℓ ≡ 3 (4)` with
`a log q < ℓ ≤ b log q` and `ℓ ∤ q`. -/
theorem exists_prime_window (a b : ℝ) (ha : 0 < a) (hab : a + 2 < b) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ % 4 = 3 ∧
      a * Real.log q < ℓ ∧ (ℓ : ℝ) ≤ b * Real.log q ∧ ¬ ℓ ∣ q := by
  set κ : ℝ := (b - a) / 2 - 1 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  set ε : ℝ := κ / (2 * (a + b)) with hε
  have hε0 : 0 < ε := by rw [hε]; have : 0 < a + b := by linarith
                         positivity
  have hε4 : ε < 1 / 4 := by
    rw [hε, div_lt_iff₀ (by linarith)]; rw [hκ]; linarith
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((th3_lower hε0).and (th3_upper' hε0))
  set L₀ : ℝ := max (N₁ / a) (1 / κ) with hL₀
  refine ⟨⌈Real.exp L₀⌉₊, fun q hq => ?_⟩
  have hqe : Real.exp L₀ ≤ q := le_trans (Nat.le_ceil _) (by exact_mod_cast hq)
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) hqe
  have hq0 : 0 < q := by exact_mod_cast hqpos
  have hL : L₀ ≤ Real.log q := (Real.le_log_iff_exp_le hqpos).2 hqe
  set L := Real.log q with hLdef
  have hLa : (N₁ : ℝ) ≤ a * L := by
    have : (N₁ : ℝ) / a ≤ L := le_trans (le_max_left _ _) hL
    rwa [div_le_iff₀ ha, mul_comm] at this
  have hLκ : 1 ≤ κ * L := by
    have : 1 / κ ≤ L := le_trans (le_max_right _ _) hL
    rwa [div_le_iff₀ hκ0, mul_comm] at this
  set NX := ⌊a * L⌋₊ with hNX
  set NY := ⌊b * L⌋₊ with hNY
  have hL0 : 0 ≤ L := by
    have : 0 < κ := hκ0
    nlinarith
  have hNXle : (NX : ℝ) ≤ a * L := Nat.floor_le (by positivity)
  have hNXgt : a * L < NX + 1 := Nat.lt_floor_add_one _
  have hNYle : (NY : ℝ) ≤ b * L := Nat.floor_le (by nlinarith)
  have hNYgt : b * L < NY + 1 := Nat.lt_floor_add_one _
  have hNX1 : N₁ ≤ NX := Nat.le_floor hLa
  have hXY : NX ≤ NY := Nat.floor_le_floor (by nlinarith)
  have hNY1 : N₁ ≤ NY := le_trans hNX1 hXY
  obtain ⟨hlow, -⟩ := hN₁ NY hNY1
  obtain ⟨-, hup⟩ := hN₁ NX hNX1
  by_contra hcon
  push Not at hcon
  set S := (Finset.Ico (NX + 1) (NY + 1)).filter (fun n => n.Prime ∧ n % 4 = 3) with hS
  have hSdvd : ∀ n ∈ S, n ∣ q := by
    intro n hn
    simp only [hS, Finset.mem_filter, Finset.mem_Ico] at hn
    obtain ⟨⟨h1, h2⟩, hp, hm⟩ := hn
    apply hcon n hp hm
    · have : (NX : ℝ) + 1 ≤ n := by exact_mod_cast h1
      linarith
    · have : (n : ℝ) ≤ NY := by exact_mod_cast (by omega : n ≤ NY)
      linarith
  have hprod : ∏ n ∈ S, n ∣ q :=
    Finset.prod_primes_dvd q (fun n hn => (Finset.mem_filter.1 hn).2.1.prime) hSdvd
  have hle : ∏ n ∈ S, n ≤ q := Nat.le_of_dvd hq0 hprod
  have hprodpos : 0 < ∏ n ∈ S, n :=
    Finset.prod_pos fun n hn => (Finset.mem_filter.1 hn).2.1.pos
  have hlog : ∑ n ∈ S, Real.log n ≤ L := by
    rw [← Real.log_prod (fun n hn => by
      have := (Finset.mem_filter.1 hn).2.1.pos
      exact_mod_cast this.ne')]
    apply Real.log_le_log
    · have : (0 : ℝ) < ((∏ n ∈ S, n : ℕ) : ℝ) := by exact_mod_cast hprodpos
      simpa [Nat.cast_prod] using this
    · have : ((∏ n ∈ S, n : ℕ) : ℝ) ≤ q := by exact_mod_cast hle
      simpa [Nat.cast_prod] using this
  rw [← th_diff NX NY hXY] at hlog
  -- numerics
  have hb1 : (b * L - 1) ≤ NY := by linarith
  have hhalf : 0 ≤ 1 / 2 - ε := by linarith
  have e1 : (1 / 2 - ε) * (b * L - 1) ≤ (1 / 2 - ε) * NY := by
    apply mul_le_mul_of_nonneg_left hb1 hhalf
  have e2 : (1 / 2 + ε) * (NX : ℝ) ≤ (1 / 2 + ε) * (a * L) := by
    apply mul_le_mul_of_nonneg_left hNXle (by linarith)
  have hab0 : a + b ≠ 0 := by linarith
  have hεab : ε * (2 * (a + b)) = κ := by rw [hε]; field_simp
  have : (1 / 2 - ε) * (b * L - 1) - (1 / 2 + ε) * (a * L)
      = L * ((b - a) / 2 - ε * (a + b)) - (1 / 2 - ε) := by ring
  have h3 : L * ((b - a) / 2 - ε * (a + b)) = L * (1 + κ / 2) := by
    congr 1; rw [hκ] at hεab ⊢; linarith
  nlinarith

/-- **Window sum.**  For `b > a + 2t`, `t > 0` and `L` large, the primes `ℓ ≡ 3 (4)` in
`(aL, bL]` have `∑ log ℓ > t L`. -/
theorem window_sum (a b t : ℝ) (ha : 0 < a) (ht : 0 < t) (hab : a + 2 * t < b) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∃ S : Finset ℕ,
      (∀ n ∈ S, n.Prime ∧ n % 4 = 3 ∧ a * L < n ∧ (n : ℝ) ≤ b * L) ∧
        t * L < ∑ n ∈ S, Real.log n := by
  set κ : ℝ := (b - a) / 2 - t with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  set ε : ℝ := κ / (2 * (a + b)) with hε
  have hab0 : a + b ≠ 0 := by linarith
  have hε0 : 0 < ε := by
    rw [hε]; have : 0 < a + b := by linarith
    positivity
  have hε4 : ε < 1 / 4 := by
    rw [hε, div_lt_iff₀ (by linarith)]; rw [hκ]; linarith
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((th3_lower hε0).and (th3_upper' hε0))
  refine ⟨max (N₁ / a) (1 / κ), fun L hL => ?_⟩
  have hLa : (N₁ : ℝ) ≤ a * L := by
    have : (N₁ : ℝ) / a ≤ L := le_trans (le_max_left _ _) hL
    rw [div_le_iff₀ ha] at this; linarith
  have hLκ : 1 ≤ κ * L := by
    have : 1 / κ ≤ L := le_trans (le_max_right _ _) hL
    rw [div_le_iff₀ hκ0] at this; linarith
  set NX := ⌊a * L⌋₊ with hNX
  set NY := ⌊b * L⌋₊ with hNY
  have hL0 : 0 ≤ L := by nlinarith
  have hNXle : (NX : ℝ) ≤ a * L := Nat.floor_le (by positivity)
  have hNXgt : a * L < NX + 1 := Nat.lt_floor_add_one _
  have hNYle : (NY : ℝ) ≤ b * L := Nat.floor_le (by nlinarith)
  have hNYgt : b * L < NY + 1 := Nat.lt_floor_add_one _
  have hNX1 : N₁ ≤ NX := Nat.le_floor hLa
  have hXY : NX ≤ NY := Nat.floor_le_floor (by nlinarith)
  have hNY1 : N₁ ≤ NY := le_trans hNX1 hXY
  obtain ⟨hlow, -⟩ := hN₁ NY hNY1
  obtain ⟨-, hup⟩ := hN₁ NX hNX1
  refine ⟨(Finset.Ico (NX + 1) (NY + 1)).filter (fun n => n.Prime ∧ n % 4 = 3), ?_, ?_⟩
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn
    obtain ⟨⟨h1, h2⟩, hp, hm⟩ := hn
    refine ⟨hp, hm, ?_, ?_⟩
    · have : (NX : ℝ) + 1 ≤ n := by exact_mod_cast h1
      linarith
    · have : (n : ℝ) ≤ NY := by exact_mod_cast (by omega : n ≤ NY)
      linarith
  · rw [← th_diff NX NY hXY]
    have hb1 : (b * L - 1) ≤ NY := by linarith
    have hhalf : 0 ≤ 1 / 2 - ε := by linarith
    have e1 : (1 / 2 - ε) * (b * L - 1) ≤ (1 / 2 - ε) * NY :=
      mul_le_mul_of_nonneg_left hb1 hhalf
    have e2 : (1 / 2 + ε) * (NX : ℝ) ≤ (1 / 2 + ε) * (a * L) :=
      mul_le_mul_of_nonneg_left hNXle (by linarith)
    have hεab : ε * (2 * (a + b)) = κ := by rw [hε]; field_simp
    have : (1 / 2 - ε) * (b * L - 1) - (1 / 2 + ε) * (a * L)
        = L * ((b - a) / 2 - ε * (a + b)) - (1 / 2 - ε) := by ring
    have h3 : L * ((b - a) / 2 - ε * (a + b)) = L * (t + κ / 2) := by
      congr 1; rw [hκ] at hεab ⊢; linarith
    nlinarith

/-- If all `n ∈ S` are primes with `n² ∣ q` then `(∏ n)² ∣ q`. -/
lemma sq_prod_dvd (q : ℕ) (S : Finset ℕ) (hS : ∀ n ∈ S, n.Prime ∧ n ^ 2 ∣ q) :
    (∏ n ∈ S, n) ^ 2 ∣ q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    have hS' : ∀ n ∈ S, n.Prime ∧ n ^ 2 ∣ q := fun n hn => hS n (Finset.mem_insert_of_mem hn)
    have iha := ih hS'
    have hap := hS a (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert ha, mul_pow]
    have hcop : Nat.Coprime (a ^ 2) ((∏ n ∈ S, n) ^ 2) := by
      apply Nat.Coprime.pow
      apply (Nat.Prime.coprime_iff_not_dvd hap.1).2
      intro hd
      obtain ⟨n, hn, hdn⟩ := (Prime.dvd_finset_prod_iff hap.1.prime _).1 hd
      have := (Nat.prime_dvd_prime_iff_eq hap.1 (hS' n hn).1).1 hdn
      exact ha (this ▸ hn)
    exact hcop.mul_dvd_of_dvd_of_dvd hap.2 iha

/-- **Prime in a window, not exactly dividing twice.**  For `b > a + 1` and `q` large there is a
prime `ℓ ≡ 3 (4)` with `a log q < ℓ ≤ b log q` and not (`ℓ² ∣ q` and `ℓ³ ∤ q`). -/
theorem exists_prime_window_sq (a b : ℝ) (ha : 0 < a) (hab : a + 1 < b) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ % 4 = 3 ∧
      a * Real.log q < ℓ ∧ (ℓ : ℝ) ≤ b * Real.log q ∧ ¬ (ℓ ^ 2 ∣ q ∧ ¬ ℓ ^ 3 ∣ q) := by
  obtain ⟨L₀, hL₀⟩ := window_sum a b (1 / 2) ha (by norm_num) (by linarith)
  refine ⟨⌈Real.exp L₀⌉₊, fun q hq => ?_⟩
  have hqe : Real.exp L₀ ≤ q := le_trans (Nat.le_ceil _) (by exact_mod_cast hq)
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (Real.exp_pos _) hqe
  have hq0 : 0 < q := by exact_mod_cast hqpos
  have hL : L₀ ≤ Real.log q := (Real.le_log_iff_exp_le hqpos).2 hqe
  obtain ⟨S, hS, hsum⟩ := hL₀ _ hL
  by_contra hcon
  push Not at hcon
  have hall : ∀ n ∈ S, n.Prime ∧ n ^ 2 ∣ q := by
    intro n hn
    obtain ⟨hp, hm, h1, h2⟩ := hS n hn
    exact ⟨hp, (hcon n hp hm h1 h2).1⟩
  have hd := sq_prod_dvd q S hall
  have hle : (∏ n ∈ S, n) ^ 2 ≤ q := Nat.le_of_dvd hq0 hd
  have hprodpos : 0 < ∏ n ∈ S, n := Finset.prod_pos fun n hn => (hall n hn).1.pos
  have hlogsum : ∑ n ∈ S, Real.log n = Real.log ((∏ n ∈ S, n : ℕ) : ℝ) := by
    rw [Nat.cast_prod, Real.log_prod (fun n hn => by
      have := (hall n hn).1.pos
      exact_mod_cast this.ne')]
  have hpos : (0 : ℝ) < ((∏ n ∈ S, n : ℕ) : ℝ) := by exact_mod_cast hprodpos
  have hle' : (((∏ n ∈ S, n : ℕ) : ℝ)) ^ 2 ≤ q := by exact_mod_cast hle
  have h2 := Real.log_le_log (by positivity) hle'
  rw [Real.log_pow, Nat.cast_ofNat] at h2
  linarith

end CatalanLambda.Measure
