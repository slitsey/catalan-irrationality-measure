module

public import CatalanCore.Arith.Weights
public import CatalanCore.Basic.Asymptotics
public import CatalanCore.NT.PNTClass
public import CatalanCore.NT.Interval

@[expose] public section

/-!
# The content engine, part 2: growth of `log Dden(h)` by residue classes

Given `ContentData` and a table of residue classes (`GrowthData`), prove
`log Dden(h) ≤ (Λ + ε) h²` eventually, with
`Λ = 2 · (1/φ(M)) · ∑_i I(c_i)`, `I(c) = 1/(2(1+c)) + c/2`.

* λ  : `M = 4`, classes `3` (`c = 4`), `1` (`c = 4/3`), `Λ = 313/105`;
* P6 : `M = 6`, classes `1` (`c = 3`), `5` (`c = 2`),  `Λ = 67/24`.

Input from WP5 (`NT/PNTClass`): `NT.thetaClass_upper`, discharged in `theta_upper_of_pnt`.

Simplification relative to FJ-P6 §5 (design flag F4): no PNT *integral* and no summation by parts.
The pointwise bound `θ(N; M, r) ≤ (1/φ(M) + ε) N + B` is applied to the thresholds
`T_i(h, a) = max(⌊c_i a + d_i⌋, h-1-a)` and the resulting piecewise-linear sum is bounded by the
exact rational `sum_max_le`; the integral `∫ g_c = 1/c + c/(1+c)` of FJ-P6 is the same number as
`I(c)` after the change of variable `θ ↔ a/h`.
-/

open Finset Classical Filter Topology

namespace CatalanCore.Arith

open Basic NT

/-- The content integral `I(c) = 1/(2(1+c)) + c/2`. -/
noncomputable def Icont (c : ℝ) : ℝ := 1 / (2 * (1 + c)) + c / 2

/-- The content constant of a table of classes with equal density `1/φ(M)`:
`Λ = 2 · ∑ density · I(c)`. -/
noncomputable def contentConst (M : ℕ) (cs : List ℝ) : ℝ :=
  2 * (M.totient : ℝ)⁻¹ * (cs.map Icont).sum

/-- 313/105 for λ. -/
theorem contentConst_lambda : contentConst 4 [4, 4 / 3] = 313 / 105 := by
  have : Nat.totient 4 = 2 := by decide
  norm_num [contentConst, Icont, this]

/-- 67/24 for P6. -/
theorem contentConst_p6 : contentConst 6 [3, 2] = 67 / 24 := by
  have : Nat.totient 6 = 2 := by decide
  norm_num [contentConst, Icont, this]

namespace ContentData

variable {Fr : Frame} (cd : ContentData Fr)

/-- Non-prime prime powers `≤ L h` prime to the bad primes. -/
noncomputable def Qnp (h : ℕ) : Finset ℕ := (cd.Qset h).filter (fun q => ¬ q.Prime)

lemma nonprime_part (h a : ℕ) (hh : 1 ≤ h) :
    ∑ q ∈ (cd.Fa h a).filter (fun q => ¬ q.Prime), Real.log (q.minFac : ℝ)
      ≤ (cd.Qnp h).card * Real.log (cd.L * h) := by
  have hL : (1 : ℝ) ≤ cd.L := by exact_mod_cast cd.hL
  have h4 : (1 : ℝ) ≤ cd.L * h := by
    have : (1 : ℝ) ≤ h := by exact_mod_cast hh
    nlinarith
  calc ∑ q ∈ (cd.Fa h a).filter (fun q => ¬ q.Prime), Real.log (q.minFac : ℝ)
      ≤ ∑ q ∈ (cd.Fa h a).filter (fun q => ¬ q.Prime), Real.log ((cd.L * h : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        simp only [Fa, Qset, Finset.mem_filter, Finset.mem_range] at hq
        obtain ⟨⟨⟨hq4, hpp, hbad⟩, hu⟩, hqp⟩ := hq
        have hqpos : 0 < q := hpp.pos
        have : q.minFac ≤ q := Nat.minFac_le hqpos
        apply Real.log_le_log (by exact_mod_cast Nat.minFac_pos q)
        exact_mod_cast (by omega : q.minFac ≤ cd.L * h)
    _ ≤ ∑ q ∈ cd.Qnp h, Real.log ((cd.L * h : ℕ) : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          simp only [Fa, Qnp, Finset.mem_filter] at hq ⊢
          exact ⟨hq.1.1, hq.2⟩
        · intros; exact Real.log_nonneg (by push_cast; exact h4)
    _ = (cd.Qnp h).card * Real.log (cd.L * h) := by
        rw [Finset.sum_const, nsmul_eq_mul]; push_cast; rfl

lemma log_W (h a : ℕ) :
    Real.log (cd.W h a) = Real.log (cd.small h) +
      ∑ q ∈ cd.Fa h a, Real.log (q.minFac : ℝ) := by
  have hq : ∀ q ∈ cd.Fa h a, (q.minFac : ℝ) ≠ 0 := fun q _ => by
    exact_mod_cast (Nat.minFac_pos q).ne'
  have hs : (cd.small h : ℝ) ≠ 0 := by exact_mod_cast (cd.small_pos h).ne'
  have : (cd.W h a : ℝ) = cd.small h * ∏ q ∈ cd.Fa h a, (q.minFac : ℝ) := by
    unfold W Wodd; push_cast; rfl
  have hprod : (∏ q ∈ cd.Fa h a, (q.minFac : ℝ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr hq
  rw [this, Real.log_mul hs hprod, Real.log_prod hq]

lemma log_W_le (h a : ℕ) (hh : 1 ≤ h) :
    Real.log (cd.W h a) ≤ Real.log (cd.small h) +
      ∑ q ∈ (cd.Fa h a).filter Nat.Prime, Real.log (q : ℝ) +
      (cd.Qnp h).card * Real.log (cd.L * h) := by
  rw [log_W]
  rw [← Finset.sum_filter_add_sum_filter_not (cd.Fa h a) Nat.Prime]
  have e : ∑ q ∈ (cd.Fa h a).filter Nat.Prime, Real.log (q.minFac : ℝ)
      = ∑ q ∈ (cd.Fa h a).filter Nat.Prime, Real.log (q : ℝ) := by
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [(Finset.mem_filter.mp hq).2.minFac_eq]
  rw [e]
  have := cd.nonprime_part h a hh
  linarith

lemma log_Dden (h : ℕ) :
    Real.log (cd.Dden h) = 2 * ∑ a ∈ Finset.range h, Real.log (cd.W h a) := by
  have hpos : ∀ a : Fin h, (cd.W h a : ℝ) ≠ 0 := fun a => by
    exact_mod_cast (cd.W_pos h a).ne'
  have : (cd.Dden h : ℝ) = (∏ a : Fin h, (cd.W h a : ℝ)) ^ 2 := by unfold Dden; push_cast; rfl
  rw [this, Real.log_pow, Real.log_prod (fun a _ => hpos a)]
  rw [Fin.sum_univ_eq_sum_range (fun a => Real.log (cd.W h a)) h]
  push_cast; ring

lemma card_Qnp_le (h : ℕ) :
    (cd.Qnp h).card ≤ (Nat.sqrt (cd.L * h) + 1) * (Nat.log 2 (cd.L * h) + 1) := by
  have hsub : cd.Qnp h ⊆ ((Finset.range (Nat.sqrt (cd.L * h) + 1)) ×ˢ
      (Finset.range (Nat.log 2 (cd.L * h) + 1))).image (fun x : ℕ × ℕ => x.1 ^ x.2) := by
    intro q hq
    simp only [Qnp, Qset, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨⟨hq4, hpp, hbad⟩, hnp⟩ := hq
    obtain ⟨p, e, hp0, he, rfl⟩ := hpp
    have hp := hp0.nat_prime
    have he2 : 2 ≤ e := by
      by_contra hlt
      have : e = 1 := by omega
      subst this
      exact hnp (by simpa using hp)
    have hp2 : p ^ 2 ≤ p ^ e := Nat.pow_le_pow_right hp.pos he2
    have hpe : p ^ e ≤ cd.L * h := by omega
    refine Finset.mem_image.mpr ⟨(p, e), ?_, rfl⟩
    simp only [Finset.mem_product, Finset.mem_range]
    constructor
    · have : p * p ≤ cd.L * h := by nlinarith
      have := Nat.le_sqrt.mpr this
      omega
    · have h2e : 2 ^ e ≤ cd.L * h := (Nat.pow_le_pow_left hp.two_le e).trans hpe
      have := Nat.le_log_of_pow_le (by norm_num) h2e
      omega
  calc (cd.Qnp h).card ≤ _ := Finset.card_le_card hsub
    _ ≤ _ := Finset.card_image_le
    _ = _ := by simp

end ContentData

/-- The table of residue classes of an instance. -/
structure GrowthData {Fr : Frame} (cd : ContentData Fr) where
  M : ℕ
  n : ℕ
  res : Fin n → ZMod M
  c : Fin n → ℝ
  d : Fin n → ℝ
  hc : ∀ i, 0 < c i
  hd : ∀ i, 0 ≤ d i
  /-- every prime prime to the bad primes lies in one of the classes -/
  cover : ∀ q : ℕ, q.Prime → (∀ p ∈ cd.bad, ¬ p ∣ q) → ∃ i, (q : ZMod M) = res i
  /-- primes of class `i` that are active through `kq q ≤ a` satisfy `q ≤ c a + d` -/
  thr : ∀ (i : Fin n) (q a : ℕ), q.Prime → (∀ p ∈ cd.bad, ¬ p ∣ q) → (q : ZMod M) = res i →
    cd.kq q ≤ a → (q : ℝ) ≤ c i * a + d i

namespace GrowthData

variable {Fr : Frame} {cd : ContentData Fr} (gd : GrowthData cd)

/-- The content constant of the table. -/
noncomputable def Lam : ℝ := 2 * (gd.M.totient : ℝ)⁻¹ * ∑ i, Icont (gd.c i)

/-- Threshold for prime class `i` at row `a`. -/
noncomputable def T (i : Fin gd.n) (h a : ℕ) : ℕ := max ⌊gd.c i * a + gd.d i⌋₊ (h - 1 - a)

lemma sum_biUnion_le_aux {ι : Type*} (s : Finset ι) (S : ι → Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s.biUnion S, f x ≤ ∑ i ∈ s, ∑ x ∈ S i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hj]
    have := Finset.sum_union_inter (s₁ := S j) (s₂ := s.biUnion S) (f := f)
    have h0 : 0 ≤ ∑ x ∈ S j ∩ s.biUnion S, f x := Finset.sum_nonneg fun x _ => hf x
    linarith

lemma prime_part (h a : ℕ) :
    ∑ q ∈ (cd.Fa h a).filter Nat.Prime, Real.log q ≤
      ∑ i, thetaClassN gd.M (gd.res i) (gd.T i h a) := by
  have hlog : ∀ x : ℕ, 0 ≤ Real.log (x : ℝ) := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hx)
  have hsub : (cd.Fa h a).filter Nat.Prime ⊆ Finset.univ.biUnion (fun i : Fin gd.n =>
      (Finset.range (gd.T i h a + 1)).filter
        (fun n : ℕ => n.Prime ∧ (n : ZMod gd.M) = gd.res i)) := by
    intro q hq
    simp only [ContentData.Fa, ContentData.Qset, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨⟨⟨hq4, hpp, hbad⟩, hu⟩, hqp⟩ := hq
    obtain ⟨i, hi⟩ := gd.cover q hqp hbad
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_range]
    refine ⟨i, ?_, hqp, hi⟩
    unfold T
    rcases hu with hu | hu
    · have := gd.thr i q a hqp hbad hi hu
      have : q ≤ ⌊gd.c i * a + gd.d i⌋₊ := Nat.le_floor this
      omega
    · omega
  calc _ ≤ ∑ x ∈ Finset.univ.biUnion (fun i : Fin gd.n =>
      (Finset.range (gd.T i h a + 1)).filter
        (fun n : ℕ => n.Prime ∧ (n : ZMod gd.M) = gd.res i)), Real.log (x : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun x _ _ => hlog x
    _ ≤ _ := sum_biUnion_le_aux _ _ _ hlog

/-- The linear/constant error of `sum_max_le` for the class `i`. -/
noncomputable def Kc (i : Fin gd.n) : ℝ :=
  |((1 + gd.c i) / 2 - gd.d i) / (1 + gd.c i) - gd.c i / 2 + gd.d i| +
    (((1 + gd.c i) / 2 - gd.d i) ^ 2) / (2 * (1 + gd.c i))

lemma Kc_nonneg (i : Fin gd.n) : 0 ≤ gd.Kc i := by
  have := gd.hc i
  unfold Kc; positivity

lemma sumT_le (i : Fin gd.n) (h : ℕ) :
    ∑ a ∈ Finset.range h, (gd.T i h a : ℝ) ≤ Icont (gd.c i) * (h : ℝ) ^ 2 + gd.Kc i * (h + 1) := by
  have hc := gd.hc i
  have hd := gd.hd i
  have key := sum_max_le (gd.c i) (gd.d i) hc hd h (fun a => (gd.T i h a : ℝ)) (by
    intro a ha
    unfold T
    rw [Nat.cast_max]
    apply max_le_max
    · exact Nat.floor_le (by positivity)
    · have : h - 1 - a + a ≤ h := by omega
      have h2 : ((h - 1 - a : ℕ) : ℝ) + a ≤ h := by exact_mod_cast this
      linarith)
  set u : ℝ := (1 + gd.c i) / 2 - gd.d i with hu
  set lin : ℝ := u / (1 + gd.c i) - gd.c i / 2 + gd.d i with hlin
  have e : ((h : ℝ) + (1 + gd.c i) / 2 - gd.d i) ^ 2 / (2 * (1 + gd.c i)) +
      gd.c i * h * (h - 1) / 2 + gd.d i * h =
      Icont (gd.c i) * (h : ℝ) ^ 2 + lin * h + u ^ 2 / (2 * (1 + gd.c i)) := by
    unfold Icont; rw [hlin, hu]
    have : (1 + gd.c i) ≠ 0 := by positivity
    field_simp
    ring
  rw [e] at key
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hK : 0 ≤ u ^ 2 / (2 * (1 + gd.c i)) := by positivity
  have h1 : lin * h ≤ |lin| * h := mul_le_mul_of_nonneg_right (le_abs_self lin) hh
  have h2 : 0 ≤ |lin| := abs_nonneg _
  have : gd.Kc i = |lin| + u ^ 2 / (2 * (1 + gd.c i)) := rfl
  rw [this]
  nlinarith

/-- A one-sided bound valid for large `N` becomes an affine bound for all `N`. -/
lemma theta_affine (m : ℕ) (r : ZMod m) {cc : ℝ} (hcc : 0 ≤ cc)
    (h : ∀ᶠ N : ℕ in atTop, thetaClassN m r N ≤ cc * N) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, thetaClassN m r N ≤ cc * N + B := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  have hnn : ∀ N, 0 ≤ thetaClassN m r N := fun N =>
    Finset.sum_nonneg fun n hn => by
      have := (Finset.mem_filter.mp hn).2.1.one_lt
      exact Real.log_nonneg (by exact_mod_cast this.le)
  refine ⟨thetaClassN m r N₀, hnn N₀, fun N => ?_⟩
  by_cases hN : N₀ ≤ N
  · have := hN₀ N hN; have := hnn N₀; linarith
  · have hle : N ≤ N₀ := by omega
    have hs := thetaClassN_sub m r hle
    have : 0 ≤ ∑ n ∈ (Finset.Ioc N N₀).filter (fun n : ℕ ↦ n.Prime ∧ (n : ZMod m) = r),
        Real.log n := Finset.sum_nonneg fun n hn => by
      have := (Finset.mem_filter.mp hn).2.1.one_lt
      exact Real.log_nonneg (by exact_mod_cast this.le)
    have : 0 ≤ cc * N := by positivity
    linarith

lemma log_Dden_pointwise (h : ℕ) (hh : 1 ≤ h) {cc : ℝ} (hcc : 0 ≤ cc) (B : Fin gd.n → ℝ)
    (hB0 : ∀ i, 0 ≤ B i) (hB : ∀ i N, thetaClassN gd.M (gd.res i) N ≤ cc * N + B i) :
    Real.log (cd.Dden h) ≤
      2 * h * (Real.log (cd.small h) + (cd.Qnp h).card * Real.log (cd.L * h)) +
      2 * cc * (∑ i, Icont (gd.c i)) * (h : ℝ) ^ 2 +
      2 * (cc * ∑ i, gd.Kc i + ∑ i, B i) * (h + 1) := by
  set E : ℝ := Real.log (cd.small h) + (cd.Qnp h).card * Real.log (cd.L * h) with hE
  have step : ∀ a ∈ Finset.range h, Real.log (cd.W h a) ≤
      E + ∑ i, (cc * (gd.T i h a : ℝ) + B i) := by
    intro a _
    have h1 := cd.log_W_le h a hh
    have h2 := gd.prime_part h a
    have h3 : ∑ i, thetaClassN gd.M (gd.res i) (gd.T i h a) ≤
        ∑ i, (cc * (gd.T i h a : ℝ) + B i) :=
      Finset.sum_le_sum fun i _ => hB i _
    linarith
  have hsum : ∑ a ∈ Finset.range h, Real.log (cd.W h a) ≤
      ∑ a ∈ Finset.range h, (E + ∑ i, (cc * (gd.T i h a : ℝ) + B i)) :=
    Finset.sum_le_sum step
  have hcomm : ∑ a ∈ Finset.range h, ∑ i, (cc * (gd.T i h a : ℝ) + B i) =
      ∑ i, (cc * ∑ a ∈ Finset.range h, (gd.T i h a : ℝ) + h * B i) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hT : ∑ i, (cc * ∑ a ∈ Finset.range h, (gd.T i h a : ℝ) + h * B i) ≤
      ∑ i, (cc * (Icont (gd.c i) * (h : ℝ) ^ 2 + gd.Kc i * (h + 1)) + h * B i) :=
    Finset.sum_le_sum fun i _ => by
      have := gd.sumT_le i h
      have := mul_le_mul_of_nonneg_left this hcc
      linarith
  have hexp : ∑ i, (cc * (Icont (gd.c i) * (h : ℝ) ^ 2 + gd.Kc i * (h + 1)) + h * B i) =
      cc * (∑ i, Icont (gd.c i)) * (h : ℝ) ^ 2 + cc * (∑ i, gd.Kc i) * (h + 1) +
        (∑ i, B i) * h := by
    have e : ∀ i, cc * (Icont (gd.c i) * (h : ℝ) ^ 2 + gd.Kc i * (h + 1)) + h * B i =
        (cc * (h : ℝ) ^ 2) * Icont (gd.c i) + (cc * (h + 1)) * gd.Kc i + h * B i := fun i => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, hcomm] at hsum
  rw [cd.log_Dden]
  have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have hsB : 0 ≤ ∑ i, B i := Finset.sum_nonneg fun i _ => hB0 i
  linarith [hsum, hT, hexp]

lemma Icont_pos {c : ℝ} (hc : 0 < c) : 0 < Icont c := by
  unfold Icont; positivity

/-- **Growth of the denominators, by residue classes.**  Input: the upper Chebyshev bound
`θ(N; M, r_i) ≤ (1/φ(M) + ε) N` eventually, for every class of the table. -/
theorem log_Dden_le
    (hθ : ∀ i : Fin gd.n, ∀ ε : ℝ, 0 < ε →
      ∀ᶠ N : ℕ in atTop, thetaClassN gd.M (gd.res i) N ≤ ((gd.M.totient : ℝ)⁻¹ + ε) * N)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℕ in atTop, Real.log (cd.Dden h) ≤ (gd.Lam + ε) * (h : ℝ) ^ 2 := by
  set D : ℝ := (gd.M.totient : ℝ)⁻¹ with hD
  have hD0 : 0 ≤ D := inv_nonneg.mpr (Nat.cast_nonneg _)
  set S : ℝ := ∑ i, Icont (gd.c i) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => (Icont_pos (gd.hc i)).le
  set ε' : ℝ := ε / (4 * (S + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  choose B hB0 hB using fun i : Fin gd.n =>
    theta_affine gd.M (gd.res i) (cc := D + ε') (by positivity) (hθ i ε' hε'0)
  set Kt : ℝ := ∑ i, gd.Kc i with hKt
  have hKt0 : 0 ≤ Kt := Finset.sum_nonneg fun i _ => gd.Kc_nonneg i
  set Bt : ℝ := ∑ i, B i with hBt
  have hBt0 : 0 ≤ Bt := Finset.sum_nonneg fun i _ => hB0 i
  set Q : ℝ := 2 * ((D + ε') * Kt + Bt) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  obtain ⟨A, C, hAC⟩ := cd.small_poly
  have hA1 : 1 ≤ A := by
    by_contra hA
    have h0 : A = 0 := by omega
    have := hAC 0
    have := cd.small_pos 0
    simp [h0] at *
    omega
  have tc : Tendsto (fun h : ℕ => (h : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hδC : 0 < ε / (64 * ((C : ℝ) + 1)) := by positivity
  have e2 := ev_sqrt_log_small cd.hL (show 0 < ε / 16 by positivity)
  have e3a : ∀ᶠ h : ℕ in atTop, Real.log (((h + 1 : ℕ)) : ℝ) ≤
      ε / (64 * ((C : ℝ) + 1)) * ((h + 1 : ℕ) : ℝ) :=
    ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).eventually (ev_log_le hδC))
  have e3b : ∀ᶠ h : ℕ in atTop, 32 * Real.log A ≤ ε * h :=
    tc.eventually_ge_atTop (32 * Real.log A / ε) |>.mono fun h hh => by
      rw [div_le_iff₀ hε] at hh; linarith
  have e4 : ∀ᶠ h : ℕ in atTop, 8 * Q ≤ ε * h :=
    tc.eventually_ge_atTop (8 * Q / ε) |>.mono fun h hh => by
      rw [div_le_iff₀ hε] at hh; linarith
  filter_upwards [e2, e3a, e3b, e4, eventually_ge_atTop 1] with h h2 h3a h3b h4 h1
  have hh1 : (1 : ℝ) ≤ h := by exact_mod_cast h1
  have hpt := gd.log_Dden_pointwise h h1 (cc := D + ε') (by positivity) B hB0 hB
  -- the small-prime weight
  have hsmall : Real.log (cd.small h) ≤ ε / 16 * h := by
    have hpos : (0 : ℝ) < cd.small h := by exact_mod_cast cd.small_pos h
    have hle : (cd.small h : ℝ) ≤ A * ((h : ℝ) + 1) ^ C := by exact_mod_cast hAC h
    have hA0 : (0 : ℝ) < A := by exact_mod_cast hA1
    have : Real.log (cd.small h) ≤ Real.log A + C * Real.log ((h : ℝ) + 1) := by
      calc _ ≤ Real.log (A * ((h : ℝ) + 1) ^ C) := Real.log_le_log hpos hle
        _ = _ := by rw [Real.log_mul hA0.ne' (by positivity), Real.log_pow]
    push_cast at h3a
    have hC : (C : ℝ) * Real.log ((h : ℝ) + 1) ≤ ε / 32 * h := by
      have h5 : (C : ℝ) * Real.log ((h : ℝ) + 1) ≤
          (C : ℝ) * (ε / (64 * ((C : ℝ) + 1)) * ((h : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left h3a (Nat.cast_nonneg C)
      have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
      have h6 : (C : ℝ) * (ε / (64 * ((C : ℝ) + 1)) * ((h : ℝ) + 1)) =
          ε * ((C : ℝ) / ((C : ℝ) + 1)) * ((h : ℝ) + 1) / 64 := by
        field_simp
      have h7 : (C : ℝ) / ((C : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have h8 : ε * ((C : ℝ) / ((C : ℝ) + 1)) ≤ ε := by nlinarith
      have h9 := mul_le_mul_of_nonneg_right h8 (by positivity : (0 : ℝ) ≤ (h : ℝ) + 1)
      have h10 := mul_le_mul_of_nonneg_left hh1 hε.le
      linarith
    linarith [h3b]
  have hcard : (cd.Qnp h).card * Real.log (cd.L * h) ≤ ε / 16 * h := by
    have hL : (1 : ℝ) ≤ cd.L := by exact_mod_cast cd.hL
    have hlog0 : 0 ≤ Real.log ((cd.L : ℝ) * h) := Real.log_nonneg (by nlinarith)
    have hc : ((cd.Qnp h).card : ℝ) ≤ ((Nat.sqrt (cd.L * h) : ℝ) + 1) *
        ((Nat.log 2 (cd.L * h) : ℝ) + 1) := by exact_mod_cast cd.card_Qnp_le h
    calc _ ≤ ((Nat.sqrt (cd.L * h) : ℝ) + 1) * ((Nat.log 2 (cd.L * h) : ℝ) + 1) *
          Real.log ((cd.L : ℝ) * h) := mul_le_mul_of_nonneg_right hc hlog0
      _ ≤ _ := h2
  have hE : 2 * (h : ℝ) * (Real.log (cd.small h) + (cd.Qnp h).card * Real.log (cd.L * h))
      ≤ ε / 4 * (h : ℝ) ^ 2 := by
    calc _ ≤ 2 * (h : ℝ) * (ε / 16 * h + ε / 16 * h) :=
          mul_le_mul_of_nonneg_left (add_le_add hsmall hcard) (by positivity)
      _ = _ := by ring
  have hLam : gd.Lam = 2 * D * S := by simp [Lam, hD, hS]
  have hQh : Q * ((h : ℝ) + 1) ≤ ε / 4 * (h : ℝ) ^ 2 := by
    have a1 : Q * ((h : ℝ) + 1) ≤ Q * (2 * h) := mul_le_mul_of_nonneg_left (by linarith) hQ0
    have a2 := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ h)
    nlinarith
  have hS' : 2 * ε' * S * (h : ℝ) ^ 2 ≤ ε / 2 * (h : ℝ) ^ 2 := by
    have : 2 * ε' * S ≤ ε / 2 := by
      rw [hε']
      rw [show 2 * (ε / (4 * (S + 1))) * S = ε / 2 * (S / (S + 1)) by field_simp; ring]
      have : S / (S + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hexp : 2 * (D + ε') * S * (h : ℝ) ^ 2 = gd.Lam * (h : ℝ) ^ 2 + 2 * ε' * S * (h : ℝ) ^ 2 := by
    rw [hLam]; ring
  have hQe : 2 * ((D + ε') * Kt + Bt) * ((h : ℝ) + 1) = Q * ((h : ℝ) + 1) := by rw [hQ]
  linarith [hpt, hE, hQh, hS', hexp, hQe]

end GrowthData




end CatalanCore.Arith

namespace CatalanCore.Arith

open NT in
/-- The Chebyshev upper bound in the `ℕ`-indexed form used above, from WP5's `thetaClass_upper`. -/
theorem theta_upper_nat {m : ℕ} [NeZero m] {r : ZMod m} (hr : IsUnit r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, thetaClassN m r N ≤ ((m.totient : ℝ)⁻¹ + ε) * N := by
  have := (thetaClass_upper hr hε)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually this] with N hN
  simpa [thetaClass] using hN

variable {Fr : Frame} {cd : ContentData Fr}

/-- **`content_const`**: the engine proves `HasContent` with `Λ = 2 · (1/φ(M)) · ∑ I(c_i)`,
given only the table of classes and the unit-ness of the residues. -/
theorem hasContent_of_classes (gd : GrowthData cd) [NeZero gd.M]
    (hunit : ∀ i, IsUnit (gd.res i)) : HasContent (PolyFamily.ofFrame Fr) gd.Lam := by
  refine ⟨cd.Dden, cd.Dden_pos, fun n _ p q hq => integrality_of cd n p q hq, ?_⟩
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (gd.log_Dden_le (fun i ε' hε' => theta_upper_nat (hunit i) hε') hε)
  exact ⟨N₀, fun n _ hn => hN₀ n hn⟩

end CatalanCore.Arith
