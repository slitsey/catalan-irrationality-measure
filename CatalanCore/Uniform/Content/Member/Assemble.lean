module

public import CatalanCore.Uniform.Content.Member.Template
public import CatalanCore.Arith.Hybrid.PrimeDenominator
public import CatalanCore.Frame.Spec

@[expose] public section

/-!
# From per-prime prices to `HasContent` (lane H5, generic assembler)

For an arbitrary polynomial family `Fam`, a scale function `sc`, a modulus `M` and class templates
(`Template`), the data `ContentCover` says:

* `gle`: at every prime `p` the member polynomial is `p^(price i p)`-integral (this is the
  per-prime minimum of the proved layers, produced by `Layers`);
* `pre`, `cov`, `tail`: for every unit class `c` mod `M`, the price is bounded by the exact
  piecewise-linear template of the class (constant prefix, linear pieces, then zero);
* `exc`: the finitely many primes dividing `M` carry at most `K · sc i` each.

Then `HasContent Fam (γ² · contentConstant M tmpl)`, where `sc i ≤ γ · deg i + K0` and
`deg i ≤ γ' · sc i + K1`.  The proof is the class-total engine (`class_total`, PNT on intervals
in residue classes) summed over the unit classes; nothing is specific to a frame, a block
geometry or a layer.
-/

open CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Basic Filter Finset Polynomial

namespace CatalanCore.Uniform.Content.Member

/-- Clearing a bounded-degree polynomial with a common denominator at a rational point. -/
theorem int_clear' (P : ℚ[X]) (r : ℕ) (hP : P.natDegree ≤ r) (D : ℕ)
    (hD : ∀ i, ∃ z : ℤ, (D : ℚ) * P.coeff i = z) (p q : ℤ) (hq : 0 < q) :
    ∃ z : ℤ, (q : ℚ) ^ r * D * P.eval ((p : ℚ) / q) = z := by
  choose z hz using hD
  refine ⟨∑ i ∈ range (r + 1), z i * p ^ i * q ^ (r - i), ?_⟩
  rw [Polynomial.eval_eq_sum_range' (n := r + 1) (by omega), Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hi' : i ≤ r := by have := Finset.mem_range.1 hi; omega
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have e : (q : ℚ) ^ r = q ^ (r - i) * q ^ i := by rw [← pow_add]; congr 1; omega
  rw [← hz i, e, div_pow]
  field_simp

/-- A fixed affine error is absorbed by an arbitrarily small quadratic loss. -/
theorem affine_le_quadratic (A B ε : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ R0 : ℕ, ∀ r : ℕ, R0 ≤ r → A * r + B ≤ ε * (r : ℝ) ^ 2 := by
  refine ⟨max 1 ⌈(A + B) / ε⌉₊, ?_⟩
  intro r hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (le_max_left _ _).trans hr
  have hrbound : (A + B) / ε ≤ (r : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hr)
  have hmul : A + B ≤ ε * r := by
    have := (div_le_iff₀ hε).mp hrbound
    nlinarith
  have hB' : B ≤ B * r := by nlinarith
  have hmain := mul_le_mul_of_nonneg_right hmul (by linarith : (0 : ℝ) ≤ r)
  nlinarith

variable {Fam : PolyFamily} {sc : Fam.ι → ℕ} {M : ℕ} [NeZero M]

/-- **The cover data.**  See the module header. -/
structure ContentCover (Fam : PolyFamily) (sc : Fam.ι → ℕ) (M : ℕ) [NeZero M] where
  tmpl : ZMod M → Template
  price : Fam.ι → ℕ → ℕ
  K : ℝ
  hK : 0 ≤ K
  gle : ∀ i, Fam.Adm i → ∀ (p : ℕ) [Fact p.Prime], GLE p (price i p) (Fam.Q i)
  tail : ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ, p.Prime → (p : ZMod M) = c →
    ⌊(tmpl c).tend * sc i⌋₊ < p → price i p = 0
  pre : ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ p : ℕ,
    p ≤ ⌊(tmpl c).t1 * sc i⌋₊ → p.Prime → (p : ZMod M) = c →
      (price i p : ℝ) ≤ (tmpl c).α0 * sc i
  cov : ∀ i, Fam.Adm i → ∀ c : ZMod M, IsUnit c → ∀ P ∈ (tmpl c).l,
    Covers c (fun p => (price i p : ℝ)) (sc i) P
  exc : ∀ i, Fam.Adm i → ∀ p : ℕ, p.Prime → p ∣ M → (price i p : ℝ) ≤ K * sc i

namespace ContentCover

variable (CC : ContentCover Fam sc M)

/-- The prime cutoff of the denominator. -/
noncomputable def bound (i : Fam.ι) : ℕ := ⌊commonEnd M CC.tmpl * sc i⌋₊ + M + 1

/-- The explicit denominator `∏_{p < bound} p^(price i p)`. -/
noncomputable def Dden (i : Fam.ι) : ℕ := primeDenominator (CC.bound i) (CC.price i)

lemma Dden_pos (i : Fam.ι) : 0 < CC.Dden i := primeDenominator_pos _ _

lemma floor_tend_lt_bound (i : Fam.ι) (c : ZMod M) :
    ⌊(CC.tmpl c).tend * sc i⌋₊ < CC.bound i := by
  have h1 : (CC.tmpl c).tend * sc i ≤ commonEnd M CC.tmpl * sc i :=
    mul_le_mul_of_nonneg_right (tend_le_commonEnd M CC.tmpl c) (Nat.cast_nonneg _)
  have h2 := Nat.floor_le_floor h1
  unfold bound
  omega

lemma price_zero_of_ge {i : Fam.ι} (hi : Fam.Adm i) {p : ℕ} (hp : p.Prime)
    (h : CC.bound i ≤ p) : CC.price i p = 0 := by
  by_cases hd : p ∣ M
  · have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hd
    unfold bound at h
    omega
  · have hc : IsUnit (p : ZMod M) := (ZMod.isUnit_prime_iff_not_dvd hp).2 hd
    exact CC.tail i hi (p : ZMod M) hc p hp rfl
      (lt_of_lt_of_le (CC.floor_tend_lt_bound i _) h)

lemma Dden_integral {i : Fam.ι} (hi : Fam.Adm i) (k : ℕ) :
    ∃ z : ℤ, (CC.Dden i : ℚ) * (Fam.Q i).coeff k = z := by
  refine primeDenominator_integral (CC.bound i) (CC.price i) (Fam.Q i) ?_ k
  intro p hp
  by_cases hb : p < CC.bound i
  · simpa only [if_pos hb] using CC.gle i hi p
  · have h0 := CC.price_zero_of_ge hi hp.out (not_lt.mp hb)
    have := CC.gle i hi p
    rw [h0] at this
    simpa only [if_neg hb] using this

lemma log_Dden_eq (i : Fam.ι) :
    Real.log (CC.Dden i) =
      ∑ p ∈ (range (CC.bound i)).filter Nat.Prime, (CC.price i p : ℝ) * Real.log p :=
  log_primeDenominator _ _

/-- The unit-class fiber of the prime sum is the class sum. -/
lemma fiber_eq_clsSum {i : Fam.ι} (hi : Fam.Adm i) {c : ZMod M} (hc : IsUnit c) :
    ∑ p ∈ (((range (CC.bound i)).filter Nat.Prime).filter (fun p => ¬ p ∣ M)).filter
        (fun p : ℕ => (p : ZMod M) = c), (CC.price i p : ℝ) * Real.log p =
      clsSum M c (fun p => (CC.price i p : ℝ)) 0 ⌊(CC.tmpl c).tend * sc i⌋₊ := by
  unfold clsSum
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range] at hp ⊢
    obtain ⟨⟨hp0, hpB⟩, hpp, hpc⟩ := hp
    refine ⟨⟨⟨?_, hpp⟩, ?_⟩, hpc⟩
    · exact lt_of_le_of_lt hpB (CC.floor_tend_lt_bound i c)
    · rw [← ZMod.isUnit_prime_iff_not_dvd hpp, hpc]; exact hc
  · intro p hp hpn
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range, not_and] at hp hpn
    obtain ⟨⟨⟨hpb, hpp⟩, hpd⟩, hpc⟩ := hp
    have hB : ⌊(CC.tmpl c).tend * sc i⌋₊ < p := by
      by_contra hcon
      exact hpn ⟨hpp.pos, not_lt.mp hcon⟩ hpp hpc
    have h0 := CC.tail i hi c hc p hpp hpc hB
    simp only [h0, Nat.cast_zero, zero_mul]

end ContentCover

lemma eventually_classes (tmpl : ZMod M → Template) {ε1 : ℝ} (hε1 : 0 < ε1) :
    ∀ᶠ r : ℕ in atTop, ∀ c ∈ unitClasses M, ∀ w : ℕ → ℝ,
      (∀ p, p ≤ ⌊(tmpl c).t1 * r⌋₊ → p.Prime → (p : ZMod M) = c → w p ≤ (tmpl c).α0 * r) →
      (∀ P ∈ (tmpl c).l, Covers c w r P) →
      clsSum M c w 0 ⌊(tmpl c).tend * r⌋₊ ≤
        (r : ℝ) ^ 2 * ((tmpl c).mass / (M.totient : ℝ) + ε1) := by
  rw [Filter.eventually_all_finset]
  intro c hc
  exact class_total (mem_unitClasses.1 hc) (tmpl c).hα0 (tmpl c).ht1 (tmpl c).l
    (tmpl c).chain hε1

namespace ContentCover

variable (CC : ContentCover Fam sc M)

/-- The prime sum splits into the exceptional primes (dividing `M`) and the unit classes. -/
lemma log_Dden_le_aux {i : Fam.ι} (hi : Fam.Adm i) {ε1 : ℝ} (hε1 : 0 ≤ ε1)
    (H : ∀ c ∈ unitClasses M,
      clsSum M c (fun p => (CC.price i p : ℝ)) 0 ⌊(CC.tmpl c).tend * sc i⌋₊ ≤
        (sc i : ℝ) ^ 2 * ((CC.tmpl c).mass / (M.totient : ℝ) + ε1)) :
    Real.log (CC.Dden i) ≤
      (sc i : ℝ) ^ 2 * (contentConstant M CC.tmpl + M * ε1) +
        ((M : ℝ) + 1) * CC.K * sc i * Real.log M := by
  classical
  rw [CC.log_Dden_eq]
  set S := (range (CC.bound i)).filter Nat.Prime with hS
  set g : ℕ → ℝ := fun p => (CC.price i p : ℝ) * Real.log p with hg
  have hlog0 : ∀ p ∈ S, 0 ≤ Real.log p := fun p hp =>
    Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
  rw [← Finset.sum_filter_add_sum_filter_not S (fun p => p ∣ M) g]
  -- exceptional part
  have hexc : ∑ p ∈ S.filter (fun p => p ∣ M), g p ≤
      ((M : ℝ) + 1) * CC.K * sc i * Real.log M := by
    have hterm : ∀ p ∈ S.filter (fun p => p ∣ M), g p ≤ CC.K * sc i * Real.log M := by
      intro p hp
      obtain ⟨hpS, hpd⟩ := Finset.mem_filter.mp hp
      have hpp : p.Prime := (Finset.mem_filter.mp hpS).2
      have hpM : p ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpd
      have hlogle : Real.log p ≤ Real.log M :=
        Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hpM)
      have hKsc : 0 ≤ CC.K * sc i := mul_nonneg CC.hK (Nat.cast_nonneg _)
      calc g p = (CC.price i p : ℝ) * Real.log p := rfl
        _ ≤ CC.K * sc i * Real.log M :=
          mul_le_mul (CC.exc i hi p hpp hpd) hlogle
            (Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)) hKsc
    have hcard : (S.filter (fun p => p ∣ M)).card ≤ M + 1 := by
      have hsub : S.filter (fun p => p ∣ M) ⊆ range (M + 1) := by
        intro p hp
        obtain ⟨-, hpd⟩ := Finset.mem_filter.mp hp
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hpd
        exact Finset.mem_range.2 (by omega)
      simpa using Finset.card_le_card hsub
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg (by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M))
    have hKsc : 0 ≤ CC.K * sc i * Real.log M :=
      mul_nonneg (mul_nonneg CC.hK (Nat.cast_nonneg _)) hlogM
    calc ∑ p ∈ S.filter (fun p => p ∣ M), g p
        ≤ (S.filter (fun p => p ∣ M)).card • (CC.K * sc i * Real.log M) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ = ((S.filter (fun p => p ∣ M)).card : ℝ) * (CC.K * sc i * Real.log M) := by
          rw [nsmul_eq_mul]
      _ ≤ ((M : ℝ) + 1) * (CC.K * sc i * Real.log M) := by
          apply mul_le_mul_of_nonneg_right _ hKsc
          exact_mod_cast hcard
      _ = _ := by ring
  -- unit part
  have hmaps : ∀ p ∈ S.filter (fun p => ¬ p ∣ M), (p : ZMod M) ∈ unitClasses M := by
    intro p hp
    obtain ⟨hpS, hpd⟩ := Finset.mem_filter.mp hp
    exact mem_unitClasses.2 ((ZMod.isUnit_prime_iff_not_dvd (Finset.mem_filter.mp hpS).2).2 hpd)
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p : ℕ => (p : ZMod M)) hmaps g]
  have hunit : ∑ c ∈ unitClasses M, ∑ p ∈ (S.filter (fun p => ¬ p ∣ M)).filter
        (fun p : ℕ => (p : ZMod M) = c), g p ≤
      (sc i : ℝ) ^ 2 * (contentConstant M CC.tmpl + M * ε1) := by
    have h1 : ∀ c ∈ unitClasses M, ∑ p ∈ (S.filter (fun p => ¬ p ∣ M)).filter
        (fun p : ℕ => (p : ZMod M) = c), g p ≤
        (sc i : ℝ) ^ 2 * ((CC.tmpl c).mass / (M.totient : ℝ) + ε1) := by
      intro c hc
      have := CC.fiber_eq_clsSum hi (mem_unitClasses.1 hc)
      exact this.le.trans (H c hc)
    calc _ ≤ ∑ c ∈ unitClasses M, (sc i : ℝ) ^ 2 * ((CC.tmpl c).mass / (M.totient : ℝ) + ε1) :=
          Finset.sum_le_sum h1
      _ = (sc i : ℝ) ^ 2 * (contentConstant M CC.tmpl + (unitClasses M).card * ε1) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            contentConstant, Finset.sum_div]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          have : ((unitClasses M).card : ℝ) ≤ M := by exact_mod_cast card_unitClasses_le M
          nlinarith
  linarith

/-- **Main assembler.**  The cover data gives `HasContent` for the family, with the content
constant `γ² · contentConstant M tmpl`. -/
theorem hasContent_of_cover (CC : ContentCover Fam sc M)
    (hnat : ∀ i, (Fam.Q i).natDegree ≤ Fam.deg i)
    {γ γ' K0 K1 : ℝ} (hγ : 0 ≤ γ) (hγ' : 0 < γ') (hK0 : 0 ≤ K0) (hK1 : 0 ≤ K1)
    (hsc : ∀ i, Fam.Adm i → (sc i : ℝ) ≤ γ * Fam.deg i + K0)
    (hdeg : ∀ i, Fam.Adm i → (Fam.deg i : ℝ) ≤ γ' * sc i + K1) :
    HasContent Fam (γ ^ 2 * contentConstant M CC.tmpl) := by
  refine ⟨CC.Dden, CC.Dden_pos, ?_, ?_⟩
  · intro i hi p q hq
    exact int_clear' (Fam.Q i) (Fam.deg i) (hnat i) (CC.Dden i) (CC.Dden_integral hi) p q hq
  · intro ε hε
    set Λs := contentConstant M CC.tmpl with hΛs
    have hΛs0 : 0 ≤ Λs := contentConstant_nonneg M CC.tmpl
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
    set ε1 : ℝ := ε / (4 * ((M : ℝ) + 1) * (γ ^ 2 + 1)) with hε1def
    have hε1 : 0 < ε1 := by positivity
    have hε1small : (M : ℝ) * ε1 * γ ^ 2 ≤ ε / 4 := by
      have hfrac : (M : ℝ) * γ ^ 2 ≤ ((M : ℝ) + 1) * (γ ^ 2 + 1) := by nlinarith [sq_nonneg γ]
      have hden : 0 < 4 * ((M : ℝ) + 1) * (γ ^ 2 + 1) := by positivity
      have e : (M : ℝ) * ε1 * γ ^ 2 = ε * ((M : ℝ) * γ ^ 2) / (4 * ((M : ℝ) + 1) * (γ ^ 2 + 1)) := by
        rw [hε1def]; field_simp
      rw [e, div_le_iff₀ hden]
      nlinarith
    obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 (eventually_classes CC.tmpl hε1)
    set A : ℝ := Λs + M * ε1 with hA
    have hA0 : 0 ≤ A := by positivity
    set E : ℝ := ((M : ℝ) + 1) * CC.K * Real.log M with hE
    have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM1
    have hE0 : 0 ≤ E := by
      have := CC.hK
      positivity
    obtain ⟨R2, hR2⟩ := affine_le_quadratic (A * (2 * γ * K0) + E * γ) (A * K0 ^ 2 + E * K0)
      (ε / 2) (by positivity) (by positivity) (by positivity)
    refine ⟨max R2 ⌈γ' * R + K1⌉₊, ?_⟩
    intro i hi hd
    have hd2 : R2 ≤ Fam.deg i := (le_max_left _ _).trans hd
    have hd1 : ⌈γ' * R + K1⌉₊ ≤ Fam.deg i := (le_max_right _ _).trans hd
    have hdR : γ' * R + K1 ≤ (Fam.deg i : ℝ) := (Nat.ceil_le).1 hd1
    have hRsc : R ≤ sc i := by
      have h1 := hdeg i hi
      have h2 : γ' * (R : ℝ) ≤ γ' * sc i := by linarith
      have h3 : (R : ℝ) ≤ sc i := le_of_mul_le_mul_left h2 hγ'
      exact_mod_cast h3
    have hH := hR (sc i) hRsc
    have hmain := CC.log_Dden_le_aux hi hε1.le (fun c hc => hH c hc _
      (CC.pre i hi c (mem_unitClasses.1 hc)) (CC.cov i hi c (mem_unitClasses.1 hc)))
    have hr0 : (0 : ℝ) ≤ sc i := Nat.cast_nonneg _
    have hd0 : (0 : ℝ) ≤ Fam.deg i := Nat.cast_nonneg _
    have hr := hsc i hi
    have hsq : (sc i : ℝ) ^ 2 ≤ (γ * Fam.deg i + K0) ^ 2 := pow_le_pow_left₀ hr0 hr 2
    have hlin := hR2 (Fam.deg i) hd2
    have h1 : (sc i : ℝ) ^ 2 * A ≤ (γ * Fam.deg i + K0) ^ 2 * A :=
      mul_le_mul_of_nonneg_right hsq hA0
    have h2 : E * (sc i : ℝ) ≤ E * (γ * Fam.deg i + K0) := mul_le_mul_of_nonneg_left hr hE0
    have hexp : (γ * Fam.deg i + K0) ^ 2 * A = A * γ ^ 2 * (Fam.deg i : ℝ) ^ 2 +
        A * (2 * γ * K0) * Fam.deg i + A * K0 ^ 2 := by ring
    have hAγ : A * γ ^ 2 ≤ γ ^ 2 * Λs + ε / 4 := by
      have : A * γ ^ 2 = γ ^ 2 * Λs + (M : ℝ) * ε1 * γ ^ 2 := by rw [hA]; ring
      linarith
    have hd2' : A * γ ^ 2 * (Fam.deg i : ℝ) ^ 2 ≤ (γ ^ 2 * Λs + ε / 4) * (Fam.deg i : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hAγ (sq_nonneg _)
    have hq : 0 ≤ (Fam.deg i : ℝ) ^ 2 := sq_nonneg _
    have hmain' : Real.log (CC.Dden i) ≤ (sc i : ℝ) ^ 2 * A + E * sc i := by
      have : (sc i : ℝ) ^ 2 * (Λs + M * ε1) + ((M : ℝ) + 1) * CC.K * sc i * Real.log M =
          (sc i : ℝ) ^ 2 * A + E * sc i := by rw [hA, hE]; ring
      linarith
    nlinarith [hmain', h1, h2, hexp, hd2', hlin, hq]


end ContentCover

end CatalanCore.Uniform.Content.Member
