module

public import CatalanCore.Zeta5.Data.Final
public import CatalanCore.Uniform.Bank.Irrational

@[expose] public section

/-!
# `μ(ζ(5)) < 87` in the plain form of the other public roots

`zeta5_irrationalityMeasure_87`: for all large `q` and every integer `p`,
`q ^ (-87) < |ζ(5) - p/q|`, with `ζ(5) = ∑' n, 1/(n+1)^5`.

Route (reuse only):
* `zeta5_exact`: the chain of `zeta5_measure_signed` (`Criterion.Signed`), restated with the
  exponent `E = (37/40)(907427/10⁵)/(138500086/10⁸ - 1288003/10⁶) = 839369975/9699786 ≈ 86.5349`
  exposed before the final monotonicity step (parity gain `Apery.parity_gain`, content
  `Content.zc32_signed`, `Λ = 1288003/10⁶`, `ρ = 907427/10⁵`, decay `Data.Design`);
* `irrational_of_family_nnv`: `irrational_of_family_nv0` with the nearby non-vanishing
  hypothesis `HasNearbyNV` in place of `HasNV0` (a rational `x = ζ(5)` is within every window);
* `TrigammaDifferences.Aux.eventually_of_point` (`Bank.Irrational`) gives the plain form.
-/

namespace CatalanCore.Zeta5.Data.Public

open Set CatalanCore.Zeta5.Cells CatalanCore.Zeta5.Potential CatalanCore.Zeta5.Data Polynomial Apery CatalanCore CatalanCore.Uniform CatalanCore.Measure CatalanCore.Zeta5

noncomputable section

/-- Irrationality of the constant from content, window decay and nearby non-vanishing.  This is
the proof of `irrational_of_family_nv0` with the non-vanishing used only at the rational
`x = const`, which lies in every window. -/
theorem irrational_of_family_nnv (Fam : PolyFamily) (scale : Fam.ι → ℕ)
    {Λ D c γ K : ℝ} (hΛ : HasScaledContent Fam scale Λ)
    (hD : HasScaledDecay Fam scale D c) (hη : Λ < D)
    (hγ : 0 < γ) (hK : 0 ≤ K)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ γ * scale n + K)
    (hcov : ∀ R : ℕ, ∃ n, Fam.Adm n ∧ R ≤ scale n)
    (hnn : HasNearbyNV Fam scale c) : Irrational Fam.const := by
  rintro ⟨x, hx⟩
  let θ := (D - Λ) / 2
  let ε := (D - Λ) / 8
  have hθ : 0 < θ := by dsimp [θ]; linarith
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hbudget : θ + 2 * ε ≤ D - Λ := by dsimp [θ, ε]; linarith
  obtain ⟨Rsep, hsep⟩ := scaled_sep Fam scale hΛ hD hε hbudget
  obtain ⟨Rnn, hnn'⟩ := hnn ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((γ + K) * Real.log (x.den : ℝ) / θ)
  obtain ⟨n, hn, hnR⟩ := hcov (max (max Rsep Rnn) (N + 1))
  have hRs : Rsep ≤ scale n := (le_max_left _ _).trans ((le_max_left _ _).trans hnR)
  have hRn : Rnn ≤ scale n := (le_max_right _ _).trans ((le_max_left _ _).trans hnR)
  have hrN : N < scale n := lt_of_lt_of_le (Nat.lt_succ_self N) ((le_max_right _ _).trans hnR)
  have hr1n : 1 ≤ scale n := (show 1 ≤ N + 1 by omega).trans ((le_max_right _ _).trans hnR)
  have hrpos : (0 : ℝ) < scale n := by exact_mod_cast hr1n
  have hr1 : (1 : ℝ) ≤ scale n := by exact_mod_cast hr1n
  have hxrat : ((x.num : ℚ) / (x.den : ℚ)) = x := Rat.num_div_den x
  have hxreal : (x.num : ℝ) / (x.den : ℝ) = Fam.const := by
    rw [← hx]
    exact (Rat.cast_def x).symm
  have hclose0 : |Fam.const - (x : ℝ)| ≤ Real.exp (-(c + ε) * (scale n : ℝ)) := by
    rw [← hx, sub_self, abs_zero]
    exact (Real.exp_pos _).le
  have hne : Fam.evalQ n x ≠ 0 := hnn' n hn hRn x hclose0
  have hclose : |Fam.const - (x.num : ℝ) / (x.den : ℝ)| ≤
      Real.exp (-(c + ε) * (scale n : ℝ)) := by
    rw [hxreal, sub_self, abs_zero]
    exact (Real.exp_pos _).le
  have key := hsep n hn hRs x.num (x.den : ℤ) (by exact_mod_cast x.den_pos)
    (by simpa [hxrat] using hne) (by simpa using hclose)
  simp only [Int.cast_natCast] at key
  have hq1 : (1 : ℝ) ≤ x.den := by exact_mod_cast x.den_pos
  have hlog : 0 ≤ Real.log (x.den : ℝ) := Real.log_nonneg hq1
  have hd := hdeg n hn
  have hd' : (Fam.deg n : ℝ) ≤ (γ + K) * scale n := by nlinarith
  have hup := key.trans (mul_le_mul_of_nonneg_right hd' hlog)
  have hbig : (γ + K) * Real.log (x.den : ℝ) < θ * scale n := by
    have hrN' : (N : ℝ) < scale n := by exact_mod_cast hrN
    have hNr := hN.trans hrN'
    exact (div_lt_iff₀ hθ).mp hNr |>.trans_eq (mul_comm _ _)
  have := mul_lt_mul_of_pos_right hbig hrpos
  nlinarith

/-- The exact exponent: `(37/40) ρ / (D₀ - Λ)` with `ρ = 907427/10⁵`, `D₀ = 138500086/10⁸`,
`Λ = 1288003/10⁶`. -/
def exponentE : ℝ :=
  37 / 40 * (907427 / 10 ^ 5) / (138500086 / 10 ^ 8 - 1288003 / 10 ^ 6)

theorem exponentE_eq : exponentE = 839369975 / 9699786 := by
  unfold exponentE; norm_num

theorem exponentE_lt : exponentE < 87 := by
  unfold exponentE; norm_num

theorem exponentE_nonneg : 0 ≤ exponentE := by
  unfold exponentE; norm_num

/-- **The exact-exponent measure and the irrationality of `ζ(5)`**, from the decay at the
constant `D ≥ 138500086/10⁸`. -/
theorem zeta5_exact {D : ℝ} (hD : DecayAtConst D) (hD0 : 138500086 / 10 ^ 8 ≤ D) :
    MeasureLBAt Apery.zeta5 exponentE ∧ Irrational Apery.zeta5 := by
  have hρ := rhoBound_907427
  obtain ⟨N0, h⟩ := CatalanCore.Zeta5.Content.zc32_signed Apery.parity_gain
  set m : ℕ → ℚ := CatalanCore.Zeta5.Content.mZ with hm
  have hpos : ∀ n, N0 ≤ n → 0 < m n := fun n hn => (h n hn).1
  have hint : ∀ n, N0 ≤ n → ∀ p q : ℤ, 0 < q →
      ∃ z : ℤ, (q : ℚ) ^ (37 * n) * m n * (Apery.F n).eval ((p : ℚ) / q) = z :=
    fun n hn => (h n hn).2.1
  have hlog : ∀ n, N0 ≤ n → Real.log (m n) ≤ (1288003 / 10 ^ 6 : ℝ) * ((40 * n : ℕ) : ℝ) ^ 2 :=
    fun n hn => (h n hn).2.2
  have hΛD : (1288003 / 10 ^ 6 : ℝ) < D := by
    have : (1288003 / 10 ^ 6 : ℝ) < 138500086 / 10 ^ 8 := by norm_num
    linarith
  have hdec := zeta5_hasScaledDecay hρ hD
  have hnn := zeta5_nearbyNV hρ
  have hevalQ : ∀ n x, (signedFamily N0 m).evalQ n x = m n * zeta5Family.evalQ n x := by
    intro n x
    simp [PolyFamily.evalQ, signedFamily, zeta5Family]
  have hΛ' : HasScaledContent (signedFamily N0 m) zeta5Scale 0 := by
    refine ⟨fun _ => 1, fun _ => Nat.one_pos, ?_, ?_⟩
    · intro (n : ℕ) hn p q hq
      obtain ⟨z, hz⟩ := hint n hn p q hq
      refine ⟨z, ?_⟩
      have he : (signedFamily N0 m).evalQ n ((p : ℚ) / q) =
          m n * (Apery.F n).eval ((p : ℚ) / q) := by
        simp [PolyFamily.evalQ, signedFamily]
      show (q : ℚ) ^ (37 * n) * ((1 : ℕ) : ℚ) * (signedFamily N0 m).evalQ n ((p : ℚ) / q) = z
      rw [he, ← hz]
      push_cast
      ring
    · intro ε hε
      refine ⟨0, fun n _ _ => ?_⟩
      simp only [Nat.cast_one, Real.log_one, zero_add]
      positivity
  have hD' : HasScaledDecay (signedFamily N0 m) zeta5Scale (D - 1288003 / 10 ^ 6)
      (907427 / 10 ^ 5) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hdec ε hε
    refine ⟨R0, fun n hn hr t ht => ?_⟩
    have h1 := h n trivial hr t ht
    have hm0 : (0 : ℝ) < (m n : ℝ) := by exact_mod_cast hpos n hn
    have hmle : (m n : ℝ) ≤ Real.exp ((1288003 / 10 ^ 6 : ℝ) * ((zeta5Scale n : ℕ) : ℝ) ^ 2) := by
      have := hlog n hn
      calc (m n : ℝ) = Real.exp (Real.log (m n : ℝ)) := (Real.exp_log hm0).symm
        _ ≤ _ := Real.exp_le_exp.mpr this
    have hev : (signedFamily N0 m).evalR n (Apery.zeta5 + t) =
        (m n : ℝ) * zeta5Family.evalR n (zeta5Family.const + t) := by
      simp [PolyFamily.evalR, signedFamily, zeta5Family]
    have hdef : (signedFamily N0 m).const = Apery.zeta5 := rfl
    rw [hdef, hev, abs_mul, abs_of_pos hm0]
    calc (m n : ℝ) * |zeta5Family.evalR n (zeta5Family.const + t)|
        ≤ Real.exp ((1288003 / 10 ^ 6 : ℝ) * ((zeta5Scale n : ℕ) : ℝ) ^ 2) *
            Real.exp (-(D - ε) * ((zeta5Scale n : ℕ) : ℝ) ^ 2) :=
          mul_le_mul hmle h1 (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (-((D - 1288003 / 10 ^ 6) - ε) * ((zeta5Scale n : ℕ) : ℝ) ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring
  have hnn' : HasNearbyNV (signedFamily N0 m) zeta5Scale (907427 / 10 ^ 5) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hnn ε hε
    refine ⟨R0, fun n hn hr x hx => ?_⟩
    rw [hevalQ]
    exact mul_ne_zero (by exact_mod_cast (hpos n hn).ne') (h n trivial hr x hx)
  have hdeg : ∀ n, (signedFamily N0 m).Adm n →
      ((signedFamily N0 m).deg n : ℝ) ≤ 37 / 40 * (zeta5Scale n : ℝ) + 0 := by
    intro (n : ℕ) _
    show ((37 * n : ℕ) : ℝ) ≤ 37 / 40 * ((40 * n : ℕ) : ℝ) + 0
    push_cast; linarith
  have hmain : (signedFamily N0 m).MeasureLB
      (37 / 40 * (907427 / 10 ^ 5) / ((D - 1288003 / 10 ^ 6) - 0)) := by
    refine measure_of_family_nnv_period (signedFamily N0 m) zeta5Scale 40 (by norm_num)
      (γ := 37 / 40) (K := 0) hΛ' hD' (by linarith) (by norm_num) (by norm_num) le_rfl
      hdeg (fun n _ => ⟨n, rfl⟩) ⟨N0, fun s hs => ⟨s, hs, rfl⟩⟩ hnn'
  refine ⟨?_, ?_⟩
  · rw [MeasureLB_iff, sub_zero] at hmain
    refine MeasureLBAt.mono ?_ hmain
    have hpos' : (0 : ℝ) < 138500086 / 10 ^ 8 - 1288003 / 10 ^ 6 := by norm_num
    have hle : (138500086 / 10 ^ 8 - 1288003 / 10 ^ 6 : ℝ) ≤ D - 1288003 / 10 ^ 6 := by linarith
    exact div_le_div_of_nonneg_left (by norm_num) hpos' hle
  · have hcov : ∀ R : ℕ, ∃ n : ℕ, N0 ≤ n ∧ R ≤ zeta5Scale n := fun R =>
      ⟨max N0 R, le_max_left _ _, by
        unfold zeta5Scale
        have := le_max_right N0 R
        omega⟩
    exact irrational_of_family_nnv (signedFamily N0 m) zeta5Scale hΛ' hD' (by linarith)
      (γ := 37 / 40) (K := 0) (by norm_num) le_rfl hdeg
      hcov hnn'

/-- `Apery.zeta5 = ∑' n, 1/(n+1)^5` (the Port series starts at `n = 0` with the term `1/0 = 0`). -/
theorem zeta5_eq_shift : Apery.zeta5 = ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 5 := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 5) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  unfold Apery.zeta5
  rw [hs.tsum_eq_zero_add]
  simp

/-- **`μ(ζ(5)) < 87`, plain form**: for all large `q` and every integer `p`,
`q^(-87) < |ζ(5) - p/q|`. -/
theorem zeta5_irrationalityMeasure_87 :
    ∀ᶠ q : ℕ in Filter.atTop, ∀ p : ℤ,
      (q : ℝ) ^ (-(87 : ℝ)) < |(∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 5) - (p : ℝ) / q| := by
  have hb : MeasureLBAt Apery.zeta5 exponentE ∧ Irrational Apery.zeta5 := by
    have hyb : (0 : ℝ) < 43 / 50 := by norm_num
    have hT : (4 : ℝ) ≤ ((43 / 50 : ℝ) ^ 2 / 2) * (1 + Real.cosh 3) := four_lt_t_three.le
    have hcell := hcell_of_cells hyb hpos_design hT zd17_design zd18_design
    have hconst := hconst_of_zd22 (c := cR) (N := 60) cR_zero zd22_design
    exact zeta5_exact
      (CatalanCore.Zeta5.Decay.zeta5_decay (b := (43 / 50 : ℝ) ^ 2) (by norm_num) (by norm_num)
        hpos_design cR_zero M0_ge hcell hconst) le_rfl
  rw [← zeta5_eq_shift]
  exact TrigammaDifferences.Aux.eventually_of_point exponentE_nonneg
    (by have := exponentE_lt; exact_mod_cast this) hb

end

end CatalanCore.Zeta5.Data.Public

#print axioms CatalanCore.Zeta5.Data.Public.zeta5_irrationalityMeasure_87
