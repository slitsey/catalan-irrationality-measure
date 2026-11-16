module

public import CatalanCore.Zeta5.Criterion.Final
public import CatalanCore.Zeta5.Content.Final

@[expose] public section

/-!
# The signed-normaliser criterion (ledger ZA17, signed form)

The content side (`CatalanCore.Zeta5.Content.zc32_signed`) supplies a positive *rational*
normaliser `m n` with `q^(37 n) · m n · F_n(p/q) ∈ ℤ` and `log (m n) ≤ Λ (40 n)²`, whose natural
multiples are too large.  Route (b): rescale the family to `Q n = m n · F n`.  Its content is
trivial (`den = 1`, `Λ' = 0`), its decay is `D' = D - Λ`, and the exponent is the same
`37/40 · ρ / (D - Λ)`.  The generic period criterion `measure_of_family_nnv_period` is reused
unchanged.

* `signedFamily N0 m`: `Q n = C (m n) · F n`, admissible for `n ≥ N0`.
* `zeta5_measure_signed`: `MeasureLBAt ζ(5) 87` from the signed content hypotheses.
* `zeta5_measure_of_parity`: the composite with `zc32_signed`; the only open input is `hpar`.
-/

open Polynomial Apery CatalanCore CatalanCore.Uniform CatalanCore.Measure

namespace CatalanCore.Zeta5

/-- Fauzan's family rescaled by the rational normaliser: `Q n = m n · F_n`, admissible for
`n ≥ N0`. -/
noncomputable def signedFamily (N0 : ℕ) (m : ℕ → ℚ) : PolyFamily where
  const := Apery.zeta5
  ι := ℕ
  deg := fun n => 37 * n
  Adm := fun n => N0 ≤ n
  Q := fun n => C (m n) * Apery.F n

/-- **ZA17 (signed form).**  Positive rational normaliser `m` with integrality
`q^(37 n) m n F_n(p/q) ∈ ℤ` and `log (m n) ≤ Λ (40 n)²` for `n ≥ N0`, `Λ ≤ 1288519/10⁶`;
decay at the constant `D ≥ 138500086/10⁸`; the ρ bound.  Then `μ(ζ(5)) ≤ 87`. -/
theorem zeta5_measure_signed {Λ D : ℝ} (N0 : ℕ) (m : ℕ → ℚ)
    (hpos : ∀ n, N0 ≤ n → 0 < m n)
    (hint : ∀ n, N0 ≤ n → ∀ p q : ℤ, 0 < q →
      ∃ z : ℤ, (q : ℚ) ^ (37 * n) * m n * (Apery.F n).eval ((p : ℚ) / q) = z)
    (hlog : ∀ n, N0 ≤ n → Real.log (m n) ≤ Λ * ((40 * n : ℕ) : ℝ) ^ 2)
    (hΛ0 : Λ ≤ 1288519 / 10 ^ 6)
    (hD : DecayAtConst D) (hD0 : 138500086 / 10 ^ 8 ≤ D)
    (hρ : RhoBound (907427 / 10 ^ 5)) :
    MeasureLBAt Apery.zeta5 87 := by
  have hΛD : Λ < D := by
    have : (1288519 / 10 ^ 6 : ℝ) < 138500086 / 10 ^ 8 := by norm_num
    linarith
  have hDL : 0 < D - Λ := sub_pos.mpr hΛD
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
  have hD' : HasScaledDecay (signedFamily N0 m) zeta5Scale (D - Λ) (907427 / 10 ^ 5) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hdec ε hε
    refine ⟨R0, fun n hn hr t ht => ?_⟩
    have h1 := h n trivial hr t ht
    have hm : (0 : ℝ) < (m n : ℝ) := by exact_mod_cast hpos n hn
    have hmle : (m n : ℝ) ≤ Real.exp (Λ * ((zeta5Scale n : ℕ) : ℝ) ^ 2) := by
      have := hlog n hn
      calc (m n : ℝ) = Real.exp (Real.log (m n : ℝ)) := (Real.exp_log hm).symm
        _ ≤ _ := Real.exp_le_exp.mpr this
    have hev : (signedFamily N0 m).evalR n (Apery.zeta5 + t) =
        (m n : ℝ) * zeta5Family.evalR n (zeta5Family.const + t) := by
      simp [PolyFamily.evalR, signedFamily, zeta5Family]
    have hdef : (signedFamily N0 m).const = Apery.zeta5 := rfl
    rw [hdef, hev, abs_mul, abs_of_pos hm]
    calc (m n : ℝ) * |zeta5Family.evalR n (zeta5Family.const + t)|
        ≤ Real.exp (Λ * ((zeta5Scale n : ℕ) : ℝ) ^ 2) *
            Real.exp (-(D - ε) * ((zeta5Scale n : ℕ) : ℝ) ^ 2) :=
          mul_le_mul hmle h1 (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (-((D - Λ) - ε) * ((zeta5Scale n : ℕ) : ℝ) ^ 2) := by
          rw [← Real.exp_add]; congr 1; ring
  have hnn' : HasNearbyNV (signedFamily N0 m) zeta5Scale (907427 / 10 ^ 5) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hnn ε hε
    refine ⟨R0, fun n hn hr x hx => ?_⟩
    rw [hevalQ]
    exact mul_ne_zero (by exact_mod_cast (hpos n hn).ne') (h n trivial hr x hx)
  have hmain : (signedFamily N0 m).MeasureLB (37 / 40 * (907427 / 10 ^ 5) / ((D - Λ) - 0)) := by
    refine measure_of_family_nnv_period (signedFamily N0 m) zeta5Scale 40 (by norm_num)
      (γ := 37 / 40) (K := 0) hΛ' hD' (by linarith) (by norm_num) (by norm_num) le_rfl
      ?_ (fun n _ => ⟨n, rfl⟩) ⟨N0, fun s hs => ⟨s, hs, rfl⟩⟩ hnn'
    intro (n : ℕ) _
    show ((37 * n : ℕ) : ℝ) ≤ 37 / 40 * ((40 * n : ℕ) : ℝ) + 0
    push_cast; linarith
  rw [MeasureLB_iff, sub_zero] at hmain
  exact MeasureLBAt.mono (exponent_lt_87 hΛ0 hD0).le hmain

/-- **ZA17 composite.**  With the parity gain `hpar` (the one open input), the signed content
of `zc32_signed` (`Λ = 1288003/10⁶`), decay at the constant and the ρ bound give
`μ(ζ(5)) ≤ 87`. -/
theorem zeta5_measure_of_parity (hpar : Apery.ParityGain) {D : ℝ}
    (hD : DecayAtConst D) (hD0 : 138500086 / 10 ^ 8 ≤ D)
    (hρ : RhoBound (907427 / 10 ^ 5)) :
    MeasureLBAt Apery.zeta5 87 := by
  obtain ⟨N0, h⟩ := CatalanCore.Zeta5.Content.zc32_signed hpar
  exact zeta5_measure_signed (Λ := 1288003 / 10 ^ 6) N0 CatalanCore.Zeta5.Content.mZ
    (fun n hn => (h n hn).1) (fun n hn => (h n hn).2.1) (fun n hn => (h n hn).2.2)
    (by norm_num) hD hD0 hρ

end CatalanCore.Zeta5

#print axioms CatalanCore.Zeta5.zeta5_measure_signed
#print axioms CatalanCore.Zeta5.zeta5_measure_of_parity
