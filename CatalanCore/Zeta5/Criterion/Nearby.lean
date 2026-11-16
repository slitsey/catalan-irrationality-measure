module

public import CatalanCore.Uniform.Measure.NV0

@[expose] public section

/-!
# The measure criterion with nearby non-vanishing (ledger ZA11, ZA13, ZA18 generic part)

`CatalanCore.Uniform.measure_of_family_nv0` needs, at every large scale `r`, a member `n` with
`Q_n(x) ≠ 0` for *every* rational `x`.  For Fauzan's family `Q_n(x) ≠ 0` is known only for `x`
near the constant (positive definiteness of the Gram matrix plus a relative-norm bound), so the
hypothesis is weakened to

  `HasNearbyNV Fam scale c`: for every `ε > 0`, every admissible member of large scale `r` has
  `Q_n(x) ≠ 0` for every rational `x` with `|const - x| ≤ exp(-(c + ε) r)`.

In the proof of `measure_of_family_nv0` the non-vanishing at `p/q` is used only after the
contradiction hypothesis `|const - p/q| ≤ q^(-ν)` has produced the closeness
`|const - p/q| ≤ exp(-(c+ε) r)`; here that step is moved before the non-vanishing is invoked.

* `measure_of_family_nnv`: scales cover every large integer (`HasScaleCover`).
* `measure_of_family_nnv_period`: scales cover the lattice `m ℕ` only (for ζ(5), `K = 40 n`,
  `m = 40`); constants rescale `Λ ↦ m²Λ`, `D ↦ m²D`, `c ↦ m c`, `γ ↦ m γ`, exponent unchanged.
  No prime window is used (ledger ZA11).

Not editing `NV0` or `Reindex` (Rule Z1): this file imports `NV0` only.
-/

namespace CatalanCore.Uniform
open Real

/-- Nearby non-vanishing: members of large scale do not vanish at rationals within
`exp(-(c+ε) scale)` of the constant. -/
def HasNearbyNV (Fam : PolyFamily) (scale : Fam.ι → ℕ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ R0 : ℕ, ∀ n, Fam.Adm n → R0 ≤ scale n → ∀ x : ℚ,
    |Fam.const - (x : ℝ)| ≤ Real.exp (-(c + ε) * (scale n : ℝ)) → Fam.evalQ n x ≠ 0

/-- Every sufficiently large integer is the scale of an admissible member. -/
def HasScaleCover (Fam : PolyFamily) (scale : Fam.ι → ℕ) : Prop :=
  ∃ R0 : ℕ, ∀ r : ℕ, R0 ≤ r → ∃ n, Fam.Adm n ∧ scale n = r

/-- **Criterion with nearby non-vanishing** (ZA13, generic).  Proof of
`measure_of_family_nv0` with the non-vanishing step moved after the closeness step. -/
theorem measure_of_family_nnv (Fam : PolyFamily) (scale : Fam.ι → ℕ)
    {Λ D c γ K : ℝ} (hΛ : HasScaledContent Fam scale Λ)
    (hD : HasScaledDecay Fam scale D c) (hη : Λ < D) (hc : 0 < c)
    (hγ : 0 < γ) (hK : 0 ≤ K)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ γ * scale n + K)
    (hcov : HasScaleCover Fam scale) (hnn : HasNearbyNV Fam scale c) :
    Fam.MeasureLB (γ * c / (D - Λ)) := by
  intro e he
  let ν := γ * c / (D - Λ) + e
  have hη0 : 0 < D - Λ := sub_pos.mpr hη
  have hν0 : 0 < ν := by dsimp [ν]; positivity
  have hgap : γ / (D - Λ) < ν / c := by
    dsimp [ν]
    apply (lt_div_iff₀ hc).mpr
    have heq : γ / (D - Λ) * c = γ * c / (D - Λ) := by ring
    rw [heq]; linarith
  obtain ⟨a, ha1, ha2⟩ := exists_between hgap
  have ha : 0 < a := lt_trans (by positivity) ha1
  have hηa : γ / a < D - Λ := by
    apply (div_lt_iff₀ ha).mpr
    have := (div_lt_iff₀ hη0).mp ha1
    nlinarith
  obtain ⟨θ, hθ1, hθ2⟩ := exists_between hηa
  have hθ0 : 0 < θ := lt_trans (by positivity) hθ1
  have hθa : γ < θ * a := by exact (div_lt_iff₀ ha).mp hθ1
  let ε := min ((D - Λ - θ) / 3) ((ν / a - c) / 2)
  have hca : c * a < ν := by
    have := (lt_div_iff₀ hc).mp ha2
    nlinarith
  have hε0 : 0 < ε := by
    apply lt_min
    · linarith
    · have : c < ν / a := (lt_div_iff₀ ha).mpr (by nlinarith)
      linarith
  have hbudget : θ + 2 * ε ≤ D - Λ := by
    have := min_le_left ((D - Λ - θ) / 3) ((ν / a - c) / 2)
    change ε ≤ (D - Λ - θ) / 3 at this
    linarith
  have hwindow : (c + ε) * a < ν := by
    have hle := min_le_right ((D - Λ - θ) / 3) ((ν / a - c) / 2)
    change ε ≤ (ν / a - c) / 2 at hle
    have hdiv : ν / a * a = ν := div_mul_cancel₀ _ ha.ne'
    nlinarith
  obtain ⟨Rsep, hsep⟩ := scaled_sep Fam scale hΛ hD hε0 hbudget
  obtain ⟨Rcov, hcov⟩ := hcov
  obtain ⟨Rnn, hnn⟩ := hnn ε hε0
  let R := max Rsep (max Rcov Rnn)
  let B := max (((R : ℝ) + 1) / a)
    (max ((c + ε) / (ν - (c + ε) * a)) ((K + 1) / (a * (θ * a - γ))))
  refine ⟨⌈Real.exp (B + 1)⌉₊, ?_⟩
  intro p q hq _
  have hqe : Real.exp (B + 1) ≤ q :=
    (Nat.le_ceil _).trans (by exact_mod_cast hq)
  have hqpos : (0 : ℝ) < q := (Real.exp_pos _).trans_le hqe
  have hqN : 0 < q := by exact_mod_cast hqpos
  have hL : B + 1 ≤ Real.log q := (Real.le_log_iff_exp_le hqpos).mpr hqe
  let L := Real.log (q : ℝ)
  have hLB1 : ((R : ℝ) + 1) / a < L := by
    have hb : ((R : ℝ) + 1) / a ≤ B := le_max_left _ _
    dsimp [L]; linarith
  have hLB2 : (c + ε) / (ν - (c + ε) * a) < L := by
    have hb : (c + ε) / (ν - (c + ε) * a) ≤ B :=
      (le_max_left _ _).trans (le_max_right _ _)
    dsimp [L]; linarith
  have hLB3 : (K + 1) / (a * (θ * a - γ)) < L := by
    have hb : (K + 1) / (a * (θ * a - γ)) ≤ B :=
      (le_max_right _ _).trans (le_max_right _ _)
    dsimp [L]; linarith
  have hL0 : 0 < L := lt_trans (by positivity) hLB1
  let r := ⌈a * L⌉₊
  have hrlo : a * L ≤ (r : ℝ) := Nat.le_ceil _
  have hrhi : (r : ℝ) < a * L + 1 := Nat.ceil_lt_add_one (by positivity)
  have hrR : R ≤ r := by
    have := (div_lt_iff₀ ha).mp hLB1
    have : (R : ℝ) ≤ r := by nlinarith
    exact_mod_cast this
  have hRcov : Rcov ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans hrR)
  have hRnn : Rnn ≤ r := (le_max_right _ _).trans ((le_max_right _ _).trans hrR)
  have hRsep : Rsep ≤ r := (le_max_left _ _).trans hrR
  obtain ⟨n, hn, hnr⟩ := hcov r hRcov
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le (by positivity) hrlo
  by_contra hcon
  have hclose : |Fam.const - (p : ℝ) / q| ≤ (q : ℝ) ^ (-ν) := le_of_not_gt hcon
  have hwin : |Fam.const - (p : ℝ) / q| ≤ Real.exp (-(c + ε) * (scale n : ℝ)) := by
    apply hclose.trans
    rw [Real.rpow_def_of_pos hqpos, hnr]
    apply Real.exp_le_exp.mpr
    have h2 := (div_lt_iff₀ (sub_pos.mpr hwindow)).mp hLB2
    have hcp : 0 < c + ε := add_pos hc hε0
    have hr' := mul_lt_mul_of_pos_left hrhi hcp
    dsimp [L] at h2
    dsimp [L] at hr'
    nlinarith only [h2, hr']
  have hne : Fam.evalQ n ((p : ℚ) / (q : ℚ)) ≠ 0 :=
    hnn n hn (by rw [hnr]; exact hRnn) ((p : ℚ) / (q : ℚ)) (by push_cast; exact hwin)
  have hsep' := hsep n hn (by rw [hnr]; exact hRsep)
    p (q : ℤ) (by exact_mod_cast hqN) (by simpa using hne) (by simpa using hwin)
  simp only [Int.cast_natCast, hnr] at hsep'
  have hdeg' := hdeg n hn
  rw [hnr] at hdeg'
  have hup : θ * (r : ℝ) ^ 2 ≤ (γ * (r : ℝ) + K) * L :=
    hsep'.trans (mul_le_mul_of_nonneg_right hdeg' hL0.le)
  have hbudget' : K + 1 < a * (θ * a - γ) * L :=
    by simpa [mul_comm] using (div_lt_iff₀ (mul_pos ha (sub_pos.mpr hθa))).mp hLB3
  have hrlarge : K < (θ * a - γ) * (r : ℝ) := by
    have := mul_le_mul_of_nonneg_left hrlo (sub_pos.mpr hθa).le
    nlinarith only [hbudget', this]
  have hscaled : a * L * (r : ℝ) ≤ (r : ℝ) ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hrlo hrpos.le]
  have hθscaled := mul_le_mul_of_nonneg_left hscaled hθ0.le
  have hlast := mul_lt_mul_of_pos_right hrlarge hL0
  nlinarith only [hup, hθscaled, hlast]

/-- **Period version** (ZA11 + ZA13 + ZA18, generic): admissible scales are multiples of
`m` and cover `m ℕ` from some point on.  The exponent is unchanged. -/
theorem measure_of_family_nnv_period (Fam : PolyFamily) (scale : Fam.ι → ℕ) (m : ℕ) (hm : 0 < m)
    {Λ D c γ K : ℝ} (hΛ : HasScaledContent Fam scale Λ)
    (hD : HasScaledDecay Fam scale D c) (hη : Λ < D) (hc : 0 < c)
    (hγ : 0 < γ) (hK : 0 ≤ K)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ γ * scale n + K)
    (hdvd : ∀ n, Fam.Adm n → m ∣ scale n)
    (hcov : ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∃ n, Fam.Adm n ∧ scale n = m * s)
    (hnn : HasNearbyNV Fam scale c) :
    Fam.MeasureLB (γ * c / (D - Λ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hcast : ∀ n, Fam.Adm n → (scale n : ℝ) = (m : ℝ) * ((scale n / m : ℕ) : ℝ) := by
    intro n hn
    obtain ⟨k, hk⟩ := hdvd n hn
    rw [hk, Nat.mul_div_cancel_left _ hm]
    push_cast; ring
  have hle : ∀ n, Fam.Adm n → scale n / m ≤ scale n := fun n _ => Nat.div_le_self _ _
  have hΛ' : HasScaledContent Fam (fun n => scale n / m) ((m : ℝ) ^ 2 * Λ) := by
    obtain ⟨den, hpos, hint, hlog⟩ := hΛ
    refine ⟨den, hpos, hint, ?_⟩
    intro ε hε
    obtain ⟨R0, h⟩ := hlog (ε / (m : ℝ) ^ 2) (by positivity)
    refine ⟨R0, fun n hn hr => ?_⟩
    have h1 := h n hn ((show R0 ≤ scale n / m from hr).trans (hle n hn))
    rw [hcast n hn] at h1
    have hmul : (m : ℝ) ^ 2 * (ε / (m : ℝ) ^ 2) = ε := by field_simp
    have hs := sq_nonneg ((scale n / m : ℕ) : ℝ)
    calc Real.log (den n) ≤ (Λ + ε / (m : ℝ) ^ 2) * ((m : ℝ) * ((scale n / m : ℕ) : ℝ)) ^ 2 := h1
      _ = ((m : ℝ) ^ 2 * Λ + ε) * ((scale n / m : ℕ) : ℝ) ^ 2 := by
        field_simp
  have hD' : HasScaledDecay Fam (fun n => scale n / m) ((m : ℝ) ^ 2 * D) ((m : ℝ) * c) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hD (ε / (m : ℝ) ^ 2) (by positivity)
    refine ⟨R0, fun n hn hr t ht => ?_⟩
    have hs := hcast n hn
    have hs0 : (0 : ℝ) ≤ ((scale n / m : ℕ) : ℝ) := Nat.cast_nonneg _
    have hε2 : ε / (m : ℝ) ^ 2 ≤ ε / (m : ℝ) :=
      div_le_div_of_nonneg_left hε.le hmR (by nlinarith)
    have h1 := h n hn ((show R0 ≤ scale n / m from hr).trans (hle n hn)) t (by
      refine ht.trans (Real.exp_le_exp.2 ?_)
      rw [hs]
      have : (c + ε / (m : ℝ) ^ 2) * ((m : ℝ) * ((scale n / m : ℕ) : ℝ)) ≤
          ((m : ℝ) * c + ε) * ((scale n / m : ℕ) : ℝ) := by
        have h3 : ε / (m : ℝ) ^ 2 * (m : ℝ) = ε / (m : ℝ) := by field_simp
        have h4 : ε / (m : ℝ) ≤ ε := div_le_self hε.le hm1
        nlinarith [mul_le_mul_of_nonneg_right h4 hs0]
      nlinarith)
    refine h1.trans (le_of_eq ?_)
    congr 1
    rw [hs]
    field_simp
  have hnn' : HasNearbyNV Fam (fun n => scale n / m) ((m : ℝ) * c) := by
    intro ε hε
    obtain ⟨R0, h⟩ := hnn (ε / (m : ℝ)) (by positivity)
    refine ⟨R0, fun n hn hr x hx => ?_⟩
    apply h n hn ((show R0 ≤ scale n / m from hr).trans (hle n hn)) x
    refine hx.trans (le_of_eq ?_)
    congr 1
    have hs := hcast n hn
    have h5 : (c + ε / (m : ℝ)) * (m : ℝ) = (m : ℝ) * c + ε := by field_simp
    rw [hs]
    simp only [neg_mul]
    rw [neg_inj]
    calc ((m : ℝ) * c + ε) * ((scale n / m : ℕ) : ℝ)
        = (c + ε / (m : ℝ)) * (m : ℝ) * ((scale n / m : ℕ) : ℝ) := by rw [h5]
      _ = _ := by ring
  have hcov' : HasScaleCover Fam (fun n => scale n / m) := by
    obtain ⟨R0, h⟩ := hcov
    refine ⟨R0, fun r hr => ?_⟩
    obtain ⟨n, hn, hs⟩ := h r hr
    exact ⟨n, hn, by show scale n / m = r; rw [hs, Nat.mul_div_cancel_left _ hm]⟩
  have hdeg' : ∀ n, Fam.Adm n →
      (Fam.deg n : ℝ) ≤ ((m : ℝ) * γ) * ((scale n / m : ℕ) : ℝ) + K := by
    intro n hn
    have := hdeg n hn
    rw [hcast n hn] at this
    linarith
  have key := measure_of_family_nnv Fam (fun n => scale n / m) hΛ' hD'
    (mul_lt_mul_of_pos_left hη hm2) (by positivity) (by positivity) hK hdeg' hcov' hnn'
  have hDL : 0 < D - Λ := sub_pos.2 hη
  have hexp : (m : ℝ) * γ * ((m : ℝ) * c) / ((m : ℝ) ^ 2 * D - (m : ℝ) ^ 2 * Λ)
      = γ * c / (D - Λ) := by
    rw [show (m : ℝ) ^ 2 * D - (m : ℝ) ^ 2 * Λ = (m : ℝ) ^ 2 * (D - Λ) by ring]
    field_simp
  rw [hexp] at key
  exact key

end CatalanCore.Uniform
