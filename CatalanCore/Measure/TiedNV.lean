module

public import CatalanCore.NT.TiedWindow
public import CatalanCore.Uniform.Measure.NV0
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FunProp
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Prime-tied nonvanishing and the measure criterion (ledger LR03, LR04, LR12)

A `TiedNV` family records, for one arithmetic family of primes `ℓ` (a set `S` of unit classes mod
`M`, outside a finite exception set), the member `mem ℓ` of the polynomial family tied to `ℓ`
(`ℓ = c · scale (mem ℓ) + d`), a predicate `Bad ℓ p q` with `ℓ ^ e ∣ W p q` whenever it holds, and
the nonvanishing statement `Q_{mem ℓ}(p/q) ≠ 0` whenever `Bad ℓ p q` fails.

`measure_of_family_tiedNV` (Criterion W2U): from scaled content `Λ`, scaled decay `(D, ρ)`, a degree
bound `deg n ≤ κ · scale n` and a list of `TiedNV` families whose union window mass
`𝓜(κ/η, κ/η + β) > 1` (`η = D - Λ`), every `μ > ρ (κ/η + β)` is a measure bound in the plain
form `∀ᶠ q, ∀ p, q ^ (-μ) < |x - p/q|`.  The number of families is arbitrary, the windows may
overlap, and `W` is the integer carrying the bad primes (the denominator `q` for a plane, the
numerator `|p|` for a ratio).

`plain_measure_smul` (LR12): the plain measure form is invariant under multiplication by a nonzero
rational, up to an arbitrarily small loss of exponent.
-/

open Filter Topology

namespace CatalanCore.Measure

/-- A prime-tied nonvanishing family (see the module docstring for the field meanings). -/
structure TiedNV (Fam : PolyFamily) (scale : Fam.ι → ℕ) (M : ℕ) (W : ℤ → ℕ → ℕ) where
  /-- unit classes mod `M` of the tied primes -/
  S : Finset (ZMod M)
  S_unit : ∀ s ∈ S, IsUnit s
  /-- slope and offset: `ℓ = c * scale (mem ℓ) + d` -/
  c : ℝ
  c_pos : 0 < c
  d : ℝ
  /-- tolerance exponent: `Bad ℓ p q → ℓ ^ e ∣ W p q` -/
  e : ℕ
  /-- finite exception set of primes -/
  exc : Finset ℕ
  /-- the member tied to the prime `ℓ` -/
  mem : ℕ → Fam.ι
  adm : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ZMod M) ∈ S → ℓ ∉ exc → Fam.Adm (mem ℓ)
  size_eq : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ZMod M) ∈ S → ℓ ∉ exc →
    (ℓ : ℝ) = c * (scale (mem ℓ) : ℝ) + d
  /-- `Bad ℓ p q`: the prime `ℓ` is unusable for the point `p / q` -/
  Bad : ℕ → ℤ → ℕ → Prop
  bad_dvd : ∀ (ℓ : ℕ) (p : ℤ) (q : ℕ), Bad ℓ p q → ℓ ^ e ∣ W p q
  nv : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ZMod M) ∈ S → ℓ ∉ exc → ∀ (p : ℤ) (q : ℕ), 0 < q →
    ¬ Bad ℓ p q → Fam.evalQ (mem ℓ) ((p : ℚ) / (q : ℚ)) ≠ 0

/-- Bad rule of a plane: `ℓ ^ e ∣ q`, carried by `W p q = q`. -/
def planeBad (e : ℕ) (ℓ : ℕ) (_p : ℤ) (q : ℕ) : Prop := ℓ ^ e ∣ q

/-- Bad rule of a ratio: `ℓ ∣ p`, carried by `W p q = |p|`. -/
def ratioBad (ℓ : ℕ) (p : ℤ) (_q : ℕ) : Prop := ℓ ∣ p.natAbs

/-- The witness `q` of a plane. -/
def planeW (_p : ℤ) (q : ℕ) : ℕ := q

/-- The witness `|p|` of a ratio. -/
def ratioW (p : ℤ) (_q : ℕ) : ℕ := p.natAbs

theorem planeBad_dvd (e ℓ : ℕ) (p : ℤ) (q : ℕ) (h : planeBad e ℓ p q) : ℓ ^ e ∣ planeW p q := h

theorem ratioBad_dvd (ℓ : ℕ) (p : ℤ) (q : ℕ) (h : ratioBad ℓ p q) : ℓ ^ 1 ∣ ratioW p q := by
  simpa [ratioBad, ratioW] using h

/-- The height hypothesis of `measure_of_family_tiedNV` for a plane: `W p q = q`, `Kh = 1`. -/
theorem planeW_hW (x : ℝ) : ∀ (p : ℤ) (q : ℕ), 0 < q → |x - (p : ℝ) / q| < 1 →
    0 < planeW p q ∧ (planeW p q : ℝ) ≤ 1 * q := by
  intro p q hq _
  exact ⟨hq, by simp [planeW]⟩

/-- The height hypothesis for a ratio `x ∈ (1, 2)`: near `x` the numerator is positive and at most
`3 q`, so `W p q = |p|` is positive with `Kh = 3`. -/
theorem ratioW_hW {x : ℝ} (hx1 : 1 < x) (hx2 : x < 2) :
    ∀ (p : ℤ) (q : ℕ), 0 < q → |x - (p : ℝ) / q| < 1 →
      0 < ratioW p q ∧ (ratioW p q : ℝ) ≤ 3 * q := by
  intro p q hq h
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨h1, h2⟩ := abs_lt.mp h
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    have : 0 < (p : ℝ) / q := by linarith
    have := (div_pos_iff_of_pos_right hqR).mp this
    exact this
  have hp3 : (p : ℝ) < 3 * q := by
    have : (p : ℝ) / q < 3 := by linarith
    rwa [div_lt_iff₀ hqR] at this
  have hpz : 0 < p := by exact_mod_cast hp0
  have habs : ((p.natAbs : ℕ) : ℝ) = (p : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hp0]
  refine ⟨by simp [ratioW]; omega, ?_⟩
  simp only [ratioW]
  rw [habs]; exact hp3.le


/-- Family-indexed union window condition of a list of tied families. -/
def TiedNV.windowOK {Fam : PolyFamily} {scale : Fam.ι → ℕ} {M : ℕ} [NeZero M]
    {W : ℤ → ℕ → ℕ} (L : List (TiedNV Fam scale M W)) (a b : ℝ) : Prop :=
  NT.UnionWindowOK (fun i : Fin L.length => (L.get i).S) (fun i => (L.get i).c)
    (fun i => (L.get i).e) a b

set_option maxHeartbeats 1600000 in
/-- **Measure criterion with prime-tied nonvanishing** (Criterion W2U), indexed by a finite type of
families. -/
theorem measure_of_family_tiedNV_index {Fam : PolyFamily} {scale : Fam.ι → ℕ} {M : ℕ} [NeZero M]
    {W : ℤ → ℕ → ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] (F : ι → TiedNV Fam scale M W)
    {Λ D ρ κ β Kh μ : ℝ}
    (hΛ : CatalanCore.Uniform.HasScaledContent Fam scale Λ) (hD : CatalanCore.Uniform.HasScaledDecay Fam scale D ρ)
    (hη : Λ < D) (hρ : 0 < ρ) (hκ : 0 < κ) (hβ : 0 < β) (hKh : 0 < Kh)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ κ * (scale n : ℝ))
    (hW : ∀ (p : ℤ) (q : ℕ), 0 < q → |Fam.const - (p : ℝ) / q| < 1 →
      0 < W p q ∧ (W p q : ℝ) ≤ Kh * q)
    (hmass : NT.UnionWindowOK (fun i => (F i).S) (fun i => (F i).c) (fun i => (F i).e)
      (κ / (D - Λ)) (κ / (D - Λ) + β))
    (hμ : ρ * (κ / (D - Λ) + β) < μ) :
    ∀ᶠ q : ℕ in atTop, ∀ p : ℤ, (q : ℝ) ^ (-μ) < |Fam.const - (p : ℝ) / q| := by
  set η : ℝ := D - Λ with hηdef
  have hη0 : 0 < η := by rw [hηdef]; linarith
  set a₀ : ℝ := κ / η with ha₀def
  have ha₀ : 0 < a₀ := by positivity
  set b₀ : ℝ := a₀ + β with hb₀def
  have hb₀ : 0 < b₀ := by rw [hb₀def]; linarith
  have hμ0 : 0 < μ := lt_of_le_of_lt (by positivity) hμ
  -- Step 1: shift the window slightly to the right, keeping the mass above 1
  have hcont : ContinuousAt (fun s : ℝ => NT.unionMass (fun i => (F i).S) (fun i => (F i).c)
      (fun i => (F i).e) (a₀ + s) (b₀ + s)) 0 := by
    have hc := (NT.continuous_unionMass (fun i => (F i).S) (fun i => (F i).c)
      (fun i => (F i).e)).comp (by fun_prop : Continuous fun s : ℝ => (a₀ + s, b₀ + s))
    exact hc.continuousAt
  have hm0 : 1 < NT.unionMass (fun i => (F i).S) (fun i => (F i).c) (fun i => (F i).e)
      (a₀ + 0) (b₀ + 0) := by
    simpa [NT.UnionWindowOK] using hmass
  obtain ⟨δ, hδ, hδmass⟩ := Metric.eventually_nhds_iff.mp (hcont.eventually (lt_mem_nhds hm0))
  have hμρ : 0 < μ - ρ * b₀ := by
    have : 0 < ρ * (κ / η + β) := by positivity
    linarith
  set s : ℝ := min (δ / 2) ((μ - ρ * b₀) / (2 * ρ)) with hsdef
  have hs0 : 0 < s := by
    have : 0 < μ - ρ * b₀ := hμρ
    rw [hsdef]; apply lt_min <;> positivity
  have hsδ : s < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hρs : ρ * (b₀ + s) < μ := by
    have h1 : s ≤ (μ - ρ * b₀) / (2 * ρ) := min_le_right _ _
    have h2 : ρ * s ≤ (μ - ρ * b₀) / 2 := by
      have := mul_le_mul_of_nonneg_left h1 hρ.le
      calc ρ * s ≤ ρ * ((μ - ρ * b₀) / (2 * ρ)) := this
        _ = (μ - ρ * b₀) / 2 := by field_simp
    have e1 : ρ * (b₀ + s) = ρ * b₀ + ρ * s := by ring
    linarith
  set a : ℝ := a₀ + s with hadef
  set b : ℝ := b₀ + s with hbdef
  have ha : 0 < a := by rw [hadef]; linarith
  have hb : 0 < b := by rw [hbdef]; linarith
  have hmassab : NT.UnionWindowOK (fun i => (F i).S) (fun i => (F i).c) (fun i => (F i).e) a b := by
    have := hδmass (y := s) (by rw [Real.dist_eq, sub_zero, abs_of_pos hs0]; exact hsδ)
    exact this
  -- Step 2: parameters of the separation
  set ε : ℝ := min (s * η / (4 * a)) ((μ - ρ * b) / (2 * b)) with hεdef
  have hε0 : 0 < ε := by
    have : 0 < μ - ρ * b := by linarith
    rw [hεdef]; apply lt_min <;> positivity
  have hε1 : ε ≤ s * η / (4 * a) := min_le_left _ _
  have hε2 : ε ≤ (μ - ρ * b) / (2 * b) := min_le_right _ _
  set θ : ℝ := η - 2 * ε with hθdef
  have hsa : s < a := by rw [hadef]; linarith
  have hεη : ε * (4 * a) ≤ s * η := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * a)).mp hε1
    exact this
  have hθ0 : 0 < θ := by
    have h1 : s * η < a * η := mul_lt_mul_of_pos_right hsa hη0
    have h2 : (4 * ε) * a < η * a := by linarith
    have h3 : 4 * ε < η := lt_of_mul_lt_mul_right h2 ha.le
    rw [hθdef]; linarith
  have hθa : κ + s * η / 2 ≤ θ * a := by
    have e1 : κ = a₀ * η := by rw [ha₀def]; field_simp
    have : θ * a = η * a - 2 * ε * a := by rw [hθdef]; ring
    have e2 : η * (a₀ + s) = a₀ * η + s * η := by ring
    have e3 : 2 * ε * (a₀ + s) = ε * (2 * a₀ + 2 * s) := by ring
    have e4 : ε * (4 * a) = 2 * (2 * ε * a) := by ring
    rw [this, hadef, e1] at *
    nlinarith
  have hρεb : (ρ + ε) * b < μ := by
    have : ε * b ≤ (μ - ρ * b) / 2 := by
      have := mul_le_mul_of_nonneg_right hε2 hb.le
      calc ε * b ≤ (μ - ρ * b) / (2 * b) * b := this
        _ = (μ - ρ * b) / 2 := by field_simp
    have e1 : (ρ + ε) * b = ρ * b + ε * b := by ring
    linarith
  obtain ⟨R0, hR0⟩ := CatalanCore.Uniform.scaled_sep Fam scale hΛ hD hε0 (θ := θ) (by rw [hθdef]; linarith)
  obtain ⟨ε₀, hε₀, L₀, hL₀⟩ := NT.exists_tied_prime (fun i => (F i).S_unit)
    (fun i => (F i).c_pos) (fun i => (F i).e) (fun i => (F i).exc) ha hb hmassab
  -- the offset bound
  set Dd : ℝ := ∑ j, |(F j).d| / (F j).c with hDddef
  have hDd0 : 0 ≤ Dd := Finset.sum_nonneg fun j _ => div_nonneg (abs_nonneg _) (F j).c_pos.le
  have hDd : ∀ i, |(F i).d| ≤ Dd * (F i).c := by
    intro i
    have h1 : |(F i).d| / (F i).c ≤ Dd :=
      Finset.single_le_sum (f := fun j => |(F j).d| / (F j).c)
        (fun j _ => div_nonneg (abs_nonneg _) (F j).c_pos.le) (Finset.mem_univ i)
    have := (div_le_iff₀ (F i).c_pos).mp h1
    linarith
  -- Step 3: the threshold height
  have hev : ∀ᶠ L : ℝ in atTop, L₀ ≤ L ∧ 1 ≤ L ∧ ((R0 : ℝ) + 1 + Dd) / a ≤ L ∧
      θ * Dd / (s * η / 2) ≤ L ∧ (ρ + ε) * Dd / (μ - (ρ + ε) * b) ≤ L ∧
      (|Real.log Kh| + 1) / ε₀ ≤ L := by
    filter_upwards [eventually_ge_atTop L₀, eventually_ge_atTop (1 : ℝ),
      eventually_ge_atTop (((R0 : ℝ) + 1 + Dd) / a), eventually_ge_atTop (θ * Dd / (s * η / 2)),
      eventually_ge_atTop ((ρ + ε) * Dd / (μ - (ρ + ε) * b)),
      eventually_ge_atTop ((|Real.log Kh| + 1) / ε₀)] with L h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨Lstar, hLstar⟩ := Filter.eventually_atTop.mp hev
  refine Filter.eventually_atTop.mpr ⟨⌈Real.exp Lstar⌉₊, fun q hq p => ?_⟩
  have hqe : Real.exp Lstar ≤ q := (Nat.le_ceil _).trans (by exact_mod_cast hq)
  have hqpos : (0 : ℝ) < q := (Real.exp_pos _).trans_le hqe
  have hq0 : 0 < q := by exact_mod_cast hqpos
  have hL : Lstar ≤ Real.log q := (Real.le_log_iff_exp_le hqpos).2 hqe
  obtain ⟨hL1, hL2, hL3, hL4, hL5, hL6⟩ := hLstar _ hL
  set L : ℝ := Real.log q with hLdef
  have hL0 : 0 < L := by linarith
  by_contra hcon
  push Not at hcon
  -- the point is close, hence `|const - p/q| < 1` and `W p q` is a positive integer of size `≤ Kh q`
  have hq1 : (1 : ℝ) < q := by
    have : 0 < L := hL0
    by_contra hle
    push Not at hle
    have := Real.log_nonpos hqpos.le hle
    linarith
  have hqμ : (q : ℝ) ^ (-μ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (by linarith)
  have hclose1 : |Fam.const - (p : ℝ) / q| < 1 := lt_of_le_of_lt hcon hqμ
  obtain ⟨hWpos, hWle⟩ := hW p q hq0 hclose1
  have hlogW : Real.log (W p q) ≤ Real.log Kh + L := by
    have : (0 : ℝ) < (W p q : ℝ) := by exact_mod_cast hWpos
    calc Real.log (W p q) ≤ Real.log (Kh * q) := Real.log_le_log this hWle
      _ = Real.log Kh + L := by rw [Real.log_mul hKh.ne' hqpos.ne']
  have hlogW' : Real.log (W p q) < (1 + ε₀) * L := by
    have h6 : |Real.log Kh| + 1 ≤ ε₀ * L := by
      have := (div_le_iff₀ hε₀).mp hL6
      linarith
    have := le_abs_self (Real.log Kh)
    nlinarith
  obtain ⟨i, ℓ, hti, hnb⟩ := hL₀ L hL1 (fun i ℓ => (F i).Bad ℓ p q) (W p q) hWpos
    (fun i ℓ h => (F i).bad_dvd ℓ p q h) hlogW'
  obtain ⟨hlp, hlcl, hlex, hlo, hhi⟩ := hti
  have hnz := (F i).nv ℓ hlp hlcl hlex p q hq0 hnb
  have hAdm := (F i).adm ℓ hlp hlcl hlex
  have hsz := (F i).size_eq ℓ hlp hlcl hlex
  set n : ℝ := (scale ((F i).mem ℓ) : ℝ) with hn
  have hci := (F i).c_pos
  have hdi := hDd i
  have hdi' := abs_le.mp hdi
  -- n lies in the window up to the offset
  have hnlo : a * L - Dd < n := by
    have h1 : (F i).c * a * L < (F i).c * n + (F i).d := by rw [← hsz]; exact hlo
    by_contra hle
    push Not at hle
    have := mul_le_mul_of_nonneg_left hle hci.le
    linarith [hdi'.2]
  have hnhi : n ≤ b * L + Dd := by
    have h1 : (F i).c * n + (F i).d ≤ (F i).c * b * L := by rw [← hsz]; exact hhi
    by_contra hle
    push Not at hle
    have := mul_lt_mul_of_pos_left hle hci
    linarith [hdi'.1]
  have hnR0 : R0 ≤ scale ((F i).mem ℓ) := by
    have : (R0 : ℝ) ≤ n := by
      have := (div_le_iff₀ ha).mp hL3
      linarith
    rw [hn] at this
    exact_mod_cast this
  have hn0 : 0 < n := by
    have := (div_le_iff₀ ha).mp hL3
    linarith
  -- closeness of `p/q` to the constant in the window of `n`
  have hwin : |Fam.const - (p : ℝ) / ((q : ℤ) : ℝ)| ≤ Real.exp (-(ρ + ε) * (scale ((F i).mem ℓ) : ℝ)) := by
    simp only [Int.cast_natCast]
    refine hcon.trans ?_
    rw [Real.rpow_def_of_pos hqpos, ← hLdef]
    apply Real.exp_le_exp.2
    have h1 : (ρ + ε) * n ≤ (ρ + ε) * (b * L + Dd) :=
      mul_le_mul_of_nonneg_left hnhi (by linarith)
    have h2 : (ρ + ε) * Dd ≤ (μ - (ρ + ε) * b) * L := by
      have := (div_le_iff₀ (by linarith : 0 < μ - (ρ + ε) * b)).mp hL5
      linarith
    have e1 : (ρ + ε) * (b * L + Dd) = (ρ + ε) * b * L + (ρ + ε) * Dd := by ring
    have e2 : (μ - (ρ + ε) * b) * L = μ * L - (ρ + ε) * b * L := by ring
    linarith
  have key := hR0 ((F i).mem ℓ) hAdm hnR0 p (q : ℤ) (by exact_mod_cast hq0)
    (by simpa using hnz) hwin
  have hdg := hdeg _ hAdm
  have hlogq : (0 : ℝ) ≤ Real.log ((q : ℤ) : ℝ) := by
    simp only [Int.cast_natCast]; exact Real.log_nonneg hq1.le
  simp only [Int.cast_natCast] at key hlogq
  have h3 : θ * n ^ 2 ≤ κ * n * L := key.trans (mul_le_mul_of_nonneg_right hdg hL0.le)
  have h4 : θ * n ≤ κ * L := by
    have : n * (θ * n) ≤ n * (κ * L) := by nlinarith
    exact le_of_mul_le_mul_left this hn0
  have h5 : (κ + s * η / 2) * L ≤ θ * a * L := mul_le_mul_of_nonneg_right hθa hL0.le
  have h6 : θ * Dd ≤ (s * η / 2) * L := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < s * η / 2)).mp hL4
    linarith
  have h7 : θ * (a * L - Dd) < θ * n := mul_lt_mul_of_pos_left hnlo hθ0
  have h8 : θ * (a * L - Dd) = θ * a * L - θ * Dd := by ring
  have h5' : κ * L + (s * η / 2) * L ≤ θ * a * L := by rw [← add_mul]; exact h5
  linarith


/-- **Measure criterion with prime-tied nonvanishing**, for a list of tied families (ledger LR03). -/
theorem measure_of_family_tiedNV {Fam : PolyFamily} {scale : Fam.ι → ℕ} {M : ℕ} [NeZero M]
    {W : ℤ → ℕ → ℕ} (L : List (TiedNV Fam scale M W)) {Λ D ρ κ β Kh μ : ℝ}
    (hΛ : CatalanCore.Uniform.HasScaledContent Fam scale Λ)
    (hD : CatalanCore.Uniform.HasScaledDecay Fam scale D ρ)
    (hη : Λ < D) (hρ : 0 < ρ) (hκ : 0 < κ) (hβ : 0 < β) (hKh : 0 < Kh)
    (hdeg : ∀ n, Fam.Adm n → (Fam.deg n : ℝ) ≤ κ * (scale n : ℝ))
    (hW : ∀ (p : ℤ) (q : ℕ), 0 < q → |Fam.const - (p : ℝ) / q| < 1 →
      0 < W p q ∧ (W p q : ℝ) ≤ Kh * q)
    (hmass : TiedNV.windowOK L (κ / (D - Λ)) (κ / (D - Λ) + β))
    (hμ : ρ * (κ / (D - Λ) + β) < μ) :
    ∀ᶠ q : ℕ in atTop, ∀ p : ℤ, (q : ℝ) ^ (-μ) < |Fam.const - (p : ℝ) / q| :=
  measure_of_family_tiedNV_index (fun i : Fin L.length => L.get i) hΛ hD hη hρ hκ hβ hKh hdeg hW
    hmass hμ

/-- **Plain measure form is invariant under a nonzero rational multiple** (ledger LR12): a bound
`q ^ (-μ') < |r x - p/q|` for all large `q` and all `p` gives `q ^ (-μ) < |x - p/q|` for every
`μ > μ'`. -/
theorem plain_measure_smul {x : ℝ} {r : ℚ} (hr : r ≠ 0) {μ' μ : ℝ} (hμ : μ' < μ)
    (h : ∀ᶠ q : ℕ in atTop, ∀ p : ℤ, (q : ℝ) ^ (-μ') < |(r : ℝ) * x - (p : ℝ) / q|) :
    ∀ᶠ q : ℕ in atTop, ∀ p : ℤ, (q : ℝ) ^ (-μ) < |x - (p : ℝ) / q| := by
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp h
  set v : ℕ := r.den with hvdef
  set u : ℤ := r.num with hudef
  have hv : 0 < v := r.den_pos
  have hvR : (0 : ℝ) < v := by exact_mod_cast hv
  have hu : u ≠ 0 := Rat.num_ne_zero.mpr hr
  have hrR : (r : ℝ) = (u : ℝ) / v := by rw [Rat.cast_def]
  have hr0 : 0 < |(r : ℝ)| := abs_pos.mpr (by exact_mod_cast hr)
  set Cc : ℝ := (v : ℝ) ^ (-μ') / |(r : ℝ)| with hCc
  have hCc0 : 0 < Cc := by positivity
  have hlim : Tendsto (fun q : ℕ => (q : ℝ) ^ (-(μ - μ'))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (sub_pos.mpr hμ)).comp tendsto_natCast_atTop_atTop
  have hev := hlim.eventually (gt_mem_nhds hCc0)
  obtain ⟨q₁, hq₁⟩ := Filter.eventually_atTop.mp (hev.and (eventually_ge_atTop (max q₀ 1)))
  refine Filter.eventually_atTop.mpr ⟨q₁, fun q hq p => ?_⟩
  obtain ⟨hsmall, hqq⟩ := hq₁ q hq
  have hq0 : 0 < q := lt_of_lt_of_le (by omega) hqq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqge : q₀ ≤ v * q := le_trans (le_trans (le_max_left _ _) hqq) (Nat.le_mul_of_pos_left q hv)
  have key := hq₀ (v * q) hqge (u * p)
  have e1 : (r : ℝ) * x - ((u * p : ℤ) : ℝ) / ((v * q : ℕ) : ℝ) = (r : ℝ) * (x - (p : ℝ) / q) := by
    rw [hrR]; push_cast; field_simp
  rw [e1, abs_mul, Nat.cast_mul, Real.mul_rpow hvR.le hqR.le] at key
  have e2 : (q : ℝ) ^ (-μ) = (q : ℝ) ^ (-μ') * (q : ℝ) ^ (-(μ - μ')) := by
    rw [← Real.rpow_add hqR]; congr 1; ring
  have hqμ' : 0 < (q : ℝ) ^ (-μ') := Real.rpow_pos_of_pos hqR _
  have h1 : (q : ℝ) ^ (-μ) < (q : ℝ) ^ (-μ') * Cc := by
    rw [e2]; exact mul_lt_mul_of_pos_left hsmall hqμ'
  have h2 : (q : ℝ) ^ (-μ') * Cc * |(r : ℝ)| = (v : ℝ) ^ (-μ') * (q : ℝ) ^ (-μ') := by
    rw [hCc]; field_simp
  have h3 : (q : ℝ) ^ (-μ') * Cc * |(r : ℝ)| < |(r : ℝ)| * |x - (p : ℝ) / q| := by
    rw [h2]; linarith
  have : (q : ℝ) ^ (-μ') * Cc < |x - (p : ℝ) / q| := by
    have := lt_of_mul_lt_mul_left (by linarith : |(r : ℝ)| * ((q : ℝ) ^ (-μ') * Cc) <
      |(r : ℝ)| * |x - (p : ℝ) / q|) hr0.le
    exact this
  linarith

end CatalanCore.Measure
