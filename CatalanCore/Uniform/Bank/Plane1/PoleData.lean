module

public import CatalanCore.Uniform.Bank.Plane1.Frame
public import CatalanCore.Arith.Hybrid.PeriodicEntries

@[expose] public section
set_option Elab.async false

/-! # Pole data of a frame with shifts of denominator at most `3` (wave H4; ledger P102, P103)

**Lemma 2.1 of the plane theorem** (pole data for all weights at once): for a frame whose shifts `μ i = num_i / den_i`
have `den_i ≤ 3`, write `lin i k = den_i (k - 1) + num_i`, so that `k - 1 + μ i = lin i k / den_i`,
`Δ_k = Σ_i w_i den_i / lin i k` and `D_k = Σ_i w_i den_i² / lin i k ²`.  Then for a prime `p ≥ 5` and `3 N < p²`
every `lin i k` (`k < N`) is `≤ 3 N < p²`, so has `p`-adic valuation at most `1`, and none if `k` is not singular
(`p ∣ lin i k` for some `i`).  Hence `v_p(δ_k) ≥ -1`, `v_p(ε_k) ≥ -2`, and `≥ 0` off the singular set, whatever the
integer weights are: **nothing but integrality of `w` is used**, and a weight divisible by `p` only helps
(`poleData_of_shifts`).

On a plane support the singular set is `p ∣ t`, `p ∣ 3 t - ρ`, `p ∣ 2 t - 1` (`planeSing_iff`), and `planePoleData`
is the `PoleData` of the plane frame for every weight triple.  `planePoleData_entry_dsq` records the entry bounds of
Lemma 2.2: `p Δ_k` and `p² D_k` are `p`-integral, which is what the cell valuations `w(x, y)` (the instance
`Inst.planeInst`, fields `off_val`, `diag_val`) are built from. -/

namespace CatalanCore.Uniform.Bank.Plane1
open CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

section Shifts

variable (Fr : Frame)

/-- The linear form `lin i k = den_i (k - 1) + num_i` of the pole of the `i`-th atom at `k`. -/
def lin (i : Fin Fr.d) (k : ℕ) : ℕ := (Fr.μ i).den * (k - 1) + (Fr.μ i).num.toNat

variable {Fr}

theorem mu_num_pos (i : Fin Fr.d) : 0 < (Fr.μ i).num := Rat.num_pos.2 (Fr.hμ i).1

theorem mu_num_le_den (i : Fin Fr.d) : (Fr.μ i).num ≤ (Fr.μ i).den := by
  have h1 : (Fr.μ i) ≤ 1 := (Fr.hμ i).2
  have hd : (0 : ℚ) < (Fr.μ i).den := by exact_mod_cast (Fr.μ i).den_pos
  have h2 : (Fr.μ i) * (Fr.μ i).den = (Fr.μ i).num := Rat.mul_den_eq_num _
  have h3 : ((Fr.μ i).num : ℚ) ≤ (Fr.μ i).den := by
    rw [← h2]; nlinarith
  exact_mod_cast h3

theorem lin_cast (i : Fin Fr.d) {k : ℕ} (hk : 1 ≤ k) :
    (lin Fr i k : ℚ) = (Fr.μ i).den * ((k : ℚ) - 1) + (Fr.μ i).num := by
  have hn : (((Fr.μ i).num.toNat : ℤ) : ℚ) = (Fr.μ i).num := by
    have := mu_num_pos i
    exact_mod_cast Int.toNat_of_nonneg this.le
  unfold lin
  push_cast [Nat.cast_sub hk]
  rw [← hn]
  push_cast
  ring

theorem lin_cast_int (i : Fin Fr.d) {k : ℕ} (hk : 1 ≤ k) :
    (lin Fr i k : ℤ) = (Fr.μ i).den * ((k : ℤ) - 1) + (Fr.μ i).num := by
  have := mu_num_pos i
  unfold lin
  push_cast [Nat.cast_sub hk]
  rw [Int.toNat_of_nonneg this.le]

theorem lin_pos (i : Fin Fr.d) {k : ℕ} (hk : 1 ≤ k) : 0 < lin Fr i k := by
  have h := lin_cast_int i hk
  have := mu_num_pos i
  have hd := (Fr.μ i).den_pos
  have : (0 : ℤ) < lin Fr i k := by
    rw [h]; nlinarith [(by exact_mod_cast hk : (1 : ℤ) ≤ k)]
  exact_mod_cast this

theorem lin_le (i : Fin Fr.d) (hden : (Fr.μ i).den ≤ 3) {k : ℕ} (hk : 1 ≤ k) : lin Fr i k ≤ 3 * k := by
  have h := lin_cast_int i hk
  have h1 := mu_num_le_den i
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have : (lin Fr i k : ℤ) ≤ 3 * k := by
    rw [h]
    have hd : ((Fr.μ i).den : ℤ) ≤ 3 := by exact_mod_cast hden
    nlinarith
  exact_mod_cast this

theorem mu_eq (i : Fin Fr.d) {k : ℕ} (hk : 1 ≤ k) :
    (k : ℚ) - 1 + Fr.μ i = (lin Fr i k : ℚ) / (Fr.μ i).den := by
  have hd : (0 : ℚ) < (Fr.μ i).den := by exact_mod_cast (Fr.μ i).den_pos
  have h2 : Fr.μ i * (Fr.μ i).den = (Fr.μ i).num := Rat.mul_den_eq_num _
  rw [lin_cast i hk]
  field_simp
  linear_combination h2

/-- `Δ_k = Σ_i w_i den_i / lin i k`. -/
theorem Delta_lin (k : ℕ) (hk : 1 ≤ k) :
    Fr.Delta k = ∑ i, ((Fr.w i : ℚ) * (Fr.μ i).den) / (lin Fr i k : ℚ) := by
  unfold Frame.Delta
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mu_eq i hk]
  have hl : (lin Fr i k : ℚ) ≠ 0 := by exact_mod_cast (lin_pos i hk).ne'
  have hd : ((Fr.μ i).den : ℚ) ≠ 0 := by exact_mod_cast (Fr.μ i).den_nz
  field_simp

/-- `D_k = Σ_i w_i den_i² / lin i k ²`. -/
theorem Dsq_lin (k : ℕ) (hk : 1 ≤ k) :
    Fr.Dsq k = ∑ i, ((Fr.w i : ℚ) * (Fr.μ i).den ^ 2) / (lin Fr i k : ℚ) ^ 2 := by
  unfold Frame.Dsq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mu_eq i hk]
  have hl : (lin Fr i k : ℚ) ≠ 0 := by exact_mod_cast (lin_pos i hk).ne'
  have hd : ((Fr.μ i).den : ℚ) ≠ 0 := by exact_mod_cast (Fr.μ i).den_nz
  field_simp

end Shifts

/-! ### The pole data -/

section PoleDataGeneric

variable (Fr : Frame)

/-- The singular set at `p`: some atom has a pole there, `p ∣ den_i (t - 1) + num_i`. -/
def FrSing (p : ℕ) (t : ℤ) : Prop :=
  ∃ i : Fin Fr.d, (p : ℤ) ∣ (Fr.μ i).den * (t - 1) + (Fr.μ i).num

variable {Fr}

theorem FrSing_periodic (p : ℕ) (t j : ℤ) : FrSing Fr p (t + j * p) ↔ FrSing Fr p t := by
  unfold FrSing
  have e : ∀ i : Fin Fr.d, ((Fr.μ i).den : ℤ) * (t + j * p - 1) + (Fr.μ i).num =
      (((Fr.μ i).den : ℤ) * (t - 1) + (Fr.μ i).num) + ((Fr.μ i).den * j) * p := by
    intro i; ring
  constructor
  · rintro ⟨i, hi⟩
    rw [e i] at hi
    exact ⟨i, (dvd_add_left (dvd_mul_left (p : ℤ) _)).1 hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [e i]; exact dvd_add hi (dvd_mul_left (p : ℤ) _)⟩

variable {p N : ℕ} [Fact p.Prime]

theorem lin_lt_sq (i : Fin Fr.d) (hden : (Fr.μ i).den ≤ 3) (hN : 3 * N < p * p) {k : ℕ} (hk : 1 ≤ k)
    (hkN : k < N) : lin Fr i k < p * p := by
  have := lin_le i hden hk
  omega

theorem good_lin_inv (i : Fin Fr.d) (hden : (Fr.μ i).den ≤ 3) (hN : 3 * N < p * p) {k : ℕ} (hk : 1 ≤ k)
    (hkN : k < N) : Good p ((p : ℚ) / (lin Fr i k : ℚ)) (invResidue p (lin Fr i k)) :=
  good_scaled_inverse (lin_pos i hk) (lin_lt_sq i hden hN hk hkN)

/-- **Lemma 2.1 for any frame with shift denominators `≤ 3` and a `p`-unit norm.** -/
noncomputable def poleData_of_shifts (hden : ∀ i, (Fr.μ i).den ≤ 3) (hN : 3 * N < p * p)
    (hn : Fr.norm ∈ S p) (hn0 : red p Fr.norm ≠ 0) : PoleData Fr p N where
  singular := fun t => FrSing Fr p t
  periodic := FrSing_periodic p
  norm_mem := hn
  norm_ne := hn0
  delta_mem := by
    intro k hk hkN
    rw [Delta_lin k hk, Finset.mul_sum]
    refine (Good.sum _ _ (fun i => ((Fr.w i : ℤ) * (Fr.μ i).den : ZMod p) *
      invResidue p (lin Fr i k)) (fun i _ => ?_)).mem
    have g := (Good.intCast (ℓ := p) (Fr.w i * ((Fr.μ i).den : ℤ))).mul
      (good_lin_inv i (hden i) hN hk hkN)
    refine (g.congr' ?_).congr ?_
    · push_cast; ring
    · push_cast; rfl
  dsq_mem := by
    intro k hk hkN
    rw [Dsq_lin k hk, Finset.mul_sum]
    refine (Good.sum _ _ (fun i => ((Fr.w i * ((Fr.μ i).den : ℤ) ^ 2 : ℤ) : ZMod p) *
      invResidue p (lin Fr i k) ^ 2) (fun i _ => ?_)).mem
    have g := (Good.intCast (ℓ := p) (Fr.w i * ((Fr.μ i).den : ℤ) ^ 2)).mul
      ((good_lin_inv i (hden i) hN hk hkN).pow' 2)
    refine g.congr' ?_
    push_cast; ring
  regular_delta := by
    intro k hk hkN hs
    rw [Delta_lin k hk]
    refine (Good.sum _ _ (fun i => ((Fr.w i * ((Fr.μ i).den : ℤ) : ℤ) : ZMod p) *
      ((lin Fr i k : ℕ) : ZMod p)⁻¹) (fun i _ => ?_)).mem
    have hne : ((lin Fr i k : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      apply hs
      refine ⟨i, ?_⟩
      have := Int.natCast_dvd_natCast.2 hd
      rwa [lin_cast_int i hk] at this
    have g := (Good.intCast (ℓ := p) (Fr.w i * ((Fr.μ i).den : ℤ))).mul
      ((Good.natCast (ℓ := p) (lin Fr i k)).inv hne)
    refine g.congr' ?_
    push_cast; rw [div_eq_mul_inv]
  regular_dsq := by
    intro k hk hkN hs
    rw [Dsq_lin k hk]
    refine (Good.sum _ _ (fun i => ((Fr.w i * ((Fr.μ i).den : ℤ) ^ 2 : ℤ) : ZMod p) *
      (((lin Fr i k : ℕ) : ZMod p)⁻¹) ^ 2) (fun i _ => ?_)).mem
    have hne : ((lin Fr i k : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      apply hs
      refine ⟨i, ?_⟩
      have := Int.natCast_dvd_natCast.2 hd
      rwa [lin_cast_int i hk] at this
    have g := (Good.intCast (ℓ := p) (Fr.w i * ((Fr.μ i).den : ℤ) ^ 2)).mul
      (((Good.natCast (ℓ := p) (lin Fr i k)).inv hne).pow' 2)
    refine g.congr' ?_
    push_cast; rw [div_eq_mul_inv, inv_pow]

end PoleDataGeneric

/-! ### The plane supports -/

section Plane

variable (σ : Support) (a b c : ℤ) (h0 : a + b + c = 0)

theorem shift_den (σ : Support) : σ.shift.den = 3 := by cases σ <;> decide +kernel

theorem shift_num (σ : Support) : σ.shift.num = 3 - (σ.rho : ℤ) := by cases σ <;> decide +kernel

theorem half_den : (1 / 2 : ℚ).den = 2 := by decide +kernel
theorem half_num : (1 / 2 : ℚ).num = 1 := by decide +kernel
theorem one_den : (1 : ℚ).den = 1 := by decide +kernel
theorem one_num : (1 : ℚ).num = 1 := by decide +kernel

theorem plane_den_le (i : Fin (planeFrame σ a b c h0).d) : ((planeFrame σ a b c h0).μ i).den ≤ 3 := by
  obtain ⟨k, hk⟩ := i
  have hk3 : k < 3 := hk
  interval_cases k
  · show σ.shift.den ≤ 3
    rw [shift_den]
  · show (1 / 2 : ℚ).den ≤ 3
    rw [half_den]; norm_num
  · show (1 : ℚ).den ≤ 3
    rw [one_den]; norm_num

/-- The singular set of a plane frame: `p ∣ t`, `p ∣ 3 t - ρ`, `p ∣ 2 t - 1`. -/
theorem planeSing_iff (p : ℕ) (t : ℤ) :
    FrSing (planeFrame σ a b c h0) p t ↔
      ((p : ℤ) ∣ t ∨ (p : ℤ) ∣ 3 * t - (σ.rho : ℤ) ∨ (p : ℤ) ∣ 2 * t - 1) := by
  unfold FrSing
  have e0 : ((σ.shift.den : ℤ) * (t - 1) + σ.shift.num) = 3 * t - (σ.rho : ℤ) := by
    rw [shift_den, shift_num]; push_cast; ring
  have e1 : (((1 / 2 : ℚ).den : ℤ) * (t - 1) + (1 / 2 : ℚ).num) = 2 * t - 1 := by
    rw [half_den, half_num]; push_cast; ring
  have e2 : (((1 : ℚ).den : ℤ) * (t - 1) + (1 : ℚ).num) = t := by
    rw [one_den, one_num]; push_cast; ring
  constructor
  · rintro ⟨⟨k, hk⟩, hi⟩
    have hk3 : k < 3 := hk
    interval_cases k
    · change (p : ℤ) ∣ ((σ.shift.den : ℤ) * (t - 1) + σ.shift.num) at hi
      rw [e0] at hi; exact Or.inr (Or.inl hi)
    · change (p : ℤ) ∣ (((1 / 2 : ℚ).den : ℤ) * (t - 1) + (1 / 2 : ℚ).num) at hi
      rw [e1] at hi; exact Or.inr (Or.inr hi)
    · change (p : ℤ) ∣ (((1 : ℚ).den : ℤ) * (t - 1) + (1 : ℚ).num) at hi
      rw [e2] at hi; exact Or.inl hi
  · rintro (h | h | h)
    · refine ⟨⟨2, by show 2 < 3; norm_num⟩, ?_⟩
      change (p : ℤ) ∣ (((1 : ℚ).den : ℤ) * (t - 1) + (1 : ℚ).num)
      rw [e2]; exact h
    · refine ⟨⟨0, by show 0 < 3; norm_num⟩, ?_⟩
      change (p : ℤ) ∣ ((σ.shift.den : ℤ) * (t - 1) + σ.shift.num)
      rw [e0]; exact h
    · refine ⟨⟨1, by show 1 < 3; norm_num⟩, ?_⟩
      change (p : ℤ) ∣ (((1 / 2 : ℚ).den : ℤ) * (t - 1) + (1 / 2 : ℚ).num)
      rw [e1]; exact h

variable {p N : ℕ} [Fact p.Prime]

/-- **The pole data of the plane frames** (P102): every weight triple of sum zero, norm `1`. -/
noncomputable def planePoleData (hN : 3 * N < p * p) : PoleData (planeFrame σ a b c h0) p N :=
  poleData_of_shifts (plane_den_le σ a b c h0) hN
    (by show (1 : ℚ) ∈ S p; exact (S p).one_mem)
    (by show red p (1 : ℚ) ≠ 0; simp [red])

theorem planePoleData_singular (hN : 3 * N < p * p) (t : ℤ) :
    (planePoleData σ a b c h0 hN).singular t ↔
      ((p : ℤ) ∣ t ∨ (p : ℤ) ∣ 3 * t - (σ.rho : ℤ) ∨ (p : ℤ) ∣ 2 * t - 1) :=
  planeSing_iff σ a b c h0 p t

/-- **Entry bounds** (Lemma 2.2, P103), in the form the valuation count reads: `p δ_k` and `p² ε_k` are
`p`-integral for `1 ≤ k < N`, and `δ_k`, `ε_k` are `p`-integral off the singular set. -/
theorem planePoleData_entry (hN : 3 * N < p * p) {k : ℕ} (hk : 1 ≤ k) (hkN : k < N) :
    ((p : ℚ) * (planeFrame σ a b c h0).Delta k ∈ S p ∧ (p : ℚ) ^ 2 * (planeFrame σ a b c h0).Dsq k ∈ S p) ∧
    (¬ ((p : ℤ) ∣ k ∨ (p : ℤ) ∣ 3 * k - (σ.rho : ℤ) ∨ (p : ℤ) ∣ 2 * k - 1) →
      (planeFrame σ a b c h0).Delta k ∈ S p ∧ (planeFrame σ a b c h0).Dsq k ∈ S p) := by
  refine ⟨⟨(planePoleData σ a b c h0 hN).delta_mem k hk hkN,
    (planePoleData σ a b c h0 hN).dsq_mem k hk hkN⟩, fun hs => ?_⟩
  have hs' : ¬ (planePoleData σ a b c h0 hN).singular (k : ℤ) := by
    rw [planePoleData_singular σ a b c h0 hN]; exact hs
  exact ⟨(planePoleData σ a b c h0 hN).regular_delta k hk hkN hs',
    (planePoleData σ a b c h0 hN).regular_dsq k hk hkN hs'⟩

end Plane

end CatalanCore.Uniform.Bank.Plane1

#print axioms CatalanCore.Uniform.Bank.Plane1.poleData_of_shifts
#print axioms CatalanCore.Uniform.Bank.Plane1.planePoleData
#print axioms CatalanCore.Uniform.Bank.Plane1.planeSing_iff
#print axioms CatalanCore.Uniform.Bank.Plane1.planePoleData_entry
