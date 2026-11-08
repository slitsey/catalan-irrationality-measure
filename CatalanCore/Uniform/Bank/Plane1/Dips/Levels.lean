module

public import CatalanCore.Uniform.Bank.Plane1.Dips.PeriodSum

@[expose] public section
set_option Elab.async false
set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

/-! # The levels in closed form (wave R0; ledger R01-R03; the bridge from `Vp`, `Up` to the cells)

For an atom `i` of the frame with `p ∤ den_i` the polar indices `k ≥ 1` (`p ∣ lin i k`) are exactly `k₀ + u p`,
`u ≥ 0`, where `k₀ = k0 p Fr i ∈ [1, p]` is the first one (`polar_iff`); the cofactor `lin i k / p` of the `u`-th polar
index is `m₀ + den_i u` (`m₀ = lin i k₀ / p`).  Hence the polar part of any function of the cofactor sums over
`u < U t`, `U t = ⌊(t - k₀)/p⌋ + 1` for `t ≥ k₀`, and `0` before (`polar_sum`).  This is the explicit form of the level
`V(t)` and of `U(t)` of the paper: they depend on `t` only through the three counts `U` of the three atoms. -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid

section FirstPolar

variable {p : ℕ} [hp : Fact p.Prime] {Fr : Frame}

/-- The first polar index of the atom `i` (in `[1, p]`). -/
noncomputable def k0 (p : ℕ) [Fact p.Prime] (Fr : Frame) (i : Fin Fr.d) : ℕ :=
  ((-((Fr.μ i).num.toNat : ZMod p) * (((Fr.μ i).den : ZMod p))⁻¹ : ZMod p).val) + 1

theorem k0_pos (i : Fin Fr.d) : 1 ≤ k0 p Fr i := Nat.succ_le_succ (Nat.zero_le _)

theorem k0_le (i : Fin Fr.d) : k0 p Fr i ≤ p := by
  unfold k0
  have := ZMod.val_lt (-((Fr.μ i).num.toNat : ZMod p) * (((Fr.μ i).den : ZMod p))⁻¹ : ZMod p)
  omega

theorem lin_zmod (i : Fin Fr.d) {k : ℕ} (hk : 1 ≤ k) :
    ((lin Fr i k : ℕ) : ZMod p) = ((Fr.μ i).den : ZMod p) * ((k - 1 : ℕ) : ZMod p) + ((Fr.μ i).num.toNat : ZMod p) := by
  unfold lin
  push_cast
  ring

/-- **The polar indices of an atom**: `k₀ + u p`. -/
theorem polar_iff (i : Fin Fr.d) (hdp : ¬ p ∣ (Fr.μ i).den) {k : ℕ} (hk : 1 ≤ k) :
    p ∣ lin Fr i k ↔ k0 p Fr i ≤ k ∧ p ∣ k - k0 p Fr i := by
  have hd : ((Fr.μ i).den : ZMod p) ≠ 0 := fun h => hdp ((ZMod.natCast_eq_zero_iff _ _).1 h)
  set x0 : ZMod p := (-((Fr.μ i).num.toNat : ZMod p) * (((Fr.μ i).den : ZMod p))⁻¹) with hx0
  have hk0 : k0 p Fr i = x0.val + 1 := rfl
  have hval : x0.val < p := ZMod.val_lt x0
  have hcast : ((k0 p Fr i - 1 : ℕ) : ZMod p) = x0 := by
    rw [hk0, Nat.add_sub_cancel, ZMod.natCast_zmod_val]
  have hmod : (k0 p Fr i - 1) % p = k0 p Fr i - 1 := Nat.mod_eq_of_lt (by omega)
  -- p ∣ lin ↔ (k - 1 : ZMod p) = x0
  have key : p ∣ lin Fr i k ↔ ((k - 1 : ℕ) : ZMod p) = x0 := by
    rw [← ZMod.natCast_eq_zero_iff, lin_zmod i hk]
    constructor
    · intro h
      have : ((k - 1 : ℕ) : ZMod p) = -(((Fr.μ i).num.toNat : ZMod p)) * (((Fr.μ i).den : ZMod p))⁻¹ := by
        field_simp
        linear_combination h
      rw [hx0]; exact this
    · intro h
      rw [h, hx0]
      field_simp
      ring
  rw [key, ← hcast, ZMod.natCast_eq_natCast_iff']
  rw [hmod]
  constructor
  · intro h
    have hlt : k0 p Fr i ≤ k := by
      by_contra hlt
      have : (k - 1) % p = k - 1 := Nat.mod_eq_of_lt (by omega)
      omega
    refine ⟨hlt, ?_⟩
    have : (k - 1) % p = (k0 p Fr i - 1) % p := by rw [hmod]; exact h
    have h2 : k - k0 p Fr i = (k - 1) - (k0 p Fr i - 1) := by omega
    rw [h2]
    exact (Nat.modEq_iff_dvd' (by omega)).1 this.symm
  · rintro ⟨hlt, hdv⟩
    obtain ⟨u, hu⟩ := hdv
    have : k - 1 = (k0 p Fr i - 1) + p * u := by omega
    rw [this, Nat.add_mul_mod_self_left, hmod]

end FirstPolar

section PolarSum

variable {p : ℕ} [hp : Fact p.Prime] {Fr : Frame}

/-- The number of polar indices `≤ t` of the atom `i`. -/
noncomputable def Ucnt (p : ℕ) [Fact p.Prime] (Fr : Frame) (i : Fin Fr.d) (t : ℕ) : ℕ :=
  if k0 p Fr i ≤ t then (t - k0 p Fr i) / p + 1 else 0

/-- The cofactor of the first polar index. -/
noncomputable def m0 (p : ℕ) [Fact p.Prime] (Fr : Frame) (i : Fin Fr.d) : ℕ := lin Fr i (k0 p Fr i) / p

theorem lin_k0 (i : Fin Fr.d) (hdp : ¬ p ∣ (Fr.μ i).den) : lin Fr i (k0 p Fr i) = p * m0 p Fr i := by
  have h := (polar_iff i hdp (k0_pos i)).2 ⟨le_refl _, by simp⟩
  unfold m0
  exact (Nat.mul_div_cancel' h).symm

theorem lin_add (i : Fin Fr.d) {k u : ℕ} (hk : 1 ≤ k) :
    lin Fr i (k + p * u) = lin Fr i k + (Fr.μ i).den * (p * u) := by
  unfold lin
  rw [show k + p * u - 1 = (k - 1) + p * u by omega]
  ring

theorem lin_polar (i : Fin Fr.d) (hdp : ¬ p ∣ (Fr.μ i).den) {u : ℕ} :
    lin Fr i (k0 p Fr i + p * u) = p * (m0 p Fr i + (Fr.μ i).den * u) := by
  rw [lin_add i (k0_pos i), lin_k0 i hdp]
  ring

theorem Ucnt_succ (i : Fin Fr.d) (hdp : ¬ p ∣ (Fr.μ i).den) (t : ℕ) :
    Ucnt p Fr i (t + 1) = Ucnt p Fr i t + (if p ∣ lin Fr i (t + 1) then 1 else 0) := by
  have hpos := hp.out.pos
  by_cases hpol : p ∣ lin Fr i (t + 1)
  · rw [if_pos hpol]
    obtain ⟨hle, u, hu⟩ := (polar_iff i hdp (by omega : 1 ≤ t + 1)).1 hpol
    have e1 : (t + 1 - k0 p Fr i) / p = u := by
      rw [hu]; exact Nat.mul_div_cancel_left u hpos
    unfold Ucnt
    rw [if_pos hle, e1]
    rcases Nat.eq_zero_or_pos u with h0 | h0
    · subst h0
      have : ¬ k0 p Fr i ≤ t := by omega
      rw [if_neg this]
    · have hle' : k0 p Fr i ≤ t := by
        by_contra hc
        have : t + 1 = k0 p Fr i := by omega
        have : p * u = 0 := by omega
        rcases Nat.mul_eq_zero.1 this with h | h
        · omega
        · omega
      rw [if_pos hle']
      have : (t - k0 p Fr i) / p = u - 1 := by
        obtain ⟨u', rfl⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
        have h1 : t - k0 p Fr i = p * u' + (p - 1) := by
          rw [Nat.mul_succ] at hu; omega
        rw [h1, Nat.mul_add_div hpos, Nat.div_eq_of_lt (by omega)]
        simp
      rw [this]
      omega
  · rw [if_neg hpol]
    unfold Ucnt
    by_cases hle : k0 p Fr i ≤ t + 1
    · have hle' : k0 p Fr i ≤ t := by
        by_contra hc
        have : t + 1 = k0 p Fr i := by omega
        exact hpol ((polar_iff i hdp (by omega : 1 ≤ t + 1)).2 ⟨hle, by rw [this]; simp⟩)
      have hnd : ¬ p ∣ t + 1 - k0 p Fr i := fun h => hpol ((polar_iff i hdp (by omega : 1 ≤ t + 1)).2 ⟨hle, h⟩)
      rw [if_pos hle, if_pos hle']
      have : t + 1 - k0 p Fr i = (t - k0 p Fr i) + 1 := by omega
      rw [this, Nat.succ_div_of_not_dvd (by rw [← this]; exact hnd)]
    · have : ¬ k0 p Fr i ≤ t := by omega
      rw [if_neg hle, if_neg this]

/-- **Sum over the polar indices**: the polar part of a function of the cofactor, in closed form. -/
theorem polar_sum (i : Fin Fr.d) (hdp : ¬ p ∣ (Fr.μ i).den) (g : ℕ → ℚ) (t : ℕ) :
    ∑ k ∈ Ioc 0 t, (if p ∣ lin Fr i k then g (lin Fr i k / p) else 0) =
      ∑ u ∈ range (Ucnt p Fr i t), g (m0 p Fr i + (Fr.μ i).den * u) := by
  induction t with
  | zero =>
    have : Ucnt p Fr i 0 = 0 := by
      unfold Ucnt
      rw [if_neg (by have := k0_pos (p := p) (Fr := Fr) i; omega)]
    simp [this]
  | succ t ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih, Ucnt_succ i hdp t]
    by_cases hpol : p ∣ lin Fr i (t + 1)
    · rw [if_pos hpol, if_pos hpol, Finset.sum_range_succ]
      congr 1
      obtain ⟨hle, u, hu⟩ := (polar_iff i hdp (by omega : 1 ≤ t + 1)).1 hpol
      have e : t + 1 = k0 p Fr i + p * u := by omega
      have hU : Ucnt p Fr i t = u := by
        have := Ucnt_succ i hdp t
        rw [if_pos hpol] at this
        have e2 : Ucnt p Fr i (t + 1) = u + 1 := by
          unfold Ucnt
          rw [if_pos hle, show t + 1 - k0 p Fr i = p * u from hu, Nat.mul_div_cancel_left u hp.out.pos]
        omega
      rw [hU, e, lin_polar i hdp, Nat.mul_div_cancel_left _ hp.out.pos]
    · rw [if_neg hpol, if_neg hpol]
      simp

end PolarSum

section Closed

variable {p : ℕ} [hp : Fact p.Prime] {Fr : Frame}

/-- A polar index has a positive cofactor. -/
theorem lin_div_pos (i : Fin Fr.d) {k : ℕ} (hk : 1 ≤ k) (h : p ∣ lin Fr i k) : 0 < lin Fr i k / p := by
  obtain ⟨m, hm⟩ := h
  have := lin_pos i hk
  rw [hm, Nat.mul_div_cancel_left _ hp.out.pos]
  rcases Nat.eq_zero_or_pos m with h0 | h0
  · subst h0; omega
  · exact h0

theorem polar_term (i : Fin Fr.d) {k : ℕ} (hk : 1 ≤ k) (h : p ∣ lin Fr i k) (c : ℚ) :
    (p : ℚ) * c / (lin Fr i k : ℚ) = c / ((lin Fr i k / p : ℕ) : ℚ) := by
  obtain ⟨m, hm⟩ := h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hm0 := lin_div_pos i hk ⟨m, hm⟩
  rw [hm, Nat.mul_div_cancel_left _ hp.out.pos] at hm0 ⊢
  have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
  push_cast
  field_simp

theorem polar_term2 (i : Fin Fr.d) {k : ℕ} (hk : 1 ≤ k) (h : p ∣ lin Fr i k) (c : ℚ) :
    (p : ℚ) ^ 2 * c / (lin Fr i k : ℚ) ^ 2 = c / ((lin Fr i k / p : ℕ) : ℚ) ^ 2 := by
  obtain ⟨m, hm⟩ := h
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hm0 := lin_div_pos i hk ⟨m, hm⟩
  rw [hm, Nat.mul_div_cancel_left _ hp.out.pos] at hm0 ⊢
  have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0.ne'
  push_cast
  field_simp

variable (hden : ∀ i, (Fr.μ i).den ≤ 3) (h5 : 5 ≤ p)

include hden h5 in
theorem not_dvd_den (i : Fin Fr.d) : ¬ p ∣ (Fr.μ i).den := fun h => by
  have := Nat.le_of_dvd (Fr.μ i).den_pos h
  have := hden i
  omega

include hden h5 in
/-- **The level `V(t)` in closed form**: `Σ_i Σ_{u < U_i(t)} w_i den_i / (m₀ᵢ + den_i u)`. -/
theorem Vp_closed (t : ℕ) :
    Vp p Fr t = ∑ i : Fin Fr.d, ∑ u ∈ range (Ucnt p Fr i t),
      ((Fr.w i : ℚ) * (Fr.μ i).den) / ((m0 p Fr i + (Fr.μ i).den * u : ℕ) : ℚ) := by
  unfold Vp dvP
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := polar_sum (p := p) (Fr := Fr) i (not_dvd_den hden h5 i)
    (fun m => ((Fr.w i : ℚ) * (Fr.μ i).den) / (m : ℚ)) t
  rw [← this]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Ioc.1 hk).1
  by_cases h : p ∣ lin Fr i k
  · simp only [h, ite_true]
    exact polar_term i hk1 h _
  · simp [h]

include hden h5 in
/-- **The level `U(t)` in closed form**. -/
theorem Up_closed (t : ℕ) :
    Up p Fr t = -∑ i : Fin Fr.d, ∑ u ∈ range (Ucnt p Fr i t),
      ((Fr.w i : ℚ) * (Fr.μ i).den ^ 2) / ((m0 p Fr i + (Fr.μ i).den * u : ℕ) : ℚ) ^ 2 := by
  unfold Up dsP
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have := polar_sum (p := p) (Fr := Fr) i (not_dvd_den hden h5 i)
    (fun m => ((Fr.w i : ℚ) * (Fr.μ i).den ^ 2) / (m : ℚ) ^ 2) t
  rw [← this]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Ioc.1 hk).1
  by_cases h : p ∣ lin Fr i k
  · simp only [h, ite_true]
    exact polar_term2 i hk1 h _
  · simp [h]

/-- The first polar index is determined by lying in `[1, p]`. -/
theorem k0_eq_of (i : Fin Fr.d) (hdp : ¬ p ∣ (Fr.μ i).den) {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ p)
    (h : p ∣ lin Fr i k) : k0 p Fr i = k := by
  obtain ⟨hle, u, hu⟩ := (polar_iff i hdp hk).1 h
  have := k0_le (p := p) i
  have := k0_pos (p := p) (Fr := Fr) i
  have hp1 := hp.out.pos
  rcases Nat.eq_zero_or_pos u with h0 | h0
  · subst h0; omega
  · have : p * 1 ≤ p * u := Nat.mul_le_mul_left p h0
    omega

end Closed

section Node

variable {p : ℕ} [hp : Fact p.Prime] {Fr : Frame}

theorem Ucnt_aux (i : Fin Fr.d) (q ξ : ℕ) (hξ : ξ < p) :
    Ucnt p Fr i (p * q + ξ) = q + (if k0 p Fr i ≤ ξ then 1 else 0) := by
  have hpos := hp.out.pos
  have hk1 := k0_pos (p := p) (Fr := Fr) i
  have hkp := k0_le (p := p) (Fr := Fr) i
  unfold Ucnt
  by_cases hx : k0 p Fr i ≤ ξ
  · have h : k0 p Fr i ≤ p * q + ξ := by omega
    rw [if_pos h, if_pos hx]
    have : p * q + ξ - k0 p Fr i = p * q + (ξ - k0 p Fr i) := by omega
    rw [this, Nat.mul_add_div hpos, Nat.div_eq_of_lt (by omega)]
  · rw [if_neg hx]
    rcases Nat.eq_zero_or_pos q with hq0 | hq1
    · subst hq0
      have : ¬ k0 p Fr i ≤ p * 0 + ξ := by omega
      rw [if_neg this]
    · have h : k0 p Fr i ≤ p * q + ξ := by
        have : p ≤ p * q := Nat.le_mul_of_pos_right p hq1
        omega
      rw [if_pos h]
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have : p * (q' + 1) + ξ - k0 p Fr i = p * q' + (p + ξ - k0 p Fr i) := by
        rw [Nat.mul_succ]; omega
      rw [this, Nat.mul_add_div hpos, Nat.div_eq_of_lt (by omega)]

/-- **The count of polar indices at a node**: `U_i(t) = ⌊t/p⌋ + 1[t mod p ≥ k₀]`. -/
theorem Ucnt_eq (i : Fin Fr.d) (t : ℕ) :
    Ucnt p Fr i t = t / p + (if k0 p Fr i ≤ t % p then 1 else 0) := by
  have := Ucnt_aux (p := p) (Fr := Fr) i (t / p) (t % p) (Nat.mod_lt t hp.out.pos)
  rwa [Nat.div_add_mod] at this

end Node

#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Ucnt_eq
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Vp_closed
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Up_closed

end CatalanCore.Uniform.Bank.Plane1.Dips
