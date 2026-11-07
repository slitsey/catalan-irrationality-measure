module

public import CatalanCore.Uniform.Support.Content
public import CatalanCore.Arith.Hybrid.RankGLE
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

/-!
# Cells, polar sums and the weight table of the plane 2 sequences (lane H, wave H2; ledger N1)

Fix integers `(v, u)` and a prime `p ≥ 5` (the plane 2 datum `Datum.plane2 v u`, `a = (u, -u)`,
`b = (v, 0)`).  With `κ = k + 1`, the increments of the Löwner data are

* `f_t = ∑_{κ=1}^{t} Δ_κ`,  `Δ_κ = u/κ - v/κ² - 2u/(2κ - 1)`,
* `e_t = ∑_{κ=1}^{t} E_κ`,  `E_κ = u/κ² - 2v/κ³ - 4u/(2κ - 1)²`,

with poles only where `p ∣ κ` (double, order 2 and 3) or `p ∣ 2κ - 1` (simple, order 1 and 2).

* **Polar sums.**  `polF`, `polE` are the singular terms of `Δ_κ`, `E_κ` (the `if`s of the two poles);
  `PF t = ∑ polF`, `PE t = ∑ polE` (the polar sums `S`, `G` of the paper), and the regular remainders
  `RF t = ∑ regF` (the `ρ_t`), `RE t = ∑ regE` (the `γ_t`) are `p`-integral (`regF_mem`, `regE_mem`),
  `f_t = PF t + RF t`, `e_t = PE t + RE t`.
* **Cells.** The *period* of `t` is `⌊t/p⌋`, its *half* is `1` if `2 (t mod p) ≥ p + 1`, else `0`; the cell
  is the pair.  A cell boundary lies at each pole: inside a cell no singular `κ` occurs
  (`no_pole_same_cell`), inside a period no `κ` with `p ∣ κ` (`no_mult_same_period`).
* **Lemma 2.1.**  `t ≡ t' (mod p)` gives `RF t' ≡ RF t (mod p)` (`regF_congr`): the difference is a sum over
  complete residue systems of `Δ`, whose reduction mod `p` is `u ∑ r⁻¹ - v ∑ r⁻² - 2u ∑ (2r-1)⁻¹ = 0`
  for `p ≥ 5`.
* **Weight table** (`weight_table`): `p^{W(s,t)} · lw f e s t` is `p`-integral for `s, t < N`, `2N < p²`, where
  `W = 3` if `s ≡ t`, `s ≠ t`; otherwise `W₃`: `0` in one cell, `1` in one period (other half), `2` in
  different periods; on the diagonal `3` in period `≥ 1`, `2` in cell `(0,1)`, `0` in cell `(0,0)`.
* **Lemma 2.2** (`det_gle_of_dual`): if `u` on rows and `u'` on columns are natural potentials with
  `W ≤ u + u'` then every coefficient of the determinant of the member is `p^{∑u + ∑u'}`-integral.

Everything is generic in `(v, u)`, in `p`, in the nodes.
-/

open Polynomial Finset Matrix CatalanCore.Basic CatalanCore.Arith.Hybrid
open CatalanCore.Uniform.Support

namespace CatalanCore.Uniform.Content.Sweep

section Terms

variable (v u : ℤ) (p : ℕ)

/-- The two pole terms of `Δ_κ`. -/
noncomputable def T1 (κ : ℕ) : ℚ := (u : ℚ) / κ - (v : ℚ) / (κ : ℚ) ^ 2
noncomputable def T2 (κ : ℕ) : ℚ := -2 * (u : ℚ) / (2 * (κ : ℚ) - 1)
/-- The two pole terms of `E_κ`. -/
noncomputable def U1 (κ : ℕ) : ℚ := (u : ℚ) / (κ : ℚ) ^ 2 - 2 * (v : ℚ) / (κ : ℚ) ^ 3
noncomputable def U2 (κ : ℕ) : ℚ := -4 * (u : ℚ) / (2 * (κ : ℚ) - 1) ^ 2

/-- Polar and regular parts of `Δ_κ`. -/
noncomputable def polF (κ : ℕ) : ℚ :=
  (if p ∣ κ then T1 v u κ else 0) + (if p ∣ 2 * κ - 1 then T2 u κ else 0)
noncomputable def regF (κ : ℕ) : ℚ :=
  (if p ∣ κ then 0 else T1 v u κ) + (if p ∣ 2 * κ - 1 then 0 else T2 u κ)
/-- Polar and regular parts of `E_κ`. -/
noncomputable def polE (κ : ℕ) : ℚ :=
  (if p ∣ κ then U1 v u κ else 0) + (if p ∣ 2 * κ - 1 then U2 u κ else 0)
noncomputable def regE (κ : ℕ) : ℚ :=
  (if p ∣ κ then 0 else U1 v u κ) + (if p ∣ 2 * κ - 1 then 0 else U2 u κ)

/-- The polar sums `S`, `G` and the integral remainders `ρ`, `γ`, over `κ = 1, …, t`. -/
noncomputable def PF (t : ℕ) : ℚ := ∑ k ∈ range t, polF v u p (k + 1)
noncomputable def RF (t : ℕ) : ℚ := ∑ k ∈ range t, regF v u p (k + 1)
noncomputable def PE (t : ℕ) : ℚ := ∑ k ∈ range t, polE v u p (k + 1)
noncomputable def RE (t : ℕ) : ℚ := ∑ k ∈ range t, regE v u p (k + 1)

theorem polF_add_regF (κ : ℕ) : polF v u p κ + regF v u p κ = T1 v u κ + T2 u κ := by
  unfold polF regF
  by_cases h1 : p ∣ κ <;> by_cases h2 : p ∣ 2 * κ - 1 <;> simp [h1, h2, add_comm]

theorem polE_add_regE (κ : ℕ) : polE v u p κ + regE v u p κ = U1 v u κ + U2 u κ := by
  unfold polE regE
  by_cases h1 : p ∣ κ <;> by_cases h2 : p ∣ 2 * κ - 1 <;> simp [h1, h2, add_comm]

theorem delta_eq (hv : v ≠ 0) (hu : u ≠ 0) (k : ℕ) :
    (Datum.plane2 v u hv hu).delta k = T1 v u (k + 1) + T2 u (k + 1) := by
  rw [plane2_delta]
  unfold T1 T2
  have e : (2 * ((k + 1 : ℕ) : ℚ) - 1) = 2 * ((k : ℚ) + 1 / 2) := by push_cast; ring
  have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((k : ℚ) + 1 / 2) ≠ 0 := by positivity
  rw [e]
  push_cast
  field_simp
  ring

theorem delta1_eq (hv : v ≠ 0) (hu : u ≠ 0) (k : ℕ) :
    -(Datum.plane2 v u hv hu).delta1 k = U1 v u (k + 1) + U2 u (k + 1) := by
  rw [plane2_delta1]
  unfold U1 U2
  have e : (2 * ((k + 1 : ℕ) : ℚ) - 1) = 2 * ((k : ℚ) + 1 / 2) := by push_cast; ring
  have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((k : ℚ) + 1 / 2) ≠ 0 := by positivity
  rw [e]
  push_cast
  field_simp
  ring

/-- `f_t = S + ρ`: the polar and regular sums. -/
theorem f_eq (hv : v ≠ 0) (hu : u ≠ 0) (t : ℕ) :
    (Datum.plane2 v u hv hu).f t = PF v u p t + RF v u p t := by
  unfold Datum.f PF RF
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [delta_eq v u hv hu, polF_add_regF]

/-- `e_t = G + γ`. -/
theorem e_eq (hv : v ≠ 0) (hu : u ≠ 0) (t : ℕ) :
    (Datum.plane2 v u hv hu).e t = PE v u p t + RE v u p t := by
  unfold Datum.e PE RE
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [delta1_eq v u hv hu, polE_add_regE]

end Terms

/-! ### The calculus of `p^{-w} ℤ_(p)` -/

section Vp

/-- `x ∈ p^{-w} ℤ_(p)`: valuation at least `-w`. -/
def Vp (p : ℕ) [Fact p.Prime] (w : ℕ) (x : ℚ) : Prop := (p : ℚ) ^ w * x ∈ LocRing p

variable {p : ℕ} [hp : Fact p.Prime] {w w' : ℕ} {x y : ℚ}

theorem Vp.mono (h : w ≤ w') (hx : Vp p w x) : Vp p w' x :=
  Content.BankShared.mem_of_le (p := p) h hx

theorem Vp.of_mem (hx : x ∈ LocRing p) : Vp p w x := by
  unfold Vp
  exact (LocRing p).mul_mem (by exact_mod_cast (int_mem_locRing (ℓ := p) ((p : ℤ) ^ w))) hx

theorem Vp.zero_iff : Vp p 0 x ↔ x ∈ LocRing p := by simp [Vp]

theorem Vp.add (hx : Vp p w x) (hy : Vp p w y) : Vp p w (x + y) := by
  unfold Vp at *; rw [mul_add]; exact (LocRing p).add_mem hx hy

theorem Vp.sub (hx : Vp p w x) (hy : Vp p w y) : Vp p w (x - y) := by
  unfold Vp at *; rw [mul_sub]; exact (LocRing p).sub_mem hx hy

theorem Vp.neg (hx : Vp p w x) : Vp p w (-x) := by
  unfold Vp at *; rw [mul_neg]; exact (LocRing p).neg_mem hx

theorem Vp.zero : Vp p w 0 := by unfold Vp; simpa using (LocRing p).zero_mem

theorem Vp.sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, Vp p w (f i)) :
    Vp p w (∑ i ∈ s, f i) := by
  unfold Vp at *; rw [Finset.mul_sum]; exact (LocRing p).sum_mem h

theorem Vp.mul_mem (hy : y ∈ LocRing p) (hx : Vp p w x) : Vp p w (y * x) := by
  unfold Vp at *
  have : (p : ℚ) ^ w * (y * x) = y * ((p : ℚ) ^ w * x) := by ring
  rw [this]; exact (LocRing p).mul_mem hy hx

theorem Vp.int_mul (m : ℤ) (hx : Vp p w x) : Vp p w ((m : ℚ) * x) :=
  Vp.mul_mem (int_mem_locRing m) hx

/-- Division by a unit. -/
theorem Vp.div_unit (hx : Vp p w x) {n : ℕ} (hn : ¬ p ∣ n) : Vp p w (x / n) := by
  have : x / n = (n : ℚ)⁻¹ * x := by rw [div_eq_inv_mul]
  rw [this]; exact Vp.mul_mem (inv_natCast_mem_locRing hn) hx

/-- Division by `p l`, `0 < l < p`. -/
theorem Vp.div_p_mul (hx : Vp p w x) {l : ℕ} (hl0 : 0 < l) (hlp : l < p) :
    Vp p (w + 1) (x / ((p * l : ℕ) : ℚ)) := by
  have hpl : ¬ p ∣ l := fun h => absurd (Nat.le_of_dvd hl0 h) (by omega)
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : (p : ℚ) ^ (w + 1) * (x / ((p * l : ℕ) : ℚ)) = ((p : ℚ) ^ w * x) * ((l : ℚ)⁻¹) := by
    push_cast
    have hl : (l : ℚ) ≠ 0 := by exact_mod_cast hl0.ne'
    field_simp
    ring
  unfold Vp
  rw [this]
  exact (LocRing p).mul_mem hx (inv_natCast_mem_locRing hpl)

end Vp

/-! ### Pole bounds of the single terms -/

section Poles

variable {v u : ℤ} {p : ℕ} [hp : Fact p.Prime]

theorem inv_mem_of_lt {j : ℕ} (hj0 : 0 < j) (hjp : j < p) : ((j : ℕ) : ℚ)⁻¹ ∈ LocRing p :=
  inv_natCast_mem_locRing (fun h => absurd (Nat.le_of_dvd hj0 h) (by omega))

theorem T1_unit {κ : ℕ} (h : ¬ p ∣ κ) : T1 v u κ ∈ LocRing p := by
  have hi := inv_natCast_mem_locRing (ℓ := p) h
  have : T1 v u κ = (u : ℚ) * (κ : ℚ)⁻¹ - (v : ℚ) * ((κ : ℚ)⁻¹) ^ 2 := by
    unfold T1; rw [div_eq_mul_inv, div_eq_mul_inv, inv_pow]
  rw [this]
  exact (LocRing p).sub_mem ((LocRing p).mul_mem (int_mem_locRing u) hi)
    ((LocRing p).mul_mem (int_mem_locRing v) ((LocRing p).pow_mem hi 2))

theorem T2_unit {κ : ℕ} (hκ : 1 ≤ κ) (h : ¬ p ∣ 2 * κ - 1) : T2 u κ ∈ LocRing p := by
  have hi := inv_natCast_mem_locRing (ℓ := p) h
  have hc : ((2 * κ - 1 : ℕ) : ℚ) = 2 * (κ : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have : T2 u κ = (-2 * (u : ℚ)) * ((2 * κ - 1 : ℕ) : ℚ)⁻¹ := by
    unfold T2; rw [hc, div_eq_mul_inv]
  rw [this]
  exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (-2 * u)) hi

theorem U1_unit {κ : ℕ} (h : ¬ p ∣ κ) : U1 v u κ ∈ LocRing p := by
  have hi := inv_natCast_mem_locRing (ℓ := p) h
  have : U1 v u κ = (u : ℚ) * ((κ : ℚ)⁻¹) ^ 2 - 2 * (v : ℚ) * ((κ : ℚ)⁻¹) ^ 3 := by
    unfold U1; rw [div_eq_mul_inv, div_eq_mul_inv, inv_pow, inv_pow]
  rw [this]
  exact (LocRing p).sub_mem ((LocRing p).mul_mem (int_mem_locRing u) ((LocRing p).pow_mem hi 2))
    ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (2 * v)) ((LocRing p).pow_mem hi 3))

theorem U2_unit {κ : ℕ} (hκ : 1 ≤ κ) (h : ¬ p ∣ 2 * κ - 1) : U2 u κ ∈ LocRing p := by
  have hi := inv_natCast_mem_locRing (ℓ := p) h
  have hc : ((2 * κ - 1 : ℕ) : ℚ) = 2 * (κ : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have : U2 u κ = (-4 * (u : ℚ)) * (((2 * κ - 1 : ℕ) : ℚ)⁻¹) ^ 2 := by
    unfold U2; rw [hc, div_eq_mul_inv, inv_pow]
  rw [this]
  exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (-4 * u))
    ((LocRing p).pow_mem hi 2)

/-- At `κ = p j` (`0 < j < p`): the double pole of `Δ` has valuation `≥ -2`. -/
theorem T1_pole {j : ℕ} (hj0 : 0 < j) (hjp : j < p) : Vp p 2 (T1 v u (p * j)) := by
  have hi := inv_mem_of_lt (p := p) hj0 hjp
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hj : (j : ℚ) ≠ 0 := by exact_mod_cast hj0.ne'
  have : (p : ℚ) ^ 2 * T1 v u (p * j) = ((u : ℚ) * p) * (j : ℚ)⁻¹ - (v : ℚ) * ((j : ℚ)⁻¹) ^ 2 := by
    unfold T1; push_cast; field_simp
  unfold Vp; rw [this]
  exact (LocRing p).sub_mem
    ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (u * p)) hi)
    ((LocRing p).mul_mem (int_mem_locRing v) ((LocRing p).pow_mem hi 2))

/-- At `κ = p j`: the triple pole of `E` has valuation `≥ -3`. -/
theorem U1_pole {j : ℕ} (hj0 : 0 < j) (hjp : j < p) : Vp p 3 (U1 v u (p * j)) := by
  have hi := inv_mem_of_lt (p := p) hj0 hjp
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hj : (j : ℚ) ≠ 0 := by exact_mod_cast hj0.ne'
  have : (p : ℚ) ^ 3 * U1 v u (p * j) =
      ((u : ℚ) * p) * ((j : ℚ)⁻¹) ^ 2 - (2 * (v : ℚ)) * ((j : ℚ)⁻¹) ^ 3 := by
    unfold U1; push_cast; field_simp
  unfold Vp; rw [this]
  exact (LocRing p).sub_mem
    ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (u * p)) ((LocRing p).pow_mem hi 2))
    ((LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (2 * v)) ((LocRing p).pow_mem hi 3))

/-- At `2κ - 1 = p i` (`0 < i < p`): the simple pole of `Δ` has valuation `≥ -1`. -/
theorem T2_pole {κ i : ℕ} (hκ : 1 ≤ κ) (hi : 2 * κ - 1 = p * i) (hi0 : 0 < i) (hip : i < p) :
    Vp p 1 (T2 u κ) := by
  have hii := inv_mem_of_lt (p := p) hi0 hip
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hi' : (i : ℚ) ≠ 0 := by exact_mod_cast hi0.ne'
  have hc : 2 * (κ : ℚ) - 1 = (p : ℚ) * i := by
    have : ((2 * κ - 1 : ℕ) : ℚ) = ((p * i : ℕ) : ℚ) := by rw [hi]
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
  have : (p : ℚ) ^ 1 * T2 u κ = (-2 * (u : ℚ)) * (i : ℚ)⁻¹ := by
    unfold T2; rw [hc]; field_simp
  unfold Vp; rw [this]
  exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (-2 * u)) hii

/-- At `2κ - 1 = p i`: the double pole of `E` has valuation `≥ -2`. -/
theorem U2_pole {κ i : ℕ} (hκ : 1 ≤ κ) (hi : 2 * κ - 1 = p * i) (hi0 : 0 < i) (hip : i < p) :
    Vp p 2 (U2 u κ) := by
  have hii := inv_mem_of_lt (p := p) hi0 hip
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hi' : (i : ℚ) ≠ 0 := by exact_mod_cast hi0.ne'
  have hc : 2 * (κ : ℚ) - 1 = (p : ℚ) * i := by
    have : ((2 * κ - 1 : ℕ) : ℚ) = ((p * i : ℕ) : ℚ) := by rw [hi]
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
  have : (p : ℚ) ^ 2 * U2 u κ = (-4 * (u : ℚ)) * ((i : ℚ)⁻¹) ^ 2 := by
    unfold U2; rw [hc]; field_simp
  unfold Vp; rw [this]
  exact (LocRing p).mul_mem (by exact_mod_cast int_mem_locRing (ℓ := p) (-4 * u))
    ((LocRing p).pow_mem hii 2)

/-- A multiple of `p` below `p²` is `p j` with `0 < j < p`, if it is positive. -/
theorem dvd_lt_sq {n : ℕ} (hn0 : 0 < n) (hn : n < p * p) (h : p ∣ n) : ∃ j, n = p * j ∧ 0 < j ∧ j < p := by
  obtain ⟨j, rfl⟩ := h
  refine ⟨j, rfl, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos j with h0 | h0
    · simp [h0] at hn0
    · exact h0
  · by_contra hge
    have hge := not_lt.1 hge
    have := Nat.mul_le_mul_left p hge
    omega

variable (v u)

theorem polF_pole {κ : ℕ} (hκ : 1 ≤ κ) (hκ2 : 2 * κ - 1 < p * p) : Vp p 2 (polF v u p κ) := by
  unfold polF
  refine Vp.add ?_ ?_
  · split_ifs with h
    · obtain ⟨j, hj, hj0, hjp⟩ := dvd_lt_sq (p := p) hκ (by omega) h
      rw [hj]; exact T1_pole hj0 hjp
    · exact Vp.zero
  · split_ifs with h
    · obtain ⟨i, hi, hi0, hip⟩ := dvd_lt_sq (p := p) (by omega) hκ2 h
      exact (T2_pole hκ hi hi0 hip).mono (by omega)
    · exact Vp.zero

/-- Outside the multiples of `p`, only the simple poles remain: valuation `≥ -1`. -/
theorem polF_pole_nomult {κ : ℕ} (hκ : 1 ≤ κ) (hκ2 : 2 * κ - 1 < p * p) (hnd : ¬ p ∣ κ) :
    Vp p 1 (polF v u p κ) := by
  unfold polF
  rw [if_neg hnd, zero_add]
  split_ifs with h
  · obtain ⟨i, hi, hi0, hip⟩ := dvd_lt_sq (p := p) (by omega) hκ2 h
    exact T2_pole hκ hi hi0 hip
  · exact Vp.zero

theorem polE_pole {κ : ℕ} (hκ : 1 ≤ κ) (hκ2 : 2 * κ - 1 < p * p) : Vp p 3 (polE v u p κ) := by
  unfold polE
  refine Vp.add ?_ ?_
  · split_ifs with h
    · obtain ⟨j, hj, hj0, hjp⟩ := dvd_lt_sq (p := p) hκ (by omega) h
      rw [hj]; exact U1_pole hj0 hjp
    · exact Vp.zero
  · split_ifs with h
    · obtain ⟨i, hi, hi0, hip⟩ := dvd_lt_sq (p := p) (by omega) hκ2 h
      exact (U2_pole hκ hi hi0 hip).mono (by omega)
    · exact Vp.zero

theorem polE_pole_nomult {κ : ℕ} (hκ : 1 ≤ κ) (hκ2 : 2 * κ - 1 < p * p) (hnd : ¬ p ∣ κ) :
    Vp p 2 (polE v u p κ) := by
  unfold polE
  rw [if_neg hnd, zero_add]
  split_ifs with h
  · obtain ⟨i, hi, hi0, hip⟩ := dvd_lt_sq (p := p) (by omega) hκ2 h
    exact U2_pole hκ hi hi0 hip
  · exact Vp.zero

theorem regF_mem {κ : ℕ} (hκ : 1 ≤ κ) : regF v u p κ ∈ LocRing p := by
  unfold regF
  refine (LocRing p).add_mem ?_ ?_
  · split_ifs with h
    · exact (LocRing p).zero_mem
    · exact T1_unit h
  · split_ifs with h
    · exact (LocRing p).zero_mem
    · exact T2_unit hκ h

theorem regE_mem {κ : ℕ} (hκ : 1 ≤ κ) : regE v u p κ ∈ LocRing p := by
  unfold regE
  refine (LocRing p).add_mem ?_ ?_
  · split_ifs with h
    · exact (LocRing p).zero_mem
    · exact U1_unit h
  · split_ifs with h
    · exact (LocRing p).zero_mem
    · exact U2_unit hκ h

end Poles

/-! ### Cells and their weights -/

section Cells

variable (p : ℕ)

/-- The half of `t` in its period: `1` if `2 (t mod p) ≥ p + 1`, else `0`. -/
def half (t : ℕ) : ℕ := if p + 1 ≤ 2 * (t % p) then 1 else 0

/-- The cell `(period, half)` of a node. -/
def cell (t : ℕ) : ℕ × ℕ := (t / p, half p t)

/-- The weight on cells: `0` in one cell, `1` in one period (other half), `2` in different periods. -/
def w3 (c c' : ℕ × ℕ) : ℕ := if c = c' then 0 else if c.1 = c'.1 then 1 else 2

/-- The diagonal weight: `3` in period `≥ 1`, `2` in cell `(0, 1)`, `0` in cell `(0, 0)`. -/
def Wd (t : ℕ) : ℕ := if 1 ≤ t / p then 3 else if half p t = 1 then 2 else 0

/-- The joint weight of a pair of nodes: `3` for congruent distinct nodes, else the cell weight. -/
def Wt (s t : ℕ) : ℕ := if s = t then Wd p s else if s % p = t % p then 3 else w3 (cell p s) (cell p t)

theorem w3_symm (c c' : ℕ × ℕ) : w3 c c' = w3 c' c := by
  unfold w3
  by_cases h : c = c'
  · subst h; simp
  · have h' : c' ≠ c := Ne.symm h
    by_cases h2 : c.1 = c'.1
    · rw [if_neg h, if_neg h', if_pos h2, if_pos h2.symm]
    · rw [if_neg h, if_neg h', if_neg h2, if_neg (Ne.symm h2)]

theorem Wt_symm (s t : ℕ) : Wt p s t = Wt p t s := by
  unfold Wt
  by_cases h : s = t
  · subst h; simp
  · have h' : t ≠ s := Ne.symm h
    simp only [h, h', if_false]
    by_cases h2 : s % p = t % p
    · simp [h2]
    · simp only [h2, Ne.symm h2, if_false]
      exact w3_symm _ _

variable {p}

theorem period_eq_of_between {s κ t : ℕ} (h1 : s ≤ κ) (h2 : κ ≤ t) (hper : s / p = t / p) :
    κ / p = s / p :=
  le_antisymm (hper ▸ Nat.div_le_div_right h2) (Nat.div_le_div_right h1)

/-- Inside a period no multiple of `p` is crossed. -/
theorem no_mult_same_period {s κ t : ℕ} (hs : s < κ) (hκt : κ ≤ t) (hper : s / p = t / p) :
    ¬ p ∣ κ := by
  have hq := period_eq_of_between hs.le hκt hper
  have h1 := Nat.div_add_mod s p
  have h2 := Nat.div_add_mod κ p
  rw [hq] at h2
  intro hd
  have := Nat.mod_eq_zero_of_dvd hd
  omega

theorem two_mul_sub_one_dvd {q ρ : ℕ} (hρ1 : 1 ≤ ρ) (hρp : ρ < p)
    (h : p ∣ 2 * (p * q + ρ) - 1) : 2 * ρ = p + 1 := by
  have e : 2 * (p * q + ρ) - 1 = p * (2 * q) + (2 * ρ - 1) := by
    have : p * (2 * q) = 2 * (p * q) := by ring
    omega
  rw [e] at h
  obtain ⟨c, hc⟩ := (Nat.dvd_add_right (dvd_mul_right p (2 * q))).1 h
  rcases Nat.lt_or_ge c 2 with hlt | hge
  · interval_cases c
    · simp at hc; omega
    · simp at hc; omega
  · have := Nat.mul_le_mul_left p hge
    omega

/-- Inside a cell no singular `κ` of either kind occurs. -/
theorem no_pole_same_cell {s κ t : ℕ} (hp0 : 0 < p) (hs : s < κ) (hκt : κ ≤ t) (hc : cell p s = cell p t) :
    ¬ p ∣ κ ∧ ¬ p ∣ 2 * κ - 1 := by
  have hper : s / p = t / p := (Prod.mk.inj hc).1
  have hhalf : half p s = half p t := (Prod.mk.inj hc).2
  refine ⟨no_mult_same_period hs hκt hper, ?_⟩
  have hq := period_eq_of_between hs.le hκt hper
  have hqt : t / p = s / p := hper.symm
  have h1 := Nat.div_add_mod s p
  have h2 := Nat.div_add_mod κ p
  have h3 := Nat.div_add_mod t p
  rw [hq] at h2
  rw [hqt] at h3
  have hρs := Nat.mod_lt s hp0
  have hρκ := Nat.mod_lt κ hp0
  have hρt := Nat.mod_lt t hp0
  have hρ1 : 1 ≤ κ % p := by omega
  intro hd
  have hκ : κ = p * (s / p) + κ % p := h2.symm
  have hd' : p ∣ 2 * (p * (s / p) + κ % p) - 1 := by rw [← hκ]; exact hd
  have h2ρ := two_mul_sub_one_dvd hρ1 hρκ hd'
  unfold half at hhalf
  by_cases hhs : p + 1 ≤ 2 * (s % p)
  · rw [if_pos hhs] at hhalf
    omega
  · rw [if_neg hhs] at hhalf
    by_cases hht : p + 1 ≤ 2 * (t % p)
    · rw [if_pos hht] at hhalf; omega
    · omega

end Cells

/-! ### Telescoping -/

section Telescope

variable {p : ℕ} [hp : Fact p.Prime]

theorem Vp_telescope (F : ℕ → ℚ) (w a : ℕ) :
    ∀ b, a ≤ b → (∀ i, a ≤ i → i < b → Vp p w (F (i + 1) - F i)) → Vp p w (F b - F a) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; simpa using (Vp.zero (p := p) (w := w))
  | succ b hab ih =>
    intro h
    have h1 := ih (fun i hi hib => h i hi (by omega))
    have h2 := h b hab (by omega)
    have := Vp.add h1 h2
    convert this using 1
    ring

theorem eq_telescope (F : ℕ → ℚ) (a : ℕ) :
    ∀ b, a ≤ b → (∀ i, a ≤ i → i < b → F (i + 1) = F i) → F b = F a := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => intro _; rfl
  | succ b hab ih =>
    intro h
    rw [h b hab (by omega), ih (fun i hi hib => h i hi (by omega))]

variable (v u : ℤ)

theorem PF_step (t : ℕ) : PF v u p (t + 1) - PF v u p t = polF v u p (t + 1) := by
  unfold PF; rw [Finset.sum_range_succ]; ring

theorem PE_step (t : ℕ) : PE v u p (t + 1) - PE v u p t = polE v u p (t + 1) := by
  unfold PE; rw [Finset.sum_range_succ]; ring

theorem RF_mem (t : ℕ) : RF v u p t ∈ LocRing p := by
  unfold RF
  exact (LocRing p).sum_mem fun k _ => regF_mem v u (by omega)

theorem RE_mem (t : ℕ) : RE v u p t ∈ LocRing p := by
  unfold RE
  exact (LocRing p).sum_mem fun k _ => regE_mem v u (by omega)

variable {N : ℕ}

theorem PF_diff_period (hN : 2 * N < p * p) {s t : ℕ} (hst : s ≤ t) (ht : t < N) :
    Vp p 2 (PF v u p t - PF v u p s) :=
  Vp_telescope _ 2 s t hst fun i _ hi => by
    rw [PF_step]; exact polF_pole v u (by omega) (by omega)

theorem PF_diff_same_period (hN : 2 * N < p * p) {s t : ℕ} (hst : s ≤ t) (ht : t < N)
    (hper : s / p = t / p) : Vp p 1 (PF v u p t - PF v u p s) :=
  Vp_telescope _ 1 s t hst fun i hsi hi => by
    rw [PF_step]
    exact polF_pole_nomult v u (by omega) (by omega) (no_mult_same_period (by omega) (by omega) hper)

theorem PF_eq_same_cell {s t : ℕ} (hst : s ≤ t) (hc : cell p s = cell p t) :
    PF v u p t = PF v u p s :=
  eq_telescope _ s t hst fun i hsi hi => by
    have h := PF_step v u (p := p) i
    have hnp := no_pole_same_cell (p := p) (s := s) (κ := i + 1) (t := t) hp.out.pos (by omega) (by omega) hc
    have : polF v u p (i + 1) = 0 := by unfold polF; simp [hnp.1, hnp.2]
    linarith

theorem PE_diff_period (hN : 2 * N < p * p) {s t : ℕ} (hst : s ≤ t) (ht : t < N) :
    Vp p 3 (PE v u p t - PE v u p s) :=
  Vp_telescope _ 3 s t hst fun i _ hi => by
    rw [PE_step]; exact polE_pole v u (by omega) (by omega)

theorem PE_diff_same_period (hN : 2 * N < p * p) {s t : ℕ} (hst : s ≤ t) (ht : t < N)
    (hper : s / p = t / p) : Vp p 2 (PE v u p t - PE v u p s) :=
  Vp_telescope _ 2 s t hst fun i hsi hi => by
    rw [PE_step]
    exact polE_pole_nomult v u (by omega) (by omega) (no_mult_same_period (by omega) (by omega) hper)

theorem PE_eq_same_cell {s t : ℕ} (hst : s ≤ t) (hc : cell p s = cell p t) :
    PE v u p t = PE v u p s :=
  eq_telescope _ s t hst fun i hsi hi => by
    have h := PE_step v u (p := p) i
    have hnp := no_pole_same_cell (p := p) (s := s) (κ := i + 1) (t := t) hp.out.pos (by omega) (by omega) hc
    have : polE v u p (i + 1) = 0 := by unfold polE; simp [hnp.1, hnp.2]
    linarith

end Telescope

/-! ### The weight table -/

section Table

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) {N : ℕ}

theorem lw_offdiag {s t : ℕ} (hst : s < t) :
    lw (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e s t =
      ((Datum.plane2 v u hv hu).f t - (Datum.plane2 v u hv hu).f s) / (((t - s : ℕ) : ℚ)) := by
  unfold lw
  rw [if_neg (Nat.ne_of_lt hst), Nat.cast_sub hst.le]

/-- The valuation of the difference of two values of `f` is bounded by the cell weight. -/
theorem Vp_fdiff (hN : 2 * N < p * p) {s t : ℕ} (hst : s < t) (ht : t < N) :
    Vp p (w3 (cell p s) (cell p t)) ((Datum.plane2 v u hv hu).f t - (Datum.plane2 v u hv hu).f s) := by
  have hdec : (Datum.plane2 v u hv hu).f t - (Datum.plane2 v u hv hu).f s =
      (PF v u p t - PF v u p s) + (RF v u p t - RF v u p s) := by
    rw [f_eq v u (p := p) hv hu, f_eq v u (p := p) hv hu]; ring
  have hR : Vp p 0 (RF v u p t - RF v u p s) :=
    Vp.zero_iff.2 ((LocRing p).sub_mem (RF_mem v u t) (RF_mem v u s))
  rw [hdec]
  by_cases hc : cell p s = cell p t
  · have h0 : PF v u p t - PF v u p s = 0 := by rw [PF_eq_same_cell v u hst.le hc]; ring
    rw [h0, zero_add]
    unfold w3; rw [if_pos hc]; exact hR
  · by_cases hper : s / p = t / p
    · have h1 := PF_diff_same_period v u hN hst.le ht hper
      have : w3 (cell p s) (cell p t) = 1 := by
        unfold w3; rw [if_neg hc, if_pos (show (cell p s).1 = (cell p t).1 from hper)]
      rw [this]; exact Vp.add h1 (hR.mono (by omega))
    · have h1 := PF_diff_period v u hN hst.le ht
      have : w3 (cell p s) (cell p t) = 2 := by
        unfold w3; rw [if_neg hc]
        have : ¬ (cell p s).1 = (cell p t).1 := hper
        rw [if_neg this]
      rw [this]; exact Vp.add h1 (hR.mono (by omega))

/-- **The weight table** (N1): for nodes `s, t < N` with `2N < p²`, `p^{W(s,t)} · lw f e s t` is
`p`-integral, whatever the integers `(v, u)`. -/
theorem weight_table (hN : 2 * N < p * p) (s t : ℕ) (hs : s < N) (ht : t < N) :
    Vp p (Wt p s t) (lw (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e s t) := by
  have lt_case : ∀ s t : ℕ, s < t → t < N →
      Vp p (Wt p s t) (lw (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e s t) := by
    intro s t hst ht
    rw [lw_offdiag v u hv hu hst]
    have hf := Vp_fdiff v u hv hu hN hst ht
    have hne : s ≠ t := Nat.ne_of_lt hst
    by_cases hcong : s % p = t % p
    · have hdvd : p ∣ t - s := (Nat.modEq_iff_dvd' hst.le).1 hcong
      obtain ⟨l, hl⟩ := hdvd
      have hl0 : 0 < l := by
        rcases Nat.eq_zero_or_pos l with h0 | h0
        · simp [h0] at hl; omega
        · exact h0
      have hlp : l < p := by
        by_contra hge
        have hge := not_lt.1 hge
        have := Nat.mul_le_mul_left p hge
        omega
      have hper : ¬ s / p = t / p := by
        intro hper
        have h1 := Nat.div_add_mod s p
        have h2 := Nat.div_add_mod t p
        rw [← hper] at h2
        omega
      have hw : w3 (cell p s) (cell p t) = 2 := by
        unfold w3
        have hc : ¬ cell p s = cell p t := fun h => hper (Prod.mk.inj h).1
        rw [if_neg hc, if_neg (show ¬ (cell p s).1 = (cell p t).1 from hper)]
      rw [hw] at hf
      have e : (((t - s : ℕ)) : ℚ) = ((p * l : ℕ) : ℚ) := by rw [hl]
      rw [e]
      have : Wt p s t = 3 := by unfold Wt; rw [if_neg hne, if_pos hcong]
      rw [this]
      exact Vp.div_p_mul hf hl0 hlp
    · have hnd : ¬ p ∣ t - s := fun h => hcong ((Nat.modEq_iff_dvd' hst.le).2 h)
      have : Wt p s t = w3 (cell p s) (cell p t) := by unfold Wt; rw [if_neg hne, if_neg hcong]
      rw [this]
      exact Vp.div_unit hf hnd
  by_cases hst : s = t
  · subst hst
    unfold lw; rw [if_pos rfl]
    unfold Wt; rw [if_pos rfl]
    rw [e_eq v u (p := p) hv hu]
    have hRE : RE v u p s ∈ LocRing p := RE_mem v u s
    have hPE0 : PE v u p 0 = 0 := by simp [PE]
    unfold Wd
    by_cases h1 : 1 ≤ s / p
    · rw [if_pos h1]
      have := PE_diff_period v u hN (Nat.zero_le s) hs
      rw [hPE0, sub_zero] at this
      exact (Vp.add this (Vp.of_mem hRE)).neg
    · rw [if_neg h1]
      have hs0 : s / p = 0 := by by_contra h; exact h1 (Nat.pos_of_ne_zero h)
      by_cases h2 : half p s = 1
      · rw [if_pos h2]
        have := PE_diff_same_period v u hN (Nat.zero_le s) hs (by rw [hs0]; simp)
        rw [hPE0, sub_zero] at this
        exact (Vp.add this (Vp.of_mem hRE)).neg
      · rw [if_neg h2]
        have hc : cell p 0 = cell p s := by
          have : half p s = 0 := by
            unfold half at h2 ⊢
            split_ifs at h2 ⊢ <;> simp_all
          unfold cell
          rw [hs0, this]
          simp [half]
        have := PE_eq_same_cell v u (Nat.zero_le s) hc
        rw [hPE0] at this
        rw [this, zero_add]
        exact (Vp.of_mem hRE).neg
  · rcases Nat.lt_or_gt_of_ne hst with hlt | hgt
    · exact lt_case s t hlt ht
    · have h := lt_case t s hgt hs
      have hsym : lw (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e s t =
          lw (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e t s := by
        unfold lw
        rw [if_neg hst, if_neg (Ne.symm hst)]
        have h1 : (s : ℚ) - t ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hst)
        have h2 : (t : ℚ) - s ≠ 0 := sub_ne_zero.2 (by exact_mod_cast (Ne.symm hst))
        field_simp
        ring
      rw [hsym, Wt_symm]
      exact h

end Table

/-! ### Lemma 2.2: the assignment bound -/

section Assignment

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ) (hv : v ≠ 0) (hu : u ≠ 0) {N : ℕ}
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Every coefficient of every entry has the weight of its pair of nodes. -/
theorem entry_gle (hN : 2 * N < p * p) (cn : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ a, cn a < N)
    (hx : ∀ i, xs i < N) (hy : ∀ i, ys i < N) (a b : ι ⊕ κ) :
    GLE p (Wt p (Sum.elim cn xs a) (Sum.elim cn ys b))
      (seqFullN (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e cn xs ys (X : ℚ[X]) a b) := by
  have bnd : ∀ a, Sum.elim cn xs a < N := fun a => by
    rcases a with a | i
    · exact hc a
    · exact hx i
  have bnd' : ∀ b, Sum.elim cn ys b < N := fun b => by
    rcases b with b | j
    · exact hc b
    · exact hy j
  have key := fun a b => GLE.C_iff.2 (weight_table v u hv hu hN _ _ (bnd a) (bnd' b))
  rcases a with a | i <;> rcases b with b | j
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.of_apply, smul_eq_mul, Polynomial.algebraMap_eq]
    by_cases h : a = b
    · simp only [h, if_true, mul_one]
      exact (key (Sum.inl b) (Sum.inl b)).add (GLE.X.mono (Nat.zero_le _))
    · simp only [h, if_false, mul_zero, add_zero]
      exact key (Sum.inl a) (Sum.inl b)
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₁₂, Matrix.of_apply, Polynomial.algebraMap_eq]
    exact key (Sum.inl a) (Sum.inr j)
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, Polynomial.algebraMap_eq]
    exact key (Sum.inr i) (Sum.inl b)
  · simp only [seqFullN, Rect.Blk, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Polynomial.algebraMap_eq]
    exact key (Sum.inr i) (Sum.inr j)

/-- **Lemma 2.2** (N1, assignment bound).  If `uR` on the rows and `uC` on the columns are natural
potentials with `W ≤ uR + uC` on every pair, then every coefficient of the determinant of the member is
`p^{∑uR + ∑uC}`-integral: `v_p(den P_I) ≤ ∑u + ∑u′` for every `I`. -/
theorem det_gle_of_dual (hN : 2 * N < p * p) (cn : ι → ℕ) (xs ys : κ → ℕ) (hc : ∀ a, cn a < N)
    (hx : ∀ i, xs i < N) (hy : ∀ i, ys i < N) (uR uC : ι ⊕ κ → ℕ)
    (hW : ∀ a b, Wt p (Sum.elim cn xs a) (Sum.elim cn ys b) ≤ uR a + uC b) :
    GLE p (∑ a, uR a + ∑ b, uC b)
      (seqFullN (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e cn xs ys (X : ℚ[X])).det := by
  have h := det_gle (p := p) (seqFullN (Datum.plane2 v u hv hu).f (Datum.plane2 v u hv hu).e cn xs ys
    (X : ℚ[X])) (fun a b => Wt p (Sum.elim cn xs a) (Sum.elim cn ys b))
    (entry_gle v u hv hu hN cn xs ys hc hx hy)
  refine h.mono ?_
  refine tropVal_le_of_dual (fun a b => Wt p (Sum.elim cn xs a) (Sum.elim cn ys b))
    (fun a => (uR a : ℚ)) (fun b => (uC b : ℚ)) ?_ ?_
  · intro a b; exact_mod_cast hW a b
  · push_cast; exact le_rfl

end Assignment

/-! ### Lemma 2.1: the regular part is a function of the residue, modulo `p` -/

section Congruence

variable {p : ℕ} [hp : Fact p.Prime] (v u : ℤ)

/-- `1/n` as an element of `ℤ_(p)`, and `0` if `p ∣ n`. -/
noncomputable def invK (p : ℕ) [Fact p.Prime] (n : ℕ) : LocRing p :=
  if h : ¬ p ∣ n then ⟨(n : ℚ)⁻¹, inv_natCast_mem_locRing h⟩ else 0

theorem coe_invK (n : ℕ) : ((invK p n : LocRing p) : ℚ) = if p ∣ n then 0 else (n : ℚ)⁻¹ := by
  unfold invK
  by_cases h : p ∣ n <;> simp [h]

theorem redQ_invK (n : ℕ) : redQ p (invK p n) = ((n : ℕ) : ZMod p)⁻¹ := by
  by_cases h : p ∣ n
  · have h0 : ((n : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff n p).2 h
    unfold invK; simp [h, h0]
  · have hmem : ((n : ℕ) : ℚ) ∈ LocRing p := by exact_mod_cast int_mem_locRing (ℓ := p) (n : ℤ)
    have e : invK p n * (⟨(n : ℚ), hmem⟩ : LocRing p) = 1 := by
      apply Subtype.ext
      unfold invK; rw [dif_pos h]
      have hn : (n : ℚ) ≠ 0 := by
        have : n ≠ 0 := fun h0 => h (h0 ▸ dvd_zero p)
        exact_mod_cast this
      simp [inv_mul_cancel₀ hn]
    have h1 := congrArg (redQ p) e
    rw [map_mul, map_one] at h1
    have h2 : redQ p (⟨(n : ℚ), hmem⟩ : LocRing p) = ((n : ℕ) : ZMod p) := by
      rw [redQ_apply]; simp
    rw [h2] at h1
    exact eq_inv_of_mul_eq_one_left h1

/-- The regular part of `Δ_κ` is the image of an element of `ℤ_(p)` built from `invK`. -/
theorem regF_eq_invK {κ : ℕ} (hκ : 1 ≤ κ) :
    regF v u p κ = (((u : LocRing p) * invK p κ - (v : LocRing p) * invK p κ ^ 2 +
      ((-2 * u : ℤ) : LocRing p) * invK p (2 * κ - 1) : LocRing p) : ℚ) := by
  have hc : ((2 * κ - 1 : ℕ) : ℚ) = 2 * (κ : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have e1 : (if p ∣ κ then (0 : ℚ) else T1 v u κ) =
      (u : ℚ) * (if p ∣ κ then 0 else (κ : ℚ)⁻¹) -
        (v : ℚ) * (if p ∣ κ then 0 else (κ : ℚ)⁻¹) ^ 2 := by
    by_cases h : p ∣ κ <;> simp [h, T1, div_eq_mul_inv, inv_pow]
  have e2 : (if p ∣ 2 * κ - 1 then (0 : ℚ) else T2 u κ) =
      (-2 * (u : ℚ)) * (if p ∣ 2 * κ - 1 then 0 else ((2 * κ - 1 : ℕ) : ℚ)⁻¹) := by
    by_cases h : p ∣ 2 * κ - 1 <;> simp [h, T2, hc, div_eq_mul_inv]
  unfold regF
  rw [e1, e2]
  push_cast
  rw [coe_invK, coe_invK]
  by_cases h : p ∣ 2 * κ - 1 <;> simp [h] <;> (left; left; norm_cast)

/-- The reduction of the regular part of `Δ_κ` modulo `p`. -/
noncomputable def gF (y : ZMod p) : ZMod p :=
  (u : ZMod p) * y⁻¹ - (v : ZMod p) * (y⁻¹) ^ 2 + ((-2 * u : ℤ) : ZMod p) * (2 * y - 1)⁻¹

theorem redQ_regF {κ : ℕ} (hκ : 1 ≤ κ) :
    redQ p ⟨regF v u p κ, regF_mem v u hκ⟩ = gF v u (κ : ZMod p) := by
  have e : (⟨regF v u p κ, regF_mem v u hκ⟩ : LocRing p) =
      (u : LocRing p) * invK p κ - (v : LocRing p) * invK p κ ^ 2 +
        ((-2 * u : ℤ) : LocRing p) * invK p (2 * κ - 1) := by
    apply Subtype.ext
    exact regF_eq_invK v u hκ
  rw [e]
  simp only [map_add, map_sub, map_mul, map_pow, map_intCast, redQ_invK]
  unfold gF
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem sum_gF_zero (hp5 : 5 ≤ p) : ∑ y : ZMod p, gF v u y = 0 := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have h1 : ∑ y : ZMod p, y⁻¹ = 0 := by
    have := Equiv.sum_comp (Equiv.inv (ZMod p)) (fun z => z ^ 1)
    simp only [pow_one, Equiv.inv_apply] at this
    rw [this]
    simpa using FiniteField.sum_pow_lt_card_sub_one (ZMod p) (i := 1) (by omega)
  have h2 : ∑ y : ZMod p, (y⁻¹) ^ 2 = 0 := by
    have := Equiv.sum_comp (Equiv.inv (ZMod p)) (fun z => z ^ 2)
    simp only [Equiv.inv_apply] at this
    rw [this]
    exact FiniteField.sum_pow_lt_card_sub_one (ZMod p) (i := 2) (by omega)
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h3 : ∑ y : ZMod p, (2 * y - 1)⁻¹ = 0 := by
    let e : ZMod p ≃ ZMod p := (Equiv.mulLeft₀ (2 : ZMod p) h2ne).trans (Equiv.subRight 1)
    have := Equiv.sum_comp e (fun z => z⁻¹)
    have he : ∀ y, e y = 2 * y - 1 := fun y => rfl
    simp only [he] at this
    rw [this]; exact h1
  unfold gF
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, h1, h2, h3]
  simp

/-- A complete block of `p` consecutive `κ` sums to a multiple of `p`. -/
theorem block_dvd (hp5 : 5 ≤ p) (a : ℕ) :
    (∑ i ∈ range p, regF v u p (a + i + 1)) / p ∈ LocRing p := by
  let x : ℕ → LocRing p := fun i => ⟨regF v u p (a + i + 1), regF_mem v u (by omega)⟩
  have hsum : (∑ i ∈ range p, regF v u p (a + i + 1)) = (((∑ i ∈ range p, x i : LocRing p)) : ℚ) := by
    have := map_sum (LocRing p).subtype x (range p)
    simpa [x] using this.symm
  have hred : redQ p (∑ i ∈ range p, x i) = 0 := by
    rw [map_sum]
    have e : ∀ i ∈ range p, redQ p (x i) = gF v u (((a + 1 + i : ℕ)) : ZMod p) := by
      intro i _
      have := redQ_regF (p := p) v u (κ := a + i + 1) (by omega)
      simp only [x]
      rw [this]
      congr 1
      push_cast; ring
    rw [Finset.sum_congr rfl e]
    -- reindex the block by the residue
    let φ : ℕ → ZMod p := fun i => ((a + 1 + i : ℕ) : ZMod p)
    have hinj : Set.InjOn φ (range p : Finset ℕ) := by
      intro i hi j hj hij
      have hi' := Finset.mem_range.1 (Finset.mem_coe.1 hi)
      have hj' := Finset.mem_range.1 (Finset.mem_coe.1 hj)
      have : ((a + 1 + i : ℕ) : ZMod p) = ((a + 1 + j : ℕ) : ZMod p) := hij
      rw [ZMod.natCast_eq_natCast_iff'] at this
      have h1 : (a + 1 + i) % p = (a + 1 + j) % p := this
      have h2 : i % p = j % p := by
        have := Nat.ModEq.add_left_cancel' (a + 1) (show a + 1 + i ≡ a + 1 + j [MOD p] from h1)
        exact this
      rwa [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at h2
    have himg : (range p).image φ = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injOn hinj, Finset.card_range, ZMod.card]
    have : ∑ i ∈ range p, gF v u (φ i) = ∑ y : ZMod p, gF v u y := by
      rw [← Finset.sum_image (f := fun y => gF v u y) hinj, himg]
    exact this.trans (sum_gF_zero v u hp5)
  obtain ⟨y, hy⟩ := (redQ_eq_zero_iff p _).1 hred
  rw [hsum, hy]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  simp only [Subring.coe_mul, Subring.coe_natCast]
  rw [mul_div_cancel_left₀ _ hp0]
  exact y.2

/-- **Lemma 2.1.**  If `t′ ≡ t (mod p)` then `ρ_{t′} ≡ ρ_t (mod p)`: `(RF t′ - RF t)/p` is `p`-integral. -/
theorem regF_congr (hp5 : 5 ≤ p) (t l : ℕ) :
    (RF v u p (t + l * p) - RF v u p t) / p ∈ LocRing p := by
  induction l with
  | zero => simp [(LocRing p).zero_mem]
  | succ l ih =>
    have hsplit : RF v u p (t + (l + 1) * p) - RF v u p t =
        (∑ i ∈ range p, regF v u p (t + l * p + i + 1)) + (RF v u p (t + l * p) - RF v u p t) := by
      have e : t + (l + 1) * p = (t + l * p) + p := by ring
      rw [e]
      unfold RF
      rw [Finset.sum_range_add]
      simp only [add_assoc]
      ring
    rw [hsplit, add_div]
    exact (LocRing p).add_mem (block_dvd v u hp5 (t + l * p)) ih

end Congruence

end CatalanCore.Uniform.Content.Sweep

#print axioms CatalanCore.Uniform.Content.Sweep.weight_table
#print axioms CatalanCore.Uniform.Content.Sweep.det_gle_of_dual
#print axioms CatalanCore.Uniform.Content.Sweep.regF_congr
#print axioms CatalanCore.Uniform.Content.Sweep.no_pole_same_cell
