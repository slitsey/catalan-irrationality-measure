module

public import CatalanCore.Uniform.Bank.Plane1.PoleData
public import CatalanCore.Arith.Hybrid.Tropical
public import CatalanCore.Basic.ZModGood
public import CatalanCore.Arith.Hybrid.RankGLE
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section
set_option Elab.async false
set_option linter.unusedSectionVars false

/-! # Lemma A (period sums) for any finite simple-pole frame (wave R0; ledger R01-R03)

Lemma A of `DIP-RANK-CLOSED-FORM-2026-11-07.md` (Lemma 5.1' of the dip rows), in the `lin` language of `Plane1.PoleData`.
For an odd prime `p ≥ 3` and an arbitrary frame write `lin i k = den_i (k - 1) + num_i`, so that
`Δ_k = Σ_i w_i den_i / lin i k` and `D_k = Σ_i w_i den_i² / lin i k²`.  A term is **polar** when `p ∣ lin i k`.
Put

* `dvP k = Σ_{i polar} p w_i den_i / lin i k` (so `Δ_k = dvP k / p + (nonpolar part)`),
* `dsP k = Σ_{i polar} p² w_i den_i² / lin i k²`,
* `Vp t = Σ_{0 < k ≤ t} dvP k`  (the level `V(t)`: the polar parts of `f_t = Σ_{k ≤ t} Δ_k` are `Vp t / p`),
* `Up t = - Σ_{0 < k ≤ t} dsP k`  (the polar part of the diagonal entry `e_t = - Σ_{k ≤ t} D_k` is `Up t / p²`).

* `periodSum`: for `t' = t + s p`, arbitrary `s`: `Σ_{t < k ≤ t'} Δ_k = (Vp t' - Vp t) / p + Δ` with `Δ / p` `p`-integral.
* `diag_split`: `Σ_{k ≤ t} D_k = - Up t / p² + (a p-integer)`.
* `Vp_mem`, `Up_mem`: with atomwise prime-square-free linear denominators (or `Q k < p²`), `Vp t` and `Up t` are `p`-integral.
* `offSum_split`: for any `t < t'`, `Σ_{t < k ≤ t'} Δ_k = (Vp t' - Vp t) / p + (a p-integer)` (no period condition). -/

namespace CatalanCore.Uniform.Bank.Plane1.Dips
open Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.Periodic

section Def

variable (p : ℕ) (Fr : Frame)

/-- `p ·` (the polar part of `Δ_k`). -/
noncomputable def dvP (k : ℕ) : ℚ :=
  ∑ i : Fin Fr.d, if p ∣ lin Fr i k then
    (p : ℚ) * ((Fr.w i : ℚ) * (Fr.μ i).den) / (lin Fr i k : ℚ) else 0

/-- `p² ·` (the polar part of `D_k`). -/
noncomputable def dsP (k : ℕ) : ℚ :=
  ∑ i : Fin Fr.d, if p ∣ lin Fr i k then
    (p : ℚ) ^ 2 * ((Fr.w i : ℚ) * (Fr.μ i).den ^ 2) / (lin Fr i k : ℚ) ^ 2 else 0

/-- The nonpolar part of `Δ_k`. -/
noncomputable def nonpolD (k : ℕ) : ℚ :=
  ∑ i : Fin Fr.d, if p ∣ lin Fr i k then 0 else ((Fr.w i : ℚ) * (Fr.μ i).den) / (lin Fr i k : ℚ)

/-- The nonpolar part of `D_k`. -/
noncomputable def nonpolS (k : ℕ) : ℚ :=
  ∑ i : Fin Fr.d, if p ∣ lin Fr i k then 0 else ((Fr.w i : ℚ) * (Fr.μ i).den ^ 2) / (lin Fr i k : ℚ) ^ 2

/-- The level `V(t)`. -/
noncomputable def Vp (t : ℕ) : ℚ := ∑ k ∈ Ioc 0 t, dvP p Fr k

/-- The level `U(t)` of the diagonal (the `p⁻²` coefficient of `e_t`). -/
noncomputable def Up (t : ℕ) : ℚ := -∑ k ∈ Ioc 0 t, dsP p Fr k

end Def

section Split

variable {p : ℕ} [hp : Fact p.Prime] {Fr : Frame}

theorem Delta_split {k : ℕ} (hk : 1 ≤ k) : Fr.Delta k = dvP p Fr k / p + nonpolD p Fr k := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [Delta_lin k hk, dvP, nonpolD, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : p ∣ lin Fr i k
  · simp only [h, ite_true, add_zero]
    field_simp
  · simp only [h, ite_false, zero_div, zero_add]

theorem Dsq_split {k : ℕ} (hk : 1 ≤ k) : Fr.Dsq k = dsP p Fr k / (p : ℚ) ^ 2 + nonpolS p Fr k := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [Dsq_lin k hk, dsP, nonpolS, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : p ∣ lin Fr i k
  · simp only [h, ite_true, add_zero]
    field_simp
  · simp only [h, ite_false, zero_div, zero_add]

theorem unit_term_mem (c : ℤ) {L : ℕ} (h : ¬ p ∣ L) : ((c : ℚ)) / (L : ℚ) ∈ LocRing p := by
  rw [div_eq_mul_inv]
  exact (LocRing p).mul_mem (int_mem_locRing c) (inv_natCast_mem_locRing h)

theorem unit_term_mem' (c : ℤ) {L : ℕ} (h : ¬ p ∣ L) : ((c : ℚ)) / (L : ℚ) ^ 2 ∈ LocRing p := by
  have : ((c : ℚ)) / (L : ℚ) ^ 2 = (c : ℚ) * ((L : ℚ)⁻¹) * ((L : ℚ)⁻¹) := by
    field_simp
  rw [this]
  exact (LocRing p).mul_mem ((LocRing p).mul_mem (int_mem_locRing c) (inv_natCast_mem_locRing h))
    (inv_natCast_mem_locRing h)

theorem nonpolD_mem (k : ℕ) : nonpolD p Fr k ∈ LocRing p := by
  refine (LocRing p).sum_mem fun i _ => ?_
  by_cases h : p ∣ lin Fr i k
  · simp only [h, ite_true]; exact (LocRing p).zero_mem
  · simp only [h, ite_false]
    have := unit_term_mem (p := p) ((Fr.w i) * ((Fr.μ i).den : ℤ)) h
    simpa using this

theorem nonpolS_mem (k : ℕ) : nonpolS p Fr k ∈ LocRing p := by
  refine (LocRing p).sum_mem fun i _ => ?_
  by_cases h : p ∣ lin Fr i k
  · simp only [h, ite_true]; exact (LocRing p).zero_mem
  · simp only [h, ite_false]
    have := unit_term_mem' (p := p) ((Fr.w i) * ((Fr.μ i).den : ℤ) ^ 2) h
    simpa using this

/-- A polar term `p c / L` with `p ∣ L`, `p² ∤ L` is `p`-integral. -/
theorem polar_mem {c : ℚ} (hc : c ∈ LocRing p) {L : ℕ} (hL : p ∣ L) (hL2 : ¬ p * p ∣ L) :
    (p : ℚ) * c / (L : ℚ) ∈ LocRing p := by
  obtain ⟨m, rfl⟩ := hL
  have hm : ¬ p ∣ m := fun h => by
    obtain ⟨t, rfl⟩ := h
    exact hL2 ⟨t, by ring⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hm0 : (m : ℚ) ≠ 0 := by
    intro h0
    have : m = 0 := by exact_mod_cast h0
    exact hm (this ▸ dvd_zero p)
  have : (p : ℚ) * c / ((p * m : ℕ) : ℚ) = c * (m : ℚ)⁻¹ := by push_cast; field_simp
  rw [this]
  exact (LocRing p).mul_mem hc (inv_natCast_mem_locRing hm)

theorem polar_mem' {c : ℚ} (hc : c ∈ LocRing p) {L : ℕ} (hL : p ∣ L) (hL2 : ¬ p * p ∣ L) :
    (p : ℚ) ^ 2 * c / (L : ℚ) ^ 2 ∈ LocRing p := by
  obtain ⟨m, rfl⟩ := hL
  have hm : ¬ p ∣ m := fun h => by
    obtain ⟨t, rfl⟩ := h
    exact hL2 ⟨t, by ring⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hm0 : (m : ℚ) ≠ 0 := by
    intro h0
    have : m = 0 := by exact_mod_cast h0
    exact hm (this ▸ dvd_zero p)
  have : (p : ℚ) ^ 2 * c / ((p * m : ℕ) : ℚ) ^ 2 = c * ((m : ℚ)⁻¹ * (m : ℚ)⁻¹) := by
    push_cast; field_simp
  rw [this]
  exact (LocRing p).mul_mem hc ((LocRing p).mul_mem (inv_natCast_mem_locRing hm) (inv_natCast_mem_locRing hm))


/-- Geometric sufficient condition for an atomwise prime-square-free denominator. -/
theorem lin_not_sq {Q k : ℕ} (hden : ∀ i, (Fr.μ i).den ≤ Q)
    (hk : 1 ≤ k) (hkQ : Q * k < p * p) (i : Fin Fr.d) :
    ¬ p * p ∣ lin Fr i k := by
  intro h
  have h0 := lin_pos i hk
  have h1 := lin_le i (hden i) hk
  have := Nat.le_of_dvd h0 h
  omega

theorem dvP_mem {k : ℕ} (hk : 1 ≤ k)
    (hsq : ∀ i, ¬ p * p ∣ lin Fr i k) : dvP p Fr k ∈ LocRing p := by
  refine (LocRing p).sum_mem fun i _ => ?_
  by_cases h : p ∣ lin Fr i k
  · simp only [h, ite_true]
    have hc := int_mem_locRing (ℓ := p) ((Fr.w i) * ((Fr.μ i).den : ℤ))
    push_cast at hc
    exact polar_mem hc h (hsq i)
  · simp only [h, ite_false]; exact (LocRing p).zero_mem

theorem dsP_mem {k : ℕ} (hk : 1 ≤ k)
    (hsq : ∀ i, ¬ p * p ∣ lin Fr i k) : dsP p Fr k ∈ LocRing p := by
  refine (LocRing p).sum_mem fun i _ => ?_
  by_cases h : p ∣ lin Fr i k
  · simp only [h, ite_true]
    have hc := int_mem_locRing (ℓ := p) ((Fr.w i) * ((Fr.μ i).den : ℤ) ^ 2)
    push_cast at hc
    exact polar_mem' hc h (hsq i)
  · simp only [h, ite_false]; exact (LocRing p).zero_mem

theorem Vp_mem {t : ℕ}
    (hsq : ∀ k, 1 ≤ k → k ≤ t → ∀ i, ¬ p * p ∣ lin Fr i k) : Vp p Fr t ∈ LocRing p := by
  refine (LocRing p).sum_mem fun k hk => ?_
  obtain ⟨hk0, hkt⟩ := Finset.mem_Ioc.mp hk
  exact dvP_mem (by omega) (hsq k (by omega) hkt)

theorem Up_mem {t : ℕ}
    (hsq : ∀ k, 1 ≤ k → k ≤ t → ∀ i, ¬ p * p ∣ lin Fr i k) : Up p Fr t ∈ LocRing p := by
  refine (LocRing p).neg_mem ((LocRing p).sum_mem fun k hk => ?_)
  obtain ⟨hk0, hkt⟩ := Finset.mem_Ioc.mp hk
  exact dsP_mem (by omega) (hsq k (by omega) hkt)

theorem Vp_mem_Q {Q t : ℕ} (hden : ∀ i, (Fr.μ i).den ≤ Q)
    (ht : Q * t < p * p) : Vp p Fr t ∈ LocRing p :=
  Vp_mem fun k hk hkt i => lin_not_sq hden hk
    (lt_of_le_of_lt (Nat.mul_le_mul_left Q hkt) ht) i

theorem Up_mem_Q {Q t : ℕ} (hden : ∀ i, (Fr.μ i).den ≤ Q)
    (ht : Q * t < p * p) : Up p Fr t ∈ LocRing p :=
  Up_mem fun k hk hkt i => lin_not_sq hden hk
    (lt_of_le_of_lt (Nat.mul_le_mul_left Q hkt) ht) i

/-- The sum of increments between two nodes: polar part plus a `p`-integer. -/
theorem offSum_split {t t' : ℕ} (h : t ≤ t') :
    ∑ k ∈ Ioc t t', Fr.Delta k =
      (Vp p Fr t' - Vp p Fr t) / p + ∑ k ∈ Ioc t t', nonpolD p Fr k := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hV : Vp p Fr t' - Vp p Fr t = ∑ k ∈ Ioc t t', dvP p Fr k := by
    unfold Vp
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le t) h]
    ring
  rw [hV, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Ioc.1 hk
  exact Delta_split (by omega)

theorem offSum_nonpol_mem (t t' : ℕ) : ∑ k ∈ Ioc t t', nonpolD p Fr k ∈ LocRing p :=
  (LocRing p).sum_mem fun k _ => nonpolD_mem k

/-- The diagonal: `Σ_{k ≤ t} D_k = - Up t / p² + (a p-integer)`. -/
theorem diag_split (t : ℕ) :
    ∑ k ∈ Ioc 0 t, Fr.Dsq k = -Up p Fr t / (p : ℚ) ^ 2 + ∑ k ∈ Ioc 0 t, nonpolS p Fr k := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  unfold Up
  rw [neg_neg, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Ioc.1 hk
  exact Dsq_split (by omega)

theorem diag_nonpol_mem (t : ℕ) : ∑ k ∈ Ioc 0 t, nonpolS p Fr k ∈ LocRing p :=
  (LocRing p).sum_mem fun k _ => nonpolS_mem k

end Split

/-! ### The block sums: Lemma A -/

section Block

variable {p : ℕ} [hp : Fact p.Prime]

theorem sum_Ioc_eq_range (f : ℕ → ℚ) (a n : ℕ) :
    ∑ k ∈ Ioc a (a + n), f k = ∑ j ∈ range n, f (a + 1 + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 by ring, Finset.sum_Ioc_succ_top (by omega), ih,
      Finset.sum_range_succ]
    rw [show a + 1 + n = a + n + 1 by ring]

theorem sum_range_affine {M : Type*} [AddCommMonoid M] {d : ZMod p} (hd : d ≠ 0) (c : ZMod p) (a : ℕ)
    (F : ZMod p → M) : ∑ j ∈ range p, F (d * ((a + j : ℕ) : ZMod p) + c) = ∑ v : ZMod p, F v := by
  classical
  set g : ℕ → ZMod p := fun j => d * ((a + j : ℕ) : ZMod p) + c with hg
  have hinj : Set.InjOn g (range p : Finset ℕ) := by
    intro j hj j' hj' h
    simp only [hg] at h
    have h1 : ((a + j : ℕ) : ZMod p) = ((a + j' : ℕ) : ZMod p) :=
      mul_left_cancel₀ hd (add_right_cancel h)
    have h2 : (j : ZMod p) = (j' : ZMod p) := by
      push_cast at h1
      linear_combination h1
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    rwa [Nat.mod_eq_of_lt (Finset.mem_range.1 hj), Nat.mod_eq_of_lt (Finset.mem_range.1 hj')] at h2
  have himg : (range p).image g = univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_image_of_injOn hinj, card_range, ZMod.card]
  calc ∑ j ∈ range p, F (g j) = ∑ v ∈ (range p).image g, F v := (Finset.sum_image hinj).symm
    _ = ∑ v : ZMod p, F v := by rw [himg]

theorem sum_inv_zmod (h3 : 3 ≤ p) : ∑ v : ZMod p, v⁻¹ = 0 := by
  have h1 : ∑ v : ZMod p, v⁻¹ = ∑ v : ZMod p, v :=
    Fintype.sum_equiv (Function.Involutive.toPerm _ inv_involutive) _ _ (fun x => rfl)
  have h2 := FiniteField.sum_pow_lt_card_sub_one (ZMod p) 1 (by rw [ZMod.card]; omega)
  rw [h1]
  simpa using h2

variable {Fr : Frame}

/-- One block of `p` consecutive indices: the nonpolar terms of one atom sum to a multiple of `p`. -/
theorem block_good (i : Fin Fr.d) (h3 : 3 ≤ p) (a : ℕ) :
    CatalanCore.Good p (∑ k ∈ Ioc a (a + p),
      (if p ∣ lin Fr i k then (0 : ℚ) else ((Fr.w i : ℚ) * (Fr.μ i).den) / (lin Fr i k : ℚ))) 0 := by
  rw [sum_Ioc_eq_range (fun k => if p ∣ lin Fr i k then (0 : ℚ) else
    ((Fr.w i : ℚ) * (Fr.μ i).den) / (lin Fr i k : ℚ))]
  set c : ℤ := Fr.w i * ((Fr.μ i).den : ℤ) with hc
  set G : ZMod p → ZMod p := fun v => (c : ZMod p) * v⁻¹ with hG
  have hgood : ∀ j ∈ range p, CatalanCore.Good p
      (if p ∣ lin Fr i (a + 1 + j) then (0 : ℚ) else ((Fr.w i : ℚ) * (Fr.μ i).den) / (lin Fr i (a + 1 + j) : ℚ))
      (G (((Fr.μ i).den : ZMod p) * ((a + j : ℕ) : ZMod p) + ((Fr.μ i).num.toNat : ZMod p))) := by
    intro j _
    have hlin : ((lin Fr i (a + 1 + j) : ℕ) : ZMod p) =
        ((Fr.μ i).den : ZMod p) * ((a + j : ℕ) : ZMod p) + ((Fr.μ i).num.toNat : ZMod p) := by
      unfold lin
      push_cast [show a + 1 + j - 1 = a + j by omega]
      ring
    rw [← hlin]
    by_cases h : p ∣ lin Fr i (a + 1 + j)
    · simp only [h, ite_true]
      have : ((lin Fr i (a + 1 + j) : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
      rw [this, hG]
      simp only [inv_zero, mul_zero]
      exact Good.zero
    · simp only [h, ite_false]
      have hne : ((lin Fr i (a + 1 + j) : ℕ) : ZMod p) ≠ 0 := fun h' => h ((ZMod.natCast_eq_zero_iff _ _).1 h')
      have := (CatalanCore.Good.intCast (ℓ := p) c).div (CatalanCore.Good.natCast (ℓ := p)
        (lin Fr i (a + 1 + j))) hne
      simpa [hG, hc, div_eq_mul_inv] using this
  have hs := CatalanCore.Good.sum (range p) _ _ hgood
  have hz : ∑ j ∈ range p, G (((Fr.μ i).den : ZMod p) * ((a + j : ℕ) : ZMod p) + ((Fr.μ i).num.toNat : ZMod p))
      = 0 := by
    by_cases hd0 : ((Fr.μ i).den : ZMod p) = 0
    · have hc0 : (c : ZMod p) = 0 := by simp [hc, hd0]
      simp [hG, hc0]
    · rw [sum_range_affine hd0 ((Fr.μ i).num.toNat : ZMod p) a G]
      simp only [hG]
      rw [← Finset.mul_sum, sum_inv_zmod h3, mul_zero]
  rw [hz] at hs
  exact hs


/-- Several blocks. -/
theorem block_multi (i : Fin Fr.d) (h3 : 3 ≤ p) (t s : ℕ) :
    CatalanCore.Good p (∑ k ∈ Ioc t (t + s * p),
      (if p ∣ lin Fr i k then (0 : ℚ) else ((Fr.w i : ℚ) * (Fr.μ i).den) / (lin Fr i k : ℚ))) 0 := by
  induction s with
  | zero => simpa using (CatalanCore.Good.zero (ℓ := p))
  | succ s ih =>
    have e : t + (s + 1) * p = (t + s * p) + p := by ring
    rw [e, ← Finset.sum_Ioc_consecutive _ (show t ≤ t + s * p by omega) (show t + s * p ≤ t + s * p + p by omega)]
    have := ih.add (block_good i h3 (t + s * p))
    simpa using this

/-- `Good p x 0` means `x / p` is `p`-integral. -/
theorem div_mem_of_good_zero {x : ℚ} (h : CatalanCore.Good p x 0) : x / p ∈ LocRing p := by
  have hx : x ∈ LocRing p := h.1
  have h0 : redQ p ⟨x, hx⟩ = 0 := h.2
  obtain ⟨y, hy⟩ := (redQ_eq_zero_iff p ⟨x, hx⟩).1 h0
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have : x = (p : ℚ) * (y : ℚ) := by
    have := congrArg (fun z : LocRing p => (z : ℚ)) hy
    simpa using this
  rw [this]
  field_simp
  exact y.2


/-- The nonpolar sum of any number of periods is divisible by every odd prime. -/
theorem periodSum_nonpol (h3 : 3 ≤ p) (t s : ℕ) :
    (∑ k ∈ Ioc t (t + s * p), nonpolD p Fr k) / (p : ℚ) ∈ LocRing p := by
  apply div_mem_of_good_zero
  unfold nonpolD
  rw [Finset.sum_comm]
  have := CatalanCore.Good.sum (univ : Finset (Fin Fr.d)) _ (fun _ => (0 : ZMod p))
    (fun i _ => block_multi i h3 t s)
  simpa using this

/-- Lemma A, without a shift-denominator or absolute-node restriction. -/
theorem lemmaA (h3 : 3 ≤ p) (t s : ℕ) :
    ∃ D : ℚ, ∑ k ∈ Ioc t (t + s * p), Fr.Delta k = (Vp p Fr (t + s * p) - Vp p Fr t) / p + D ∧
      D / (p : ℚ) ∈ LocRing p :=
  ⟨_, offSum_split (by nlinarith [Nat.zero_le (s * p)]), periodSum_nonpol h3 t s⟩

end Block

end CatalanCore.Uniform.Bank.Plane1.Dips

#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.lemmaA
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.diag_split
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Vp_mem
#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Up_mem
