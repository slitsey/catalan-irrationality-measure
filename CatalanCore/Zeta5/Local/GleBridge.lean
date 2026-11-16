module

public import CatalanCore.Zeta5.Local.Val
public import CatalanCore.Arith.Hybrid.Tropical
public import CatalanCore.Arith.Hybrid.PrimeDenominator

@[expose] public section

/-!
# Conversion of Gauss-valuation bounds `GV` to the tropical `GLE`

`GV p f r` (this directory) says every coefficient of `f ∈ ℚ[X]` has `v_p ≥ r` (rational `r`).
`CatalanCore.Arith.Hybrid.GLE p B f` (`B : ℕ`) says every coefficient `c` has `p^B c ∈ ℤ_(p)`.
They agree for `r = -B`:

* `GLE_iff_GV : GLE p B f ↔ GV p f (-(B : ℚ))`;
* `GLE_of_GV_le : GV p f r → -r ≤ B → GLE p B f` (any natural `B ≥ -r`, so `B = ⌈-r⌉` for a
  half-integer weight bound);
* `GLE_det_of_weights` : the weighted determinant bound `det_GV` in `GLE` form;
* `primeDenominator_integral_of_GV` : per-prime `GV` budgets give one integer denominator
  (`CatalanCore.Arith.Hybrid.primeDenominator_integral`).
-/

open Finset Polynomial

namespace Apery

open CatalanCore.Basic CatalanCore.Arith.Hybrid

variable {p : ℕ} [hp : Fact p.Prime]

/-- `ℤ_(p)` is `{0} ∪ {v_p ≥ 0}`. -/
theorem mem_locRing_iff_VG (q : ℚ) : q ∈ LocRing p ↔ VG p q 0 := by
  by_cases hq : q = 0
  · subst hq
    simp only [VG, true_or, iff_true]
    exact (LocRing p).zero_mem
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have hden : q.den ≠ 0 := q.den_nz
  have hcop : q.num.natAbs.Coprime q.den := q.reduced
  have hv : padicValRat p q = (padicValInt p q.num : ℤ) - (padicValNat p q.den : ℤ) := rfl
  constructor
  · intro h
    have hpd : ¬ p ∣ q.den := h
    right
    rw [hv, padicValNat.eq_zero_of_not_dvd hpd]
    simp
  · intro h
    have h0 := h.resolve_left hq
    rw [hv] at h0
    by_contra hpd
    have hpd' : p ∣ q.den := by simpa [mem_locRing] using hpd
    have h1 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd hden hpd'
    have h2 : 1 ≤ padicValInt p q.num := by
      have : (1 : ℚ) ≤ (padicValInt p q.num : ℤ) := by
        have h3 : ((0 : ℤ) : ℚ) ≤ ((padicValInt p q.num : ℤ) - (padicValNat p q.den : ℤ) : ℤ) := by
          exact_mod_cast (by exact_mod_cast h0 : (0 : ℚ) ≤ ((padicValInt p q.num : ℤ) - (padicValNat p q.den : ℤ) : ℤ))
        have h4 : (1 : ℤ) ≤ padicValNat p q.den := by exact_mod_cast h1
        have h5 : (0 : ℤ) ≤ (padicValInt p q.num : ℤ) - (padicValNat p q.den : ℤ) := by exact_mod_cast h3
        have : (1 : ℤ) ≤ (padicValInt p q.num : ℤ) := by omega
        exact_mod_cast this
      exact_mod_cast this
    have hpn : p ∣ q.num.natAbs := by
      have : (p : ℤ) ∣ q.num := by
        have := (padicValInt_dvd_iff (p := p) 1 q.num).mpr (Or.inr h2)
        simpa using this
      exact Int.natCast_dvd.mp this
    exact hp.out.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hpn hpd')

/-- **GLE = GV at `-B`.** -/
theorem GLE_iff_GV (B : ℕ) (f : ℚ[X]) : GLE p B f ↔ GV p f (-(B : ℚ)) := by
  unfold GLE GV
  refine forall_congr' fun i => ?_
  rw [mem_locRing_iff_VG]
  set c := f.coeff i
  by_cases hc : c = 0
  · simp [hc, VG]
  · have hpB : ((p : ℚ) ^ B) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
    have hv : padicValRat p ((p : ℚ) ^ B * c) = B + padicValRat p c := by
      rw [padicValRat.mul hpB hc, padicValRat.pow (q := (p : ℚ)),
        padicValRat.self hp.out.one_lt]
      simp
    simp only [VG, hc, hpB, mul_eq_zero, or_self, false_or, hv]
    constructor
    · intro h; push_cast at h; linarith
    · intro h; push_cast; linarith

theorem GLE_of_GV_le {f : ℚ[X]} {r : ℚ} (h : GV p f r) {B : ℕ} (hB : -r ≤ (B : ℚ)) : GLE p B f :=
  (GLE_iff_GV B f).mpr (h.mono (by linarith))

/-- The weighted determinant bound `det_GV` in `GLE` form: if `GV p (M i j) (ρ i + κ j)` and
`-(∑ ρ + ∑ κ) ≤ B` then `GLE p B (det M)`. -/
theorem GLE_det_of_weights {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℚ[X])
    (ρ κ : ι → ℚ) (h : ∀ i j, GV p (M i j) (ρ i + κ j)) {B : ℕ}
    (hB : -(∑ i, ρ i + ∑ j, κ j) ≤ (B : ℚ)) : GLE p B M.det :=
  GLE_of_GV_le (det_GV M ρ κ h) hB

/-- Per-prime Gauss-valuation budgets (`GV p f (-E p)` for `p < N`, `GV p f 0` otherwise) give one
integer denominator: `primeDenominator N E * f_i ∈ ℤ` for every coefficient. -/
theorem primeDenominator_integral_of_GV (N : ℕ) (E : ℕ → ℕ) (f : ℚ[X])
    (hf : ∀ (p : ℕ) [Fact p.Prime], GV p f (-((if p < N then E p else 0 : ℕ) : ℚ))) (i : ℕ) :
    ∃ z : ℤ, (primeDenominator N E : ℚ) * f.coeff i = z :=
  primeDenominator_integral N E f (fun p _ => (GLE_iff_GV _ f).mpr (hf p)) i

end Apery
