module

public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Order

/-!
# Z0.11: bridge from polynomials to power series at a point

`toPS f a : R[X] →+* S⟦X⟧` sends `θ ↦ C (f a) + X` (so `p ↦ p(a + ε)`).  If `ε^e ∣ toPS f (-c) p`
and `f` is injective, then `(X + C c)^e ∣ p`.
-/

@[expose] public section

open Polynomial

namespace CatalanCore.Bordered

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `θ ↦ f a + ε`. -/
noncomputable def toPS (f : R →+* S) (a : R) : R[X] →+* PowerSeries S :=
  Polynomial.eval₂RingHom (PowerSeries.C.comp f) (PowerSeries.C (f a) + PowerSeries.X)

lemma toPS_eq (f : R →+* S) (a : R) (p : R[X]) :
    toPS f a p = PowerSeries.map f (((p.comp (X + C a) : R[X])) : PowerSeries R) := by
  have : toPS f a = (PowerSeries.map f).comp
      ((Polynomial.coeToPowerSeries.ringHom).comp (Polynomial.compRingHom (X + C a))) := by
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · simp [toPS]
    · simp [toPS, Polynomial.coeToPowerSeries.ringHom_apply, add_comm]
  rw [this]; simp

/-- **Z0.11.** -/
theorem dvd_of_toPS (f : R →+* S) (hf : Function.Injective f) (c : R) (p : R[X]) (e : ℕ)
    (h : (PowerSeries.X : PowerSeries S) ^ e ∣ toPS f (-c) p) :
    (X + C c) ^ e ∣ p := by
  rw [toPS_eq, PowerSeries.X_pow_dvd_iff] at h
  have hq : (X : R[X]) ^ e ∣ p.comp (X + C (-c)) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro m hm
    have := h m hm
    rw [PowerSeries.coeff_map, Polynomial.coeff_coe] at this
    exact hf (by simpa using this)
  have key : p = (p.comp (X + C (-c))).comp (X + C c) := by
    rw [Polynomial.comp_assoc]
    simp [add_assoc, ← C_add]
  obtain ⟨r, hr⟩ := hq
  refine ⟨r.comp (X + C c), ?_⟩
  conv_lhs => rw [key, hr]
  simp [Polynomial.mul_comp]

end CatalanCore.Bordered
