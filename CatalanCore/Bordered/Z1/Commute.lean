module

public import CatalanCore.Bordered.Z1.Bisp
public import CatalanCore.Bordered.Z1.Ratios

/-!
# Z1.2: `[T, X′] = 0`

Over `ℚ` at `θ > 0`, then lifted to `ℚ[X]`.
-/

@[expose] public section

open Finset Matrix

namespace CatalanCore.Bordered.Z1

lemma PiY_ne (s m j : ℕ) (hj : j ≤ s) : PiY s m j ≠ 0 := by
  unfold PiY
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  have : (j : ℚ) ≤ s := by exact_mod_cast hj
  push_cast
  intro h
  have : (0 : ℚ) ≤ 2 * i := by positivity
  linarith

/-- Common setup: ratios for `poch` and `ω′`. -/
lemma ratio_facts (s m k : ℕ) (θ : ℚ) (hθ : 0 < θ) (hk : k + 1 < s) :
    poch θ (s + m) (k + 2) = poch θ (s + m) (k + 1) * (θ + (k + 1) + (s + m : ℕ)) / (θ + (k + 1)) ∧
    omegaP s (k + 2) = -((k : ℚ) + 1) * omegaP s (k + 1) / ((s : ℚ) - (k + 1)) := by
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have hsk : (s : ℚ) - (k + 1) ≠ 0 := by
    have : (k + 1 : ℚ) < s := by exact_mod_cast hk
    linarith
  constructor
  · have h := poch_succ θ (s + m) (k + 1)
    rw [eq_div_iff (by linarith)]
    push_cast at h ⊢
    linarith
  · have h := omegaP_succ s (k + 1) (by omega) hk
    rw [eq_div_iff hsk]
    push_cast at h ⊢
    linarith

lemma E1a (s m k : ℕ) (θ : ℚ) (hθ : 0 < θ) (hk : k + 1 < s) :
    Lam2 s m θ k * (-(((k : ℚ) + 1) * ((k : ℚ) + 1 + θ) * ((k : ℚ) + 1 + θ + ((s + m : ℕ) : ℚ))
        * ((s : ℚ) - k - 1)) * qc (pj s m k)) =
      lq θ ((k : ℚ) + 2) * Lam2 s m θ (k + 1) := by
  obtain ⟨hp, hw⟩ := ratio_facts s m k θ hθ hk
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have hsk : (s : ℚ) - (k + 1) ≠ 0 := by
    have : (k + 1 : ℚ) < s := by exact_mod_cast hk
    linarith
  have x1 := PiX_ne s m (k + 1) (by omega)
  have x2 := PiX_ne s m (k + 2) (by omega)
  have w1 := omegaP_ne s (k + 1)
  have w2 := omegaP_ne s (k + 2)
  simp only [Lam2, qc, Algebra.algebraMap_self, RingHom.id_apply, pj, lq]
  rw [hp] at *
  have e1 : ((k + 1 + 1 : ℕ) : ℚ) = k + 2 := by push_cast; ring
  rw [show k + 1 + 1 = k + 2 from rfl, hp, hw]
  push_cast
  have hb : θ + ((k : ℚ) + 1) ≠ 0 := by linarith
  have hb' : (k : ℚ) + 1 + θ ≠ 0 := by linarith
  have ha : (k : ℚ) + 1 ≠ 0 := by linarith
  have hsk' : (s : ℚ) - k - 1 ≠ 0 := by intro h; apply hsk; linarith
  field_simp
  ring

lemma E1b (s m k : ℕ) (θ : ℚ) (hθ : 0 < θ) (hk : k + 1 < s) :
    Lam2 s m θ (k + 1) * (-(((k : ℚ) + 1) * ((k : ℚ) + 1 + θ) * ((s : ℚ) + 2 * m - k - 1)
        * (((s + m : ℕ) : ℚ) + θ + k + 1)) * qc (1 / pj s m k)) =
      rq s m θ ((k : ℚ) + 1) * Lam2 s m θ k := by
  obtain ⟨hp, hw⟩ := ratio_facts s m k θ hθ hk
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have hsk : (s : ℚ) - (k + 1) ≠ 0 := by
    have : (k + 1 : ℚ) < s := by exact_mod_cast hk
    linarith
  have x1 := PiX_ne s m (k + 1) (by omega)
  have x2 := PiX_ne s m (k + 2) (by omega)
  have w1 := omegaP_ne s (k + 1)
  have w2 := omegaP_ne s (k + 2)
  simp only [Lam2, qc, Algebra.algebraMap_self, RingHom.id_apply, pj, rq]
  rw [show k + 1 + 1 = k + 2 from rfl, hp, hw]
  push_cast
  have hb : θ + ((k : ℚ) + 1) ≠ 0 := by linarith
  have hb' : (k : ℚ) + 1 + θ ≠ 0 := by linarith
  have ha : (k : ℚ) + 1 ≠ 0 := by linarith
  have hsk' : (s : ℚ) - k - 1 ≠ 0 := by intro h; apply hsk; linarith
  field_simp
  ring

lemma E2a (s m k : ℕ) (θ : ℚ) (hθ : 0 < θ) (hk : k + 1 < s) :
    (-(((k : ℚ) + 1) * ((k : ℚ) + 1 + θ) * ((k : ℚ) + 1 + θ + ((s + m : ℕ) : ℚ))
        * ((s : ℚ) - k - 1)) * qc (pj s m k)) * Lam1 s m θ (k + 1) =
      Lam1 s m θ k * rq s m θ ((k : ℚ) + 1) := by
  obtain ⟨hp, hw⟩ := ratio_facts s m k θ hθ hk
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have hsk : (s : ℚ) - (k + 1) ≠ 0 := by
    have : (k + 1 : ℚ) < s := by exact_mod_cast hk
    linarith
  have x1 := PiX_ne s m (k + 1) (by omega)
  have x2 := PiX_ne s m (k + 2) (by omega)
  have y1 := PiY_ne s m (k + 1) (by omega)
  have y2 := PiY_ne s m (k + 2) (by omega)
  have w1 := omegaP_ne s (k + 1)
  have w2 := omegaP_ne s (k + 2)
  have hxy := PiXY_shift s m k
  have hsk' : (s : ℚ) - k - 1 ≠ 0 := by intro h; apply hsk; linarith
  have hY1 : PiY s m (k + 1) = PiX s m (k + 2) * PiY s m (k + 2) * ((s : ℚ) + 2 * m - k - 1)
      / (PiX s m (k + 1) * ((s : ℚ) - k - 1)) := by
    rw [eq_div_iff (mul_ne_zero x1 hsk')]; linarith
  simp only [Lam1, qc, Algebra.algebraMap_self, RingHom.id_apply, pj, rq]
  rw [show k + 1 + 1 = k + 2 from rfl, hp, hw, hY1]
  push_cast
  have hb : θ + ((k : ℚ) + 1) ≠ 0 := by linarith
  have hb' : (k : ℚ) + 1 + θ ≠ 0 := by linarith
  have ha : (k : ℚ) + 1 ≠ 0 := by linarith
  have he : (s : ℚ) + 2 * m - k - 1 ≠ 0 := by
    intro h
    have : (k + 1 : ℚ) < s := by exact_mod_cast hk
    have : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    linarith
  have he2 : (s : ℚ) + 2 * m - (k + 1) ≠ 0 := by intro h; apply he; linarith
  have he3 : -1 - (k : ℚ) + s + m * 2 ≠ 0 := by intro h; apply he; linarith
  have he4 : (s : ℚ) + m * 2 - k - 1 ≠ 0 := by intro h; apply he; linarith
  have hd3 : -1 - (k : ℚ) + s ≠ 0 := by intro h; apply hsk'; linarith
  field_simp
  ring

lemma E2b (s m k : ℕ) (θ : ℚ) (hθ : 0 < θ) (hk : k + 1 < s) :
    (-(((k : ℚ) + 1) * ((k : ℚ) + 1 + θ) * ((s : ℚ) + 2 * m - k - 1)
        * (((s + m : ℕ) : ℚ) + θ + k + 1)) * qc (1 / pj s m k)) * Lam1 s m θ k =
      Lam1 s m θ (k + 1) * lq θ ((k : ℚ) + 2) := by
  obtain ⟨hp, hw⟩ := ratio_facts s m k θ hθ hk
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  have hsk : (s : ℚ) - (k + 1) ≠ 0 := by
    have : (k + 1 : ℚ) < s := by exact_mod_cast hk
    linarith
  have x1 := PiX_ne s m (k + 1) (by omega)
  have x2 := PiX_ne s m (k + 2) (by omega)
  have y1 := PiY_ne s m (k + 1) (by omega)
  have y2 := PiY_ne s m (k + 2) (by omega)
  have w1 := omegaP_ne s (k + 1)
  have w2 := omegaP_ne s (k + 2)
  have hxy := PiXY_shift s m k
  have hsk' : (s : ℚ) - k - 1 ≠ 0 := by intro h; apply hsk; linarith
  have hY1 : PiY s m (k + 1) = PiX s m (k + 2) * PiY s m (k + 2) * ((s : ℚ) + 2 * m - k - 1)
      / (PiX s m (k + 1) * ((s : ℚ) - k - 1)) := by
    rw [eq_div_iff (mul_ne_zero x1 hsk')]; linarith
  simp only [Lam1, qc, Algebra.algebraMap_self, RingHom.id_apply, pj, lq]
  rw [show k + 1 + 1 = k + 2 from rfl, hp, hw, hY1]
  push_cast
  have hb : θ + ((k : ℚ) + 1) ≠ 0 := by linarith
  have hb' : (k : ℚ) + 1 + θ ≠ 0 := by linarith
  have ha : (k : ℚ) + 1 ≠ 0 := by linarith
  have he : (s : ℚ) + 2 * m - k - 1 ≠ 0 := by
    intro h
    have : (k + 1 : ℚ) < s := by exact_mod_cast hk
    have : (0 : ℚ) ≤ m := Nat.cast_nonneg m
    linarith
  have he2 : (s : ℚ) + 2 * m - (k + 1) ≠ 0 := by intro h; apply he; linarith
  have he3 : -1 - (k : ℚ) + s + m * 2 ≠ 0 := by intro h; apply he; linarith
  have he4 : (s : ℚ) + m * 2 - k - 1 ≠ 0 := by intro h; apply he; linarith
  have hd3 : -1 - (k : ℚ) + s ≠ 0 := by intro h; apply hsk'; linarith
  field_simp
  ring

end CatalanCore.Bordered.Z1
