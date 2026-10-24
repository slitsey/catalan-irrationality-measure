module

public import CatalanCore.Decay.Window

@[expose] public section

/-!
# `decay_of_cert`: the generic decay theorem (WP2b)

```
theorem decay_of_cert (hFr : Fr.DecayOK') (F : CertCore K ρ ε c m) {D : ℚ}
    (hD : D ≤ F.Dof Fr.d 0 (3/2)) : HasDecay (PolyFamily.ofFrame Fr) D F.ccert
```

Every frame satisfying the (decidable) hypotheses `DecayOK'` inherits the decay exponent of any
certificate: `D(d) = 2 (m′ + d · Sbase) - I + 3/2`, with the atom density `d = Fr.d`.
-/

open Polynomial Filter

namespace CatalanCore


namespace Frame

variable (Fr : Frame)

/-- Real evaluation of `Ppoly` at `const + t` is `det (T_h + t I)`. -/
theorem aeval_Ppoly_eq_det (h : ℕ) (t : ℝ) :
    aeval (Fr.const + t) (Fr.Ppoly h)
      = (Frame.Tmat Fr h + t • (1 : Matrix (Fin h) (Fin h) ℝ)).det := by
  unfold Frame.Ppoly
  rw [← AlgHom.coe_toRingHom, RingHom.map_det]
  congr 1
  ext a b
  by_cases hab : a = b
  · subst hab
    simp [Frame.Tmat, Tent]
    ring
  · have hab' : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
    simp [Frame.Tmat, Tent, hab, hab']

end Frame

/-- **`decay_of_cert`.**  Any certificate gives the decay of the square polynomial family of any
frame satisfying `DecayOK'`, at the exponent `D ≤ Dof Fr.d 0 (3/2)` and window constant `ccert`. -/
theorem decay_of_cert {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ} {Fr : Frame}
    (hFr : Fr.DecayOK') (F : Cert.CertCore K ρ ε c m) {D : ℚ}
    (hD : D ≤ F.Dof Fr.d 0 (3 / 2)) :
    HasDecay (PolyFamily.ofFrame Fr) (D : ℝ) (F.ccert : ℝ) := by
  intro δ hδ
  obtain ⟨m0, hm0, hm0xs, hm0μ⟩ := Frame.exists_m0 Fr hFr.contour.xs_pos
  have hD' : (D : ℝ) ≤ 2 * ((F.mprime : ℝ) + Fr.d * F.Sbase) - F.Ibound + 3 / 2 := by
    have h1 : ((D : ℚ) : ℝ) ≤ ((F.Dof Fr.d 0 (3 / 2) : ℚ) : ℝ) := by exact_mod_cast hD
    rw [Cert.CertCore.Dof_square] at h1
    push_cast at h1
    exact h1
  obtain ⟨h₀, H⟩ := Frame.window_liminf hFr.toDecayOKs' F hD' hm0 hm0xs hm0μ hδ
  refine ⟨h₀, fun n _ hn t ht => ?_⟩
  have := H n hn t ht
  have e := Frame.aeval_Ppoly_eq_det Fr n t
  show |aeval (Fr.const + t) (Fr.Ppoly n)| ≤ _
  convert this using 2
  rfl

end CatalanCore
