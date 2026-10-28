module

public import CatalanCore.Uniform.Decay.Cert.AllMinorAux
public import CatalanCore.Uniform.Decay.Nodes.EnergySmall
public import CatalanCore.Uniform.Decay.Nodes.Hypotheses
public import CatalanCore.Decay.Rect.LemmaBG
public import CatalanCore.Decay.Rect.Energy1
public import CatalanCore.Decay.Rect.CertG

@[expose] public section

/-!
# Glue: D3's all-deletion energy estimate to `HasAllMinorDecay` (lane D, package D5)

`hasAllMinorDecay_of_certG` wires `BlockGeom.energy_geom_small` (D3) through `Frame.lemmaBG`
(cap sum), `free_norm_le` (norm control) and `Frame.theoremN_rect` into
`NodeFamily.HasAllMinorDecay G.geometry Fr D0 cB` with

  `D0 = 2 M m' + 2 d S_base - M² I_bound + J_node`.

`hasScaledDecay_of_certG` then applies D5a/D3's `BlockGeom.hasScaledDecay_of_allMinor`.
The weights are nonnegative (V = 1); signed weights need a signed variant of D3's energy estimate.
-/

namespace CatalanCore.Uniform.Decay.Cert

open Finset Matrix CatalanCore CatalanCore.Uniform CatalanLambda.Decay Rect

theorem N_log_le {Nn Mm rc A B r : ℝ} (hN0 : 0 ≤ Nn) (hMm : 0 ≤ Mm) (hrc : 0 ≤ rc)
    (hA : 0 ≤ A) (hB : 1 ≤ B) (hr : 1 ≤ r) (hN : Nn ≤ Mm * r + rc) :
    Nn * Real.log (A * r + B) ≤
      ((Mm + rc) * (1 + |Real.log (A + B)|)) * r * (Real.log (r + 1) + 1) := by
  have hM1 : 1 ≤ A * r + B := by nlinarith
  have hl0 : 0 ≤ Real.log (A * r + B) := Real.log_nonneg hM1
  have hP : 0 < A + B := by linarith
  have hle : A * r + B ≤ (A + B) * (r + 1) := by nlinarith
  have hlog : Real.log (A * r + B) ≤ Real.log (A + B) + Real.log (r + 1) := by
    rw [← Real.log_mul hP.ne' (by linarith)]
    exact Real.log_le_log (by linarith) hle
  have hr1 : 0 ≤ Real.log (r + 1) := Real.log_nonneg (by linarith)
  have hL : Real.log (A * r + B) ≤ (1 + |Real.log (A + B)|) * (Real.log (r + 1) + 1) := by
    have := le_abs_self (Real.log (A + B))
    nlinarith [abs_nonneg (Real.log (A + B))]
  have hNr : Nn ≤ (Mm + rc) * r := by nlinarith
  calc Nn * Real.log (A * r + B)
      ≤ ((Mm + rc) * r) * ((1 + |Real.log (A + B)|) * (Real.log (r + 1) + 1)) :=
        mul_le_mul hNr hL hl0 (by positivity)
    _ = _ := by ring

theorem rowN_inj {G : BlockGeom} {r : ℕ} (S : Finset (G.geometry r).C) :
    Function.Injective (Sum.elim (fun a : S => ((a.1 : (G.geometry r).C) : ℕ)) (G.geometry r).xs) := by
  rintro (a | i) (b | j) h
  · simp only [Sum.elim_inl] at h
    exact congrArg Sum.inl (Subtype.ext (Subtype.ext h))
  · simp only [Sum.elim_inl, Sum.elim_inr] at h
    exact absurd (h ▸ a.1.2) (fun hc => Finset.disjoint_left.mp (G.geometry r).disjCX hc
      (Finset.orderEmbOfFin_mem _ _ j))
  · simp only [Sum.elim_inl, Sum.elim_inr] at h
    exact absurd (h ▸ b.1.2) (fun hc => Finset.disjoint_left.mp (G.geometry r).disjCX hc
      (Finset.orderEmbOfFin_mem _ _ i))
  · simp only [Sum.elim_inr] at h
    exact congrArg Sum.inr (((G.geometry r).X'.orderEmbOfFin rfl).injective h)

theorem colN_inj {G : BlockGeom} {r : ℕ} (S : Finset (G.geometry r).C) :
    Function.Injective (Sum.elim (fun a : S => ((a.1 : (G.geometry r).C) : ℕ)) (G.geometry r).ys) := by
  rintro (a | i) (b | j) h
  · simp only [Sum.elim_inl] at h
    exact congrArg Sum.inl (Subtype.ext (Subtype.ext h))
  · simp only [Sum.elim_inl, Sum.elim_inr] at h
    exact absurd (h ▸ a.1.2) (fun hc => Finset.disjoint_left.mp (G.geometry r).disjCY hc
      (Finset.orderEmbOfFin_mem _ _ j))
  · simp only [Sum.elim_inl, Sum.elim_inr] at h
    exact absurd (h ▸ b.1.2) (fun hc => Finset.disjoint_left.mp (G.geometry r).disjCY hc
      (Finset.orderEmbOfFin_mem _ _ i))
  · simp only [Sum.elim_inr] at h
    exact congrArg Sum.inr (((G.geometry r).Y'.orderEmbOfFin (G.geometry r).card_eq.symm).injective h)

end CatalanCore.Uniform.Decay.Cert
