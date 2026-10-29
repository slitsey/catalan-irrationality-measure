import CatalanCore.Uniform.Bank.Chi3.KContent.Content
import CatalanCore.Uniform.Bank.Chi3New.Geom
import CatalanCore.Uniform.Content.Shape.Reindex
import CatalanCore.Uniform.Frame.NVAdapter
set_option Elab.async false

/-! # Link of the k-shift content to the chi_{-3} measure theorem (lane K)

`AltEven (1/2) c12_pos p6Frame depth` is definitionally `(G12.family p6Frame depth).restrictAdm (r % 2 = 0)`
(`G12 = altGeom (1/2)` of `Chi3New.Geom`), the family of the chi_{-3} measure theorem `Chi3New.Final.chi3_measureLB`.

* `chi3_content_G12`: the content of that family at the depth `kDepth0 = G12.selectionDepth p6Frame 2` (`≤ 64`);
* `chi3_nv0_even`: nonvanishing at the scales `2 s` (from `G12.hasNV0`);
* `chi3_measureLB_of_decay`: content + any `HasScaledDecay (G12.family p6Frame kDepth0)` with `Λ < D`, `c > 0` give the
  measure bound `c / (D - Λ)` for the even-scale family.  The decay is a hypothesis (the chi_{-3} decay is being
  regenerated; `Chi3New.Decay.chi3_decay` has this shape). -/

namespace CatalanCore.Uniform.Bank.Chi3.KContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanFrames.P6
  CatalanCore.Uniform.Bank.Chi3New

/-- The selection depth of the chi_{-3} block family (period `L = 2`). -/
noncomputable def kDepth0 : ℕ := G12.selectionDepth p6Frame 2

theorem kDepth0_le : kDepth0 ≤ 64 := by
  unfold kDepth0 BlockGeom.selectionDepth
  decide +kernel

theorem p6_w_ne' (i : Fin p6Frame.d) : p6Frame.w i ≠ 0 := by
  rcases i with ⟨k, hk⟩
  have hk3 : k < 3 := hk
  interval_cases k
  · exact (by decide : (1 : ℤ) ≠ 0)
  · exact (by decide : (2 : ℤ) ≠ 0)
  · exact (by decide : (-3 : ℤ) ≠ 0)

theorem G12_common_mass' : G12.common.mass = 1 := by
  simp [G12, altGeom, single_mass, commonB, PeriodicBlock.mass]

/-- **The content of the chi_{-3} block family at even scales**, `Λ_fin = kData.Λ`. -/
theorem chi3_content_G12 :
    HasScaledContent ((G12.family p6Frame kDepth0).restrictAdm (fun i => i.1 % 2 = 0)) G12.scale
      ((kData.Λ : ℚ) : ℝ) :=
  chi3_k_content kDepth0 kDepth0_le

theorem chi3_nv0_even : ∃ R0 : ℕ, ∀ s : ℕ, R0 ≤ s → ∀ x : ℚ,
    ∃ n, ((G12.family p6Frame kDepth0).restrictAdm (fun i => i.1 % 2 = 0)).Adm n ∧ G12.scale n = 2 * s ∧
      ((G12.family p6Frame kDepth0).restrictAdm (fun i => i.1 % 2 = 0)).evalQ n x ≠ 0 := by
  obtain ⟨R0, hR⟩ := G12.hasNV0 p6Frame 2 kDepth0 (by norm_num) (by show 1 ≤ 3; norm_num) p6_w_ne'
    (fun i => by simp [G12, altGeom, single, commonB])
    (fun i => by simp [G12, altGeom, single, rowB])
    (fun i => by simp [G12, altGeom, single, colB]) le_rfl
  refine ⟨R0, fun s hs x => ?_⟩
  obtain ⟨n, hn, hsc, hne⟩ := hR (2 * s) (by omega) x
  exact ⟨n, ⟨hn, by show n.1 % 2 = 0; have : G12.scale n = n.1 := rfl; omega⟩, hsc, hne⟩

/-- **The measure bound from the content and a decay**, for the even-scale chi_{-3} family. -/
theorem chi3_measureLB_of_decay {D c : ℚ}
    (hD : HasScaledDecay (G12.family p6Frame kDepth0) G12.scale (D : ℝ) (c : ℝ))
    (hη : ((kData.Λ : ℚ) : ℝ) < (D : ℝ)) (hc : (0 : ℝ) < (c : ℝ)) :
    ((G12.family p6Frame kDepth0).restrictAdm (fun i => i.1 % 2 = 0)).MeasureLB
      ((1 : ℝ) * (c : ℝ) / ((D : ℝ) - ((kData.Λ : ℚ) : ℝ))) := by
  have hmass : (G12.common.mass : ℝ) = 1 := by rw [G12_common_mass']; norm_num
  exact measure_of_family_nv0_even
    ((G12.family p6Frame kDepth0).restrictAdm (fun i => i.1 % 2 = 0)) G12.scale
    (γ := 1) (K := G12.common.n) chi3_content_G12
    (fun ε hε => by
      obtain ⟨R0, hR⟩ := hD ε hε
      exact ⟨R0, fun n hn => hR n hn.1⟩) hη hc one_pos (Nat.cast_nonneg _)
    (fun n _ => by
      have := G12.degree_bound p6Frame kDepth0 n
      rw [hmass] at this
      exact this)
    (fun n hn => hn.2) chi3_nv0_even

end CatalanCore.Uniform.Bank.Chi3.KContent

#print axioms CatalanCore.Uniform.Bank.Chi3.KContent.chi3_content_G12
#print axioms CatalanCore.Uniform.Bank.Chi3.KContent.chi3_measureLB_of_decay
