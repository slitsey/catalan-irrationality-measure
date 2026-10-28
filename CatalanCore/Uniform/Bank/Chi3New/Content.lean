import CatalanCore.Uniform.Bank.Chi3New.Geom
import CatalanCore.Uniform.Bank.Chi3Content.Final
import CatalanCore.Uniform.Content.Shape.Reindex
set_option Elab.async false

/-! Content of the chi3 block family at scales `r ≡ 0 (mod 4)` (lane B, B3f).

At `r = 4 j` the member `(r, S)` of the block family `G12.family p6Frame depth` is the common-node
minor `commonMinorPoly p6Frame r j s` of the old route, with `j = r/4` border pairs, so the
M3D-refined denominator `Dnew r j` (B3c, `Λ = 4744590251372789/1155228423148800`) clears it. -/

namespace CatalanCore.Uniform.Bank.Chi3New
open Polynomial Finset Filter CatalanCore CatalanCore.Rect CatalanCore.Uniform
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Wire CatalanFrames.P6
  CatalanFrames.P6Hybrid CatalanCore.Uniform.Bank.Chi3Content

theorem G12_borderSize {r : ℕ} (hr : r % 4 = 0) : G12.borderSize r = r / 4 := by
  have h2 : r % 2 = 0 := by omega
  show (altGeom (1 / 2) half_pos).borderSize r = r / 4
  rw [altGeom_borderSize _ _ h2]
  obtain ⟨j, rfl⟩ : ∃ j, r = 4 * j := ⟨r / 4, by omega⟩
  have e1 : ((1 / 2 : ℚ) * ((4 * j : ℕ) : ℚ) / 2) = (j : ℚ) := by push_cast; ring
  have h1 : ⌈((1 / 2 : ℚ) * ((4 * j : ℕ) : ℚ) / 2)⌉₊ = j := by rw [e1, Nat.ceil_natCast]
  have h3 : ⌈(((1 / 2 : ℚ) * ((4 * j : ℕ) : ℚ) - 1) / 2)⌉₊ = j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0
      simp only [Nat.mul_zero, Nat.cast_zero, mul_zero, zero_sub]
      exact Nat.ceil_eq_zero.2 (by norm_num)
    · rw [Nat.ceil_eq_iff (by omega)]
      constructor
      · push_cast
        have : ((j - 1 : ℕ) : ℚ) = (j : ℚ) - 1 := by
          rw [Nat.cast_sub (by omega)]; simp
        rw [this]; linarith
      · push_cast; linarith
  rw [h1, h3]
  simp

theorem G12_k {r : ℕ} (hr : r % 4 = 0) : (G12.geometry r).k = r / 4 := by
  have h2 : r % 2 = 0 := by omega
  have hf : Function.Injective (fun i : ℕ => r + 2 * i) := fun a b h => by simp at h; omega
  show ((altGeom (1 / 2) half_pos).geometry r).X'.card = r / 4
  rw [altGeom_X _ _ h2, Finset.card_image_of_injective _ hf, Finset.card_range]
  exact G12_borderSize hr

theorem G12_hyb {r : ℕ} (hr : r % 2 = 0) : HybShape G12 r := altGeom_hybShape _ half_pos hr

theorem G12_adm {r : ℕ} (hr : r % 4 = 0) : Quarter.Adm r (G12.geometry r).k := by
  rw [G12_k hr]; unfold Quarter.Adm; omega

/-- The family member at an even scale is a common-node minor of the old route. -/
theorem G12_poly_eq (Fr : Frame) {r : ℕ} (hr : r % 2 = 0) (S : Finset (G12.geometry r).C) :
    ∃ s : Finset (Fin r), (FullN Fr (fun a : S => ((a.1 : (G12.geometry r).C) : ℕ))
        (G12.geometry r).xs (G12.geometry r).ys (X : ℚ[X])).det =
      commonMinorPoly Fr r (G12.geometry r).k s := by
  classical
  have hs := G12_hyb hr
  have hCmem : ∀ x : (G12.geometry r).C, x.1 < r := by
    intro x
    have h : x.1 ∈ Finset.range r := by rw [← hs.C_eq]; exact x.2
    exact Finset.mem_range.mp h
  let s : Finset (Fin r) := Finset.univ.filter (fun c => ∃ a ∈ S, (a : ℕ) = c.val)
  have hmem : ∀ c : Fin r, c ∈ s ↔ ∃ a ∈ S, (a : ℕ) = c.val := by
    intro c; simp [s]
  let f : s ≃ S :=
    { toFun := fun c => ⟨((hmem c.1).1 c.2).choose, ((hmem c.1).1 c.2).choose_spec.1⟩
      invFun := fun a => ⟨⟨a.1.1, hCmem a.1⟩, (hmem _).2 ⟨a.1, a.2, rfl⟩⟩
      left_inv := fun c => Subtype.ext (Fin.ext (((hmem c.1).1 c.2).choose_spec.2))
      right_inv := fun a => Subtype.ext (Subtype.ext (by
        have h := ((hmem ⟨a.1.1, hCmem a.1⟩).1 ((hmem _).2 ⟨a.1, a.2, rfl⟩)).choose_spec.2
        exact h)) }
  have hdet := det_fullN_reindex Fr (fun a : S => ((a.1 : (G12.geometry r).C) : ℕ))
    (fun a : s => (a.1 : Fin r).val) f (fun a => (((hmem a.1).1 a.2).choose_spec.2).symm)
    (G12.geometry r).xs (G12.geometry r).ys
  have hxs : (G12.geometry r).xs = fun i : Fin (G12.geometry r).k => r + 2 * i.val :=
    funext hs.xs_eq
  have hys : (G12.geometry r).ys = fun i : Fin (G12.geometry r).k => r + 2 * i.val + 1 :=
    funext hs.ys_eq
  refine ⟨s, ?_⟩
  unfold commonMinorPoly
  rw [← hdet, hxs, hys]

/-- **Scaled content of the chi3 block family at scales `≡ 0 mod 4`.** -/
theorem hasScaledContent_chi3 (depth : ℕ) :
    HasScaledContent ((G12.family p6Frame depth).restrictAdm (fun i => i.1 % 4 = 0)) G12.scale
      (LamNew : ℝ) := by
  refine ⟨fun i => Dnew i.1 (G12.geometry i.1).k, fun i => Dnew_pos _ _, ?_, ?_⟩
  · intro i hi p q hq
    have hr2 : i.1 % 2 = 0 := by have := hi.2; omega
    obtain ⟨s, hQ⟩ := G12_poly_eq p6Frame hr2 i.2
    have hQ' : (G12.family p6Frame depth).Q i = commonMinorPoly p6Frame i.1 (G12.geometry i.1).k s :=
      hQ
    exact Content.Member.int_clear' ((G12.family p6Frame depth).Q i) i.2.card
      (NodeFamily.polynomial_degree p6Frame G12.geometry i) (Dnew i.1 (G12.geometry i.1).k)
      (fun j => by rw [hQ']; exact Dnew_integral i.1 _ s j) p q hq
  · intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1 (log_content_m3 ε hε)
    refine ⟨N, fun i hi hR => ?_⟩
    exact hN i.1 hR _ (G12_adm hi.2)

end CatalanCore.Uniform.Bank.Chi3New
