module

public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Bank
public import CatalanCore.Uniform.Bank.Plane2.Content.Transl
public import CatalanCore.Uniform.Bank.Plane2.BoundEdge

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-!
# Plane 2 content (lane H, wave P210-L; ledger P210, P213)

The content of the plane 2 families at `α = 3/41` (`c = 6/41`), by the closed route: Theorem PC
(`KTerm.Periodic.hasScaledContent_of_periodic_ok`) for the bank `Content.Data.p2D` (a table of one period of the bands
`1 .. 6`, `8` strips and a partial strip of the translates, a head of rows `P₄ .. P₇`, `E₁`, `E₂`, the tail), with the
rows `Real` of the catalogue (`Content.RowsBand`, `RowsE`, `RowsP`, `Tail`, `Union`), the translation instance
`Content.p2Tr` and the data check of `Content.Data`.

* `plane2_content_fS`: `HasScaledContent` of the even-scale family of the sequences `(fS v u, eS v u)` (`v ≠ 0`, any `u`,
  any constant) with `Λ = plane2Lam` (`≈ 3.4768376`, the exact value `Data.p2D.Λ = 3.476837530…` rounded up);
* `plane2Content_inst : Plane2Content plane2Lam`, `plane2ContentZeta_inst : Plane2ContentZeta plane2Lam`, and
  `plane2Lam ≤ p2LamMax`.
-/

namespace CatalanCore.Uniform.Bank.Plane2

open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Support CatalanCore.Uniform.Content.Sweep
  CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Bank.Plane2.Content
  CatalanCore.Uniform.Bank.Plane2.Content.Data

/-- Content is monotone in the constant. -/
theorem hasScaledContent_mono {Fam : PolyFamily} {scale : Fam.ι → ℕ} {Λ Λ' : ℝ}
    (h : HasScaledContent Fam scale Λ) (hle : Λ ≤ Λ') : HasScaledContent Fam scale Λ' := by
  obtain ⟨den, hd, hz, hl⟩ := h
  refine ⟨den, hd, hz, fun ε hε => ?_⟩
  obtain ⟨R0, hR⟩ := hl ε hε
  refine ⟨R0, fun n hn hR0 => (hR n hn hR0).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- **The finite-strip value** (the exact rational `Data.p2D.Λ` of the bank, rounded up to nine digits). -/
def plane2Lam : ℚ := 3476837531 / 1000000000

theorem plane2Lam_ge : Data.p2D.Λ ≤ plane2Lam := by
  -- kcost: rational comparison of a 3500-digit literal, < 1 s
  decide +kernel

theorem plane2Lam_le_max : plane2Lam ≤ p2LamMax := by
  unfold plane2Lam p2LamMax
  norm_num

theorem plane2Lam_lt_Dt : plane2Lam < Cover.Dchi.Dt := lt_of_le_of_lt plane2Lam_le_max p2_eta

theorem p2D_t0_le : Data.p2D.t0 ≤ 1 := by
  -- kcost: 0.01 s measured (one rational comparison)
  decide +kernel

theorem p2D_alpha0b : (132 / 41 : ℚ) ≤ Data.p2D.α0b := by
  -- kcost: 0.01 s measured (one rational comparison)
  decide +kernel

/-- **The content of the plane 2 families.**  For every `v ≠ 0`, every `u`, every constant and every selection depth
`≤ 64` (all debits are `0`, so the depth plays no role). -/
theorem plane2_content_fS (v u : ℤ) (hv : v ≠ 0) (const : ℝ) (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent
      (((altGeom (6 / 41) plane2_pos).seqFamily (fS v u) (eS v u) const depth).restrictAdm
        (fun n => SeqFamily.scale (altGeom (6 / 41) plane2_pos).geometry n % 2 = 0))
      (SeqFamily.scale (altGeom (6 / 41) plane2_pos).geometry) (plane2Lam : ℝ) := by
  have hQ := p2_altQ v u hv
  have hpre := p2_preValid v u hv const depth 2 66 le_rfl Data.p2D.t0 Data.p2D.α0b p2D_t0_le
    p2D_alpha0b
  have hcat := kcatValid_of_real v u const depth (headList ++ brU56 :: bandList 0 6) kcat_debit (real_kcat v u hv)
  have hvalid : ∀ n, KCatValidFam (6 / 41) plane2_pos const depth
      (SeqFamily.poly (fS v u) (eS v u) p2G.geometry) p2shifts 2 p2Pbad (p2N0 v)
      ((bandList 0 6).map (p2rho n)) := fun n =>
    kcatValid_of_real v u const depth _ (rho_debit n) (by
      intro b hb
      obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hb
      exact real_rho v u hv n hb')
  have h := hasScaledContent_of_periodic_ok Data.p2D p2_params p2_class p2_heads (6 / 41) plane2_pos
    (by norm_num [Data.p2D, Data.p2H, qq]) const depth (SeqFamily.poly (fS v u) (eS v u) p2G.geometry) hd hQ
    (p2Budget 16 66) (p2N0 v) (b := 41) (a := 3) (Kc := 132) (Ω := 400)
    (by norm_num [Data.p2D, Data.p2H, qq]) p2Tr [(1, Data.p2T)] rfl
    (by
      intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst hx
      exact Data.p2_cells y hy)
    (by
      intro x hx y hy
      simp only [List.mem_singleton] at hx
      subst hx
      exact Data.p2_headok y hy)
    hcat hvalid hpre
  have hle : (Data.p2D.Λ : ℝ) ≤ (plane2Lam : ℝ) := by exact_mod_cast plane2Lam_ge
  exact hasScaledContent_mono h hle

/-- **`Plane2Content`** (`P209`, `BoundEdge`): the generic datum `plane2 v u`, `v u ≠ 0`, at depth `1`. -/
theorem plane2Content_inst : Plane2Content (plane2Lam : ℝ) := by
  intro v u hv hu
  have h := plane2_content_fS v u hv (Datum.plane2 v u hv hu).xi 1 (by norm_num)
  unfold p2Fam
  rw [plane2_f v u hv hu, plane2_e v u hv hu]
  exact h

/-- **`Plane2ContentZeta`**: the one-term datum of `ζ(3)`. -/
theorem plane2ContentZeta_inst : Plane2ContentZeta (plane2Lam : ℝ) := by
  have h := plane2_content_fS 1 0 one_ne_zero zeta3Datum.xi 1 (by norm_num)
  unfold Plane2ContentZeta
  rw [zeta3Datum_f, zeta3Datum_e]
  exact h

end CatalanCore.Uniform.Bank.Plane2
#print axioms CatalanCore.Uniform.Bank.Plane2.plane2_content_fS
#print axioms CatalanCore.Uniform.Bank.Plane2.plane2Content_inst
#print axioms CatalanCore.Uniform.Bank.Plane2.plane2ContentZeta_inst
#print axioms CatalanCore.Uniform.Bank.Plane2.plane2Lam_le_max
