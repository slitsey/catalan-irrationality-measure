module
public import CatalanCore.Uniform.Decay.Nodes.Hypotheses
@[expose] public section

/-!
# The energy step for a `BlockGeom` (all node-sum hypotheses discharged)

`energy_geom`: for the actual row/column node lists of `G.geometry r` (any balancing trim),
with the common nodes enumerated first, every retained pattern (all non-common nodes kept)
and every admissible free configuration,

`∑ log q + (1/2)(log ‖C(z, R∖J)‖² + log ‖C(z, Q∖J)‖²) ≤ -r² D_0 + c r (N - k) + Err`,

`D_0 = 2 M m' + 2 S - M² I + J_node`, `J_node` the average of the separate row/column
self-energies, and `Err = O(r log r)` explicit.  Remaining inputs (certificate side): the
cap sum (`hcap`, from `lemmaBG`), the free-point norm control, the common-support bound `hℓ`.
-/

namespace CatalanCore.Uniform
open Decay.Nodes Finset CatalanLambda.Decay

/-- Enumerations of the row/column node lists with the common nodes first. -/
structure NodeEnum (G : BlockGeom) (r N nc : ℕ) where
  nR : Fin N → ℕ
  nQ : Fin N → ℕ
  injR : Function.Injective nR
  injQ : Function.Injective nQ
  imgR : Finset.univ.image nR = (G.geometry r).rows
  imgQ : Finset.univ.image nQ = (G.geometry r).cols
  commonAgree : ∀ b : Fin N, (b : ℕ) < nc → nR b = nQ b
  commonMem : ∀ b : Fin N, (b : ℕ) < nc → nR b ∈ (G.geometry r).C

theorem sum_fin_eq {N : ℕ} (nR : Fin N → ℕ) (hinj : Function.Injective nR) (S : Finset ℕ)
    (himg : Finset.univ.image nR = S) (f : ℕ → ℝ) :
    ∑ b : Fin N, f (nR b) = ∑ j ∈ S, f j := by
  rw [← himg, Finset.sum_image (fun a _ b _ h => hinj h)]

namespace BlockGeom

theorem rows_card_eq_N (G : BlockGeom) {r N nc : ℕ} (E : NodeEnum G r N nc) :
    (G.geometry r).rows.card = N := by
  rw [← E.imgR, Finset.card_image_of_injective _ E.injR]
  simp

set_option maxHeartbeats 8000000 in
/-- **Energy step for a block geometry.** -/
theorem energy_geom (G : BlockGeom) {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    (hρ : 0 < ρ) (hw0 : ∀ k, 0 ≤ wt k) (hm : ∑ k, wt k = 1) {Rc : ℝ} (hc : ∀ k, ‖c k‖ ≤ Rc)
    (g : ℂ → ℝ)
    (hg : ∀ s : ℂ, g s = (G.totalMass : ℝ) * Usig ρ c wt s - G.nodePot s +
      (1 - ε) * Real.pi * |s.im|)
    {r N nc : ℕ} (hr : 0 < r) (hN : 0 < N) (E : NodeEnum G r N nc)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) {k : ℕ} (z : Fin k → ℂ) (hzi : Function.Injective z)
    (hre : ∀ l, m0 ≤ -(z l).re)
    {a0 : ℝ} (ha1 : 1 ≤ a0) (hnorm : ∀ l, ‖z l‖ ≤ a0 * r + 2 * |(z l).im|)
    (s : Fin k → Fin N) (hs : Function.Injective s)
    (hkeep : ∀ b : Fin N, nc ≤ (b : ℕ) → ∃ i, s i = b)
    {e Cl mp ℓ cB Ibd Scap Cdef : ℝ}
    (hε : 0 < ε) (he0 : 0 < e) (heε : e < ε) (hCl : 0 ≤ Cl)
    (q : Fin k → ℝ) (hq : ∀ l, Real.log (q l) ≤ (1 - e) * (Cl - 2 * Real.pi * |(z l).im|))
    (hIb : Irho ρ c wt ≤ Ibd)
    (hcap : (k : ℝ) * mp + r * Scap - Cdef ≤ ∑ l, g (z l / r))
    (hℓ : ∀ b : Fin N, (b : ℕ) < nc → ℓ ≤ g ((E.nR b : ℂ) / r)) (hcB : 2 * (mp - ℓ) ≤ cB)
    (hmargin : 4 * (G.rowConst : ℝ) + G.E2 ≤ 2 * Real.pi * (ε - e) * r) :
    ∑ l, Real.log (q l) +
        (1 / 2) * (Real.log (‖cexpr z (fun i => ((E.nR (s i) : ℕ) : ℂ))‖ ^ 2) +
          Real.log (‖cexpr z (fun i => ((E.nQ (s i) : ℕ) : ℂ))‖ ^ 2))
      ≤ -((r : ℝ) ^ 2 * (2 * (G.totalMass : ℝ) * mp + 2 * Scap -
            (G.totalMass : ℝ) ^ 2 * Ibd + G.nodeEnergy)) + cB * r * ((N : ℝ) - k)
        + (2 * r * Cdef + 2 * r * (G.rowConst : ℝ) * |mp|
          + (2 * (G.totalMass : ℝ) * r * G.rowConst + (G.rowConst : ℝ) ^ 2) * |Ibd|
          + (1 - e) * k * Cl + 2 * (G.rowConst : ℝ) * k * (a0 + Rc + ρ + |Real.log ρ|)
          + 2 * (G.rowConst : ℝ) * ((N : ℝ) - k) * (Bd + Rc + ρ + |Real.log ρ|)
          + ((N : ℝ) - k) * G.E3 r Bd
          + k * G.E1 r Bd a0 m0 + G.E4 r Bd / 2 + N * |Real.log ρ|) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hM0 : (0 : ℝ) ≤ (G.totalMass : ℝ) := by
    have : 0 ≤ G.totalMass := by
      unfold BlockGeom.totalMass BlockGeom.gamma BlockGeom.beta
      have := G.common_pos
      have h2 : 0 ≤ G.row.mass := by
        unfold BlockCollection.mass
        exact Finset.sum_nonneg (fun i _ => (G.row.block i).mass_pos.le)
      linarith
    exact_mod_cast this
  have hcardN := G.rows_card_eq_N E
  have hNM : |(N : ℝ) - (G.totalMass : ℝ) * r| ≤ (G.rowConst : ℝ) := by
    have := G.card_rows_bound r
    rw [hcardN] at this
    exact this
  have hbd : ∀ b : Fin N, (b : ℕ) < nc → (E.nR b : ℝ) ≤ Bd * r := by
    intro b hb
    have hmem : E.nR b ∈ (G.geometry r).rows := by
      rw [← E.imgR]; exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
    rcases G.mem_rows_cases r _ hmem with h | h
    · exact node_lt_bound G.common r _ hBc h
    · exact node_lt_bound G.row r _ hBr h
  refine energy_block hρ hw0 hm hc hM0 g G.nodePot hg hr hN (Nat.cast_nonneg _) hNM
    E.nR E.nQ E.injR E.injQ E.commonAgree hbd hBd0 hm0 z hzi hre (by linarith) hnorm s hs hkeep
    hε he0 heε hCl q hq hIb hcap hℓ hcB ?_ ?_ ?_ hmargin
  · -- free-point hypothesis
    intro l
    have h := G.ps_hyp hr hBd0 hBc hBr hBq hm0 ha1 (z l) (hre l) (hnorm l)
    rw [sum_fin_eq E.nR E.injR _ E.imgR (fun j => elog (z l / r) ((j : ℂ) / r)),
      sum_fin_eq E.nQ E.injQ _ E.imgQ (fun j => elog (z l / r) ((j : ℂ) / r))]
    exact h
  · -- punctured hypothesis
    intro b hb
    have hq' := E.commonAgree b hb
    have hCm := E.commonMem b hb
    have har : E.nR b ∈ (G.geometry r).rows := by
      unfold Rect.Geometry.rows; exact Finset.mem_union_left _ hCm
    have hac : E.nR b ∈ (G.geometry r).cols := by
      unfold Rect.Geometry.cols; exact Finset.mem_union_left _ hCm
    have h := G.rs_hyp hr hBd0 hBc hBr hBq har hac
    rw [← hq']
    rw [sum_fin_eq E.nR E.injR _ E.imgR (fun j => elog ((E.nR b : ℂ) / r) ((j : ℂ) / r)),
      sum_fin_eq E.nQ E.injQ _ E.imgQ (fun j => elog ((E.nR b : ℂ) / r) ((j : ℂ) / r))]
    exact h
  · -- self-energy hypothesis
    have h := G.as_hyp hr hBd0 hBc hBr hBq
    have e1 : ∑ b : Fin N, ∑ b' : Fin N, elog ((E.nR b : ℂ) / r) ((E.nR b' : ℂ) / r) =
        ∑ a ∈ (G.geometry r).rows, ∑ b ∈ (G.geometry r).rows,
          elog ((a : ℂ) / r) ((b : ℂ) / r) := by
      have inner : ∀ b : Fin N, ∑ b' : Fin N, elog ((E.nR b : ℂ) / r) ((E.nR b' : ℂ) / r) =
          ∑ j ∈ (G.geometry r).rows, elog ((E.nR b : ℂ) / r) ((j : ℂ) / r) := fun b =>
        sum_fin_eq E.nR E.injR _ E.imgR (fun j => elog ((E.nR b : ℂ) / r) ((j : ℂ) / r))
      simp_rw [inner]
      exact sum_fin_eq E.nR E.injR _ E.imgR
        (fun a => ∑ j ∈ (G.geometry r).rows, elog ((a : ℂ) / r) ((j : ℂ) / r))
    have e2 : ∑ b : Fin N, ∑ b' : Fin N, elog ((E.nQ b : ℂ) / r) ((E.nQ b' : ℂ) / r) =
        ∑ a ∈ (G.geometry r).cols, ∑ b ∈ (G.geometry r).cols,
          elog ((a : ℂ) / r) ((b : ℂ) / r) := by
      have inner : ∀ b : Fin N, ∑ b' : Fin N, elog ((E.nQ b : ℂ) / r) ((E.nQ b' : ℂ) / r) =
          ∑ j ∈ (G.geometry r).cols, elog ((E.nQ b : ℂ) / r) ((j : ℂ) / r) := fun b =>
        sum_fin_eq E.nQ E.injQ _ E.imgQ (fun j => elog ((E.nQ b : ℂ) / r) ((j : ℂ) / r))
      simp_rw [inner]
      exact sum_fin_eq E.nQ E.injQ _ E.imgQ
        (fun a => ∑ j ∈ (G.geometry r).cols, elog ((a : ℂ) / r) ((j : ℂ) / r))
    rw [e1, e2]
    exact h

end BlockGeom
end CatalanCore.Uniform
