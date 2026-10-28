module

public import CatalanCore.Uniform.Decay.PolyChain.Points
public import CatalanCore.Uniform.Decay.PolyChain.EnergyD
public import CatalanCore.Uniform.Decay.Cert.AllMinor

@[expose] public section

/-!
# Glue over a polygon: energy estimate to `HasAllMinorDecay` (lane D, package D7)

Polygon analogue of D5's `Cert.hasAllMinorDecay_of_certG`.  At scale `r ≥ Rmin`, head
`N0 = N0Of Fr P.r0 r`, the physical polygon `r Γ + h_r` carries D5a's `polygonRep_scaled`
source representation; then

* the contour premises of D3's energy step come from `poly_dist` (distance `≥ min m0 1` from
  `[0,∞)`), `poly_norm` (`‖z‖ ≤ a0 r + 2|Im z|`, `a0 = r0 + vRat + xs + 1`) and the
  polygon Lemma B (`lemmaBG_gen` + `poly_atom_or_ge`, tube field of `CertCoreP`);
* `BlockGeom.energy_geom_small_d` gives `PolyEnergy` with `Cl = log (amp (CP Fr q))`;
* `theoremN_poly` (chain length `r · L_Γ`) and `N_log_le` absorb `N log M0` into `δ r²`.

Frame hypotheses: `ContourOK`, the head-range test `hAR`, `norm ≥ 1` (no slope hypothesis).
-/

namespace CatalanCore.Uniform.Decay.PolyChain

open Finset Matrix CatalanCore CatalanCore.Uniform CatalanLambda.Decay Rect
  CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Assembly CatalanCore.Uniform.Decay.Cert

set_option maxHeartbeats 8000000 in
/-- **Polygon energy estimate gives `HasAllMinorDecay`.**  Nonnegative weights. -/
theorem hasAllMinorDecay_of_certG_poly (G : BlockGeom) {Fr : Frame} (hC : Fr.ContourOK)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    (hnorm1 : (1 : ℚ) ≤ Fr.norm) {P : RatPolygon} (hP : P.OK)
    {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    (F : CertCoreP P K ρ ε c wt) (hw0 : ∀ k, 0 ≤ wt k) {Rc : ℝ}
    (hc : ∀ k, ‖c k‖ ≤ Rc)
    (hg : ∀ s : ℂ, F.g s = (G.totalMass : ℝ) * Usig ρ c wt s - G.nodePot s +
      (1 - ε) * Real.pi * |s.im|)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < ε) {ℓ cB : ℝ}
    (hℓ : ∀ (r a : ℕ), a ∈ (G.geometry r).C → ℓ ≤ F.g ((a : ℂ) / (r : ℂ)))
    (hcB : 2 * ((F.mprime : ℝ) - ℓ) ≤ cB) :
    NodeFamily.HasAllMinorDecay G.geometry Fr
      (2 * (G.totalMass : ℝ) * F.mprime + 2 * ((Fr.d : ℝ) * F.Sbase)
        - (G.totalMass : ℝ) ^ 2 * F.Ibound + G.nodeEnergy) cB := by
  classical
  intro δ hδ
  have hM := G.totalMass_nonneg'
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
  have hr0 : (0 : ℝ) < P.r0 := by exact_mod_cast hP.r0_pos
  have hW0 : (0 : ℝ) < F.W := by exact_mod_cast F.W_pos
  have he1 : e < 1 := lt_trans heε F.hε1
  have hv0 : (0 : ℝ) ≤ P.vRat := by exact_mod_cast P.vRat_nonneg
  have hn0 : (0 : ℝ) ≤ Fr.n0off := Nat.cast_nonneg _
  set Cq : ℝ := CP Fr (P.qRat : ℝ) with hCq
  set a0 : ℝ := P.r0 + P.vRat + Fr.xs + Fr.n0off + 1 with ha0
  have ha1 : 1 ≤ a0 := by rw [ha0]; linarith
  set m1 : ℝ := min m0 1 with hm1d
  have hm1 : 0 < m1 := lt_min hm0 one_pos
  obtain ⟨R0, hR0⟩ := G.energy_geom_small_d (K := K) (ρ := ρ) (ε := ε) (c := c) (wt := wt) F.hρ hw0
    F.hm hc F.g hg hBd0 hBc hBr hBq hm1 ha1 (mp := (F.mprime : ℝ)) (Ibd := (F.Ibound : ℝ))
    (Scap := (Fr.d : ℝ) * F.Sbase)
    (Cdef := (Fr.d : ℝ) * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0)
    F.hε0 he0 heε (log_amp_nonneg Cq) F.I_ok hcB (half_pos hδ)
  have hW1 := Fr.Wabs_nonneg
  have hAp := amp_pos Cq
  have hd := RatPolygon.tailDir_im_pos hP
  set L0 : ℝ := chainLen 0 (P.verts.map P.off) with hL0d
  have hL00 : 0 ≤ L0 := chainLen_nonneg _ _
  set Dd : ℝ := ‖P.tailDir‖ / ((2 * Real.pi * e) * P.tailDir.im) with hDd
  have hDd0 : 0 ≤ Dd := by
    have : 0 < (2 * Real.pi * e) * P.tailDir.im := by have := Real.pi_pos; positivity
    positivity
  have hAe : 0 ≤ amp Cq ^ e := by positivity
  set A : ℝ := Fr.Wabs * P.r0 + 2 * (amp Cq ^ e * L0) with hA
  have hA0 : 0 ≤ A := by positivity
  set c1 : ℝ := Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ + 2 * (amp Cq ^ e * Dd) + 1 with hc1
  have hc1' : 1 ≤ c1 := by
    have : 0 ≤ Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ := by positivity
    have : 0 ≤ amp Cq ^ e * Dd := by positivity
    rw [hc1]; linarith
  set Kc : ℝ := ((G.totalMass : ℝ) + G.rowConst) * (1 + |Real.log (A + c1)|) with hKc
  have hKc0 : 0 ≤ Kc := by
    have : (0 : ℝ) ≤ G.rowConst := Nat.cast_nonneg _
    rw [hKc]; positivity
  obtain ⟨R2, hR2⟩ := eventually_rlog_le hKc0 (half_pos hδ)
  obtain ⟨R3, hR3⟩ : ∃ R3 : ℕ, ∀ r : ℕ, R3 ≤ r →
      Rmin Fr P ≤ (r : ℝ) ∧ 1 + (Fr.n0off : ℝ) + Fr.xs ≤ F.W * r := by
    refine ⟨⌈Rmin Fr P + (1 + (Fr.n0off : ℝ) + Fr.xs) / F.W⌉₊, fun r hr => ?_⟩
    have hX : Rmin Fr P + (1 + (Fr.n0off : ℝ) + Fr.xs) / F.W ≤ r :=
      (Nat.le_ceil _).trans (by exact_mod_cast hr)
    have hR1 : (1 : ℝ) ≤ Rmin Fr P := le_max_left _ _
    have h2 : 0 ≤ (1 + (Fr.n0off : ℝ) + Fr.xs) / F.W := by positivity
    refine ⟨by linarith, ?_⟩
    have : (1 + (Fr.n0off : ℝ) + Fr.xs) / F.W ≤ r := by linarith
    rwa [div_le_iff₀ hW0, mul_comm] at this
  obtain ⟨R4, hR4⟩ : ∃ R4 : ℕ, ∀ r : ℕ, R4 ≤ r → 0 < (G.geometry r).C.card := by
    have hpos : (0 : ℝ) < (G.common.mass : ℝ) := by exact_mod_cast G.common_pos
    refine ⟨⌈(G.common.n : ℝ) / G.common.mass⌉₊ + 1, fun r hr => ?_⟩
    have hX : (G.common.n : ℝ) / G.common.mass < r := by
      have := Nat.le_ceil ((G.common.n : ℝ) / G.common.mass)
      have h2 : ((⌈(G.common.n : ℝ) / G.common.mass⌉₊ + 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast hr
      push_cast at h2
      linarith
    have h3 : (G.common.n : ℝ) < G.common.mass * r := by
      rwa [div_lt_iff₀ hpos, mul_comm] at hX
    have h4 := (G.card_common r).1
    have h5 : (G.common.n : ℚ) < G.common.mass * r := by exact_mod_cast h3
    have h6 : (0 : ℚ) < ((G.geometry r).C.card : ℚ) := by linarith
    exact_mod_cast h6
  refine ⟨max (max R0 R2) (max R3 R4), fun r hr S => ?_⟩
  have hrR0 : R0 ≤ r := (le_max_left _ _).trans ((le_max_left _ _).trans hr)
  have hrR2 : R2 ≤ r := (le_max_right _ _).trans ((le_max_left _ _).trans hr)
  have hrR3 : R3 ≤ r := (le_max_left _ _).trans ((le_max_right _ _).trans hr)
  have hrR4 : R4 ≤ r := (le_max_right _ _).trans ((le_max_right _ _).trans hr)
  obtain ⟨hRmin, hWr⟩ := hR3 r hrR3
  have hCpos := hR4 r hrR4
  have hr1 : (1 : ℝ) ≤ r := (le_max_left _ _).trans hRmin
  have hrpos : 0 < r := by exact_mod_cast (lt_of_lt_of_le one_pos hr1)
  have hrposR : (0 : ℝ) < r := by linarith
  obtain ⟨hS, hH⟩ := polygonRep_scaled hC hP hRmin
  -- the head
  have hq : (|(P.qRat : ℝ)| + 2 + Fr.n0off) / (P.r0 : ℝ) ≤ r :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hRmin
  have hfl := floor_ge (Fr := Fr) hP hq
  have hn : Fr.n0off ≤ ⌊(P.r0 : ℝ) * r⌋₊ := by
    have : (Fr.n0off : ℝ) ≤ (⌊(P.r0 : ℝ) * r⌋₊ : ℝ) := by
      have : 0 ≤ |(P.qRat : ℝ)| := abs_nonneg _
      linarith
    exact_mod_cast this
  set N0 : ℕ := N0Of Fr P.r0 r with hN0d
  have hN1 : (N0 : ℝ) + Fr.n0off ≤ P.r0 * r := by
    rw [hN0d, N0Of_cast hn]
    have := Nat.floor_le (show (0 : ℝ) ≤ P.r0 * r by positivity)
    linarith
  have hH' : |hShift Fr P.r0 r| ≤ (F.W : ℝ) * r := by linarith
  have hmk : (G.geometry r).k = (G.geometry r).X'.card := rfl
  set k := S.card + (G.geometry r).k with hk
  let eq : (S ⊕ Fin (G.geometry r).k) ≃ Fin k := Fintype.equivFinOfCardEq (by simp [k])
  let s : Fin k → Fin ((G.geometry r).C.card + (G.geometry r).X'.card) := fun i => sIdx G r S (eq.symm i)
  have hrow : ∀ p, (G.nodeEnum r).nR (sIdx G r S p) =
      Sum.elim (fun a : S => ((a.1 : (G.geometry r).C) : ℕ)) (G.geometry r).xs p := by
    rintro (a | j)
    · exact nR_sIdx_inl a
    · exact nR_sIdx_inr j
  have hcol : ∀ p, (G.nodeEnum r).nQ (sIdx G r S p) =
      Sum.elim (fun a : S => ((a.1 : (G.geometry r).C) : ℕ)) (G.geometry r).ys p := by
    rintro (a | j)
    · exact nQ_sIdx_inl a
    · exact nQ_sIdx_inr j
  have hRinj : Function.Injective (fun i => (G.nodeEnum r).nR (s i)) := by
    intro a b h
    have h' : (G.nodeEnum r).nR (sIdx G r S (eq.symm a)) = (G.nodeEnum r).nR (sIdx G r S (eq.symm b)) := h
    rw [hrow, hrow] at h'
    exact eq.symm.injective (rowN_inj S h')
  have hQinj : Function.Injective (fun i => (G.nodeEnum r).nQ (s i)) := by
    intro a b h
    have h' : (G.nodeEnum r).nQ (sIdx G r S (eq.symm a)) = (G.nodeEnum r).nQ (sIdx G r S (eq.symm b)) := h
    rw [hcol, hcol] at h'
    exact eq.symm.injective (colN_inj S h')
  have hs : Function.Injective s := fun a b h => hRinj (by simp only [h])
  have hkeep : ∀ b : Fin ((G.geometry r).C.card + (G.geometry r).X'.card), (G.geometry r).C.card ≤ (b : ℕ) → ∃ i, s i = b := by
    intro b hb
    refine ⟨eq (Sum.inr ⟨(b : ℕ) - (G.geometry r).C.card, by have := b.isLt; omega⟩), ?_⟩
    show sIdx G r S (eq.symm (eq (Sum.inr _))) = b
    rw [Equiv.symm_apply_apply]
    exact Fin.ext (by show (G.geometry r).C.card + ((b : ℕ) - (G.geometry r).C.card) = b.val; omega)
  have hkN : k ≤ (G.geometry r).C.card + (G.geometry r).X'.card := by
    have : S.card ≤ (G.geometry r).C.card := by simpa using Finset.card_le_univ S
    simp only [hk]; omega
  have hcommon : ∀ b : Fin ((G.geometry r).C.card + (G.geometry r).X'.card), (b : ℕ) < (G.geometry r).C.card →
      ℓ ≤ F.g (((G.nodeEnum r).nR b : ℂ) / r) := fun b hb => hℓ r _ ((G.nodeEnum r).commonMem b hb)
  have hRE : PolyEnergy Fr N0 (physL Fr P r) P.tailDir k e (Real.log (amp Cq))
      (-((r : ℝ) ^ 2 * (2 * (G.totalMass : ℝ) * F.mprime + 2 * ((Fr.d : ℝ) * F.Sbase)
        - (G.totalMass : ℝ) ^ 2 * F.Ibound + G.nodeEnergy - δ / 2))
      + cB * r * ((((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℝ) - k))
      (fun i => (G.nodeEnum r).nR (s i)) (fun i => (G.nodeEnum r).nQ (s i)) := by
    intro x hxi hz q hq
    choose y hy using hz
    have hdist : ∀ l (t : ℝ), 0 ≤ t → m1 ≤ ‖x l - (t : ℂ)‖ := by
      intro l t ht
      rw [← hy l]; exact poly_dist hS hm0μ (y l) ht
    have hV : |Fr.xstar N0| + r * (P.vRat : ℝ) ≤ a0 * r := by
      have := growth_const_le hC hP hRmin
      rw [ha0]; nlinarith
    have hBN : (N0 : ℝ) + Fr.n0off ≤ a0 * r := by
      rw [ha0]; nlinarith
    have hnorm : ∀ l, ‖x l‖ ≤ a0 * r + 2 * |(x l).im| := by
      intro l
      rw [← hy l]; exact poly_norm hS hAR hBN hV (y l)
    have hcap := lemmaBG_gen hAR F hrpos hN1 x hxi
      (fun l => by rw [← hy l]; exact poly_atom_or_ge F hrpos hH' (y l))
    exact hR0 (r := r) (N := (G.geometry r).C.card + (G.geometry r).X'.card) (nc := (G.geometry r).C.card) hrR0
      (by omega) (G.nodeEnum r) x hxi hdist hnorm s hs hkeep q hq hcap hcommon
  have hLc : chainLen ((Fr.xstar N0 : ℝ) : ℂ) (physL Fr P r) ≤ r * L0 := by
    have e1 : physL Fr P r = P.physPts (Fr.xstar N0) r := (physPts_eq_scaled P Fr r).symm
    rw [e1, RatPolygon.chainLen_physPts P _ hrposR.le]
  have hdetN := theoremN_poly hnorm1 hS hd he0 he1 hLc
    (Nn := (G.geometry r).C.card + (G.geometry r).X'.card) hkN
    (R := (P.r0 : ℝ) * r) (by linarith) hRinj hQinj hRE
  have hfull : (FullN Fr (fun a : S => ((a.1 : (G.geometry r).C) : ℕ)) (G.geometry r).xs (G.geometry r).ys (Fr.const : ℝ)).det =
      (Matrix.of fun i j : Fin k => Fr.Tent ((G.nodeEnum r).nR (s i)) ((G.nodeEnum r).nQ (s j))).det := by
    have hxm : ∀ i, (G.geometry r).xs i ∈ (G.geometry r).X' := fun i => Finset.orderEmbOfFin_mem _ _ i
    have hym : ∀ j, (G.geometry r).ys j ∈ (G.geometry r).Y' := fun j => Finset.orderEmbOfFin_mem _ _ j
    rw [fullN_eq_tent Fr _ _ _ (fun a b h => Subtype.ext (Subtype.ext h))
      (fun a j h => Finset.disjoint_left.mp (G.geometry r).disjCY a.1.2
        (by have := hym j; rwa [← h] at this))
      (fun i b h => Finset.disjoint_left.mp (G.geometry r).disjCX b.1.2
        (by have := hxm i; rwa [h] at this))
      (fun i j h => Finset.disjoint_left.mp (G.geometry r).disjXY (hxm i)
        (by have := hym j; rwa [← h] at this))]
    rw [← Matrix.det_submatrix_equiv_self eq]
    congr 1
    ext p q
    simp only [Matrix.submatrix_apply, Matrix.of_apply, s, Equiv.symm_apply_apply, hrow, hcol]
  rw [hfull]
  refine hdetN.trans (Real.exp_le_exp.2 ?_)
  have hNrows : ((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) = (G.geometry r).rows.card := by
    rw [← G.rows_card_eq_N (G.nodeEnum r)]
  have hNle : (((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℝ) ≤ (G.totalMass : ℝ) * r + G.rowConst := by
    have := (abs_le.1 (G.card_rows_bound r)).2
    rw [hNrows]; linarith
  have habs := N_log_le (Nn := (((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℝ)) (Mm := (G.totalMass : ℝ))
    (rc := G.rowConst) (A := A) (B := c1) (r := r) (Nat.cast_nonneg _) hM
    (Nat.cast_nonneg _) hA0 hc1' hr1 hNle
  have hR2r := hR2 r hrR2
  have hsub : ((((G.geometry r).C.card - S.card : ℕ)) : ℝ) = ((G.geometry r).C.card : ℝ) - S.card := by
    have : S.card ≤ (G.geometry r).C.card := by simpa using Finset.card_le_univ S
    exact Nat.cast_sub this
  have hNk : ((((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℝ)) - k = ((G.geometry r).C.card : ℝ) - S.card := by
    simp only [hk]; push_cast; rw [show (((G.geometry r).k : ℕ) : ℝ) = (G.geometry r).X'.card by exact_mod_cast hmk]; ring
  have hM0 : Fr.Wabs * ((P.r0 : ℝ) * r) + (Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊
      + 2 * (amp Cq ^ e * (r * L0 + ‖P.tailDir‖ / ((2 * Real.pi * e) * P.tailDir.im))) + 1)
      = A * r + c1 := by
    rw [hA, hc1, hDd]; ring
  rw [hM0]
  have hmain : (((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℝ) * Real.log (A * r + c1) ≤
      δ / 2 * (r : ℝ) ^ 2 := habs.trans hR2r
  rw [hsub, hNk]
  nlinarith [hmain]

end CatalanCore.Uniform.Decay.PolyChain
