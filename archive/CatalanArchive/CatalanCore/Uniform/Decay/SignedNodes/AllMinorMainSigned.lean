module

public import CatalanCore.Uniform.Decay.Cert.AllMinorMain
public import CatalanCore.Uniform.Decay.SignedNodes.EnergySmallSigned

@[expose] public section

/-!
# `HasAllMinorDecay` from the signed block energy step (lane D, package D8)

`hasAllMinorDecay_of_certG_signed`: `Cert.hasAllMinorDecay_of_certG` with the nonnegativity of
the trial weights replaced by `∑ |wt| ≤ V`, using `BlockGeom.energy_geom_small_signed`.
-/

namespace CatalanCore.Uniform.Decay.Cert

open Finset Matrix CatalanCore CatalanCore.Uniform CatalanLambda.Decay Rect

set_option maxHeartbeats 8000000 in
/-- **D3 energy estimate gives `HasAllMinorDecay`, signed weights** (`∑ |wt| ≤ V`; `V = 1` is the
positive case).  Same exponent `D_0` and window `c_B`: the signed loss only affects the threshold. -/
theorem hasAllMinorDecay_of_certG_signed (G : BlockGeom) {sl : ℝ} {Fr : Frame} (hFr : Fr.DecayOKs' sl)
    {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {wt : Fin K → ℝ}
    (F : Cert.CertCoreGs sl K ρ ε c wt) {V : ℝ} (hV : ∑ k, |wt k| ≤ V) {Rc : ℝ}
    (hc : ∀ k, ‖c k‖ ≤ Rc)
    (hg : ∀ s : ℂ, F.g s = (G.totalMass : ℝ) * Usig ρ c wt s - G.nodePot s +
      (1 - ε) * Real.pi * |s.im|)
    {Bd : ℝ} (hBd0 : 0 ≤ Bd) (hBc : ∀ i, ((G.common.block i).v : ℝ) ≤ Bd)
    (hBr : ∀ i, ((G.row.block i).v : ℝ) ≤ Bd) (hBq : ∀ i, ((G.column.block i).v : ℝ) ≤ Bd)
    {m0 : ℝ} (hm0 : 0 < m0) (hm0xs : m0 ≤ Fr.xs) (hm0μ : ∀ i, m0 ≤ Fr.μ i)
    {e : ℝ} (he0 : 0 < e) (heε : e < ε) {ℓ cB : ℝ}
    (hℓ : ∀ (r a : ℕ), a ∈ (G.geometry r).C → ℓ ≤ F.g ((a : ℂ) / (r : ℂ)))
    (hcB : 2 * ((F.mprime : ℝ) - ℓ) ≤ cB) :
    NodeFamily.HasAllMinorDecay G.geometry Fr
      (2 * (G.totalMass : ℝ) * F.mprime + 2 * ((Fr.d : ℝ) * F.Sbase)
        - (G.totalMass : ℝ) ^ 2 * F.Ibound + G.nodeEnergy) cB := by
  classical
  intro δ hδ
  have hC := hFr.contour
  have hM := G.totalMass_nonneg'
  have hxs : (0 : ℝ) < Fr.xs := by exact_mod_cast hC.xs_pos
  have hr0 : (0 : ℝ) < F.r0 := by exact_mod_cast F.r0_pos
  have hW0 : (0 : ℝ) < F.W := by exact_mod_cast F.W_pos
  have he1 : e < 1 := lt_trans heε F.hε1
  set a0 : ℝ := F.r0 + Fr.xs + 1 with ha0
  have ha1 : 1 ≤ a0 := by rw [ha0]; linarith
  obtain ⟨R0, hR0⟩ := G.energy_geom_small_signed (K := K) (ρ := ρ) (ε := ε) (c := c) (wt := wt) F.hρ hV
    F.hm hc F.g hg hBd0 hBc hBr hBq hm0 ha1 (mp := (F.mprime : ℝ)) (Ibd := (F.Ibound : ℝ))
    (Scap := (Fr.d : ℝ) * F.Sbase)
    (Cdef := (Fr.d : ℝ) * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0)
    F.hε0 he0 heε (le_max_right (Real.log Fr.Aco) 0) F.I_ok hcB (half_pos hδ)
  have hW1 := Fr.Wabs_nonneg
  have hAp := Frame.Aco_pos hC
  have hbe := Frame.betaE_pos hFr.slope.pos he0
  set c1 : ℝ := Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ + 2 * (Fr.Aco ^ e / Frame.betaE sl e) + 1 with hc1
  have hc1' : 1 ≤ c1 := by
    have : 0 ≤ Fr.Wabs * ⌈(Fr.xs : ℝ)⌉₊ := by positivity
    have : 0 ≤ Fr.Aco ^ e / Frame.betaE sl e := by positivity
    rw [hc1]; linarith
  set Kc : ℝ := ((G.totalMass : ℝ) + G.rowConst) *
    (1 + |Real.log (Fr.Wabs * F.r0 + c1)|) with hKc
  have hKc0 : 0 ≤ Kc := by
    have : (0 : ℝ) ≤ G.rowConst := Nat.cast_nonneg _
    rw [hKc]; positivity
  obtain ⟨R2, hR2⟩ := eventually_rlog_le hKc0 (half_pos hδ)
  obtain ⟨R3, hR3⟩ : ∃ R3 : ℕ, ∀ r : ℕ, R3 ≤ r →
      (1 : ℝ) ≤ r ∧ (Fr.n0off : ℝ) ≤ F.r0 * r ∧ (Fr.n0off : ℝ) + 1 + Fr.xs ≤ F.W * r := by
    refine ⟨⌈(Fr.n0off : ℝ) / F.r0 + ((Fr.n0off : ℝ) + 1 + Fr.xs) / F.W + 1⌉₊, fun r hr => ?_⟩
    have hX : (Fr.n0off : ℝ) / F.r0 + ((Fr.n0off : ℝ) + 1 + Fr.xs) / F.W + 1 ≤ r :=
      (Nat.le_ceil _).trans (by exact_mod_cast hr)
    have h1 : 0 ≤ (Fr.n0off : ℝ) / F.r0 := by positivity
    have h2 : 0 ≤ ((Fr.n0off : ℝ) + 1 + Fr.xs) / F.W := by positivity
    refine ⟨by linarith, ?_, ?_⟩
    · have : (Fr.n0off : ℝ) / F.r0 ≤ r := by linarith
      rwa [div_le_iff₀ hr0, mul_comm] at this
    · have : ((Fr.n0off : ℝ) + 1 + Fr.xs) / F.W ≤ r := by linarith
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
  obtain ⟨hr1, hfl, hWr⟩ := hR3 r hrR3
  have hCpos := hR4 r hrR4
  have hrpos : 0 < r := by exact_mod_cast (lt_of_lt_of_le one_pos hr1)
  have hflN : Fr.n0off ≤ ⌊(F.r0 : ℝ) * r⌋₊ := Nat.le_floor (by exact_mod_cast hfl)
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, N0 + Fr.n0off = ⌊(F.r0 : ℝ) * r⌋₊ := ⟨⌊(F.r0 : ℝ) * r⌋₊ - Fr.n0off, by omega⟩
  have hN0r : (N0 : ℝ) + Fr.n0off ≤ F.r0 * r := by
    have := Nat.floor_le (show (0 : ℝ) ≤ F.r0 * r by positivity)
    rw [← hN0] at this
    exact_mod_cast this
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
  have hRE : Frame.RectEnergy Fr sl N0 k e m0 (max (Real.log Fr.Aco) 0)
      (-((r : ℝ) ^ 2 * (2 * (G.totalMass : ℝ) * F.mprime + 2 * ((Fr.d : ℝ) * F.Sbase)
        - (G.totalMass : ℝ) ^ 2 * F.Ibound + G.nodeEnergy - δ / 2))
      + cB * r * ((((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℝ) - k))
      (fun i => (G.nodeEnum r).nR (s i)) (fun i => (G.nodeEnum r).nQ (s i)) := by
    intro x hxi hz hre q hq
    have hnorm : ∀ l, ‖x l‖ ≤ a0 * r + 2 * |(x l).im| := by
      intro l
      have h1 := Decay.free_norm_le hFr.slope.one_le hxs.le hFr.atomRange (T := F.r0 * r) hN0r (hz l)
      rw [ha0]
      nlinarith
    have hcap := Frame.lemmaBG hFr.toDecayOKs F hrpos hN0
      (by exact_mod_cast hWr) x hxi hz
    exact hR0 (r := r) (N := (G.geometry r).C.card + (G.geometry r).X'.card) (nc := (G.geometry r).C.card) hrR0
      (by omega) (G.nodeEnum r) x hxi hre hnorm s hs hkeep q hq hcap hcommon
  have hdetN := Frame.theoremN_rect hFr he0 he1 hm0xs hm0μ (Nn := (G.geometry r).C.card + (G.geometry r).X'.card) hkN
    (R := (F.r0 : ℝ) * r) (by linarith) hRinj hQinj hRE
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
    (rc := G.rowConst) (A := Fr.Wabs * F.r0) (B := c1) (r := r) (Nat.cast_nonneg _) hM
    (Nat.cast_nonneg _) (by positivity) hc1' hr1 hNle
  have hR2r := hR2 r hrR2
  have hsub : ((((G.geometry r).C.card - S.card : ℕ)) : ℝ) = ((G.geometry r).C.card : ℝ) - S.card := by
    have : S.card ≤ (G.geometry r).C.card := by simpa using Finset.card_le_univ S
    exact Nat.cast_sub this
  have hNk : ((((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℝ)) - k = ((G.geometry r).C.card : ℝ) - S.card := by
    simp only [hk]; push_cast; rw [show (((G.geometry r).k : ℕ) : ℝ) = (G.geometry r).X'.card by exact_mod_cast hmk]; ring
  have hM0 : Fr.Wabs * ((F.r0 : ℝ) * r) + c1 = (Fr.Wabs * F.r0) * r + c1 := by ring
  rw [hM0]
  have hmain : (((G.geometry r).C.card + (G.geometry r).X'.card : ℕ) : ℝ) * Real.log ((Fr.Wabs * F.r0) * r + c1) ≤
      δ / 2 * (r : ℝ) ^ 2 := habs.trans hR2r
  rw [hsub, hNk]
  nlinarith [hmain]

end CatalanCore.Uniform.Decay.Cert
