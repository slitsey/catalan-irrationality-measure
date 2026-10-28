module

public import CatalanCore.Uniform.Content.UFMember.Moments
public import CatalanCore.Uniform.Content.UFMember.JKill

@[expose] public section

/-!
# UF member package: wedge kills from the one-node moments

`W_reduction`: for distinct residues, `W_{zy} mod p = (dispNum_{zy}/p mod p)/(det Q · norm · (y-z))`.
Hence an outside border column `t` whose displacement numerator against the `J` rows is
`p · g · m_z κ_t` (`κ_t` = its wedge with `J`) has `W_{·t}|_{Jr} = (κ_t) · A_{·, t̄}`, and kills the
residue `t̄` when `κ_t ≠ 0`; symmetrically for outside rows (`κ'_t`, where the residue must carry a
nonzero weight).  `JBlockKill.of_moments` assembles `JBlockCauchy.of_moments` with these kills.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Rect CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMember

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- **First-order value of `W` from the displacement numerator.** -/
theorem W_reduction (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ)
    (xs ys : κ → ℕ) (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p)) (z y : κ)
    (q : (LocRing p)[X])
    (hq : dispNum (sLift c xs ys (hint_of_poleData D hN hc hx hy)) Fr c xs ys z y =
      Polynomial.C ((p : ℕ) : LocRing p) * q) :
    phiP p (schurW c xs ys (hint_of_poleData D hN hc hx hy) z y) *
        (phiP p (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁.det *
          rfH p (red p Fr.norm * (((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p)))) =
      phiP p q := by
  set hint := hint_of_poleData D hN hc hx hy
  set A := sLift c xs ys hint
  have hπ0 : (Polynomial.C ((p : ℕ) : LocRing p) : (LocRing p)[X]) ≠ 0 :=
    (Polynomial.prime_C_iff.2 (prime_p p)).ne_zero
  have hSch := sLift_schur_eq c xs ys hint (hfib_of_poleData D hc hx hy) hdist
  have hd := sLift_displacement D hN c xs ys hc hx hy z y
  simp only at hd
  rw [hSch, Matrix.smul_apply, smul_eq_mul] at hd
  have e : Polynomial.C ((p : ℕ) : LocRing p) * (A.toBlocks₁₁.det *
      (nL p Fr * (nd p (ys y) - nd p (xs z))) * schurW c xs ys hint z y) =
      Polynomial.C ((p : ℕ) : LocRing p) * q := by
    rw [← hq]; unfold dispNum; rw [← hd]; ring
  have e2 := congrArg (phiP p) (mul_left_cancel₀ hπ0 e)
  rw [map_mul, map_mul, map_mul, phiP_nL D, phiP_natCast_sub] at e2
  rw [← e2, map_mul]
  ring

/-- **The `J`-block with wedge kills, from the moments** (weights and wedges in `𝔽_p(U)`). -/
noncomputable def JBlockKill.of_moments (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ)
    (xs ys : κ → ℕ) (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)
    (hdist : ∀ i j, ((xs i : ℕ) : ZMod p) ≠ ((ys j : ℕ) : ZMod p))
    (Jr Jc : Finset κ) (Ret : Finset (ZMod p)) (v : ZMod p → RatFunc (ZMod p))
    (mR mC : κ → RatFunc (ZMod p))
    (hnum : ∀ z ∈ Jr, ∀ y ∈ Jc, ∃ q : (LocRing p)[X],
      dispNum (sLift c xs ys (hint_of_poleData D hN hc hx hy)) Fr c xs ys z y =
        Polynomial.C ((p : ℕ) : LocRing p) ^ 2 * q ∧
      phiP p q = phiP p (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁.det *
        (mR z * mC y * (hDer Ret v (ys y) - hDer Ret v (xs z))))
    (hRr : ∀ z ∈ Jr, ∀ c' ∈ Ret, v c' ≠ 0 → c' ≠ ((xs z : ℕ) : ZMod p))
    (hRc : ∀ y ∈ Jc, ∀ c' ∈ Ret, v c' ≠ 0 → c' ≠ ((ys y : ℕ) : ZMod p))
    (TC : Finset κ) (wC : κ → RatFunc (ZMod p)) (hwC : ∀ t ∈ TC, wC t ≠ 0)
    (hTC : ∀ t ∈ TC, ∀ z ∈ Jr, ∃ q : (LocRing p)[X],
      dispNum (sLift c xs ys (hint_of_poleData D hN hc hx hy)) Fr c xs ys z t =
        Polynomial.C ((p : ℕ) : LocRing p) * q ∧
      phiP p q = phiP p (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁.det *
        (mR z * wC t))
    (TR : Finset κ) (wR : κ → RatFunc (ZMod p)) (hwR : ∀ t ∈ TR, wR t ≠ 0)
    (hvR : ∀ t ∈ TR, v ((xs t : ℕ) : ZMod p) ≠ 0)
    (hTR : ∀ t ∈ TR, ∀ y ∈ Jc, ∃ q : (LocRing p)[X],
      dispNum (sLift c xs ys (hint_of_poleData D hN hc hx hy)) Fr c xs ys t y =
        Polynomial.C ((p : ℕ) : LocRing p) * q ∧
      phiP p q = phiP p (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁.det *
        (wR t * mC y)) :
    JBlockKill (schurW c xs ys (hint_of_poleData D hN hc hx hy)) := by
  classical
  have hg := sLift_core_det c xs ys (hint_of_poleData D hN hc hx hy)
  have hn : red p Fr.norm ≠ 0 := D.norm_ne
  have hrfH : ∀ u : ZMod p, u ≠ 0 → rfH p u ≠ 0 := fun u hu h0 =>
    hu (rfH_injective (by rw [h0, map_zero]))
  have hnb := hrfH _ hn
  exact
  { toJBlockCauchy := JBlockCauchy.of_moments D hN c xs ys hc hx hy hdist Jr Jc Ret v mR mC
      hnum hRr hRc
    KillR := TC.image fun t => ((ys t : ℕ) : ZMod p)
    KillC := TR.image fun t => ((xs t : ℕ) : ZMod p)
    hKR := by
      intro c' hc'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hc'
      refine ⟨t, wC t, hwC t ht, fun z hz => ?_⟩
      obtain ⟨q, hq1, hq2⟩ := hTC t ht z hz
      have h := W_reduction D hN c xs ys hc hx hy hdist z t q hq1
      rw [hq2] at h
      have hyz : ((ys t : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p) ≠ 0 :=
        sub_ne_zero.2 (Ne.symm (hdist z t))
      have h2 := hrfH _ hyz
      have hden : phiP p (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁.det *
          rfH p (red p Fr.norm * (((ys t : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p))) ≠ 0 :=
        mul_ne_zero hg (hrfH _ (mul_ne_zero hn hyz))
      show _ = wC t * (mR z / rfH p (red p Fr.norm) *
        rfH p (((ys t : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p))⁻¹)
      apply mul_right_cancel₀ hden
      rw [h, map_mul, map_inv₀]
      field_simp
    hKC := by
      intro c' hc'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hc'
      have hv := hvR t ht
      refine ⟨t, -(wR t) / (rfH p (red p Fr.norm) * v ((xs t : ℕ) : ZMod p)),
        div_ne_zero (neg_ne_zero.2 (hwR t ht)) (mul_ne_zero hnb hv), fun y hy' => ?_⟩
      obtain ⟨q, hq1, hq2⟩ := hTR t ht y hy'
      have h := W_reduction D hN c xs ys hc hx hy hdist t y q hq1
      rw [hq2] at h
      have hyz : ((ys y : ℕ) : ZMod p) - ((xs t : ℕ) : ZMod p) ≠ 0 :=
        sub_ne_zero.2 (Ne.symm (hdist t y))
      have hzy : ((xs t : ℕ) : ZMod p) - ((ys y : ℕ) : ZMod p) ≠ 0 :=
        sub_ne_zero.2 (hdist t y)
      have h3 := hrfH _ hzy
      have hden : phiP p (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁.det *
          rfH p (red p Fr.norm * (((ys y : ℕ) : ZMod p) - ((xs t : ℕ) : ZMod p))) ≠ 0 :=
        mul_ne_zero hg (hrfH _ (mul_ne_zero hn hyz))
      show _ = -(wR t) / (rfH p (red p Fr.norm) * v ((xs t : ℕ) : ZMod p)) *
        (v ((xs t : ℕ) : ZMod p) * rfH p (((xs t : ℕ) : ZMod p) - ((ys y : ℕ) : ZMod p))⁻¹ * mC y)
      apply mul_right_cancel₀ hden
      have e : ((ys y : ℕ) : ZMod p) - ((xs t : ℕ) : ZMod p) =
          -(((xs t : ℕ) : ZMod p) - ((ys y : ℕ) : ZMod p)) := by ring
      rw [h, e, map_mul, map_neg, map_inv₀]
      field_simp }

/-- The empty `J`-block (no joint type): the border-level Smith witness. -/
noncomputable def JBlockKill.empty (W : Matrix κ κ (LocRing p)[X]) : JBlockKill W where
  Jr := ∅
  Jc := ∅
  Hc := 0
  hJ := by simp
  Ret := ∅
  A := 0
  B := 0
  hcauchy := by simp
  KillR := ∅
  KillC := ∅
  hKR := by simp
  hKC := by simp

/-- **Sanity instance.**  With the empty `J`-block the Smith datum is discharged by frame data
alone (pole data, node bounds, distinct border residues), at price `2|C| + m`. -/
theorem SmithJKDatum.price_empty {G : BlockGeom} {r : ℕ} (S : SmithJKDatum G Fr r p)
    (hJ : S.J.Jr = ∅ ∧ S.J.Jc = ∅) :
    S.price = 2 * Fintype.card (G.geometry r).C + (G.geometry r).k := by
  unfold SmithJKDatum.price
  rw [hJ.1, hJ.2]
  simp only [Finset.card_empty, Fintype.card_sum, Fintype.card_fin]
  omega

end CatalanCore.Uniform.Content.UFMember
