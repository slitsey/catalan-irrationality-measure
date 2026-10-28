module

public import CatalanCore.Uniform.Content.UFMember.Displace

@[expose] public section

/-!
# UF member package: (S7) on `J × J` from the one-node moments

`JBlockCauchy.of_moments`: if, for border rows `z ∈ Jr` and columns `y ∈ Jc` of one joint type,
the displacement numerator `α_z β'_y - β_z α'_y` of `sLift_displacement` is divisible by `p²`
with quotient `≡ det Q · m_z m'_y (h(y) - h(z))` modulo `p`, where
`h(t) = Σ_{c ∈ Ret} v(c)/(c - t)` (the derived frame of Theorem UF), and no weighted pole sits
at a node of `J`, then the `J`-block datum `JBlockCauchy` of the divided Schur complement holds
with retained set `Ret`.  Divisions use that `det Q`, `norm` and `y - z` are units modulo `p`.

So, for the sevenths Smith layer, the remaining frame computation is the expansion of the
one-node moments `α, β` of the `J` nodes to order `p²` (`(S6)` and the weights of `(S7)`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Rect CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.Hybrid

namespace CatalanCore.Uniform.Content.UFMember

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- The displacement numerator `α_z β'_y - β_z α'_y` of the scaled lift. -/
noncomputable def dispNum (A : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X]) (Fr : Frame) (c : ι → ℕ)
    (xs ys : κ → ℕ) (z y : κ) : (LocRing p)[X] :=
  (A.toBlocks₁₁.det - ∑ i, A.toBlocks₂₁ z i * ∑ k, A.toBlocks₁₁.adjugate i k) *
      (A.toBlocks₁₁.det * PF p Fr (ys y) -
        ∑ j, (∑ k, PF p Fr (c k) * A.toBlocks₁₁.adjugate k j) * A.toBlocks₁₂ j y) -
    (A.toBlocks₁₁.det * PF p Fr (xs z) -
        ∑ i, A.toBlocks₂₁ z i * ∑ k, A.toBlocks₁₁.adjugate i k * PF p Fr (c k)) *
      (A.toBlocks₁₁.det - ∑ j, (∑ k, A.toBlocks₁₁.adjugate k j) * A.toBlocks₁₂ j y)

/-- The derived-frame function `h(t) = Σ_{c ∈ Ret} v(c)/(c - t)`, with weights `v(c) ∈ 𝔽_p(U)`
(in the scaled gauge the weights `γ(c)` are rational functions of `U`). -/
noncomputable def hDer (Ret : Finset (ZMod p)) (v : ZMod p → RatFunc (ZMod p)) (t : ZMod p) :
    RatFunc (ZMod p) :=
  ∑ c ∈ Ret, v c * rfH p (c - t)⁻¹

/-- The Loewner difference of the derived frame is its Cauchy sum. -/
lemma hDer_sub (Ret : Finset (ZMod p)) (v : ZMod p → RatFunc (ZMod p)) {z y : ZMod p}
    (hz : ∀ c ∈ Ret, v c ≠ 0 → c ≠ z) (hy : ∀ c ∈ Ret, v c ≠ 0 → c ≠ y) :
    hDer Ret v y - hDer Ret v z =
      rfH p (y - z) * ∑ c ∈ Ret, v c * rfH p ((c - z)⁻¹ * (c - y)⁻¹) := by
  unfold hDer
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  by_cases hv : v c = 0
  · simp [hv]
  · have h1 : c - z ≠ 0 := sub_ne_zero.2 (hz c hc hv)
    have h2 : c - y ≠ 0 := sub_ne_zero.2 (hy c hc hv)
    have e : (c - y)⁻¹ - (c - z)⁻¹ = (y - z) * ((c - z)⁻¹ * (c - y)⁻¹) := by
      field_simp; ring
    rw [← mul_sub, ← map_sub, e, map_mul]
    ring

lemma phiP_natCast_sub (a b : ℕ) :
    phiP p (nd p a - nd p b) = rfH p ((a : ZMod p) - (b : ZMod p)) := by
  unfold nd
  rw [← C_sub, phiP_C, map_sub, map_natCast, map_natCast]
  rfl

lemma phiP_nL (D : PoleData Fr p N) : phiP p (nL p Fr) = rfH p (red p Fr.norm) := by
  unfold nL
  rw [phiP_C, redQ_apply, Hybrid.liftQ_val (show Fr.norm ∈ S p from D.norm_mem)]
  rfl

/-- **(S7) on `J × J` from the moments.** -/
noncomputable def JBlockCauchy.of_moments (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ)
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
    (hRc : ∀ y ∈ Jc, ∀ c' ∈ Ret, v c' ≠ 0 → c' ≠ ((ys y : ℕ) : ZMod p)) :
    JBlockCauchy (schurW c xs ys (hint_of_poleData D hN hc hx hy)) := by
  classical
  set hint := hint_of_poleData D hN hc hx hy
  set A := sLift c xs ys hint
  set π : (LocRing p)[X] := Polynomial.C ((p : ℕ) : LocRing p)
  have hπ : Prime π := Polynomial.prime_C_iff.2 (prime_p p)
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hg : phiP p A.toBlocks₁₁.det ≠ 0 := sLift_core_det c xs ys hint
  have hn : red p Fr.norm ≠ 0 := D.norm_ne
  have hSch := sLift_schur_eq c xs ys hint (hfib_of_poleData D hc hx hy) hdist
  have hrel : ∀ z ∈ Jr, ∀ y ∈ Jc, ∃ q : (LocRing p)[X],
      A.toBlocks₁₁.det * (nL p Fr * (nd p (ys y) - nd p (xs z))) *
          schurW c xs ys hint z y = π * q ∧
        phiP p q = phiP p A.toBlocks₁₁.det *
          (mR z * mC y * (hDer Ret v (ys y) - hDer Ret v (xs z))) := by
    intro z hz y hy'
    obtain ⟨q, hq1, hq2⟩ := hnum z hz y hy'
    refine ⟨q, ?_, hq2⟩
    have hd := sLift_displacement D hN c xs ys hc hx hy z y
    simp only at hd
    rw [hSch, Matrix.smul_apply, smul_eq_mul] at hd
    have e : A.toBlocks₁₁.det * (nL p Fr * (nd p (ys y) - nd p (xs z))) *
        (π * schurW c xs ys hint z y) = π * (π * q) := by
      rw [hd]
      unfold dispNum at hq1
      rw [hq1]; ring
    have e' : π * (A.toBlocks₁₁.det * (nL p Fr * (nd p (ys y) - nd p (xs z))) *
        schurW c xs ys hint z y) = π * (π * q) := by rw [← e]; ring
    exact mul_left_cancel₀ hπ0 e'
  have hunit : ∀ z y, ((xs z : ℕ) : ZMod p) ≠ ((ys y : ℕ) : ZMod p) →
      phiP p (A.toBlocks₁₁.det * (nL p Fr * (nd p (ys y) - nd p (xs z)))) ≠ 0 := by
    intro z y h
    rw [map_mul, map_mul, phiP_nL D, phiP_natCast_sub]
    refine mul_ne_zero hg (mul_ne_zero ?_ ?_)
    · exact fun h0 => hn (rfH_injective (by rw [h0, map_zero]))
    · exact fun h0 => (sub_ne_zero.2 (Ne.symm h)) (rfH_injective (by rw [h0, map_zero]))
  have hdvd : ∀ z ∈ Jr, ∀ y ∈ Jc, π ∣ schurW c xs ys hint z y := by
    intro z hz y hy'
    obtain ⟨q, hq1, -⟩ := hrel z hz y hy'
    have hnd : ¬ π ∣ A.toBlocks₁₁.det * (nL p Fr * (nd p (ys y) - nd p (xs z))) := by
      rw [← phiP_eq_zero_iff]; exact hunit z y (hdist z y)
    exact (hπ.dvd_or_dvd ⟨q, hq1⟩).resolve_left hnd
  let Hc : Matrix κ κ (LocRing p)[X] := Matrix.of fun z y => quotP p (schurW c xs ys hint z y)
  have hHc : ∀ z ∈ Jr, ∀ y ∈ Jc, schurW c xs ys hint z y = π * Hc z y := fun z hz y hy' =>
    (quotP_spec p (hdvd z hz y hy')).symm
  let nb : RatFunc (ZMod p) := rfH p (red p Fr.norm)
  have hnb : nb ≠ 0 := fun h0 => hn (rfH_injective (by rw [show rfH p _ = nb from rfl, h0,
    map_zero]))
  exact
  { Jr := Jr
    Jc := Jc
    Hc := Hc
    hJ := hHc
    Ret := Ret
    A := fun z c' => mR z / nb * rfH p (c' - ((xs z : ℕ) : ZMod p))⁻¹
    B := fun c' y => v c' * rfH p (c' - ((ys y : ℕ) : ZMod p))⁻¹ * mC y
    hcauchy := by
      intro z hz y hy'
      obtain ⟨q, hq1, hq2⟩ := hrel z hz y hy'
      rw [hHc z hz y hy'] at hq1
      have hq : A.toBlocks₁₁.det * (nL p Fr * (nd p (ys y) - nd p (xs z))) * Hc z y = q := by
        apply mul_left_cancel₀ hπ0
        rw [← hq1]; ring
      have hφ := congrArg (phiP p) hq
      rw [hq2, map_mul, map_mul, map_mul, phiP_nL D, phiP_natCast_sub] at hφ
      have hyz : ((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p) ≠ 0 :=
        sub_ne_zero.2 (Ne.symm (hdist z y))
      have h2 : rfH p (((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p)) ≠ 0 :=
        fun h0 => hyz (rfH_injective (by rw [h0, map_zero]))
      have hsub := hDer_sub Ret v (hRr z hz) (hRc y hy')
      -- cancel `det Q`
      have hφ2 : nb * rfH p (((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p)) * phiP p (Hc z y) =
          mR z * mC y * (rfH p (((ys y : ℕ) : ZMod p) - ((xs z : ℕ) : ZMod p)) *
            ∑ c' ∈ Ret, v c' * rfH p ((c' - ((xs z : ℕ) : ZMod p))⁻¹ *
              (c' - ((ys y : ℕ) : ZMod p))⁻¹)) := by
        rw [← hsub]
        apply mul_left_cancel₀ hg
        rw [← hφ]; ring
      have hφ3 : phiP p (Hc z y) = mR z / nb * mC y *
          ∑ c' ∈ Ret, v c' * rfH p ((c' - ((xs z : ℕ) : ZMod p))⁻¹ *
            (c' - ((ys y : ℕ) : ZMod p))⁻¹) := by
        apply mul_left_cancel₀ (mul_ne_zero hnb h2)
        rw [hφ2]
        field_simp
      rw [hφ3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [map_mul]
      ring }

end CatalanCore.Uniform.Content.UFMember
