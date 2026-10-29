module

public import CatalanCore.Uniform.Content.UFSimple.Lead
public import CatalanCore.Uniform.Content.UFSimple.Sep
public import CatalanCore.Uniform.Content.UFWedge.Cell

@[expose] public section

/-!
# UF simplification (H18): certificate-free kills

`wedgeC_ne_of_V`, `wedgeR_ne_of_V`: for ANY pole data and any lift, a border column (row) whose
border prefix residue `V` differs from that of the representative `t₀` has a nonzero kill wedge.
This is lemma W0 (`Lead`) composed with H9's reduction `wedgeC/R_ne_zero_of_cross`.

`altWedgeC_ne_of_sing`, `altWedgeR_ne_of_sing`: in the alternating geometry of a two-term frame,
a border node separated from `t₀` by a singular index (`Sep`, lemma S) is killed.  These are the
`hwC`/`hwR` fields of `UFCellF` and `Cell3` with no data at all.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.UFFamily
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform CatalanCore.Uniform.Content.Shape
  CatalanCore.Uniform.Content.UFWire

namespace CatalanCore.Uniform.Content.UFSimple

section General

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]
variable (D : PoleData Fr p N) (hN : N < p * p) (c : ι → ℕ) (xs ys : κ → ℕ)
  (hc : ∀ a, c a < N) (hx : ∀ i, xs i < N) (hy : ∀ j, ys j < N)

theorem coreShape_sLift :
    CoreShape (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
      (fun a b => Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn (c a) (c b))) :=
  sLift_core_entry D hN c xs ys hc hx hy


theorem redQ_PF1 {a : ℕ} (ha : a < N) :
    redQ p (Hybrid.liftQ p ((p : ℚ) * Fp Fr a)) = D.V a :=
  redQ_liftQ (good_PF1 D ha)

/-- The phiP cross wedge of two fibers is nonzero when the border prefixes differ. -/
theorem cross_phiP_ne_of_V (t0 t : ℕ) (ht0 : t0 < N) (ht : t < N) (hV : D.V t0 ≠ D.V t) :
    (fibOf (phiP p) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
        (loewRow p Fr c t0) (PF1 p Fr t0) ((t0 : ℕ) : ZMod p)).cross
      (fibOf (phiP p) Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
        (loewRow p Fr c t) (PF1 p Fr t) ((t : ℕ) : ZMod p)) ≠ 0 := by
  set Q := (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁
  intro h0
  have e1 : (fibOf (phiP p) Fr c Q (loewRow p Fr c t0) (PF1 p Fr t0) ((t0 : ℕ) : ZMod p)) =
      (fibOf (psiP p) Fr c Q (loewRow p Fr c t0) (PF1 p Fr t0) ((t0 : ℕ) : ZMod p)).map
        (algebraMap (ZMod p)[X] (RatFunc (ZMod p))) := rfl
  have e2 : (fibOf (phiP p) Fr c Q (loewRow p Fr c t) (PF1 p Fr t) ((t : ℕ) : ZMod p)) =
      (fibOf (psiP p) Fr c Q (loewRow p Fr c t) (PF1 p Fr t) ((t : ℕ) : ZMod p)).map
        (algebraMap (ZMod p)[X] (RatFunc (ZMod p))) := rfl
  rw [e1, e2, ← FibD.map_cross] at h0
  have hp : (fibOf (psiP p) Fr c Q (loewRow p Fr c t0) (PF1 p Fr t0) ((t0 : ℕ) : ZMod p)).cross
      (fibOf (psiP p) Fr c Q (loewRow p Fr c t) (PF1 p Fr t) ((t : ℕ) : ZMod p)) = 0 :=
    (RatFunc.algebraMap_injective (ZMod p)) (by rw [h0, map_zero])
  have hz : redQ p (Hybrid.liftQ p ((p : ℚ) * Fp Fr t0)) ≠
      redQ p (Hybrid.liftQ p ((p : ℚ) * Fp Fr t)) := by
    rw [redQ_PF1 D ht0, redQ_PF1 D ht]; exact hV
  exact cross_psiP_ne Q _ (coreShape_sLift D hN c xs ys hc hx hy) c
    (fun a => Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn t0 (c a)))
    (fun a => Hybrid.liftQ p ((p : ℚ) ^ 2 * Fr.Mn t (c a)))
    (Hybrid.liftQ p ((p : ℚ) * Fp Fr t0)) (Hybrid.liftQ p ((p : ℚ) * Fp Fr t)) _ _ hz hp

/-- **Column kill from distinct border prefixes** (no certificate). -/
theorem wedgeC_ne_of_V (t0 : ℕ) (ht0 : t0 < N) (t : κ) (hV : D.V t0 ≠ D.V (ys t)) :
    wedgeC (sLift c xs ys (hint_of_poleData D hN hc hx hy)) Fr c ys
      (dirOf Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ t0
        (loewRow p Fr c t0)) t ≠ 0 := by
  refine wedgeC_ne_zero_of_cross D hN c xs ys hc hx hy t0 ht0 t ?_
  rw [sLift_col_eq_loew D hN c xs ys hc hx hy t]
  exact cross_phiP_ne_of_V D hN c xs ys hc hx hy t0 (ys t) ht0 (hy t) hV

/-- **Row kill from distinct border prefixes** (no certificate). -/
theorem wedgeR_ne_of_V (t0 : ℕ) (ht0 : t0 < N) (t : κ) (hV : D.V t0 ≠ D.V (xs t)) :
    wedgeR (sLift c xs ys (hint_of_poleData D hN hc hx hy)) Fr c xs
      (dirOf Fr c (sLift c xs ys (hint_of_poleData D hN hc hx hy)).toBlocks₁₁ t0
        (loewRow p Fr c t0)) t ≠ 0 := by
  refine wedgeR_ne_zero_of_cross D hN c xs ys hc hx hy t0 ht0 t ?_
  rw [sLift_row_eq_loew D hN c xs ys hc hx hy t]
  exact cross_phiP_ne_of_V D hN c xs ys hc hx hy t0 (xs t) ht0 (hx t) hV

end General

section Alt

variable {c : ℚ} {hc : 0 < c} {Fr : Frame} {q o p N : ℕ} [Fact p.Prime]

/-- Two nodes of a short window separated by a singular index have distinct prefixes (either
order). -/
theorem V_ne_of_sep (T : TwoTermData Fr q o) (hqp : q < p) (hN : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) {t0 v : ℕ} (ht0 : t0 < N) (hv : v < N)
    (hsep : (t0 < v ∧ v < t0 + p ∧ ∃ k, t0 < k ∧ k ≤ v ∧ (p ∣ k ∨ p ∣ q * k - o)) ∨
      (v < t0 ∧ t0 < v + p ∧ ∃ k, v < k ∧ k ≤ t0 ∧ (p ∣ k ∨ p ∣ q * k - o))) :
    (twoTermPoleData T hN hsq hnorm hnorm0).V t0 ≠ (twoTermPoleData T hN hsq hnorm hnorm0).V v := by
  rcases hsep with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact V_ne_of_sing T hqp hN hsq hnorm hnorm0 h1 hv h2 h3
  · exact (V_ne_of_sing T hqp hN hsq hnorm hnorm0 h1 ht0 h2 h3).symm

set_option maxHeartbeats 1600000 in
/-- **Alternating geometry: column kill from a separating singular index.** -/
theorem altWedgeC_ne_of_sep {r : ℕ} (hr : r % 2 = 0) (T : TwoTermData Fr q o) (hqp : q < p)
    (hNp : N < p * p) (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N) (t0 : ℕ)
    (ht0 : t0 < N) (t : Fin ((altGeom c hc).geometry r).k)
    (hsep : (t0 < ((altGeom c hc).geometry r).ys t ∧ ((altGeom c hc).geometry r).ys t < t0 + p ∧
        ∃ k, t0 < k ∧ k ≤ ((altGeom c hc).geometry r).ys t ∧ (p ∣ k ∨ p ∣ q * k - o)) ∨
      (((altGeom c hc).geometry r).ys t < t0 ∧ t0 < ((altGeom c hc).geometry r).ys t + p ∧
        ∃ k, ((altGeom c hc).geometry r).ys t < k ∧ k ≤ t0 ∧ (p ∣ k ∨ p ∣ q * k - o))) :
    wedgeC (altLift c hc hr T hNp hsq hnorm hnorm0 hrN) Fr
      (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).ys
      (dirOf Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        (altLift c hc hr T hNp hsq hnorm hnorm0 hrN).toBlocks₁₁ t0
        (loewRow p Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0)) t ≠ 0 :=
  wedgeC_ne_of_V (twoTermPoleData T hNp.le hsq hnorm hnorm0) hNp _ _ _
    (alt_hc' c hc hrN) (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN) t0 ht0 t
    (V_ne_of_sep T hqp hNp.le hsq hnorm hnorm0 ht0 (alt_hy' c hc hr hrN t) hsep)

set_option maxHeartbeats 1600000 in
/-- **Alternating geometry: row kill from a separating singular index.** -/
theorem altWedgeR_ne_of_sep {r : ℕ} (hr : r % 2 = 0) (T : TwoTermData Fr q o) (hqp : q < p)
    (hNp : N < p * p) (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N) (t0 : ℕ)
    (ht0 : t0 < N) (t : Fin ((altGeom c hc).geometry r).k)
    (hsep : (t0 < ((altGeom c hc).geometry r).xs t ∧ ((altGeom c hc).geometry r).xs t < t0 + p ∧
        ∃ k, t0 < k ∧ k ≤ ((altGeom c hc).geometry r).xs t ∧ (p ∣ k ∨ p ∣ q * k - o)) ∨
      (((altGeom c hc).geometry r).xs t < t0 ∧ t0 < ((altGeom c hc).geometry r).xs t + p ∧
        ∃ k, ((altGeom c hc).geometry r).xs t < k ∧ k ≤ t0 ∧ (p ∣ k ∨ p ∣ q * k - o))) :
    wedgeR (altLift c hc hr T hNp hsq hnorm hnorm0 hrN) Fr
      (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) ((altGeom c hc).geometry r).xs
      (dirOf Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        (altLift c hc hr T hNp hsq hnorm hnorm0 hrN).toBlocks₁₁ t0
        (loewRow p Fr (fun a : ((altGeom c hc).geometry r).C => (a : ℕ)) t0)) t ≠ 0 :=
  wedgeR_ne_of_V (twoTermPoleData T hNp.le hsq hnorm hnorm0) hNp _ _ _
    (alt_hc' c hc hrN) (alt_hx' c hc hr hrN) (alt_hy' c hc hr hrN) t0 ht0 t
    (V_ne_of_sep T hqp hNp.le hsq hnorm hnorm0 ht0 (alt_hx' c hc hr hrN t) hsep)

end Alt

end CatalanCore.Uniform.Content.UFSimple
