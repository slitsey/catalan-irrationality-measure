module

public import CatalanCore.Decay.Lemma
public import CatalanCore.Decay.Rect.CertG

@[expose] public section

/-!
# Lemma B over an abstract `g` (WP-H2-core)

Verbatim generalisation of `Frame.ray_point_g` and `Frame.lemmaB` to `Cert.CertCoreG`
(the function `gfun ρ ε c m` is replaced by the field `F.g`).
-/

open Finset
open CatalanLambda.Decay (gfun Usig Utau Irho cexpr nodeC rmask rmask_cases sum_mask rayPt)

namespace CatalanCore
namespace Frame

open Decay

variable {Fr : Frame}

/-- Ray points, scaled by `1/h`, are of the form of the certified ray `-r0 + δ + u(-1 ± 3i)`. -/
theorem ray_point_gG {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : Cert.CertCoreG K ρ ε c m) (hxs : (0 : ℚ) < Fr.xs)
    {h : ℕ} (hh : 0 < h) {N0 : ℕ} (hN0 : N0 + Fr.n0off = ⌊(F.r0 : ℝ) * h⌋₊)
    (hW : (Fr.n0off : ℝ) + 1 + (Fr.xs : ℝ) ≤ (F.W : ℝ) * h) {θ : ℝ}
    (hθ : θ = phiR ∨ θ = -phiR) {r : ℝ} (hr : 0 < r) :
    (F.mprime : ℝ) ≤ F.g (rayPt (Fr.xstar N0) θ r / h) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hr0 : (0 : ℝ) < F.r0 := by exact_mod_cast F.r0_pos
  have hxs' : (0 : ℝ) < Fr.xs := by exact_mod_cast hxs
  have hn0 : (0 : ℝ) ≤ Fr.n0off := Nat.cast_nonneg _
  have hs10 : (0 : ℝ) < Real.sqrt 10 := by positivity
  have hN1 : ((N0 : ℝ) + Fr.n0off) ≤ F.r0 * h := by
    have := Nat.floor_le (show (0 : ℝ) ≤ F.r0 * h by positivity)
    rw [← hN0] at this
    push_cast at this
    exact this
  have hN2 : (F.r0 : ℝ) * h < (N0 : ℝ) + Fr.n0off + 1 := by
    have := Nat.lt_floor_add_one ((F.r0 : ℝ) * h)
    rw [← hN0] at this
    push_cast at this
    exact this
  set u : ℝ := r / (Real.sqrt 10 * h) with hu
  set δ : ℝ := F.r0 - ((N0 : ℝ) + Fr.xs) / h with hδ
  have hu0 : 0 ≤ u := by positivity
  have hδb : |δ| ≤ F.W := by
    have e : δ = ((F.r0 : ℝ) * h - N0 - Fr.xs) / h := by rw [hδ]; field_simp; ring
    rw [e, abs_div, abs_of_pos hh', div_le_iff₀ hh', abs_le]
    constructor <;> linarith
  have hz : rayPt (Fr.xstar N0) θ r / h = ⟨-(F.r0 : ℝ) + δ - u, (if θ = phiR then 3 else -3) * u⟩ := by
    apply Complex.ext
    · rw [Complex.div_natCast_re, CatalanLambda.Decay.rayPt_re]
      have hc : Real.cos θ = -(1 / Real.sqrt 10) := by
        rcases hθ with e | e
        · rw [e, cos_phiR]
        · rw [e, Real.cos_neg, cos_phiR]
      rw [hc]; unfold xstar; simp only [hδ, hu]; field_simp; ring
    · rw [Complex.div_natCast_im, CatalanLambda.Decay.rayPt_im]
      rcases hθ with e | e
      · rw [e, sin_phiR, if_pos rfl]; simp only [hu]; field_simp
      · have : θ ≠ phiR := by
          intro e2; rw [e] at e2
          have := phiR_gt; have := Real.pi_pos
          unfold phiR at e2
          have := Real.arctan_lt_pi_div_two 3
          have := Real.arctan_pos.2 (show (0:ℝ) < 3 by norm_num)
          linarith
        rw [e, Real.sin_neg, sin_phiR, if_neg (by rwa [← e])]; simp only [hu]; field_simp
  rw [hz]
  split_ifs with hp
  · exact F.ray_g_ge hu0 hδb
  · have := F.ray_g_ge' hu0 hδb
    simpa using this

/-- **Lemma B** (finite-cell version, general frame): for distinct free points, each an atom or a
ray point, `k m′ + h d Sbase - d Γ ≤ ∑_l g(z_l / h)`. -/
theorem lemmaBG {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (hFr : Fr.DecayOK) (F : Cert.CertCoreG K ρ ε c m)
    {h k : ℕ} (hh : 0 < h) {N0 : ℕ} (hN0 : N0 + Fr.n0off = ⌊(F.r0 : ℝ) * h⌋₊)
    (hW : (Fr.n0off : ℝ) + 1 + (Fr.xs : ℝ) ≤ (F.W : ℝ) * h) (z : Fin k → ℂ)
    (hzi : Function.Injective z)
    (hz : ∀ l, Fr.IsAtom N0 (z l) ∨ Fr.IsRay N0 (z l)) :
    (k : ℝ) * F.mprime + h * (Fr.d * F.Sbase)
        - Fr.d * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0
      ≤ ∑ l, F.g (z l / h) := by
  classical
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hr0 : (0 : ℝ) < F.r0 := by exact_mod_cast F.r0_pos
  have hxs : (0 : ℚ) < Fr.xs := hFr.contour.xs_pos
  have hN1 : ((N0 : ℝ) + Fr.n0off) ≤ F.r0 * h := by
    have := Nat.floor_le (show (0 : ℝ) ≤ F.r0 * h by positivity)
    rw [← hN0] at this
    push_cast at this
    exact this
  obtain ⟨i0, _⟩ := F.seg_cover 0 (by linarith) le_rfl
  have hcell : ∀ l : Fin k, ∃ i : Fin F.nSeg, Fr.IsAtom N0 (z l) →
      ((F.segA i : ℝ) ≤ (z l / h).re ∧ (z l / h).re ≤ F.segB i) := by
    intro l
    by_cases ha : Fr.IsAtom N0 (z l)
    · obtain ⟨h1, h2⟩ := atom_re_range hFr.atomRange hh ha
      have h3 : -(F.r0 : ℝ) ≤ (z l / h).re := by
        refine le_trans ?_ h1
        have hq : ((N0 : ℝ) + Fr.n0off) / h ≤ F.r0 := by
          rw [div_le_iff₀ hh']; linarith
        rw [neg_div]
        linarith
      obtain ⟨i, hi⟩ := F.seg_cover _ h3 h2
      exact ⟨i, fun _ => hi⟩
    · exact ⟨i0, fun h => absurd h ha⟩
  choose φ hφ using hcell
  set μ : Fin k → ℝ := fun l =>
    if Fr.IsAtom N0 (z l) then min ((F.segG (φ l) : ℝ) - F.mprime) 0 else 0 with hμ
  have hpt : ∀ l, (F.mprime : ℝ) + μ l ≤ F.g (z l / h) := by
    intro l
    by_cases ha : Fr.IsAtom N0 (z l)
    · have hs := F.seg_ok (φ l) _ (hφ l ha).1 (hφ l ha).2
      have e : (z l / h) = ⟨(z l / h).re, 0⟩ := Complex.ext rfl (atom_im ha)
      rw [e]
      simp only [hμ, if_pos ha]
      have := min_le_left ((F.segG (φ l) : ℝ) - F.mprime) 0
      rw [← e] at hs
      rw [e] at hs
      linarith
    · have hr : Fr.IsRay N0 (z l) := (hz l).resolve_left ha
      obtain ⟨r, hr0', θ, hθ, hzl⟩ := hr
      simp only [hμ, if_neg ha, add_zero]
      rw [hzl]
      exact ray_point_gG F hxs hh hN0 hW hθ hr0'
  have hsumpt : (k : ℝ) * F.mprime + ∑ l, μ l ≤ ∑ l, F.g (z l / h) := by
    have := Finset.sum_le_sum (s := univ) (fun l _ => hpt l)
    rw [Finset.sum_add_distrib] at this
    simpa using this
  set A : Finset (Fin k) := univ.filter (fun l => Fr.IsAtom N0 (z l)) with hA
  have hμA : ∑ l, μ l = ∑ l ∈ A, min ((F.segG (φ l) : ℝ) - F.mprime) 0 := by
    rw [hA, Finset.sum_filter]
  have hfib : ∑ l ∈ A, min ((F.segG (φ l) : ℝ) - F.mprime) 0
      = ∑ j, ((A.filter (fun l => φ l = j)).card : ℝ) * min ((F.segG j : ℝ) - F.mprime) 0 := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := A) (t := (univ : Finset (Fin F.nSeg))) (g := φ)
      (fun l _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => min ((F.segG j : ℝ) - F.mprime) 0)
      (fun l hl => by rw [(Finset.mem_filter.1 hl).2])]
    simp
  have hcard : ∀ j, ((A.filter (fun l => φ l = j)).card : ℝ)
      ≤ Fr.d * (h * ((F.segB j : ℝ) - F.segA j) + 1) := by
    intro j
    have hab : (F.segA j : ℝ) ≤ F.segB j := by exact_mod_cast F.seg_ab j
    refine le_trans ?_ (card_atomCell_le Fr h N0 hab hh)
    refine Nat.cast_le.2 (Finset.card_le_card_of_injOn z ?_ (hzi.injOn))
    intro l hl
    rw [Finset.mem_coe, Finset.mem_filter] at hl
    have ha : Fr.IsAtom N0 (z l) := (Finset.mem_filter.1 hl.1).2
    have := hφ l ha
    rw [hl.2] at this
    exact mem_atomCell hh ha this
  have hmin : ∀ j, ((F.segG j : ℝ) - F.mprime) ⊓ 0 ≤ 0 := fun j => min_le_right _ _
  have hlow : ∑ j, Fr.d * (h * ((F.segB j : ℝ) - F.segA j) + 1) * min ((F.segG j : ℝ) - F.mprime) 0
      ≤ ∑ j, ((A.filter (fun l => φ l = j)).card : ℝ) * min ((F.segG j : ℝ) - F.mprime) 0 :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonpos_right (hcard j) (hmin j))
  have hmax : ∀ j, min ((F.segG j : ℝ) - F.mprime) 0 = -max ((F.mprime : ℝ) - F.segG j) 0 := by
    intro j
    rcases le_total ((F.segG j : ℝ) - F.mprime) 0 with h1 | h1
    · rw [min_eq_left h1, max_eq_left (by linarith)]; ring
    · rw [min_eq_right h1, max_eq_right (by linarith)]; ring
  have hexp : ∑ j, Fr.d * (h * ((F.segB j : ℝ) - F.segA j) + 1) * min ((F.segG j : ℝ) - F.mprime) 0
      = h * (Fr.d * ∑ j, ((F.segB j : ℝ) - F.segA j) * min ((F.segG j : ℝ) - F.mprime) 0)
        - Fr.d * ∑ j, max ((F.mprime : ℝ) - F.segG j) 0 := by
    have hj : ∀ j, Fr.d * (h * ((F.segB j : ℝ) - F.segA j) + 1) * min ((F.segG j : ℝ) - F.mprime) 0
        = h * (Fr.d * (((F.segB j : ℝ) - F.segA j) * min ((F.segG j : ℝ) - F.mprime) 0))
          - Fr.d * max ((F.mprime : ℝ) - F.segG j) 0 := by
      intro j; rw [hmax j]; ring
    rw [Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_sub_distrib]
    simp only [← Finset.mul_sum]
  have hS : (h : ℝ) * (Fr.d * F.Sbase) ≤ h * (Fr.d * ∑ j, ((F.segB j : ℝ) - F.segA j) * min ((F.segG j : ℝ) - F.mprime) 0) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left F.Sbase_le (Nat.cast_nonneg _)) hh'.le
  rw [hμA, hfib] at hsumpt
  linarith


end Frame
end CatalanCore
