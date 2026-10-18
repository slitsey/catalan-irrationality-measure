import CatalanLambda.Decay.ThmNCert
import CatalanLambda.Decay.RayDirection

/-!
# Theorem N_ρ: Lemma B_ρ (finite-cell version)
-/

open Finset

namespace CatalanLambda.Decay

/-- Ray points, scaled by `1/h`, are of the form of the certified ray `-r0 + δ + u(-1 ± 3i)`. -/
theorem ray_point_g {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ} (F : CertFacts K ρ ε c m)
    {h : ℕ} (hh : 0 < h) (hW : 5 / (8 * (F.W : ℝ)) ≤ h) {θ : ℝ} (hθ : θ = phiR ∨ θ = -phiR)
    {r : ℝ} (hr : 0 < r) :
    (F.mprime : ℝ) ≤ gfun ρ ε c m (rayPt (xstar ⌊(F.r0 : ℝ) * h⌋₊) θ r / h) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hr0 : (0 : ℝ) < F.r0 := by exact_mod_cast F.r0_pos
  have hW0 : (0 : ℝ) < F.W := by exact_mod_cast F.W_pos
  set N0 := ⌊(F.r0 : ℝ) * h⌋₊ with hN0
  have hN1 : (N0 : ℝ) ≤ F.r0 * h := Nat.floor_le (by positivity)
  have hN2 : (F.r0 : ℝ) * h < N0 + 1 := Nat.lt_floor_add_one _
  have hs10 : (0 : ℝ) < Real.sqrt 10 := by positivity
  set u : ℝ := r / (Real.sqrt 10 * h) with hu
  set δ : ℝ := F.r0 - ((N0 : ℝ) + 3 / 8) / h with hδ
  have hu0 : 0 ≤ u := by positivity
  have hδb : |δ| ≤ F.W := by
    have e : δ = ((F.r0 : ℝ) * h - N0 - 3 / 8) / h := by rw [hδ]; field_simp; ring
    rw [e, abs_div, abs_of_pos hh', div_le_iff₀ hh', abs_le]
    constructor <;> nlinarith [mul_div_cancel₀ (5 / 8 : ℝ) hh'.ne', div_mul_cancel₀ (5 / 8 : ℝ) (show (F.W : ℝ) ≠ 0 from hW0.ne'),
      (div_le_iff₀ (show (0:ℝ) < 8 * F.W by positivity)).1 hW]
  have hz : rayPt (xstar N0) θ r / h = ⟨-(F.r0 : ℝ) + δ - u, (if θ = phiR then 3 else -3) * u⟩ := by
    apply Complex.ext
    · rw [Complex.div_natCast_re, rayPt_re]
      have hc : Real.cos θ = -(1 / Real.sqrt 10) := by
        rcases hθ with e | e
        · rw [e, cos_phiR]
        · rw [e, Real.cos_neg, cos_phiR]
      rw [hc]; unfold xstar; simp only [hδ, hu]; field_simp; ring
    · rw [Complex.div_natCast_im, rayPt_im]
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

/-- The atom positions `-(n + 3/4)` and `-(n + 1)`. -/
noncomputable def atomPos1 (n : ℕ) : ℂ := ((-((n : ℝ) + 3 / 4) : ℝ) : ℂ)

noncomputable def atomPos2 (n : ℕ) : ℂ := ((-((n : ℝ) + 1) : ℝ) : ℂ)

/-- `w` is one of the `2 N0` atom positions. -/
def IsAtom (N0 : ℕ) (w : ℂ) : Prop := (∃ n < N0, w = atomPos1 n) ∨ (∃ n < N0, w = atomPos2 n)

lemma atomPos1_inj : Function.Injective atomPos1 := by
  intro a b h
  simp only [atomPos1, Complex.ofReal_inj] at h
  exact_mod_cast (by linarith : (a : ℝ) = b)

lemma atomPos2_inj : Function.Injective atomPos2 := by
  intro a b h
  simp only [atomPos2, Complex.ofReal_inj] at h
  exact_mod_cast (by linarith : (a : ℝ) = b)

lemma card_nat_Icc_le (M : ℕ) (x y : ℝ) (hxy : x ≤ y) :
    (((range M).filter fun n : ℕ => x ≤ n ∧ (n : ℝ) ≤ y).card : ℝ) ≤ y - x + 1 := by
  rcases lt_or_ge y 0 with hy | hy
  · have : (range M).filter (fun n : ℕ => x ≤ n ∧ (n : ℝ) ≤ y) = ∅ := by
      apply Finset.filter_false_of_mem
      intro n _ hn
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith [hn.2]
    rw [this]; simp; linarith
  · have hsub : (range M).filter (fun n : ℕ => x ≤ n ∧ (n : ℝ) ≤ y) ⊆ Finset.Icc ⌈x⌉₊ ⌊y⌋₊ := by
      intro n hn
      rw [Finset.mem_filter] at hn
      rw [Finset.mem_Icc]
      exact ⟨Nat.ceil_le.2 hn.2.1, Nat.le_floor hn.2.2⟩
    have h1 := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h1
    have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy
    have hce : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    by_cases hc : ⌈x⌉₊ ≤ ⌊y⌋₊ + 1
    · have : (((range M).filter fun n : ℕ => x ≤ n ∧ (n : ℝ) ≤ y).card : ℝ)
          ≤ ((⌊y⌋₊ + 1 - ⌈x⌉₊ : ℕ) : ℝ) := by exact_mod_cast h1
      rw [Nat.cast_sub hc] at this
      push_cast at this
      linarith
    · have h0 : ⌊y⌋₊ + 1 - ⌈x⌉₊ = 0 := by omega
      rw [h0] at h1
      have : ((range M).filter fun n : ℕ => x ≤ n ∧ (n : ℝ) ≤ y).card = 0 := by omega
      rw [this]; simp; linarith

/-- Atom positions lying in the scaled cell `[a, b]`. -/
noncomputable def atomCell (h N0 : ℕ) (a b : ℝ) : Finset ℂ :=
  ((range N0).filter (fun n : ℕ => -(h : ℝ) * b - 3 / 4 ≤ n ∧ (n : ℝ) ≤ -(h : ℝ) * a - 3 / 4)).image atomPos1
  ∪ ((range N0).filter (fun n : ℕ => -(h : ℝ) * b - 1 ≤ n ∧ (n : ℝ) ≤ -(h : ℝ) * a - 1)).image atomPos2

lemma card_atomCell_le (h N0 : ℕ) {a b : ℝ} (hab : a ≤ b) (hh : 0 < h) :
    ((atomCell h N0 a b).card : ℝ) ≤ 2 * (h * (b - a) + 1) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  unfold atomCell
  refine (Nat.cast_le.2 (Finset.card_union_le _ _)).trans ?_
  push_cast
  have c1 := card_nat_Icc_le N0 (-(h : ℝ) * b - 3 / 4) (-(h : ℝ) * a - 3 / 4)
    (by nlinarith)
  have c2 := card_nat_Icc_le N0 (-(h : ℝ) * b - 1) (-(h : ℝ) * a - 1) (by nlinarith)
  have i1 := (Nat.cast_le (α := ℝ)).2 (Finset.card_image_le (s := (range N0).filter
    (fun n : ℕ => -(h : ℝ) * b - 3 / 4 ≤ n ∧ (n : ℝ) ≤ -(h : ℝ) * a - 3 / 4)) (f := atomPos1))
  have i2 := (Nat.cast_le (α := ℝ)).2 (Finset.card_image_le (s := (range N0).filter
    (fun n : ℕ => -(h : ℝ) * b - 1 ≤ n ∧ (n : ℝ) ≤ -(h : ℝ) * a - 1)) (f := atomPos2))
  nlinarith

lemma mem_atomCell {h N0 : ℕ} (hh : 0 < h) {a b : ℝ} {w : ℂ} (hw : IsAtom N0 w)
    (hx : a ≤ (w / h).re ∧ (w / h).re ≤ b) : w ∈ atomCell h N0 a b := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  unfold atomCell
  rw [Finset.mem_union]
  rcases hw with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · left
    rw [Finset.mem_image]
    refine ⟨n, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.2 hn, ?_⟩
    simp only [atomPos1, Complex.div_natCast_re, Complex.ofReal_re] at hx
    obtain ⟨h1, h2⟩ := hx
    rw [le_div_iff₀ hh'] at h1
    rw [div_le_iff₀ hh'] at h2
    constructor <;> nlinarith
  · right
    rw [Finset.mem_image]
    refine ⟨n, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.2 hn, ?_⟩
    simp only [atomPos2, Complex.div_natCast_re, Complex.ofReal_re] at hx
    obtain ⟨h1, h2⟩ := hx
    rw [le_div_iff₀ hh'] at h1
    rw [div_le_iff₀ hh'] at h2
    constructor <;> nlinarith

lemma atom_re_range {h N0 : ℕ} (hh : 0 < h) {w : ℂ} (hw : IsAtom N0 w) :
    -(N0 : ℝ) / h ≤ (w / h).re ∧ (w / h).re ≤ 0 := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  rcases hw with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩
  · simp only [atomPos1, Complex.div_natCast_re, Complex.ofReal_re]
    have : (n : ℝ) + 1 ≤ N0 := by exact_mod_cast hn
    constructor
    · exact div_le_div_of_nonneg_right (by linarith) hh'.le
    · exact div_nonpos_of_nonpos_of_nonneg (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) hh'.le
  · simp only [atomPos2, Complex.div_natCast_re, Complex.ofReal_re]
    have : (n : ℝ) + 1 ≤ N0 := by exact_mod_cast hn
    constructor
    · exact div_le_div_of_nonneg_right (by linarith) hh'.le
    · exact div_nonpos_of_nonpos_of_nonneg (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) hh'.le

lemma atom_im {h N0 : ℕ} {w : ℂ} (hw : IsAtom N0 w) : (w / h).im = 0 := by
  rcases hw with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩ <;> simp [atomPos1, atomPos2, Complex.div_natCast_im]

/-- `w` is a point of one of the two certified rays. -/
def IsRay (N0 : ℕ) (w : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ θ : ℝ, (θ = phiR ∨ θ = -phiR) ∧ w = rayPt (xstar N0) θ r

/-- **Lemma B_ρ (finite-cell version).**  For `h ≥ 5/(8W)`, `N0 = ⌊r0 h⌋`, and any family of
distinct free points, each an atom or a point of a ray,
`k m′ + h S_cert - 2 ∑_ℓ (m′ - γ_ℓ)⁺ ≤ ∑_l g(z_l / h)`. -/
theorem lemmaB {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ} (F : CertFacts K ρ ε c m)
    {h k : ℕ} (hh : 0 < h) (hW : 5 / (8 * (F.W : ℝ)) ≤ h) (z : Fin k → ℂ)
    (hzi : Function.Injective z)
    (hz : ∀ l, IsAtom ⌊(F.r0 : ℝ) * h⌋₊ (z l) ∨ IsRay ⌊(F.r0 : ℝ) * h⌋₊ (z l)) :
    (k : ℝ) * F.mprime + h * F.Scert - 2 * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0
      ≤ ∑ l, gfun ρ ε c m (z l / h) := by
  classical
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hr0 : (0 : ℝ) < F.r0 := by exact_mod_cast F.r0_pos
  set N0 := ⌊(F.r0 : ℝ) * h⌋₊ with hN0
  have hN1 : (N0 : ℝ) ≤ F.r0 * h := Nat.floor_le (by positivity)
  obtain ⟨i0, _⟩ := F.seg_cover 0 (by linarith) le_rfl
  have hcell : ∀ l : Fin k, ∃ i : Fin F.nSeg, IsAtom N0 (z l) →
      ((F.segA i : ℝ) ≤ (z l / h).re ∧ (z l / h).re ≤ F.segB i) := by
    intro l
    by_cases ha : IsAtom N0 (z l)
    · obtain ⟨h1, h2⟩ := atom_re_range hh ha
      have h3 : -(F.r0 : ℝ) ≤ (z l / h).re := by
        refine le_trans ?_ h1
        rw [neg_div, neg_le_neg_iff, div_le_iff₀ hh']; exact hN1
      obtain ⟨i, hi⟩ := F.seg_cover _ h3 h2
      exact ⟨i, fun _ => hi⟩
    · exact ⟨i0, fun h => absurd h ha⟩
  choose φ hφ using hcell
  set μ : Fin k → ℝ := fun l =>
    if IsAtom N0 (z l) then min ((F.segG (φ l) : ℝ) - F.mprime) 0 else 0 with hμ
  have hpt : ∀ l, (F.mprime : ℝ) + μ l ≤ gfun ρ ε c m (z l / h) := by
    intro l
    by_cases ha : IsAtom N0 (z l)
    · have hs := F.seg_ok (φ l) _ (hφ l ha).1 (hφ l ha).2
      have e : (z l / h) = ⟨(z l / h).re, 0⟩ := Complex.ext rfl (atom_im ha)
      rw [e]
      simp only [hμ, if_pos ha]
      have := min_le_left ((F.segG (φ l) : ℝ) - F.mprime) 0
      rw [← e] at hs
      rw [e] at hs
      linarith
    · have hr : IsRay N0 (z l) := (hz l).resolve_left ha
      obtain ⟨r, hr0', θ, hθ, hzl⟩ := hr
      simp only [hμ, if_neg ha, add_zero]
      rw [hzl]
      exact ray_point_g F hh hW hθ hr0'
  have hsumpt : (k : ℝ) * F.mprime + ∑ l, μ l ≤ ∑ l, gfun ρ ε c m (z l / h) := by
    have := Finset.sum_le_sum (s := univ) (fun l _ => hpt l)
    rw [Finset.sum_add_distrib] at this
    simpa using this
  -- the cell counting
  set A : Finset (Fin k) := univ.filter (fun l => IsAtom N0 (z l)) with hA
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
      ≤ 2 * (h * ((F.segB j : ℝ) - F.segA j) + 1) := by
    intro j
    have hab : (F.segA j : ℝ) ≤ F.segB j := by exact_mod_cast F.seg_ab j
    refine le_trans ?_ (card_atomCell_le h N0 hab hh)
    refine Nat.cast_le.2 (Finset.card_le_card_of_injOn z ?_ (hzi.injOn))
    intro l hl
    rw [Finset.mem_coe, Finset.mem_filter] at hl
    have ha : IsAtom N0 (z l) := (Finset.mem_filter.1 hl.1).2
    have := hφ l ha
    rw [hl.2] at this
    exact mem_atomCell hh ha this
  have hmin : ∀ j, ((F.segG j : ℝ) - F.mprime) ⊓ 0 ≤ 0 := fun j => min_le_right _ _
  have hlow : ∑ j, 2 * (h * ((F.segB j : ℝ) - F.segA j) + 1) * min ((F.segG j : ℝ) - F.mprime) 0
      ≤ ∑ j, ((A.filter (fun l => φ l = j)).card : ℝ) * min ((F.segG j : ℝ) - F.mprime) 0 :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonpos_right (hcard j) (hmin j))
  have hmax : ∀ j, min ((F.segG j : ℝ) - F.mprime) 0 = -max ((F.mprime : ℝ) - F.segG j) 0 := by
    intro j
    rcases le_total ((F.segG j : ℝ) - F.mprime) 0 with h1 | h1
    · rw [min_eq_left h1, max_eq_left (by linarith)]; ring
    · rw [min_eq_right h1, max_eq_right (by linarith)]; ring
  have hexp : ∑ j, 2 * (h * ((F.segB j : ℝ) - F.segA j) + 1) * min ((F.segG j : ℝ) - F.mprime) 0
      = h * (2 * ∑ j, ((F.segB j : ℝ) - F.segA j) * min ((F.segG j : ℝ) - F.mprime) 0)
        - 2 * ∑ j, max ((F.mprime : ℝ) - F.segG j) 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hmax j]; ring
  have hS : (h : ℝ) * F.Scert ≤ h * (2 * ∑ j, ((F.segB j : ℝ) - F.segA j) * min ((F.segG j : ℝ) - F.mprime) 0) :=
    mul_le_mul_of_nonneg_left F.Scert_le hh'.le
  rw [hμA, hfib] at hsumpt
  linarith

end CatalanLambda.Decay
