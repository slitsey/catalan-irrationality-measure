module

public import CatalanCore.Decay.Space
public import CatalanCore.Decay.Point
public import CatalanCore.Cert.Facts

@[expose] public section

/-!
# Lemma B and Lemma A for a general frame (WP2b)

Generalisation of the legacy `ThmNLemmaB` / `ThmNLemmaA` to a frame `Fr` with atom density
`d = Fr.d` (atoms per unit length: `d`), pole-distance parameter `m0`, and the certificate
`CertCore`.  Where the density enters (FK-P6-decay/result.md, FP-audit item 1):

* **Lemma B** : the number of atoms in a scaled cell `[a, b]` is `≤ d (h (b - a) + 1)`
  (`card_atomCell_le`), so `∑ g(z_l/h) ≥ k m′ + h · d · Sbase - d · Γ`, with
  `Γ = ∑ (m′ - segG)⁺`.
* **Rerr** : `Rerr h (d Γ) ρ Cl m0 = 2 h (dΓ) + h |log ρ| + 2h log h + 3h + 1/2 + 2h log(1 + h/m0) + h Cl`
  (legacy: `d = 2`, `m0 = 3/8`).
* **Lemma A** : `∑ log q + log ‖C(z,s)‖² ≤ -h² D + h(h-k) c + Rerr`, for `D ≤ 2(m′ + d Sbase) - I + 3/2`
  (`D ≤ CertCore.Dof d 0 (3/2)`).

Frame hypotheses (`DecayOK`): `ContourOK`; `δ0 ≥ 1/12` (so that the certified ray direction
`(-1, ±3)` satisfies the cotangent condition); and `atomRange`: every atom `m + μ_i` with its pole
east of `x*` satisfies `m + μ_i ≤ N0 + n0off`, i.e. lies in the segment window `[-r0 h, 0]`.
-/

open Finset
open CatalanLambda.Decay (gfun Usig Utau Irho cexpr nodeC rmask rmask_cases sum_mask rayPt)

namespace CatalanCore

namespace Frame

/-- The frame hypotheses of the generic decay argument. -/
structure DecayOK (Fr : Frame) : Prop where
  contour : Fr.ContourOK
  delta : (1 : ℚ) / 12 ≤ Fr.δ0
  atomRange : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off

/-- A positive lower bound for `xs` and all shifts `μ i` (the distance of the free points from the
nodes `0, 1, 2, …`). -/
theorem exists_m0 (Fr : Frame) (hxs : (0 : ℚ) < Fr.xs) :
    ∃ m0 : ℝ, 0 < m0 ∧ m0 ≤ Fr.xs ∧ ∀ i, m0 ≤ Fr.μ i := by
  by_cases hd : Nonempty (Fin Fr.d)
  · obtain ⟨i0, hi0⟩ := Finite.exists_min (fun i : Fin Fr.d => (Fr.μ i : ℝ))
    refine ⟨min (Fr.xs : ℝ) (Fr.μ i0), lt_min (by exact_mod_cast hxs) (Fr.mu_pos i0),
      min_le_left _ _, fun i => (min_le_right _ _).trans (hi0 i)⟩
  · exact ⟨Fr.xs, by exact_mod_cast hxs, le_rfl, fun i => absurd ⟨i⟩ hd⟩

variable {Fr : Frame}

/-- Atoms lie in the segment window. -/
lemma atom_le (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off) {N0 : ℕ}
    {p : ℕ × Fin Fr.d} (hp : p ∈ Fr.atomIdx N0) :
    (p.1 : ℝ) + (Fr.μ p.2 : ℝ) ≤ (N0 : ℝ) + (Fr.n0off : ℝ) := by
  classical
  unfold atomIdx at hp
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true, not_lt] at hp
  obtain ⟨_, h⟩ := hp
  have hq : (p.1 : ℚ) + Fr.μ p.2 ≤ N0 + Fr.xs := by exact_mod_cast h
  have hj : ((p.1 : ℤ) - (N0 : ℤ)) ≤ ⌊Fr.xs - Fr.μ p.2⌋ := by
    apply Int.le_floor.2
    push_cast
    linarith
  have hjq : (((p.1 : ℤ) - (N0 : ℤ) : ℤ) : ℚ) ≤ ((⌊Fr.xs - Fr.μ p.2⌋ : ℤ) : ℚ) := by exact_mod_cast hj
  push_cast at hjq
  have := hAR p.2
  have h2 : (p.1 : ℚ) + Fr.μ p.2 ≤ N0 + Fr.n0off := by linarith
  exact_mod_cast h2

/-- `w` is one of the atom positions. -/
def IsAtom (Fr : Frame) (N0 : ℕ) (w : ℂ) : Prop :=
  ∃ p ∈ Fr.atomIdx N0, w = ((Fr.atomPos p : ℝ) : ℂ)

/-- `w` is a point of one of the two certified rays. -/
def IsRay (Fr : Frame) (N0 : ℕ) (w : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ θ : ℝ, (θ = Decay.phiR ∨ θ = -Decay.phiR) ∧ w = rayPt (Fr.xstar N0) θ r

end Frame

namespace Decay

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

/-- The explicit error term `R(h)` of Lemma A (an `O(h log h)` quantity); `Γd = d · Γ`. -/
noncomputable def Rerr (h : ℕ) (Γd ρ Cl m0 : ℝ) : ℝ :=
  2 * h * Γd + h * |Real.log ρ| + 2 * h * Real.log h + 3 * h + 1 / 2
    + 2 * h * Real.log (1 + h / m0) + h * Cl

theorem arith_core (h k Cl ε SIm G Rm Γ Ib D Sc mp gm cc I lr Lh L1 Sq LC : ℝ)
    (hh : 0 < h) (hk0 : 0 ≤ k) (hkh : k ≤ h) (hCl : 0 ≤ Cl) (hε1 : ε < 1) (hε0 : 0 < ε)
    (hL1 : 0 ≤ L1) (hLh : 0 ≤ Lh)
    (hE : 2 * h * (G + Rm) - 2 * ((1 - ε) * SIm) - h ^ 2 * I + h * lr + 3 / 2 * h ^ 2
        - 2 * h * Lh - 3 * h - 1 / 2 - 2 * k * L1 + 2 * k * Lh ≤ -LC)
    (hfield : Sq ≤ (1 - ε) * (k * Cl) - 2 * ((1 - ε) * SIm))
    (hB : k * mp + h * Sc - 2 * Γ ≤ G) (hrem : (h - k) * gm ≤ Rm) (hI : I ≤ Ib)
    (hD : D ≤ 2 * (mp + Sc) - Ib + 3 / 2) (hc : 2 * (mp - gm) ≤ cc) :
    Sq + LC ≤ -h ^ 2 * D + h * (h - k) * cc
      + (4 * h * Γ + h * |lr| + 2 * h * Lh + 3 * h + 1 / 2 + 2 * h * L1 + h * Cl) := by
  have p1 := mul_le_mul_of_nonneg_left hB (show (0 : ℝ) ≤ 2 * h by positivity)
  have p2 := mul_le_mul_of_nonneg_left hrem (show (0 : ℝ) ≤ 2 * h by positivity)
  have p3 := mul_le_mul_of_nonneg_left hI (show (0 : ℝ) ≤ h ^ 2 by positivity)
  have p4 : 0 ≤ h * (h - k) * (cc - 2 * (mp - gm)) :=
    mul_nonneg (mul_nonneg hh.le (by linarith)) (by linarith)
  have p5 := mul_le_mul_of_nonneg_left hD (show (0 : ℝ) ≤ h ^ 2 by positivity)
  have p6 : (1 - ε) * (k * Cl) ≤ h * Cl := by
    have : k * Cl ≤ h * Cl := mul_le_mul_of_nonneg_right hkh hCl
    have : (1 - ε) * (k * Cl) ≤ 1 * (k * Cl) :=
      mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hk0 hCl)
    linarith
  have p7 : -h * lr ≤ h * |lr| := by
    have := neg_le_abs lr
    nlinarith
  have p8 : 2 * k * L1 ≤ 2 * h * L1 := by nlinarith [mul_le_mul_of_nonneg_right hkh hL1]
  have p9 : 0 ≤ 2 * k * Lh := by positivity
  nlinarith [hE, hfield, p1, p2, p3, p4, p5, p6, p7, p8, p9]

end Decay

namespace Frame

open Decay

variable {Fr : Frame}

/-! ### Lemma B -/

/-- Ray points, scaled by `1/h`, are of the form of the certified ray `-r0 + δ + u(-1 ± 3i)`. -/
theorem ray_point_g {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : Cert.CertCore K ρ ε c m) (hxs : (0 : ℚ) < Fr.xs)
    {h : ℕ} (hh : 0 < h) {N0 : ℕ} (hN0 : N0 + Fr.n0off = ⌊(F.r0 : ℝ) * h⌋₊)
    (hW : (Fr.n0off : ℝ) + 1 + (Fr.xs : ℝ) ≤ (F.W : ℝ) * h) {θ : ℝ}
    (hθ : θ = phiR ∨ θ = -phiR) {r : ℝ} (hr : 0 < r) :
    (F.mprime : ℝ) ≤ gfun ρ ε c m (rayPt (Fr.xstar N0) θ r / h) := by
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

/-- Atoms in the scaled cell `[a, b]`. -/
noncomputable def atomCell (Fr : Frame) (h N0 : ℕ) (a b : ℝ) : Finset ℂ :=
  (Finset.univ : Finset (Fin Fr.d)).biUnion fun i =>
    ((range (N0 + ⌈(Fr.xs : ℝ)⌉₊)).filter
      (fun n : ℕ => -(h : ℝ) * b - (Fr.μ i : ℝ) ≤ n ∧ (n : ℝ) ≤ -(h : ℝ) * a - (Fr.μ i : ℝ))).image
        (fun n => ((Fr.atomPos (n, i) : ℝ) : ℂ))

lemma card_atomCell_le (Fr : Frame) (h N0 : ℕ) {a b : ℝ} (hab : a ≤ b) (hh : 0 < h) :
    ((Fr.atomCell h N0 a b).card : ℝ) ≤ Fr.d * (h * (b - a) + 1) := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  unfold atomCell
  refine (Nat.cast_le.2 Finset.card_biUnion_le).trans ?_
  push_cast
  have : ∀ i : Fin Fr.d, (((range (N0 + ⌈(Fr.xs : ℝ)⌉₊)).filter
      (fun n : ℕ => -(h : ℝ) * b - (Fr.μ i : ℝ) ≤ n ∧ (n : ℝ) ≤ -(h : ℝ) * a - (Fr.μ i : ℝ))).image
        (fun n => ((Fr.atomPos (n, i) : ℝ) : ℂ))).card ≤ (h : ℝ) * (b - a) + 1 := by
    intro i
    have c1 := card_nat_Icc_le (N0 + ⌈(Fr.xs : ℝ)⌉₊) (-(h : ℝ) * b - (Fr.μ i : ℝ))
      (-(h : ℝ) * a - (Fr.μ i : ℝ)) (by nlinarith)
    have i1 := (Nat.cast_le (α := ℝ)).2 (Finset.card_image_le (s := (range (N0 + ⌈(Fr.xs : ℝ)⌉₊)).filter
      (fun n : ℕ => -(h : ℝ) * b - (Fr.μ i : ℝ) ≤ n ∧ (n : ℝ) ≤ -(h : ℝ) * a - (Fr.μ i : ℝ)))
      (f := fun n => ((Fr.atomPos (n, i) : ℝ) : ℂ)))
    have e : -(h : ℝ) * a - (Fr.μ i : ℝ) - (-(h : ℝ) * b - (Fr.μ i : ℝ)) + 1 = (h : ℝ) * (b - a) + 1 := by
      ring
    have := i1.trans c1
    rw [e] at this
    exact_mod_cast this
  calc ∑ i : Fin Fr.d, ((((range (N0 + ⌈(Fr.xs : ℝ)⌉₊)).filter
      (fun n : ℕ => -(h : ℝ) * b - (Fr.μ i : ℝ) ≤ n ∧ (n : ℝ) ≤ -(h : ℝ) * a - (Fr.μ i : ℝ))).image
        (fun n => ((Fr.atomPos (n, i) : ℝ) : ℂ))).card : ℝ)
      ≤ ∑ _i : Fin Fr.d, ((h : ℝ) * (b - a) + 1) := Finset.sum_le_sum (fun i _ => this i)
    _ = _ := by simp; ring

lemma mem_atomCell {h N0 : ℕ} (hh : 0 < h) {a b : ℝ} {w : ℂ} (hw : Fr.IsAtom N0 w)
    (hx : a ≤ (w / h).re ∧ (w / h).re ≤ b) : w ∈ Fr.atomCell h N0 a b := by
  classical
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  obtain ⟨p, hp, rfl⟩ := hw
  unfold atomCell
  rw [Finset.mem_biUnion]
  refine ⟨p.2, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_image]
  refine ⟨p.1, ?_, rfl⟩
  rw [Finset.mem_filter]
  have hp' := hp
  unfold atomIdx at hp'
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true] at hp'
  refine ⟨hp'.1, ?_⟩
  simp only [atomPos, Complex.div_natCast_re, Complex.ofReal_re] at hx
  obtain ⟨h1, h2⟩ := hx
  rw [le_div_iff₀ hh'] at h1
  rw [div_le_iff₀ hh'] at h2
  constructor <;> nlinarith

lemma atom_re_range (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    {h N0 : ℕ} (hh : 0 < h) {w : ℂ} (hw : Fr.IsAtom N0 w) :
    -((N0 : ℝ) + Fr.n0off) / h ≤ (w / h).re ∧ (w / h).re ≤ 0 := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  obtain ⟨p, hp, rfl⟩ := hw
  have hle := atom_le hAR hp
  have hmu := Fr.mu_pos p.2
  have hm : (0 : ℝ) ≤ p.1 := Nat.cast_nonneg _
  simp only [atomPos, Complex.div_natCast_re, Complex.ofReal_re]
  constructor
  · exact div_le_div_of_nonneg_right (by linarith) hh'.le
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) hh'.le

lemma atom_im {h N0 : ℕ} {w : ℂ} (hw : Fr.IsAtom N0 w) : (w / h).im = 0 := by
  obtain ⟨p, hp, rfl⟩ := hw
  simp [Complex.div_natCast_im]

/-- **Lemma B** (finite-cell version, general frame): for distinct free points, each an atom or a
ray point, `k m′ + h d Sbase - d Γ ≤ ∑_l g(z_l / h)`. -/
theorem lemmaB {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (hFr : Fr.DecayOK) (F : Cert.CertCore K ρ ε c m)
    {h k : ℕ} (hh : 0 < h) {N0 : ℕ} (hN0 : N0 + Fr.n0off = ⌊(F.r0 : ℝ) * h⌋₊)
    (hW : (Fr.n0off : ℝ) + 1 + (Fr.xs : ℝ) ≤ (F.W : ℝ) * h) (z : Fin k → ℂ)
    (hzi : Function.Injective z)
    (hz : ∀ l, Fr.IsAtom N0 (z l) ∨ Fr.IsRay N0 (z l)) :
    (k : ℝ) * F.mprime + h * (Fr.d * F.Sbase)
        - Fr.d * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0
      ≤ ∑ l, gfun ρ ε c m (z l / h) := by
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
  have hpt : ∀ l, (F.mprime : ℝ) + μ l ≤ gfun ρ ε c m (z l / h) := by
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
      exact ray_point_g F hxs hh hN0 hW hθ hr0'
  have hsumpt : (k : ℝ) * F.mprime + ∑ l, μ l ≤ ∑ l, gfun ρ ε c m (z l / h) := by
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

/-! ### Lemma A -/

theorem lemmaA {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (hFr : Fr.DecayOK) (F : Cert.CertCore K ρ ε c m) {D : ℝ}
    (hD : D ≤ 2 * ((F.mprime : ℝ) + Fr.d * F.Sbase) - F.Ibound + 3 / 2)
    {m0 : ℝ} (hm0 : 0 < m0)
    {h k : ℕ} (hh : 0 < h) {N0 : ℕ} (hN0 : N0 + Fr.n0off = ⌊(F.r0 : ℝ) * h⌋₊)
    (hW : (Fr.n0off : ℝ) + 1 + (Fr.xs : ℝ) ≤ (F.W : ℝ) * h)
    (s : Fin k → Fin h) (hs : Function.Injective s) (z : Fin k → ℂ) (hzi : Function.Injective z)
    (hz : ∀ l, Fr.IsAtom N0 (z l) ∨ Fr.IsRay N0 (z l))
    (hre : ∀ l, m0 ≤ -(z l).re) (q : Fin k → ℝ) (Cl : ℝ) (hCl : 0 ≤ Cl)
    (hq : ∀ l, Real.log (q l) ≤ (1 - ε) * (Cl - 2 * Real.pi * |(z l).im|)) :
    ∑ l, Real.log (q l) + Real.log (‖cexpr z (fun i => (((s i : Fin h) : ℕ) : ℂ))‖ ^ 2)
      ≤ -(h : ℝ) ^ 2 * D + h * ((h : ℝ) - k) * F.ccert
        + Rerr h (Fr.d * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0) ρ Cl m0 := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hkh : k ≤ h := by simpa using Fintype.card_le_of_injective s hs
  have hkh' : (k : ℝ) ≤ h := by exact_mod_cast hkh
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlogh : 0 ≤ Real.log h := Real.log_nonneg (show (1 : ℝ) ≤ h by exact_mod_cast hh)
  have hlog1 : 0 ≤ Real.log (1 + (h : ℝ) / m0) :=
    Real.log_nonneg (by have : (0:ℝ) ≤ h / m0 := by positivity
                        linarith)
  have hρ := F.hρ
  have hE := energy_A0 hh hm0 hρ c m F.hm s hs z hzi hre
  set Γ := ∑ i, max ((F.mprime : ℝ) - F.segG i) 0 with hΓ
  have hB := lemmaB hFr F hh hN0 hW z hzi hz
  have hfree : ∑ l, (Usig ρ c m (z l / h) - Utau (z l / h))
      = ∑ l, gfun ρ ε c m (z l / h) - (1 - ε) * (∑ l, Real.pi * |(z l).im|) / h := by
    have : ∀ l, Usig ρ c m (z l / h) - Utau (z l / h)
        = gfun ρ ε c m (z l / h) - (1 - ε) * (Real.pi * |(z l).im|) / h := by
      intro l
      unfold gfun
      rw [Complex.div_natCast_im, abs_div, abs_of_pos hh']
      field_simp
      ring
    simp_rw [this, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  set r := rmask s with hr
  have hr0 : ∀ b, 0 ≤ r b := fun b => by rcases rmask_cases s b with e | e <;> rw [hr, e] <;> norm_num
  have hrs : ∑ b, r b = (h : ℝ) - k := by
    have := sum_mask s hs (fun _ => (1 : ℝ))
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_sub_distrib] at this
    simp only [hr]; linarith
  have hnode : ∀ b : Fin h, Usig ρ c m (nodeC h b) - Utau (nodeC h b)
      = gfun ρ ε c m (nodeC h b) := by
    intro b; unfold gfun nodeC; simp
  have hgnode : ∀ b : Fin h, (F.gmin : ℝ) ≤ gfun ρ ε c m (nodeC h b) := by
    intro b
    have h0 : (0 : ℝ) ≤ (b : ℝ) / h := by positivity
    have h1 : (b : ℝ) / h ≤ 1 := by
      rw [div_le_one hh']; exact_mod_cast b.2.le
    have := F.g_line_ge (x := (b : ℝ) / h) (by linarith) h1
    unfold nodeC
    convert this using 2
  have hremoved : (h - k : ℝ) * F.gmin ≤ ∑ b, r b * (Usig ρ c m (nodeC h b) - Utau (nodeC h b)) := by
    simp_rw [hnode]
    calc (h - k : ℝ) * F.gmin = ∑ b, r b * F.gmin := by rw [← Finset.sum_mul, hrs]
      _ ≤ _ := Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hgnode b) (hr0 b))
  have hfield : ∑ l, Real.log (q l) ≤ (1 - ε) * (k * Cl - 2 * ∑ l, Real.pi * |(z l).im|) := by
    have := Finset.sum_le_sum (s := univ) (fun l _ => hq l)
    rw [← Finset.mul_sum, Finset.sum_sub_distrib] at this
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    have e : ∑ l : Fin k, 2 * Real.pi * |(z l).im| = 2 * ∑ l, Real.pi * |(z l).im| := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [e] at this; exact this
  rw [hfree] at hE
  have hIb := F.I_ok
  have hc := F.ccert_ge
  unfold Rerr
  have hε1 := F.hε1
  have hε0 := F.hε0
  set SIm := ∑ l, Real.pi * |(z l).im| with hSIm
  have hS0 : 0 ≤ SIm := Finset.sum_nonneg (fun l _ => by positivity)
  set G := ∑ l, gfun ρ ε c m (z l / h) with hG
  set Rm := ∑ b, r b * (Usig ρ c m (nodeC h b) - Utau (nodeC h b)) with hRm
  have hfin : 2 * h * (G - (1 - ε) * SIm / h + Rm) = 2 * h * (G + Rm) - 2 * ((1 - ε) * SIm) := by
    field_simp; ring
  rw [hfin] at hE
  have p10 : (1 - ε) * (k * Cl - 2 * SIm) = (1 - ε) * (k * Cl) - 2 * ((1 - ε) * SIm) := by ring
  rw [p10] at hfield
  have hB' : (k : ℝ) * F.mprime + h * (Fr.d * F.Sbase) - 2 * (Fr.d * Γ / 2) ≤ G := by linarith
  have := arith_core (h : ℝ) (k : ℝ) Cl ε SIm G Rm (Fr.d * Γ / 2) F.Ibound D (Fr.d * F.Sbase)
    F.mprime F.gmin F.ccert (Irho ρ c m) (Real.log ρ) (Real.log h) (Real.log (1 + h / m0))
    (∑ l, Real.log (q l)) (Real.log (‖cexpr z (fun i => (((s i : Fin h) : ℕ) : ℂ))‖ ^ 2))
    hh' hk0 hkh' hCl hε1 hε0 hlog1 hlogh hE hfield hB' hremoved hIb hD hc
  linarith

end Frame
end CatalanCore
