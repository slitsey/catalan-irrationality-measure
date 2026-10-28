module

public import CatalanCore.Uniform.Decay.PolyChain.Integ
public import CatalanCore.Uniform.Decay.Assembly.Normalize
public import CatalanCore.Decay.Rect.CertG

@[expose] public section

/-!
# The polygon certificate interface and the polygon Lemma B (lane D, package D7)

`CertCoreP P K ρ ε c m` is `Cert.CertCoreGs` with the straight-ray fields (`rayBoxes`,
`ray_box_ok`, `ray_cover`, `ray_tail`, slope `sl`) replaced by ONE tube field over the
normalised polygon `Γ = chainSet (-r0) (p_1 … p_m) ∪ tailSet p_m (-1 + i s)`:

`tube_ok : ∀ w ∈ Γ, ∀ δ : ℝ, |δ| ≤ W → m' ≤ g (w + δ)`

(the lower path is covered by `g_conj`).  The base point is `-P.r0`.  All other fields
(cap cells, line cells, energy, `c ≥ 2(m' - g_min)`) are those of `CertCoreGs`.

* `pathPt_affine`: `γ` commutes with real affine maps (the tail direction rescales).
* `scaled_upper` / `scaled_lower`: physical polygon points of `polygonRep_scaled` satisfy
  `z / r = w + h_r / r` resp. `conj z / r = w + h_r / r` with `w ∈ Γ`.
* `lemmaBG_gen`: Lemma B for free points that are atoms or satisfy `g(z/h) ≥ m'`
  (contour-free); `CertCoreP.g_ge_poly`: `g(z/h) ≥ m'` at polygon points once `|h_r| ≤ W h`.
-/

open Finset Set
open CatalanLambda.Decay (Usig Irho)

namespace CatalanCore.Uniform.Decay.PolyChain

open CatalanCore CatalanCore.Decay CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Assembly

/-- The normalised upper polygon `Γ` (finite edges from `-r0` and the closed tail). -/
def normSet (P : RatPolygon) : Set ℂ :=
  chainSet (((-(P.r0 : ℝ)) : ℝ) : ℂ) (P.verts.map vertC) ∪
    tailSet (((((-(P.r0 : ℝ)) : ℝ) : ℂ) :: P.verts.map vertC).getLast (List.cons_ne_nil _ _))
      P.tailDir

/-- **The polygon certificate interface.** -/
structure CertCoreP (P : RatPolygon) (K : ℕ) (ρ ε : ℝ) (c : Fin K → ℂ) (m : Fin K → ℝ) where
  g : ℂ → ℝ
  W : ℚ
  mprime : ℚ
  gmin : ℚ
  Sbase : ℚ
  Ibound : ℚ
  ccert : ℚ
  W_pos : 0 < W
  hρ : 0 < ρ
  hε0 : 0 < ε
  hε1 : ε < 1
  hm : ∑ k, m k = 1
  g_conj : ∀ s : ℂ, g ((starRingEnd ℂ) s) = g s
  tube_ok : ∀ w ∈ normSet P, ∀ δ : ℝ, |δ| ≤ W → (mprime : ℝ) ≤ g (w + δ)
  nSeg : ℕ
  segA : Fin nSeg → ℚ
  segB : Fin nSeg → ℚ
  segG : Fin nSeg → ℚ
  seg_ab : ∀ i, segA i ≤ segB i
  seg_ok : ∀ i, ∀ x : ℝ, (segA i : ℝ) ≤ x → x ≤ segB i → (segG i : ℝ) ≤ g ⟨x, 0⟩
  seg_cover : ∀ x : ℝ, -(P.r0 : ℝ) ≤ x → x ≤ 0 → ∃ i, (segA i : ℝ) ≤ x ∧ x ≤ segB i
  Sbase_le : (Sbase : ℝ) ≤ ∑ i, ((segB i : ℝ) - segA i) * min ((segG i : ℝ) - mprime) 0
  lineCells : List (ℚ × ℚ)
  line_ok : ∀ p ∈ lineCells, ∀ x : ℝ, (p.1 : ℝ) ≤ x → x ≤ p.2 → (gmin : ℝ) ≤ g ⟨x, 0⟩
  line_cover : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∃ p ∈ lineCells, (p.1 : ℝ) ≤ x ∧ x ≤ p.2
  I_ok : Irho ρ c m ≤ Ibound
  ccert_ge : 2 * ((mprime : ℝ) - gmin) ≤ ccert

/-! ### Real affine maps of the parametrised polygon -/

/-- `γ` commutes with `z ↦ r z + h` (`r ≠ 0` real); the tail direction becomes `d / r`. -/
theorem pathPt_affine {r : ℝ} (hr : r ≠ 0) (h d : ℂ) :
    ∀ (l : List ℂ) (a : ℂ) (u : ℝ),
      pathPt d ((r : ℂ) * a + h) (l.map (fun z => (r : ℂ) * z + h)) u
        = (r : ℂ) * pathPt (d / (r : ℂ)) a l u + h
  | [], a, u => by
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
    simp only [pathPt, List.map_nil]
    field_simp
    ring
  | b :: l, a, u => by
    simp only [pathPt, List.map_cons]
    split_ifs with h1
    · ring
    · exact pathPt_affine hr h d l b (u - 1)

theorem tailSet_div {L d : ℂ} {r : ℝ} (hr : 0 < r) : tailSet L (d / (r : ℂ)) ⊆ tailSet L d := by
  rintro z ⟨t, ht, rfl⟩
  refine ⟨t / r, div_nonneg ht hr.le, ?_⟩
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp

theorem xstar_complex (Fr : Frame) (r0 : ℚ) (r : ℝ) :
    ((Fr.xstar (N0Of Fr r0 r) : ℝ) : ℂ)
      = (r : ℂ) * (((-(r0 : ℝ)) : ℝ) : ℂ) + ((hShift Fr r0 r : ℝ) : ℂ) := by
  rw [xstar_eq_base]; push_cast; ring

/-- The physical polygon list of `polygonRep_scaled`. -/
noncomputable abbrev physL (Fr : Frame) (P : RatPolygon) (r : ℝ) : List ℂ :=
  P.verts.map (fun p => (r : ℂ) * vertC p + (hShift Fr P.r0 r : ℂ))

/-- **Upper physical points, rescaled**: `γ_r(u) = r w + h_r` with `w ∈ Γ`. -/
theorem scaled_upper (Fr : Frame) (P : RatPolygon) {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : 0 ≤ u) :
    ∃ w ∈ normSet P, pathPt P.tailDir ((Fr.xstar (N0Of Fr P.r0 r) : ℝ) : ℂ) (physL Fr P r) u
      = (r : ℂ) * w + ((hShift Fr P.r0 r : ℝ) : ℂ) := by
  have hl : physL Fr P r = (P.verts.map vertC).map
      (fun z => (r : ℂ) * z + ((hShift Fr P.r0 r : ℝ) : ℂ)) := by
    unfold physL; rw [List.map_map]; rfl
  rw [hl, xstar_complex, pathPt_affine hr.ne']
  refine ⟨_, ?_, rfl⟩
  rcases pathPt_mem (P.tailDir / (r : ℂ)) (P.verts.map vertC) (((-(P.r0 : ℝ)) : ℝ) : ℂ) hu with h | h
  · exact Or.inl h
  · exact Or.inr (tailSet_div hr h)

/-- Real shift bound: `|h_r / r| ≤ W` once `|h_r| ≤ W r`. -/
theorem g_ge_shift {P : RatPolygon} {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertCoreP P K ρ ε c m) {r H : ℝ} (hr : 0 < r) (hH : |H| ≤ (F.W : ℝ) * r)
    {w : ℂ} (hw : w ∈ normSet P) :
    (F.mprime : ℝ) ≤ F.g (((r : ℂ) * w + (H : ℂ)) / (r : ℂ)) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have e : ((r : ℂ) * w + (H : ℂ)) / (r : ℂ) = w + ((H / r : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [e]
  refine F.tube_ok w hw _ ?_
  rw [abs_div, abs_of_pos hr, div_le_iff₀ hr]; exact hH

/-- **`g ≥ m'` at every polygon point** (both copies) once `|h_r| ≤ W r`. -/
theorem g_ge_poly {P : RatPolygon} {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertCoreP P K ρ ε c m) (Fr : Frame) {r : ℝ} (hr : 0 < r)
    (hH : |hShift Fr P.r0 r| ≤ (F.W : ℝ) * r) (x : Fr.XT (N0Of Fr P.r0 r))
    (hx : ∀ p, x ≠ Sum.inl p) :
    (F.mprime : ℝ) ≤ F.g (polyPt Fr (N0Of Fr P.r0 r) (physL Fr P r) P.tailDir x / (r : ℂ)) := by
  rcases x with p | u | u
  · exact absurd rfl (hx p)
  · obtain ⟨w, hw, he⟩ := scaled_upper Fr P hr u.2.le
    simp only [polyPt, Sum.elim_inr, Sum.elim_inl]
    rw [he]; exact g_ge_shift F hr hH hw
  · obtain ⟨w, hw, he⟩ := scaled_upper Fr P hr u.2.le
    simp only [polyPt, Sum.elim_inr]
    rw [conjL_conj_path, he, ← F.g_conj]
    have : (starRingEnd ℂ) ((starRingEnd ℂ) ((r : ℂ) * w + ((hShift Fr P.r0 r : ℝ) : ℂ)) / (r : ℂ))
        = ((r : ℂ) * w + ((hShift Fr P.r0 r : ℝ) : ℂ)) / (r : ℂ) := by
      rw [map_div₀, Complex.conj_conj, Complex.conj_ofReal]
    rw [this]; exact g_ge_shift F hr hH hw

/-! ### Lemma B, contour-free -/

/-- **Lemma B** (contour-free): for distinct free points, each an atom or a point where
`g(z/h) ≥ m'`, `k m' + h d Sbase - d Γ ≤ ∑ g(z_l/h)`. -/
theorem lemmaBG_gen {Fr : Frame}
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    {P : RatPolygon} {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertCoreP P K ρ ε c m) {h k : ℕ} (hh : 0 < h) {N0 : ℕ}
    (hN1 : ((N0 : ℝ) + Fr.n0off) ≤ P.r0 * h) (z : Fin k → ℂ)
    (hzi : Function.Injective z)
    (hz : ∀ l, Fr.IsAtom N0 (z l) ∨ (F.mprime : ℝ) ≤ F.g (z l / h)) :
    (k : ℝ) * F.mprime + h * (Fr.d * F.Sbase)
        - Fr.d * ∑ i, max ((F.mprime : ℝ) - F.segG i) 0
      ≤ ∑ l, F.g (z l / h) := by
  classical
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hr0 : (0 : ℝ) ≤ P.r0 := by
    have h1 : (0 : ℝ) ≤ (N0 : ℝ) + Fr.n0off := by positivity
    by_contra hneg
    push Not at hneg
    nlinarith
  obtain ⟨i0, _⟩ := F.seg_cover 0 (by linarith) le_rfl
  have hcell : ∀ l : Fin k, ∃ i : Fin F.nSeg, Fr.IsAtom N0 (z l) →
      ((F.segA i : ℝ) ≤ (z l / h).re ∧ (z l / h).re ≤ F.segB i) := by
    intro l
    by_cases ha : Fr.IsAtom N0 (z l)
    · obtain ⟨h1, h2⟩ := Frame.atom_re_range hAR hh ha
      have h3 : -(P.r0 : ℝ) ≤ (z l / h).re := by
        refine le_trans ?_ h1
        have hq : ((N0 : ℝ) + Fr.n0off) / h ≤ P.r0 := by
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
      have e : (z l / h) = ⟨(z l / h).re, 0⟩ := Complex.ext rfl (Frame.atom_im ha)
      rw [e]
      simp only [hμ, if_pos ha]
      have := min_le_left ((F.segG (φ l) : ℝ) - F.mprime) 0
      rw [← e] at hs
      rw [e] at hs
      linarith
    · simp only [hμ, if_neg ha, add_zero]
      exact (hz l).resolve_left ha
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
    refine le_trans ?_ (Frame.card_atomCell_le Fr h N0 hab hh)
    refine Nat.cast_le.2 (Finset.card_le_card_of_injOn z ?_ (hzi.injOn))
    intro l hl
    rw [Finset.mem_coe, Finset.mem_filter] at hl
    have ha : Fr.IsAtom N0 (z l) := (Finset.mem_filter.1 hl.1).2
    have := hφ l ha
    rw [hl.2] at this
    exact Frame.mem_atomCell hh ha this
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

end CatalanCore.Uniform.Decay.PolyChain
