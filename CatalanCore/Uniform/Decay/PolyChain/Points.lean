module

public import CatalanCore.Uniform.Decay.PolyChain.CertP

@[expose] public section

/-!
# Contour premises of the energy step at polygon points (lane D, package D7)

For a source representation `SourceRep Fr N0 pts d C V` (D4), every point of the polygon space:

* `poly_dist`: keeps distance `≥ min m0 1` from the node half-line `[0, ∞)` (atoms through
  `m0 ≤ μ_i`, both path copies through `node_dist`);
* `poly_norm`: satisfies `‖z‖ ≤ B + 2 |Im z|` for any `B ≥ N0 + n0off` and `B ≥ V`
  (atoms through the head range, both path copies through `growth`);
* `poly_atom_or_ge`: (at the scaled polygon of `polygonRep_scaled`) is an atom or satisfies
  `g(z/h) ≥ m'` (`CertCoreP.tube_ok`), as needed by `lemmaBG_gen`.
-/

open Finset Set

namespace CatalanCore.Uniform.Decay.PolyChain

open CatalanCore CatalanCore.Decay CatalanCore.Uniform.Decay.Polygon CatalanCore.Uniform.Decay.Assembly

variable {Fr : Frame}

theorem norm_conj_sub_real (z : ℂ) (t : ℝ) : ‖(starRingEnd ℂ) z - (t : ℂ)‖ = ‖z - (t : ℂ)‖ := by
  rw [← Complex.norm_conj (z - (t : ℂ)), map_sub, Complex.conj_ofReal]

/-- **Node distance at polygon-space points.** -/
theorem poly_dist {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ} (hS : SourceRep Fr N0 pts d C V)
    {m0 : ℝ} (hμ : ∀ i, m0 ≤ Fr.μ i) (x : Fr.XT N0) {t : ℝ} (ht : 0 ≤ t) :
    min m0 1 ≤ ‖polyPt Fr N0 pts d x - (t : ℂ)‖ := by
  rcases x with p | u | u
  · simp only [polyPt, Sum.elim_inl, Frame.atomPos]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hμ p.1.2
    have h2 : (0 : ℝ) ≤ (p.1.1 : ℝ) := Nat.cast_nonneg _
    have h3 : -(-((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ)) - t) ≤ |-((p.1.1 : ℝ) + (Fr.μ p.1.2 : ℝ)) - t| :=
      neg_le_abs _
    have := min_le_left m0 1
    linarith
  · simp only [polyPt, Sum.elim_inr, Sum.elim_inl]
    exact (min_le_right _ _).trans (hS.node_dist u.1 u.2.le t ht)
  · simp only [polyPt, Sum.elim_inr]
    rw [hS.conj_pt u.1, norm_conj_sub_real]
    exact (min_le_right _ _).trans (hS.node_dist u.1 u.2.le t ht)

/-- **Norm control at polygon-space points.** -/
theorem poly_norm {N0 : ℕ} {pts : List ℂ} {d : ℂ} {C V : ℝ} (hS : SourceRep Fr N0 pts d C V)
    (hAR : ∀ i : Fin Fr.d, ((⌊Fr.xs - Fr.μ i⌋ : ℤ) : ℚ) + Fr.μ i ≤ Fr.n0off)
    {B : ℝ} (hBN : (N0 : ℝ) + Fr.n0off ≤ B) (hBV : V ≤ B) (x : Fr.XT N0) :
    ‖polyPt Fr N0 pts d x‖ ≤ B + 2 * |(polyPt Fr N0 pts d x).im| := by
  rcases x with p | u | u
  · simp only [polyPt, Sum.elim_inl, Frame.atomPos, Complex.norm_real, Real.norm_eq_abs,
      Complex.ofReal_im, abs_zero, mul_zero, add_zero]
    have hle := Frame.atom_le hAR p.2
    have hmu := Fr.mu_pos p.1.2
    have hmu' : (0 : ℝ) < (Fr.μ p.1.2 : ℝ) := by exact_mod_cast hmu
    have hm : (0 : ℝ) ≤ p.1.1 := Nat.cast_nonneg _
    rw [abs_of_nonpos (by linarith)]
    linarith
  · simp only [polyPt, Sum.elim_inr, Sum.elim_inl]
    have := hS.growth u.1 u.2.le
    linarith
  · simp only [polyPt, Sum.elim_inr]
    rw [hS.conj_pt u.1, Complex.norm_conj, Complex.conj_im, abs_neg]
    have := hS.growth u.1 u.2.le
    linarith

/-- **Lemma B premise at the scaled polygon**: atom, or `g(z/h) ≥ m'`. -/
theorem poly_atom_or_ge {P : RatPolygon} {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertCoreP P K ρ ε c m) {h : ℕ} (hh : 0 < h)
    (hH : |hShift Fr P.r0 h| ≤ (F.W : ℝ) * h) (x : Fr.XT (N0Of Fr P.r0 h)) :
    Fr.IsAtom (N0Of Fr P.r0 h) (polyPt Fr (N0Of Fr P.r0 h) (physL Fr P h) P.tailDir x) ∨
      (F.mprime : ℝ) ≤ F.g (polyPt Fr (N0Of Fr P.r0 h) (physL Fr P h) P.tailDir x / (h : ℂ)) := by
  by_cases hx : ∃ p, x = Sum.inl p
  · obtain ⟨p, rfl⟩ := hx
    left; exact ⟨p.1, p.2, rfl⟩
  · right
    push Not at hx
    have hh' : (0 : ℝ) < h := by exact_mod_cast hh
    have := g_ge_poly F Fr hh' hH x hx
    simpa using this

end CatalanCore.Uniform.Decay.PolyChain
