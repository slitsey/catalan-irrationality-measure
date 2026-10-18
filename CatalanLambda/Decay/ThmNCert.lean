import CatalanLambda.Decay.ThmNPoint

/-!
# Theorem N_ρ: the numerical certificate facts as hypotheses (`CertFacts`)

`g(s) = U_ρ^σ(s) - U^τ(s) + (1-ε) π |Im s|`.  The structure packages exactly the finite
inequalities listed in BT §2.1 / §5.1, with rational constants, as `∀`-statements over explicit
cell lists, so that a later `decide +kernel` module (plus soundness lemmas for the log/arctan
brackets) can supply them.
-/

open Finset

namespace CatalanLambda.Decay

/-- The function `g`. -/
noncomputable def gfun {K : ℕ} (ρ ε : ℝ) (c : Fin K → ℂ) (m : Fin K → ℝ) (s : ℂ) : ℝ :=
  Usig ρ c m s - Utau s + (1 - ε) * Real.pi * |s.im|

/-- **Certificate facts** (BT §2.1). -/
structure CertFacts (K : ℕ) (ρ ε : ℝ) (c : Fin K → ℂ) (m : Fin K → ℝ) where
  /-- rational constants -/
  r0 : ℚ
  W : ℚ
  umax : ℚ
  mprime : ℚ
  gmin : ℚ
  Scert : ℚ
  Ibound : ℚ
  Dcert : ℚ
  ccert : ℚ
  r0_pos : 0 < r0
  W_pos : 0 < W
  hρ : 0 < ρ
  hε0 : 0 < ε
  hε1 : ε < 1
  hm : ∑ k, m k = 1
  /-- `g` is invariant under complex conjugation (symmetry of the data `σ`). -/
  g_conj : ∀ s : ℂ, gfun ρ ε c m ((starRingEnd ℂ) s) = gfun ρ ε c m s
  /-- (R) ray boxes, given by `u`-intervals `[p.1, p.2]` -/
  rayBoxes : List (ℚ × ℚ)
  ray_box_ok : ∀ p ∈ rayBoxes, ∀ x y : ℝ, -(r0 : ℝ) - p.2 - W ≤ x → x ≤ -(r0 : ℝ) - p.1 + W →
    3 * (p.1 : ℝ) ≤ y → y ≤ 3 * (p.2 : ℝ) → (mprime : ℝ) ≤ gfun ρ ε c m ⟨x, y⟩
  ray_cover : ∀ u : ℝ, 0 ≤ u → u ≤ umax → ∃ p ∈ rayBoxes, (p.1 : ℝ) ≤ u ∧ u ≤ p.2
  /-- tail bound (`u ≥ umax`) -/
  ray_tail : ∀ u δ : ℝ, (umax : ℝ) ≤ u → |δ| ≤ W → (mprime : ℝ) ≤ gfun ρ ε c m ⟨-(r0 : ℝ) + δ - u, 3 * u⟩
  /-- (S) segment cells `[segA i, segB i]` with lower bounds `segG i` -/
  nSeg : ℕ
  segA : Fin nSeg → ℚ
  segB : Fin nSeg → ℚ
  segG : Fin nSeg → ℚ
  seg_ab : ∀ i, segA i ≤ segB i
  seg_ok : ∀ i, ∀ x : ℝ, (segA i : ℝ) ≤ x → x ≤ segB i → (segG i : ℝ) ≤ gfun ρ ε c m ⟨x, 0⟩
  seg_cover : ∀ x : ℝ, -(r0 : ℝ) ≤ x → x ≤ 0 → ∃ i, (segA i : ℝ) ≤ x ∧ x ≤ segB i
  Scert_le : (Scert : ℝ) ≤ 2 * ∑ i, ((segB i : ℝ) - segA i) * min ((segG i : ℝ) - mprime) 0
  /-- (L) line cells covering `[-1/64, 1]`, with `g ≥ gmin` -/
  lineCells : List (ℚ × ℚ)
  line_ok : ∀ p ∈ lineCells, ∀ x : ℝ, (p.1 : ℝ) ≤ x → x ≤ p.2 → (gmin : ℝ) ≤ gfun ρ ε c m ⟨x, 0⟩
  line_cover : ∀ x : ℝ, -(1 / 64 : ℝ) ≤ x → x ≤ 1 → ∃ p ∈ lineCells, (p.1 : ℝ) ≤ x ∧ x ≤ p.2
  /-- (I) -/
  I_ok : Irho ρ c m ≤ Ibound
  /-- the final arithmetic -/
  Dcert_le : (Dcert : ℝ) ≤ 2 * (mprime + Scert) - Ibound + 3 / 2
  ccert_ge : 2 * ((mprime : ℝ) - gmin) ≤ ccert

namespace CertFacts

variable {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ} (F : CertFacts K ρ ε c m)

/-- `g ≥ m′` on the upper ray (all `u ≥ 0`, shifts `|δ| ≤ W`). -/
theorem ray_g_ge {u δ : ℝ} (hu : 0 ≤ u) (hδ : |δ| ≤ F.W) :
    (F.mprime : ℝ) ≤ gfun ρ ε c m ⟨-(F.r0 : ℝ) + δ - u, 3 * u⟩ := by
  rcases le_total u F.umax with h | h
  · obtain ⟨p, hp, h1, h2⟩ := F.ray_cover u hu h
    refine F.ray_box_ok p hp _ _ ?_ ?_ ?_ ?_
    · have := abs_le.1 hδ; linarith
    · have := abs_le.1 hδ; linarith
    · linarith
    · linarith
  · exact F.ray_tail u δ h hδ

/-- `g ≥ m′` on the lower ray, by conjugation symmetry. -/
theorem ray_g_ge' {u δ : ℝ} (hu : 0 ≤ u) (hδ : |δ| ≤ F.W) :
    (F.mprime : ℝ) ≤ gfun ρ ε c m ⟨-(F.r0 : ℝ) + δ - u, -(3 * u)⟩ := by
  have h := F.ray_g_ge hu hδ
  have e : (starRingEnd ℂ) (⟨-(F.r0 : ℝ) + δ - u, 3 * u⟩ : ℂ) = ⟨-(F.r0 : ℝ) + δ - u, -(3 * u)⟩ := by
    apply Complex.ext <;> simp
  rw [← e, F.g_conj]; exact h

/-- `g ≥ g_min` on `[0, 1]` (real axis). -/
theorem g_line_ge {x : ℝ} (h0 : -(1 / 64 : ℝ) ≤ x) (h1 : x ≤ 1) :
    (F.gmin : ℝ) ≤ gfun ρ ε c m ⟨x, 0⟩ := by
  obtain ⟨p, hp, a, b⟩ := F.line_cover x h0 h1
  exact F.line_ok p hp x a b

end CertFacts

end CatalanLambda.Decay
