module

public import CatalanLambda.Decay.ThmNCert

@[expose] public section

/-!
# `CertCore`: the frame-free numerical certificate facts (WP3)

Exactly the legacy `CertFacts` minus the two density-dependent fields `Scert`, `Dcert`:

* `Sbase` is a lower bound for the UNscaled segment sum `∑ (segB - segA) · min (segG - m′) 0`
  (legacy: `Scert = 2 · Sbase`, i.e. the legacy statement is the density `d = 2`);
* `Dof F d α Inu = 2((1+α) m′ + d · Sbase) - (1+α)² I + Inu` is the decay exponent for atom
  density `d`, node-measure parameter `α` and node-measure energy `Inu`.  The square frames use
  `α = 0`, `Inu = 3/2`; the hybrid (design 9.4) will use other `(α, Inu)`.

`CertCore.ofFacts` is the legacy facade: every legacy `CertFacts` is a `CertCore`, and
`Dof 2 0 (3/2) ≥ Dcert` (`le_Dof_two`), so the legacy certificate is reused with no change.

The log-potential vocabulary (`gfun`, `Usig`, `Utau`, `Irho`) stays in the legacy namespace
`CatalanLambda.Decay` for now (frame-free; moves at cut-over, WP15).
-/

open Finset
open CatalanLambda.Decay (gfun CertFacts Irho)

namespace CatalanCore.Cert

/-- **Frame-free certificate facts.** -/
structure CertCore (K : ℕ) (ρ ε : ℝ) (c : Fin K → ℂ) (m : Fin K → ℝ) where
  /-- rational constants -/
  r0 : ℚ
  W : ℚ
  umax : ℚ
  mprime : ℚ
  gmin : ℚ
  Sbase : ℚ
  Ibound : ℚ
  ccert : ℚ
  r0_pos : 0 < r0
  W_pos : 0 < W
  hρ : 0 < ρ
  hε0 : 0 < ε
  hε1 : ε < 1
  hm : ∑ k, m k = 1
  g_conj : ∀ s : ℂ, gfun ρ ε c m ((starRingEnd ℂ) s) = gfun ρ ε c m s
  /-- (R) ray boxes -/
  rayBoxes : List (ℚ × ℚ)
  ray_box_ok : ∀ p ∈ rayBoxes, ∀ x y : ℝ, -(r0 : ℝ) - p.2 - W ≤ x → x ≤ -(r0 : ℝ) - p.1 + W →
    3 * (p.1 : ℝ) ≤ y → y ≤ 3 * (p.2 : ℝ) → (mprime : ℝ) ≤ gfun ρ ε c m ⟨x, y⟩
  ray_cover : ∀ u : ℝ, 0 ≤ u → u ≤ umax → ∃ p ∈ rayBoxes, (p.1 : ℝ) ≤ u ∧ u ≤ p.2
  ray_tail : ∀ u δ : ℝ, (umax : ℝ) ≤ u → |δ| ≤ W →
    (mprime : ℝ) ≤ gfun ρ ε c m ⟨-(r0 : ℝ) + δ - u, 3 * u⟩
  /-- (S) segment cells -/
  nSeg : ℕ
  segA : Fin nSeg → ℚ
  segB : Fin nSeg → ℚ
  segG : Fin nSeg → ℚ
  seg_ab : ∀ i, segA i ≤ segB i
  seg_ok : ∀ i, ∀ x : ℝ, (segA i : ℝ) ≤ x → x ≤ segB i → (segG i : ℝ) ≤ gfun ρ ε c m ⟨x, 0⟩
  seg_cover : ∀ x : ℝ, -(r0 : ℝ) ≤ x → x ≤ 0 → ∃ i, (segA i : ℝ) ≤ x ∧ x ≤ segB i
  /-- the UNscaled segment sum -/
  Sbase_le : (Sbase : ℝ) ≤ ∑ i, ((segB i : ℝ) - segA i) * min ((segG i : ℝ) - mprime) 0
  /-- (L) line cells -/
  lineCells : List (ℚ × ℚ)
  line_ok : ∀ p ∈ lineCells, ∀ x : ℝ, (p.1 : ℝ) ≤ x → x ≤ p.2 → (gmin : ℝ) ≤ gfun ρ ε c m ⟨x, 0⟩
  line_cover : ∀ x : ℝ, -(1 / 64 : ℝ) ≤ x → x ≤ 1 → ∃ p ∈ lineCells, (p.1 : ℝ) ≤ x ∧ x ≤ p.2
  /-- (I) -/
  I_ok : Irho ρ c m ≤ Ibound
  ccert_ge : 2 * ((mprime : ℝ) - gmin) ≤ ccert

namespace CertCore

variable {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ} (F : CertCore K ρ ε c m)

/-- The decay exponent for atom density `d`, node-measure mass parameter `α` and node energy `Inu`. -/
def Dof (d : ℕ) (α Inu : ℚ) : ℚ :=
  2 * ((1 + α) * F.mprime + d * F.Sbase) - (1 + α) ^ 2 * F.Ibound + Inu

/-- The square-frame exponent: `α = 0`, `Inu = 3/2`. -/
theorem Dof_square (d : ℕ) : F.Dof d 0 (3 / 2) = 2 * (F.mprime + d * F.Sbase) - F.Ibound + 3 / 2 := by
  unfold Dof; ring

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

/-- `g ≥ g_min` on `[-1/64, 1]` (real axis). -/
theorem g_line_ge {x : ℝ} (h0 : -(1 / 64 : ℝ) ≤ x) (h1 : x ≤ 1) :
    (F.gmin : ℝ) ≤ gfun ρ ε c m ⟨x, 0⟩ := by
  obtain ⟨p, hp, a, b⟩ := F.line_cover x h0 h1
  exact F.line_ok p hp x a b

end CertCore

/-- **The legacy facade.**  A legacy `CertFacts` is a `CertCore` with `Sbase = Scert/2`. -/
def CertCore.ofFacts {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) : CertCore K ρ ε c m where
  r0 := F.r0
  W := F.W
  umax := F.umax
  mprime := F.mprime
  gmin := F.gmin
  Sbase := F.Scert / 2
  Ibound := F.Ibound
  ccert := F.ccert
  r0_pos := F.r0_pos
  W_pos := F.W_pos
  hρ := F.hρ
  hε0 := F.hε0
  hε1 := F.hε1
  hm := F.hm
  g_conj := F.g_conj
  rayBoxes := F.rayBoxes
  ray_box_ok := F.ray_box_ok
  ray_cover := F.ray_cover
  ray_tail := F.ray_tail
  nSeg := F.nSeg
  segA := F.segA
  segB := F.segB
  segG := F.segG
  seg_ab := F.seg_ab
  seg_ok := F.seg_ok
  seg_cover := F.seg_cover
  Sbase_le := by
    have := F.Scert_le
    push_cast
    linarith
  lineCells := F.lineCells
  line_ok := F.line_ok
  line_cover := F.line_cover
  I_ok := F.I_ok
  ccert_ge := F.ccert_ge

/-- The legacy decay constant is recovered at density `2`: `Dcert ≤ Dof 2 0 (3/2)`. -/
theorem CertCore.le_Dof_two {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ}
    (F : CertFacts K ρ ε c m) : (F.Dcert : ℝ) ≤ ((CertCore.ofFacts F).Dof 2 0 (3 / 2) : ℚ) := by
  have h := F.Dcert_le
  unfold CertCore.Dof CertCore.ofFacts
  push_cast
  linarith

end CatalanCore.Cert
