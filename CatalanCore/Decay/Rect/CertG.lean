module

public import CatalanCore.Cert.Facts

@[expose] public section

/-!
# `CertCoreG`: the certificate interface over an ABSTRACT function `g` (WP-H2-core)

`CertCore` (WP3) hard-wires the square function `gfun = U^σ - U^τ + (1-ε)π|Im|`.  `CertCoreG` has
the same fields but the function `g : ℂ → ℝ` is a data field.  Which function it is (the square
`gfun`, or the hybrid `g_h = (1+α) U^σ - U^ν + (1-ε) π |Im|`, or `g_sq + h`) is recorded only by the
separate soundness hypothesis used by the energy step (`Rect/Energy`).

* `CertCore.toG` : the square `CertCore` is an instance (`g := gfun ρ ε c m`).
* `CertCoreG.Dof` : same formula as `CertCore.Dof`.
-/

open Finset
open CatalanLambda.Decay (gfun Usig Utau Irho)

namespace CatalanCore.Cert

/-- **Frame-free certificate facts over an abstract `g`.** -/
structure CertCoreG (K : ℕ) (ρ ε : ℝ) (c : Fin K → ℂ) (m : Fin K → ℝ) where
  /-- the certified function -/
  g : ℂ → ℝ
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
  g_conj : ∀ s : ℂ, g ((starRingEnd ℂ) s) = g s
  rayBoxes : List (ℚ × ℚ)
  ray_box_ok : ∀ p ∈ rayBoxes, ∀ x y : ℝ, -(r0 : ℝ) - p.2 - W ≤ x → x ≤ -(r0 : ℝ) - p.1 + W →
    3 * (p.1 : ℝ) ≤ y → y ≤ 3 * (p.2 : ℝ) → (mprime : ℝ) ≤ g ⟨x, y⟩
  ray_cover : ∀ u : ℝ, 0 ≤ u → u ≤ umax → ∃ p ∈ rayBoxes, (p.1 : ℝ) ≤ u ∧ u ≤ p.2
  ray_tail : ∀ u δ : ℝ, (umax : ℝ) ≤ u → |δ| ≤ W →
    (mprime : ℝ) ≤ g ⟨-(r0 : ℝ) + δ - u, 3 * u⟩
  nSeg : ℕ
  segA : Fin nSeg → ℚ
  segB : Fin nSeg → ℚ
  segG : Fin nSeg → ℚ
  seg_ab : ∀ i, segA i ≤ segB i
  seg_ok : ∀ i, ∀ x : ℝ, (segA i : ℝ) ≤ x → x ≤ segB i → (segG i : ℝ) ≤ g ⟨x, 0⟩
  seg_cover : ∀ x : ℝ, -(r0 : ℝ) ≤ x → x ≤ 0 → ∃ i, (segA i : ℝ) ≤ x ∧ x ≤ segB i
  Sbase_le : (Sbase : ℝ) ≤ ∑ i, ((segB i : ℝ) - segA i) * min ((segG i : ℝ) - mprime) 0
  lineCells : List (ℚ × ℚ)
  line_ok : ∀ p ∈ lineCells, ∀ x : ℝ, (p.1 : ℝ) ≤ x → x ≤ p.2 → (gmin : ℝ) ≤ g ⟨x, 0⟩
  line_cover : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∃ p ∈ lineCells, (p.1 : ℝ) ≤ x ∧ x ≤ p.2
  I_ok : Irho ρ c m ≤ Ibound
  ccert_ge : 2 * ((mprime : ℝ) - gmin) ≤ ccert

namespace CertCoreG

variable {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ} (F : CertCoreG K ρ ε c m)

/-- The decay exponent `2((1+α) m′ + d Sbase) - (1+α)² I + Inu` (same formula as `CertCore.Dof`). -/
def Dof (d : ℕ) (α Inu : ℚ) : ℚ :=
  2 * ((1 + α) * F.mprime + d * F.Sbase) - (1 + α) ^ 2 * F.Ibound + Inu

/-- `g ≥ m′` on the upper ray. -/
theorem ray_g_ge {u δ : ℝ} (hu : 0 ≤ u) (hδ : |δ| ≤ F.W) :
    (F.mprime : ℝ) ≤ F.g ⟨-(F.r0 : ℝ) + δ - u, 3 * u⟩ := by
  rcases le_total u F.umax with h | h
  · obtain ⟨p, hp, h1, h2⟩ := F.ray_cover u hu h
    refine F.ray_box_ok p hp _ _ ?_ ?_ ?_ ?_
    · have := abs_le.1 hδ; linarith
    · have := abs_le.1 hδ; linarith
    · linarith
    · linarith
  · exact F.ray_tail u δ h hδ

/-- `g ≥ m′` on the lower ray. -/
theorem ray_g_ge' {u δ : ℝ} (hu : 0 ≤ u) (hδ : |δ| ≤ F.W) :
    (F.mprime : ℝ) ≤ F.g ⟨-(F.r0 : ℝ) + δ - u, -(3 * u)⟩ := by
  have h := F.ray_g_ge hu hδ
  have e : (starRingEnd ℂ) (⟨-(F.r0 : ℝ) + δ - u, 3 * u⟩ : ℂ) = ⟨-(F.r0 : ℝ) + δ - u, -(3 * u)⟩ := by
    apply Complex.ext <;> simp
  rw [← e, F.g_conj]; exact h

/-- `g ≥ g_min` on `[0, 1]` (the interface is narrowed from legacy `[-1/64, 1]`: only nodes `x ≥ 0` are used). -/
theorem g_line_ge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (F.gmin : ℝ) ≤ F.g ⟨x, 0⟩ := by
  obtain ⟨p, hp, a, b⟩ := F.line_cover x h0 h1
  exact F.line_ok p hp x a b

end CertCoreG

/-- **Bridge.**  The square `CertCore` is an instance of `CertCoreG` with `g := gfun ρ ε c m`. -/
noncomputable def CertCore.toG {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ} (F : CertCore K ρ ε c m) :
    CertCoreG K ρ ε c m where
  g := gfun ρ ε c m
  r0 := F.r0
  W := F.W
  umax := F.umax
  mprime := F.mprime
  gmin := F.gmin
  Sbase := F.Sbase
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
  Sbase_le := F.Sbase_le
  lineCells := F.lineCells
  line_ok := F.line_ok
  line_cover := fun x h0 h1 => F.line_cover x (by linarith) h1
  I_ok := F.I_ok
  ccert_ge := F.ccert_ge

theorem CertCore.toG_Dof {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ} (F : CertCore K ρ ε c m)
    (d : ℕ) (α Inu : ℚ) : F.toG.Dof d α Inu = F.Dof d α Inu := rfl

theorem CertCore.toG_g {K : ℕ} {ρ ε : ℝ} {c : Fin K → ℂ} {m : Fin K → ℝ} (F : CertCore K ρ ε c m) :
    F.toG.g = gfun ρ ε c m := rfl

/-- The hybrid function `g_{α,U}(s) = (1+α) U^σ(s) - U(s) + (1-ε) π |Im s|`; the square one is
`α = 0`, `U = Utau`. -/
noncomputable def gAlpha {K : ℕ} (ρ ε : ℝ) (c : Fin K → ℂ) (m : Fin K → ℝ) (α : ℝ) (U : ℂ → ℝ)
    (s : ℂ) : ℝ :=
  (1 + α) * Usig ρ c m s - U s + (1 - ε) * Real.pi * |s.im|

theorem gAlpha_square {K : ℕ} (ρ ε : ℝ) (c : Fin K → ℂ) (m : Fin K → ℝ) :
    gAlpha ρ ε c m 0 Utau = gfun ρ ε c m := by
  funext s; simp [gAlpha, gfun]

end CatalanCore.Cert
