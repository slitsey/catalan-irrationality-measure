module

public import CatalanCore.Uniform.Content.UFFamily4.CoverRho1
public import CatalanCore.Uniform.Content.UFFamily4.CoverRho2
public import CatalanCore.Uniform.Content.UFWire.Layer

@[expose] public section

/-!
# The thirds UF layer: coverage and the content theorem (lane H, H13)

* `thirds_cover`: every `(r, p)` of the thirds band (`r` even, `p` odd, `p % 3 ≠ 0`, `60 ≤ p`,
  `3 r < 10 p ≤ 39 r`) lies in one of the 52 family regions.  This is a finite decomposition of the
  band into polygons (`CoverRho1`, `CoverRho2`: a decision tree on the affine-with-floor
  inequalities, each leaf closed by `omega` or by naming the family).
* `thirds_valid`: the layer `thirdsUFLayer T` is valid on the whole band for a prime `p`.
* `thirds_eff_le`: bookkeeping `eff = baseOf (idx r p) r p + depth` with `RegOf (idx r p) r p`.
* `thirdsUFContent`: `HasContent` of the thirds even-scale family from `hasContent_twoTerm_cons`
  with `L := thirdsUFLayer T`, the UF layer being used on the band `60 ≤ p`, `3 r < 10 p ≤ 39 r`
  and the bound required of it being a per-family inequality.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Smith CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.UFFamily3

namespace CatalanCore.Uniform.Content.UFFamily4

/-- **Coverage.**  The 52 family regions cover the thirds band. -/
theorem thirds_cover {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hp3 : p % 3 ≠ 0)
    (hlo : 3 * r < 10 * p) (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) : ∃ i, RegOf i r p := by
  rcases (by omega : p % 3 = 1 ∨ p % 3 = 2) with h | h
  · exact cover_rho1 hr hp2 hlo hhi hp60 h
  · exact cover_rho2 hr hp2 hlo hhi hp60 h

/-- A prime `p ≥ 60` is odd and prime to `3`. -/
theorem prime_odd_of_ge {p : ℕ} (hp : p.Prime) (h60 : 60 ≤ p) : p % 2 = 1 ∧ p % 3 ≠ 0 := by
  constructor
  · by_contra hne
    have h2 : 2 ∣ p := by omega
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega
  · intro h
    rcases hp.eq_one_or_self_of_dvd 3 (by omega : 3 ∣ p) with h | h <;> omega

/-- The band conditions of the thirds UF layer. -/
def Band (r p : ℕ) : Prop := 60 ≤ p ∧ 3 * r < 10 * p ∧ 10 * p ≤ 39 * r

variable {Fr : Frame}

/-- **The thirds UF layer is valid on the whole band** (for a prime `p`, even `r`, norm `1`). -/
theorem thirds_valid (T : TwoTermData Fr 3 2) {depth : ℕ} (hn : Fr.norm = 1) {r p : ℕ}
    (hp : p.Prime) (hr : r % 2 = 0) (hb : Band r p) :
    (thirdsUFLayer (depth := depth) T).valid r p := by
  obtain ⟨h60, hlo, hhi⟩ := hb
  obtain ⟨h2, h3⟩ := prime_odd_of_ge hp h60
  refine ⟨thirds_cover hr h2 h3 hlo hhi h60, hn, ?_⟩
  intro hf
  have : Fr.norm ∈ S p := by rw [hn]; exact one_mem _
  refine ⟨this, ?_⟩
  rw [hn]
  simp [red]

/-- On the band the layer's effective price is the price of a family that contains `(r, p)`. -/
theorem thirds_eff (T : TwoTermData Fr 3 2) {depth : ℕ} {r p : ℕ} (hc : ∃ i, RegOf i r p) :
    RegOf (idx r p) r p ∧ (thirdsUFLayer (depth := depth) T).eff r p = baseOf (idx r p) r p + depth :=
  ⟨idx_spec hc, thirdsUFLayer_eff T r p⟩

end CatalanCore.Uniform.Content.UFFamily4
