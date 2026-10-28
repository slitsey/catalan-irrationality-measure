module
public import CatalanMeasure.GenD.Uniform.W.Slots.Core
@[expose] public section
set_option Elab.async false

/-!
# Condition groups and the Theorem Z counts

Plan.md S6 / Risk 2: each condition group is its own rank bound, and the groups are summed
with `omega`.

* `finrank_iInf_ker_ge`: a family of `m` linear maps `A → F^{c_i}` cuts `A` down by at most
  `Σ c_i`.
* `zNH`, `zNL`: the condition-count forms `N_H`, `N_L` of zone2 sec. 5 (integers, with
  positive parts), written as `dof - Σ groups`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module
noncomputable section

/-- A family of maps `A → F^{c_i}`: the common kernel has dimension `≥ dim A - Σ c_i`. -/
theorem finrank_iInf_ker_ge {F A : Type*} [Field F] [AddCommGroup A] [Module F A]
    [FiniteDimensional F A] {ι : Type*} [Fintype ι] (c : ι → ℕ)
    (Φ : (i : ι) → A →ₗ[F] (Fin (c i) → F)) :
    finrank F A - ∑ i, c i ≤ finrank F (⨅ i, LinearMap.ker (Φ i) : Submodule F A) := by
  have hk : (⨅ i, LinearMap.ker (Φ i) : Submodule F A) = LinearMap.ker (LinearMap.pi Φ) := by
    ext x; simp [LinearMap.mem_ker, funext_iff, Submodule.mem_iInf]
  rw [hk]
  have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi Φ)
  have h2 : finrank F (LinearMap.range (LinearMap.pi Φ)) ≤ ∑ i, c i := by
    have := Submodule.finrank_le (LinearMap.range (LinearMap.pi Φ))
    simpa [Module.finrank_pi_fintype] using this
  omega

/-- Positive part. -/
def pos (z : ℤ) : ℤ := max z 0

/-- `N_H(s)` of zone2 sec. 5 (Law_H), as `dof - Σ groups`; `p` odd, `hp = (p-1)/2`.
Groups: block-0 virtual rows, top-block virtual rows, window-`s` main zone, window-`(s+1)`
zone (2 per residue), window `s-1`, digit-0 residues, digit-`s` (rtop), digit-`s+1`. -/
def zNH (n b q g h p s : ℤ) : ℤ :=
  let hp := (p - 1) / 2
  let L := n + b + q
  let H := L + g + h
  let M := n - 1 - g
  let eta := H - 1 - s * p
  let t := eta - p
  let rtop := M - (s - 1) * p
  let r' := min rtop hp
  (2 * h + q + 2 * hp) - (hp - g) - (hp - r') - pos (h + hp - 1 - max t (-1)) -
    2 * pos (t + 1) - pos (p - 1 - eta) - pos (min p (eta + 1) - b) - pos (r' - g) -
    pos (t + 1 - h - max g rtop)

/-- `N_L(s)` of zone2 sec. 5 (Law_L). -/
def zNL (n b q g h p s : ℤ) : ℤ :=
  let hp := (p - 1) / 2
  let L := n + b + q
  let H := L + g + h
  let M := n - 1 - g
  let eta := H - 1 - s * p
  let t := eta - p
  let d0 := s * p - M
  (2 * h + q + 2 * hp) - (2 * hp - g + d0) - pos (h + hp - 1 - max t (-1)) - pos (t + 1) -
    pos (L - (s + 1) * p) - pos (t - b + 1) - pos (p - 1 - eta)

/-- The H count is the dof minus the eight group counts (definitional bookkeeping, `omega`). -/
theorem zNH_groups (n b q g h p s : ℤ) :
    zNH n b q g h p s =
      (2 * h + q + 2 * ((p - 1) / 2)) -
        ((((p - 1) / 2) - g) + ((((p - 1) / 2) - min (n - 1 - g - (s - 1) * p) ((p - 1) / 2))) +
          pos (h + (p - 1) / 2 - 1 - max (n + b + q + g + h - 1 - s * p - p) (-1)) +
          2 * pos (n + b + q + g + h - 1 - s * p - p + 1) +
          pos (p - 1 - (n + b + q + g + h - 1 - s * p)) +
          pos (min p (n + b + q + g + h - 1 - s * p + 1) - b) +
          pos (min (n - 1 - g - (s - 1) * p) ((p - 1) / 2) - g) +
          pos (n + b + q + g + h - 1 - s * p - p + 1 - h - max g (n - 1 - g - (s - 1) * p))) := by
  unfold zNH
  simp only []
  omega

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
