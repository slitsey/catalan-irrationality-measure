module
public import CatalanMeasure.GenD.Uniform.W.Atoms
public import CatalanMeasure.GenD.Uniform.Prefix.RawResponse
@[expose] public section
set_option Elab.async false

/-!
# Tiling index versus G row index (shared step)

The enlarged physical tiling index `ρ ∈ Fin (b p + 1)` (`fullRowIndexEquiv`) and the G row
index `r : Fin n` (Laurent exponent `m = r - g`) are related by `ρ = lo + r` with the shift
`lo = rowShift p g = (p - g % p) % p`, which makes the block boundaries `ρ = k p` land on the
exponents `m = k p - (lo + g)`, multiples of `p`.  Hence the tiling pairs are the H-type pairs
`e_{c p + j'} ± e_{(c+1) p - j'}` of the source, with `c = k - (lo+g)/p`.

* `rowShift_lt`, `rowShift_dvd`: `lo < p`, `p ∣ lo + g`;
* `fullRowIndex_pair_plus/minus/center`: positions of the labels;
* `gRow_exponent`: the Laurent exponent of the actual row `r` read at tiling index `lo + r`;
* `physicalAtoms_apply`: coordinate of an atom at row `r` is the tiling coordinate at `lo + r`.
-/

namespace CatalanMeasure.GenD.Uniform.W.Thin
open CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W
noncomputable section

/-- The alignment shift of the tiling relative to the first G row. -/
def rowShift (p g : ℕ) : ℕ := (p - g % p) % p

theorem rowShift_lt {p : ℕ} (hp : 0 < p) (g : ℕ) : rowShift p g < p :=
  Nat.mod_lt _ hp

theorem rowShift_dvd {p : ℕ} (hp : 0 < p) (g : ℕ) : p ∣ rowShift p g + g := by
  unfold rowShift
  have h1 := Nat.mod_lt g hp
  have h2 := Nat.div_add_mod g p
  by_cases h0 : g % p = 0
  · rw [h0]
    simp only [Nat.sub_zero, Nat.mod_self, zero_add]
    exact (Nat.dvd_of_mod_eq_zero h0)
  · have : (p - g % p) % p = p - g % p := Nat.mod_eq_of_lt (by omega)
    rw [this]
    refine ⟨g / p + 1, ?_⟩
    have : p - g % p + g = p * (g / p) + p := by omega
    rw [this]; ring

theorem fullRowIndex_pair_plus (b h p : ℕ) (hp : p = 2 * h + 1) (k : Fin b) (j : Fin h) :
    (fullRowIndexEquiv b h p hp (.inr (k, j, true))).val = k.val * p + (j.val + 1) := rfl

theorem fullRowIndex_pair_minus (b h p : ℕ) (hp : p = 2 * h + 1) (k : Fin b) (j : Fin h) :
    (fullRowIndexEquiv b h p hp (.inr (k, j, false))).val = k.val * p + (p - j.val - 1) := rfl

theorem fullRowIndex_pair_minus' (b h p : ℕ) (hp : p = 2 * h + 1) (k : Fin b) (j : Fin h) :
    ((fullRowIndexEquiv b h p hp (.inr (k, j, false))).val : ℤ) =
      ((k.val : ℤ) + 1) * p - (j.val + 1) := by
  have := j.isLt
  rw [fullRowIndex_pair_minus]
  push_cast [Nat.cast_sub (show j.val + 1 ≤ p by omega), Nat.cast_sub (show (j.val : ℕ) ≤ p by omega)]
  ring_nf
  omega

theorem fullRowIndex_center (b h p : ℕ) (hp : p = 2 * h + 1) (k : Fin (b + 1)) :
    (fullRowIndexEquiv b h p hp (.inl k)).val = k.val * p := by
  show k.val * p + 0 = k.val * p
  rfl

/-- The Laurent exponent of the G row `r` equals its tiling position minus `lo + g`. -/
theorem gRow_exponent (p g lo r : ℕ) :
    ((r : ℤ) - g) = ((lo + r : ℕ) : ℤ) - ((lo + g : ℕ) : ℤ) := by
  push_cast; ring

/-- The coordinate of a physical atom at the G row `r` is the tiling coordinate at `lo + r`. -/
theorem physicalAtoms_apply {K : Type*} [Field K] (b h p : ℕ) (hp : p = 2 * h + 1)
    (h2 : (2 : K) ≠ 0) (lo n : ℕ) (hlen : lo + n ≤ b * p + 1)
    (S : Submodule K (TilingCoordinates (K := K) b h))
    (hS : ∀ x ∈ S, physicalTilingEquiv b h p hp h2 x ∈ intervalRows (K := K) lo n (b * p + 1))
    (x : S) (r : Fin n) :
    physicalAtoms b h p hp h2 lo n hlen S hS x r =
      physicalTilingEquiv b h p hp h2 x.1 ⟨lo + r.val, by have := r.isLt; omega⟩ :=
  supportedRows_apply _ lo n hlen S hS x r

#print axioms rowShift_dvd
#print axioms fullRowIndex_pair_minus'
end
end CatalanMeasure.GenD.Uniform.W.Thin
