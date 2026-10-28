module

public import CatalanCore.Uniform.Content.UFMember.KillMom
public import CatalanCore.Uniform.Content.Shape.Alt
public import CatalanCore.Uniform.Content.Smith.TwoTerm

@[expose] public section

/-!
# UF member package, step (3): frame data of the Smith layer for the alternating geometry

For `altGeom c` at an even scale `r`, a two-term frame (`TwoTermData Fr q o`) and a prime `p`:

* `alt_xs_eq`, `alt_ys_eq`: border rows are `r + 2a`, border columns `r + 2b + 1`, `a, b < m`;
* `alt_hdist`: if `2m ≤ p` no border row is congruent to a border column modulo `p`;
* `alt_nodes_lt`: all nodes are `< r + 2m`;
* `altSmithJKDatum`: a `SmithJKDatum (altGeom c hc) Fr r p` from these facts, H3's
  `twoTermPoleData` (corrected condition `p² ∤ q t - o`) and ANY `J`-block datum `JB`;
  with the empty block (`altSmithJKDatum_empty`) every hypothesis is discharged by frame data
  and the price is `2|C| + m` (`altSmithJKDatum_empty_price`).

The only obligation left for the sevenths gain is the `J`-block datum itself (second order).
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.Smith
  CatalanCore.Arith.Hybrid.Periodic

namespace CatalanCore.Uniform.Content.UFMember

variable (c : ℚ) (hc : 0 < c) {r : ℕ}

theorem alt_xs_eq (hr : r % 2 = 0) (i : Fin ((altGeom c hc).geometry r).k) :
    ∃ a < (altGeom c hc).borderSize r, ((altGeom c hc).geometry r).xs i = r + 2 * a := by
  have h := Finset.orderEmbOfFin_mem ((altGeom c hc).geometry r).X' rfl i
  have hm : ∀ x, x ∈ ((altGeom c hc).geometry r).X' → x ∈ (Finset.range ((altGeom c hc).borderSize r)).image (fun i => r + 2 * i) := fun x hx => by rwa [altGeom_X c hc hr] at hx
  have h := Finset.mem_image.1 (hm _ h)
  obtain ⟨a, ha, he⟩ := h
  exact ⟨a, Finset.mem_range.1 ha, he.symm⟩

theorem alt_ys_eq (hr : r % 2 = 0) (i : Fin ((altGeom c hc).geometry r).k) :
    ∃ b < (altGeom c hc).borderSize r, ((altGeom c hc).geometry r).ys i = r + 2 * b + 1 := by
  have h := Finset.orderEmbOfFin_mem ((altGeom c hc).geometry r).Y'
    ((altGeom c hc).geometry r).card_eq.symm i
  have hm : ∀ x, x ∈ ((altGeom c hc).geometry r).Y' → x ∈ (Finset.range ((altGeom c hc).borderSize r)).image (fun i => r + 2 * i + 1) := fun x hx => by rwa [altGeom_Y c hc hr] at hx
  have h := Finset.mem_image.1 (hm _ h)
  obtain ⟨a, ha, he⟩ := h
  exact ⟨a, Finset.mem_range.1 ha, he.symm⟩

/-- Distinct border residues for the alternating geometry when `2m ≤ p`. -/
theorem alt_hdist (hr : r % 2 = 0) {p : ℕ} [Fact p.Prime]
    (hp : 2 * (altGeom c hc).borderSize r ≤ p) (i j : Fin ((altGeom c hc).geometry r).k) :
    ((((altGeom c hc).geometry r).xs i : ℕ) : ZMod p) ≠
      ((((altGeom c hc).geometry r).ys j : ℕ) : ZMod p) := by
  obtain ⟨a, ha, hx⟩ := alt_xs_eq c hc hr i
  obtain ⟨b, hb, hy⟩ := alt_ys_eq c hc hr j
  rw [hx, hy]
  intro h
  have h2 := (ZMod.intCast_eq_intCast_iff_dvd_sub ((r + 2 * a : ℕ) : ℤ) ((r + 2 * b + 1 : ℕ) : ℤ)
    p).1 (by exact_mod_cast h)
  obtain ⟨t, ht⟩ := h2
  push_cast at ht
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rcases lt_trichotomy t 0 with h3 | h3 | h3
  · have : (p : ℤ) * t ≤ -p := by nlinarith
    omega
  · subst h3; omega
  · have : (p : ℤ) ≤ p * t := by nlinarith
    omega

theorem alt_core_lt (a : ((altGeom c hc).geometry r).C) : (a : ℕ) < r := by
  have h := a.2
  have hm : ∀ x, x ∈ ((altGeom c hc).geometry r).C → x < r := fun x hx => by rwa [altGeom_C c hc r, Finset.mem_range] at hx
  exact hm _ h

/-- The Smith datum of the alternating geometry from frame data and a `J`-block datum. -/
noncomputable def altSmithJKDatum (hr : r % 2 = 0) {Fr : Frame} {q o p N : ℕ} [Fact p.Prime]
    (T : TwoTermData Fr q o) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0)
    (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N)
    (hp : 2 * (altGeom c hc).borderSize r ≤ p)
    (JB : (D : PoleData Fr p N) → (hc' : ∀ a : ((altGeom c hc).geometry r).C, (a : ℕ) < N) →
      (hx : ∀ i, ((altGeom c hc).geometry r).xs i < N) →
      (hy : ∀ j, ((altGeom c hc).geometry r).ys j < N) →
      JBlockKill (schurW (fun a : ((altGeom c hc).geometry r).C => (a : ℕ))
        ((altGeom c hc).geometry r).xs ((altGeom c hc).geometry r).ys
        (hint_of_poleData D hNp hc' hx hy))) :
    SmithJKDatum (altGeom c hc) Fr r p :=
  have D : PoleData Fr p N := twoTermPoleData T hNp.le hsq hnorm hnorm0
  have hc' : ∀ a : ((altGeom c hc).geometry r).C, (a : ℕ) < N := fun a => by
    have := alt_core_lt c hc a; omega
  have hx : ∀ i, ((altGeom c hc).geometry r).xs i < N := fun i => by
    obtain ⟨a, ha, he⟩ := alt_xs_eq c hc hr i; omega
  have hy : ∀ j, ((altGeom c hc).geometry r).ys j < N := fun j => by
    obtain ⟨b, hb, he⟩ := alt_ys_eq c hc hr j; omega
  { N := N
    D := D
    hN := hNp
    hc := hc'
    hx := hx
    hy := hy
    hdist := alt_hdist c hc hr hp
    J := JB D hc' hx hy }

/-- **Fully discharged sanity instance**: the empty `J`-block. -/
noncomputable def altSmithJKDatum_empty (hr : r % 2 = 0) {Fr : Frame} {q o p N : ℕ}
    [Fact p.Prime] (T : TwoTermData Fr q o) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0)
    (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N)
    (hp : 2 * (altGeom c hc).borderSize r ≤ p) : SmithJKDatum (altGeom c hc) Fr r p :=
  altSmithJKDatum c hc hr T hNp hsq hnorm hnorm0 hrN hp fun _ _ _ _ => JBlockKill.empty _

theorem altSmithJKDatum_empty_price (hr : r % 2 = 0) {Fr : Frame} {q o p N : ℕ}
    [Fact p.Prime] (T : TwoTermData Fr q o) (hNp : N < p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0)
    (hrN : r + 2 * (altGeom c hc).borderSize r ≤ N)
    (hp : 2 * (altGeom c hc).borderSize r ≤ p) :
    (altSmithJKDatum_empty c hc hr T hNp hsq hnorm hnorm0 hrN hp).price =
      2 * Fintype.card ((altGeom c hc).geometry r).C + ((altGeom c hc).geometry r).k :=
  SmithJKDatum.price_empty _ ⟨rfl, rfl⟩

end CatalanCore.Uniform.Content.UFMember
