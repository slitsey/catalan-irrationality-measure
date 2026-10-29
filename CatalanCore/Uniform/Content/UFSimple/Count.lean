module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic

@[expose] public section

/-!
# UF simplification (H18): the residue-union count of one window

For a residue window `W = [w₀, w₁]` (length `≤ p`) and the border `[r, r + 2m)` (`2m ≤ p`), both
inside a range where node differences are `< 2p`, the residues of `W` together with the residues of
the border nodes NOT congruent to `W` number at least

  `(w₁ + 1 - w₀) + (2m - β)`,   `β = ovl W + ovl (W + p) + ovl (W - p)`,

where `ovl [a, b] = |[r, r + 2m) ∩ [a, b]| = min (r + 2m) (b + 1) - max r a` (`card_Ico_filter_Icc`).
This is the `|I_J ∪ K|` count of the closed UF price: `I_J` is the image of the window and every
border node outside it is killed.
-/

namespace CatalanCore.Uniform.Content.UFSimple

open Finset

/-- `|[r, R) ∩ [a, b]|`. -/
def ovl (r R a b : ℕ) : ℕ := min R (b + 1) - max r a

theorem card_Ico_filter_Icc (r R a b : ℕ) :
    ((Finset.Ico r R).filter (fun v => a ≤ v ∧ v ≤ b)).card = ovl r R a b := by
  have : (Finset.Ico r R).filter (fun v => a ≤ v ∧ v ≤ b) = Finset.Ico (max r a) (min R (b + 1)) := by
    ext v; simp only [mem_filter, mem_Ico]; omega
  rw [this, Nat.card_Ico, ovl]

/-- Congruent naturals at distance `< 2p` differ by `0` or `± p`. -/
theorem modEq_cases {p v w : ℕ} (hp : 0 < p) (h1 : v < w + 2 * p) (h2 : w < v + 2 * p)
    (h : ((v : ℕ) : ZMod p) = ((w : ℕ) : ZMod p)) : v = w ∨ v = w + p ∨ v + p = w := by
  have hm : v % p = w % p := (ZMod.natCast_eq_natCast_iff' v w p).1 h
  have ev := Nat.div_add_mod v p
  have ew := Nat.div_add_mod w p
  rw [hm] at ev
  generalize w % p = ρ at ev ew
  generalize ha : v / p = a at ev
  generalize hb : w / p = b at ew
  rcases Nat.lt_or_ge a (b + 2) with hab | hab
  · rcases Nat.lt_or_ge b (a + 2) with hba | hba
    · have hc : a = b ∨ a = b + 1 ∨ b = a + 1 := by omega
      rcases hc with rfl | rfl | rfl
      · left; omega
      · right; left; rw [Nat.mul_add, Nat.mul_one] at ev; omega
      · right; right; rw [Nat.mul_add, Nat.mul_one] at ew; omega
    · have := Nat.mul_le_mul_left p hba
      rw [Nat.mul_add] at this
      omega
  · have := Nat.mul_le_mul_left p hab
    rw [Nat.mul_add] at this
    omega

/-- Residues are injective on a window of length `≤ p`. -/
theorem injOn_window {p a b : ℕ} (hp : 0 < p) (hab : b ≤ a + p) :
    Set.InjOn (fun t : ℕ => ((t : ℕ) : ZMod p)) (Finset.Ico a b : Set ℕ) := by
  intro x hx y hy hxy
  simp only [Finset.coe_Ico, Set.mem_Ico] at hx hy
  rcases modEq_cases hp (by omega) (by omega) hxy with h | h | h <;> omega

theorem card_image_window {p w0 w1 : ℕ} (hp : 0 < p) (hw : w1 < w0 + p) :
    ((Finset.Icc w0 w1).image (fun t : ℕ => ((t : ℕ) : ZMod p))).card = w1 + 1 - w0 := by
  have e : Finset.Icc w0 w1 = Finset.Ico w0 (w1 + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e, Finset.card_image_of_injOn (injOn_window hp (by omega)), Nat.card_Ico]

/-- Border nodes congruent to the window lie in one of its three translates. -/
theorem card_border_in_le {p r m w0 w1 : ℕ} (hp : 0 < p) (hR : r + 2 * m ≤ w0 + 2 * p)
    (hW : w1 < r + 2 * p) :
    ((Finset.Ico r (r + 2 * m)).filter
        (fun v => ∃ w ∈ Finset.Icc w0 w1, ((v : ℕ) : ZMod p) = ((w : ℕ) : ZMod p))).card ≤
      ovl r (r + 2 * m) w0 w1 + ovl r (r + 2 * m) (w0 + p) (w1 + p) +
        ovl r (r + 2 * m) (w0 - p) (w1 - p) := by
  classical
  have hsub : (Finset.Ico r (r + 2 * m)).filter
        (fun v => ∃ w ∈ Finset.Icc w0 w1, ((v : ℕ) : ZMod p) = ((w : ℕ) : ZMod p)) ⊆
      ((Finset.Ico r (r + 2 * m)).filter (fun v => w0 ≤ v ∧ v ≤ w1) ∪
        (Finset.Ico r (r + 2 * m)).filter (fun v => w0 + p ≤ v ∧ v ≤ w1 + p)) ∪
        (Finset.Ico r (r + 2 * m)).filter (fun v => w0 - p ≤ v ∧ v ≤ w1 - p) := by
    intro v hv
    obtain ⟨hv1, w, hw, hvw⟩ := Finset.mem_filter.1 hv
    have hv1' := Finset.mem_Ico.1 hv1
    have hw' := Finset.mem_Icc.1 hw
    simp only [Finset.mem_union, Finset.mem_filter]
    rcases modEq_cases hp (by omega) (by omega) hvw with h | h | h
    · left; left; exact ⟨hv1, by omega, by omega⟩
    · left; right; exact ⟨hv1, by omega, by omega⟩
    · right; exact ⟨hv1, by omega, by omega⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_union_le _ _).trans ?_
  rw [card_Ico_filter_Icc]
  have := Finset.card_union_le ((Finset.Ico r (r + 2 * m)).filter (fun v => w0 ≤ v ∧ v ≤ w1))
    ((Finset.Ico r (r + 2 * m)).filter (fun v => w0 + p ≤ v ∧ v ≤ w1 + p))
  rw [card_Ico_filter_Icc, card_Ico_filter_Icc] at this
  omega

/-- The border nodes whose residue is outside the window. -/
def outNodes (p r m w0 w1 : ℕ) : Finset ℕ :=
  (Finset.Ico r (r + 2 * m)).filter
    (fun v => ¬ ∃ w ∈ Finset.Icc w0 w1, ((v : ℕ) : ZMod p) = ((w : ℕ) : ZMod p))

theorem mem_outNodes {p r m w0 w1 v : ℕ} :
    v ∈ outNodes p r m w0 w1 ↔ (r ≤ v ∧ v < r + 2 * m) ∧
      ¬ ∃ w ∈ Finset.Icc w0 w1, ((v : ℕ) : ZMod p) = ((w : ℕ) : ZMod p) := by
  unfold outNodes
  rw [Finset.mem_filter, Finset.mem_Ico]

/-- **The residue-union count of a window and its outside border.** -/
theorem card_union_window {p r m w0 w1 : ℕ} (hp : 0 < p) (hw : w1 < w0 + p) (hm : 2 * m ≤ p)
    (hR : r + 2 * m ≤ w0 + 2 * p) (hW : w1 < r + 2 * p) :
    (w1 + 1 - w0) + (2 * m - (ovl r (r + 2 * m) w0 w1 + ovl r (r + 2 * m) (w0 + p) (w1 + p) +
        ovl r (r + 2 * m) (w0 - p) (w1 - p))) ≤
      ((Finset.Icc w0 w1).image (fun t : ℕ => ((t : ℕ) : ZMod p)) ∪
        (outNodes p r m w0 w1).image (fun t : ℕ => ((t : ℕ) : ZMod p))).card := by
  classical
  have hD : Disjoint ((Finset.Icc w0 w1).image (fun t : ℕ => ((t : ℕ) : ZMod p)))
      ((outNodes p r m w0 w1).image (fun t : ℕ => ((t : ℕ) : ZMod p))) := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hz1
    obtain ⟨v, hv, hvw⟩ := Finset.mem_image.1 hz2
    exact (mem_outNodes.1 hv).2 ⟨w, hw, hvw⟩
  rw [Finset.card_union_of_disjoint hD, card_image_window hp hw]
  have hsub : outNodes p r m w0 w1 ⊆ Finset.Ico r (r + 2 * m) := by
    intro v hv; exact Finset.mem_Ico.2 (mem_outNodes.1 hv).1
  have hinj : Set.InjOn (fun t : ℕ => ((t : ℕ) : ZMod p)) (outNodes p r m w0 w1 : Set ℕ) :=
    (injOn_window (a := r) (b := r + 2 * m) hp (by omega)).mono (by exact_mod_cast hsub)
  rw [Finset.card_image_of_injOn hinj]
  have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.Ico r (r + 2 * m))
    (fun v => ∃ w ∈ Finset.Icc w0 w1, ((v : ℕ) : ZMod p) = ((w : ℕ) : ZMod p))
  have e : (Finset.Ico r (r + 2 * m)).filter
      (fun v => ¬ ∃ w ∈ Finset.Icc w0 w1, ((v : ℕ) : ZMod p) = ((w : ℕ) : ZMod p)) =
      outNodes p r m w0 w1 := rfl
  rw [e, Nat.card_Ico] at hsplit
  have := card_border_in_le (m := m) hp hR hW
  omega

end CatalanCore.Uniform.Content.UFSimple
