module

public import CatalanCore.Uniform.Bank.Chi3Content.PoleData
public import CatalanCore.Uniform.Content.Layers.DelWitness
public import CatalanCore.Uniform.Content.Wire.M3D
public import CatalanCore.Rect.MinorContent
public import CatalanFrames.P6Hybrid.Level

@[expose] public section

/-!
# The M3D layer on the chi_{-3} common-minor family (lane B, B3c)

`M3Hyp r m p a b`: the hypotheses of `M3D_debit` for the chi_{-3} frame (`chi3PoleData`) with witness
segment `[a, b)`.  `m3_gle_minor`: every common-node minor `commonMinorPoly p6Frame r m s` is
`p^(m3price)`-integral.  `nocut_window`: the cut-freeness of a segment from four consecutive
multiples (of `p`, of `p` on the `3t-2` scale, on the `2t-1` scale, and shifted by `r`).
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Rect CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Arith.Hybrid.ChainClasses CatalanFrames.P6
  CatalanCore.Uniform.Content.Layers.Del CatalanCore.Uniform.Content.Wire

set_option maxHeartbeats 1600000

namespace CatalanCore.Uniform.Bank.Chi3Content

/-- Hypotheses of M3D for the chi_{-3} frame at `(r, m, p)` with segment `[a, b)`. -/
structure M3Hyp (r m p a b : ℕ) : Prop where
  prime : p.Prime
  p5 : 5 ≤ p
  hN : 3 * (r + 2 * m) < p * p
  hra : r ≤ a
  hab : a ≤ b
  hb : b ≤ r + 2 * m
  hbp : b ≤ r + p
  hj : max a (r + 2 * m - p) ≤ b
  hcut : ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
    NoCut (Cut p r (chi3Sing p)) (min (x : ℤ) y) (max (x : ℤ) y)

/-- The full-member price of M3D. -/
def m3price (r m p a b : ℕ) : ℕ := 2 * r + (2 * m - (b - max a (r + 2 * m - p)))

theorem m3_gle_minor {r m p a b : ℕ} [Fact p.Prime] (h : M3Hyp r m p a b) (s : Finset (Fin r)) :
    GLE p (m3price r m p a b) (commonMinorPoly p6Frame r m s) := by
  classical
  let I : Finset ℕ := (Finset.univ \ s).image (fun c : Fin r => c.val)
  have hI : ∀ u ∈ I, u < r := by
    intro u hu
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hu
    exact c.2
  have hD := M3D_debit (chi3PoleData h.p5 h.hN) (by have := h.hN; omega) I hI h.hra h.hab h.hb h.hbp h.hj h.hcut
  have hiff : ∀ c : Fin r, c ∈ s ↔ c.val ∉ I := by
    intro c
    constructor
    · intro hc hI'
      obtain ⟨d, hd, hdc⟩ := Finset.mem_image.mp hI'
      have : d = c := Fin.ext hdc
      subst this
      simp at hd; exact hd hc
    · intro hc
      by_contra hcs
      exact hc (Finset.mem_image.mpr ⟨c, by simpa using hcs, rfl⟩)
  let f : s ≃ {c : Fin r // c.val ∉ I} := Equiv.subtypeEquivRight hiff
  have hdet := det_fullN_reindex p6Frame (fun i : {c : Fin r // c.val ∉ I} => i.1.val)
    (fun a : s => (a.1 : Fin r).val) f (fun a => rfl)
    (fun i : Fin m => r + 2 * (i : ℕ)) (fun i : Fin m => r + 2 * (i : ℕ) + 1)
  have hcm : commonMinorPoly p6Frame r m s = (FullN p6Frame (fun i : {c : Fin r // c.val ∉ I} => i.1.val)
      (fun i : Fin m => r + 2 * i.val) (fun j : Fin m => r + 2 * j.val + 1) (X : ℚ[X])).det := by
    unfold commonMinorPoly
    exact hdet
  rw [hcm]
  have hk : I.card ≤ r := by
    have : I ⊆ Finset.range r := fun u hu => Finset.mem_range.mpr (hI u hu)
    simpa using Finset.card_le_card this
  unfold m3price
  exact hD.mono (by omega)

/-- Cut-freeness of a segment `(a, b)`: four gaps between consecutive multiples; on the `3t-2` and
`2t-1` scales the gap may contain up to `K1`, `K2` multiples of `p` that do not give an integer `t`. -/
theorem nocut_window (p r a b : ℕ) (hp : 0 < p) (n0 n1 K1 n2 K2 n3 : ℕ)
    (h0 : n0 * p ≤ a ∧ b ≤ (n0 + 1) * p)
    (h1 : n1 * p + 2 ≤ 3 * a ∧ 3 * b ≤ (n1 + K1 + 1) * p + 2)
    (m1 : ∀ i : ℕ, 1 ≤ i → i ≤ K1 → ((n1 + i) * p + 2) % 3 ≠ 0)
    (h2 : n2 * p + 1 ≤ 2 * a ∧ 2 * b ≤ (n2 + K2 + 1) * p + 1)
    (m2 : ∀ i : ℕ, 1 ≤ i → i ≤ K2 → ((n2 + i) * p + 1) % 2 ≠ 0)
    (h3 : r + n3 * p ≤ a ∧ b ≤ r + (n3 + 1) * p) :
    ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut p r (chi3Sing p)) (min (x : ℤ) y) (max (x : ℤ) y) := by
  intro x y hax hxb hay hyb t hat htb hcut
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have ha : (a : ℤ) < t := by
    have : (a : ℤ) ≤ min (x : ℤ) y := le_min (by exact_mod_cast hax) (by exact_mod_cast hay)
    omega
  have hb : t < b := by
    have hx : (x : ℤ) < b := by exact_mod_cast hxb
    have hy : (y : ℤ) < b := by exact_mod_cast hyb
    have : max (x : ℤ) y ≤ (b : ℤ) - 1 := max_le (by omega) (by omega)
    omega
  have bet : ∀ (n j : ℤ), n * p < j * p → j * p < (n + 1) * p → False := by
    intro n j h1 h2
    have u : n < j := lt_of_mul_lt_mul_right h1 hpz.le
    have v : j < n + 1 := lt_of_mul_lt_mul_right h2 hpz.le
    omega
  obtain ⟨h0a, h0b⟩ := h0
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  obtain ⟨h3a, h3b⟩ := h3
  have c0a : ((n0 : ℤ)) * p ≤ a := by exact_mod_cast h0a
  have c0b : (b : ℤ) ≤ ((n0 : ℤ) + 1) * p := by exact_mod_cast h0b
  have c1a : ((n1 : ℤ)) * p + 2 ≤ 3 * a := by exact_mod_cast h1a
  have c1b : 3 * (b : ℤ) ≤ ((n1 : ℤ) + K1 + 1) * p + 2 := by exact_mod_cast h1b
  have c2a : ((n2 : ℤ)) * p + 1 ≤ 2 * a := by exact_mod_cast h2a
  have c2b : 2 * (b : ℤ) ≤ ((n2 : ℤ) + K2 + 1) * p + 1 := by exact_mod_cast h2b
  have c3a : (r : ℤ) + ((n3 : ℤ)) * p ≤ a := by exact_mod_cast h3a
  have c3b : (b : ℤ) ≤ r + ((n3 : ℤ) + 1) * p := by exact_mod_cast h3b
  rcases hcut with (⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩) | ⟨j, hj⟩ | ⟨j, hj⟩
  · exact bet n0 j (by linarith) (by linarith)
  · -- 3t - 2 = j p
    have l1 : (n1 : ℤ) * p < j * p := by linarith
    have l2 : j * p < ((n1 : ℤ) + K1 + 1) * p := by linarith
    have u : (n1 : ℤ) < j := lt_of_mul_lt_mul_right l1 hpz.le
    have v : j < (n1 : ℤ) + K1 + 1 := lt_of_mul_lt_mul_right l2 hpz.le
    obtain ⟨i, hi⟩ : ∃ i : ℕ, j = (n1 : ℤ) + i := ⟨(j - n1).toNat, by omega⟩
    have hz := m1 i (by omega) (by omega)
    have hz2 : (((n1 + i) * p + 2 : ℕ) : ℤ) = 3 * t := by
      push_cast; rw [← hi]; linarith
    generalize (n1 + i) * p = X at hz hz2
    omega
  · -- 2t - 1 = j p
    have l1 : (n2 : ℤ) * p < j * p := by linarith
    have l2 : j * p < ((n2 : ℤ) + K2 + 1) * p := by linarith
    have u : (n2 : ℤ) < j := lt_of_mul_lt_mul_right l1 hpz.le
    have v : j < (n2 : ℤ) + K2 + 1 := lt_of_mul_lt_mul_right l2 hpz.le
    obtain ⟨i, hi⟩ : ∃ i : ℕ, j = (n2 : ℤ) + i := ⟨(j - n2).toNat, by omega⟩
    have hz := m2 i (by omega) (by omega)
    have hz2 : (((n2 + i) * p + 1 : ℕ) : ℤ) = 2 * t := by
      push_cast; rw [← hi]; linarith
    generalize (n2 + i) * p = X at hz hz2
    omega
  · exact bet n0 j (by linarith) (by linarith)
  · exact bet n3 j (by linarith) (by linarith)

end CatalanCore.Uniform.Bank.Chi3Content
