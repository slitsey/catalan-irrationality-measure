module

public import CatalanCore.Uniform.Content.UFMoments.S7Final
public import CatalanCore.Uniform.Content.UFMember.AltData

@[expose] public section

/-!
# (S7-Lean) on the alternating geometry: joint types are shifts

For the core `[0, r)` and border nodes `t₀ ≤ t < r + p` with `r ≤ t₀` and `⌊t/p⌋ = ⌊t₀/p⌋`, the own
chain of `t` is the `(t - t₀)`-shift of that of `t₀` (`chainShift`), and if no singular index lies in
`(t₀, t]` then every window is nonsingular (periodicity).  Hence `ShiftData` holds
(`alt_shiftData`) and `s7_twoTerm` applies to any such window of border nodes.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFMoments

variable {p : ℕ} [hp : Fact p.Prime]

theorem dvd_sub_of_cast_eq {a t : ℕ} (h : ((a : ℕ) : ZMod p) = ((t : ℕ) : ZMod p)) (hat : a ≤ t) :
    ∃ j, t = a + p * j := by
  obtain ⟨j, hj⟩ := (Nat.modEq_iff_dvd' hat).1 ((ZMod.natCast_eq_natCast_iff a t p).1 h)
  exact ⟨j, by omega⟩

theorem down_ok {x r t0 Δ : ℕ} (hx : x < r) (hr : r ≤ t0) (hq : (t0 + Δ) / p = t0 / p)
    (hcong : ((x : ℕ) : ZMod p) = ((t0 + Δ : ℕ) : ZMod p)) :
    Δ ≤ x ∧ ((x - Δ : ℕ) : ZMod p) = ((t0 : ℕ) : ZMod p) := by
  obtain ⟨j, hj⟩ := dvd_sub_of_cast_eq hcong (by omega)
  have hp0 := hp.out.pos
  have h2 : j ≤ (t0 + Δ) / p := (Nat.le_div_iff_mul_le hp0).2 (by nlinarith)
  rw [hq] at h2
  have h3 : j * p ≤ t0 / p * p := Nat.mul_le_mul_right p h2
  have h4 := Nat.div_mul_le_self t0 p
  have hjt : p * j ≤ t0 := by nlinarith
  refine ⟨by omega, ?_⟩
  rw [show x - Δ = t0 - p * j by omega, Nat.cast_sub hjt]
  push_cast; simp

theorem up_ok {y r t0 Δ : ℕ} (hy : y < r) (hr : r ≤ t0) (htp : t0 + Δ < r + p)
    (hcong : ((y : ℕ) : ZMod p) = ((t0 : ℕ) : ZMod p)) :
    y + Δ < r ∧ ((y + Δ : ℕ) : ZMod p) = ((t0 + Δ : ℕ) : ZMod p) := by
  obtain ⟨j, hj⟩ := dvd_sub_of_cast_eq hcong (by omega)
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; omega
    · exact h
  have : p ≤ p * j := Nat.le_mul_of_pos_right p hj1
  refine ⟨by omega, ?_⟩
  push_cast; rw [hcong]

/-- The chain-shift equivalence on the core `C = [0, r)`. -/
noncomputable def chainShift {r : ℕ} (C : Finset ℕ) (hC : C = Finset.range r) (t0 Δ : ℕ)
    (hr : r ≤ t0) (htp : t0 + Δ < r + p) (hq : (t0 + Δ) / p = t0 / p) :
    {a : C // colOf (p := p) (fun a : C => (a : ℕ)) a = ((t0 + Δ : ℕ) : ZMod p)} ≃
      {a : C // colOf (p := p) (fun a : C => (a : ℕ)) a = ((t0 : ℕ) : ZMod p)} where
  toFun a :=
    have ha := Finset.mem_range.1 ((Finset.ext_iff.1 hC (a.1 : ℕ)).1 a.1.2)
    have h := down_ok ha hr hq a.2
    ⟨⟨(a.1 : ℕ) - Δ, (Finset.ext_iff.1 hC _).2 (Finset.mem_range.2 (by omega))⟩, h.2⟩
  invFun b :=
    have hb := Finset.mem_range.1 ((Finset.ext_iff.1 hC (b.1 : ℕ)).1 b.1.2)
    have h := up_ok hb hr htp b.2
    ⟨⟨(b.1 : ℕ) + Δ, (Finset.ext_iff.1 hC _).2 (Finset.mem_range.2 h.1)⟩, h.2⟩
  left_inv a := by
    have ha := Finset.mem_range.1 ((Finset.ext_iff.1 hC (a.1 : ℕ)).1 a.1.2)
    have h := down_ok ha hr hq a.2
    apply Subtype.ext; apply Subtype.ext
    show (a.1 : ℕ) - Δ + Δ = a.1
    omega
  right_inv b := by
    apply Subtype.ext; apply Subtype.ext
    show (b.1 : ℕ) + Δ - Δ = b.1
    omega

theorem chainShift_symm {r : ℕ} (C : Finset ℕ) (hC : C = Finset.range r) (t0 Δ : ℕ)
    (hr : r ≤ t0) (htp : t0 + Δ < r + p) (hq : (t0 + Δ) / p = t0 / p) (i) :
    (((chainShift (p := p) C hC t0 Δ hr htp hq).symm i).1 : ℕ) = (i.1 : ℕ) + Δ := rfl

section Frame

variable {Fr : Frame} {q o N : ℕ}

/-- Nonsingular windows propagate down the chain (periodicity of the singular set). -/
theorem window_periodic (T : TwoTermData Fr q o) (hN : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) {x t0 Δ : ℕ} (hxt : x ≤ t0)
    (hcong : ((x : ℕ) : ZMod p) = ((t0 : ℕ) : ZMod p))
    (hw : NoSingWin (twoTermPoleData T hN hsq hnorm hnorm0) t0 Δ) :
    NoSingWin (twoTermPoleData T hN hsq hnorm hnorm0) x Δ := by
  obtain ⟨j, hj⟩ := dvd_sub_of_cast_eq hcong hxt
  intro k hk1 hk2 hs
  have hs' : ttSing p q o ((k : ℤ) + (j : ℤ) * p) := (ttSing_periodic p q o k j).2 hs
  have := hw (k + p * j) (by omega) (by omega)
  apply this
  have e : (((k + p * j : ℕ)) : ℤ) = (k : ℤ) + (j : ℤ) * p := by push_cast; ring
  rw [e]; exact hs'

/-- **Joint types of the alternating geometry are chain shifts.** -/
theorem alt_shiftData (T : TwoTermData Fr q o) (hN : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) {r : ℕ} (C : Finset ℕ) (hC : C = Finset.range r) (t0 Δ : ℕ)
    (hr : r ≤ t0) (htp : t0 + Δ < r + p) (hq : (t0 + Δ) / p = t0 / p)
    (hw : NoSingWin (twoTermPoleData T hN hsq hnorm hnorm0) t0 Δ) :
    ShiftData (twoTermPoleData T hN hsq hnorm hnorm0) (fun a : C => (a : ℕ)) t0 (t0 + Δ) := by
  refine ⟨Δ, rfl, hw, chainShift C hC t0 Δ hr htp hq, fun i => rfl, fun i => ?_⟩
  have hx := Finset.mem_range.1 ((Finset.ext_iff.1 hC (i.1 : ℕ)).1 i.1.2)
  exact window_periodic (x := (i.1 : ℕ)) T hN hsq hnorm hnorm0 (by omega) i.2 hw

end Frame

end CatalanCore.Uniform.Content.UFMoments
