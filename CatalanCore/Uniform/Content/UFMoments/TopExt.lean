module

public import CatalanCore.Uniform.Content.UFMoments.AltFinal
public import CatalanCore.Uniform.Content.Smith.Weights

@[expose] public section

/-!
# Top extensions (Theorem UF (ii)): the derived weight vanishes at residues whose chain is the
# chain of `J` plus the image of the representative node

For the core `[0, r)` and a backward shift `δ` with `a* = t₀ - δ < r` (the shifted representative
lands in the core), the fiber of `a*` is `{a*} ∪ (chain(t₀) - δ)` (`topEquiv`).  Its fiber moment
equals that of `t₀` by H2's `gamma_topExt` (the top condition is the residue of `own_dir_zero`),
and the cyclic step agrees, so `vS7(a*) = 0` (`vS7_topext`).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFMoments

variable {p : ℕ} [hp : Fact p.Prime]

theorem te_down {j r t0 δ : ℕ} (hj : j < r) (hr : r ≤ t0) (hq : (t0 - δ) / p = t0 / p)
    (hcong : ((j : ℕ) : ZMod p) = ((t0 : ℕ) : ZMod p)) :
    δ ≤ j ∧ ((j - δ : ℕ) : ZMod p) = ((t0 - δ : ℕ) : ZMod p) ∧ j - δ ≠ t0 - δ := by
  obtain ⟨k, hk⟩ := dvd_sub_of_cast_eq hcong (by omega)
  have hp0 := hp.out.pos
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; omega
    · exact h
  have h2 : k ≤ t0 / p := (Nat.le_div_iff_mul_le hp0).2 (by nlinarith)
  rw [← hq] at h2
  have h3 : k * p ≤ (t0 - δ) / p * p := Nat.mul_le_mul_right p h2
  have h4 := Nat.div_mul_le_self (t0 - δ) p
  have hkt : p * k ≤ t0 - δ := by nlinarith
  have hpk : p ≤ p * k := Nat.le_mul_of_pos_right p hk1
  refine ⟨by omega, ?_, by omega⟩
  rw [show j - δ = (t0 - δ) - p * k by omega, Nat.cast_sub hkt]
  push_cast; simp

theorem te_up {x r t0 δ : ℕ} (hx : x < r) (hlt : t0 - δ < r) (hr3 : r ≤ t0 - δ + p)
    (htp : t0 < r + p) (hδ : δ ≤ t0)
    (hcong : ((x : ℕ) : ZMod p) = ((t0 - δ : ℕ) : ZMod p)) (hne : x ≠ t0 - δ) :
    x + δ < r ∧ ((x + δ : ℕ) : ZMod p) = ((t0 : ℕ) : ZMod p) := by
  have hle : x ≤ t0 - δ := by
    by_contra h
    push Not at h
    obtain ⟨k, hk⟩ := dvd_sub_of_cast_eq hcong.symm h.le
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h' | h'
      · subst h'; omega
      · exact h'
    have : p ≤ p * k := Nat.le_mul_of_pos_right p hk1
    omega
  obtain ⟨k, hk⟩ := dvd_sub_of_cast_eq hcong hle
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h' | h'
    · subst h'; omega
    · exact h'
  have : p ≤ p * k := Nat.le_mul_of_pos_right p hk1
  refine ⟨by omega, ?_⟩
  have e : x + δ = t0 - p * k := by omega
  rw [e, Nat.cast_sub (by omega)]
  push_cast; simp

/-- The top-extension equivalence: fiber of `a* = t₀ - δ` ≃ `Option` (fiber of `t₀`). -/
noncomputable def topEquiv {r : ℕ} (C : Finset ℕ) (hC : C = Finset.range r) (t0 δ : ℕ)
    (hr : r ≤ t0) (hδ : δ ≤ t0) (hlt : t0 - δ < r) (hr3 : r ≤ t0 - δ + p) (htp : t0 < r + p)
    (hq : (t0 - δ) / p = t0 / p) :
    {a : C // colOf (p := p) (fun a : C => (a : ℕ)) a = ((t0 - δ : ℕ) : ZMod p)} ≃
      Option {a : C // colOf (p := p) (fun a : C => (a : ℕ)) a = ((t0 : ℕ) : ZMod p)} where
  toFun x :=
    if h : ((x.1 : ℕ) = t0 - δ) then none else
      have hx := Finset.mem_range.1 ((Finset.ext_iff.1 hC (x.1 : ℕ)).1 x.1.2)
      have hu := te_up hx hlt hr3 htp hδ x.2 h
      some ⟨⟨(x.1 : ℕ) + δ, (Finset.ext_iff.1 hC _).2 (Finset.mem_range.2 hu.1)⟩, hu.2⟩
  invFun o := o.elim ⟨⟨t0 - δ, (Finset.ext_iff.1 hC _).2 (Finset.mem_range.2 hlt)⟩, rfl⟩
    (fun j =>
      have hj := Finset.mem_range.1 ((Finset.ext_iff.1 hC (j.1 : ℕ)).1 j.1.2)
      have hd := te_down hj hr hq j.2
      ⟨⟨(j.1 : ℕ) - δ, (Finset.ext_iff.1 hC _).2 (Finset.mem_range.2 (by omega))⟩, hd.2.1⟩)
  left_inv x := by
    by_cases h : (x.1 : ℕ) = t0 - δ
    · simp only [h, ↓reduceDIte, Option.elim_none]
      apply Subtype.ext; apply Subtype.ext; exact h.symm
    · simp only [h, ↓reduceDIte, Option.elim_some]
      apply Subtype.ext; apply Subtype.ext
      show (x.1 : ℕ) + δ - δ = x.1
      omega
  right_inv o := by
    cases o with
    | none => simp
    | some j =>
      have hj := Finset.mem_range.1 ((Finset.ext_iff.1 hC (j.1 : ℕ)).1 j.1.2)
      have hd := te_down hj hr hq j.2
      simp only [Option.elim_some, hd.2.2, ↓reduceDIte, Option.some.injEq]
      apply Subtype.ext; apply Subtype.ext
      show (j.1 : ℕ) - δ + δ = j.1
      omega

end CatalanCore.Uniform.Content.UFMoments
