module

public import CatalanCore.Arith.Hybrid.LemmaE.EntriesE
public import CatalanCore.Arith.Hybrid.DefBLam

@[expose] public section

/-!
# Lemma E, class 1: the reduction matrix `BE` and the lifts (`hred`)

`BE` is the matrix over `𝔽_p(X)` indexed by `Fin r ⊕ Fin m` with entries `rfC (TE ...)` plus `X` on
the weight-`0` diagonal.  `hred_E`: the scaled entries `p^{wE + wE} Full_ab` lift to integral
polynomials with reduction `BE a b`.  Evaluation lemmas for `TE` on the label classes used in the
rank count.
-/

open Finset Polynomial CatalanCore CatalanCore.Basic

namespace CatalanCore.Arith.Hybrid

section

variable {p : ℕ} [Fact p.Prime] {Fr : Frame} {r m j k : ℕ}

/-- The reduction matrix of Lemma E (class 1). -/
noncomputable def BE (p j r m k : ℕ) [Fact p.Prime] :
    Matrix (Fin r ⊕ Fin m) (Fin r ⊕ Fin m) (RatFunc (ZMod p)) :=
  Matrix.of fun a b => rfC p (TE p j r k (Frame.hybRow r m a) (Frame.hybCol r m b)) +
    (match a, b with
      | Sum.inl c, Sum.inl c' => if c = c' ∧ wE p r k (c : ℕ) = 0 then rfX p else 0
      | _, _ => 0)

lemma lift_offdiagE (hL : LamData Fr) (S : ESetup p r m j k) {A B : ℕ} (hAB : A ≠ B)
    (hA : A < r + 2 * m) (hB : B < r + 2 * m) :
    ∃ g : (LocRing p)[X], toQ p g =
      C ((p : ℚ) ^ (wE p r k A + wE p r k B)) * C (Fr.Mn A B) ∧
      phiP p g = rfC p (TE p j r k A B) := by
  rcases lt_or_gt_of_ne hAB with h | h
  · have := good_TEo hL S h hB
    have e : TE p j r k A B = TEo p j k (wE p r k A + wE p r k B) A B := by
      unfold TE; rw [if_pos h]
    rw [e]; exact lift_good p this
  · have := good_TEo hL S h hA
    have e : TE p j r k A B = TEo p j k (wE p r k B + wE p r k A) B A := by
      unfold TE; rw [if_neg (by omega), if_pos h, Nat.add_comm (wE p r k A)]
    rw [e, Nat.add_comm (wE p r k A), Mn_symm]; exact lift_good p this

/-- **The entries of `Full(X)` reduce to `BE`.** -/
theorem hred_E (hL : LamData Fr) (S : ESetup p r m j k) (a b : Fin r ⊕ Fin m) :
    ∃ g : (LocRing p)[X], toQ p g =
      C ((p : ℚ) ^ (wE p r k (Frame.hybRow r m a) + wE p r k (Frame.hybCol r m b))) *
        fullEntry Fr r m a b ∧ phiP p g = BE p j r m k a b := by
  have hA := hybRow_lt (r := r) (m := m) a
  have hB := hybCol_lt (r := r) (m := m) b
  rcases a with c | i <;> rcases b with c' | i'
  · by_cases hcc : c = c'
    · subst hcc
      have hcr := c.2
      have hgood := good_TEd hL S (A := (c : ℕ)) hcr
      obtain ⟨g, h1, h2⟩ := exists_lift_diag p (wE p r k c + wE p r k c) (Fr.Mn c c) hgood.1
      refine ⟨g, ?_, ?_⟩
      · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
      · rw [h2]
        have e1 : redQ p ⟨_, hgood.1⟩ = TEd p j k (wE p r k c + wE p r k c) c := hgood.2
        rw [e1]
        have e2 : TE p j r k c c = TEd p j k (wE p r k c + wE p r k c) c := by
          unfold TE; rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
        have e3 : wE p r k (c : ℕ) + wE p r k (c : ℕ) = 0 ↔ wE p r k (c : ℕ) = 0 := by omega
        simp only [BE, Matrix.of_apply, Frame.hybRow, Frame.hybCol, Sum.elim_inl, e2, true_and, e3]
        rw [add_comm]
    · have hne : (c : ℕ) ≠ c' := fun h => hcc (Fin.ext h)
      obtain ⟨g, h1, h2⟩ := lift_offdiagE hL S hne (by have := c.2; omega) (by have := c'.2; omega)
      refine ⟨g, ?_, ?_⟩
      · rw [h1]; simp [fullEntry, hcc, Frame.hybRow, Frame.hybCol]
      · rw [h2]; simp [BE, hcc, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := lift_offdiagE hL S (A := c) (B := r + 2 * (i' : ℕ) + 1)
      (by have := c.2; omega) (by have := c.2; omega) hB
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BE, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := lift_offdiagE hL S (A := r + 2 * (i : ℕ)) (B := c')
      (by have := c'.2; omega) hA (by have := c'.2; omega)
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BE, Frame.hybRow, Frame.hybCol]
  · obtain ⟨g, h1, h2⟩ := lift_offdiagE hL S (A := r + 2 * (i : ℕ)) (B := r + 2 * (i' : ℕ) + 1)
      (by omega) hA hB
    refine ⟨g, ?_, ?_⟩
    · rw [h1]; simp [fullEntry, Frame.hybRow, Frame.hybCol]
    · rw [h2]; simp [BE, Frame.hybRow, Frame.hybCol]

end

end CatalanCore.Arith.Hybrid
