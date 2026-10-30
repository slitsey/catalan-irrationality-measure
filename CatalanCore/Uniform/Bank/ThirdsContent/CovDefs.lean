module

public import CatalanCore.Uniform.Bank.ThirdsContent.OfBounds
public import CatalanCore.Arith.Hybrid.PieceTools

@[expose] public section
set_option Elab.async false

/-! # Integer-form piece covers (lane B, B4b)

`PCov Fr depth i p A B E D`: some `n` clears the member at the prime `p` and `D n <= A r + B p + E`
(`r = i.1`).  `cov_mk` turns it into the real `cov` hypothesis of `thirds_content_of_bounds` for the
template piece `mkPiece sn sd tn td A B E D`.  For `r < 10^6` the crude exponent (at most
`1.84e8`) is the witness (`pcov_small`). -/

namespace CatalanCore.Uniform.Bank.ThirdsContent
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.BankShared
  CatalanCore.Arith.Hybrid

/-- Integer-form cover of one member at one prime. -/
def PCov (Fr : Frame) (depth : ℕ) (i : (FamE Fr depth).ι) (p : ℕ) [Fact p.Prime] (A B E D : ℤ) : Prop :=
  ∃ n : ℕ, GLE p n ((FamE Fr depth).Q i) ∧
    D * (n : ℤ) ≤ A * (i.1 : ℤ) + B * (p : ℤ) + E

theorem cov_mk {Fr : Frame} {depth : ℕ} (i : (FamE Fr depth).ι) (p : ℕ) [Fact p.Prime]
    (sn sd tn td : ℕ) (A B E D : ℤ) (hD : 0 < D)
    (h : sn * i.1 / sd < p → p ≤ tn * i.1 / td → PCov Fr depth i p A B E D)
    (hs : ⌊(mkPiece sn sd tn td A B E D).s * (G310.scale i : ℝ)⌋₊ < p)
    (ht : p ≤ ⌊(mkPiece sn sd tn td A B E D).t * (G310.scale i : ℝ)⌋₊) :
    ∃ n : ℕ, GLE p n ((FamE Fr depth).Q i) ∧
      (n : ℝ) ≤ (mkPiece sn sd tn td A B E D).α * (G310.scale i : ℝ) +
        (mkPiece sn sd tn td A B E D).β * p + (mkPiece sn sd tn td A B E D).C := by
  have hs' : sn * i.1 / sd < p := by
    have : G310.scale i = i.1 := rfl
    rw [this, floor_mk_s] at hs; exact hs
  have ht' : p ≤ tn * i.1 / td := by
    have : G310.scale i = i.1 := rfl
    rw [this, floor_mk_t] at ht; exact ht
  obtain ⟨n, hn, hb⟩ := h hs' ht'
  refine ⟨n, hn, ?_⟩
  exact real_of_int_bound (x := n) (r := i.1) (p := p) D A B E hD hb

theorem Ecrude_small (cE : ℕ) (hcE : cE ≤ 25) (r p : ℕ) (hr : r < 10 ^ 6) (hp : 2 ≤ p) :
    Ecrude cE r p ≤ 188000000 := by
  unfold Ecrude
  have h1 : Nat.log p (14 * r) ≤ 23 := by
    refine (Nat.log_anti_left (by omega) hp).trans ?_
    have : Nat.log 2 (14 * r) < 24 := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0; simp
      · exact Nat.log_lt_of_lt_pow (by omega) (by
          have : 14 * r < 14 * 10 ^ 6 := by omega
          have h24 : (14 * 10 ^ 6 : ℕ) < 2 ^ 24 := by norm_num
          omega)
    omega
  have h2 : 3 * Nat.log p (14 * r) + cE ≤ 94 := by omega
  calc 2 * r * (3 * Nat.log p (14 * r) + cE) ≤ 2 * (10 ^ 6) * 94 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hr.le) h2
    _ = 188000000 := by norm_num

theorem pcov_small {Fr : Frame} {depth : ℕ} (hc : cFr Fr ≤ 25) (i : (FamE Fr depth).ι)
    (hi : (FamE Fr depth).Adm i) (hr : i.1 < 10 ^ 6) (p : ℕ) [Fact p.Prime] (hp : 2 ≤ p) (A B E D : ℤ)
    (hD : 0 < D) (hlin : D * 188000000 ≤ A * (i.1 : ℤ) + B * (p : ℤ) + E) :
    PCov Fr depth i p A B E D := by
  refine ⟨Ecrude (cFr Fr) i.1 p, altGeom_gle_Ecrude (3 / 10) c310_pos (by norm_num) Fr depth i hi.2 p, ?_⟩
  have h := Ecrude_small (cFr Fr) hc i.1 p hr hp
  have h' : ((Ecrude (cFr Fr) i.1 p : ℕ) : ℤ) ≤ 188000000 := by exact_mod_cast h
  nlinarith


/-- The `cov` obligation of `thirds_content_of_bounds` (modulus `6`) for one template piece. -/
def PieceCov (Fr : Frame) (depth : ℕ) (c : ZMod 6) (i : (FamE Fr depth).ι) (P : Piece) : Prop :=
  ∀ p : ℕ, ⌊P.s * (G310.scale i : ℝ)⌋₊ < p → p ≤ ⌊P.t * (G310.scale i : ℝ)⌋₊ → p.Prime →
    (p : ZMod 6) = c → ∀ [Fact p.Prime], ∃ n : ℕ, GLE p n ((FamE Fr depth).Q i) ∧
      (n : ℝ) ≤ P.α * (G310.scale i : ℝ) + P.β * p + P.C

theorem pieceCov_mk {Fr : Frame} {depth : ℕ} (c : ZMod 6) (i : (FamE Fr depth).ι)
    (sn sd tn td : ℕ) (A B E D : ℤ) (hD : 0 < D)
    (h : ∀ (p : ℕ) [Fact p.Prime], (p : ZMod 6) = c → sn * i.1 / sd < p → p ≤ tn * i.1 / td →
      PCov Fr depth i p A B E D) :
    PieceCov Fr depth c i (mkPiece sn sd tn td A B E D) := by
  intro p hs ht hp hpc hpf
  exact cov_mk i p sn sd tn td A B E D hD (fun h1 h2 => h p hpc h1 h2) hs ht

end CatalanCore.Uniform.Bank.ThirdsContent
