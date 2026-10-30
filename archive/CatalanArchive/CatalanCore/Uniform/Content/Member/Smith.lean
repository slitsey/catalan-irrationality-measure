module

public import CatalanCore.Uniform.Content.Member.Combine

@[expose] public section

/-!
# Theorem SD (lane H5): the Smith layer of a deletion member

`denexp P_{r,I} ≤ max(0, 2|C| + m - max(G0, σ, 2σ - s) + k)`.

Proved here, for the member's own matrix and with no inheritance of the full determinant:

* `sd_first_layer`: the first Smith corank `G0` of the full matrix `A = p² Φ` (rank of `A mod p`
  at most `n - G0`) prices every member at `2n - G0 + k` (`k = |C| - |S|`): Lemma R' plus
  Lemma M with the constant potentials `u = v = 1`.
* the tropical and rank layers (`member_gle_trop`, `member_gle_rank`): debit 0.

Pending (lane H2, UF): the two-level terms `σ` and `2σ - s`.  They enter as the hypothesis of
`DebitLayer.smithSD`, a GLE bound for the member at `p` with the debit `k`.
-/

open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid CatalanCore.Rect
  CatalanCore.Uniform

namespace CatalanCore.Uniform.Content.Member

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **SD, first Smith layer.**  If `A = p² Φ` has the integral lift `Bl` (entries
`p² · entry`) and the reduction has rank `≤ n - G0`, every deletion member has
`GLE p (2n - G0 + k)`, `n = |C| + m` the size of the full matrix and `k = |C| - |S|`. -/
theorem sd_first_layer (Fr : Frame) (common : ι → ℕ) (xs ys : κ → ℕ) (S : Finset ι)
    {p : ℕ} [Fact p.Prime] (Bl : Matrix (ι ⊕ κ) (ι ⊕ κ) (LocRing p)[X])
    (hB : ∀ i j, toQ p (Bl i j) = C ((p : ℚ) ^ 2) * FullN Fr common xs ys (X : ℚ[X]) i j)
    (G0 : ℕ) (hrk : (Bl.map (phiP p)).rank + G0 ≤ Fintype.card (ι ⊕ κ)) :
    GLE p ((2 * Fintype.card (ι ⊕ κ) - G0) + (Fintype.card ι - S.card))
      (FullN Fr (fun a : S => common a.1) xs ys (X : ℚ[X])).det := by
  have h := lpd_member_debit Fr common xs ys S (fun _ => 1) (fun _ => 1) Bl
    (by intro i j; rw [hB i j]) G0 hrk
  simpa [two_mul] using h

/-- The full-member Smith price `max(0, 2|C| + m - gain)` at scale `r`. -/
def sdBase (G : BlockGeom) (gain : ℕ → ℕ → ℕ) (r p : ℕ) : ℕ :=
  2 * (G.geometry r).C.card + (G.geometry r).k - gain r p

namespace DebitLayer

variable {G : BlockGeom} {Fr : Frame} {depth : ℕ}

/-- **The Smith layer in the form of Theorem SD:** the member bound
`max(0, 2|C| + m - gain + k)` where `gain = max(G0, σ, 2σ - s)` (hypothesis, H2). -/
def smithSD (gain : ℕ → ℕ → ℕ) (valid : ℕ → ℕ → Prop)
    (h : ∀ (i : NodeFamily.Index G.geometry), (G.family Fr depth).Adm i →
      ∀ (p : ℕ) [Fact p.Prime], valid i.1 p →
        GLE p (2 * (G.geometry i.1).C.card + (G.geometry i.1).k + delCount G i - gain i.1 p)
          ((G.family Fr depth).Q i)) : DebitLayer G Fr depth :=
  smith (sdBase G gain) valid (fun i hi p _ hv =>
    (h i hi p hv).mono (by unfold sdBase; omega))

end DebitLayer

end CatalanCore.Uniform.Content.Member
