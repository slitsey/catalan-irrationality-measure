module

public import CatalanCore.Uniform.Decay.NearFast.Agg
public import CatalanCore.Uniform.Decay.Breakpoint.Rev

@[expose] public section
set_option Elab.async false

/-!
# Per-cell piece reversal (lane D, package WALL)

The fast piece evaluator `pieceEval2F` rejects a cell that crosses the line of a piece `P` beyond its
end `B` (the side condition `sideOk3` holds only if `Im ζ` keeps one sign on the cell or
`Re ζ₀ < 0`, where `ζ = (z - A)/(B - A)`).  The potential is real-analytic there.  The reversed piece
`revWP P` (`Breakpoint.Rev`: endpoints swapped, density `a(1 - t)`) has local coordinate `1 - ζ`, so
such a cell has `Re ζ₀' < 0` for it, and it has the same potential (`PhiW_revWP`).

`flipAt ix ps` replaces the pieces at the indices `ix` by their reversals.  The weighted potentials of
`flipAt ix ps` and `ps` are equal lists (`flipAt_pot`), so any cell rule proved for a list of pieces
transfers to the flipped list; `aggEvalMF_flip_sound` is the aggregate soundness in that form.
-/

namespace CatalanCore.Uniform.Decay.NearFast

open Finset CatalanCore.Uniform.Decay.Tools CatalanCore.Uniform.Decay.NearCells
open CatalanCore.Uniform.Decay.Breakpoint (revWP PhiW_revWP)

/-- `ps` with the pieces at the indices `ix` reversed (indices counted from `k`). -/
def flipFrom (ix : List ℕ) : ℕ → List WP → List WP
  | _, [] => []
  | k, P :: ps => (if ix.contains k then revWP P else P) :: flipFrom ix (k + 1) ps

/-- `ps` with the pieces at the indices `ix` (from `0`) reversed. -/
def flipAt (ix : List ℕ) (ps : List WP) : List WP := flipFrom ix 0 ps

theorem flipFrom_map {β : Type*} (g : WP → β) (hg : ∀ P, g (revWP P) = g P) (ix : List ℕ) :
    ∀ (k : ℕ) (ps : List WP), (flipFrom ix k ps).map g = ps.map g
  | _, [] => rfl
  | k, P :: ps => by
      rw [flipFrom, List.map_cons, List.map_cons, flipFrom_map g hg ix (k + 1) ps]
      by_cases hk : ix.contains k = true
      · rw [if_pos hk, hg]
      · rw [if_neg hk]

/-- **Same potential.**  The weighted potentials of the flipped list are those of `ps`. -/
theorem flipAt_pot (ix : List ℕ) (ps : List WP) (z : ℂ) :
    (flipAt ix ps).map (fun P => (P.w : ℝ) * PhiW P z) = ps.map (fun P => (P.w : ℝ) * PhiW P z) :=
  flipFrom_map (fun P => (P.w : ℝ) * PhiW P z)
    (fun P => by
      show ((revWP P).w : ℝ) * PhiW (revWP P) z = (P.w : ℝ) * PhiW P z
      exact congrArg (fun x => (P.w : ℝ) * x) (PhiW_revWP P z)) ix 0 ps

theorem flipAt_sum (ix : List ℕ) (ps : List WP) (z : ℂ) :
    ((flipAt ix ps).map (fun P => (P.w : ℝ) * PhiW P z)).sum
      = (ps.map (fun P => (P.w : ℝ) * PhiW P z)).sum := by
  rw [flipAt_pot]

theorem length_flipFrom (ix : List ℕ) : ∀ (k : ℕ) (ps : List WP), (flipFrom ix k ps).length = ps.length
  | _, [] => rfl
  | k, _ :: ps => by rw [flipFrom, List.length_cons, List.length_cons, length_flipFrom ix (k + 1) ps]

theorem length_flipAt (ix : List ℕ) (ps : List WP) : (flipAt ix ps).length = ps.length :=
  length_flipFrom ix 0 ps

/-- **Aggregate soundness on the flipped list**, stated for the original pieces. -/
theorem aggEvalMF_flip_sound {n : ℕ} {zc dd : CQ} {h : ℚ} (s : ℝ) (hs : |s| ≤ h) (ix : List ℕ)
    (ps : List WP) {C : List ℚ} {F : ℚ} (hC : aggEvalMF n zc dd h (flipAt ix ps) = some (C, F)) :
    |(-(ps.map (fun P => (P.w : ℝ) * PhiW P (zc.toC + (s : ℂ) * dd.toC))).sum)
        - ∑ m ∈ range n, ((coeffs C m : ℚ) : ℝ) * s ^ m| ≤ (F : ℝ) := by
  have key := aggEvalMF_sound s hs (flipAt ix ps) hC
  rwa [flipAt_sum] at key

/-- Any lower bound of the flipped potential (the conclusion of every cell rule) is one of the
original potential. -/
theorem flip_lower {m' cpi : ℚ} {z : ℂ} (ix : List ℕ) (ps : List WP)
    (hk : (m' : ℝ) ≤ -((flipAt ix ps).map (fun P => (P.w : ℝ) * PhiW P z)).sum + (cpi : ℝ) * |z.im|) :
    (m' : ℝ) ≤ -(ps.map (fun P => (P.w : ℝ) * PhiW P z)).sum + (cpi : ℝ) * |z.im| := by
  rwa [flipAt_sum] at hk

end CatalanCore.Uniform.Decay.NearFast
