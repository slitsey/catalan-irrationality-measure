module
public import CatalanCore.Arith.Hybrid.LemmaE.ModelWeighted
public import CatalanCore.Arith.Hybrid.LemmaE.ModelPartners
@[expose] public section
open Matrix Polynomial
namespace CatalanCore.Arith.Hybrid.LemmaE
variable {p : ℕ} [Fact p.Prime]
variable {I Z : Type} [Fintype I] [DecidableEq I] [Fintype Z] [DecidableEq Z]

/-- An integral change to the common core preserves every nonnegative cleared
entry budget. Primitivity of the changed scaled core is supplied separately. -/
theorem integral_core_add_weighted
    (A E : Matrix I I ℚ[X]) (B : Matrix I Z ℚ[X])
    (C : Matrix Z I ℚ[X]) (D : Matrix Z Z ℚ[X])
    (h : ℚ[X]) (Sr : Matrix Z I ℚ[X]) (Sc : Matrix I Z ℚ[X])
    (hh : gn p h=1) (hsr : ∀z i,Int1 p (Sr z i))
    (hsc : ∀i y,Int1 p (Sc i y)) (he : ∀i j,Int1 p (E i j))
    (w : Z→Z→ℕ)
    (hL : ∀z i,gn p ((h • C-Sr*A) z i)≤p)
    (hR : ∀i y,gn p ((h • B-A*Sc) i y)≤p)
    (hd : ∀z y,GLE p (w z y) ((h^2 • D-h • (Sr*B)-h • (C*Sc)+Sr*A*Sc) z y))
    (hI : ∀i j,Int1 p (Atil p (fun _:I=>1) (A+E) i j))
    (hp : gn p (Atil p (fun _:I=>1) (A+E)).det=1) :
    GLE p (tropVal w+2*Fintype.card I) (Matrix.fromBlocks (A+E) B C D).det := by
  have hse := matrix_mul_int1 Sr E hsr he
  have hes := matrix_mul_int1 E Sc he hsc
  have hses := matrix_mul_int1 (Sr*E) Sc hse hsc
  have hp1 : (1:ℝ)≤p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  apply tcore_cleared_weighted (Matrix.fromBlocks (A+E) B C D)
    (by simpa only [Matrix.toBlocks_fromBlocks₁₁] using hI)
    (by simpa only [Matrix.toBlocks_fromBlocks₁₁] using hp) h hh Sr Sc w
  · intro z i
    change gn p ((h • C-Sr*(A+E)) z i)≤p
    rw [Matrix.mul_add,sub_add_eq_sub_sub]
    exact (gn_sub_le _ _).trans (max_le (hL z i) ((hse z i).trans hp1))
  · intro i y
    change gn p ((h • B-(A+E)*Sc) i y)≤p
    rw [Matrix.add_mul,sub_add_eq_sub_sub]
    exact (gn_sub_le _ _).trans (max_le (hR i y) ((hes i y).trans hp1))
  · intro z y
    change GLE p (w z y) ((h^2 • D-h • (Sr*B)-h • (C*Sc)+Sr*(A+E)*Sc) z y)
    rw [Matrix.mul_add,Matrix.add_mul,←add_assoc,Matrix.add_apply]
    apply (hd z y).add
    apply GLE.mono (Nat.zero_le _)
    exact (gle_iff_gn p 0 _).mpr (by simpa only [Int1, pow_zero] using hses z y)
end CatalanCore.Arith.Hybrid.LemmaE
