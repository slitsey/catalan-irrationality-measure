module

public import CatalanFrames.LambdaHybrid.NV.FinalGood
public import CatalanCore.Star.Leonard.Induct

/-!
# The hybrid nonvanishing, modulo the K-step transfer only

Everything except the Darboux K-step `KSTransfer` (good form of `uu m (n'+1) (n'+1)` from good form of
`uu m n' (n'+1)`) is proved: base case (Cauchy), diagonal steps (`uu_good_succ`), the normalising
constant `ν` (`kgen_eq_nu_mul_u`, `nu_form`, `Cnu_LU`), the `θ → 0` limit and the mod-`ℓ` glue.
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanFrames.LambdaHybrid.NV

variable {ℓ K : ℕ} [Fact ℓ.Prime]

theorem nv_hyb_nonvanishing_of_KS {Fr : Frame} (D : ModData Fr ℓ K) (m s' r : ℕ)
    (hm : 1 ≤ m) (hmK : m < K) (hrK : K ≤ r) (hr : r + 2 * m + (s' + 1) = ℓ)
    (hS : K - m ≤ s' + 1) (KS : CatalanCore.Star.Leonard.KSTransfer ℓ m)
    {x : ℚ} (hx : x ∈ CatalanCore.S ℓ)
    (h1 : ((after r m).Full Fr x).det = 0) (h2 : ((afterTop r m).Full Fr x).det = 0) : False := by
  obtain ⟨n, rfl⟩ : ∃ n, K = m + n := ⟨K - m, by omega⟩
  have hn : 1 ≤ n := by omega
  have huu := CatalanCore.Star.Leonard.uu_good m hm KS n hn (s' + 1) (by omega) (by omega)
  have hkg := CatalanCore.Star.Leonard.kgen_good m n (s' + 1) hm hn (by omega) (by omega) huu
  exact nv_hyb_nonvanishing_of_good D m s' r hmK hrK hr hS _ (by omega) hkg hx h1 h2

end CatalanFrames.LambdaHybrid.NV
