module

public import CatalanArchive.CatalanFrames.LambdaHybrid.NV.FinalS
public import CatalanArchive.CatalanFrames.LambdaHybrid.NV.HDelta
public import CatalanArchive.CatalanFrames.LambdaHybrid.NV.KgenMod
public import CatalanCore.Star.Leonard.KgenLUL
public import CatalanCore.Star.Leonard.GoodForm
public import CatalanCore.Star.Leonard.Induct
public import CatalanCore.Star.Leonard.LpGood

/-!
# The unconditional hybrid nonvanishing (one generic chain)

`hyb_primal_false`: the primal pair of `borderedN` determinants (output of `pair_red`) contradicts the
Darboux/Leonard closed form of `k^gen` (`hDelta_after`, base case, diagonal steps, K-steps, `θ → 0`
and the mod-`ℓ` last mile).  Frame-free.

`nv_hyb_nonvanishing_gen`: for level-indexed `ModData3 Fr ℓ K T` (see `Mod3.lean`), with
`1 ≤ m < K ≤ r`, `r + 2m + (s'+1) = ℓ`, `K - m ≤ s'+1`, the two hybrid member determinants
`det (after r m).Full Fr x` and `det (afterTop r m).Full Fr x` cannot both vanish at `x ∈ S ℓ`.
`nv_hyb_nonvanishing` is the two-level instance (`T = ℓ`, `ModData.toLevels`); P6 is the instance
`S = T`, `ℓ + 1 = 2T`.
-/

@[expose] public section

open Finset Matrix CatalanCore CatalanCore.Rect

namespace CatalanArchive.CatalanFrames.LambdaHybrid.NV

variable {ℓ K T : ℕ} [Fact ℓ.Prime]

/-- **Generic closed-form end of the hybrid chain, from the primal pair.**  The hypothesis `hred` is the
output of the mod-`ℓ` reduction of both members (`pair_red3`, or the two-level analogue); the rest is the
frame-free chain of `nv_hyb_nonvanishing` (primal lemma with general `τ`, `hDelta_after`, Leonard/Darboux). -/
theorem hyb_primal_false (m s' r : ℕ) (hm : 1 ≤ m) (hmK : m < K) (hrK : K ≤ r)
    (hr : r + 2 * m + (s' + 1) = ℓ) (hS : K - m ≤ s' + 1)
    (hred : ∃ z τ : ZMod ℓ, τ ≠ 0 ∧
      (borderedN z (N2 ℓ K s') (WX ℓ K (after r m)) (WY ℓ K (after r m))).det = 0 ∧
      (borderedN z (N2 ℓ K s' + τ • vecMulVec (wLast ℓ K s') (wLast ℓ K s'))
        (WX ℓ K (after r m)) (WY ℓ K (after r m))).det = 0) : False := by
  obtain ⟨z, τ, hτ, hb2, hb1⟩ := hred
  have hΔ := hDelta_after (ℓ := ℓ) K m r (by omega) hmK.le hrK (by omega)
  have hpair := primal_pair hτ (N2 ℓ K s')
    (by simp [N2, Matrix.transpose_mul, Matrix.transpose_transpose]) (wLast ℓ K s') _ _ hΔ hb2 hb1
  have KS : CatalanCore.Star.Leonard.KSTransfer ℓ m := CatalanCore.Star.Leonard.ks_transfer_of_LpG m hm fun n' hn' hl =>
    CatalanCore.Star.Leonard.LpG_good m n' hm hn' hl
  obtain ⟨n, rfl⟩ : ∃ n, K = m + n := ⟨K - m, by omega⟩
  have hn : 1 ≤ n := by omega
  have huu := CatalanCore.Star.Leonard.uu_good m hm KS n hn (s' + 1) (by omega) (by omega)
  have hkg := CatalanCore.Star.Leonard.kgen_good m n (s' + 1) hm hn (by omega) (by omega) huu
  have hl : (s' + 1) + (m + n) + 2 * m ≤ ℓ := by omega
  have hR := CatalanCore.Star.Leonard.kgen_LU_of_good (ℓ := ℓ) (m + n) m (s' + 1) _ hmK hS
    (by omega) hkg
  have hL := CatalanCore.Star.Leonard.kgenL_LU_of_good (ℓ := ℓ) (m + n) m (s' + 1) _ hmK hS hl
    (by omega) hkg
  obtain ⟨U, hU, hne⟩ := kgenR'_ne_zero_of_LU (m + n) m r s' hmK hrK hr hR
  obtain ⟨U', hU', hne'⟩ := kgenL'_ne_zero_of_LU (m + n) m r s' hmK hrK hr (by simpa using hL)
  rcases hpair with h | h
  · exact hne (h _ U hU)
  · exact hne' (h _ U' hU')

theorem nv_hyb_nonvanishing_gen {Fr : Frame} (D : ModData3 Fr ℓ K T) (m s' r : ℕ)
    (hm : 1 ≤ m) (hmK : m < K) (hrK : K ≤ r) (hr : r + 2 * m + (s' + 1) = ℓ)
    (hS : K - m ≤ s' + 1) (hcase : T = ℓ ∨ (s' + 1 = T ∧ ℓ + 1 = 2 * T))
    {x : ℚ} (hx : x ∈ CatalanCore.S ℓ)
    (h1 : ((after r m).Full Fr x).det = 0) (h2 : ((afterTop r m).Full Fr x).det = 0) : False :=
  hyb_primal_false m s' r hm hmK hrK hr hS (pair_red D m s' r hrK hr hcase hx h1 h2)

theorem nv_hyb_nonvanishing {Fr : Frame} (D : ModData Fr ℓ K) (m s' r : ℕ)
    (hm : 1 ≤ m) (hmK : m < K) (hrK : K ≤ r) (hr : r + 2 * m + (s' + 1) = ℓ)
    (hS : K - m ≤ s' + 1) {x : ℚ} (hx : x ∈ CatalanCore.S ℓ)
    (h1 : ((after r m).Full Fr x).det = 0) (h2 : ((afterTop r m).Full Fr x).det = 0) : False :=
  nv_hyb_nonvanishing_gen D.toLevels m s' r hm hmK hrK hr hS (Or.inl rfl) hx h1 h2

#print axioms nv_hyb_nonvanishing

end CatalanArchive.CatalanFrames.LambdaHybrid.NV
