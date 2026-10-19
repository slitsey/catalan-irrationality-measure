module

public import CatalanCore.Arith.Hybrid.SingLev

@[expose] public section

/-!
# Sign transfer of content data

If `Fr₂.Delta = -Fr₁.Delta`, `Fr₂.Dsq = -Fr₁.Dsq`, `Fr₂.Mn = -Fr₁.Mn` and the norms agree, then every
`ContentData`/`HybInst` of `Fr₁` gives one of `Fr₂` (all statements are about membership in a
local ring, which is closed under negation).  Used to run the λ-like deficit machinery
(`LamData Fr 3`) on the mirror frame `mirNFrame` while keeping the legacy `mirFrame` content data.
-/

open CatalanCore CatalanCore.Arith CatalanCore.Basic

namespace CatalanCore.Arith

variable {Fr₁ Fr₂ : Frame}

/-- Transfer of `ContentData` along a sign change. -/
noncomputable def ContentData.neg (cd : ContentData Fr₁) (hΔ : ∀ k, Fr₂.Delta k = -Fr₁.Delta k)
    (hD : ∀ k, Fr₂.Dsq k = -Fr₁.Dsq k) (hn : Fr₂.norm = Fr₁.norm)
    (hM : ∀ a b, Fr₂.Mn a b = -Fr₁.Mn a b) : ContentData Fr₂ where
  L := cd.L
  hL := cd.hL
  Phi := cd.Phi
  Phi_pos := cd.Phi_pos
  bad := cd.bad
  bad_prime := cd.bad_prime
  normN := cd.normN
  norm_eq := hn.trans cd.norm_eq
  norm_dvd := cd.norm_dvd
  delta_int := fun k hk => by
    obtain ⟨z, hz⟩ := cd.delta_int k hk
    exact ⟨-z, by rw [hΔ, neg_mul, hz]; push_cast; ring⟩
  dsq_int := fun k hk => by
    obtain ⟨z, hz⟩ := cd.dsq_int k hk
    exact ⟨-z, by rw [hD, neg_mul, hz]; push_cast; ring⟩
  kq := cd.kq
  kq_le := cd.kq_le
  small := cd.small
  small_pos := cd.small_pos
  small_ok := fun p _ hp h a b ha hb => by
    have := cd.small_ok p hp h a b ha hb
    rw [hM, mul_neg]
    exact (LocRing p).neg_mem this
  small_poly := cd.small_poly

end CatalanCore.Arith

namespace CatalanCore.Arith.Hybrid

variable {Fr₁ Fr₂ : Frame}

/-- Transfer of `HybInst` along a sign change. -/
noncomputable def HybInst.neg (I : HybInst Fr₁) (hΔ : ∀ k, Fr₂.Delta k = -Fr₁.Delta k)
    (hD : ∀ k, Fr₂.Dsq k = -Fr₁.Dsq k) (hn : Fr₂.norm = Fr₁.norm)
    (hM : ∀ a b, Fr₂.Mn a b = -Fr₁.Mn a b) : HybInst Fr₂ where
  cd := I.cd.neg hΔ hD hn hM
  Ebd := I.Ebd
  lev := I.lev
  off_val := fun p _ E N lo hi h1 h2 h3 h4 => by
    have := I.off_val p E N lo hi h1 h2 h3 h4
    have e : (1 / ((hi : ℚ) - lo)) * ∑ k ∈ Finset.Ioc lo hi, Fr₂.Delta k =
        -((1 / ((hi : ℚ) - lo)) * ∑ k ∈ Finset.Ioc lo hi, Fr₁.Delta k) := by
      simp only [hΔ, Finset.sum_neg_distrib]; ring
    rw [e, mul_neg]
    exact (LocRing p).neg_mem this
  diag_val := fun p _ E N a h1 h2 => by
    have := I.diag_val p E N a h1 h2
    have e : ∑ k ∈ Finset.Icc 1 a, Fr₂.Dsq k = -∑ k ∈ Finset.Icc 1 a, Fr₁.Dsq k := by
      simp only [hD, Finset.sum_neg_distrib]
    rw [e, mul_neg]
    exact (LocRing p).neg_mem this
  lev_large := I.lev_large
  lev_Ebd := I.lev_Ebd

end CatalanCore.Arith.Hybrid
