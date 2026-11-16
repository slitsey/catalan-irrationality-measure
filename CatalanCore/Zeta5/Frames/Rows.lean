module

public import CatalanCore.Zeta5.Frames.Normalizer
public import CatalanCore.Zeta5.Frames.OuterExt

@[expose] public section

/-!
# Content ledger rows ZC10–ZC15 and ZC18: the frames, in one place

| row | theorem | module |
|---|---|---|
| ZC10 | `zc10_weight`, `zc10_delta` | WeightLemma |
| ZC11 | `zc11_comp_minor` | CompMinor |
| ZC12 | `InnerHyp.zc12_inner`, `InnerHyp.sum_innerL`, `InnerHyp.innerL_spec`, `InnerHyp.inner_gamma_int`, `class_unimodular`, `class_entry` | InnerAlloc, ClassFrame |
| ZC13 | `zc13_split`, `zc13_factor` | Rows, OuterFrame |
| ZC14 | `outer_bound` (I15), `zc14_poleValue_congr`, `zc14_outer` (I17), `zc14_big` (I18) | OuterEntryMain, PoleVal, Outer |
| ZC15 | `zc15_normaliser`, `log_mKM` | Normalizer |
| ZC18 | `ExtHyp.zc18_ext`, `ExtHyp.T_ge2`, `ExtHyp.T_le6`, `ExtHyp.extL_spec`, `ExtHyp.sum_extL` | OuterExt |
-/

open Finset Polynomial

namespace Apery

/-- **ZC13, integral part.** For `p ≥ 5` and `Q ∈ ℤ_(p)[x]`: `μ(Q) = μ₀(Q) + μ_{≥ 2p-3}(Q)` with
`μ₀ = μ - μ_{≥}` integral on monomials and `p μ_{≥}(Q)` integral. -/
theorem zc13_split {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {Q : ℚ[X]} (hQ : GV p Q 0) :
    VG p (μpoly Q - μGe p Q) 0 ∧ VG p ((p : ℚ) * μGe p Q) 0 :=
  ⟨VG_μpoly_sub_μGe hp5 hQ, VG_p_μGe hp5 hQ⟩

/-- **ZC14, the low-pole congruence** `μ_X(1/(t+(p-c)²)) ≡ μ_X(1/(t+c²)) (mod p)`
(this contains `H^{(5)}_{p-c} ≡ H^{(5)}_{c-1}`). -/
theorem zc14_poleValue_congr {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) {c : ℕ} (hc : 1 ≤ c)
    (hcp : c < p) : GV p (poleValue (p - c) - poleValue c) 1 :=
  GV_poleValue_congr hp3 hc hcp

end Apery
