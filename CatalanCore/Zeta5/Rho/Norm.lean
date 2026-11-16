module

public import CatalanCore.Zeta5.Rho.Assembly
public import CatalanCore.Zeta5.Rho.Numerics

@[expose] public section

/-!
# The stability constant `ρ = 907427/10⁵` (ledger ZR10)

`‖B_K‖ ≤ exp(907427 K / 10⁵)` for all large `K ∈ 40ℕ`, for the unchanged Fauzan pencil
`G_K(X) = G + (X - ζ(5)) M_K`, `B_K = G^{-1/2} M_K G^{-1/2}`.  Stated in the equivalent
quadratic-form (Loewner) form `-e^{ρK} G ≤ M ≤ e^{ρK} G`, i.e. `|vᵀ M v| ≤ e^{ρ K} vᵀ G v`, which is
the hypothesis `RhoBound` of `CatalanCore.Zeta5.Criterion.Family` (`Mmat = M0`, `Gmat` = the
Gram matrix `(G n).map (aeval zeta5)`).  The constant is exactly `907427/10⁵`: the slack
`907427/10⁵ - 9.0742658` absorbs the polynomial prefactor `h³/((b-a)c_{a,b})` (ZR09).
-/

namespace CatalanCore.Zeta5.Rho

open Apery Matrix Polynomial

/-- **ZR10.**  For all large `n` (`K = 40 n`) and every vector `v`:
`|vᵀ M_K v| ≤ exp(907427/10⁵ · K) · vᵀ G_K(ζ(5)) v`. -/
theorem zeta5_rho_bound : ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n → ∀ v : Fin (37 * n) → ℝ,
    |v ⬝ᵥ (M0 n *ᵥ v)| ≤ Real.exp ((907427 / 10 ^ 5 : ℝ) * ((40 * n : ℕ) : ℝ)) *
      (v ⬝ᵥ (((G n).map (aeval zeta5)) *ᵥ v)) := by
  obtain ⟨hW, hP, hgap⟩ := rho_numerics
  obtain ⟨n0, _, hn⟩ := norm_eventually aR_pos aR_lt_bR hW hP hgap
  refine ⟨n0, fun n hnn v => ?_⟩
  have h := hn n hnn v
  rw [star_trivial] at h
  push_cast
  exact h

end CatalanCore.Zeta5.Rho
