module
public import CatalanArchive.CatalanMeasure.Parametric.U3Digits
public import CatalanMeasure.Parametric.SecondaryTentFilteredResponse
@[expose] public section

/-!
# The canonical rank bound of Lemma U3

For `N ≥ 1` and a prime `p` with `8N < p < 9N`, the scaled residue matrix of
the canonical base matrix has rank at most `20N - (18N - 2p - 1)`.
-/

namespace CatalanMeasure.Parametric
open Polynomial OAI.InternalCatalan
noncomputable section

section
variable {p N : ℕ} [hp : Fact p.Prime]

/-- Costs of the five constraint groups. -/
def u3Cost (p N : ℕ) : Fin 5 → ℕ
  | 0 => (p + 1) / 2 - N
  | 1 => (p + 1) / 2
  | 2 => 2 * (27 * N - 3 * p)
  | 3 => p - 3 * N
  | 4 => 2 * (3 * p - 24 * N)

def u3Constraint (p N : ℕ) [Fact p.Prime] :
    ∀ i : Fin 5, (Fin (20 * N) → ZMod p) →ₗ[ZMod p] (Fin (u3Cost p N i) → ZMod p)
  | 0 => u3FlagUp p N
  | 1 => u3FlagDown p N
  | 2 => LinearMap.pi fun a : Fin (2 * (27 * N - 3 * p)) =>
      u3Resp p N (((a.val % 2) + 1) * p + a.val / 2)
  | 3 => LinearMap.pi fun a : Fin (p - 3 * N) =>
      (lcoeff (ZMod p) (p + (27 * N - 3 * p) + a.val)).comp
        ((LinearMap.mulLeft (ZMod p) ((1 - X : (ZMod p)[X]) ^ N)).comp (u3U p N))
  | 4 => LinearMap.pi fun a : Fin (2 * (3 * p - 24 * N)) =>
      u3Resp p N ((a.val % 2) * p + (24 * N - 2 * p) + a.val / 2)

theorem u3Cost_sum (h8 : 8 * N < p) (h9 : p < 9 * N) (hodd : p % 2 = 1) :
    ∑ i, u3Cost p N i = 2 * p + 2 * N + 1 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, u3Cost, Fin.isValue,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  norm_num
  omega

theorem u3_kernel_response (hN : 0 < N) (hp2 : p ≠ 2) (h8 : 8 * N < p) (h9 : p < 9 * N)
    (c : Fin (20 * N) → ZMod p) (hc : ∀ i, u3Constraint p N i c = 0)
    {j : ℕ} (hj1 : 3 * N ≤ j) (hj2 : j < 24 * N) : u3Resp p N j c = 0 := by
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  obtain ⟨Y, hY⟩ := u3Flag_dvd hp2 (by omega) c (hc 0) (hc 1)
  have hjd := Nat.div_add_mod j p
  have hℓp : j % p < p := Nat.mod_lt _ hp.out.pos
  generalize hJ : j / p = J at hjd
  generalize hL : j % p = ℓ at hjd hℓp
  have hJ3 : J < 3 := by
    by_contra h
    have := Nat.mul_le_mul_left p (show 3 ≤ J by omega)
    nlinarith
  by_cases hA : ℓ < 27 * N - 3 * p
  · -- two free columns per residue
    have hJ0 : J ≠ 0 := by rintro rfl; omega
    have hJ' : J = 1 ∨ J = 2 := by omega
    rcases hJ' with rfl | rfl
    · have key : u3Resp p N (((2 * ℓ + 0) % 2 + 1) * p + (2 * ℓ + 0) / 2) c = 0 :=
        congrFun (hc 2) ⟨2 * ℓ + 0, by simp only [u3Cost]; omega⟩
      have h1 : (2 * ℓ + 0) % 2 = 0 := by omega
      have h2 : (2 * ℓ + 0) / 2 = ℓ := by omega
      rw [h1, h2] at key
      rwa [show j = (0 + 1) * p + ℓ by omega]
    · have key : u3Resp p N (((2 * ℓ + 1) % 2 + 1) * p + (2 * ℓ + 1) / 2) c = 0 :=
        congrFun (hc 2) ⟨2 * ℓ + 1, by simp only [u3Cost]; omega⟩
      have h1 : (2 * ℓ + 1) % 2 = 1 := by omega
      have h2 : (2 * ℓ + 1) / 2 = ℓ := by omega
      rw [h1, h2] at key
      rwa [show j = (1 + 1) * p + ℓ by omega]
  by_cases hB : ℓ < 24 * N - 2 * p
  · have hw := u3Resp_window hN hp2 h8 h9 hj2 (by rw [hL]; omega) (by rw [hL]; omega) c Y hY
    rw [hw, hL]
    have key : ((1 - X : (ZMod p)[X]) ^ N * u3U p N c).coeff
        (p + (27 * N - 3 * p) + (ℓ - (27 * N - 3 * p))) = 0 :=
      congrFun (hc 3) ⟨ℓ - (27 * N - 3 * p), by simp only [u3Cost]; omega⟩
    rw [show p + ℓ = p + (27 * N - 3 * p) + (ℓ - (27 * N - 3 * p)) by omega, key, zero_mul]
  · have hJ' : J = 0 ∨ J = 1 := by
      by_contra h
      have := Nat.mul_le_mul_left p (show 2 ≤ J by omega)
      omega
    rcases hJ' with rfl | rfl
    · have key : u3Resp p N (((2 * (ℓ - (24 * N - 2 * p)) + 0) % 2) * p + (24 * N - 2 * p) +
          (2 * (ℓ - (24 * N - 2 * p)) + 0) / 2) c = 0 :=
        congrFun (hc 4) ⟨2 * (ℓ - (24 * N - 2 * p)) + 0, by simp only [u3Cost]; omega⟩
      have h1 : (2 * (ℓ - (24 * N - 2 * p)) + 0) % 2 = 0 := by omega
      have h2 : (2 * (ℓ - (24 * N - 2 * p)) + 0) / 2 = ℓ - (24 * N - 2 * p) := by omega
      rw [h1, h2] at key
      rwa [show j = 0 * p + (24 * N - 2 * p) + (ℓ - (24 * N - 2 * p)) by omega]
    · have key : u3Resp p N (((2 * (ℓ - (24 * N - 2 * p)) + 1) % 2) * p + (24 * N - 2 * p) +
          (2 * (ℓ - (24 * N - 2 * p)) + 1) / 2) c = 0 :=
        congrFun (hc 4) ⟨2 * (ℓ - (24 * N - 2 * p)) + 1, by simp only [u3Cost]; omega⟩
      have h1 : (2 * (ℓ - (24 * N - 2 * p)) + 1) % 2 = 1 := by omega
      have h2 : (2 * (ℓ - (24 * N - 2 * p)) + 1) / 2 = ℓ - (24 * N - 2 * p) := by omega
      rw [h1, h2] at key
      rwa [show j = 1 * p + (24 * N - 2 * p) + (ℓ - (24 * N - 2 * p)) by omega]

/-- The canonical rank bound of Lemma U3. -/
theorem u3_canonical_rank (hN : 0 < N) (h8 : 8 * N < p) (h9 : p < 9 * N) :
    (scaledResidueMatrix (p := p) (measureBaseMatrix twenty N)).rank + (18 * N - 2 * p - 1) ≤
      20 * N := by
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hH : twenty.H N < p ^ 2 := by rw [twenty_H]; nlinarith
  have hzp : (((p : ℚ) * 0).den : ZMod p) ≠ 0 := by simp
  let J : LinearMap.ker (secondaryTentConstraintMap (u3Cost p N) (u3Constraint p N)) →ₗ[ZMod p]
      (Fin (twenty.n N) → ZMod p) := Submodule.subtype _
  have hr := secondaryTent_rank_of_raw_polynomial_responses (P := twenty) (p := p) (N := N)
    (V := Fin (20 * N) → ZMod p) hp2 hH 0 hzp (u3Cost p N) (u3Constraint p N) J
    Subtype.val_injective (by
      intro v
      refine ⟨0, ?_, ?_⟩
      · simp [twenty, Parameters.q]; omega
      · intro j hj1 hj2
        have hv := (secondaryTentConstraintMap_eq_zero_iff _ _ v.1).mp v.2
        have := u3_kernel_response hN hp2 h8 h9 v.1 hv
          (by simpa [twenty, Parameters.b] using hj1)
          (by simp only [twenty, Parameters.L, Parameters.n, Parameters.b, Parameters.q] at hj2; omega)
        rw [eval_zero]
        exact this)
  rw [u3Cost_sum h8 h9 hodd, Module.finrank_fin_fun] at hr
  have e : 20 * N - (2 * p + 2 * N + 1) = 18 * N - 2 * p - 1 := by omega
  change _ + (20 * N - (2 * p + 2 * N + 1)) ≤ _ at hr
  rw [e] at hr
  exact hr

end

end
end CatalanMeasure.Parametric
