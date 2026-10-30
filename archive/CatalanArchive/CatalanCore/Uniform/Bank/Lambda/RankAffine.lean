import CatalanCore.Uniform.Bank.Lambda.RankFinish
import CatalanCore.Uniform.Content.RankProducer.AffineCost
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Basic CatalanCore.Uniform.Content.Hybrid
open CatalanCore.Uniform.Content.RankProducer CatalanCore.Uniform.Content.Member
open CatalanCore.Uniform.Bank.Chi3Rank
open scoped Classical

/-- Physical counts and selected rational matching counts supply an actual member price. -/
theorem rank_affine_member (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
    (hReal : ∀ x, Realizes (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x (cert x))
    (hRs : ∀ x, (cert x).kr.card ≤ 1) (hCs : ∀ x, (cert x).kc.card ≤ 1)
    (v : ℚ × ℚ) (hv1 : v.1 ∈ S p) (hv2 : v.2 ∈ S p) (hv : castV p v ≠ 0)
    (hRu : ∀ x, ∀ d ∈ (cert x).kr, ((cert x).rload d).1 ∈ S p ∧ ((cert x).rload d).2 ∈ S p)
    (hCu : ∀ x, ∀ d ∈ (cert x).kc, ((cert x).cload d).1 ∈ S p ∧ ((cert x).cload d).2 ∈ S p)
    (hCn : ∀ x, ∀ d ∈ (cert x).kc, castV p ((cert x).cload d) ≠ 0)
    (L G E : ℚ)
    (hR : L - E ≤ ((∑ x : ZMod p, (cert x).kr.card : ℕ) : ℚ) ∧
      ((∑ x : ZMod p, (cert x).kr.card : ℕ) : ℚ) ≤ L + E)
    (hC : L - E ≤ ((∑ x : ZMod p, (cert x).kc.card : ℕ) : ℚ) ∧
      ((∑ x : ZMod p, (cert x).kc.card : ℕ) : ℚ) ≤ L + E)
    (hMatch : G - 2 * E ≤ (((∑ x : ZMod p, rationalRowMatches (cert x) v) +
      (∑ x : ZMod p, rationalColMatches (cert x) v) : ℕ) : ℚ)) :
    ∃ M : RankMember (pipelineFrame a ha) (u4 a) q4 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      (M.price : ℚ) ≤ (11 / 5 : ℚ) * r + 1 - G + 6 * E := by
  let PS := lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1
  let R := (killRows (p := p) (rowsOf r m s) cert).card
  let C := (killCols (p := p) (colsOf r m s) cert).card
  have hrow : R = ∑ x : ZMod p, (cert x).kr.card :=
    killRows_card_eq_sum PS (rowsOf r m s) (colsOf r m s) (rows_inj r m s) cert hOk hReal
  have hcol : C = ∑ x : ZMod p, (cert x).kc.card :=
    killCols_card_eq_sum PS (rowsOf r m s) (colsOf r m s) (cols_inj r m s) cert hOk hReal
  have hRq : L - E ≤ (R : ℚ) ∧ (R : ℚ) ≤ L + E := by simpa only [hrow] using hR
  have hCq : L - E ≤ (C : ℚ) ∧ (C : ℚ) ≤ L + E := by simpa only [hcol] using hC
  obtain ⟨M, hMK, hP, hS⟩ := balanced_rank_line a p r m s ha hp29 hp4 hrp hm1
    cert hOk hInt hReal hRs hCs v hv1 hv2 hv hRu hCu hCn
  have hK : L - E ≤ (M.killCount : ℚ) := by
    change M.killCount = min R C at hMK
    rw [hMK]
    rcases le_total R C with h | h
    · rw [min_eq_left h]; exact hRq.1
    · rw [min_eq_right h]; exact hCq.1
  have hKR : M.killCount ≤ R := by rw [hMK]; exact min_le_left _ _
  have hKC : M.killCount ≤ C := by rw [hMK]; exact min_le_right _ _
  have hH : ((2 * (s.card + m) : ℕ) : ℚ) ≤ (11 / 5 : ℚ) * r + 1 := by
    have hs : s.card ≤ r := by simpa using Finset.card_le_univ s
    have hsQ : (s.card : ℚ) ≤ r := by exact_mod_cast hs
    have hmQ : (10 : ℚ) * m ≤ r + 5 := by exact_mod_cast hm1
    push_cast
    linarith
  refine ⟨M, ?_⟩
  exact affine_line_price_bound (s.card + m) M.killCount R C M.colScore M.rowScore
    M.price _ L G ((11 / 5 : ℚ) * r + 1) E hKR hKC hK hRq.2 hCq.2 hMatch
    (by simpa only [Nat.add_comm M.colScore M.rowScore] using hS) hP hH

#print axioms rank_affine_member

/-- The raw price needs only the common lower count, without a selected line. -/
theorem rank_raw_member (a p r m : ℕ) [Fact p.Prime] (s : Finset (Fin r))
    (ha : a = 1 ∨ a = 3) (hp29 : 29 ≤ p) (hp4 : ¬ p ∣ 4)
    (hrp : r ≤ 5 * p) (hm1 : 10 * m ≤ r + 5) (cert : ZMod p → FibreCert)
    (hOk : ∀ x, (cert x).Ok) (hInt : ∀ x, (cert x).Integral p)
    (hReal : ∀ x, Realizes (lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1)
      (rowsOf r m s) (colsOf r m s) x (cert x)) (L E : ℚ)
    (hR : L - E ≤ ((∑ x : ZMod p, (cert x).kr.card : ℕ) : ℚ))
    (hC : L - E ≤ ((∑ x : ZMod p, (cert x).kc.card : ℕ) : ℚ)) :
    ∃ M : RankMember (pipelineFrame a ha) (u4 a) q4 (fun c : Fin r => (c : ℕ))
      (fun j : Fin m => r + 2 * (j : ℕ)) (fun j : Fin m => r + 2 * (j : ℕ) + 1) s p,
      (M.price : ℚ) ≤ (11 / 5 : ℚ) * r - L + 1 + E := by
  let PS := lambdaPoleSplit a p r m ha hp29 hp4 hrp hm1
  have hOR := killRows_card_eq_sum PS (rowsOf r m s) (colsOf r m s) (rows_inj r m s) cert hOk hReal
  have hOC := killCols_card_eq_sum PS (rowsOf r m s) (colsOf r m s) (cols_inj r m s) cert hOk hReal
  obtain ⟨bal, hBO, hBI, hBR, hK, hKC⟩ :=
    RankTools.exists_balanced_realization PS r m s cert hOk hInt hReal
  have hBC : (killRows (p := p) (rowsOf r m s) bal).card =
      (killCols (p := p) (colsOf r m s) bal).card := hK.trans hKC.symm
  have hw : ((1, 0) : RatFunc (ZMod p) × RatFunc (ZMod p)) ≠ 0 := by
    intro h
    have hf := congrArg Prod.fst h
    exact one_ne_zero hf
  let M := rankMemberOfAssignment a p r m s ha hp29 hp4 hrp hm1 bal hBO hBI hBR hBC (1, 0) hw
  have hMK : M.killCount = min (killRows (p := p) (rowsOf r m s) cert).card
      (killCols (p := p) (colsOf r m s) cert).card := hK
  have hKR : M.killCount ≤ s.card + m := by
    change (killRows (p := p) (rowsOf r m s) bal).card ≤ s.card + m
    simpa only [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin] using
      (Finset.card_le_univ (killRows (p := p) (rowsOf r m s) bal))
  have hraw : M.price ≤ (s.card + m) + (s.card + m - M.killCount) := by
    simpa only [Fintype.card_sum, Fintype.card_coe, Fintype.card_fin] using M.price_le_raw
  have hN : M.price + M.killCount ≤ 2 * (s.card + m) := by omega
  have hQ : (M.price : ℚ) + (M.killCount : ℚ) ≤ 2 * ((s.card : ℚ) + (m : ℚ)) := by exact_mod_cast hN
  have hmin : L - E ≤ (M.killCount : ℚ) := by
    rw [hMK]
    rcases le_total (killRows (p := p) (rowsOf r m s) cert).card
        (killCols (p := p) (colsOf r m s) cert).card with h | h
    · rw [min_eq_left h, hOR]; exact hR
    · rw [min_eq_right h, hOC]; exact hC
  have hs : s.card ≤ r := by simpa using Finset.card_le_univ s
  have hsQ : (s.card : ℚ) ≤ r := by exact_mod_cast hs
  have hmQ : (10 : ℚ) * m ≤ r + 5 := by exact_mod_cast hm1
  exact ⟨M, by linarith⟩

#print axioms rank_raw_member
end CatalanCore.Uniform.Bank.Lambda
