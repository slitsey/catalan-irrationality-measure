module

public import CatalanCore.Uniform.Bank.FourthsContent.Mu
public import CatalanCore.Uniform.Content.BankShared.Check.Normalise
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.Trop
public import CatalanFrames.Lambda.HybInst
public import CatalanFrames.LambdaMirrorHybrid.MirFinal
public import CatalanFrames.LambdaMirrorHybrid.MirTrop
public import CatalanCore.Uniform.Bank.Fourths.Final
public import CatalanCore.Uniform.Bank.Fourths.TwoTerm
public import CatalanCore.Uniform.Bank.Fourths.Frame
public import CatalanCore.Arith.Hybrid.PieceTools

@[expose] public section
set_option Elab.async false

/-! # Automatic content of the λ± frames (lane C1L)

The content of `lambdaFrame false` (λ−, `lamFrame`, member `a = 3`, offset `o = 1`) and `lambdaFrame true`
(λ+, `mirFrame`, member `a = 1`, offset `o = 3`) from the one bank check (`hasScaledContent_of_check`):

* data: `AutoData.bankData` (C1's generated UF template, `n = 100`), `bank_check : check bankData = true`;
* instance hypotheses, λ−: `lamMinus_catValid` (`catValid_bankUFwP` at `lamInst`, `lam_badInfo`, `lam_tropFacts`,
  the two-term data of `pipeline false`, norm `16`, bad primes `{2}`, `P_bad = 28`, `K = 10`, `N1 = 44`) and
  `lamMinus_preValid` (`pre_gle_any`, `p ≤ r/1000`, `α0 = 11/5`);
* instance hypotheses, λ+: the same on the sign-normalised mirror `mirNFrame` (`mirNInst`, `mirBad`,
  `mirN_tropFacts`, two-term data of `pipeline true`), transported to `mirFrame` along `mir_Mn_neg`
  (`catValid_neg`, `preValid_neg`);
* `lamMinus_content_auto`, `lamPlus_content_auto`: `HasScaledContent ((FL.family (lambdaFrame sgn) depth).restrictAdm
  even) FL.scale Λ_fin`, `Λ_fin = bankData.Λ` (`bankData_Λ`), every depth `≤ 64`;
* `lambda_mu_le` (module `Mu`). -/

namespace CatalanCore.Uniform.Bank.FourthsContent.Auto
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.HybGen CatalanCore.Uniform.Bank.Fourths CatalanCore.Uniform.Content.RankProducer
  CatalanCore.Uniform.Content.Smith
open CatalanFrames.Lambda (lamFrame lamCD lamInst lam_badInfo lam_tropFacts lam_kq_att lam_odd_good)
open CatalanFrames.LambdaMirrorHybrid (mirNFrame mirNInst mirBad mirN_tropFacts mir_kq_att mir_Mn_neg)

/-! ### Frame facts -/

/-- `lamFrame` has the two-term data of `pipeline false` (same `Δ`, `Δ²`): `q = 4`, `o = 1`. -/
theorem lam_twoTerm : TwoTermData lamFrame 4 1 := by
  have T := pipeline_twoTerm 3 (Or.inr rfl)
  exact ⟨T.o_pos, T.o_lt, fun t ht => T.delta_eq t ht, fun t ht => T.dsq_eq t ht⟩

/-- `mirNFrame` has the two-term data of `pipeline true`: `q = 4`, `o = 3`. -/
theorem mirN_twoTerm : TwoTermData mirNFrame 4 3 := by
  have T := pipeline_twoTerm 1 (Or.inl rfl)
  exact ⟨T.o_pos, T.o_lt, fun t ht => T.delta_eq t ht, fun t ht => T.dsq_eq t ht⟩

theorem cFr_lamMinus : cFr (lambdaFrame false) ≤ 36 := by decide +kernel
theorem cFr_lamPlus : cFr (lambdaFrame true) ≤ 36 := by decide +kernel
theorem cFr_mirN : cFr mirNFrame ≤ 36 := by decide +kernel

/-! ### λ− : `lamFrame` -/

/-- The branch catalogue of `bankData` is valid on `lamFrame` (`o = 1`). -/
theorem lamMinus_catValid (depth : ℕ) :
    CatValid (1 / 5) one_fifth_pos lamFrame depth 4 1 28
      (max (NFr (1 / lamFrame.norm) (-1 / lamFrame.norm) 4 10) 44) bankData.cat := by
  rw [bankData_cat]
  exact catValid_bankUFwP lamInst (arith_of_bad lam_badInfo).L_eq lam_tropFacts.toLevelFacts (1 / 5) one_fifth_pos
    (by norm_num) lam_twoTerm (nm := 4 * 4) (by show (16 : ℚ) = ((4 * 4 : ℕ) : ℚ); norm_num) depth 28 10 44
    (by norm_num) (by norm_num) (by norm_num) le_rfl
    (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega, by omega,
      not_bad_of_levels lam_tropFacts.toLevelFacts hp (show 5 ≤ p by omega), (show 5 ≤ p by omega),
      by omega⟩)
    (fun p hp h j k hk hj0 hjq _ _ => by
      have hb := (lam_odd_good hp (by omega)).2
      obtain ⟨h1, -⟩ := kq_eq_poleIndex lamCD (fun _ => rfl) (by norm_num) (by norm_num) hp (by omega) hb
        (lam_kq_att p hp.isPrimePow hb)
      have hk' : 4 * k = j * p + (4 - (4 - 1)) := hk
      have h2 := (rootClass_unique hp (by norm_num) (by norm_num) (by omega) hjq hk').2
      show lamCD.kq p = k
      rw [h1, h2])
    bankWins bankPres

/-- The prefix bound of `lamFrame` (`pre_gle_any`), for `p ≤ r/1000`, `α0 = 11/5`. -/
theorem lamMinus_preValid (depth : ℕ) :
    PreValid (1 / 5) one_fifth_pos lamFrame depth 4 (SmallBudget.add (SmallBudget.sqrtLog 5 96) SmallBudget.unit)
      (qq 1 1000) (qq 11 5) := by
  intro i hi p _ _ h
  have hp : p.Prime := Fact.out
  have e1 : ((qq 1 1000 : ℚ) : ℝ) = ((1 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by norm_num [qq]
  rw [e1, floor_frac 1 1000 i.1] at h
  have h1000 : 1000 * p ≤ i.1 := by omega
  have hp2 := hp.two_le
  have hr2 : i.1 % 2 = 0 := hi.2
  obtain ⟨hb1, hb2⟩ := altGeom_border_nat (1 / 5) one_fifth_pos 1 5 (by norm_num) (by norm_num) hr2
  have hR : (5 : ℝ) * (2 * ((altGeom (1 / 5) one_fifth_pos).borderSize i.1 : ℝ)) < 1 * i.1 + 5 := by
    exact_mod_cast hb2
  have hbad : p ∈ lamInst.cd.bad → p * p ≤ 5 * i.1 := by
    intro hpb
    have hp3 : p ≤ 3 := lam_badInfo.bad_le p hpb
    have : p * p ≤ 3 * 3 := Nat.mul_le_mul hp3 hp3
    omega
  obtain ⟨n, hn, hle⟩ := pre_gle_any lamInst (arith_of_bad lam_badInfo).L_eq (1 / 5) one_fifth_pos
    (by norm_num) depth i hr2 (by omega) p 5 96 3 36 (11 / 5) (by norm_num) cFr_lamMinus (by norm_num) hbad
    (by omega) (by norm_num; omega) (by omega) (by omega) (by linarith) (by omega)
  refine ⟨n, hn, ?_⟩
  have e2 : ((qq 11 5 : ℚ) : ℝ) = 11 / 5 := by norm_num [qq]
  rw [e2]
  exact hle

/-- **Automatic content of λ−** (`lambdaFrame false = lamFrame`, member `a = 3`). -/
theorem lamMinus_content_auto (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent ((FL.family (lambdaFrame false) depth).restrictAdm (fun i => i.1 % 2 = 0)) FL.scale
      ((bankData.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_check bankData bank_check (1 / 5) one_fifth_pos (by norm_num) (by decide +kernel)
    (lambdaFrame false) depth hd cFr_lamMinus 3 (by decide) _ _ (lamMinus_catValid depth)
    (lamMinus_preValid depth)

/-! ### λ+ : `mirFrame`, through the sign-normalised mirror `mirNFrame` -/

/-- The branch catalogue of `bankData` is valid on `mirNFrame` (`o = 3`). -/
theorem mirN_catValid (depth : ℕ) :
    CatValid (1 / 5) one_fifth_pos mirNFrame depth 4 3 28
      (max (NFr (1 / mirNFrame.norm) (-1 / mirNFrame.norm) 4 10) 44) bankData.cat := by
  rw [bankData_cat]
  exact catValid_bankUFwP mirNInst (arith_of_bad mirBad).L_eq mirN_tropFacts.toLevelFacts (1 / 5) one_fifth_pos
    (by norm_num) mirN_twoTerm (nm := 4 * 4) (by show (16 : ℚ) = ((4 * 4 : ℕ) : ℚ); norm_num) depth 28 10 44
    (by norm_num) (by norm_num) (by norm_num) le_rfl
    (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega, by omega,
      not_bad_of_levels mirN_tropFacts.toLevelFacts hp (show 5 ≤ p by omega), (show 5 ≤ p by omega),
      by omega⟩)
    (fun p hp h j k hk hj0 hjq _ _ => by
      have hb := (mirN_tropFacts.good p hp (show 5 ≤ p by omega)).2
      obtain ⟨h1, -⟩ := kq_eq_poleIndex mirNInst.cd (fun _ => rfl) (by norm_num) (by norm_num) hp (by omega)
        hb (mir_kq_att p hp.isPrimePow hb)
      have hk' : 4 * k = j * p + (4 - (4 - 3)) := hk
      have h2 := (rootClass_unique hp (by norm_num) (by norm_num) (by omega) hjq hk').2
      rw [h1, h2])
    bankWins bankPres

/-- The prefix bound of `mirNFrame` (`pre_gle_any`), for `p ≤ r/1000`, `α0 = 11/5`. -/
theorem mirN_preValid (depth : ℕ) :
    PreValid (1 / 5) one_fifth_pos mirNFrame depth 4 (SmallBudget.add (SmallBudget.sqrtLog 5 96) SmallBudget.unit)
      (qq 1 1000) (qq 11 5) := by
  intro i hi p _ _ h
  have hp : p.Prime := Fact.out
  have e1 : ((qq 1 1000 : ℚ) : ℝ) = ((1 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by norm_num [qq]
  rw [e1, floor_frac 1 1000 i.1] at h
  have h1000 : 1000 * p ≤ i.1 := by omega
  have hp2 := hp.two_le
  have hr2 : i.1 % 2 = 0 := hi.2
  obtain ⟨hb1, hb2⟩ := altGeom_border_nat (1 / 5) one_fifth_pos 1 5 (by norm_num) (by norm_num) hr2
  have hR : (5 : ℝ) * (2 * ((altGeom (1 / 5) one_fifth_pos).borderSize i.1 : ℝ)) < 1 * i.1 + 5 := by
    exact_mod_cast hb2
  have hbad : p ∈ mirNInst.cd.bad → p * p ≤ 5 * i.1 := by
    intro hpb
    have hp3 : p ≤ 3 := mirBad.bad_le p hpb
    have : p * p ≤ 3 * 3 := Nat.mul_le_mul hp3 hp3
    omega
  obtain ⟨n, hn, hle⟩ := pre_gle_any mirNInst (arith_of_bad mirBad).L_eq (1 / 5) one_fifth_pos
    (by norm_num) depth i hr2 (by omega) p 5 96 3 36 (11 / 5) (by norm_num) cFr_mirN (by norm_num) hbad
    (by omega) (by norm_num; omega) (by omega) (by omega) (by linarith) (by omega)
  refine ⟨n, hn, ?_⟩
  have e2 : ((qq 11 5 : ℚ) : ℝ) = 11 / 5 := by norm_num [qq]
  rw [e2]
  exact hle

/-- **Automatic content of λ+** (`lambdaFrame true = mirFrame`, member `a = 1`): the mirror's hypotheses
transported along `mirFrame.Mn = -mirNFrame.Mn`. -/
theorem lamPlus_content_auto (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent ((FL.family (lambdaFrame true) depth).restrictAdm (fun i => i.1 % 2 = 0)) FL.scale
      ((bankData.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_check bankData bank_check (1 / 5) one_fifth_pos (by norm_num) (by decide +kernel)
    (lambdaFrame true) depth hd cFr_lamPlus 1 (by decide) _ _
    (catValid_neg (Fr := lambdaFrame true) mir_Mn_neg (mirN_catValid depth))
    (preValid_neg (Fr := lambdaFrame true) mir_Mn_neg (mirN_preValid depth))

#print axioms lamMinus_content_auto
#print axioms lamPlus_content_auto
#print axioms bank_check
#print axioms bankData_Λ

end CatalanCore.Uniform.Bank.FourthsContent.Auto
