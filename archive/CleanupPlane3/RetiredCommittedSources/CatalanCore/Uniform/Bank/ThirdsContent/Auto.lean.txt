module

public import CatalanCore.Uniform.Content.BankShared.Check.Rank
public import CatalanCore.Uniform.Content.BankShared.Check.Test
public import CatalanCore.Uniform.Bank.ThirdsContent.Edge

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Thirds acceptance test of automatic content, no UF (lane C1L)

The content of both thirds frames from the one bank check (`hasScaledContent_of_check`):

* data: the templates and certificates of `Check.Test.thirdsData` (the pieces of `Tmpl/*.lean`), at depth `≤ 64`;
* `noUF_check : check noUF = true`, by `decide +kernel` (one declaration per chunk);
* instance hypotheses: `thirds_catValid` (`catValid_bank` with the thirds instance `thirdsInst`,
  `thirds_badInfo`, `thirds_levels`: norm `9`, bad primes `{2, 3}`, good primes `p ≥ 5`, all `≤ P_bad = 5`) and
  `thirds_preValid` (`thirds_pre_gle`);
* `thirdsAc_content_auto`, `thirdsBc_content_auto`: `HasScaledContent (FamE thirdsX depth) G310.scale Λ_fin`,
  `Λ_fin = noUF.Λ` (`noUF_Λ`: the `LamFin` of `Final.lean`). -/

namespace CatalanCore.Uniform.Bank.ThirdsContent.Auto
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Content.BankShared.TwoTerm
  CatalanCore.Uniform.Content.SmallPrimes CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanFrames.HybCommon
  CatalanFrames.HybGen CatalanFrames.Thirds CatalanCore.Uniform.Bank.ThirdsContent
  CatalanCore.Uniform.Bank.Thirds CatalanCore.Uniform.Content.RankProducer

/-! ### Data and the check -/

/-- The thirds no-UF bank (templates and certificates of `Check.Test.thirdsData`), depth `≤ 64`. -/
def noUF : BankData := { Test.thirdsData with depth := 64 }

theorem noUF_Λ : noUF.Λ =
    (1194048404178978899352258982735187880439 / 360228242681094717840986896769807040000 : ℚ) := by
  decide +kernel

set_option profiler true in
theorem noUF_p0_1 : pieceAll noUF 1 Test.c_prefTmpl0 = true := by decide +kernel
set_option profiler true in
theorem noUF_p1_1 : pieceAll noUF 1 Test.c_prefTmpl1 = true := by decide +kernel
set_option profiler true in
theorem noUF_p2_1 : pieceAll noUF 1 Test.c_prefTmpl2 = true := by decide +kernel
set_option profiler true in
theorem noUF_q0_1 : pieceAll noUF 1 Test.c1_profTmpl1_0 = true := by decide +kernel
set_option profiler true in
theorem noUF_q1_1 : pieceAll noUF 1 Test.c1_profTmpl1_1 = true := by decide +kernel
set_option profiler true in
theorem noUF_head_1 : tmplHead noUF 1 Test.thirdsT1 = true := by decide +kernel
set_option profiler true in
theorem noUF_p0_2 : pieceAll noUF 2 Test.c_prefTmpl0 = true := by decide +kernel
set_option profiler true in
theorem noUF_p1_2 : pieceAll noUF 2 Test.c_prefTmpl1 = true := by decide +kernel
set_option profiler true in
theorem noUF_p2_2 : pieceAll noUF 2 Test.c_prefTmpl2 = true := by decide +kernel
set_option profiler true in
theorem noUF_q0_2 : pieceAll noUF 2 Test.c2_profTmpl2_0 = true := by decide +kernel
set_option profiler true in
theorem noUF_q1_2 : pieceAll noUF 2 Test.c2_profTmpl2_1 = true := by decide +kernel
set_option profiler true in
theorem noUF_head_2 : tmplHead noUF 2 Test.thirdsT2 = true := by decide +kernel
set_option profiler true in
theorem noUF_params : checkParams noUF = true := by decide +kernel
set_option profiler true in
theorem noUF_classes : noUF.members.all (classOK noUF) = true := by decide +kernel

theorem noUF_T1 : tmplOK noUF 1 Test.thirdsT1 = true := by
  unfold tmplOK
  rw [noUF_head_1]
  show (true && pieceAll noUF 1 (Test.c_prefTmpl0 ++ (Test.c_prefTmpl1 ++ (Test.c_prefTmpl2 ++
    (Test.c1_profTmpl1_0 ++ Test.c1_profTmpl1_1))))) = true
  simp only [pieceAll_append, noUF_p0_1, noUF_p1_1, noUF_p2_1, noUF_q0_1, noUF_q1_1, Bool.and_self]

theorem noUF_T2 : tmplOK noUF 2 Test.thirdsT2 = true := by
  unfold tmplOK
  rw [noUF_head_2]
  show (true && pieceAll noUF 2 (Test.c_prefTmpl0 ++ (Test.c_prefTmpl1 ++ (Test.c_prefTmpl2 ++
    (Test.c2_profTmpl2_0 ++ Test.c2_profTmpl2_1))))) = true
  simp only [pieceAll_append, noUF_p0_2, noUF_p1_2, noUF_p2_2, noUF_q0_2, noUF_q1_2, Bool.and_self]

theorem noUF_tmpls : noUF.tmpls.all (fun x => tmplOK noUF x.1 x.2) = true := by
  show [(1, Test.thirdsT1), (2, Test.thirdsT2)].all (fun x => tmplOK noUF x.1 x.2) = true
  simp only [List.all_cons, List.all_nil, noUF_T1, noUF_T2, Bool.and_self]

/-- **The bank check accepts the thirds no-UF data.** -/
theorem noUF_check : check noUF = true := by
  unfold check
  rw [noUF_params, noUF_tmpls, noUF_classes]
  rfl

/-! ### Instance hypotheses of the thirds frames -/

/-- The branch catalogue of `noUF` is valid on every thirds frame (`ThirdsData Fr e`, `o = e`), with the rank
bound `N0 = NFr` of `rankClosedLayer` and `K = 7` (`(3/10) · 7 ≥ 2`). -/
theorem thirds_catValid {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (depth : ℕ) :
    CatValid (3 / 10) c310_pos Fr depth 3 e 5 (NFr (1 / Fr.norm) (-1 / Fr.norm) 3 7) noUF.cat := by
  have he := T.he
  exact catValid_bank (thirdsInst T) (arith_of_bad (thirds_badInfo T)).L_eq (thirds_levels T) (3 / 10)
    c310_pos (by norm_num) (ThirdsData.twoTerm T) (nm := 3 * 3) (by rw [T.norm_eq]; norm_num) depth 5 7
    (by norm_num) (by norm_num) le_rfl
    (fun p hp h => ⟨not_dvd_sq_of_lt hp (by norm_num) (by omega), by omega, by omega,
      not_bad_of_levels (thirds_levels T) hp (show 5 ≤ p by omega), (show 5 ≤ p by omega), by omega⟩)
    (fun p hp h j k hk hj0 hjq _ _ => by
      have h5 : 5 ≤ p := by omega
      have hb := (thirds_good T hp h5).2
      obtain ⟨h1, -⟩ := kq_eq_poleIndex (thirdsCD T) (fun _ => rfl) (by omega) (by omega) hp (by omega) hb
        (thirds_kq_att T p hp.isPrimePow hb)
      have hk' : 3 * k = j * p + (3 - (3 - e)) := by rw [show 3 - (3 - e) = e by omega]; exact hk
      have h2 := (rootClass_unique hp (by omega) (by omega) (by omega) hjq hk').2
      show (thirdsCD T).kq p = k
      rw [h1, h2])
    [(3, 4), (4, 4), (4, 5), (5, 5), (5, 6), (6, 6), (6, 7), (7, 7), (7, 8)]

/-- The prefix bound of every thirds frame (`thirds_pre_gle`), for `p ≤ 3 r/1000`, `α0 = 23/10`. -/
theorem thirds_preValid {Fr : Frame} {e : ℕ} (T : ThirdsData Fr e) (depth : ℕ) :
    PreValid (3 / 10) c310_pos Fr depth 6 thirdsBudget (Test.qq 3 1000) (Test.qq 23 10) := by
  intro i hi p _ hpM h
  have hp : p.Prime := Fact.out
  have h5 : 5 ≤ p := by
    have h2 : p ≠ 2 := fun h => hpM (by rw [h]; norm_num)
    have h3 : p ≠ 3 := fun h => hpM (by rw [h]; norm_num)
    have h4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
    have := hp.two_le
    omega
  have e1 : ((Test.qq 3 1000 : ℚ) : ℝ) = ((3 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) := by norm_num [Test.qq]
  rw [e1, floor_frac 3 1000 i.1] at h
  obtain ⟨n, hn, hb⟩ := thirds_pre_gle T depth i hi p h5 h
  refine ⟨n, hn, ?_⟩
  have e2 : ((Test.qq 23 10 : ℚ) : ℝ) = 23 / 10 := by norm_num [Test.qq]
  rw [e2]
  exact hb

theorem cFr_thirdsAc_le : CatalanCore.Uniform.Content.BankShared.cFr thirdsAc ≤ 25 := by
  have : CatalanCore.Uniform.Content.BankShared.cFr thirdsAc =
      CatalanCore.Uniform.Bank.ThirdsContent.cFr thirdsAc := rfl
  rw [this, cFr_thirdsAc]; norm_num

theorem cFr_thirdsBc_le : CatalanCore.Uniform.Content.BankShared.cFr thirdsBc ≤ 25 := by
  have : CatalanCore.Uniform.Content.BankShared.cFr thirdsBc =
      CatalanCore.Uniform.Bank.ThirdsContent.cFr thirdsBc := rfl
  rw [this, cFr_thirdsBc]

/-! ### The content of both thirds frames -/

/-- **Automatic content of `thirdsAc`** (member `a = 1`, `o = 2`), no UF. -/
theorem thirdsAc_content_auto (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent (FamE thirdsAc depth) G310.scale ((noUF.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_check noUF noUF_check (3 / 10) c310_pos (by norm_num) (by decide +kernel) thirdsAc
    depth hd cFr_thirdsAc_le 1 (by decide) thirdsBudget _ (thirds_catValid thirdsAc_data depth)
    (thirds_preValid thirdsAc_data depth)

/-- **Automatic content of `thirdsBc`** (member `a = 2`, `o = 1`), no UF. -/
theorem thirdsBc_content_auto (depth : ℕ) (hd : depth ≤ 64) :
    HasScaledContent (FamE thirdsBc depth) G310.scale ((noUF.Λ : ℚ) : ℝ) :=
  hasScaledContent_of_check noUF noUF_check (3 / 10) c310_pos (by norm_num) (by decide +kernel) thirdsBc
    depth hd cFr_thirdsBc_le 2 (by decide) thirdsBudget _ (thirds_catValid thirdsBc_data depth)
    (thirds_preValid thirdsBc_data depth)

end CatalanCore.Uniform.Bank.ThirdsContent.Auto
