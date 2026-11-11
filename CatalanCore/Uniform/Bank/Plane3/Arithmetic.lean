module

public import CatalanCore.Uniform.Bank.Plane3.Frame
public import CatalanCore.Uniform.Bank.Plane3.Data
public import CatalanCore.Uniform.Support.HPoleRefinedCatalogue

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # Plane 3: actual rational coefficient arithmetic (Q09)
The general all-order suppliers are reused on the exact datum sequences.
All common deletions and all rational coefficients are retained. The first
coefficient is zero; no numerator-prime exclusion or new ND assertion occurs.
-/
namespace CatalanCore.Uniform.Bank.Plane3
open CatalanCore CatalanCore.Basic CatalanCore.Uniform CatalanCore.Uniform.Support
open CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Shape
open CatalanCore.Uniform.Content.BankShared CatalanCore.Uniform.Content.BankShared.Check
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.Member
open CatalanCore.Uniform.Content.SmallPrimes Finset Polynomial
open CatalanCore.Uniform.Content.Wire

def coefficients (v u : ℚ) (j : ℕ) : ℚ :=
  if j = 2 then -v else if j = 3 then 2*u else 0

theorem datum_f (v u : ℚ) (hu : u ≠ 0) :
    (datum v u hu).f = hpoleF 4 (coefficients v u) := by
  funext t
  unfold PoleDatum.f hpoleF
  apply Finset.sum_congr rfl
  intro k hk
  change (∑ _i : Fin 1, ∑ j ∈ Icc (1 : ℕ) 3,
    coefficients v u j / ((k : ℚ)+1)^j) = _
  rw [Fin.sum_univ_one]

theorem datum_e (v u : ℚ) (hu : u ≠ 0) :
    (datum v u hu).e = hpoleE 4 (coefficients v u) := by
  funext t
  unfold PoleDatum.e hpoleE
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  change -(-(∑ _i : Fin 1, ∑ j ∈ Icc (1 : ℕ) 3,
    (j : ℚ)*coefficients v u j / ((k : ℚ)+1)^(j+1))) = _
  rw [neg_neg, Fin.sum_univ_one]

def coefficientThreshold (v u : ℚ) : ℕ := IntegerPoleRows.coeffCrude 4 (coefficients v u)

theorem coefficients_mem (v u : ℚ) {p : ℕ} [Fact p.Prime]
    (hp : coefficientThreshold v u < p) :
    ∀ j ∈ Icc (1 : ℕ) 3, coefficients v u j ∈ LocRing p := by
  intro j hj
  have hden : (coefficients v u j).den ≤ coefficientThreshold v u := by
    exact Finset.single_le_sum (f := fun j => (coefficients v u j).den)
      (fun _ _ => Nat.zero_le _) hj
  rw [mem_locRing]
  intro hd
  have := Nat.le_of_dvd (coefficients v u j).den_pos hd
  omega

theorem plane3_catalogue (v u : ℚ) (c : ℚ) (hc : 0 < c) (const : ℝ) (depth : ℕ) :
    KCatValidFam c hc const depth
      (SeqFamily.poly (hpoleF 4 (coefficients v u)) (hpoleE 4 (coefficients v u))
        (altGeom c hc).geometry)
      [⟨2,1,1⟩, ⟨2,1,1⟩] 2 2 (coefficientThreshold v u) plane3Catalogue := by
  exact hpole_refined_catalogue 4 (by decide) (coefficients v u) c hc const depth
    [⟨2,1,1⟩,⟨2,1,1⟩] 2 2 (coefficientThreshold v u)
    (by decide) (by decide) (fun p _ hp => coefficients_mem v u hp)
    plane3Chambers (by intro j hj; norm_num [plane3Chambers] at hj; omega)

def plane3Translation : Transl 200 13 852 816 plane3BaseCatalogue where
  ρ _ br := br
  debit _ _ := rfl
  price := by
    intro n br hbr r p m kv
    simp only [plane3BaseCatalogue, List.mem_singleton] at hbr
    subst br
    simpa [firstBranch, KExpr.evalN, IntegerPoleRows.lowPrice, IntegerPoleRows.delta] using
      IntegerPoleRows.lowPrice_cov 4 (by decide) r m n 13 200 p
  cond := by
    intro n br hbr r p m kv hΩ hcond cd hcd
    simp only [plane3BaseCatalogue, List.mem_singleton] at hbr
    subst br
    simp [firstBranch] at hcd

theorem plane3_translated_catalogue (v u : ℚ) (c : ℚ) (hc : 0 < c)
    (const : ℝ) (depth n : ℕ) :
    KCatValidFam c hc const depth
      (SeqFamily.poly (hpoleF 4 (coefficients v u)) (hpoleE 4 (coefficients v u))
        (altGeom c hc).geometry)
      [⟨2,1,1⟩, ⟨2,1,1⟩] 2 2 (coefficientThreshold v u)
      (plane3BaseCatalogue.map (plane3Translation.ρ n)) := by
  intro br hbr
  have hm : br = firstBranch := by
    simpa only [plane3BaseCatalogue,List.map_cons,List.map_nil,List.mem_singleton,plane3Translation] using hbr
  subst br
  have old := hpole_catalogue 4 (by decide) (coefficients v u) c hc const depth
    [⟨2,1,1⟩,⟨2,1,1⟩] 2 2 (coefficientThreshold v u)
    (by decide) (by decide) (fun p _ hp => coefficients_mem v u hp)
  apply old firstBranch
  simp [IntegerPoleRows.catalogue,IntegerPoleRows.firstBranch,firstBranch]

def prefixCutoff (v u : ℚ) : ℕ := 400001 + (coefficientThreshold v u + 1)^2
def crudeFactor (v u : ℚ) : ℕ := coefficientThreshold v u + 5

theorem plane3_scaled_crude (v u : ℚ) (c : ℚ) (hc : 0 < c) (hc1 : c ≤ 1)
    (const : ℝ) (depth : ℕ) :
    ∀ i, (AltEvenFam c hc const depth
      (SeqFamily.poly (hpoleF 4 (coefficients v u)) (hpoleE 4 (coefficients v u))
        (altGeom c hc).geometry)).Adm i →
    ∀ (p : ℕ) [Fact p.Prime],
      GLE p (crudeFactor v u * Ecrude 1 i.1 p)
        (SeqFamily.poly (hpoleF 4 (coefficients v u)) (hpoleE 4 (coefficients v u))
          (altGeom c hc).geometry i) := by
  intro i hi p _
  apply seq_alt_scaled_crude c hc hc1 _ _ (crudeFactor v u) 1 ?_ i hi.2 p
  intro p _ N A B hN hA hB
  have hb := IntegerPoleRows.hpole_lw_gle_crude (p := p) 4 (by decide) (coefficients v u)
    (coefficientThreshold v u)
    (fun j hj => IntegerPoleRows.coeff_scaled_mem (p := p) 4 (coefficients v u) hj) hN hA hB
  refine hb.mono ?_
  dsimp [crudeFactor]
  nlinarith

theorem plane3_pre (v u : ℚ) (const : ℝ) (depth : ℕ) :
    PreValidFam (13/100) (by norm_num) const depth
      (SeqFamily.poly (hpoleF 4 (coefficients v u)) (hpoleE 4 (coefficients v u))
        (altGeom (13/100) (by norm_num)).geometry) 2
      (SmallBudget.sqrtLog (prefixCutoff v u) (32*crudeFactor v u))
      (13/400) (426001/100000) := by
  apply preValid_of_scaled_crude_rows (13/100) (by norm_num) const depth _
    (plane3_scaled_crude v u (13/100) (by norm_num) (by norm_num) const depth)
    2 (SmallBudget.sqrtLog (prefixCutoff v u) (32*crudeFactor v u))
    (prefixCutoff v u) (32*crudeFactor v u) (by omega)
    (fun r p hp hpr => by rw [SmallBudget.sqrtLog_X_of _ _ _ _ hp])
    (13/400) (426001/100000) (by norm_num) (by norm_num)
  intro i hi p _ hsq hpr
  have hr : 0 < i.1 := lt_of_lt_of_le (Fact.out : p.Prime).pos hpr
  have hlarge : prefixCutoff v u < i.1 := by
    have hsqr := Nat.mul_self_le_mul_self hpr
    nlinarith
  have hp : coefficientThreshold v u < p := by
    by_contra hn
    have h1 : p ≤ coefficientThreshold v u := by omega
    have h2 : p*p ≤ (coefficientThreshold v u)^2 := by simpa only [pow_two] using Nat.mul_self_le_mul_self h1
    have h3 : prefixCutoff v u ≤ prefixCutoff v u * i.1 := Nat.le_mul_of_pos_right _ hr
    have h4 : (coefficientThreshold v u)^2 < prefixCutoff v u := by
      dsimp [prefixCutoff]
      nlinarith
    omega
  have hs := altGeom_hybShape (13/100) (by norm_num) hi.2
  have hwin : i.1 + 2*((altGeom (13/100) (by norm_num)).geometry i.1).k < p*p := by
    have hm := altGeom_borderSize_le (13/100) (by norm_num) (by norm_num) hi.2
    rw [geometry_k_eq_borderSize]
    have hA : 3 ≤ prefixCutoff v u := by dsimp [prefixCutoff]; omega
    have hmA := Nat.mul_le_mul_right i.1 hA
    omega
  have hodd : p % 2 = 1 := by
    have hpb : 2 < p := by
      have hA : 3 ≤ prefixCutoff v u := by dsimp [prefixCutoff]; omega
      have hmA := Nat.mul_le_mul_right i.1 hA
      nlinarith [(Fact.out : p.Prime).two_le]
    rcases (Fact.out : p.Prime).eq_two_or_odd with hp2 | hp2 <;> omega
  have hrow := IntegerPoleRows.family_first 4 (by decide) (coefficients v u)
    (coefficients_mem v u hp) hs i.2 hwin hodd
  refine ⟨_, hrow, ?_⟩
  have hle : 4*(i.1+((altGeom (13/100) (by norm_num)).geometry i.1).k) -
      IntegerPoleRows.delta ((altGeom (13/100) (by norm_num)).geometry i.1).k p ≤
      4*(i.1+((altGeom (13/100) (by norm_num)).geometry i.1).k) := Nat.sub_le _ _
  have hb := (TwoTerm.altGeom_border (13/100) (by norm_num) hi.2).2
  have hbR := (Rat.cast_lt (K := ℝ)).2 hb
  push_cast at hbR
  have hrR : (400001 : ℝ) < i.1 := by
    exact_mod_cast (show 400001 < i.1 by dsimp [prefixCutoff] at hlarge; omega)
  have hleR : ((4*(i.1+((altGeom (13/100) (by norm_num)).geometry i.1).k) -
      IntegerPoleRows.delta ((altGeom (13/100) (by norm_num)).geometry i.1).k p : ℕ) : ℝ) ≤
      4*((i.1 : ℝ)+((altGeom (13/100) (by norm_num)).geometry i.1).k) := by exact_mod_cast hle
  change _ ≤ (426001/100000 : ℚ) * (i.1 : ℝ)
  push_cast
  change _ ≤ (426001/100000 : ℝ) * (i.1 : ℝ)
  rw [geometry_k_eq_borderSize] at hleR ⊢
  linarith

end CatalanCore.Uniform.Bank.Plane3
#print axioms CatalanCore.Uniform.Bank.Plane3.datum_f
#print axioms CatalanCore.Uniform.Bank.Plane3.datum_e
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_catalogue
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3Translation
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_translated_catalogue
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_scaled_crude
#print axioms CatalanCore.Uniform.Bank.Plane3.plane3_pre
