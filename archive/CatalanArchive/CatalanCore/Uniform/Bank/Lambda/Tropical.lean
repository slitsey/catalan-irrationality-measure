import CatalanFrames.LambdaMirrorHybrid.MirTrop
import CatalanCore.Uniform.Bank.Lambda.TwoTerm
import CatalanCore.Uniform.Bank.Lambda.Layers
import CatalanCore.Uniform.Bank.Lambda.MemberIdentity
import CatalanFrames.Lambda.HybInst
import CatalanFrames.LambdaMirrorHybrid.MirInst
import CatalanFrames.LambdaMirrorHybrid.MirFinal
import CatalanFrames.HybCommon.Numer
import CatalanCore.Rect.MinorContent
set_option Elab.async false
namespace CatalanCore.Uniform.Bank.Lambda
open CatalanCore CatalanCore.Arith.Hybrid CatalanCore.Uniform CatalanCore.Rect
open CatalanCore.Uniform.Content.BankShared

/-- The existing entrywise instances, used on the new one-fifth node family. -/
noncomputable def lambdaHybInst (sgn : Bool) : HybInst (lambdaFrame sgn) :=
  match sgn with
  | false => CatalanFrames.Lambda.lamInst
  | true => CatalanFrames.LambdaMirrorHybrid.mirInst

instance lambdaHybInst_diagOK (sgn : Bool) (r m : ℕ) : (lambdaHybInst sgn).DiagOK r m := by
  cases sgn
  · exact CatalanFrames.Lambda.lamInst_diagOK r m
  · exact CatalanFrames.LambdaMirrorHybrid.mirInst_diagOK r m

/-- The full tropical exponent clears every actual common-deletion member. -/
theorem lambda_tropical_gle (sgn : Bool) (depth : ℕ) (i : (FamE (lambdaFrame sgn) depth).ι)
    (hi : (FamE (lambdaFrame sgn) depth).Adm i) (p : ℕ) [Fact p.Prime] :
    GLE p (tropExp (lambdaHybInst sgn) i.1 (FL.borderSize i.1) p)
      ((FamE (lambdaFrame sgn) depth).Q i) := by
  rcases i with ⟨r, S⟩
  have hQ := lambda_member_commonMinor (lambdaFrame sgn) depth r hi.2 S
  change GLE p (tropExp (lambdaHybInst sgn) r (FL.borderSize r) p)
    ((FL.family (lambdaFrame sgn) depth).Q ⟨r, S⟩)
  rw [hQ]
  exact commonMinorPoly_gle (lambdaHybInst sgn) p r (FL.borderSize r)
    (retainedFin (FL_hyb hi.2) S)

/-- The actual tropical layer is available to the same certified minimum as rank and LP. -/
noncomputable def lambdaTropical (sgn : Bool) (depth : ℕ) :
    CertifiedPrice (FamE (lambdaFrame sgn) depth) where
  price i p := tropExp (lambdaHybInst sgn) i.1 (FL.borderSize i.1) p
  gle := lambda_tropical_gle sgn depth

/-- Only the existing small bad primes occur in these entrywise instances. -/
theorem lambda_badInfo (sgn : Bool) : CatalanFrames.HybCommon.BadInfo (lambdaHybInst sgn) 4 4 := by
  cases sgn
  · exact CatalanFrames.Lambda.lam_badInfo
  · refine ⟨rfl, le_rfl, le_rfl, (fun N => CatalanFrames.HybCommon.cubic_Ebd N), ?_, ?_, ?_⟩
    · change 2 ∈ ({2, 3} : Finset ℕ)
      decide
    · intro b hb
      change b ∈ ({2, 3} : Finset ℕ) at hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      omega
    · intro p
      change CatalanFrames.HybCommon.cOf CatalanFrames.LambdaMirrorHybrid.mirNInst p ≤ 4
      exact CatalanFrames.LambdaMirrorHybrid.mir_cOf_le p

/-- In the single-level band, the exact table-T value clears the new family. -/
theorem lambda_tableT_gle (sgn : Bool) (depth : ℕ) (i : (FamE (lambdaFrame sgn) depth).ι)
    (hi : (FamE (lambdaFrame sgn) depth).Adm i) (hr1 : 1 ≤ i.1)
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (hsq : 4 * (i.1 + 2 * FL.borderSize i.1) < p * p) :
    GLE p (CatalanFrames.HybGen.XGm (lambdaHybInst sgn) i.1 (FL.borderSize i.1) p)
      ((FamE (lambdaFrame sgn) depth).Q i) := by
  have hb := lambda_badInfo sgn
  have hpp : p.Prime := Fact.out
  have hnb : p ∉ (lambdaHybInst sgn).cd.bad := by
    intro h
    have hle := hb.bad_le p h
    omega
  have hcnt : CatalanFrames.HybCommon.cntG (lambdaHybInst sgn) i.1 (FL.borderSize i.1) p = 0 := by
    apply CatalanFrames.HybCommon.cntG_zero _ _ _ _ hpp
    rw [hb.L_eq]
    nlinarith
  have hle := CatalanFrames.HybCommon.tropExp_leG hb i.1 (FL.borderSize i.1) p hr1 hpp
  rw [if_neg hnb, hcnt] at hle
  simp only [if_neg hnb, Nat.cast_zero, mul_zero, add_zero, zero_add] at hle
  have hle' : tropExp (lambdaHybInst sgn) i.1 (FL.borderSize i.1) p ≤
      CatalanFrames.HybGen.XGm (lambdaHybInst sgn) i.1 (FL.borderSize i.1) p := by
    unfold CatalanFrames.HybGen.XGm
    exact_mod_cast hle
  exact (lambda_tropical_gle sgn depth i hi p).mono hle'

#print axioms lambda_tropical_gle
#print axioms lambda_tableT_gle
#print axioms lambdaTropical
/-- The sign change in the mirror preserves all entrywise level facts. -/
theorem lambda_levelFacts (sgn : Bool) :
    CatalanFrames.HybCommon.LevelFacts (lambdaHybInst sgn) (fun p => 5 ≤ p)
      (fun q c => c < (lambdaHybInst sgn).cd.kq q) := by
  cases sgn
  · exact CatalanFrames.Lambda.lam_tropFacts.toLevelFacts
  · refine ⟨?_, ?_, ?_⟩
    · exact CatalanFrames.LambdaMirrorHybrid.mirN_tropFacts.good
    · exact CatalanFrames.LambdaMirrorHybrid.mirN_tropFacts.zero_iff
    · exact CatalanFrames.LambdaMirrorHybrid.mirN_tropFacts.high

/-- The exact pole equation only needs an odd prime at least five. -/
theorem one_based_pole4_five (a p : ℕ) (ha : a = 1 ∨ a = 3) (hp5 : 5 ≤ p)
    (hodd : p % 2 = 1) :
    (root4 a p = 1 ∨ root4 a p = 3) ∧
    4 * (pole4 a p + 1) = root4 a p * p + (4 - a) ∧
    0 < pole4 a p + 1 ∧ pole4 a p + 1 < p ∧ 0 < root4 a p := by
  obtain ⟨hj, hk, hkp⟩ := root4_spec a p ha hodd
  have hroot : 4 * pole4 a p + a = root4 a p * p := by simpa [Nat.mul_comm] using hk
  have hja : root4 a p ≤ 3 := by omega
  have hjp : root4 a p * p ≤ 3 * p := Nat.mul_le_mul_right p hja
  exact ⟨hj, by omega, by omega, by omega, by omega⟩

/-- The entrywise table and rank pipeline use the same one-based pole. -/
theorem lambda_kq_eq (sgn : Bool) (p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hodd : p % 2 = 1) :
    (lambdaHybInst sgn).cd.kq p = pole4 (pipelineNum sgn) p + 1 := by
  have hpp : p.Prime := Fact.out
  have h4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hk := (one_based_pole4_five (pipelineNum sgn) p (pipelineNum_valid sgn) hp5 hodd).2.1
  cases sgn
  · change 4 * (pole4 3 p + 1) = root4 3 p * p + 1 at hk
    change CatalanFrames.Lambda.lamInst.cd.kq p = pole4 3 p + 1
    rcases h4 with h4 | h4
    · have h := CatalanFrames.Lambda.lam_tropFacts.kq3 p hpp (by omega) h4
      rw [h]
      norm_num [root4, h4] at hk
      omega
    · have h := CatalanFrames.Lambda.lam_tropFacts.kq1 p hpp (by omega) (by omega)
      rw [h]
      norm_num [root4, h4] at hk
      omega
  · change 4 * (pole4 1 p + 1) = root4 1 p * p + 3 at hk
    change CatalanFrames.LambdaMirrorHybrid.mirNInst.cd.kq p = pole4 1 p + 1
    rcases h4 with h4 | h4
    · have h := CatalanFrames.LambdaMirrorHybrid.mirN_tropFacts.kq1 p hpp (by omega) (by omega)
      rw [h]
      norm_num [root4, h4] at hk
      omega
    · have h := CatalanFrames.LambdaMirrorHybrid.mirN_tropFacts.kq3 p hpp (by omega) h4
      rw [h]
      norm_num [root4, h4] at hk
      omega

/-- The small-prime table bound in the entire band p > m. -/
theorem lambda_tableT_D1 (sgn : Bool) (r m p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hmp : m < p) :
    CatalanFrames.HybGen.XGm (lambdaHybInst sgn) r m p ≤
      2 * r + 2 * m - min m (p - m) := by
  have h := CatalanFrames.HybGen.XGm_D1x (lambdaHybInst sgn) r m p Fact.out (by omega)
  simpa only [Nat.mod_eq_of_lt hmp] using h

/-- Table D4/D5 on the actual unrestricted border size. -/
theorem lambda_tableT_D45 (sgn : Bool) (r m p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hodd : p % 2 = 1) (hrp : r < p) (hmr : 2 * m ≤ r) :
    CatalanFrames.HybGen.XGm (lambdaHybInst sgn) r m p ≤
      2 * (r - (pole4 (pipelineNum sgn) p + 1)) + 2 * m + (2 * m - (p - r)) := by
  have h := CatalanFrames.HybGen.XGm_D45 (lambda_levelFacts sgn) r m p Fact.out
    (by omega) hrp hmr
  rwa [lambda_kq_eq sgn p hp5 hodd] at h

/-- Table D6, including its zero tail. -/
theorem lambda_tableT_D6 (sgn : Bool) (r m p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hodd : p % 2 = 1) (hN : r + 2 * m ≤ p)
    (hkr : r ≤ pole4 (pipelineNum sgn) p + 1) :
    CatalanFrames.HybGen.XGm (lambdaHybInst sgn) r m p ≤
      2 * m - ((pole4 (pipelineNum sgn) p + 1) - r) := by
  have hkr' : r ≤ (lambdaHybInst sgn).cd.kq p := by
    rwa [lambda_kq_eq sgn p hp5 hodd]
  have h := CatalanFrames.HybGen.XGm_D6 (lambda_levelFacts sgn) r m p Fact.out
    (by omega) hN hkr'
  rwa [lambda_kq_eq sgn p hp5 hodd] at h

#print axioms lambda_levelFacts
#print axioms lambda_kq_eq
#print axioms lambda_tableT_D6
/-- Exact parity and border rounding give the zero tail at the profile endpoint. -/
theorem lambda_tableT_tail (sgn : Bool) (r m p : ℕ) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hodd : p % 2 = 1) (hr : r % 2 = 0)
    (hm : 10 * m ≤ r + 5) (hcut : 24 * r < 5 * p) :
    CatalanFrames.HybGen.XGm (lambdaHybInst sgn) r m p = 0 := by
  obtain ⟨hj, hk, hk0, hkp, hj0⟩ := one_based_pole4_five (pipelineNum sgn) p
    (pipelineNum_valid sgn) hp5 hodd
  have hNk : r + 2 * m ≤ pole4 (pipelineNum sgn) p + 1 := by
    rcases pipelineNum_valid sgn with ha | ha <;> rcases hj with hj | hj <;>
      rw [ha, hj] at hk <;> omega
  have hN : r + 2 * m ≤ p := by omega
  have h := lambda_tableT_D6 sgn r m p hp5 hodd hN (by omega)
  omega

#print axioms lambda_tableT_tail
end CatalanCore.Uniform.Bank.Lambda
