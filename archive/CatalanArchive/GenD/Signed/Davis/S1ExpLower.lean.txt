module

public import CatalanMeasure.GenD.Signed.Davis.PolynomialNorm
public import CatalanMeasure.CellCert.RawInts

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 10
namespace CatalanMeasure.GenD.Signed.Davis.S1ExpLower
open CatalanMeasure.Refinement
noncomputable section

theorem rational_pow_le_exp_of_taylor (q x : ℚ) (k n : ℕ)
    (hq : 0 ≤ q) (hx : 0 ≤ x) (h : q ≤ expTaylorRat x n) :
    ((q : ℝ) ^ k) ≤ Real.exp ((k : ℝ) * (x : ℝ)) := by
  have hqR : 0 ≤ (q : ℝ) := by exact_mod_cast hq
  have hR : (q : ℝ) ≤ (expTaylorRat x n : ℝ) := by exact_mod_cast h
  have hb := hR.trans (expTaylorRat_le_exp hx n)
  simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ hqR hb k

def qNum : List ℤ := raw_ints% [45011828794882473817571026637763815595857031]
def expLower : List ℤ := raw_ints% [20409390564934800892831784483473697925122072386350108559141772109285553837214361725756786460388990988535335251349444230864839533924579682345382063377515614367580976771493254347862484737752689741017608603640213662654055440395393026150426551120492203146766926953555392037604218074341299641774514217784632515542667902744072555987699449514861096621845516289840800961332144356086213167139189478632817627258372127903553280383107248544626565563556438401119764687230425433014641320611178169081425982875780397458521342101553781619778099555566570720516658912747513670046321947000529066693655847686559137531751765421108190301967770604686270447536748933361536831312097012783170371188765634106294000572306893063317312085205216841152455862594755261834445847490784863107348142326632589149718361839993887521578222644056796215437810536207072015117920965408446100845353502586403857768339366841630490663057979998115794116080972103691327056869820912194019723561025517540216024315364269207487452387984578801724924574020089992897132233521705172258732518122755732898985630406739450086798019067431837186280100466128735238086696943357520396311362746783153330965184131584441742816229504086603583508956326362701300942438227494064358487170359906293635605392086627030662178144255]
def smallArgument : ℚ := 1581450769073045 / 2251799813685248
def q : ℚ := (qNum.getD 0 0 : ℚ) / 2^144

theorem q_nonneg : 0 ≤ q := by decide +kernel
theorem smallArgument_nonneg : 0 ≤ smallArgument := by decide +kernel
theorem taylor_check : q ≤ expTaylorRat smallArgument 40 := by
  -- kcost: 2 s estimated;40 rational Taylor terms, shared once globally.
  decide +kernel

theorem power_check : (expLower.getD 0 0 : ℚ) ≤ q ^ 4096 := by
  -- kcost: 5 s estimated;one rational power comparison on about590k-bit integers.
  decide +kernel

theorem expLower_le : (expLower.getD 0 0 : ℝ) ≤
    Real.exp (65 * (24330011831893 / 549755813888 : ℝ)) := by
  have hp : (expLower.getD 0 0 : ℝ) ≤ (q : ℝ) ^ 4096 := by
    exact_mod_cast power_check
  have ht := rational_pow_le_exp_of_taylor q smallArgument 4096 40
    q_nonneg smallArgument_nonneg taylor_check
  have he : (4096 : ℝ) * (smallArgument : ℝ) =
      65 * (24330011831893 / 549755813888 : ℝ) := by norm_num [smallArgument]
  norm_num only [Nat.cast_ofNat] at ht
  rw [he] at ht
  exact hp.trans ht

end
end CatalanMeasure.GenD.Signed.Davis.S1ExpLower

#print axioms CatalanMeasure.GenD.Signed.Davis.S1ExpLower.rational_pow_le_exp_of_taylor

#print axioms CatalanMeasure.GenD.Signed.Davis.S1ExpLower.q_nonneg

#print axioms CatalanMeasure.GenD.Signed.Davis.S1ExpLower.smallArgument_nonneg

#print axioms CatalanMeasure.GenD.Signed.Davis.S1ExpLower.taylor_check

#print axioms CatalanMeasure.GenD.Signed.Davis.S1ExpLower.power_check

#print axioms CatalanMeasure.GenD.Signed.Davis.S1ExpLower.expLower_le
