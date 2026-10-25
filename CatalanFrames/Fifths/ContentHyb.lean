module
public import CatalanFrames.Fifths.ClassSum
public import CatalanFrames.Fifths.Extra
public import CatalanFrames.HybGen.NumerologyAny
@[expose] public section
open Finset Filter CatalanCore CatalanCore.Arith CatalanCore.Arith.Hybrid
  CatalanFrames.HybCommon CatalanFrames.HybGen
namespace CatalanFrames.Fifths
variable {Fr : Frame} {u : ℕ} (T : ShiftData Fr 5 u)
/-- Finite bad residues are checked directly; no closed ZMod disjunction simplification. -/
lemma badPrimes_no_unitClass (b : ℕ) (hb : b∈badPrimes) : (b : ZMod 30)∉unitClasses := by
  have hc : b=2 ∨ b=3 ∨ b=5 := by simpa [badPrimes] using hb
  rcases hc with rfl|rfl|rfl <;> decide +kernel
lemma fifths_arithmetic : ArithmeticInfo (fifthsInst T) 5 2 where
  L_eq := rfl
  Ebd_le := fifths_Ebd_cubic T
  cOf_le := fifths_cOf_le T
lemma fifths_kq_lower {p : ℕ} (hp : p.Prime) (h7 : 7≤p) :
    p+1≤5*(fifthsInst T).cd.kq p := by
  obtain ⟨hq,hb⟩ := fifths_good T hp h7
  obtain ⟨hq5,hu5⟩ := good_primePower_inputs hq hb
  have hs := firstRoot_spec T.hu0 T.hu1 hq5 hu5
  have hmul : p≤classIndex u p*p := by
    simpa using Nat.mul_le_mul_right p hs.2.2.2.1
  have hu0 := T.hu0
  change p+1≤5*firstRoot u p
  omega
/-- The tropical weight is exactly zero beyond7r, not merely bounded by an additive6. -/
lemma fifths_tail {r m p : ℕ} (hp : p.Prime) (h7 : 7≤p) (hr : 400≤r)
    (hm1 : r≤8*m) (hm2 : 8*m≤r+9) (hcut : 7*r<p) :
    WGm (fifthsInst T) r m p=0 := by
  have hk := fifths_kq_lower T hp h7
  have h6 := XGm_D6_good (fifths_levels T) r m p hp h7 (by omega) (by omega)
  have hz : XGm (fifthsInst T) r m p=0 := by omega
  simp [WGm,hz]
/-- Exact finite-table content price; arbitrary-Bd numerology uses the actual LN+8 cutoff. -/
theorem fifths_log_content {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ r : ℕ in atTop,∀ m : ℕ,r≤8*m → 8*m≤r+9 →
      Real.log (Dhyb (fifthsInst T) r m) ≤ ((fifthsPrice : ℝ)+ε)*(r : ℝ)^2 := by
  have hclass := fifths_class_sum T (ε := ε/2) (by positivity)
  have hextra := fifthsExtra_small (ε/2) (by positivity)
  filter_upwards [hclass,hextra,eventually_ge_atTop 400] with r hcl hx hr m h1 h2
  have hD := log_Dhyb_le_arbitrary (fifths_arithmetic T) (M := 30) unitClasses (fun _ => 7*r)
    r m (by omega) (WGm (fifthsInst T) r m) (fun p => Nat.cast_nonneg _) (fun p _ => le_rfl)
    (fun p hp hb => cls_mem_of_bad hp hb) (by
      intro c hc b hb hbc
      exfalso
      exact badPrimes_no_unitClass b hb (by rw [hbc];exact hc)) (by
      intro c hc p hp hb hpc hcut
      have hp7 := prime_class_ge_seven hp (by rw [hpc];exact hc)
      exact fifths_tail T hp hp7 hr h1 h2 hcut)
  rw [fifths_badLog T] at hD
  have hm : m≤r := by omega
  have he := hx m hm
  change extraG 5 Ecub 2 (Real.log 30) r m≤(ε/2)*(r : ℝ)^2 at he
  have hc := hcl m h1 h2
  nlinarith
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.fifths_tail
#print axioms CatalanFrames.Fifths.fifths_log_content
