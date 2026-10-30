module
public import CatalanCore.Measure.Irrational
public import CatalanCore.Measure.Pinned
public import CatalanCore.NT.PowerDvd
public import CatalanFrames.Thirds.Window
@[expose] public section
open CatalanCore
namespace CatalanFrames.HybGen
/-- A pinned class containing1 supplies the ordinary NV interface needed for irrationality. -/
theorem nv_of_pin_one (Fam : PolyFamily) (M : ℕ) (S : Finset (ZMod M))
    (h1 : (1 : ZMod M) ∈ S)
    (hNV : HasNVPinC Fam (Thirds.ClsIn M S) (Thirds.PowBad 2) 1 2) :
    HasNV Fam (PrimeRule.ofPowDvd M 1 isUnit_one 2) 1 1 := by
  obtain ⟨C,N1,H⟩ := hNV
  refine ⟨max C 0,⌈max N1 0⌉₊,fun l hl hl0 hlc p q hq hcop hbad => ?_⟩
  have hN : N1 ≤ (l : ℝ) :=
    le_trans (le_max_left N1 0) (le_trans (Nat.le_ceil _) (by exact_mod_cast hl0))
  have hcls : Thirds.ClsIn M S l := by
    change (l : ZMod M) ∈ S
    have hc : (l : ZMod M) = 1 := hlc
    rw [hc]
    exact h1
  obtain ⟨n,ha,hn1,hn2,hne⟩ := H l hl hcls l hN (by simp)
    (by have : (0 : ℝ) ≤ l := Nat.cast_nonneg l; linarith)
    p q hq hcop (by simpa [PrimeRule.ofPowDvd,Thirds.PowBad] using hbad)
  refine ⟨n,ha,?_,?_,hne⟩
  · have := le_max_right C 0; simpa only [one_mul] using (by linarith : (l : ℝ)-max C 0 ≤ Fam.deg n)
  · have := le_max_left C 0; simpa only [one_mul] using (by linarith : (Fam.deg n : ℝ) ≤ (l : ℝ)+max C 0)
/-- Irrationality is a separate deduction, not a consequence of MeasureLBAt alone. -/
theorem irrational_of_pin_one (Fam : PolyFamily) (M : ℕ) (hM : M ≠ 0)
    (S : Finset (ZMod M)) (h1 : (1 : ZMod M) ∈ S) {Λ D c : ℝ}
    (hC : HasContent Fam Λ) (hD : HasDecay Fam D c) (hgap : Λ < D)
    (hNV : HasNVPinC Fam (Thirds.ClsIn M S) (Thirds.PowBad 2) 1 2) :
    Irrational Fam.const := by
  apply Measure.irrational_of_family Fam hC hD hgap
    (PrimeRule.ofPowDvd M 1 isUnit_one 2) (by simpa [PrimeRule.ofPowDvd] using hM)
    (by norm_num : (0 : ℝ) < 1) ?_ (nv_of_pin_one Fam M S h1 hNV)
  intro q hq
  refine ⟨q,fun l hl hd => ?_⟩
  change l^2 ∣ q at hd
  have hle : l^2 ≤ q := Nat.le_of_dvd hq hd
  have hlpos : 0 < l := lt_of_le_of_lt (Nat.zero_le q) hl
  have hlpow : l ≤ l^2 := by nlinarith
  omega
end CatalanFrames.HybGen
#print axioms CatalanFrames.HybGen.nv_of_pin_one
#print axioms CatalanFrames.HybGen.irrational_of_pin_one
