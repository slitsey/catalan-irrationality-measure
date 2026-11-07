module
public import CatalanFrames.HybGen.ExtraScaled
@[expose] public section
open CatalanCore.Arith.Hybrid Filter
namespace CatalanFrames.Fifths
noncomputable def fifthsExtra (r m : ℕ) : ℝ :=
  extraG 5 (fun N => 5*N^3) 2 (Real.log 30) r m
private theorem double_extra_eq (r m : ℕ) :
    extraBound (2*r) (2*m) =
      2*extraG 8 (fun N => 5*(2*N)^3) 4 (Real.log 2) r m := by
  have hN : 2*r+2*(2*m) = 2*(r+2*m) := by omega
  have hQ : 4*(2*(r+2*m)) = 8*(r+2*m) := by omega
  have harg : (4 : ℝ)*(((2*r : ℕ) : ℝ)+2*((2*m : ℕ) : ℝ))+5 =
      (8 : ℝ)*((r : ℝ)+2*(m : ℝ))+5 := by
    push_cast
    ring
  unfold extraBound extraG
  rw [hN,hQ]
  push_cast at harg ⊢
  rw [harg]
  ring
/-- Concrete domination for L5 and bad primes2,3,5, proved for every r,m. -/
theorem fifthsExtra_dom (r m : ℕ) :
    fifthsExtra r m ≤ 5*extraBound (2*r) (2*m) := by
  have hlog : Real.log 30 ≤ 5*Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 30) (by norm_num : (30 : ℝ) ≤ 32)
    have he : Real.log 32 = 5*Real.log 2 := by
      rw [show (32 : ℝ) = 2^5 by norm_num,Real.log_pow]
      norm_num
    rwa [he] at h
  have hE : ∀ N : ℕ, 5*N^3 ≤ 5*(2*N)^3 := by
    intro N
    exact Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left (show N ≤ 2*N by omega) 3)
  have hm := extraG_mono (by norm_num : 5 ≤ 8) hE (by norm_num : 2 ≤ 4)
    hlog (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 30)) r m
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogQ : 0 ≤ Real.log ((8 : ℝ)*(r+2*m)+5) :=
    Real.log_nonneg (by
      have hn : (0 : ℝ) ≤ (8 : ℝ)*(r+2*m) := by positivity
      linarith)
  have hB : 0 ≤ ((Nat.sqrt (8*(r+2*m)) : ℝ)+1)*
      (2*(r+m : ℝ)*(Nat.log 2 (8*(r+2*m)) : ℝ)*Real.log ((8 : ℝ)*(r+2*m)+5)) := by positivity
  have hscale : extraG 8 (fun N => 5*(2*N)^3) 4 (5*Real.log 2) r m ≤
      5*extraG 8 (fun N => 5*(2*N)^3) 4 (Real.log 2) r m := by
    unfold extraG
    push_cast
    nlinarith only [hB]
  have hnonneg : 0 ≤ extraG 8 (fun N => 5*(2*N)^3) 4 (Real.log 2) r m := by
    unfold extraG
    push_cast
    positivity
  change extraG 5 (fun N => 5*N^3) 2 (Real.log 30) r m ≤ _
  refine hm.trans (hscale.trans ?_)
  rw [double_extra_eq]
  nlinarith only [hnonneg]
/-- The fifths extra term is uniformly o(r^2); this spends no finite-table price. -/
theorem fifthsExtra_small (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ m ≤ r, fifthsExtra r m ≤ ε*(r : ℝ)^2 :=
  CatalanFrames.HybGen.extra_small_of_double_domination fifthsExtra (fun r m _ => fifthsExtra_dom r m) ε hε
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.fifthsExtra_dom
#print axioms CatalanFrames.Fifths.fifthsExtra_small
