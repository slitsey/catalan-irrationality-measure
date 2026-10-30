module
public import CatalanFrames.HybCommon.DeficitProfile.K3Key
@[expose] public section
namespace CatalanFrames.HybCommon

theorem k3cov_0 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=17) (hB : P.B4=20) (hq : P.q4=3) (hr : 1000000000 ≤ r) (hl : 2500001 * r < 10000000 * p)
    (hh : 170000000 * p ≤ 44999983 * r) :
    (9 : ℤ) * r + (-34) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  have hL : profileLeft o r p P ≤ (17*p+o)/4 := by
    unfold profileLeft profileCut
    simp only [hA]
    (try norm_num) <;> omega
  have hR : (r+2*(r/8)) ≤ profileRight o r p P := by
    unfold profileRight profileCut
    simp only [hk, hB]
    (try norm_num) <;> omega
  have h0 : 0 ≤ profileShortCell o r p P.poleClass P.q4 := by
    unfold profileShortCell profileShortLo profileShortHi
    simp only [hc, hq]
    (try norm_num) <;> omega
  have h1 : ((4*p+(p+o)/4)-(4*p)) ≤ profileShortCell o r p P.poleClass (P.q4+1) := by
    unfold profileShortCell profileShortLo profileShortHi
    simp only [hc, hq]
    (try norm_num) <;> omega
  have hsz : profileShortSize o p P.poleClass = (p+o)/4 := by
    simp only [profileShortSize, hc]
    norm_num
  have hp := k3_pure (r/8) (profileLeft o r p P) (profileRight o r p P) ((17*p+o)/4) ((r+2*(r/8)))
    (profileShortCell o r p P.poleClass P.q4) (profileShortCell o r p P.poleClass (P.q4+1))
    (0) (((4*p+(p+o)/4)-(4*p))) ((p+o)/4) hL hR h0 h1
  have key : (9 : ℤ) * r + (-34) * p - 8 * 4 ≤ 4 * ((min (r/8) ((((r+2*(r/8)))-((17*p+o)/4)-(r/8)) + ((((r+2*(r/8)))-((17*p+o)/4)-(r/8)) - (((p+o)/4) - ((0) + (((4*p+(p+o)/4)-(4*p))))))) : ℕ) : ℤ) := by
    clear hp hL hR h0 h1 hsz
    refine k3_min_lin _ _ (by norm_num) _ _ _ _ _ ?_ ?_
    · omega
    · omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((r+2*(r/8)))-((17*p+o)/4)-(r/8)) + ((((r+2*(r/8)))-((17*p+o)/4)-(r/8)) - (((p+o)/4) - ((0) + (((4*p+(p+o)/4)-(4*p)))))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

theorem k3cov_5 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=13) (hB : P.B4=16) (hq : P.q4=3) (hr : 1000000000 ≤ r) (hl : 3125001 * r < 10000000 * p)
    (hh : 70000000 * p ≤ 22499993 * r) :
    (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * (profileKind3Deficit o r p P : ℤ) := by
  have hL : profileLeft o r p P ≤ (13*p+o)/4 := by
    unfold profileLeft profileCut
    simp only [hA]
    (try norm_num) <;> omega
  have hR : (r+2*(r/8)) ≤ profileRight o r p P := by
    unfold profileRight profileCut
    simp only [hk, hB]
    (try norm_num) <;> omega
  have h0 : ((3*p+(p+o)/4)-r) ≤ profileShortCell o r p P.poleClass P.q4 := by
    unfold profileShortCell profileShortLo profileShortHi
    simp only [hc, hq]
    (try norm_num) <;> omega
  have h1 : 0 ≤ profileShortCell o r p P.poleClass (P.q4+1) := by
    unfold profileShortCell profileShortLo profileShortHi
    simp only [hc, hq]
    (try norm_num) <;> omega
  have hsz : profileShortSize o p P.poleClass = (p+o)/4 := by
    simp only [profileShortSize, hc]
    norm_num
  have hp := k3_pure (r/8) (profileLeft o r p P) (profileRight o r p P) ((13*p+o)/4) ((r+2*(r/8)))
    (profileShortCell o r p P.poleClass P.q4) (profileShortCell o r p P.poleClass (P.q4+1))
    (((3*p+(p+o)/4)-r)) (0) ((p+o)/4) hL hR h0 h1
  have key : (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * ((min (r/8) ((((r+2*(r/8)))-((13*p+o)/4)-(r/8)) + ((((r+2*(r/8)))-((13*p+o)/4)-(r/8)) - (((p+o)/4) - ((((3*p+(p+o)/4)-r)) + (0))))) : ℕ) : ℤ) := by
    clear hp hL hR h0 h1 hsz
    refine k3_min_lin _ _ (by norm_num) _ _ _ _ _ ?_ ?_
    · omega
    · omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((r+2*(r/8)))-((13*p+o)/4)-(r/8)) + ((((r+2*(r/8)))-((13*p+o)/4)-(r/8)) - (((p+o)/4) - ((((3*p+(p+o)/4)-r)) + (0)))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

theorem k3cov_10 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=9) (hB : P.B4=12) (hq : P.q4=2) (hr : 1000000000 ≤ r) (hl : 45000011 * r < 110000000 * p)
    (hh : 30000000 * p ≤ 12499997 * r) :
    (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * (profileKind3Deficit o r p P : ℤ) := by
  have hL : profileLeft o r p P ≤ r := by
    unfold profileLeft profileCut
    simp only [hA]
    (try norm_num) <;> omega
  have hR : (12*p)/4 ≤ profileRight o r p P := by
    unfold profileRight profileCut
    simp only [hk, hB]
    (try norm_num) <;> omega
  have h0 : 0 ≤ profileShortCell o r p P.poleClass P.q4 := by
    unfold profileShortCell profileShortLo profileShortHi
    simp only [hc, hq]
    (try norm_num) <;> omega
  have h1 : ((r+2*(r/8))-(3*p)) ≤ profileShortCell o r p P.poleClass (P.q4+1) := by
    unfold profileShortCell profileShortLo profileShortHi
    simp only [hc, hq]
    (try norm_num) <;> omega
  have hsz : profileShortSize o p P.poleClass = (p+o)/4 := by
    simp only [profileShortSize, hc]
    norm_num
  have hp := k3_pure (r/8) (profileLeft o r p P) (profileRight o r p P) (r) ((12*p)/4)
    (profileShortCell o r p P.poleClass P.q4) (profileShortCell o r p P.poleClass (P.q4+1))
    (0) (((r+2*(r/8))-(3*p))) ((p+o)/4) hL hR h0 h1
  have key : (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * ((min (r/8) ((((12*p)/4)-(r)-(r/8)) + ((((12*p)/4)-(r)-(r/8)) - (((p+o)/4) - ((0) + (((r+2*(r/8))-(3*p))))))) : ℕ) : ℤ) := by
    clear hp hL hR h0 h1 hsz
    refine k3_min_lin _ _ (by norm_num) _ _ _ _ _ ?_ ?_
    · omega
    · omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((12*p)/4)-(r)-(r/8)) + ((((12*p)/4)-(r)-(r/8)) - (((p+o)/4) - ((0) + (((r+2*(r/8))-(3*p)))))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

theorem k3cov_15 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=16) (hB : P.B4=19) (hq : P.q4=3) (hr : 1000000000 ≤ r) (hl : 45000017 * r < 170000000 * p)
    (hh : 30000000 * p ≤ 7999997 * r) :
    (5 : ℤ) * r + (-17) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  have hL : profileLeft o r p P ≤ (16*p)/4 := by
    unfold profileLeft profileCut
    simp only [hA]
    (try norm_num) <;> omega
  have hR : (r+2*(r/8)) ≤ profileRight o r p P := by
    unfold profileRight profileCut
    simp only [hk, hB]
    (try norm_num) <;> omega
  have h0 : ((4*p)-r) ≤ profileShortCell o r p P.poleClass P.q4 := by
    unfold profileShortCell profileShortLo profileShortHi
    simp only [hc, hq]
    (try norm_num) <;> omega
  have h1 : 0 ≤ profileShortCell o r p P.poleClass (P.q4+1) := by
    unfold profileShortCell profileShortLo profileShortHi
    simp only [hc, hq]
    (try norm_num) <;> omega
  have hsz : profileShortSize o p P.poleClass = (p-o)/4 := by
    simp only [profileShortSize, hc]
    norm_num
  have hp := k3_pure (r/8) (profileLeft o r p P) (profileRight o r p P) ((16*p)/4) ((r+2*(r/8)))
    (profileShortCell o r p P.poleClass P.q4) (profileShortCell o r p P.poleClass (P.q4+1))
    (((4*p)-r)) (0) ((p-o)/4) hL hR h0 h1
  have key : (5 : ℤ) * r + (-17) * p - 8 * 4 ≤ 4 * ((min (r/8) ((((r+2*(r/8)))-((16*p)/4)-(r/8)) + ((((r+2*(r/8)))-((16*p)/4)-(r/8)) - (((p-o)/4) - ((((4*p)-r)) + (0))))) : ℕ) : ℤ) := by
    clear hp hL hR h0 h1 hsz
    refine k3_min_lin _ _ (by norm_num) _ _ _ _ _ ?_ ?_
    · omega
    · omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((r+2*(r/8)))-((16*p)/4)-(r/8)) + ((((r+2*(r/8)))-((16*p)/4)-(r/8)) - (((p-o)/4) - ((((4*p)-r)) + (0)))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

theorem k3cov_20 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=12) (hB : P.B4=15) (hq : P.q4=2) (hr : 1000000000 ≤ r) (hl : 10000003 * r < 30000000 * p)
    (hh : 130000000 * p ≤ 44999987 * r) :
    (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * (profileKind3Deficit o r p P : ℤ) := by
  have hL : profileLeft o r p P ≤ (12*p)/4 := by
    unfold profileLeft profileCut
    simp only [hA]
    (try norm_num) <;> omega
  have hR : (r+2*(r/8)) ≤ profileRight o r p P := by
    unfold profileRight profileCut
    simp only [hk, hB]
    (try norm_num) <;> omega
  have h0 : ((3*p)-r) ≤ profileShortCell o r p P.poleClass P.q4 := by
    unfold profileShortCell profileShortLo profileShortHi
    simp only [hc, hq]
    (try norm_num) <;> omega
  have h1 : 0 ≤ profileShortCell o r p P.poleClass (P.q4+1) := by
    unfold profileShortCell profileShortLo profileShortHi
    simp only [hc, hq]
    (try norm_num) <;> omega
  have hsz : profileShortSize o p P.poleClass = (p-o)/4 := by
    simp only [profileShortSize, hc]
    norm_num
  have hp := k3_pure (r/8) (profileLeft o r p P) (profileRight o r p P) ((12*p)/4) ((r+2*(r/8)))
    (profileShortCell o r p P.poleClass P.q4) (profileShortCell o r p P.poleClass (P.q4+1))
    (((3*p)-r)) (0) ((p-o)/4) hL hR h0 h1
  have key : (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * ((min (r/8) ((((r+2*(r/8)))-((12*p)/4)-(r/8)) + ((((r+2*(r/8)))-((12*p)/4)-(r/8)) - (((p-o)/4) - ((((3*p)-r)) + (0))))) : ℕ) : ℤ) := by
    clear hp hL hR h0 h1 hsz
    refine k3_min_lin _ _ (by norm_num) _ _ _ _ _ ?_ ?_
    · omega
    · omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((r+2*(r/8)))-((12*p)/4)-(r/8)) + ((((r+2*(r/8)))-((12*p)/4)-(r/8)) - (((p-o)/4) - ((((3*p)-r)) + (0)))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

theorem k3cov_25 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=8) (hB : P.B4=11) (hq : P.q4=2) (hr : 1000000000 ≤ r) (hl : 4500001 * r < 10000000 * p)
    (hh : 110000000 * p ≤ 49999989 * r) :
    (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * (profileKind3Deficit o r p P : ℤ) := by
  have hL : profileLeft o r p P ≤ r := by
    unfold profileLeft profileCut
    simp only [hA]
    (try norm_num) <;> omega
  have hR : (11*p+o)/4 ≤ profileRight o r p P := by
    unfold profileRight profileCut
    simp only [hk, hB]
    (try norm_num) <;> omega
  have h0 : ((r+2*(r/8))-(2*p+(3*p+o)/4)) ≤ profileShortCell o r p P.poleClass P.q4 := by
    unfold profileShortCell profileShortLo profileShortHi
    simp only [hc, hq]
    (try norm_num) <;> omega
  have h1 : 0 ≤ profileShortCell o r p P.poleClass (P.q4+1) := by
    unfold profileShortCell profileShortLo profileShortHi
    simp only [hc, hq]
    (try norm_num) <;> omega
  have hsz : profileShortSize o p P.poleClass = (p-o)/4 := by
    simp only [profileShortSize, hc]
    norm_num
  have hp := k3_pure (r/8) (profileLeft o r p P) (profileRight o r p P) (r) ((11*p+o)/4)
    (profileShortCell o r p P.poleClass P.q4) (profileShortCell o r p P.poleClass (P.q4+1))
    (((r+2*(r/8))-(2*p+(3*p+o)/4))) (0) ((p-o)/4) hL hR h0 h1
  have key : (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * ((min (r/8) ((((11*p+o)/4)-(r)-(r/8)) + ((((11*p+o)/4)-(r)-(r/8)) - (((p-o)/4) - ((((r+2*(r/8))-(2*p+(3*p+o)/4))) + (0))))) : ℕ) : ℤ) := by
    clear hp hL hR h0 h1 hsz
    refine k3_min_lin _ _ (by norm_num) _ _ _ _ _ ?_ ?_
    · omega
    · omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((11*p+o)/4)-(r)-(r/8)) + ((((11*p+o)/4)-(r)-(r/8)) - (((p-o)/4) - ((((r+2*(r/8))-(2*p+(3*p+o)/4))) + (0)))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

end CatalanFrames.HybCommon
