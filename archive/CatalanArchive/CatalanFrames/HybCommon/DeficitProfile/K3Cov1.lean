module
public import CatalanFrames.HybCommon.DeficitProfile.K3Pure
@[expose] public section
namespace CatalanFrames.HybCommon

theorem k3cov_1 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=13) (hB : P.B4=16) (hq : P.q4=3) (hr : 1000000000 ≤ r) (hl : 2812501 * r < 10000000 * p)
    (hh : 170000000 * p ≤ 49999983 * r) :
    (-9 : ℤ) * r + (32) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  have hL : profileLeft o r p P ≤ r := by
    unfold profileLeft profileCut
    simp only [hA]
    (try norm_num) <;> omega
  have hR : (16*p)/4 ≤ profileRight o r p P := by
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
  have hp := k3_pure (r/8) (profileLeft o r p P) (profileRight o r p P) (r) ((16*p)/4)
    (profileShortCell o r p P.poleClass P.q4) (profileShortCell o r p P.poleClass (P.q4+1))
    (0) (((4*p+(p+o)/4)-(4*p))) ((p+o)/4) hL hR h0 h1
  have key : (-9 : ℤ) * r + (32) * p - 8 * 4 ≤ 4 * ((min (r/8) ((((16*p)/4)-(r)-(r/8)) + ((((16*p)/4)-(r)-(r/8)) - (((p+o)/4) - ((0) + (((4*p+(p+o)/4)-(4*p))))))) : ℕ) : ℤ) := by
    omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((16*p)/4)-(r)-(r/8)) + ((((16*p)/4)-(r)-(r/8)) - (((p+o)/4) - ((0) + (((4*p+(p+o)/4)-(4*p)))))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

theorem k3cov_6 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=13) (hB : P.B4=16) (hq : P.q4=3) (hr : 1000000000 ≤ r) (hl : 22500007 * r < 70000000 * p)
    (hh : 30000000 * p ≤ 9999997 * r) :
    (5 : ℤ) * r + (-14) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
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
  have key : (5 : ℤ) * r + (-14) * p - 8 * 4 ≤ 4 * ((min (r/8) ((((r+2*(r/8)))-((13*p+o)/4)-(r/8)) + ((((r+2*(r/8)))-((13*p+o)/4)-(r/8)) - (((p+o)/4) - ((((3*p+(p+o)/4)-r)) + (0))))) : ℕ) : ℤ) := by
    omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((r+2*(r/8)))-((13*p+o)/4)-(r/8)) + ((((r+2*(r/8)))-((13*p+o)/4)-(r/8)) - (((p+o)/4) - ((((3*p+(p+o)/4)-r)) + (0)))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

theorem k3cov_11 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=9) (hB : P.B4=12) (hq : P.q4=2) (hr : 1000000000 ≤ r) (hl : 40000009 * r < 90000000 * p)
    (hh : 10000000 * p ≤ 4499999 * r) :
    (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * (profileKind3Deficit o r p P : ℤ) := by
  have hL : profileLeft o r p P ≤ (9*p+o)/4 := by
    unfold profileLeft profileCut
    simp only [hA]
    (try norm_num) <;> omega
  have hR : (r+2*(r/8)) ≤ profileRight o r p P := by
    unfold profileRight profileCut
    simp only [hk, hB]
    (try norm_num) <;> omega
  have h0 : ((2*p+(p+o)/4)-r) ≤ profileShortCell o r p P.poleClass P.q4 := by
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
  have hp := k3_pure (r/8) (profileLeft o r p P) (profileRight o r p P) ((9*p+o)/4) ((r+2*(r/8)))
    (profileShortCell o r p P.poleClass P.q4) (profileShortCell o r p P.poleClass (P.q4+1))
    (((2*p+(p+o)/4)-r)) (0) ((p+o)/4) hL hR h0 h1
  have key : (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * ((min (r/8) ((((r+2*(r/8)))-((9*p+o)/4)-(r/8)) + ((((r+2*(r/8)))-((9*p+o)/4)-(r/8)) - (((p+o)/4) - ((((2*p+(p+o)/4)-r)) + (0))))) : ℕ) : ℤ) := by
    omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((r+2*(r/8)))-((9*p+o)/4)-(r/8)) + ((((r+2*(r/8)))-((9*p+o)/4)-(r/8)) - (((p+o)/4) - ((((2*p+(p+o)/4)-r)) + (0)))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

theorem k3cov_16 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=16) (hB : P.B4=19) (hq : P.q4=3) (hr : 1000000000 ≤ r) (hl : 8000003 * r < 30000000 * p)
    (hh : 10000000 * p ≤ 2812499 * r) :
    (9 : ℤ) * r + (-32) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  have hL : profileLeft o r p P ≤ (16*p)/4 := by
    unfold profileLeft profileCut
    simp only [hA]
    (try norm_num) <;> omega
  have hR : (r+2*(r/8)) ≤ profileRight o r p P := by
    unfold profileRight profileCut
    simp only [hk, hB]
    (try norm_num) <;> omega
  have h0 : ((4*p)-(3*p+(3*p+o)/4)) ≤ profileShortCell o r p P.poleClass P.q4 := by
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
    (((4*p)-(3*p+(3*p+o)/4))) (0) ((p-o)/4) hL hR h0 h1
  have key : (9 : ℤ) * r + (-32) * p - 8 * 4 ≤ 4 * ((min (r/8) ((((r+2*(r/8)))-((16*p)/4)-(r/8)) + ((((r+2*(r/8)))-((16*p)/4)-(r/8)) - (((p-o)/4) - ((((4*p)-(3*p+(3*p+o)/4))) + (0))))) : ℕ) : ℤ) := by
    omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((r+2*(r/8)))-((16*p)/4)-(r/8)) + ((((r+2*(r/8)))-((16*p)/4)-(r/8)) - (((p-o)/4) - ((((4*p)-(3*p+(3*p+o)/4))) + (0)))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

theorem k3cov_21 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=12) (hB : P.B4=15) (hq : P.q4=2) (hr : 1000000000 ≤ r) (hl : 45000013 * r < 130000000 * p)
    (hh : 110000000 * p ≤ 39999989 * r) :
    (5 : ℤ) * r + (-13) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
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
  have key : (5 : ℤ) * r + (-13) * p - 8 * 4 ≤ 4 * ((min (r/8) ((((r+2*(r/8)))-((12*p)/4)-(r/8)) + ((((r+2*(r/8)))-((12*p)/4)-(r/8)) - (((p-o)/4) - ((((3*p)-r)) + (0))))) : ℕ) : ℤ) := by
    omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((r+2*(r/8)))-((12*p)/4)-(r/8)) + ((((r+2*(r/8)))-((12*p)/4)-(r/8)) - (((p-o)/4) - ((((3*p)-r)) + (0)))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

end CatalanFrames.HybCommon
