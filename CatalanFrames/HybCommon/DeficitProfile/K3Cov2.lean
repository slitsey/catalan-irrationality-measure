module
public import CatalanFrames.HybCommon.DeficitProfile.K3Pure
@[expose] public section
namespace CatalanFrames.HybCommon

theorem k3cov_2 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=13) (hB : P.B4=16) (hq : P.q4=3) (hr : 1000000000 ≤ r) (hl : 50000017 * r < 170000000 * p)
    (hh : 10000000 * p ≤ 2999999 * r) :
    (-4 : ℤ) * r + (15) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
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
  have h1 : ((r+2*(r/8))-(4*p)) ≤ profileShortCell o r p P.poleClass (P.q4+1) := by
    unfold profileShortCell profileShortLo profileShortHi
    simp only [hc, hq]
    (try norm_num) <;> omega
  have hsz : profileShortSize o p P.poleClass = (p+o)/4 := by
    simp only [profileShortSize, hc]
    norm_num
  have hp := k3_pure (r/8) (profileLeft o r p P) (profileRight o r p P) (r) ((16*p)/4)
    (profileShortCell o r p P.poleClass P.q4) (profileShortCell o r p P.poleClass (P.q4+1))
    (0) (((r+2*(r/8))-(4*p))) ((p+o)/4) hL hR h0 h1
  have key : (-4 : ℤ) * r + (15) * p - 8 * 4 ≤ 4 * ((min (r/8) ((((16*p)/4)-(r)-(r/8)) + ((((16*p)/4)-(r)-(r/8)) - (((p+o)/4) - ((0) + (((r+2*(r/8))-(4*p))))))) : ℕ) : ℤ) := by
    omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((16*p)/4)-(r)-(r/8)) + ((((16*p)/4)-(r)-(r/8)) - (((p+o)/4) - ((0) + (((r+2*(r/8))-(4*p)))))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

theorem k3cov_7 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=13) (hB : P.B4=16) (hq : P.q4=2) (hr : 1000000000 ≤ r) (hl : 10000003 * r < 30000000 * p)
    (hh : 130000000 * p ≤ 44999987 * r) :
    (9 : ℤ) * r + (-26) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  have hL : profileLeft o r p P ≤ (13*p+o)/4 := by
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
  have h1 : ((3*p+(p+o)/4)-(3*p)) ≤ profileShortCell o r p P.poleClass (P.q4+1) := by
    unfold profileShortCell profileShortLo profileShortHi
    simp only [hc, hq]
    (try norm_num) <;> omega
  have hsz : profileShortSize o p P.poleClass = (p+o)/4 := by
    simp only [profileShortSize, hc]
    norm_num
  have hp := k3_pure (r/8) (profileLeft o r p P) (profileRight o r p P) ((13*p+o)/4) ((r+2*(r/8)))
    (profileShortCell o r p P.poleClass P.q4) (profileShortCell o r p P.poleClass (P.q4+1))
    (0) (((3*p+(p+o)/4)-(3*p))) ((p+o)/4) hL hR h0 h1
  have key : (9 : ℤ) * r + (-26) * p - 8 * 4 ≤ 4 * ((min (r/8) ((((r+2*(r/8)))-((13*p+o)/4)-(r/8)) + ((((r+2*(r/8)))-((13*p+o)/4)-(r/8)) - (((p+o)/4) - ((0) + (((3*p+(p+o)/4)-(3*p))))))) : ℕ) : ℤ) := by
    omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((r+2*(r/8)))-((13*p+o)/4)-(r/8)) + ((((r+2*(r/8)))-((13*p+o)/4)-(r/8)) - (((p+o)/4) - ((0) + (((3*p+(p+o)/4)-(3*p)))))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

theorem k3cov_12 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=9) (hB : P.B4=12) (hq : P.q4=2) (hr : 1000000000 ≤ r) (hl : 4500001 * r < 10000000 * p)
    (hh : 10000000 * p ≤ 4999999 * r) :
    (5 : ℤ) * r + (-10) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
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
  have key : (5 : ℤ) * r + (-10) * p - 8 * 4 ≤ 4 * ((min (r/8) ((((r+2*(r/8)))-((9*p+o)/4)-(r/8)) + ((((r+2*(r/8)))-((9*p+o)/4)-(r/8)) - (((p+o)/4) - ((((2*p+(p+o)/4)-r)) + (0))))) : ℕ) : ℤ) := by
    omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((r+2*(r/8)))-((9*p+o)/4)-(r/8)) + ((((r+2*(r/8)))-((9*p+o)/4)-(r/8)) - (((p+o)/4) - ((((2*p+(p+o)/4)-r)) + (0)))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

theorem k3cov_17 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=12) (hB : P.B4=15) (hq : P.q4=3) (hr : 1000000000 ≤ r) (hl : 3000001 * r < 10000000 * p)
    (hh : 10000000 * p ≤ 3124999 * r) :
    (-9 : ℤ) * r + (30) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  have hL : profileLeft o r p P ≤ r := by
    unfold profileLeft profileCut
    simp only [hA]
    (try norm_num) <;> omega
  have hR : (15*p+o)/4 ≤ profileRight o r p P := by
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
  have hp := k3_pure (r/8) (profileLeft o r p P) (profileRight o r p P) (r) ((15*p+o)/4)
    (profileShortCell o r p P.poleClass P.q4) (profileShortCell o r p P.poleClass (P.q4+1))
    (((4*p)-(3*p+(3*p+o)/4))) (0) ((p-o)/4) hL hR h0 h1
  have key : (-9 : ℤ) * r + (30) * p - 8 * 4 ≤ 4 * ((min (r/8) ((((15*p+o)/4)-(r)-(r/8)) + ((((15*p+o)/4)-(r)-(r/8)) - (((p-o)/4) - ((((4*p)-(3*p+(3*p+o)/4))) + (0))))) : ℕ) : ℤ) := by
    omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((15*p+o)/4)-(r)-(r/8)) + ((((15*p+o)/4)-(r)-(r/8)) - (((p-o)/4) - ((((4*p)-(3*p+(3*p+o)/4))) + (0)))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

theorem k3cov_22 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=12) (hB : P.B4=15) (hq : P.q4=2) (hr : 1000000000 ≤ r) (hl : 40000011 * r < 110000000 * p)
    (hh : 10000000 * p ≤ 3749999 * r) :
    (9 : ℤ) * r + (-24) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  have hL : profileLeft o r p P ≤ (12*p)/4 := by
    unfold profileLeft profileCut
    simp only [hA]
    (try norm_num) <;> omega
  have hR : (r+2*(r/8)) ≤ profileRight o r p P := by
    unfold profileRight profileCut
    simp only [hk, hB]
    (try norm_num) <;> omega
  have h0 : ((3*p)-(2*p+(3*p+o)/4)) ≤ profileShortCell o r p P.poleClass P.q4 := by
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
    (((3*p)-(2*p+(3*p+o)/4))) (0) ((p-o)/4) hL hR h0 h1
  have key : (9 : ℤ) * r + (-24) * p - 8 * 4 ≤ 4 * ((min (r/8) ((((r+2*(r/8)))-((12*p)/4)-(r/8)) + ((((r+2*(r/8)))-((12*p)/4)-(r/8)) - (((p-o)/4) - ((((3*p)-(2*p+(3*p+o)/4))) + (0))))) : ℕ) : ℤ) := by
    omega
  unfold profileKind3Deficit
  rw [hsz]
  have hp' : (((min (r/8) ((((r+2*(r/8)))-((12*p)/4)-(r/8)) + ((((r+2*(r/8)))-((12*p)/4)-(r/8)) - (((p-o)/4) - ((((3*p)-(2*p+(3*p+o)/4))) + (0)))))) : ℕ) : ℤ) ≤ _ := Nat.cast_le.2 hp
  linarith

end CatalanFrames.HybCommon
