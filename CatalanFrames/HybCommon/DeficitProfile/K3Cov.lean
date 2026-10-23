module
public import CatalanFrames.HybCommon.DeficitProfile.Family
@[expose] public section
namespace CatalanFrames.HybCommon

theorem k3cov_0 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=17) (hB : P.B4=20) (hq : P.q4=3) (hl : 2500001 * r < 10000000 * p)
    (hh : 170000000 * p ≤ 44999983 * r) :
    (9 : ℤ) * r + (-34) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_1 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=13) (hB : P.B4=16) (hq : P.q4=3) (hl : 2812501 * r < 10000000 * p)
    (hh : 170000000 * p ≤ 49999983 * r) :
    (-9 : ℤ) * r + (32) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_2 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=13) (hB : P.B4=16) (hq : P.q4=3) (hl : 50000017 * r < 170000000 * p)
    (hh : 10000000 * p ≤ 2999999 * r) :
    (-4 : ℤ) * r + (15) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_3 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=13) (hB : P.B4=16) (hq : P.q4=3) (hl : 3000001 * r < 10000000 * p)
    (hh : 70000000 * p ≤ 22499993 * r) :
    (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_4 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=13) (hB : P.B4=16) (hq : P.q4=3) (hl : 22500007 * r < 70000000 * p)
    (hh : 30000000 * p ≤ 9999997 * r) :
    (5 : ℤ) * r + (-14) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_5 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=13) (hB : P.B4=16) (hq : P.q4=2) (hl : 10000003 * r < 30000000 * p)
    (hh : 130000000 * p ≤ 44999987 * r) :
    (9 : ℤ) * r + (-26) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_6 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=9) (hB : P.B4=12) (hq : P.q4=2) (hl : 3750001 * r < 10000000 * p)
    (hh : 130000000 * p ≤ 49999987 * r) :
    (-9 : ℤ) * r + (24) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_7 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=9) (hB : P.B4=12) (hq : P.q4=2) (hl : 50000013 * r < 130000000 * p)
    (hh : 110000000 * p ≤ 44999989 * r) :
    (-4 : ℤ) * r + (11) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_8 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=9) (hB : P.B4=12) (hq : P.q4=2) (hl : 45000011 * r < 110000000 * p)
    (hh : 30000000 * p ≤ 12499997 * r) :
    (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_9 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=9) (hB : P.B4=12) (hq : P.q4=2) (hl : 40000009 * r < 90000000 * p)
    (hh : 10000000 * p ≤ 4499999 * r) :
    (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_10 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=1)
    (hA : P.A4=9) (hB : P.B4=12) (hq : P.q4=2) (hl : 4500001 * r < 10000000 * p)
    (hh : 10000000 * p ≤ 4999999 * r) :
    (5 : ℤ) * r + (-10) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_11 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=16) (hB : P.B4=19) (hq : P.q4=3) (hl : 2500001 * r < 10000000 * p)
    (hh : 170000000 * p ≤ 44999983 * r) :
    (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_12 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=16) (hB : P.B4=19) (hq : P.q4=3) (hl : 45000017 * r < 170000000 * p)
    (hh : 30000000 * p ≤ 7999997 * r) :
    (5 : ℤ) * r + (-17) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_13 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=16) (hB : P.B4=19) (hq : P.q4=3) (hl : 8000003 * r < 30000000 * p)
    (hh : 10000000 * p ≤ 2812499 * r) :
    (9 : ℤ) * r + (-32) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_14 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=12) (hB : P.B4=15) (hq : P.q4=3) (hl : 3000001 * r < 10000000 * p)
    (hh : 10000000 * p ≤ 3124999 * r) :
    (-9 : ℤ) * r + (30) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_15 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=12) (hB : P.B4=15) (hq : P.q4=3) (hl : 3125001 * r < 10000000 * p)
    (hh : 70000000 * p ≤ 22499993 * r) :
    (-2 : ℤ) * r + (7) * p - 8 * 2 ≤ 2 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_16 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=12) (hB : P.B4=15) (hq : P.q4=3) (hl : 22500007 * r < 70000000 * p)
    (hh : 30000000 * p ≤ 9999997 * r) :
    (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_17 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=12) (hB : P.B4=15) (hq : P.q4=2) (hl : 10000003 * r < 30000000 * p)
    (hh : 130000000 * p ≤ 44999987 * r) :
    (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_18 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=12) (hB : P.B4=15) (hq : P.q4=2) (hl : 45000013 * r < 130000000 * p)
    (hh : 110000000 * p ≤ 39999989 * r) :
    (5 : ℤ) * r + (-13) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_19 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=12) (hB : P.B4=15) (hq : P.q4=2) (hl : 40000011 * r < 110000000 * p)
    (hh : 10000000 * p ≤ 3749999 * r) :
    (9 : ℤ) * r + (-24) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_20 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=8) (hB : P.B4=11) (hq : P.q4=2) (hl : 45000011 * r < 110000000 * p)
    (hh : 30000000 * p ≤ 12499997 * r) :
    (-9 : ℤ) * r + (22) * p - 8 * 4 ≤ 4 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_21 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=8) (hB : P.B4=11) (hq : P.q4=2) (hl : 12500003 * r < 30000000 * p)
    (hh : 10000000 * p ≤ 4499999 * r) :
    (-2 : ℤ) * r + (5) * p - 8 * 2 ≤ 2 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

theorem k3cov_22 {o r p : ℕ} (P : DeficitRow) (ho : o=1 ∨ o=3) (hk : P.kind=3) (hc : P.poleClass=3)
    (hA : P.A4=8) (hB : P.B4=11) (hq : P.q4=2) (hl : 4500001 * r < 10000000 * p)
    (hh : 110000000 * p ≤ 49999989 * r) :
    (1 : ℤ) * r + (0) * p - 8 * 8 ≤ 8 * (profileKind3Deficit o r p P : ℤ) := by
  unfold profileKind3Deficit profileRight profileLeft profileCut profileShortSize profileShortCell profileShortLo profileShortHi
  simp only [hk, hc, hA, hB, hq, Nat.reduceEqDiff, ite_true, ite_false]
  norm_num
  omega

end CatalanFrames.HybCommon
