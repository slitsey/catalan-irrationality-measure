module

public import CatalanCore.Uniform.Content.UFFamily3.Sing3

@[expose] public section

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.UFFamily CatalanCore.Uniform.Content.UFFamily.SevE
  CatalanCore.Uniform.Content.UFFamily2

namespace CatalanCore.Uniform.Content.UFFamily3
def lu1_0 : LuData where
  LM := []
  UM := []
  LA := [[1]]
  UA := [[0]]
  LB := [[1]]
  UB := [[1]]
  a := 0
  b := 1

theorem intOK_1_0_0_2 : IntOK 3 2 1 (1 : ℚ) 2 (famType 3 0 0 1 0) 1 := by decide +kernel
theorem ok_1_0_0_2 : lu1_0.ok (famType 3 0 0 1 0).nodes.length (mkFib 3 2 1 (1 : ℚ) 2 (famType 3 0 0 1 0) 1) 1 = true := by
  decide +kernel
def lu1_1 : LuData where
  LM := []
  UM := []
  LA := [[1]]
  UA := [[-3]]
  LB := [[1]]
  UB := [[1]]
  a := -3
  b := 1

theorem intOK_1_0_1_2 : IntOK 3 2 1 (1 : ℚ) 2 (famType 3 0 1 1 0) 1 := by decide +kernel
theorem ok_1_0_1_2 : lu1_1.ok (famType 3 0 1 1 0).nodes.length (mkFib 3 2 1 (1 : ℚ) 2 (famType 3 0 1 1 0) 1) 1 = true := by
  decide +kernel
theorem pair_1_0_0_0_1 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 0 0 1 0) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 0 1 1 0) DK ∧
      XJ.ok (famType 3 0 0 1 0).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 0 0 1 0) DJ) DJ = true ∧
      XK.ok (famType 3 0 1 1 0).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 0 1 1 0) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨2, 1, 1, lu1_0, lu1_1, intOK_1_0_0_2, intOK_1_0_1_2,
    ok_1_0_0_2, ok_1_0_1_2,
    not_dvd_smooth (Fact.out) hp _ 1 (by decide +kernel)⟩

theorem pair_1_0_1_0_0 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 0 1 1 0) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 0 0 1 0) DK ∧
      XJ.ok (famType 3 0 1 1 0).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 0 1 1 0) DJ) DJ = true ∧
      XK.ok (famType 3 0 0 1 0).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 0 0 1 0) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨2, 1, 1, lu1_1, lu1_0, intOK_1_0_1_2, intOK_1_0_0_2,
    ok_1_0_1_2, ok_1_0_0_2,
    not_dvd_smooth (Fact.out) hp _ 1 (by decide +kernel)⟩

theorem intOK_1_0_2_2 : IntOK 3 2 1 (1 : ℚ) 2 (famType 3 0 2 1 0) 1 := by decide +kernel
theorem ok_1_0_2_2 : lu1_1.ok (famType 3 0 2 1 0).nodes.length (mkFib 3 2 1 (1 : ℚ) 2 (famType 3 0 2 1 0) 1) 1 = true := by
  decide +kernel
def lu1_2 : LuData where
  LM := [[1]]
  UM := [[2]]
  LA := [[1, 0], [1, 1]]
  UA := [[2, 0], [0, -2]]
  LB := [[1, 0], [1, 1]]
  UB := [[2, 1], [0, 2]]
  a := -4
  b := 4

theorem intOK_1_1_3_2 : IntOK 3 2 1 (1 : ℚ) 2 (famType 3 1 3 1 1) 1 := by decide +kernel
theorem ok_1_1_3_2 : lu1_2.ok (famType 3 1 3 1 1).nodes.length (mkFib 3 2 1 (1 : ℚ) 2 (famType 3 1 3 1 1) 1) 1 = true := by
  decide +kernel
theorem pair_1_0_2_1_3 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 0 2 1 0) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 3 1 1) DK ∧
      XJ.ok (famType 3 0 2 1 0).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 0 2 1 0) DJ) DJ = true ∧
      XK.ok (famType 3 1 3 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 3 1 1) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨2, 1, 1, lu1_1, lu1_2, intOK_1_0_2_2, intOK_1_1_3_2,
    ok_1_0_2_2, ok_1_1_3_2,
    not_dvd_smooth (Fact.out) hp _ 3 (by decide +kernel)⟩

theorem pair_1_1_3_0_2 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 3 1 1) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 0 2 1 0) DK ∧
      XJ.ok (famType 3 1 3 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 3 1 1) DJ) DJ = true ∧
      XK.ok (famType 3 0 2 1 0).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 0 2 1 0) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨2, 1, 1, lu1_2, lu1_1, intOK_1_1_3_2, intOK_1_0_2_2,
    ok_1_1_3_2, ok_1_0_2_2,
    not_dvd_smooth (Fact.out) hp _ 3 (by decide +kernel)⟩

def lu1_3 : LuData where
  LM := [[1]]
  UM := [[44]]
  LA := [[1, 0], [-1, 44]]
  UA := [[44, -12], [0, -472]]
  LB := [[1, 0], [-1, 44]]
  UB := [[44, 4], [0, 172]]
  a := -472
  b := 172

theorem intOK_1_1_4_2 : IntOK 3 2 1 (1 : ℚ) 2 (famType 3 1 4 1 1) 4 := by decide +kernel
theorem ok_1_1_4_2 : lu1_3.ok (famType 3 1 4 1 1).nodes.length (mkFib 3 2 1 (1 : ℚ) 2 (famType 3 1 4 1 1) 4) 4 = true := by
  decide +kernel
theorem pair_1_1_3_1_4 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 3 1 1) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 4 1 1) DK ∧
      XJ.ok (famType 3 1 3 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 3 1 1) DJ) DJ = true ∧
      XK.ok (famType 3 1 4 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 4 1 1) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨2, 1, 4, lu1_2, lu1_3, intOK_1_1_3_2, intOK_1_1_4_2,
    ok_1_1_3_2, ok_1_1_4_2,
    not_dvd_smooth (Fact.out) hp _ 4 (by decide +kernel)⟩

theorem pair_1_1_4_1_3 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 4 1 1) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 3 1 1) DK ∧
      XJ.ok (famType 3 1 4 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 4 1 1) DJ) DJ = true ∧
      XK.ok (famType 3 1 3 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 3 1 1) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨2, 4, 1, lu1_3, lu1_2, intOK_1_1_4_2, intOK_1_1_3_2,
    ok_1_1_4_2, ok_1_1_3_2,
    not_dvd_smooth (Fact.out) hp _ 4 (by decide +kernel)⟩

def lu1_4 : LuData where
  LM := [[1]]
  UM := [[160]]
  LA := [[1, 0], [-1, 160]]
  UA := [[160, -12], [0, -1748]]
  LB := [[1, 0], [-1, 160]]
  UB := [[160, 4], [0, 636]]
  a := -1748
  b := 636

theorem intOK_1_1_4_31 : IntOK 3 2 1 (1 : ℚ) 31 (famType 3 1 4 1 1) 4 := by decide +kernel
theorem ok_1_1_4_31 : lu1_4.ok (famType 3 1 4 1 1).nodes.length (mkFib 3 2 1 (1 : ℚ) 31 (famType 3 1 4 1 1) 4) 4 = true := by
  decide +kernel
def lu1_5 : LuData where
  LM := [[1, 0], [2, 39]]
  UM := [[312, -16], [0, 9640]]
  LA := [[1, 0, 0], [2, 39, 0], [16, 71, 1928]]
  UA := [[312, -16, -16], [0, 9640, -32], [0, 0, -34960]]
  LB := [[1, 0, 0], [2, 39, 0], [16, 71, 1928]]
  UB := [[312, -16, 8], [0, 9640, 328], [0, 0, 16120]]
  a := -1398400
  b := 644800

theorem intOK_1_2_6_31 : IntOK 3 2 1 (1 : ℚ) 31 (famType 3 2 6 1 2) 8 := by decide +kernel
theorem ok_1_2_6_31 : lu1_5.ok (famType 3 2 6 1 2).nodes.length (mkFib 3 2 1 (1 : ℚ) 31 (famType 3 2 6 1 2) 8) 8 = true := by
  decide +kernel
theorem pair_1_1_4_2_6 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 4 1 1) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DK ∧
      XJ.ok (famType 3 1 4 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 4 1 1) DJ) DJ = true ∧
      XK.ok (famType 3 2 6 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨31, 4, 8, lu1_4, lu1_5, intOK_1_1_4_31, intOK_1_2_6_31,
    ok_1_1_4_31, ok_1_2_6_31,
    not_dvd_smooth (Fact.out) hp _ 8 (by decide +kernel)⟩

theorem intOK_1_1_5_31 : IntOK 3 2 1 (1 : ℚ) 31 (famType 3 1 5 1 1) 4 := by decide +kernel
theorem ok_1_1_5_31 : lu1_4.ok (famType 3 1 5 1 1).nodes.length (mkFib 3 2 1 (1 : ℚ) 31 (famType 3 1 5 1 1) 4) 4 = true := by
  decide +kernel
theorem pair_1_1_5_2_6 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 5 1 1) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DK ∧
      XJ.ok (famType 3 1 5 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 5 1 1) DJ) DJ = true ∧
      XK.ok (famType 3 2 6 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨31, 4, 8, lu1_4, lu1_5, intOK_1_1_5_31, intOK_1_2_6_31,
    ok_1_1_5_31, ok_1_2_6_31,
    not_dvd_smooth (Fact.out) hp _ 8 (by decide +kernel)⟩

theorem pair_1_2_6_1_5 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 5 1 1) DK ∧
      XJ.ok (famType 3 2 6 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DJ) DJ = true ∧
      XK.ok (famType 3 1 5 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 5 1 1) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨31, 8, 4, lu1_5, lu1_4, intOK_1_2_6_31, intOK_1_1_5_31,
    ok_1_2_6_31, ok_1_1_5_31,
    not_dvd_smooth (Fact.out) hp _ 8 (by decide +kernel)⟩

def lu1_6 : LuData where
  LM := [[1, 0], [2, 29]]
  UM := [[232, -16], [0, 4840]]
  LA := [[1, 0, 0], [2, 29, 0], [12, 53, 968]]
  UA := [[232, -16, -16], [0, 4840, -32], [0, 0, -17616]]
  LB := [[1, 0, 0], [2, 29, 0], [12, 53, 968]]
  UB := [[232, -16, 8], [0, 4840, 248], [0, 0, 8264]]
  a := -704640
  b := 330560

theorem intOK_1_2_6_21 : IntOK 3 2 1 (1 : ℚ) 21 (famType 3 2 6 1 2) 8 := by decide +kernel
theorem ok_1_2_6_21 : lu1_6.ok (famType 3 2 6 1 2).nodes.length (mkFib 3 2 1 (1 : ℚ) 21 (famType 3 2 6 1 2) 8) 8 = true := by
  decide +kernel
def lu1_7 : LuData where
  LM := [[1, 0], [-4, 473]]
  UM := [[3311, 28], [0, 1589168]]
  LA := [[1, 0, 0], [-4, 473, 0], [-1884, -4241, 794584]]
  UA := [[3311, 28, -308], [0, 1589168, -157696], [0, 0, -236369952]]
  LB := [[1, 0, 0], [-4, 473, 0], [-1884, -4241, 794584]]
  UB := [[3311, 28, 112], [0, 1589168, 52528], [0, 0, 88307408]]
  a := -3309179328
  b := 1236303712

theorem intOK_1_2_7_21 : IntOK 3 2 1 (1 : ℚ) 21 (famType 3 2 7 1 2) 112 := by decide +kernel
theorem ok_1_2_7_21 : lu1_7.ok (famType 3 2 7 1 2).nodes.length (mkFib 3 2 1 (1 : ℚ) 21 (famType 3 2 7 1 2) 112) 112 = true := by
  decide +kernel
theorem pair_1_2_6_2_7 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 7 1 2) DK ∧
      XJ.ok (famType 3 2 6 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DJ) DJ = true ∧
      XK.ok (famType 3 2 7 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 7 1 2) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨21, 8, 112, lu1_6, lu1_7, intOK_1_2_6_21, intOK_1_2_7_21,
    ok_1_2_6_21, ok_1_2_7_21,
    not_dvd_smooth (Fact.out) hp _ 23 (by decide +kernel)⟩

def lu1_8 : LuData where
  LM := [[1, 0], [-4, 169]]
  UM := [[1183, 28], [0, 208096]]
  LA := [[1, 0, 0], [-4, 169, 0], [-668, -1505, 104048]]
  UA := [[1183, 28, -308], [0, 208096, -55552], [0, 0, -30502976]]
  LB := [[1, 0, 0], [-4, 169, 0], [-668, -1505, 104048]]
  UB := [[1183, 28, 112], [0, 208096, 18480], [0, 0, 11410000]]
  a := -427041664
  b := 159740000

theorem intOK_1_2_7_2 : IntOK 3 2 1 (1 : ℚ) 2 (famType 3 2 7 1 2) 112 := by decide +kernel
theorem ok_1_2_7_2 : lu1_8.ok (famType 3 2 7 1 2).nodes.length (mkFib 3 2 1 (1 : ℚ) 2 (famType 3 2 7 1 2) 112) 112 = true := by
  decide +kernel
def lu1_9 : LuData where
  LM := [[1, 0, 0], [4, 165, 0], [376, 669, 3298]]
  UM := [[10395, -252, -1134], [0, 1662192, -337176], [0, 0, 4873680]]
  LA := [[1, 0, 0, 0], [4, 165, 0, 0], [376, 669, 3298, 0], [360752, 643413, 2751326, 4873680]]
  UA := [[10395, -252, -1134, -2268], [0, 1662192, -337176, -341712], [0, 0, 4873680, -2201472], [0, 0, 0, -13636685664]]
  LB := [[1, 0, 0, 0], [4, 165, 0, 0], [376, 669, 3298, 0], [360752, 643413, 2751326, 4873680]]
  UB := [[10395, -252, -1134, 1008], [0, 1662192, -337176, 170352], [0, 0, 4873680, 4377744], [0, 0, 0, 8698204368]]
  a := -432992043203328
  b := 276185385092736

theorem intOK_1_3_9_2 : IntOK 3 2 1 (1 : ℚ) 2 (famType 3 3 9 1 3) 1008 := by decide +kernel
theorem ok_1_3_9_2 : lu1_9.ok (famType 3 3 9 1 3).nodes.length (mkFib 3 2 1 (1 : ℚ) 2 (famType 3 3 9 1 3) 1008) 1008 = true := by
  decide +kernel
def lu1_10 : LuData where
  LM := [[1, 0], [-4, 185]]
  UM := [[1295, 28], [0, 248528]]
  LA := [[1, 0, 0], [-4, 185, 0], [-732, -1649, 124264]]
  UA := [[1295, 28, -308], [0, 248528, -60928], [0, 0, -36499680]]
  LB := [[1, 0, 0], [-4, 185, 0], [-732, -1649, 124264]]
  UB := [[1295, 28, 112], [0, 248528, 20272], [0, 0, 13650896]]
  a := -510995520
  b := 191112544

theorem intOK_1_2_7_3 : IntOK 3 2 1 (1 : ℚ) 3 (famType 3 2 7 1 2) 112 := by decide +kernel
theorem ok_1_2_7_3 : lu1_10.ok (famType 3 2 7 1 2).nodes.length (mkFib 3 2 1 (1 : ℚ) 3 (famType 3 2 7 1 2) 112) 112 = true := by
  decide +kernel
def lu1_11 : LuData where
  LM := [[1, 0, 0], [4, 181, 0], [412, 733, 3980]]
  UM := [[11403, -252, -1134], [0, 2005920, -369432], [0, 0, 10090584]]
  LA := [[1, 0, 0, 0], [4, 181, 0, 0], [412, 733, 3980, 0], [430448, 768737, 3303334, 10090584]]
  UA := [[11403, -252, -1134, -2268], [0, 2005920, -369432, -373968], [0, 0, 10090584, -2412144], [0, 0, 0, -26380170432]]
  LB := [[1, 0, 0, 0], [4, 181, 0, 0], [412, 733, 3980, 0], [430448, 768737, 3303334, 10090584]]
  UB := [[11403, -252, -1134, 1008], [0, 2005920, -369432, 186480], [0, 0, 10090584, 5166000], [0, 0, 0, 14709847824]]
  a := -837623171556864
  b := 467067088107648

theorem intOK_1_3_9_3 : IntOK 3 2 1 (1 : ℚ) 3 (famType 3 3 9 1 3) 1008 := by decide +kernel
theorem ok_1_3_9_3 : lu1_11.ok (famType 3 3 9 1 3).nodes.length (mkFib 3 2 1 (1 : ℚ) 3 (famType 3 3 9 1 3) 1008) 1008 = true := by
  decide +kernel
theorem pair_1_2_7_3_9 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 7 1 2) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DK ∧
      XJ.ok (famType 3 2 7 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 7 1 2) DJ) DJ = true ∧
      XK.ok (famType 3 3 9 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (369560348435 : ℤ) * (lu1_8.b * lu1_9.a - lu1_8.a * lu1_9.b) + (-229369135856 : ℤ) * (lu1_10.b * lu1_11.a - lu1_10.a * lu1_11.b) = 100370866176 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (100370866176 : ℤ) := not_dvd_smooth (Fact.out) hp _ 13 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 112, 1008, lu1_8, lu1_9, intOK_1_2_7_2, intOK_1_3_9_2,
      ok_1_2_7_2, ok_1_3_9_2, h⟩
  · exact ⟨3, 112, 1008, lu1_10, lu1_11, intOK_1_2_7_3, intOK_1_3_9_3,
      ok_1_2_7_3, ok_1_3_9_3, h⟩

def lu1_12 : LuData where
  LM := [[1, 0, 0], [-56, 8229, 0], [-21070, -32772, 1390637]]
  UM := [[370305, 2520, 5670], [0, 3066354585, 72262260], [0, 0, 539269891020]]
  LA := [[1, 0, 0, 0], [-56, 8229, 0, 0], [-21070, -32772, 1390637, 0], [-57423562, -90290868, -204157021, 19259638965]]
  UA := [[370305, 2520, 5670, -94500], [0, 3066354585, 72262260, -793085580], [0, 0, 539269891020, -142014365640], [0, 0, 0, -1761592021044660]]
  LB := [[1, 0, 0, 0], [-56, 8229, 0, 0], [-21070, -32772, 1390637, 0], [-57423562, -90290868, -204157021, 19259638965]]
  UB := [[370305, 2520, 5670, 35280], [0, 3066354585, 72262260, 288343440], [0, 0, 539269891020, 47162127600], [0, 0, 0, 667066037893920]]
  a := -4894231112068378878000
  b := 1853309573080677936000

theorem intOK_1_3_10_2 : IntOK 3 2 1 (1 : ℚ) 2 (famType 3 3 10 1 3) 35280 := by decide +kernel
theorem ok_1_3_10_2 : lu1_12.ok (famType 3 3 10 1 3).nodes.length (mkFib 3 2 1 (1 : ℚ) 2 (famType 3 3 10 1 3) 35280) 35280 = true := by
  decide +kernel
def lu1_13 : LuData where
  LM := [[1, 0, 0], [-56, 9013, 0], [-23086, -35908, 1667341]]
  UM := [[405585, 2520, 5670], [0, 3676486905, 79177140], [0, 0, 705437879580]]
  LA := [[1, 0, 0, 0], [-56, 9013, 0, 0], [-23086, -35908, 1667341, 0], [-68951050, -108410644, -245094269, 25194209985]]
  UA := [[405585, 2520, 5670, -94500], [0, 3676486905, 79177140, -869149260], [0, 0, 705437879580, -170805950280], [0, 0, 0, -2308249800303300]]
  LB := [[1, 0, 0, 0], [-56, 9013, 0, 0], [-23086, -35908, 1667341, 0], [-68951050, -108410644, -245094269, 25194209985]]
  UB := [[405585, 2520, 5670, 35280], [0, 3676486905, 79177140, 316002960], [0, 0, 705437879580, 56742482160], [0, 0, 0, 873947481896160]]
  a := -6413010420182658390000
  b := 2428088288952101328000

theorem intOK_1_3_10_3 : IntOK 3 2 1 (1 : ℚ) 3 (famType 3 3 10 1 3) 35280 := by decide +kernel
theorem ok_1_3_10_3 : lu1_13.ok (famType 3 3 10 1 3).nodes.length (mkFib 3 2 1 (1 : ℚ) 3 (famType 3 3 10 1 3) 35280) 35280 = true := by
  decide +kernel
theorem pair_1_2_7_3_10 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 7 1 2) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 10 1 3) DK ∧
      XJ.ok (famType 3 2 7 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 7 1 2) DJ) DJ = true ∧
      XK.ok (famType 3 3 10 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 10 1 3) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (-92454634998648 : ℤ) * (lu1_8.b * lu1_12.a - lu1_8.a * lu1_12.b) + (58860687404497 : ℤ) * (lu1_10.b * lu1_13.a - lu1_10.a * lu1_13.b) = 38423222208000 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (38423222208000 : ℤ) := not_dvd_smooth (Fact.out) hp _ 9 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 112, 35280, lu1_8, lu1_12, intOK_1_2_7_2, intOK_1_3_10_2,
      ok_1_2_7_2, ok_1_3_10_2, h⟩
  · exact ⟨3, 112, 35280, lu1_10, lu1_13, intOK_1_2_7_3, intOK_1_3_10_3,
      ok_1_2_7_3, ok_1_3_10_3, h⟩

theorem intOK_1_2_8_2 : IntOK 3 2 1 (1 : ℚ) 2 (famType 3 2 8 1 2) 112 := by decide +kernel
theorem ok_1_2_8_2 : lu1_8.ok (famType 3 2 8 1 2).nodes.length (mkFib 3 2 1 (1 : ℚ) 2 (famType 3 2 8 1 2) 112) 112 = true := by
  decide +kernel
theorem intOK_1_2_8_3 : IntOK 3 2 1 (1 : ℚ) 3 (famType 3 2 8 1 2) 112 := by decide +kernel
theorem ok_1_2_8_3 : lu1_10.ok (famType 3 2 8 1 2).nodes.length (mkFib 3 2 1 (1 : ℚ) 3 (famType 3 2 8 1 2) 112) 112 = true := by
  decide +kernel
theorem pair_1_2_8_3_9 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 8 1 2) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DK ∧
      XJ.ok (famType 3 2 8 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 8 1 2) DJ) DJ = true ∧
      XK.ok (famType 3 3 9 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (369560348435 : ℤ) * (lu1_8.b * lu1_9.a - lu1_8.a * lu1_9.b) + (-229369135856 : ℤ) * (lu1_10.b * lu1_11.a - lu1_10.a * lu1_11.b) = 100370866176 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (100370866176 : ℤ) := not_dvd_smooth (Fact.out) hp _ 13 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 112, 1008, lu1_8, lu1_9, intOK_1_2_8_2, intOK_1_3_9_2,
      ok_1_2_8_2, ok_1_3_9_2, h⟩
  · exact ⟨3, 112, 1008, lu1_10, lu1_11, intOK_1_2_8_3, intOK_1_3_9_3,
      ok_1_2_8_3, ok_1_3_9_3, h⟩

theorem pair_1_2_8_3_10 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 8 1 2) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 10 1 3) DK ∧
      XJ.ok (famType 3 2 8 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 8 1 2) DJ) DJ = true ∧
      XK.ok (famType 3 3 10 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 10 1 3) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (-92454634998648 : ℤ) * (lu1_8.b * lu1_12.a - lu1_8.a * lu1_12.b) + (58860687404497 : ℤ) * (lu1_10.b * lu1_13.a - lu1_10.a * lu1_13.b) = 38423222208000 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (38423222208000 : ℤ) := not_dvd_smooth (Fact.out) hp _ 9 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 112, 35280, lu1_8, lu1_12, intOK_1_2_8_2, intOK_1_3_10_2,
      ok_1_2_8_2, ok_1_3_10_2, h⟩
  · exact ⟨3, 112, 35280, lu1_10, lu1_13, intOK_1_2_8_3, intOK_1_3_10_3,
      ok_1_2_8_3, ok_1_3_10_3, h⟩

theorem pair_1_3_10_2_8 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 10 1 3) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 8 1 2) DK ∧
      XJ.ok (famType 3 3 10 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 10 1 3) DJ) DJ = true ∧
      XK.ok (famType 3 2 8 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 8 1 2) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (92454634998648 : ℤ) * (lu1_12.b * lu1_8.a - lu1_12.a * lu1_8.b) + (-58860687404497 : ℤ) * (lu1_13.b * lu1_10.a - lu1_13.a * lu1_10.b) = 38423222208000 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (38423222208000 : ℤ) := not_dvd_smooth (Fact.out) hp _ 9 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 35280, 112, lu1_12, lu1_8, intOK_1_3_10_2, intOK_1_2_8_2,
      ok_1_3_10_2, ok_1_2_8_2, h⟩
  · exact ⟨3, 35280, 112, lu1_13, lu1_10, intOK_1_3_10_3, intOK_1_2_8_3,
      ok_1_3_10_3, ok_1_2_8_3, h⟩

theorem pair_1_3_10_3_9 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 10 1 3) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DK ∧
      XJ.ok (famType 3 3 10 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 10 1 3) DJ) DJ = true ∧
      XK.ok (famType 3 3 9 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (5330604869275737 : ℤ) * (lu1_12.b * lu1_9.a - lu1_12.a * lu1_9.b) + (-3045105762794504 : ℤ) * (lu1_13.b * lu1_11.a - lu1_13.a * lu1_11.b) = 2352884435129088000 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (2352884435129088000 : ℤ) := not_dvd_smooth (Fact.out) hp _ 13 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 35280, 1008, lu1_12, lu1_9, intOK_1_3_10_2, intOK_1_3_9_2,
      ok_1_3_10_2, ok_1_3_9_2, h⟩
  · exact ⟨3, 35280, 1008, lu1_13, lu1_11, intOK_1_3_10_3, intOK_1_3_9_3,
      ok_1_3_10_3, ok_1_3_9_3, h⟩

theorem pair_1_2_7_2_6 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 7 1 2) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DK ∧
      XJ.ok (famType 3 2 7 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 7 1 2) DJ) DJ = true ∧
      XK.ok (famType 3 2 6 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨21, 112, 8, lu1_7, lu1_6, intOK_1_2_7_21, intOK_1_2_6_21,
    ok_1_2_7_21, ok_1_2_6_21,
    not_dvd_smooth (Fact.out) hp _ 23 (by decide +kernel)⟩

def lu1_14 : LuData where
  LM := [[1, 0, 0, 0], [672, 73277, 0, 0], [203658, 294964, 12089681, 0], [115555692, 166366386, 296044864, 1449454965]]
  UM := [[366385, -3360, -6090, -27580], [0, 26657746605, -650395620, -2926897890], [0, 0, 4261397597100, -870371900160], [0, 0, 0, 71594508880860]]
  LA := [[1, 0, 0, 0, 0], [672, 73277, 0, 0, 0], [203658, 294964, 12089681, 0, 0], [115555692, 166366386, 296044864, 1449454965, 0], [635728633596, 916240016158, 1634312141532, 6991558508589, 15341680474470]]
  UA := [[366385, -3360, -6090, -27580, -82740], [0, 26657746605, -650395620, -2926897890, -5872329540], [0, 0, 4261397597100, -870371900160, -893312796600], [0, 0, 0, 71594508880860, -43656167280600], [0, 0, 0, 0, -1537081751147465880]]
  LB := [[1, 0, 0, 0, 0], [672, 73277, 0, 0, 0], [203658, 294964, 12089681, 0, 0], [115555692, 166366386, 296044864, 1449454965, 0], [635728633596, 916240016158, 1634312141532, 6991558508589, 15341680474470]]
  UB := [[366385, -3360, -6090, -27580, 35280], [0, 26657746605, -650395620, -2926897890, 2608920720], [0, 0, 4261397597100, -870371900160, 444115329840], [0, 0, 0, 71594508880860, 71527444878960], [0, 0, 0, 0, 900328657638891600]]
  a := -232503596923819131406440000
  b := 136186413740431660090800000

theorem intOK_1_4_12_2 : IntOK 3 2 1 (1 : ℚ) 2 (famType 3 4 12 1 4) 35280 := by decide +kernel
theorem ok_1_4_12_2 : lu1_14.ok (famType 3 4 12 1 4).nodes.length (mkFib 3 2 1 (1 : ℚ) 2 (famType 3 4 12 1 4) 35280) 35280 = true := by
  decide +kernel
def lu1_15 : LuData where
  LM := [[1, 0, 0, 0], [672, 80333, 0, 0], [223146, 323188, 14539249, 0], [138740028, 199737514, 355398336, 1917749073]]
  UM := [[401665, -3360, -6090, -27580], [0, 32059044045, -712629540, -3206950530], [0, 0, 5638182274620, -1044871107840], [0, 0, 0, 166143623395260]]
  LA := [[1, 0, 0, 0, 0], [672, 80333, 0, 0, 0], [223146, 323188, 14539249, 0, 0], [138740028, 199737514, 355398336, 1917749073, 0], [830357294508, 1197495094774, 2138964666796, 9197726421897, 35602205013270]]
  UA := [[401665, -3360, -6090, -27580, -82740], [0, 32059044045, -712629540, -3206950530, -6432434820], [0, 0, 5638182274620, -1044871107840, -1070007172920], [0, 0, 0, 166143623395260, -52411420366200], [0, 0, 0, 0, -3323215002501245880]]
  LB := [[1, 0, 0, 0, 0], [672, 80333, 0, 0, 0], [223146, 323188, 14539249, 0, 0], [138740028, 199737514, 355398336, 1917749073, 0], [830357294508, 1197495094774, 2138964666796, 9197726421897, 35602205013270]]
  UB := [[401665, -3360, -6090, -27580, 35280], [0, 32059044045, -712629540, -3206950530, 2857856400], [0, 0, 5638182274620, -1044871107840, 532219368240], [0, 0, 0, 166143623395260, 92138128271280], [0, 0, 0, 0, 1727546886771123600]]
  a := -502679470923345955546440000
  b := 261313924733660469106800000

theorem intOK_1_4_12_3 : IntOK 3 2 1 (1 : ℚ) 3 (famType 3 4 12 1 4) 35280 := by decide +kernel
theorem ok_1_4_12_3 : lu1_15.ok (famType 3 4 12 1 4).nodes.length (mkFib 3 2 1 (1 : ℚ) 3 (famType 3 4 12 1 4) 35280) 35280 = true := by
  decide +kernel
theorem pair_1_3_10_4_12 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 1) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 10 1 3) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 4 12 1 4) DK ∧
      XJ.ok (famType 3 3 10 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 10 1 3) DJ) DJ = true ∧
      XK.ok (famType 3 4 12 1 4).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 4 12 1 4) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (778114433223253260654450 : ℤ) * (lu1_12.b * lu1_14.a - lu1_12.a * lu1_14.b) + (-402725869540109211388637 : ℤ) * (lu1_13.b * lu1_15.a - lu1_13.a * lu1_15.b) = 130770266869095840000000 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (130770266869095840000000 : ℤ) := not_dvd_smooth (Fact.out) hp _ 12 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 35280, 35280, lu1_12, lu1_14, intOK_1_3_10_2, intOK_1_4_12_2,
      ok_1_3_10_2, ok_1_4_12_2, h⟩
  · exact ⟨3, 35280, 35280, lu1_13, lu1_15, intOK_1_3_10_3, intOK_1_4_12_3,
      ok_1_3_10_3, ok_1_4_12_3, h⟩

def lu2_16 : LuData where
  LM := []
  UM := []
  LA := [[1]]
  UA := [[0]]
  LB := [[1]]
  UB := [[1]]
  a := 0
  b := 1

theorem intOK_2_0_1_2 : IntOK 3 2 2 (1 : ℚ) 2 (famType 3 0 1 1 0) 1 := by decide +kernel
theorem ok_2_0_1_2 : lu2_16.ok (famType 3 0 1 1 0).nodes.length (mkFib 3 2 2 (1 : ℚ) 2 (famType 3 0 1 1 0) 1) 1 = true := by
  decide +kernel
def lu2_17 : LuData where
  LM := []
  UM := []
  LA := [[1]]
  UA := [[-3]]
  LB := [[1]]
  UB := [[2]]
  a := -3
  b := 2

theorem intOK_2_0_2_2 : IntOK 3 2 2 (1 : ℚ) 2 (famType 3 0 2 1 0) 2 := by decide +kernel
theorem ok_2_0_2_2 : lu2_17.ok (famType 3 0 2 1 0).nodes.length (mkFib 3 2 2 (1 : ℚ) 2 (famType 3 0 2 1 0) 2) 2 = true := by
  decide +kernel
theorem pair_2_0_1_0_2 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 0 1 1 0) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 0 2 1 0) DK ∧
      XJ.ok (famType 3 0 1 1 0).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 0 1 1 0) DJ) DJ = true ∧
      XK.ok (famType 3 0 2 1 0).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 0 2 1 0) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨2, 1, 2, lu2_16, lu2_17, intOK_2_0_1_2, intOK_2_0_2_2,
    ok_2_0_1_2, ok_2_0_2_2,
    not_dvd_smooth (Fact.out) hp _ 1 (by decide +kernel)⟩

theorem pair_2_0_2_0_1 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 0 2 1 0) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 0 1 1 0) DK ∧
      XJ.ok (famType 3 0 2 1 0).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 0 2 1 0) DJ) DJ = true ∧
      XK.ok (famType 3 0 1 1 0).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 0 1 1 0) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨2, 2, 1, lu2_17, lu2_16, intOK_2_0_2_2, intOK_2_0_1_2,
    ok_2_0_2_2, ok_2_0_1_2,
    not_dvd_smooth (Fact.out) hp _ 1 (by decide +kernel)⟩

def lu2_18 : LuData where
  LM := [[1]]
  UM := [[4]]
  LA := [[1, 0], [1, 4]]
  UA := [[4, 0], [0, -4]]
  LB := [[1, 0], [1, 4]]
  UB := [[4, 2], [0, 10]]
  a := -4
  b := 10

theorem intOK_2_1_3_2 : IntOK 3 2 2 (1 : ℚ) 2 (famType 3 1 3 1 1) 2 := by decide +kernel
theorem ok_2_1_3_2 : lu2_18.ok (famType 3 1 3 1 1).nodes.length (mkFib 3 2 2 (1 : ℚ) 2 (famType 3 1 3 1 1) 2) 2 = true := by
  decide +kernel
theorem pair_2_0_2_1_3 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 0 2 1 0) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 3 1 1) DK ∧
      XJ.ok (famType 3 0 2 1 0).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 0 2 1 0) DJ) DJ = true ∧
      XK.ok (famType 3 1 3 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 3 1 1) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨2, 2, 2, lu2_17, lu2_18, intOK_2_0_2_2, intOK_2_1_3_2,
    ok_2_0_2_2, ok_2_1_3_2,
    not_dvd_smooth (Fact.out) hp _ 1 (by decide +kernel)⟩

theorem pair_2_1_3_0_2 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 3 1 1) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 0 2 1 0) DK ∧
      XJ.ok (famType 3 1 3 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 3 1 1) DJ) DJ = true ∧
      XK.ok (famType 3 0 2 1 0).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 0 2 1 0) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨2, 2, 2, lu2_18, lu2_17, intOK_2_1_3_2, intOK_2_0_2_2,
    ok_2_1_3_2, ok_2_0_2_2,
    not_dvd_smooth (Fact.out) hp _ 1 (by decide +kernel)⟩

def lu2_19 : LuData where
  LM := [[1]]
  UM := [[85]]
  LA := [[1, 0], [-8, 85]]
  UA := [[85, -30], [0, -1630]]
  LB := [[1, 0], [-8, 85]]
  UB := [[85, 20], [0, 1540]]
  a := -1630
  b := 1540

theorem intOK_2_1_5_2 : IntOK 3 2 2 (1 : ℚ) 2 (famType 3 1 5 1 1) 20 := by decide +kernel
theorem ok_2_1_5_2 : lu2_19.ok (famType 3 1 5 1 1).nodes.length (mkFib 3 2 2 (1 : ℚ) 2 (famType 3 1 5 1 1) 20) 20 = true := by
  decide +kernel
theorem pair_2_1_3_1_5 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 3 1 1) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 5 1 1) DK ∧
      XJ.ok (famType 3 1 3 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 3 1 1) DJ) DJ = true ∧
      XK.ok (famType 3 1 5 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 5 1 1) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨2, 2, 20, lu2_18, lu2_19, intOK_2_1_3_2, intOK_2_1_5_2,
    ok_2_1_3_2, ok_2_1_5_2,
    not_dvd_smooth (Fact.out) hp _ 2 (by decide +kernel)⟩

theorem intOK_2_1_4_2 : IntOK 3 2 2 (1 : ℚ) 2 (famType 3 1 4 1 1) 2 := by decide +kernel
theorem ok_2_1_4_2 : lu2_18.ok (famType 3 1 4 1 1).nodes.length (mkFib 3 2 2 (1 : ℚ) 2 (famType 3 1 4 1 1) 2) 2 = true := by
  decide +kernel
theorem pair_2_1_4_1_5 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 4 1 1) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 5 1 1) DK ∧
      XJ.ok (famType 3 1 4 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 4 1 1) DJ) DJ = true ∧
      XK.ok (famType 3 1 5 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 5 1 1) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨2, 2, 20, lu2_18, lu2_19, intOK_2_1_4_2, intOK_2_1_5_2,
    ok_2_1_4_2, ok_2_1_5_2,
    not_dvd_smooth (Fact.out) hp _ 2 (by decide +kernel)⟩

theorem pair_2_1_5_1_4 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 5 1 1) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 4 1 1) DK ∧
      XJ.ok (famType 3 1 5 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 5 1 1) DJ) DJ = true ∧
      XK.ok (famType 3 1 4 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 4 1 1) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨2, 20, 2, lu2_19, lu2_18, intOK_2_1_5_2, intOK_2_1_4_2,
    ok_2_1_5_2, ok_2_1_4_2,
    not_dvd_smooth (Fact.out) hp _ 2 (by decide +kernel)⟩

def lu2_20 : LuData where
  LM := [[1, 0], [2, 13]]
  UM := [[65, -10], [0, 500]]
  LA := [[1, 0, 0], [2, 13, 0], [14, 41, 250]]
  UA := [[65, -10, -10], [0, 500, -20], [0, 0, -3140]]
  LB := [[1, 0, 0], [2, 13, 0], [14, 41, 250]]
  UB := [[65, -10, 20], [0, 500, 300], [0, 0, 6100]]
  a := -31400
  b := 61000

theorem intOK_2_2_6_2 : IntOK 3 2 2 (1 : ℚ) 2 (famType 3 2 6 1 2) 20 := by decide +kernel
theorem ok_2_2_6_2 : lu2_20.ok (famType 3 2 6 1 2).nodes.length (mkFib 3 2 2 (1 : ℚ) 2 (famType 3 2 6 1 2) 20) 20 = true := by
  decide +kernel
def lu2_21 : LuData where
  LM := [[1]]
  UM := [[105]]
  LA := [[1, 0], [-8, 105]]
  UA := [[105, -30], [0, -2070]]
  LB := [[1, 0], [-8, 105]]
  UB := [[105, 20], [0, 1940]]
  a := -2070
  b := 1940

theorem intOK_2_1_5_3 : IntOK 3 2 2 (1 : ℚ) 3 (famType 3 1 5 1 1) 20 := by decide +kernel
theorem ok_2_1_5_3 : lu2_21.ok (famType 3 1 5 1 1).nodes.length (mkFib 3 2 2 (1 : ℚ) 3 (famType 3 1 5 1 1) 20) 20 = true := by
  decide +kernel
def lu2_22 : LuData where
  LM := [[1, 0], [2, 17]]
  UM := [[85, -10], [0, 1000]]
  LA := [[1, 0, 0], [2, 17, 0], [18, 53, 500]]
  UA := [[85, -10, -10], [0, 1000, -20], [0, 0, -6180]]
  LB := [[1, 0, 0], [2, 17, 0], [18, 53, 500]]
  UB := [[85, -10, 20], [0, 1000, 380], [0, 0, 11420]]
  a := -61800
  b := 114200

theorem intOK_2_2_6_3 : IntOK 3 2 2 (1 : ℚ) 3 (famType 3 2 6 1 2) 20 := by decide +kernel
theorem ok_2_2_6_3 : lu2_22.ok (famType 3 2 6 1 2).nodes.length (mkFib 3 2 2 (1 : ℚ) 3 (famType 3 2 6 1 2) 20) 20 = true := by
  decide +kernel
theorem pair_2_1_5_2_6 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 5 1 1) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DK ∧
      XJ.ok (famType 3 1 5 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 5 1 1) DJ) DJ = true ∧
      XK.ok (famType 3 2 6 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (5860 : ℤ) * (lu2_19.b * lu2_20.a - lu2_19.a * lu2_20.b) + (-2569 : ℤ) * (lu2_21.b * lu2_22.a - lu2_21.a * lu2_22.b) = 2000 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (2000 : ℤ) := not_dvd_smooth (Fact.out) hp _ 4 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 20, 20, lu2_19, lu2_20, intOK_2_1_5_2, intOK_2_2_6_2,
      ok_2_1_5_2, ok_2_2_6_2, h⟩
  · exact ⟨3, 20, 20, lu2_21, lu2_22, intOK_2_1_5_3, intOK_2_2_6_3,
      ok_2_1_5_3, ok_2_2_6_3, h⟩

theorem pair_2_2_6_1_5 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 1 5 1 1) DK ∧
      XJ.ok (famType 3 2 6 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DJ) DJ = true ∧
      XK.ok (famType 3 1 5 1 1).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 1 5 1 1) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (-5860 : ℤ) * (lu2_20.b * lu2_19.a - lu2_20.a * lu2_19.b) + (2569 : ℤ) * (lu2_22.b * lu2_21.a - lu2_22.a * lu2_21.b) = 2000 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (2000 : ℤ) := not_dvd_smooth (Fact.out) hp _ 4 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 20, 20, lu2_20, lu2_19, intOK_2_2_6_2, intOK_2_1_5_2,
      ok_2_2_6_2, ok_2_1_5_2, h⟩
  · exact ⟨3, 20, 20, lu2_22, lu2_21, intOK_2_2_6_3, intOK_2_1_5_3,
      ok_2_2_6_3, ok_2_1_5_3, h⟩

def lu2_23 : LuData where
  LM := [[1, 0, 0], [5, 168, 0], [205, 342, 2182]]
  UM := [[12096, -360, -1080], [0, 1963800, -307800], [0, 0, 14873400]]
  LA := [[1, 0, 0, 0], [5, 168, 0, 0], [205, 342, 2182, 0], [36320, 61197, 179810, 1487340]]
  UA := [[12096, -360, -1080, -2160], [0, 1963800, -307800, -313200], [0, 0, 14873400, -1058400], [0, 0, 0, -3624361200]]
  LB := [[1, 0, 0, 0], [5, 168, 0, 0], [205, 342, 2182, 0], [36320, 61197, 179810, 1487340]]
  UB := [[12096, -360, -1080, 3600], [0, 1963800, -307800, 622800], [0, 0, 14873400, 9824400], [0, 0, 0, 6352801200]]
  a := -2348586057600000
  b := 4116615177600000

theorem intOK_2_3_9_2 : IntOK 3 2 2 (1 : ℚ) 2 (famType 3 3 9 1 3) 3600 := by decide +kernel
theorem ok_2_3_9_2 : lu2_23.ok (famType 3 3 9 1 3).nodes.length (mkFib 3 2 2 (1 : ℚ) 2 (famType 3 3 9 1 3) 3600) 3600 = true := by
  decide +kernel
def lu2_24 : LuData where
  LM := [[1, 0], [-40, 361]]
  UM := [[1444, 160], [0, 607300]]
  LA := [[1, 0, 0], [-40, 361, 0], [-3410, -7181, 121460]]
  UA := [[1444, 160, -440], [0, 607300, -199000], [0, 0, -41560400]]
  LB := [[1, 0, 0], [-40, 361, 0], [-3410, -7181, 121460]]
  UB := [[1444, 160, 400], [0, 607300, 128400], [0, 0, 44347600]]
  a := -831208000
  b := 886952000

theorem intOK_2_2_8_2 : IntOK 3 2 2 (1 : ℚ) 2 (famType 3 2 8 1 2) 400 := by decide +kernel
theorem ok_2_2_8_2 : lu2_24.ok (famType 3 2 8 1 2).nodes.length (mkFib 3 2 2 (1 : ℚ) 2 (famType 3 2 8 1 2) 400) 400 = true := by
  decide +kernel
def lu2_25 : LuData where
  LM := [[1, 0, 0], [5, 218, 0], [265, 442, 3704]]
  UM := [[15696, -360, -1080], [0, 3333600, -397800], [0, 0, 38921400]]
  LA := [[1, 0, 0, 0], [5, 218, 0, 0], [265, 442, 3704, 0], [8600, 14519, 42922, 556020]]
  UA := [[15696, -360, -1080, -2160], [0, 3333600, -397800, -403200], [0, 0, 38921400, -1368000], [0, 0, 0, -1329116400]]
  LB := [[1, 0, 0, 0], [5, 218, 0, 0], [265, 442, 3704, 0], [8600, 14519, 42922, 556020]]
  UB := [[15696, -360, -1080, 3600], [0, 3333600, -397800, 802800], [0, 0, 38921400, 15879600], [0, 0, 0, 2239419600]]
  a := -6028871990400000
  b := 10158007305600000

theorem intOK_2_3_9_3 : IntOK 3 2 2 (1 : ℚ) 3 (famType 3 3 9 1 3) 3600 := by decide +kernel
theorem ok_2_3_9_3 : lu2_25.ok (famType 3 3 9 1 3).nodes.length (mkFib 3 2 2 (1 : ℚ) 3 (famType 3 3 9 1 3) 3600) 3600 = true := by
  decide +kernel
def lu2_26 : LuData where
  LM := [[1, 0], [-40, 461]]
  UM := [[1844, 160], [0, 961700]]
  LA := [[1, 0, 0], [-40, 461, 0], [-4410, -9281, 192340]]
  UA := [[1844, 160, -440], [0, 961700, -259000], [0, 0, -67503600]]
  LB := [[1, 0, 0], [-40, 461, 0], [-4410, -9281, 192340]]
  UB := [[1844, 160, 400], [0, 961700, 168400], [0, 0, 71459600]]
  a := -1350072000
  b := 1429192000

theorem intOK_2_2_8_3 : IntOK 3 2 2 (1 : ℚ) 3 (famType 3 2 8 1 2) 400 := by decide +kernel
theorem ok_2_2_8_3 : lu2_26.ok (famType 3 2 8 1 2).nodes.length (mkFib 3 2 2 (1 : ℚ) 3 (famType 3 2 8 1 2) 400) 400 = true := by
  decide +kernel
theorem pair_2_3_9_2_8 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 8 1 2) DK ∧
      XJ.ok (famType 3 3 9 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DJ) DJ = true ∧
      XK.ok (famType 3 2 8 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 8 1 2) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (-27291933801 : ℤ) * (lu2_23.b * lu2_24.a - lu2_23.a * lu2_24.b) + (7167096740 : ℤ) * (lu2_25.b * lu2_26.a - lu2_25.a * lu2_26.b) = 74649600000000 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (74649600000000 : ℤ) := not_dvd_smooth (Fact.out) hp _ 18 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 3600, 400, lu2_23, lu2_24, intOK_2_3_9_2, intOK_2_2_8_2,
      ok_2_3_9_2, ok_2_2_8_2, h⟩
  · exact ⟨3, 3600, 400, lu2_25, lu2_26, intOK_2_3_9_3, intOK_2_2_8_3,
      ok_2_3_9_3, ok_2_2_8_3, h⟩

def lu2_27 : LuData where
  LM := [[1, 0, 0], [-200, 5601, 0], [-143620, -218790, 2019461]]
  UM := [[554499, 19800, 41580], [0, 3198826224, 346563360], [0, 0, 1339666891200]]
  LA := [[1, 0, 0, 0], [-200, 5601, 0, 0], [-143620, -218790, 2019461, 0], [-223463120, -342630915, -723084614, 16745836140]]
  UA := [[554499, 19800, 41580, -154440], [0, 3198826224, 346563360, -945030240], [0, 0, 1339666891200, -419521291200], [0, 0, 0, -2159450347348800]]
  LB := [[1, 0, 0, 0], [-200, 5601, 0, 0], [-143620, -218790, 2019461, 0], [-223463120, -342630915, -723084614, 16745836140]]
  UB := [[554499, 19800, 41580, 158400], [0, 3198826224, 346563360, 855518400], [0, 0, 1339666891200, 262476878400], [0, 0, 0, 2448334546574400]]
  a := -27090909253587953664000
  b := 30715042420448888832000

theorem intOK_2_3_11_2 : IntOK 3 2 2 (1 : ℚ) 2 (famType 3 3 11 1 3) 158400 := by decide +kernel
theorem ok_2_3_11_2 : lu2_27.ok (famType 3 3 11 1 3).nodes.length (mkFib 3 2 2 (1 : ℚ) 2 (famType 3 3 11 1 3) 158400) 158400 = true := by
  decide +kernel
def lu2_28 : LuData where
  LM := [[1, 0, 0], [-200, 7201, 0], [-185620, -282790, 3317161]]
  UM := [[712899, 19800, 41580], [0, 5254383024, 447939360], [0, 0, 2732915433600]]
  LA := [[1, 0, 0, 0], [-200, 7201, 0, 0], [-185620, -282790, 3317161, 0], [-186833560, -286381645, -603922832, 17080721460]]
  UA := [[712899, 19800, 41580, -154440], [0, 5254383024, 447939360, -1223814240], [0, 0, 2732915433600, -710216971200], [0, 0, 0, -2251725918552000]]
  LB := [[1, 0, 0, 0], [-200, 7201, 0, 0], [-185620, -282790, 3317161, 0], [-186833560, -286381645, -603922832, 17080721460]]
  UB := [[712899, 19800, 41580, 158400], [0, 5254383024, 447939360, 1108958400], [0, 0, 2732915433600, 451242158400], [0, 0, 0, 2534967614203200]]
  a := -56497064262984069120000
  b := 63603757022222241792000

theorem intOK_2_3_11_3 : IntOK 3 2 2 (1 : ℚ) 3 (famType 3 3 11 1 3) 158400 := by decide +kernel
theorem ok_2_3_11_3 : lu2_28.ok (famType 3 3 11 1 3).nodes.length (mkFib 3 2 2 (1 : ℚ) 3 (famType 3 3 11 1 3) 158400) 158400 = true := by
  decide +kernel
theorem pair_2_3_9_3_11 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 11 1 3) DK ∧
      XJ.ok (famType 3 3 9 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DJ) DJ = true ∧
      XK.ok (famType 3 3 11 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 11 1 3) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (31490370544078 : ℤ) * (lu2_23.b * lu2_27.a - lu2_23.a * lu2_27.b) + (-6512739145817 : ℤ) * (lu2_25.b * lu2_28.a - lu2_25.a * lu2_28.b) = 222512431811788800000000 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (222512431811788800000000 : ℤ) := not_dvd_smooth (Fact.out) hp _ 28 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 3600, 158400, lu2_23, lu2_27, intOK_2_3_9_2, intOK_2_3_11_2,
      ok_2_3_9_2, ok_2_3_11_2, h⟩
  · exact ⟨3, 3600, 158400, lu2_25, lu2_28, intOK_2_3_9_3, intOK_2_3_11_3,
      ok_2_3_9_3, ok_2_3_11_3, h⟩

def lu2_29 : LuData where
  LM := [[1, 0], [2, 109]]
  UM := [[545, -10], [0, 56660]]
  LA := [[1, 0, 0], [2, 109, 0], [110, 329, 28330]]
  UA := [[545, -10, -10], [0, 56660, -20], [0, 0, -341060]]
  LB := [[1, 0, 0], [2, 109, 0], [110, 329, 28330]]
  UB := [[545, -10, 20], [0, 56660, 2220], [0, 0, 575380]]
  a := -3410600
  b := 5753800

theorem intOK_2_2_6_26 : IntOK 3 2 2 (1 : ℚ) 26 (famType 3 2 6 1 2) 20 := by decide +kernel
theorem ok_2_2_6_26 : lu2_29.ok (famType 3 2 6 1 2).nodes.length (mkFib 3 2 2 (1 : ℚ) 26 (famType 3 2 6 1 2) 20) 20 = true := by
  decide +kernel
def lu2_30 : LuData where
  LM := [[1, 0], [-40, 2761]]
  UM := [[11044, 160], [0, 31192900]]
  LA := [[1, 0, 0], [-40, 2761, 0], [-27410, -57581, 6238580]]
  UA := [[11044, 160, -440], [0, 31192900, -1639000], [0, 0, -2386437200]]
  LB := [[1, 0, 0], [-40, 2761, 0], [-27410, -57581, 6238580]]
  UB := [[11044, 160, 400], [0, 31192900, 1088400], [0, 0, 2461435600]]
  a := -47728744000
  b := 49228712000

theorem intOK_2_2_8_26 : IntOK 3 2 2 (1 : ℚ) 26 (famType 3 2 8 1 2) 400 := by decide +kernel
theorem ok_2_2_8_26 : lu2_30.ok (famType 3 2 8 1 2).nodes.length (mkFib 3 2 2 (1 : ℚ) 26 (famType 3 2 8 1 2) 400) 400 = true := by
  decide +kernel
theorem pair_2_2_6_2_8 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 8 1 2) DK ∧
      XJ.ok (famType 3 2 6 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DJ) DJ = true ∧
      XK.ok (famType 3 2 8 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 8 1 2) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨26, 20, 400, lu2_29, lu2_30, intOK_2_2_6_26, intOK_2_2_8_26,
    ok_2_2_6_26, ok_2_2_8_26,
    not_dvd_smooth (Fact.out) hp _ 11 (by decide +kernel)⟩

theorem pair_2_2_6_3_9 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DK ∧
      XJ.ok (famType 3 2 6 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 6 1 2) DJ) DJ = true ∧
      XK.ok (famType 3 3 9 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (-13653634 : ℤ) * (lu2_20.b * lu2_23.a - lu2_20.a * lu2_23.b) + (3147889 : ℤ) * (lu2_22.b * lu2_25.a - lu2_22.a * lu2_25.b) = 1866240000000 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (1866240000000 : ℤ) := not_dvd_smooth (Fact.out) hp _ 15 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 20, 3600, lu2_20, lu2_23, intOK_2_2_6_2, intOK_2_3_9_2,
      ok_2_2_6_2, ok_2_3_9_2, h⟩
  · exact ⟨3, 20, 3600, lu2_22, lu2_25, intOK_2_2_6_3, intOK_2_3_9_3,
      ok_2_2_6_3, ok_2_3_9_3, h⟩

theorem intOK_2_2_7_26 : IntOK 3 2 2 (1 : ℚ) 26 (famType 3 2 7 1 2) 20 := by decide +kernel
theorem ok_2_2_7_26 : lu2_29.ok (famType 3 2 7 1 2).nodes.length (mkFib 3 2 2 (1 : ℚ) 26 (famType 3 2 7 1 2) 20) 20 = true := by
  decide +kernel
theorem pair_2_2_7_2_8 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 7 1 2) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 8 1 2) DK ∧
      XJ.ok (famType 3 2 7 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 7 1 2) DJ) DJ = true ∧
      XK.ok (famType 3 2 8 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 8 1 2) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  exact ⟨26, 20, 400, lu2_29, lu2_30, intOK_2_2_7_26, intOK_2_2_8_26,
    ok_2_2_7_26, ok_2_2_8_26,
    not_dvd_smooth (Fact.out) hp _ 11 (by decide +kernel)⟩

theorem intOK_2_2_7_2 : IntOK 3 2 2 (1 : ℚ) 2 (famType 3 2 7 1 2) 20 := by decide +kernel
theorem ok_2_2_7_2 : lu2_20.ok (famType 3 2 7 1 2).nodes.length (mkFib 3 2 2 (1 : ℚ) 2 (famType 3 2 7 1 2) 20) 20 = true := by
  decide +kernel
theorem intOK_2_2_7_3 : IntOK 3 2 2 (1 : ℚ) 3 (famType 3 2 7 1 2) 20 := by decide +kernel
theorem ok_2_2_7_3 : lu2_22.ok (famType 3 2 7 1 2).nodes.length (mkFib 3 2 2 (1 : ℚ) 3 (famType 3 2 7 1 2) 20) 20 = true := by
  decide +kernel
theorem pair_2_2_7_3_9 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 7 1 2) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DK ∧
      XJ.ok (famType 3 2 7 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 7 1 2) DJ) DJ = true ∧
      XK.ok (famType 3 3 9 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (-13653634 : ℤ) * (lu2_20.b * lu2_23.a - lu2_20.a * lu2_23.b) + (3147889 : ℤ) * (lu2_22.b * lu2_25.a - lu2_22.a * lu2_25.b) = 1866240000000 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (1866240000000 : ℤ) := not_dvd_smooth (Fact.out) hp _ 15 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 20, 3600, lu2_20, lu2_23, intOK_2_2_7_2, intOK_2_3_9_2,
      ok_2_2_7_2, ok_2_3_9_2, h⟩
  · exact ⟨3, 20, 3600, lu2_22, lu2_25, intOK_2_2_7_3, intOK_2_3_9_3,
      ok_2_2_7_3, ok_2_3_9_3, h⟩

theorem pair_2_3_9_2_7 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 2 7 1 2) DK ∧
      XJ.ok (famType 3 3 9 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DJ) DJ = true ∧
      XK.ok (famType 3 2 7 1 2).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 2 7 1 2) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (13653634 : ℤ) * (lu2_23.b * lu2_20.a - lu2_23.a * lu2_20.b) + (-3147889 : ℤ) * (lu2_25.b * lu2_22.a - lu2_25.a * lu2_22.b) = 1866240000000 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (1866240000000 : ℤ) := not_dvd_smooth (Fact.out) hp _ 15 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 3600, 20, lu2_23, lu2_20, intOK_2_3_9_2, intOK_2_2_7_2,
      ok_2_3_9_2, ok_2_2_7_2, h⟩
  · exact ⟨3, 3600, 20, lu2_25, lu2_22, intOK_2_3_9_3, intOK_2_2_7_3,
      ok_2_3_9_3, ok_2_2_7_3, h⟩

def lu2_31 : LuData where
  LM := [[1, 0, 0, 0], [600, 48809, 0, 0], [87180, 123085, 4099331, 0], [5394300, 7570155, 12631427, 79826052]]
  UM := [[536899, -6600, -11220, -33880], [0, 25973361216, -779866560, -2339731680], [0, 0, 2107407772800, -333469672800], [0, 0, 0, 23745991605600]]
  LA := [[1, 0, 0, 0, 0], [600, 48809, 0, 0, 0], [87180, 123085, 4099331, 0, 0], [5394300, 7570155, 12631427, 79826052, 0], [97214823540, 137094588715, 231122751417, 680367445494, 7123797481680]]
  UA := [[536899, -6600, -11220, -33880, -101640], [0, 25973361216, -779866560, -2339731680, -4699791360], [0, 0, 2107407772800, -333469672800, -345225988800], [0, 0, 0, 23745991605600, -2268153201600], [0, 0, 0, 0, -790923753260308800]]
  LB := [[1, 0, 0, 0, 0], [600, 48809, 0, 0, 0], [87180, 123085, 4099331, 0, 0], [5394300, 7570155, 12631427, 79826052, 0], [97214823540, 137094588715, 231122751417, 680367445494, 7123797481680]]
  UB := [[536899, -6600, -11220, -33880, 158400], [0, 25973361216, -779866560, -2339731680, 7826385600], [0, 0, 2107407772800, -333469672800, 682640006400], [0, 0, 0, 23745991605600, 16698834345600], [0, 0, 0, 0, 1309904179190006400]]
  a := -4850931527836282426982400000
  b := 8033967187208748372787200000

theorem intOK_2_4_12_2 : IntOK 3 2 2 (1 : ℚ) 2 (famType 3 4 12 1 4) 158400 := by decide +kernel
theorem ok_2_4_12_2 : lu2_31.ok (famType 3 4 12 1 4).nodes.length (mkFib 3 2 2 (1 : ℚ) 2 (famType 3 4 12 1 4) 158400) 158400 = true := by
  decide +kernel
def lu2_32 : LuData where
  LM := [[1, 0, 0, 0], [600, 63209, 0, 0], [112680, 159085, 6889156, 0], [1287660, 1806830, 3014061, 25075734]]
  UM := [[695299, -6600, -11220, -33880], [0, 43649692416, -1007962560, -3024019680], [0, 0, 4633995643200, -556998472800], [0, 0, 0, 11547788683200]]
  LA := [[1, 0, 0, 0, 0], [600, 63209, 0, 0, 0], [112680, 159085, 6889156, 0, 0], [1287660, 1806830, 3014061, 25075734, 0], [4243930380, 5990878330, 10121001589, 29989500858, 494905229280]]
  UA := [[695299, -6600, -11220, -33880, -101640], [0, 43649692416, -1007962560, -3024019680, -6068367360], [0, 0, 4633995643200, -556998472800, -572193388800], [0, 0, 0, 11547788683200, -541312516800], [0, 0, 0, 0, -53886135815582400]]
  LB := [[1, 0, 0, 0, 0], [600, 63209, 0, 0, 0], [112680, 159085, 6889156, 0, 0], [1287660, 1806830, 3014061, 25075734, 0], [4243930380, 5990878330, 10121001589, 29989500858, 494905229280]]
  UB := [[695299, -6600, -11220, -33880, 158400], [0, 43649692416, -1007962560, -3024019680, 10107345600], [0, 0, 4633995643200, -556998472800, 1134289886400], [0, 0, 0, 11547788683200, 4939590744000], [0, 0, 0, 0, 86367685605220800]]
  a := -16194354701213807058124800000
  b := 25956007315139613796761600000

theorem intOK_2_4_12_3 : IntOK 3 2 2 (1 : ℚ) 3 (famType 3 4 12 1 4) 158400 := by decide +kernel
theorem ok_2_4_12_3 : lu2_32.ok (famType 3 4 12 1 4).nodes.length (mkFib 3 2 2 (1 : ℚ) 3 (famType 3 4 12 1 4) 158400) 158400 = true := by
  decide +kernel
theorem pair_2_3_9_4_12 {Fr : Frame} {p : ℕ} [Fact p.Prime] (hp3 : p % 3 = 2) (hp : 60 ≤ p) (hn : Fr.norm = 1) :
    ∃ (u0 DJ DK : ℤ) (XJ XK : LuData),
      IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DJ ∧ IntOK 3 2 (p % 3) Fr.norm u0 (famType 3 4 12 1 4) DK ∧
      XJ.ok (famType 3 3 9 1 3).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 3 9 1 3) DJ) DJ = true ∧
      XK.ok (famType 3 4 12 1 4).nodes.length (mkFib 3 2 (p % 3) Fr.norm u0 (famType 3 4 12 1 4) DK) DK = true ∧
      ¬ (p : ℤ) ∣ XJ.b * XK.a - XJ.a * XK.b := by
  rw [hp3, hn]
  have hb : (740161835414766165 : ℤ) * (lu2_23.b * lu2_31.a - lu2_23.a * lu2_31.b) + (-101645531540237624 : ℤ) * (lu2_25.b * lu2_32.a - lu2_25.a * lu2_32.b) = 2266330324008960000000000 := by decide +kernel
  have hg : ¬ (p : ℤ) ∣ (2266330324008960000000000 : ℤ) := not_dvd_smooth (Fact.out) hp _ 28 (by decide +kernel)
  rcases not_dvd_or_of_bezout hb hg with h | h
  · exact ⟨2, 3600, 158400, lu2_23, lu2_31, intOK_2_3_9_2, intOK_2_4_12_2,
      ok_2_3_9_2, ok_2_4_12_2, h⟩
  · exact ⟨3, 3600, 158400, lu2_25, lu2_32, intOK_2_3_9_3, intOK_2_4_12_3,
      ok_2_3_9_3, ok_2_4_12_3, h⟩

end CatalanCore.Uniform.Content.UFFamily3
