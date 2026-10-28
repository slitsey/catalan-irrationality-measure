module

public import CatalanCore.Uniform.Content.UFFamily3.Thirds

@[expose] public section

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.UFFamily CatalanCore.Uniform.Content.UFFamily.SevE
  CatalanCore.Uniform.Content.UFFamily2 CatalanCore.Uniform.Content.UFFamily3

namespace CatalanCore.Uniform.Content.UFFamily4

open CatalanCore.Uniform.Content.UFFamily3

set_option maxHeartbeats 1600000 in
theorem emp1_1 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : r ≤ 2 * p)
    (h45 : (r + 2 * ((3 * r + 9) / 20)) ≤ ((7*p+2)/3))
    (h46 : 3 * r < 5 * p + 2)
    (h53 : 1 * p < r)
    (h54 : 4 * p + 2 < 3 * r)
    (h55 : 3 * r ≤ 7 * p + 2)
    (h56 : 4 * p + 2 ≤ 3 * r)
    (h57 : r < (2*p))
    (h58 : base3 ((3 * r + 9) / 20) r p (2*p+1) (((7*p+2)/3)-1) < base3 ((3 * r + 9) / 20) r p r ((2*p)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp1_2 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : r ≤ 2 * p)
    (h45 : ((7*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h59 : (2*p) ≤ r)
    (h60 : 1 * p < r)
    (h61 : 4 * p + 2 < 3 * r)
    (h62 : 3 * r ≤ 7 * p + 2)
    (h63 : base3 ((3 * r + 9) / 20) r p ((7*p+2)/3) (r+p-1) < base3 ((3 * r + 9) / 20) r p (2*p+1) (((7*p+2)/3)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp1_3 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : r ≤ 2 * p)
    (h45 : ((7*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h59 : r < (2*p))
    (h64 : 1 * p < r)
    (h65 : 4 * p + 2 < 3 * r)
    (h66 : 3 * r ≤ 7 * p + 2)
    (h67 : 5 * p + 2 ≤ 3 * r)
    (h68 : 3 * r < 6 * p + 2)
    (h69 : base3 ((3 * r + 9) / 20) r p r ((2*p)-1) ≤ base3 ((3 * r + 9) / 20) r p (2*p+1) (((7*p+2)/3)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp1_4 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : r ≤ 2 * p)
    (h45 : ((7*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h59 : r < (2*p))
    (h64 : 1 * p < r)
    (h65 : 4 * p + 2 < 3 * r)
    (h66 : 3 * r ≤ 7 * p + 2)
    (h67 : 5 * p + 2 ≤ 3 * r)
    (h68 : 3 * r < 6 * p + 2)
    (h69 : base3 ((3 * r + 9) / 20) r p (2*p+1) (((7*p+2)/3)-1) < base3 ((3 * r + 9) / 20) r p r ((2*p)-1))
    (h70 : base3 ((3 * r + 9) / 20) r p ((7*p+2)/3) (r+p-1) < base3 ((3 * r + 9) / 20) r p (2*p+1) (((7*p+2)/3)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

theorem sub1_5 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : r ≤ 2 * p) :
    ∃ i, RegOf i r p := by
  rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((7*p+2)/3)) with h45 | h45
  · rcases le_or_gt (5 * p + 2) (3 * r) with h46 | h46
    · rcases le_or_gt (r) (1 * p) with h47 | h47
      · exfalso; omega
      · rcases le_or_gt (3 * r) (4 * p + 2) with h48 | h48
        · exfalso; omega
        · rcases le_or_gt (3 * r) (7 * p + 2) with h49 | h49
          · rcases le_or_gt (6 * p + 2) (3 * r) with h50 | h50
            · exfalso; omega
            · rcases le_or_gt ((2*p)) (r) with h51 | h51
              · exfalso; omega
              · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r ((2*p)-1)) (base3 ((3 * r + 9) / 20) r p (2*p+1) (((7*p+2)/3)-1)) with h52 | h52
                · exact ⟨13, show F13.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h47, h44, h48, h49, h46, h50, h51, h24, h45, h52⟩⟩
                · exact ⟨14, show F14.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h47, h44, h48, h49, h46, h50, h51, h24, h45, h52⟩⟩
          · exfalso; omega
    · rcases le_or_gt (r) (1 * p) with h53 | h53
      · exfalso; omega
      · rcases le_or_gt (3 * r) (4 * p + 2) with h54 | h54
        · exfalso; omega
        · rcases le_or_gt (3 * r) (7 * p + 2) with h55 | h55
          · rcases le_or_gt (4 * p + 2) (3 * r) with h56 | h56
            · rcases le_or_gt ((2*p)) (r) with h57 | h57
              · exfalso; omega
              · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r ((2*p)-1)) (base3 ((3 * r + 9) / 20) r p (2*p+1) (((7*p+2)/3)-1)) with h58 | h58
                · exact ⟨12, show F12.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h53, h44, h54, h55, h56, h46, h57, h24, h45, h58⟩⟩
                · exact absurd (emp1_1 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h45 h46 h53 h54 h55 h56 h57 h58) id
            · exfalso; omega
          · exfalso; omega
  · rcases le_or_gt ((2*p)) (r) with h59 | h59
    · rcases le_or_gt (r) (1 * p) with h60 | h60
      · exfalso; omega
      · rcases le_or_gt (3 * r) (4 * p + 2) with h61 | h61
        · exfalso; omega
        · rcases le_or_gt (3 * r) (7 * p + 2) with h62 | h62
          · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p (2*p+1) (((7*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((7*p+2)/3) (r+p-1)) with h63 | h63
            · exact ⟨16, show F16.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h60, h44, h61, h62, h59, h24, h45, h63⟩⟩
            · exact absurd (emp1_2 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h45 h59 h60 h61 h62 h63) id
          · exfalso; omega
    · rcases le_or_gt (r) (1 * p) with h64 | h64
      · exfalso; omega
      · rcases le_or_gt (3 * r) (4 * p + 2) with h65 | h65
        · exfalso; omega
        · rcases le_or_gt (3 * r) (7 * p + 2) with h66 | h66
          · rcases le_or_gt (5 * p + 2) (3 * r) with h67 | h67
            · rcases le_or_gt (6 * p + 2) (3 * r) with h68 | h68
              · exfalso; omega
              · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r ((2*p)-1)) (base3 ((3 * r + 9) / 20) r p (2*p+1) (((7*p+2)/3)-1)) with h69 | h69
                · exact absurd (emp1_3 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h45 h59 h64 h65 h66 h67 h68 h69) id
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p (2*p+1) (((7*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((7*p+2)/3) (r+p-1)) with h70 | h70
                  · exact ⟨15, show F15.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h64, h44, h65, h66, h67, h68, h59, h24, h45, h69, h70⟩⟩
                  · exact absurd (emp1_4 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h45 h59 h64 h65 h66 h67 h68 h69 h70) id
            · exfalso; omega
          · exfalso; omega

set_option maxHeartbeats 1600000 in
theorem emp1_6 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : 2 * p < r)
    (h71 : 3 * r ≤ 7 * p + 2)
    (h72 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h80 : r ≤ 3 * p)
    (h81 : 4 * p + 2 < 3 * r)
    (h82 : 6 * p + 2 ≤ 3 * r)
    (h83 : 3 * r < 7 * p + 2)
    (h84 : r < ((7*p+2)/3))
    (h85 : ((7*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h86 : base3 ((3 * r + 9) / 20) r p r (((7*p+2)/3)-1) ≤ base3 ((3 * r + 9) / 20) r p ((7*p+2)/3) ((3*p)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp1_7 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : 2 * p < r)
    (h71 : 3 * r ≤ 7 * p + 2)
    (h72 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h80 : r ≤ 3 * p)
    (h81 : 4 * p + 2 < 3 * r)
    (h82 : 6 * p + 2 ≤ 3 * r)
    (h83 : 3 * r < 7 * p + 2)
    (h84 : r < ((7*p+2)/3))
    (h85 : ((7*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h86 : base3 ((3 * r + 9) / 20) r p ((7*p+2)/3) ((3*p)-1) < base3 ((3 * r + 9) / 20) r p r (((7*p+2)/3)-1))
    (h87 : base3 ((3 * r + 9) / 20) r p (3*p+1) (r+p-1) < base3 ((3 * r + 9) / 20) r p ((7*p+2)/3) ((3*p)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp1_8 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : 2 * p < r)
    (h71 : 7 * p + 2 < 3 * r)
    (h88 : 8 * p + 2 ≤ 3 * r)
    (h89 : r ≤ 3 * p)
    (h90 : 3 * r ≤ 10 * p + 2)
    (h91 : 3 * r < 9 * p + 2)
    (h92 : r < (3*p))
    (h93 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h94 : ((10*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h95 : base3 ((3 * r + 9) / 20) r p r ((3*p)-1) ≤ base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) (r+p-1))
    (h96 : base3 ((3 * r + 9) / 20) r p (3*p+1) (((10*p+2)/3)-1) < base3 ((3 * r + 9) / 20) r p r ((3*p)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp1_9 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : 2 * p < r)
    (h71 : 7 * p + 2 < 3 * r)
    (h88 : 8 * p + 2 ≤ 3 * r)
    (h89 : r ≤ 3 * p)
    (h90 : 3 * r ≤ 10 * p + 2)
    (h91 : 3 * r < 9 * p + 2)
    (h92 : r < (3*p))
    (h93 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h94 : ((10*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h95 : base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) (r+p-1) < base3 ((3 * r + 9) / 20) r p r ((3*p)-1))
    (h97 : base3 ((3 * r + 9) / 20) r p (3*p+1) (((10*p+2)/3)-1) ≤ base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) (r+p-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp1_10 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : 2 * p < r)
    (h71 : 7 * p + 2 < 3 * r)
    (h88 : 8 * p + 2 ≤ 3 * r)
    (h89 : 3 * p < r)
    (h98 : (r + 2 * ((3 * r + 9) / 20)) ≤ (4*p+1))
    (h99 : r ≤ 4 * p)
    (h100 : 3 * r ≤ 10 * p + 2)
    (h101 : 9 * p + 2 ≤ 3 * r)
    (h102 : 3 * r < 10 * p + 2)
    (h103 : r < ((10*p+2)/3))
    (h104 : ((10*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h105 : base3 ((3 * r + 9) / 20) r p r (((10*p+2)/3)-1) ≤ base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) ((4*p)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp1_11 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : 2 * p < r)
    (h71 : 7 * p + 2 < 3 * r)
    (h88 : 8 * p + 2 ≤ 3 * r)
    (h89 : 3 * p < r)
    (h98 : (4*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h106 : r ≤ 4 * p)
    (h107 : 3 * r ≤ 10 * p + 2)
    (h108 : 9 * p + 2 ≤ 3 * r)
    (h109 : 3 * r < 10 * p + 2)
    (h110 : r < ((10*p+2)/3))
    (h111 : ((10*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h112 : base3 ((3 * r + 9) / 20) r p r (((10*p+2)/3)-1) ≤ base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) ((4*p)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp1_12 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : 2 * p < r)
    (h71 : 7 * p + 2 < 3 * r)
    (h88 : 8 * p + 2 ≤ 3 * r)
    (h89 : 3 * p < r)
    (h98 : (4*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h106 : r ≤ 4 * p)
    (h107 : 3 * r ≤ 10 * p + 2)
    (h108 : 9 * p + 2 ≤ 3 * r)
    (h109 : 3 * r < 10 * p + 2)
    (h110 : r < ((10*p+2)/3))
    (h111 : ((10*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h112 : base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) ((4*p)-1) < base3 ((3 * r + 9) / 20) r p r (((10*p+2)/3)-1))
    (h113 : base3 ((3 * r + 9) / 20) r p (4*p+1) (r+p-1) < base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) ((4*p)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

theorem sub1_13 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : 2 * p < r)
    (h71 : 7 * p + 2 < 3 * r)
    (h88 : 8 * p + 2 ≤ 3 * r) :
    ∃ i, RegOf i r p := by
  rcases le_or_gt (r) (3 * p) with h89 | h89
  · rcases le_or_gt (3 * r) (10 * p + 2) with h90 | h90
    · rcases le_or_gt (9 * p + 2) (3 * r) with h91 | h91
      · exfalso; omega
      · rcases le_or_gt ((3*p)) (r) with h92 | h92
        · exfalso; omega
        · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((3*p+1)) with h93 | h93
          · exfalso; omega
          · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((10*p+2)/3)) with h94 | h94
            · exfalso; omega
            · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r ((3*p)-1)) (base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) (r+p-1)) with h95 | h95
              · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r ((3*p)-1)) (base3 ((3 * r + 9) / 20) r p (3*p+1) (((10*p+2)/3)-1)) with h96 | h96
                · exact ⟨19, show F19.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h44, h89, h71, h90, h88, h91, h92, h93, h94, h96, h95⟩⟩
                · exact absurd (emp1_8 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h71 h88 h89 h90 h91 h92 h93 h94 h95 h96) id
              · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p (3*p+1) (((10*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) (r+p-1)) with h97 | h97
                · exact absurd (emp1_9 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h71 h88 h89 h90 h91 h92 h93 h94 h95 h97) id
                · exact ⟨20, show F20.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h44, h89, h71, h90, h88, h91, h92, h93, h94, h95, h97⟩⟩
    · exfalso; omega
  · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((4*p+1)) with h98 | h98
    · rcases le_or_gt (r) (4 * p) with h99 | h99
      · rcases le_or_gt (3 * r) (10 * p + 2) with h100 | h100
        · rcases le_or_gt (9 * p + 2) (3 * r) with h101 | h101
          · rcases le_or_gt (10 * p + 2) (3 * r) with h102 | h102
            · exfalso; omega
            · rcases le_or_gt (((10*p+2)/3)) (r) with h103 | h103
              · exfalso; omega
              · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((10*p+2)/3)) with h104 | h104
                · exfalso; omega
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((10*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) ((4*p)-1)) with h105 | h105
                  · exact absurd (emp1_10 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h71 h88 h89 h98 h99 h100 h101 h102 h103 h104 h105) id
                  · exact ⟨24, show F24.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h89, h99, h71, h100, h101, h102, h103, h104, h98, h105⟩⟩
          · exfalso; omega
        · exfalso; omega
      · exfalso; omega
    · rcases le_or_gt (r) (4 * p) with h106 | h106
      · rcases le_or_gt (3 * r) (10 * p + 2) with h107 | h107
        · rcases le_or_gt (9 * p + 2) (3 * r) with h108 | h108
          · rcases le_or_gt (10 * p + 2) (3 * r) with h109 | h109
            · exfalso; omega
            · rcases le_or_gt (((10*p+2)/3)) (r) with h110 | h110
              · exfalso; omega
              · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((10*p+2)/3)) with h111 | h111
                · exfalso; omega
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((10*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) ((4*p)-1)) with h112 | h112
                  · exact absurd (emp1_11 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h71 h88 h89 h98 h106 h107 h108 h109 h110 h111 h112) id
                  · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) ((4*p)-1)) (base3 ((3 * r + 9) / 20) r p (4*p+1) (r+p-1)) with h113 | h113
                    · exact ⟨25, show F25.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h89, h106, h71, h107, h108, h109, h110, h111, h98, h112, h113⟩⟩
                    · exact absurd (emp1_12 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h71 h88 h89 h98 h106 h107 h108 h109 h110 h111 h112 h113) id
          · exfalso; omega
        · exfalso; omega
      · exfalso; omega

set_option maxHeartbeats 1600000 in
theorem emp1_14 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : 2 * p < r)
    (h71 : 7 * p + 2 < 3 * r)
    (h88 : 3 * r < 8 * p + 2)
    (h114 : (r + 2 * ((3 * r + 9) / 20)) ≤ ((10*p+2)/3))
    (h115 : r ≤ 3 * p)
    (h116 : 3 * r ≤ 10 * p + 2)
    (h117 : 7 * p + 2 ≤ 3 * r)
    (h118 : r < (3*p))
    (h119 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h120 : base3 ((3 * r + 9) / 20) r p (3*p+1) (((10*p+2)/3)-1) < base3 ((3 * r + 9) / 20) r p r ((3*p)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp1_15 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : 2 * p < r)
    (h71 : 7 * p + 2 < 3 * r)
    (h88 : 3 * r < 8 * p + 2)
    (h114 : ((10*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h121 : r ≤ 3 * p)
    (h122 : 3 * r ≤ 10 * p + 2)
    (h123 : 7 * p + 2 ≤ 3 * r)
    (h124 : r < (3*p))
    (h125 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h126 : base3 ((3 * r + 9) / 20) r p r ((3*p)-1) ≤ base3 ((3 * r + 9) / 20) r p (3*p+1) (((10*p+2)/3)-1))
    (h127 : base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) (r+p-1) < base3 ((3 * r + 9) / 20) r p r ((3*p)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp1_16 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : 2 * p < r)
    (h71 : 7 * p + 2 < 3 * r)
    (h88 : 3 * r < 8 * p + 2)
    (h114 : ((10*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h121 : r ≤ 3 * p)
    (h122 : 3 * r ≤ 10 * p + 2)
    (h123 : 7 * p + 2 ≤ 3 * r)
    (h124 : r < (3*p))
    (h125 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h126 : base3 ((3 * r + 9) / 20) r p (3*p+1) (((10*p+2)/3)-1) < base3 ((3 * r + 9) / 20) r p r ((3*p)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

theorem sub1_17 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r)
    (h2 : ((4*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h24 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h44 : 2 * p < r) :
    ∃ i, RegOf i r p := by
  rcases le_or_gt (3 * r) (7 * p + 2) with h71 | h71
  · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((3*p+1)) with h72 | h72
    · rcases le_or_gt (r) (3 * p) with h73 | h73
      · rcases le_or_gt (3 * r) (4 * p + 2) with h74 | h74
        · exfalso; omega
        · rcases le_or_gt (6 * p + 2) (3 * r) with h75 | h75
          · rcases le_or_gt (7 * p + 2) (3 * r) with h76 | h76
            · exfalso; omega
            · rcases le_or_gt (((7*p+2)/3)) (r) with h77 | h77
              · exfalso; omega
              · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((7*p+2)/3)) with h78 | h78
                · exfalso; omega
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((7*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((7*p+2)/3) ((3*p)-1)) with h79 | h79
                  · exact ⟨21, show F21.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h44, h73, h74, h71, h75, h76, h77, h78, h72, h79⟩⟩
                  · exact ⟨22, show F22.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h44, h73, h74, h71, h75, h76, h77, h78, h72, h79⟩⟩
          · exfalso; omega
      · exfalso; omega
    · rcases le_or_gt (r) (3 * p) with h80 | h80
      · rcases le_or_gt (3 * r) (4 * p + 2) with h81 | h81
        · exfalso; omega
        · rcases le_or_gt (6 * p + 2) (3 * r) with h82 | h82
          · rcases le_or_gt (7 * p + 2) (3 * r) with h83 | h83
            · exfalso; omega
            · rcases le_or_gt (((7*p+2)/3)) (r) with h84 | h84
              · exfalso; omega
              · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((7*p+2)/3)) with h85 | h85
                · exfalso; omega
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((7*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((7*p+2)/3) ((3*p)-1)) with h86 | h86
                  · exact absurd (emp1_6 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h71 h72 h80 h81 h82 h83 h84 h85 h86) id
                  · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p ((7*p+2)/3) ((3*p)-1)) (base3 ((3 * r + 9) / 20) r p (3*p+1) (r+p-1)) with h87 | h87
                    · exact ⟨23, show F23.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h44, h80, h81, h71, h82, h83, h84, h85, h72, h86, h87⟩⟩
                    · exact absurd (emp1_7 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h71 h72 h80 h81 h82 h83 h84 h85 h86 h87) id
          · exfalso; omega
      · exfalso; omega
  · rcases le_or_gt (8 * p + 2) (3 * r) with h88 | h88
    · exact sub1_13 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h71 h88
    · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((10*p+2)/3)) with h114 | h114
      · rcases le_or_gt (r) (3 * p) with h115 | h115
        · rcases le_or_gt (3 * r) (10 * p + 2) with h116 | h116
          · rcases le_or_gt (7 * p + 2) (3 * r) with h117 | h117
            · rcases le_or_gt ((3*p)) (r) with h118 | h118
              · exfalso; omega
              · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((3*p+1)) with h119 | h119
                · exfalso; omega
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r ((3*p)-1)) (base3 ((3 * r + 9) / 20) r p (3*p+1) (((10*p+2)/3)-1)) with h120 | h120
                  · exact ⟨17, show F17.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h44, h115, h71, h116, h117, h88, h118, h119, h114, h120⟩⟩
                  · exact absurd (emp1_14 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h71 h88 h114 h115 h116 h117 h118 h119 h120) id
            · exfalso; omega
          · exfalso; omega
        · exfalso; omega
      · rcases le_or_gt (r) (3 * p) with h121 | h121
        · rcases le_or_gt (3 * r) (10 * p + 2) with h122 | h122
          · rcases le_or_gt (7 * p + 2) (3 * r) with h123 | h123
            · rcases le_or_gt ((3*p)) (r) with h124 | h124
              · exfalso; omega
              · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((3*p+1)) with h125 | h125
                · exfalso; omega
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r ((3*p)-1)) (base3 ((3 * r + 9) / 20) r p (3*p+1) (((10*p+2)/3)-1)) with h126 | h126
                  · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r ((3*p)-1)) (base3 ((3 * r + 9) / 20) r p ((10*p+2)/3) (r+p-1)) with h127 | h127
                    · exact ⟨18, show F18.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h44, h121, h71, h122, h123, h88, h124, h125, h114, h126, h127⟩⟩
                    · exact absurd (emp1_15 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h71 h88 h114 h121 h122 h123 h124 h125 h126 h127) id
                  · exact absurd (emp1_16 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44 h71 h88 h114 h121 h122 h123 h124 h125 h126) id
            · exfalso; omega
          · exfalso; omega
        · exfalso; omega

theorem sub1_18 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) (hr0 : 0 < r)
    (h1 : 2 * p + 2 ≤ 3 * r) :
    ∃ i, RegOf i r p := by
  rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((4*p+2)/3)) with h2 | h2
  · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((1*p+1)) with h3 | h3
    · rcases le_or_gt (r) (0 * p) with h4 | h4
      · exfalso; omega
      · rcases le_or_gt (r) (1 * p) with h5 | h5
        · rcases le_or_gt (3 * r) (1 * p + 2) with h6 | h6
          · exfalso; omega
          · rcases le_or_gt (3 * r) (4 * p + 2) with h7 | h7
            · rcases le_or_gt (3 * p + 2) (3 * r) with h8 | h8
              · exfalso; omega
              · rcases le_or_gt ((1*p)) (r) with h9 | h9
                · exfalso; omega
                · exact ⟨4, show F4.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h4, h5, h6, h7, h1, h8, h9, h3, h2⟩⟩
            · exfalso; omega
        · exfalso; omega
    · rcases le_or_gt (r) (1 * p) with h10 | h10
      · rcases le_or_gt (r) (0 * p) with h11 | h11
        · exfalso; omega
        · rcases le_or_gt (3 * r) (1 * p + 2) with h12 | h12
          · exfalso; omega
          · rcases le_or_gt (3 * r) (4 * p + 2) with h13 | h13
            · rcases le_or_gt (3 * p + 2) (3 * r) with h14 | h14
              · exfalso; omega
              · rcases le_or_gt ((1*p)) (r) with h15 | h15
                · exfalso; omega
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r ((1*p)-1)) (base3 ((3 * r + 9) / 20) r p (1*p+1) (((4*p+2)/3)-1)) with h16 | h16
                  · exact ⟨5, show F5.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h11, h10, h12, h13, h1, h14, h15, h3, h2, h16⟩⟩
                  · exact ⟨6, show F6.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h11, h10, h12, h13, h1, h14, h15, h3, h2, h16⟩⟩
            · exfalso; omega
      · rcases le_or_gt (r) (2 * p) with h17 | h17
        · rcases le_or_gt (3 * r) (1 * p + 2) with h18 | h18
          · exfalso; omega
          · rcases le_or_gt (3 * r) (4 * p + 2) with h19 | h19
            · rcases le_or_gt (3 * p + 2) (3 * r) with h20 | h20
              · rcases le_or_gt (4 * p + 2) (3 * r) with h21 | h21
                · exfalso; omega
                · rcases le_or_gt (((4*p+2)/3)) (r) with h22 | h22
                  · exfalso; omega
                  · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((2*p+1)) with h23 | h23
                    · exact ⟨7, show F7.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h10, h17, h18, h19, h20, h21, h22, h2, h23⟩⟩
                    · exfalso; omega
              · exfalso; omega
            · exfalso; omega
        · exfalso; omega
  · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((2*p+1)) with h24 | h24
    · rcases le_or_gt (4 * p + 2) (3 * r) with h25 | h25
      · rcases le_or_gt (3 * r) (4 * p + 2) with h26 | h26
        · rcases le_or_gt (r) (1 * p) with h27 | h27
          · exfalso; omega
          · rcases le_or_gt (r) (2 * p) with h28 | h28
            · rcases le_or_gt (3 * r) (1 * p + 2) with h29 | h29
              · exfalso; omega
              · rcases le_or_gt (((4*p+2)/3)) (r) with h30 | h30
                · exact ⟨10, show F10.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h27, h28, h29, h26, h30, h2, h24⟩⟩
                · exfalso; omega
            · exfalso; omega
        · rcases le_or_gt (r) (1 * p) with h31 | h31
          · exfalso; omega
          · rcases le_or_gt (r) (2 * p) with h32 | h32
            · rcases le_or_gt (3 * r) (7 * p + 2) with h33 | h33
              · rcases le_or_gt (5 * p + 2) (3 * r) with h34 | h34
                · exfalso; omega
                · rcases le_or_gt ((2*p)) (r) with h35 | h35
                  · exfalso; omega
                  · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((7*p+2)/3)) with h36 | h36
                    · exact ⟨11, show F11.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h31, h32, h26, h33, h25, h34, h35, h24, h36⟩⟩
                    · exfalso; omega
              · exfalso; omega
            · exfalso; omega
      · rcases le_or_gt (r) (1 * p) with h37 | h37
        · exfalso; omega
        · rcases le_or_gt (r) (2 * p) with h38 | h38
          · rcases le_or_gt (3 * r) (1 * p + 2) with h39 | h39
            · exfalso; omega
            · rcases le_or_gt (3 * r) (4 * p + 2) with h40 | h40
              · rcases le_or_gt (3 * p + 2) (3 * r) with h41 | h41
                · rcases le_or_gt (((4*p+2)/3)) (r) with h42 | h42
                  · exfalso; omega
                  · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((4*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((4*p+2)/3) ((2*p)-1)) with h43 | h43
                    · exact ⟨8, show F8.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h37, h38, h39, h40, h41, h25, h42, h2, h24, h43⟩⟩
                    · exact ⟨9, show F9.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h37, h38, h39, h40, h41, h25, h42, h2, h24, h43⟩⟩
                · exfalso; omega
              · exfalso; omega
          · exfalso; omega
    · rcases le_or_gt (r) (2 * p) with h44 | h44
      · exact sub1_5 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44
      · exact sub1_17 hr hp2 hlo hhi hp60 hp3 hr0 h1 h2 h24 h44

/-- Coverage of the thirds band by the families, residue class `p ≡ 1 (3)`. -/
theorem cover_rho1 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 1) : ∃ i, RegOf i r p := by
  have hr0 : 0 < r := by omega
  rcases le_or_gt (2 * p + 2) (3 * r) with h1 | h1
  · exact sub1_18 hr hp2 hlo hhi hp60 hp3 hr0 h1
  · rcases le_or_gt (3 * r) (1 * p + 2) with h128 | h128
    · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((1*p+2)/3)) with h129 | h129
      · rcases le_or_gt (r) (0 * p) with h130 | h130
        · exfalso; omega
        · rcases le_or_gt (r) (1 * p) with h131 | h131
          · rcases le_or_gt (0 * p + 2) (3 * r) with h132 | h132
            · rcases le_or_gt (1 * p + 2) (3 * r) with h133 | h133
              · exfalso; omega
              · rcases le_or_gt (((1*p+2)/3)) (r) with h134 | h134
                · exfalso; omega
                · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((1*p+1)) with h135 | h135
                  · exact ⟨0, show F0.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h130, h131, hr0, h128, h132, h133, h134, h129, h135⟩⟩
                  · exfalso; omega
            · exfalso; omega
          · exfalso; omega
      · rcases le_or_gt (r) (0 * p) with h136 | h136
        · exfalso; omega
        · rcases le_or_gt (r) (1 * p) with h137 | h137
          · rcases le_or_gt (0 * p + 2) (3 * r) with h138 | h138
            · rcases le_or_gt (1 * p + 2) (3 * r) with h139 | h139
              · exfalso; omega
              · rcases le_or_gt (((1*p+2)/3)) (r) with h140 | h140
                · exfalso; omega
                · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((1*p+1)) with h141 | h141
                  · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((1*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((1*p+2)/3) ((1*p)-1)) with h142 | h142
                    · exact ⟨1, show F1.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h136, h137, hr0, h128, h138, h139, h140, h129, h141, h142⟩⟩
                    · exact ⟨2, show F2.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h136, h137, hr0, h128, h138, h139, h140, h129, h141, h142⟩⟩
                  · exfalso; omega
            · exfalso; omega
          · exfalso; omega
    · rcases le_or_gt (r) (0 * p) with h143 | h143
      · exfalso; omega
      · rcases le_or_gt (r) (1 * p) with h144 | h144
        · rcases le_or_gt (3 * r) (4 * p + 2) with h145 | h145
          · rcases le_or_gt (1 * p + 2) (3 * r) with h146 | h146
            · rcases le_or_gt ((1*p)) (r) with h147 | h147
              · exfalso; omega
              · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((1*p+1)) with h148 | h148
                · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((4*p+2)/3)) with h149 | h149
                  · exact ⟨3, show F3.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h143, h144, h128, h145, h146, h1, h147, h148, h149⟩⟩
                  · exfalso; omega
                · exfalso; omega
            · exfalso; omega
          · exfalso; omega
        · exfalso; omega

end CatalanCore.Uniform.Content.UFFamily4
