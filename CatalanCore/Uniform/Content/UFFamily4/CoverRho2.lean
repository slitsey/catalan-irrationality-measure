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

theorem sub2_19 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : r ≤ 1 * p) :
    ∃ i, RegOf i r p := by
  rcases le_or_gt (3 * r) (2 * p + 2) with h165 | h165
  · rcases le_or_gt (2 * p + 2) (3 * r) with h166 | h166
    · rcases le_or_gt (r) (0 * p) with h167 | h167
      · exfalso; omega
      · rcases le_or_gt (((2*p+2)/3)) (r) with h168 | h168
        · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((1*p+1)) with h169 | h169
          · exact ⟨30, show F30.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h167, h164, hr0, h165, h168, h150, h169⟩⟩
          · exfalso; omega
        · exfalso; omega
    · rcases le_or_gt (r) (0 * p) with h170 | h170
      · exfalso; omega
      · rcases le_or_gt (1 * p + 2) (3 * r) with h171 | h171
        · rcases le_or_gt (((2*p+2)/3)) (r) with h172 | h172
          · exfalso; omega
          · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((1*p+1)) with h173 | h173
            · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((2*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((2*p+2)/3) ((1*p)-1)) with h174 | h174
              · exact ⟨28, show F28.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h170, h164, hr0, h165, h171, h166, h172, h150, h173, h174⟩⟩
              · exact ⟨29, show F29.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h170, h164, hr0, h165, h171, h166, h172, h150, h173, h174⟩⟩
            · exfalso; omega
        · exfalso; omega
  · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((1*p+1)) with h175 | h175
    · rcases le_or_gt (r) (0 * p) with h176 | h176
      · exfalso; omega
      · rcases le_or_gt (3 * r) (5 * p + 2) with h177 | h177
        · rcases le_or_gt (2 * p + 2) (3 * r) with h178 | h178
          · rcases le_or_gt (3 * p + 2) (3 * r) with h179 | h179
            · exfalso; omega
            · rcases le_or_gt ((1*p)) (r) with h180 | h180
              · exfalso; omega
              · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((5*p+2)/3)) with h181 | h181
                · exact ⟨31, show F31.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h176, h164, h165, h177, h178, h179, h180, h175, h181⟩⟩
                · exfalso; omega
          · exfalso; omega
        · exfalso; omega
    · rcases le_or_gt (r) (0 * p) with h182 | h182
      · exfalso; omega
      · rcases le_or_gt (3 * r) (5 * p + 2) with h183 | h183
        · rcases le_or_gt (2 * p + 2) (3 * r) with h184 | h184
          · rcases le_or_gt (3 * p + 2) (3 * r) with h185 | h185
            · exfalso; omega
            · rcases le_or_gt ((1*p)) (r) with h186 | h186
              · exfalso; omega
              · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((5*p+2)/3)) with h187 | h187
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r ((1*p)-1)) (base3 ((3 * r + 9) / 20) r p (1*p+1) (((5*p+2)/3)-1)) with h188 | h188
                  · exact ⟨32, show F32.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h182, h164, h165, h183, h184, h185, h186, h175, h187, h188⟩⟩
                  · exact ⟨33, show F33.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h182, h164, h165, h183, h184, h185, h186, h175, h187, h188⟩⟩
                · exfalso; omega
          · exfalso; omega
        · exfalso; omega

set_option maxHeartbeats 1600000 in
theorem emp2_20 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (r + 2 * ((3 * r + 9) / 20)) ≤ (2*p+1))
    (h190 : ((5*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h197 : 3 * r < 4 * p + 2)
    (h204 : r ≤ 2 * p)
    (h205 : 2 * p + 2 < 3 * r)
    (h206 : 3 * r ≤ 5 * p + 2)
    (h207 : 3 * p + 2 ≤ 3 * r)
    (h208 : r < ((5*p+2)/3))
    (h209 : base3 ((3 * r + 9) / 20) r p ((5*p+2)/3) ((2*p)-1) < base3 ((3 * r + 9) / 20) r p r (((5*p+2)/3)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp2_21 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : (r + 2 * ((3 * r + 9) / 20)) ≤ ((8*p+2)/3))
    (h211 : 3 * r ≤ 5 * p + 2)
    (h212 : r ≤ 2 * p)
    (h213 : 2 * p + 2 < 3 * r)
    (h214 : 4 * p + 2 ≤ 3 * r)
    (h215 : 3 * r < 5 * p + 2)
    (h216 : r < ((5*p+2)/3))
    (h217 : ((5*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h218 : base3 ((3 * r + 9) / 20) r p r (((5*p+2)/3)-1) ≤ base3 ((3 * r + 9) / 20) r p ((5*p+2)/3) ((2*p)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp2_22 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : (r + 2 * ((3 * r + 9) / 20)) ≤ ((8*p+2)/3))
    (h211 : 3 * r ≤ 5 * p + 2)
    (h212 : r ≤ 2 * p)
    (h213 : 2 * p + 2 < 3 * r)
    (h214 : 4 * p + 2 ≤ 3 * r)
    (h215 : 3 * r < 5 * p + 2)
    (h216 : r < ((5*p+2)/3))
    (h217 : ((5*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h218 : base3 ((3 * r + 9) / 20) r p ((5*p+2)/3) ((2*p)-1) < base3 ((3 * r + 9) / 20) r p r (((5*p+2)/3)-1))
    (h219 : base3 ((3 * r + 9) / 20) r p (2*p+1) (r+p-1) < base3 ((3 * r + 9) / 20) r p ((5*p+2)/3) ((2*p)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

theorem sub2_23 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : (r + 2 * ((3 * r + 9) / 20)) ≤ ((8*p+2)/3)) :
    ∃ i, RegOf i r p := by
  rcases le_or_gt (3 * r) (5 * p + 2) with h211 | h211
  · rcases le_or_gt (r) (2 * p) with h212 | h212
    · rcases le_or_gt (3 * r) (2 * p + 2) with h213 | h213
      · exfalso; omega
      · rcases le_or_gt (4 * p + 2) (3 * r) with h214 | h214
        · rcases le_or_gt (5 * p + 2) (3 * r) with h215 | h215
          · exfalso; omega
          · rcases le_or_gt (((5*p+2)/3)) (r) with h216 | h216
            · exfalso; omega
            · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((5*p+2)/3)) with h217 | h217
              · exfalso; omega
              · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((5*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((5*p+2)/3) ((2*p)-1)) with h218 | h218
                · exact absurd (emp2_21 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h211 h212 h213 h214 h215 h216 h217 h218) id
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p ((5*p+2)/3) ((2*p)-1)) (base3 ((3 * r + 9) / 20) r p (2*p+1) (r+p-1)) with h219 | h219
                  · exact ⟨38, show F38.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h164, h212, h213, h211, h214, h215, h216, h217, h189, h218, h219⟩⟩
                  · exact absurd (emp2_22 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h211 h212 h213 h214 h215 h216 h217 h218 h219) id
        · exfalso; omega
    · exfalso; omega
  · rcases le_or_gt ((2*p)) (r) with h220 | h220
    · rcases le_or_gt (r) (2 * p) with h221 | h221
      · rcases le_or_gt (3 * r) (8 * p + 2) with h222 | h222
        · exact ⟨41, show F41.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h164, h221, h211, h222, h220, h189, h210⟩⟩
        · exfalso; omega
      · rcases le_or_gt (r) (3 * p) with h223 | h223
        · rcases le_or_gt (3 * r) (8 * p + 2) with h224 | h224
          · rcases le_or_gt (6 * p + 2) (3 * r) with h225 | h225
            · rcases le_or_gt (7 * p + 2) (3 * r) with h226 | h226
              · exfalso; omega
              · rcases le_or_gt (((8*p+2)/3)) (r) with h227 | h227
                · exfalso; omega
                · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((3*p+1)) with h228 | h228
                  · exact ⟨44, show F44.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h221, h223, h211, h224, h225, h226, h227, h210, h228⟩⟩
                  · exfalso; omega
            · exfalso; omega
          · exfalso; omega
        · exfalso; omega
    · rcases le_or_gt (r) (2 * p) with h229 | h229
      · rcases le_or_gt (3 * r) (8 * p + 2) with h230 | h230
        · rcases le_or_gt (5 * p + 2) (3 * r) with h231 | h231
          · rcases le_or_gt (6 * p + 2) (3 * r) with h232 | h232
            · exfalso; omega
            · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r ((2*p)-1)) (base3 ((3 * r + 9) / 20) r p (2*p+1) (((8*p+2)/3)-1)) with h233 | h233
              · exact ⟨39, show F39.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h164, h229, h211, h230, h231, h232, h220, h189, h210, h233⟩⟩
              · exact ⟨40, show F40.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h164, h229, h211, h230, h231, h232, h220, h189, h210, h233⟩⟩
          · exfalso; omega
        · exfalso; omega
      · exfalso; omega

set_option maxHeartbeats 1600000 in
theorem emp2_24 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : ((8*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h234 : ((8*p+2)/3) ≤ r)
    (h235 : r ≤ 3 * p)
    (h236 : (r + 2 * ((3 * r + 9) / 20)) ≤ ((11*p+2)/3))
    (h237 : 3 * r ≤ 8 * p + 2)
    (h238 : 2 * p < r)
    (h239 : 5 * p + 2 < 3 * r)
    (h240 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h241 : base3 ((3 * r + 9) / 20) r p ((8*p+2)/3) ((3*p)-1) ≤ base3 ((3 * r + 9) / 20) r p (3*p+1) (r+p-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp2_25 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : ((8*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h234 : ((8*p+2)/3) ≤ r)
    (h235 : r ≤ 3 * p)
    (h236 : (r + 2 * ((3 * r + 9) / 20)) ≤ ((11*p+2)/3))
    (h237 : 8 * p + 2 < 3 * r)
    (h242 : 2 * p < r)
    (h243 : 3 * r ≤ 11 * p + 2)
    (h244 : 8 * p + 2 ≤ 3 * r)
    (h245 : 3 * r < 9 * p + 2)
    (h246 : r < (3*p))
    (h247 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h248 : base3 ((3 * r + 9) / 20) r p r ((3*p)-1) ≤ base3 ((3 * r + 9) / 20) r p (3*p+1) (((11*p+2)/3)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp2_26 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : ((8*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h234 : ((8*p+2)/3) ≤ r)
    (h235 : r ≤ 3 * p)
    (h236 : ((11*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h249 : 2 * p < r)
    (h250 : 8 * p + 2 < 3 * r)
    (h251 : 3 * r ≤ 11 * p + 2)
    (h252 : 8 * p + 2 ≤ 3 * r)
    (h253 : 3 * r < 9 * p + 2)
    (h254 : r < (3*p))
    (h255 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h256 : base3 ((3 * r + 9) / 20) r p r ((3*p)-1) ≤ base3 ((3 * r + 9) / 20) r p (3*p+1) (((11*p+2)/3)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp2_27 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : ((8*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h234 : ((8*p+2)/3) ≤ r)
    (h235 : r ≤ 3 * p)
    (h236 : ((11*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h249 : 2 * p < r)
    (h250 : 8 * p + 2 < 3 * r)
    (h251 : 3 * r ≤ 11 * p + 2)
    (h252 : 8 * p + 2 ≤ 3 * r)
    (h253 : 3 * r < 9 * p + 2)
    (h254 : r < (3*p))
    (h255 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h256 : base3 ((3 * r + 9) / 20) r p (3*p+1) (((11*p+2)/3)-1) < base3 ((3 * r + 9) / 20) r p r ((3*p)-1))
    (h257 : base3 ((3 * r + 9) / 20) r p ((11*p+2)/3) (r+p-1) < base3 ((3 * r + 9) / 20) r p (3*p+1) (((11*p+2)/3)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp2_28 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : ((8*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h234 : ((8*p+2)/3) ≤ r)
    (h235 : 3 * p < r)
    (h258 : (r + 2 * ((3 * r + 9) / 20)) ≤ (4*p+1))
    (h259 : r ≤ 4 * p)
    (h260 : 8 * p + 2 < 3 * r)
    (h261 : 3 * r ≤ 11 * p + 2)
    (h262 : 9 * p + 2 ≤ 3 * r)
    (h263 : 3 * r < 10 * p + 2)
    (h264 : r < ((11*p+2)/3))
    (h265 : ((11*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h266 : base3 ((3 * r + 9) / 20) r p ((11*p+2)/3) ((4*p)-1) < base3 ((3 * r + 9) / 20) r p r (((11*p+2)/3)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp2_29 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : ((8*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h234 : ((8*p+2)/3) ≤ r)
    (h235 : 3 * p < r)
    (h258 : (4*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h267 : r ≤ 4 * p)
    (h268 : 8 * p + 2 < 3 * r)
    (h269 : 3 * r ≤ 11 * p + 2)
    (h270 : 9 * p + 2 ≤ 3 * r)
    (h271 : 3 * r < 10 * p + 2)
    (h272 : r < ((11*p+2)/3))
    (h273 : ((11*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h274 : base3 ((3 * r + 9) / 20) r p r (((11*p+2)/3)-1) ≤ base3 ((3 * r + 9) / 20) r p ((11*p+2)/3) ((4*p)-1))
    (h275 : base3 ((3 * r + 9) / 20) r p (4*p+1) (r+p-1) < base3 ((3 * r + 9) / 20) r p r (((11*p+2)/3)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp2_30 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : ((8*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h234 : ((8*p+2)/3) ≤ r)
    (h235 : 3 * p < r)
    (h258 : (4*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h267 : r ≤ 4 * p)
    (h268 : 8 * p + 2 < 3 * r)
    (h269 : 3 * r ≤ 11 * p + 2)
    (h270 : 9 * p + 2 ≤ 3 * r)
    (h271 : 3 * r < 10 * p + 2)
    (h272 : r < ((11*p+2)/3))
    (h273 : ((11*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h274 : base3 ((3 * r + 9) / 20) r p ((11*p+2)/3) ((4*p)-1) < base3 ((3 * r + 9) / 20) r p r (((11*p+2)/3)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

theorem sub2_31 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : ((8*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h234 : ((8*p+2)/3) ≤ r) :
    ∃ i, RegOf i r p := by
  rcases le_or_gt (r) (3 * p) with h235 | h235
  · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((11*p+2)/3)) with h236 | h236
    · rcases le_or_gt (3 * r) (8 * p + 2) with h237 | h237
      · rcases le_or_gt (r) (2 * p) with h238 | h238
        · exfalso; omega
        · rcases le_or_gt (3 * r) (5 * p + 2) with h239 | h239
          · exfalso; omega
          · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((3*p+1)) with h240 | h240
            · exfalso; omega
            · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p ((8*p+2)/3) ((3*p)-1)) (base3 ((3 * r + 9) / 20) r p (3*p+1) (r+p-1)) with h241 | h241
              · exact absurd (emp2_24 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h234 h235 h236 h237 h238 h239 h240 h241) id
              · exact ⟨49, show F49.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h238, h235, h239, h237, h234, h210, h240, h241⟩⟩
      · rcases le_or_gt (r) (2 * p) with h242 | h242
        · exfalso; omega
        · rcases le_or_gt (3 * r) (11 * p + 2) with h243 | h243
          · rcases le_or_gt (8 * p + 2) (3 * r) with h244 | h244
            · rcases le_or_gt (9 * p + 2) (3 * r) with h245 | h245
              · exfalso; omega
              · rcases le_or_gt ((3*p)) (r) with h246 | h246
                · exfalso; omega
                · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((3*p+1)) with h247 | h247
                  · exfalso; omega
                  · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r ((3*p)-1)) (base3 ((3 * r + 9) / 20) r p (3*p+1) (((11*p+2)/3)-1)) with h248 | h248
                    · exact absurd (emp2_25 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h234 h235 h236 h237 h242 h243 h244 h245 h246 h247 h248) id
                    · exact ⟨42, show F42.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h242, h235, h237, h243, h244, h245, h246, h247, h236, h248⟩⟩
            · exfalso; omega
          · exfalso; omega
    · rcases le_or_gt (r) (2 * p) with h249 | h249
      · exfalso; omega
      · rcases le_or_gt (3 * r) (8 * p + 2) with h250 | h250
        · exfalso; omega
        · rcases le_or_gt (3 * r) (11 * p + 2) with h251 | h251
          · rcases le_or_gt (8 * p + 2) (3 * r) with h252 | h252
            · rcases le_or_gt (9 * p + 2) (3 * r) with h253 | h253
              · exfalso; omega
              · rcases le_or_gt ((3*p)) (r) with h254 | h254
                · exfalso; omega
                · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((3*p+1)) with h255 | h255
                  · exfalso; omega
                  · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r ((3*p)-1)) (base3 ((3 * r + 9) / 20) r p (3*p+1) (((11*p+2)/3)-1)) with h256 | h256
                    · exact absurd (emp2_26 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h234 h235 h236 h249 h250 h251 h252 h253 h254 h255 h256) id
                    · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p (3*p+1) (((11*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((11*p+2)/3) (r+p-1)) with h257 | h257
                      · exact ⟨43, show F43.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h249, h235, h250, h251, h252, h253, h254, h255, h236, h256, h257⟩⟩
                      · exact absurd (emp2_27 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h234 h235 h236 h249 h250 h251 h252 h253 h254 h255 h256 h257) id
            · exfalso; omega
          · exfalso; omega
  · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((4*p+1)) with h258 | h258
    · rcases le_or_gt (r) (4 * p) with h259 | h259
      · rcases le_or_gt (3 * r) (8 * p + 2) with h260 | h260
        · exfalso; omega
        · rcases le_or_gt (3 * r) (11 * p + 2) with h261 | h261
          · rcases le_or_gt (9 * p + 2) (3 * r) with h262 | h262
            · rcases le_or_gt (10 * p + 2) (3 * r) with h263 | h263
              · exfalso; omega
              · rcases le_or_gt (((11*p+2)/3)) (r) with h264 | h264
                · exfalso; omega
                · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((11*p+2)/3)) with h265 | h265
                  · exfalso; omega
                  · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((11*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((11*p+2)/3) ((4*p)-1)) with h266 | h266
                    · exact ⟨50, show F50.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h235, h259, h260, h261, h262, h263, h264, h265, h258, h266⟩⟩
                    · exact absurd (emp2_28 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h234 h235 h258 h259 h260 h261 h262 h263 h264 h265 h266) id
            · exfalso; omega
          · exfalso; omega
      · exfalso; omega
    · rcases le_or_gt (r) (4 * p) with h267 | h267
      · rcases le_or_gt (3 * r) (8 * p + 2) with h268 | h268
        · exfalso; omega
        · rcases le_or_gt (3 * r) (11 * p + 2) with h269 | h269
          · rcases le_or_gt (9 * p + 2) (3 * r) with h270 | h270
            · rcases le_or_gt (10 * p + 2) (3 * r) with h271 | h271
              · exfalso; omega
              · rcases le_or_gt (((11*p+2)/3)) (r) with h272 | h272
                · exfalso; omega
                · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((11*p+2)/3)) with h273 | h273
                  · exfalso; omega
                  · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((11*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((11*p+2)/3) ((4*p)-1)) with h274 | h274
                    · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((11*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p (4*p+1) (r+p-1)) with h275 | h275
                      · exact ⟨51, show F51.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h235, h267, h268, h269, h270, h271, h272, h273, h258, h274, h275⟩⟩
                      · exact absurd (emp2_29 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h234 h235 h258 h267 h268 h269 h270 h271 h272 h273 h274 h275) id
                    · exact absurd (emp2_30 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h234 h235 h258 h267 h268 h269 h270 h271 h272 h273 h274) id
            · exfalso; omega
          · exfalso; omega
      · exfalso; omega

set_option maxHeartbeats 1600000 in
theorem emp2_32 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : ((8*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h234 : r < ((8*p+2)/3))
    (h276 : (r + 2 * ((3 * r + 9) / 20)) ≤ (3*p+1))
    (h277 : 2 * p < r)
    (h278 : r ≤ 3 * p)
    (h279 : 5 * p + 2 < 3 * r)
    (h280 : 3 * r ≤ 8 * p + 2)
    (h281 : 6 * p + 2 ≤ 3 * r)
    (h282 : 3 * r < 7 * p + 2)
    (h283 : base3 ((3 * r + 9) / 20) r p ((8*p+2)/3) ((3*p)-1) < base3 ((3 * r + 9) / 20) r p r (((8*p+2)/3)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp2_33 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : ((8*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h234 : r < ((8*p+2)/3))
    (h276 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h284 : 7 * p + 2 ≤ 3 * r)
    (h285 : 2 * p < r)
    (h286 : r ≤ 3 * p)
    (h287 : 5 * p + 2 < 3 * r)
    (h288 : 3 * r ≤ 8 * p + 2)
    (h289 : 3 * r < 8 * p + 2)
    (h290 : base3 ((3 * r + 9) / 20) r p r (((8*p+2)/3)-1) ≤ base3 ((3 * r + 9) / 20) r p (3*p+1) (r+p-1))
    (h291 : base3 ((3 * r + 9) / 20) r p ((8*p+2)/3) ((3*p)-1) < base3 ((3 * r + 9) / 20) r p r (((8*p+2)/3)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp2_34 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : ((8*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h234 : r < ((8*p+2)/3))
    (h276 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h284 : 7 * p + 2 ≤ 3 * r)
    (h285 : 2 * p < r)
    (h286 : r ≤ 3 * p)
    (h287 : 5 * p + 2 < 3 * r)
    (h288 : 3 * r ≤ 8 * p + 2)
    (h289 : 3 * r < 8 * p + 2)
    (h290 : base3 ((3 * r + 9) / 20) r p (3*p+1) (r+p-1) < base3 ((3 * r + 9) / 20) r p r (((8*p+2)/3)-1))
    (h292 : base3 ((3 * r + 9) / 20) r p ((8*p+2)/3) ((3*p)-1) ≤ base3 ((3 * r + 9) / 20) r p (3*p+1) (r+p-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp2_35 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : ((8*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h234 : r < ((8*p+2)/3))
    (h276 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h284 : 3 * r < 7 * p + 2)
    (h293 : 2 * p < r)
    (h294 : r ≤ 3 * p)
    (h295 : 5 * p + 2 < 3 * r)
    (h296 : 3 * r ≤ 8 * p + 2)
    (h297 : 6 * p + 2 ≤ 3 * r)
    (h298 : base3 ((3 * r + 9) / 20) r p r (((8*p+2)/3)-1) ≤ base3 ((3 * r + 9) / 20) r p ((8*p+2)/3) ((3*p)-1))
    (h299 : base3 ((3 * r + 9) / 20) r p (3*p+1) (r+p-1) < base3 ((3 * r + 9) / 20) r p r (((8*p+2)/3)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

set_option maxHeartbeats 1600000 in
theorem emp2_36 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : ((8*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h234 : r < ((8*p+2)/3))
    (h276 : (3*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h284 : 3 * r < 7 * p + 2)
    (h293 : 2 * p < r)
    (h294 : r ≤ 3 * p)
    (h295 : 5 * p + 2 < 3 * r)
    (h296 : 3 * r ≤ 8 * p + 2)
    (h297 : 6 * p + 2 ≤ 3 * r)
    (h298 : base3 ((3 * r + 9) / 20) r p ((8*p+2)/3) ((3*p)-1) < base3 ((3 * r + 9) / 20) r p r (((8*p+2)/3)-1)) :
    False := by
  first | omega | (simp only [base3] at *; omega)

theorem sub2_37 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r)
    (h189 : (2*p+1) < (r + 2 * ((3 * r + 9) / 20)))
    (h210 : ((8*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h234 : r < ((8*p+2)/3)) :
    ∃ i, RegOf i r p := by
  rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((3*p+1)) with h276 | h276
  · rcases le_or_gt (r) (2 * p) with h277 | h277
    · exfalso; omega
    · rcases le_or_gt (r) (3 * p) with h278 | h278
      · rcases le_or_gt (3 * r) (5 * p + 2) with h279 | h279
        · exfalso; omega
        · rcases le_or_gt (3 * r) (8 * p + 2) with h280 | h280
          · rcases le_or_gt (6 * p + 2) (3 * r) with h281 | h281
            · rcases le_or_gt (7 * p + 2) (3 * r) with h282 | h282
              · exfalso; omega
              · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((8*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((8*p+2)/3) ((3*p)-1)) with h283 | h283
                · exact ⟨45, show F45.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h277, h278, h279, h280, h281, h282, h234, h210, h276, h283⟩⟩
                · exact absurd (emp2_32 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h234 h276 h277 h278 h279 h280 h281 h282 h283) id
            · exfalso; omega
          · exfalso; omega
      · exfalso; omega
  · rcases le_or_gt (7 * p + 2) (3 * r) with h284 | h284
    · rcases le_or_gt (r) (2 * p) with h285 | h285
      · exfalso; omega
      · rcases le_or_gt (r) (3 * p) with h286 | h286
        · rcases le_or_gt (3 * r) (5 * p + 2) with h287 | h287
          · exfalso; omega
          · rcases le_or_gt (3 * r) (8 * p + 2) with h288 | h288
            · rcases le_or_gt (8 * p + 2) (3 * r) with h289 | h289
              · exfalso; omega
              · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((8*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p (3*p+1) (r+p-1)) with h290 | h290
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((8*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((8*p+2)/3) ((3*p)-1)) with h291 | h291
                  · exact ⟨47, show F47.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h285, h286, h287, h288, h284, h289, h234, h210, h276, h291, h290⟩⟩
                  · exact absurd (emp2_33 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h234 h276 h284 h285 h286 h287 h288 h289 h290 h291) id
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p ((8*p+2)/3) ((3*p)-1)) (base3 ((3 * r + 9) / 20) r p (3*p+1) (r+p-1)) with h292 | h292
                  · exact absurd (emp2_34 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h234 h276 h284 h285 h286 h287 h288 h289 h290 h292) id
                  · exact ⟨48, show F48.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h285, h286, h287, h288, h284, h289, h234, h210, h276, h290, h292⟩⟩
            · exfalso; omega
        · exfalso; omega
    · rcases le_or_gt (r) (2 * p) with h293 | h293
      · exfalso; omega
      · rcases le_or_gt (r) (3 * p) with h294 | h294
        · rcases le_or_gt (3 * r) (5 * p + 2) with h295 | h295
          · exfalso; omega
          · rcases le_or_gt (3 * r) (8 * p + 2) with h296 | h296
            · rcases le_or_gt (6 * p + 2) (3 * r) with h297 | h297
              · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((8*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((8*p+2)/3) ((3*p)-1)) with h298 | h298
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((8*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p (3*p+1) (r+p-1)) with h299 | h299
                  · exact ⟨46, show F46.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h293, h294, h295, h296, h297, h284, h234, h210, h276, h298, h299⟩⟩
                  · exact absurd (emp2_35 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h234 h276 h284 h293 h294 h295 h296 h297 h298 h299) id
                · exact absurd (emp2_36 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h234 h276 h284 h293 h294 h295 h296 h297 h298) id
              · exfalso; omega
            · exfalso; omega
        · exfalso; omega

theorem sub2_38 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) (hr0 : 0 < r)
    (h150 : ((2*p+2)/3) < (r + 2 * ((3 * r + 9) / 20)))
    (h164 : 1 * p < r) :
    ∃ i, RegOf i r p := by
  rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((2*p+1)) with h189 | h189
  · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((5*p+2)/3)) with h190 | h190
    · rcases le_or_gt (r) (2 * p) with h191 | h191
      · rcases le_or_gt (3 * r) (2 * p + 2) with h192 | h192
        · exfalso; omega
        · rcases le_or_gt (3 * r) (5 * p + 2) with h193 | h193
          · rcases le_or_gt (3 * p + 2) (3 * r) with h194 | h194
            · rcases le_or_gt (4 * p + 2) (3 * r) with h195 | h195
              · exfalso; omega
              · rcases le_or_gt (((5*p+2)/3)) (r) with h196 | h196
                · exfalso; omega
                · exact ⟨34, show F34.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h164, h191, h192, h193, h194, h195, h196, h190, h189⟩⟩
            · exfalso; omega
          · exfalso; omega
      · exfalso; omega
    · rcases le_or_gt (4 * p + 2) (3 * r) with h197 | h197
      · rcases le_or_gt (r) (2 * p) with h198 | h198
        · rcases le_or_gt (3 * r) (2 * p + 2) with h199 | h199
          · exfalso; omega
          · rcases le_or_gt (3 * r) (5 * p + 2) with h200 | h200
            · rcases le_or_gt (5 * p + 2) (3 * r) with h201 | h201
              · exfalso; omega
              · rcases le_or_gt (((5*p+2)/3)) (r) with h202 | h202
                · exfalso; omega
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((5*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((5*p+2)/3) ((2*p)-1)) with h203 | h203
                  · exact ⟨36, show F36.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h164, h198, h199, h200, h197, h201, h202, h190, h189, h203⟩⟩
                  · exact ⟨37, show F37.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h164, h198, h199, h200, h197, h201, h202, h190, h189, h203⟩⟩
            · exfalso; omega
        · exfalso; omega
      · rcases le_or_gt (r) (2 * p) with h204 | h204
        · rcases le_or_gt (3 * r) (2 * p + 2) with h205 | h205
          · exfalso; omega
          · rcases le_or_gt (3 * r) (5 * p + 2) with h206 | h206
            · rcases le_or_gt (3 * p + 2) (3 * r) with h207 | h207
              · rcases le_or_gt (((5*p+2)/3)) (r) with h208 | h208
                · exfalso; omega
                · rcases le_or_gt (base3 ((3 * r + 9) / 20) r p r (((5*p+2)/3)-1)) (base3 ((3 * r + 9) / 20) r p ((5*p+2)/3) ((2*p)-1)) with h209 | h209
                  · exact ⟨35, show F35.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h164, h204, h205, h206, h207, h197, h208, h190, h189, h209⟩⟩
                  · exact absurd (emp2_20 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h190 h197 h204 h205 h206 h207 h208 h209) id
              · exfalso; omega
            · exfalso; omega
        · exfalso; omega
  · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((8*p+2)/3)) with h210 | h210
    · exact sub2_23 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210
    · rcases le_or_gt (((8*p+2)/3)) (r) with h234 | h234
      · exact sub2_31 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h234
      · exact sub2_37 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164 h189 h210 h234

/-- Coverage of the thirds band by the families, residue class `p ≡ 2 (3)`. -/
theorem cover_rho2 {r p : ℕ} (hr : r % 2 = 0) (hp2 : p % 2 = 1) (hlo : 3 * r < 10 * p)
    (hhi : 10 * p ≤ 39 * r) (hp60 : 60 ≤ p) (hp3 : p % 3 = 2) : ∃ i, RegOf i r p := by
  have hr0 : 0 < r := by omega
  rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) (((2*p+2)/3)) with h150 | h150
  · rcases le_or_gt (1 * p + 2) (3 * r) with h151 | h151
    · rcases le_or_gt (r) (0 * p) with h152 | h152
      · exfalso; omega
      · rcases le_or_gt (r) (1 * p) with h153 | h153
        · rcases le_or_gt (3 * r) (2 * p + 2) with h154 | h154
          · rcases le_or_gt (2 * p + 2) (3 * r) with h155 | h155
            · exfalso; omega
            · rcases le_or_gt (((2*p+2)/3)) (r) with h156 | h156
              · exfalso; omega
              · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((1*p+1)) with h157 | h157
                · exact ⟨27, show F27.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h152, h153, hr0, h154, h151, h155, h156, h150, h157⟩⟩
                · exfalso; omega
          · exfalso; omega
        · exfalso; omega
    · rcases le_or_gt (r) (0 * p) with h158 | h158
      · exfalso; omega
      · rcases le_or_gt (r) (1 * p) with h159 | h159
        · rcases le_or_gt (3 * r) (2 * p + 2) with h160 | h160
          · rcases le_or_gt (0 * p + 2) (3 * r) with h161 | h161
            · rcases le_or_gt (((2*p+2)/3)) (r) with h162 | h162
              · exfalso; omega
              · rcases le_or_gt ((r + 2 * ((3 * r + 9) / 20))) ((1*p+1)) with h163 | h163
                · exact ⟨26, show F26.Reg r p from ⟨hr, hp3, hlo, hhi, hp60, h158, h159, hr0, h160, h161, h151, h162, h150, h163⟩⟩
                · exfalso; omega
            · exfalso; omega
          · exfalso; omega
        · exfalso; omega
  · rcases le_or_gt (r) (1 * p) with h164 | h164
    · exact sub2_19 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164
    · exact sub2_38 hr hp2 hlo hhi hp60 hp3 hr0 h150 h164

end CatalanCore.Uniform.Content.UFFamily4
