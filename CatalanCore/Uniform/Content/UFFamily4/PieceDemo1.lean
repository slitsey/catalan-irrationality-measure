module

public import CatalanCore.Uniform.Content.UFFamily4.Piece

@[expose] public section

open CatalanCore CatalanCore.Uniform.Content.UFFamily3

namespace CatalanCore.Uniform.Content.UFFamily4

set_option maxHeartbeats 3200000 in
theorem piece_k3 :
    UFBound 0 (((3 : ℕ) : ℝ) / (10 : ℕ)) (((2 : ℕ) : ℝ) / (5 : ℕ))
      (((109 : ℤ) : ℝ) / (50 : ℕ)) (((0 : ℤ) : ℝ) / (50 : ℕ)) (((0 : ℤ) : ℝ) / (50 : ℕ)) :=
  ufbound_of_nat (by norm_num) (by norm_num) (by norm_num) (109) (0) (0) (by
    intro r p hr hb hs ht i hi
    obtain ⟨h60, hlo, hhi⟩ := hb
    match i, hi with
    | 0, hi =>
      have hi' : F0.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F0.T0, F0.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F0.T0, F0.TV, base3] at *; omega)
    | 1, hi =>
      have hi' : F1.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F1.T0, F1.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F1.T0, F1.TV, base3] at *; omega)
    | 2, hi =>
      have hi' : F2.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F2.T0, F2.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F2.T0, F2.TV, base3] at *; omega)
    | 3, hi =>
      have hi' : F3.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F3.T0, F3.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F3.T0, F3.TV, base3] at *; omega)
    | 4, hi =>
      have hi' : F4.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F4.T0, F4.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F4.T0, F4.TV, base3] at *; omega)
    | 5, hi =>
      have hi' : F5.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F5.T0, F5.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F5.T0, F5.TV, base3] at *; omega)
    | 6, hi =>
      have hi' : F6.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F6.T0, F6.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F6.T0, F6.TV, base3] at *; omega)
    | 7, hi =>
      have hi' : F7.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F7.T0, F7.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F7.T0, F7.TV, base3] at *; omega)
    | 8, hi =>
      have hi' : F8.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F8.T0, F8.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F8.T0, F8.TV, base3] at *; omega)
    | 9, hi =>
      have hi' : F9.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F9.T0, F9.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F9.T0, F9.TV, base3] at *; omega)
    | 10, hi =>
      have hi' : F10.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F10.T0, F10.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F10.T0, F10.TV, base3] at *; omega)
    | 11, hi =>
      have hi' : F11.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F11.T0, F11.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F11.T0, F11.TV, base3] at *; omega)
    | 12, hi =>
      have hi' : F12.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F12.T0, F12.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F12.T0, F12.TV, base3] at *; omega)
    | 13, hi =>
      have hi' : F13.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F13.T0, F13.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F13.T0, F13.TV, base3] at *; omega)
    | 14, hi =>
      have hi' : F14.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F14.T0, F14.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F14.T0, F14.TV, base3] at *; omega)
    | 15, hi =>
      have hi' : F15.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F15.T0, F15.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F15.T0, F15.TV, base3] at *; omega)
    | 16, hi =>
      have hi' : F16.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F16.T0, F16.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F16.T0, F16.TV, base3] at *; omega)
    | 17, hi =>
      have hi' : F17.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F17.T0, F17.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F17.T0, F17.TV, base3] at *; omega)
    | 18, hi =>
      have hi' : F18.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F18.T0, F18.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F18.T0, F18.TV, base3] at *; omega)
    | 19, hi =>
      have hi' : F19.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F19.T0, F19.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F19.T0, F19.TV, base3] at *; omega)
    | 20, hi =>
      have hi' : F20.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F20.T0, F20.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F20.T0, F20.TV, base3] at *; omega)
    | 21, hi =>
      have hi' : F21.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F21.T0, F21.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F21.T0, F21.TV, base3] at *; omega)
    | 22, hi =>
      have hi' : F22.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F22.T0, F22.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F22.T0, F22.TV, base3] at *; omega)
    | 23, hi =>
      have hi' : F23.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F23.T0, F23.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F23.T0, F23.TV, base3] at *; omega)
    | 24, hi =>
      have hi' : F24.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F24.T0, F24.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F24.T0, F24.TV, base3] at *; omega)
    | 25, hi =>
      have hi' : F25.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F25.T0, F25.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F25.T0, F25.TV, base3] at *; omega)
    | 26, hi =>
      have hi' : F26.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F26.T0, F26.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F26.T0, F26.TV, base3] at *; omega)
    | 27, hi =>
      have hi' : F27.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F27.T0, F27.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F27.T0, F27.TV, base3] at *; omega)
    | 28, hi =>
      have hi' : F28.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F28.T0, F28.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F28.T0, F28.TV, base3] at *; omega)
    | 29, hi =>
      have hi' : F29.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F29.T0, F29.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F29.T0, F29.TV, base3] at *; omega)
    | 30, hi =>
      have hi' : F30.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F30.T0, F30.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F30.T0, F30.TV, base3] at *; omega)
    | 31, hi =>
      have hi' : F31.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F31.T0, F31.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F31.T0, F31.TV, base3] at *; omega)
    | 32, hi =>
      have hi' : F32.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F32.T0, F32.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F32.T0, F32.TV, base3] at *; omega)
    | 33, hi =>
      have hi' : F33.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F33.T0, F33.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F33.T0, F33.TV, base3] at *; omega)
    | 34, hi =>
      have hi' : F34.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F34.T0, F34.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F34.T0, F34.TV, base3] at *; omega)
    | 35, hi =>
      have hi' : F35.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F35.T0, F35.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F35.T0, F35.TV, base3] at *; omega)
    | 36, hi =>
      have hi' : F36.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F36.T0, F36.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F36.T0, F36.TV, base3] at *; omega)
    | 37, hi =>
      have hi' : F37.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F37.T0, F37.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F37.T0, F37.TV, base3] at *; omega)
    | 38, hi =>
      have hi' : F38.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F38.T0, F38.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F38.T0, F38.TV, base3] at *; omega)
    | 39, hi =>
      have hi' : F39.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F39.T0, F39.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F39.T0, F39.TV, base3] at *; omega)
    | 40, hi =>
      have hi' : F40.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F40.T0, F40.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F40.T0, F40.TV, base3] at *; omega)
    | 41, hi =>
      have hi' : F41.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F41.T0, F41.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F41.T0, F41.TV, base3] at *; omega)
    | 42, hi =>
      have hi' : F42.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F42.T0, F42.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F42.T0, F42.TV, base3] at *; omega)
    | 43, hi =>
      have hi' : F43.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F43.T0, F43.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F43.T0, F43.TV, base3] at *; omega)
    | 44, hi =>
      have hi' : F44.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F44.T0, F44.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F44.T0, F44.TV, base3] at *; omega)
    | 45, hi =>
      have hi' : F45.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F45.T0, F45.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F45.T0, F45.TV, base3] at *; omega)
    | 46, hi =>
      have hi' : F46.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F46.T0, F46.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F46.T0, F46.TV, base3] at *; omega)
    | 47, hi =>
      have hi' : F47.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F47.T0, F47.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F47.T0, F47.TV, base3] at *; omega)
    | 48, hi =>
      have hi' : F48.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F48.T0, F48.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F48.T0, F48.TV, base3] at *; omega)
    | 49, hi =>
      have hi' : F49.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F49.T0, F49.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F49.T0, F49.TV, base3] at *; omega)
    | 50, hi =>
      have hi' : F50.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F50.T0, F50.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F50.T0, F50.TV, base3] at *; omega)
    | 51, hi =>
      have hi' : F51.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F51.T0, F51.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F51.T0, F51.TV, base3] at *; omega)
    | n + 52, hi => exact absurd hi (by simp [RegOf]))

set_option maxHeartbeats 3200000 in
theorem piece_k4 :
    UFBound 0 (((2 : ℕ) : ℝ) / (5 : ℕ)) (((1 : ℕ) : ℝ) / (2 : ℕ))
      (((109 : ℤ) : ℝ) / (50 : ℕ)) (((0 : ℤ) : ℝ) / (50 : ℕ)) (((0 : ℤ) : ℝ) / (50 : ℕ)) :=
  ufbound_of_nat (by norm_num) (by norm_num) (by norm_num) (109) (0) (0) (by
    intro r p hr hb hs ht i hi
    obtain ⟨h60, hlo, hhi⟩ := hb
    match i, hi with
    | 0, hi =>
      have hi' : F0.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F0.T0, F0.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F0.T0, F0.TV, base3] at *; omega)
    | 1, hi =>
      have hi' : F1.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F1.T0, F1.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F1.T0, F1.TV, base3] at *; omega)
    | 2, hi =>
      have hi' : F2.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F2.T0, F2.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F2.T0, F2.TV, base3] at *; omega)
    | 3, hi =>
      have hi' : F3.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F3.T0, F3.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F3.T0, F3.TV, base3] at *; omega)
    | 4, hi =>
      have hi' : F4.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F4.T0, F4.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F4.T0, F4.TV, base3] at *; omega)
    | 5, hi =>
      have hi' : F5.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F5.T0, F5.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F5.T0, F5.TV, base3] at *; omega)
    | 6, hi =>
      have hi' : F6.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F6.T0, F6.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F6.T0, F6.TV, base3] at *; omega)
    | 7, hi =>
      have hi' : F7.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F7.T0, F7.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F7.T0, F7.TV, base3] at *; omega)
    | 8, hi =>
      have hi' : F8.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F8.T0, F8.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F8.T0, F8.TV, base3] at *; omega)
    | 9, hi =>
      have hi' : F9.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F9.T0, F9.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F9.T0, F9.TV, base3] at *; omega)
    | 10, hi =>
      have hi' : F10.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F10.T0, F10.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F10.T0, F10.TV, base3] at *; omega)
    | 11, hi =>
      have hi' : F11.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F11.T0, F11.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F11.T0, F11.TV, base3] at *; omega)
    | 12, hi =>
      have hi' : F12.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F12.T0, F12.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F12.T0, F12.TV, base3] at *; omega)
    | 13, hi =>
      have hi' : F13.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F13.T0, F13.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F13.T0, F13.TV, base3] at *; omega)
    | 14, hi =>
      have hi' : F14.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F14.T0, F14.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F14.T0, F14.TV, base3] at *; omega)
    | 15, hi =>
      have hi' : F15.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F15.T0, F15.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F15.T0, F15.TV, base3] at *; omega)
    | 16, hi =>
      have hi' : F16.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F16.T0, F16.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F16.T0, F16.TV, base3] at *; omega)
    | 17, hi =>
      have hi' : F17.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F17.T0, F17.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F17.T0, F17.TV, base3] at *; omega)
    | 18, hi =>
      have hi' : F18.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F18.T0, F18.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F18.T0, F18.TV, base3] at *; omega)
    | 19, hi =>
      have hi' : F19.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F19.T0, F19.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F19.T0, F19.TV, base3] at *; omega)
    | 20, hi =>
      have hi' : F20.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F20.T0, F20.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F20.T0, F20.TV, base3] at *; omega)
    | 21, hi =>
      have hi' : F21.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F21.T0, F21.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F21.T0, F21.TV, base3] at *; omega)
    | 22, hi =>
      have hi' : F22.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F22.T0, F22.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F22.T0, F22.TV, base3] at *; omega)
    | 23, hi =>
      have hi' : F23.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F23.T0, F23.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F23.T0, F23.TV, base3] at *; omega)
    | 24, hi =>
      have hi' : F24.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F24.T0, F24.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F24.T0, F24.TV, base3] at *; omega)
    | 25, hi =>
      have hi' : F25.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F25.T0, F25.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F25.T0, F25.TV, base3] at *; omega)
    | 26, hi =>
      have hi' : F26.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F26.T0, F26.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F26.T0, F26.TV, base3] at *; omega)
    | 27, hi =>
      have hi' : F27.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F27.T0, F27.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F27.T0, F27.TV, base3] at *; omega)
    | 28, hi =>
      have hi' : F28.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F28.T0, F28.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F28.T0, F28.TV, base3] at *; omega)
    | 29, hi =>
      have hi' : F29.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F29.T0, F29.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F29.T0, F29.TV, base3] at *; omega)
    | 30, hi =>
      have hi' : F30.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F30.T0, F30.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F30.T0, F30.TV, base3] at *; omega)
    | 31, hi =>
      have hi' : F31.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F31.T0, F31.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F31.T0, F31.TV, base3] at *; omega)
    | 32, hi =>
      have hi' : F32.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F32.T0, F32.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F32.T0, F32.TV, base3] at *; omega)
    | 33, hi =>
      have hi' : F33.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F33.T0, F33.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F33.T0, F33.TV, base3] at *; omega)
    | 34, hi =>
      have hi' : F34.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F34.T0, F34.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F34.T0, F34.TV, base3] at *; omega)
    | 35, hi =>
      have hi' : F35.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F35.T0, F35.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F35.T0, F35.TV, base3] at *; omega)
    | 36, hi =>
      have hi' : F36.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F36.T0, F36.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F36.T0, F36.TV, base3] at *; omega)
    | 37, hi =>
      have hi' : F37.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F37.T0, F37.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F37.T0, F37.TV, base3] at *; omega)
    | 38, hi =>
      have hi' : F38.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F38.T0, F38.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F38.T0, F38.TV, base3] at *; omega)
    | 39, hi =>
      have hi' : F39.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F39.T0, F39.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F39.T0, F39.TV, base3] at *; omega)
    | 40, hi =>
      have hi' : F40.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F40.T0, F40.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F40.T0, F40.TV, base3] at *; omega)
    | 41, hi =>
      have hi' : F41.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F41.T0, F41.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F41.T0, F41.TV, base3] at *; omega)
    | 42, hi =>
      have hi' : F42.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F42.T0, F42.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F42.T0, F42.TV, base3] at *; omega)
    | 43, hi =>
      have hi' : F43.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F43.T0, F43.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F43.T0, F43.TV, base3] at *; omega)
    | 44, hi =>
      have hi' : F44.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F44.T0, F44.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F44.T0, F44.TV, base3] at *; omega)
    | 45, hi =>
      have hi' : F45.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F45.T0, F45.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F45.T0, F45.TV, base3] at *; omega)
    | 46, hi =>
      have hi' : F46.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F46.T0, F46.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F46.T0, F46.TV, base3] at *; omega)
    | 47, hi =>
      have hi' : F47.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F47.T0, F47.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F47.T0, F47.TV, base3] at *; omega)
    | 48, hi =>
      have hi' : F48.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F48.T0, F48.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F48.T0, F48.TV, base3] at *; omega)
    | 49, hi =>
      have hi' : F49.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F49.T0, F49.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F49.T0, F49.TV, base3] at *; omega)
    | 50, hi =>
      have hi' : F50.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F50.T0, F50.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F50.T0, F50.TV, base3] at *; omega)
    | 51, hi =>
      have hi' : F51.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F51.T0, F51.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F51.T0, F51.TV, base3] at *; omega)
    | n + 52, hi => exact absurd hi (by simp [RegOf]))

set_option maxHeartbeats 3200000 in
theorem piece_k5 :
    UFBound 0 (((1 : ℕ) : ℝ) / (2 : ℕ)) (((3 : ℕ) : ℝ) / (5 : ℕ))
      (((394 : ℤ) : ℝ) / (200 : ℕ)) (((75 : ℤ) : ℝ) / (200 : ℕ)) (((0 : ℤ) : ℝ) / (200 : ℕ)) :=
  ufbound_of_nat (by norm_num) (by norm_num) (by norm_num) (394) (75) (0) (by
    intro r p hr hb hs ht i hi
    obtain ⟨h60, hlo, hhi⟩ := hb
    match i, hi with
    | 0, hi =>
      have hi' : F0.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F0.T0, F0.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F0.T0, F0.TV, base3] at *; omega)
    | 1, hi =>
      have hi' : F1.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F1.T0, F1.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F1.T0, F1.TV, base3] at *; omega)
    | 2, hi =>
      have hi' : F2.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F2.T0, F2.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F2.T0, F2.TV, base3] at *; omega)
    | 3, hi =>
      have hi' : F3.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F3.T0, F3.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F3.T0, F3.TV, base3] at *; omega)
    | 4, hi =>
      have hi' : F4.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F4.T0, F4.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F4.T0, F4.TV, base3] at *; omega)
    | 5, hi =>
      have hi' : F5.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F5.T0, F5.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F5.T0, F5.TV, base3] at *; omega)
    | 6, hi =>
      have hi' : F6.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F6.T0, F6.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F6.T0, F6.TV, base3] at *; omega)
    | 7, hi =>
      have hi' : F7.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F7.T0, F7.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F7.T0, F7.TV, base3] at *; omega)
    | 8, hi =>
      have hi' : F8.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F8.T0, F8.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F8.T0, F8.TV, base3] at *; omega)
    | 9, hi =>
      have hi' : F9.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F9.T0, F9.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F9.T0, F9.TV, base3] at *; omega)
    | 10, hi =>
      have hi' : F10.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F10.T0, F10.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F10.T0, F10.TV, base3] at *; omega)
    | 11, hi =>
      have hi' : F11.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F11.T0, F11.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F11.T0, F11.TV, base3] at *; omega)
    | 12, hi =>
      have hi' : F12.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F12.T0, F12.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F12.T0, F12.TV, base3] at *; omega)
    | 13, hi =>
      have hi' : F13.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F13.T0, F13.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F13.T0, F13.TV, base3] at *; omega)
    | 14, hi =>
      have hi' : F14.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F14.T0, F14.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F14.T0, F14.TV, base3] at *; omega)
    | 15, hi =>
      have hi' : F15.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F15.T0, F15.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F15.T0, F15.TV, base3] at *; omega)
    | 16, hi =>
      have hi' : F16.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F16.T0, F16.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F16.T0, F16.TV, base3] at *; omega)
    | 17, hi =>
      have hi' : F17.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F17.T0, F17.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F17.T0, F17.TV, base3] at *; omega)
    | 18, hi =>
      have hi' : F18.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F18.T0, F18.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F18.T0, F18.TV, base3] at *; omega)
    | 19, hi =>
      have hi' : F19.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F19.T0, F19.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F19.T0, F19.TV, base3] at *; omega)
    | 20, hi =>
      have hi' : F20.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F20.T0, F20.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F20.T0, F20.TV, base3] at *; omega)
    | 21, hi =>
      have hi' : F21.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F21.T0, F21.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F21.T0, F21.TV, base3] at *; omega)
    | 22, hi =>
      have hi' : F22.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F22.T0, F22.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F22.T0, F22.TV, base3] at *; omega)
    | 23, hi =>
      have hi' : F23.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F23.T0, F23.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F23.T0, F23.TV, base3] at *; omega)
    | 24, hi =>
      have hi' : F24.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F24.T0, F24.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F24.T0, F24.TV, base3] at *; omega)
    | 25, hi =>
      have hi' : F25.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F25.T0, F25.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F25.T0, F25.TV, base3] at *; omega)
    | 26, hi =>
      have hi' : F26.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F26.T0, F26.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F26.T0, F26.TV, base3] at *; omega)
    | 27, hi =>
      have hi' : F27.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F27.T0, F27.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F27.T0, F27.TV, base3] at *; omega)
    | 28, hi =>
      have hi' : F28.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F28.T0, F28.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F28.T0, F28.TV, base3] at *; omega)
    | 29, hi =>
      have hi' : F29.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F29.T0, F29.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F29.T0, F29.TV, base3] at *; omega)
    | 30, hi =>
      have hi' : F30.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F30.T0, F30.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F30.T0, F30.TV, base3] at *; omega)
    | 31, hi =>
      have hi' : F31.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F31.T0, F31.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F31.T0, F31.TV, base3] at *; omega)
    | 32, hi =>
      have hi' : F32.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F32.T0, F32.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F32.T0, F32.TV, base3] at *; omega)
    | 33, hi =>
      have hi' : F33.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F33.T0, F33.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F33.T0, F33.TV, base3] at *; omega)
    | 34, hi =>
      have hi' : F34.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F34.T0, F34.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F34.T0, F34.TV, base3] at *; omega)
    | 35, hi =>
      have hi' : F35.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F35.T0, F35.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F35.T0, F35.TV, base3] at *; omega)
    | 36, hi =>
      have hi' : F36.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F36.T0, F36.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F36.T0, F36.TV, base3] at *; omega)
    | 37, hi =>
      have hi' : F37.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F37.T0, F37.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F37.T0, F37.TV, base3] at *; omega)
    | 38, hi =>
      have hi' : F38.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F38.T0, F38.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F38.T0, F38.TV, base3] at *; omega)
    | 39, hi =>
      have hi' : F39.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F39.T0, F39.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F39.T0, F39.TV, base3] at *; omega)
    | 40, hi =>
      have hi' : F40.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F40.T0, F40.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F40.T0, F40.TV, base3] at *; omega)
    | 41, hi =>
      have hi' : F41.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F41.T0, F41.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F41.T0, F41.TV, base3] at *; omega)
    | 42, hi =>
      have hi' : F42.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F42.T0, F42.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F42.T0, F42.TV, base3] at *; omega)
    | 43, hi =>
      have hi' : F43.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F43.T0, F43.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F43.T0, F43.TV, base3] at *; omega)
    | 44, hi =>
      have hi' : F44.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F44.T0, F44.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F44.T0, F44.TV, base3] at *; omega)
    | 45, hi =>
      have hi' : F45.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F45.T0, F45.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F45.T0, F45.TV, base3] at *; omega)
    | 46, hi =>
      have hi' : F46.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F46.T0, F46.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F46.T0, F46.TV, base3] at *; omega)
    | 47, hi =>
      have hi' : F47.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F47.T0, F47.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F47.T0, F47.TV, base3] at *; omega)
    | 48, hi =>
      have hi' : F48.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F48.T0, F48.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F48.T0, F48.TV, base3] at *; omega)
    | 49, hi =>
      have hi' : F49.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F49.T0, F49.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F49.T0, F49.TV, base3] at *; omega)
    | 50, hi =>
      have hi' : F50.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F50.T0, F50.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F50.T0, F50.TV, base3] at *; omega)
    | 51, hi =>
      have hi' : F51.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F51.T0, F51.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F51.T0, F51.TV, base3] at *; omega)
    | n + 52, hi => exact absurd hi (by simp [RegOf]))

set_option maxHeartbeats 3200000 in
theorem piece_k6 :
    UFBound 0 (((3 : ℕ) : ℝ) / (5 : ℕ)) (((7 : ℕ) : ℝ) / (10 : ℕ))
      (((183 : ℤ) : ℝ) / (100 : ℕ)) (((50 : ℤ) : ℝ) / (100 : ℕ)) (((0 : ℤ) : ℝ) / (100 : ℕ)) :=
  ufbound_of_nat (by norm_num) (by norm_num) (by norm_num) (183) (50) (0) (by
    intro r p hr hb hs ht i hi
    obtain ⟨h60, hlo, hhi⟩ := hb
    match i, hi with
    | 0, hi =>
      have hi' : F0.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F0.T0, F0.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F0.T0, F0.TV, base3] at *; omega)
    | 1, hi =>
      have hi' : F1.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F1.T0, F1.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F1.T0, F1.TV, base3] at *; omega)
    | 2, hi =>
      have hi' : F2.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F2.T0, F2.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F2.T0, F2.TV, base3] at *; omega)
    | 3, hi =>
      have hi' : F3.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F3.T0, F3.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F3.T0, F3.TV, base3] at *; omega)
    | 4, hi =>
      have hi' : F4.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F4.T0, F4.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F4.T0, F4.TV, base3] at *; omega)
    | 5, hi =>
      have hi' : F5.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F5.T0, F5.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F5.T0, F5.TV, base3] at *; omega)
    | 6, hi =>
      have hi' : F6.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F6.T0, F6.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F6.T0, F6.TV, base3] at *; omega)
    | 7, hi =>
      have hi' : F7.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F7.T0, F7.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F7.T0, F7.TV, base3] at *; omega)
    | 8, hi =>
      have hi' : F8.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F8.T0, F8.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F8.T0, F8.TV, base3] at *; omega)
    | 9, hi =>
      have hi' : F9.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F9.T0, F9.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F9.T0, F9.TV, base3] at *; omega)
    | 10, hi =>
      have hi' : F10.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F10.T0, F10.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F10.T0, F10.TV, base3] at *; omega)
    | 11, hi =>
      have hi' : F11.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F11.T0, F11.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F11.T0, F11.TV, base3] at *; omega)
    | 12, hi =>
      have hi' : F12.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F12.T0, F12.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F12.T0, F12.TV, base3] at *; omega)
    | 13, hi =>
      have hi' : F13.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F13.T0, F13.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F13.T0, F13.TV, base3] at *; omega)
    | 14, hi =>
      have hi' : F14.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F14.T0, F14.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F14.T0, F14.TV, base3] at *; omega)
    | 15, hi =>
      have hi' : F15.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F15.T0, F15.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F15.T0, F15.TV, base3] at *; omega)
    | 16, hi =>
      have hi' : F16.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F16.T0, F16.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F16.T0, F16.TV, base3] at *; omega)
    | 17, hi =>
      have hi' : F17.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F17.T0, F17.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F17.T0, F17.TV, base3] at *; omega)
    | 18, hi =>
      have hi' : F18.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F18.T0, F18.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F18.T0, F18.TV, base3] at *; omega)
    | 19, hi =>
      have hi' : F19.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F19.T0, F19.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F19.T0, F19.TV, base3] at *; omega)
    | 20, hi =>
      have hi' : F20.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F20.T0, F20.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F20.T0, F20.TV, base3] at *; omega)
    | 21, hi =>
      have hi' : F21.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F21.T0, F21.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F21.T0, F21.TV, base3] at *; omega)
    | 22, hi =>
      have hi' : F22.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F22.T0, F22.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F22.T0, F22.TV, base3] at *; omega)
    | 23, hi =>
      have hi' : F23.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F23.T0, F23.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F23.T0, F23.TV, base3] at *; omega)
    | 24, hi =>
      have hi' : F24.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F24.T0, F24.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F24.T0, F24.TV, base3] at *; omega)
    | 25, hi =>
      have hi' : F25.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F25.T0, F25.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F25.T0, F25.TV, base3] at *; omega)
    | 26, hi =>
      have hi' : F26.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F26.T0, F26.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F26.T0, F26.TV, base3] at *; omega)
    | 27, hi =>
      have hi' : F27.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F27.T0, F27.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F27.T0, F27.TV, base3] at *; omega)
    | 28, hi =>
      have hi' : F28.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F28.T0, F28.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F28.T0, F28.TV, base3] at *; omega)
    | 29, hi =>
      have hi' : F29.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F29.T0, F29.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F29.T0, F29.TV, base3] at *; omega)
    | 30, hi =>
      have hi' : F30.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F30.T0, F30.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F30.T0, F30.TV, base3] at *; omega)
    | 31, hi =>
      have hi' : F31.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F31.T0, F31.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F31.T0, F31.TV, base3] at *; omega)
    | 32, hi =>
      have hi' : F32.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F32.T0, F32.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F32.T0, F32.TV, base3] at *; omega)
    | 33, hi =>
      have hi' : F33.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F33.T0, F33.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F33.T0, F33.TV, base3] at *; omega)
    | 34, hi =>
      have hi' : F34.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F34.T0, F34.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F34.T0, F34.TV, base3] at *; omega)
    | 35, hi =>
      have hi' : F35.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F35.T0, F35.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F35.T0, F35.TV, base3] at *; omega)
    | 36, hi =>
      have hi' : F36.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F36.T0, F36.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F36.T0, F36.TV, base3] at *; omega)
    | 37, hi =>
      have hi' : F37.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F37.T0, F37.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F37.T0, F37.TV, base3] at *; omega)
    | 38, hi =>
      have hi' : F38.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F38.T0, F38.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F38.T0, F38.TV, base3] at *; omega)
    | 39, hi =>
      have hi' : F39.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F39.T0, F39.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F39.T0, F39.TV, base3] at *; omega)
    | 40, hi =>
      have hi' : F40.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F40.T0, F40.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F40.T0, F40.TV, base3] at *; omega)
    | 41, hi =>
      have hi' : F41.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F41.T0, F41.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F41.T0, F41.TV, base3] at *; omega)
    | 42, hi =>
      have hi' : F42.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F42.T0, F42.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F42.T0, F42.TV, base3] at *; omega)
    | 43, hi =>
      have hi' : F43.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F43.T0, F43.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F43.T0, F43.TV, base3] at *; omega)
    | 44, hi =>
      have hi' : F44.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F44.T0, F44.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F44.T0, F44.TV, base3] at *; omega)
    | 45, hi =>
      have hi' : F45.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F45.T0, F45.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F45.T0, F45.TV, base3] at *; omega)
    | 46, hi =>
      have hi' : F46.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F46.T0, F46.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F46.T0, F46.TV, base3] at *; omega)
    | 47, hi =>
      have hi' : F47.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F47.T0, F47.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F47.T0, F47.TV, base3] at *; omega)
    | 48, hi =>
      have hi' : F48.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F48.T0, F48.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F48.T0, F48.TV, base3] at *; omega)
    | 49, hi =>
      have hi' : F49.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F49.T0, F49.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F49.T0, F49.TV, base3] at *; omega)
    | 50, hi =>
      have hi' : F50.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F50.T0, F50.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F50.T0, F50.TV, base3] at *; omega)
    | 51, hi =>
      have hi' : F51.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F51.T0, F51.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F51.T0, F51.TV, base3] at *; omega)
    | n + 52, hi => exact absurd hi (by simp [RegOf]))

set_option maxHeartbeats 3200000 in
theorem piece_k8 :
    UFBound 0 (((4 : ℕ) : ℝ) / (5 : ℕ)) (((9 : ℕ) : ℝ) / (10 : ℕ))
      (((242 : ℤ) : ℝ) / (200 : ℕ)) (((225 : ℤ) : ℝ) / (200 : ℕ)) (((0 : ℤ) : ℝ) / (200 : ℕ)) :=
  ufbound_of_nat (by norm_num) (by norm_num) (by norm_num) (242) (225) (0) (by
    intro r p hr hb hs ht i hi
    obtain ⟨h60, hlo, hhi⟩ := hb
    match i, hi with
    | 0, hi =>
      have hi' : F0.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F0.T0, F0.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F0.T0, F0.TV, base3] at *; omega)
    | 1, hi =>
      have hi' : F1.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F1.T0, F1.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F1.T0, F1.TV, base3] at *; omega)
    | 2, hi =>
      have hi' : F2.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F2.T0, F2.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F2.T0, F2.TV, base3] at *; omega)
    | 3, hi =>
      have hi' : F3.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F3.T0, F3.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F3.T0, F3.TV, base3] at *; omega)
    | 4, hi =>
      have hi' : F4.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F4.T0, F4.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F4.T0, F4.TV, base3] at *; omega)
    | 5, hi =>
      have hi' : F5.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F5.T0, F5.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F5.T0, F5.TV, base3] at *; omega)
    | 6, hi =>
      have hi' : F6.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F6.T0, F6.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F6.T0, F6.TV, base3] at *; omega)
    | 7, hi =>
      have hi' : F7.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F7.T0, F7.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F7.T0, F7.TV, base3] at *; omega)
    | 8, hi =>
      have hi' : F8.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F8.T0, F8.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F8.T0, F8.TV, base3] at *; omega)
    | 9, hi =>
      have hi' : F9.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F9.T0, F9.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F9.T0, F9.TV, base3] at *; omega)
    | 10, hi =>
      have hi' : F10.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F10.T0, F10.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F10.T0, F10.TV, base3] at *; omega)
    | 11, hi =>
      have hi' : F11.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F11.T0, F11.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F11.T0, F11.TV, base3] at *; omega)
    | 12, hi =>
      have hi' : F12.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F12.T0, F12.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F12.T0, F12.TV, base3] at *; omega)
    | 13, hi =>
      have hi' : F13.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F13.T0, F13.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F13.T0, F13.TV, base3] at *; omega)
    | 14, hi =>
      have hi' : F14.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F14.T0, F14.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F14.T0, F14.TV, base3] at *; omega)
    | 15, hi =>
      have hi' : F15.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F15.T0, F15.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F15.T0, F15.TV, base3] at *; omega)
    | 16, hi =>
      have hi' : F16.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F16.T0, F16.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F16.T0, F16.TV, base3] at *; omega)
    | 17, hi =>
      have hi' : F17.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F17.T0, F17.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F17.T0, F17.TV, base3] at *; omega)
    | 18, hi =>
      have hi' : F18.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F18.T0, F18.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F18.T0, F18.TV, base3] at *; omega)
    | 19, hi =>
      have hi' : F19.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F19.T0, F19.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F19.T0, F19.TV, base3] at *; omega)
    | 20, hi =>
      have hi' : F20.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F20.T0, F20.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F20.T0, F20.TV, base3] at *; omega)
    | 21, hi =>
      have hi' : F21.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F21.T0, F21.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F21.T0, F21.TV, base3] at *; omega)
    | 22, hi =>
      have hi' : F22.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F22.T0, F22.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F22.T0, F22.TV, base3] at *; omega)
    | 23, hi =>
      have hi' : F23.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F23.T0, F23.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F23.T0, F23.TV, base3] at *; omega)
    | 24, hi =>
      have hi' : F24.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F24.T0, F24.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F24.T0, F24.TV, base3] at *; omega)
    | 25, hi =>
      have hi' : F25.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F25.T0, F25.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F25.T0, F25.TV, base3] at *; omega)
    | 26, hi =>
      have hi' : F26.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F26.T0, F26.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F26.T0, F26.TV, base3] at *; omega)
    | 27, hi =>
      have hi' : F27.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F27.T0, F27.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F27.T0, F27.TV, base3] at *; omega)
    | 28, hi =>
      have hi' : F28.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F28.T0, F28.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F28.T0, F28.TV, base3] at *; omega)
    | 29, hi =>
      have hi' : F29.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F29.T0, F29.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F29.T0, F29.TV, base3] at *; omega)
    | 30, hi =>
      have hi' : F30.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F30.T0, F30.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F30.T0, F30.TV, base3] at *; omega)
    | 31, hi =>
      have hi' : F31.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F31.T0, F31.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F31.T0, F31.TV, base3] at *; omega)
    | 32, hi =>
      have hi' : F32.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F32.T0, F32.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F32.T0, F32.TV, base3] at *; omega)
    | 33, hi =>
      have hi' : F33.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F33.T0, F33.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F33.T0, F33.TV, base3] at *; omega)
    | 34, hi =>
      have hi' : F34.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F34.T0, F34.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F34.T0, F34.TV, base3] at *; omega)
    | 35, hi =>
      have hi' : F35.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F35.T0, F35.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F35.T0, F35.TV, base3] at *; omega)
    | 36, hi =>
      have hi' : F36.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F36.T0, F36.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F36.T0, F36.TV, base3] at *; omega)
    | 37, hi =>
      have hi' : F37.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F37.T0, F37.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F37.T0, F37.TV, base3] at *; omega)
    | 38, hi =>
      have hi' : F38.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F38.T0, F38.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F38.T0, F38.TV, base3] at *; omega)
    | 39, hi =>
      have hi' : F39.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F39.T0, F39.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F39.T0, F39.TV, base3] at *; omega)
    | 40, hi =>
      have hi' : F40.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F40.T0, F40.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F40.T0, F40.TV, base3] at *; omega)
    | 41, hi =>
      have hi' : F41.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F41.T0, F41.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F41.T0, F41.TV, base3] at *; omega)
    | 42, hi =>
      have hi' : F42.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F42.T0, F42.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F42.T0, F42.TV, base3] at *; omega)
    | 43, hi =>
      have hi' : F43.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F43.T0, F43.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F43.T0, F43.TV, base3] at *; omega)
    | 44, hi =>
      have hi' : F44.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F44.T0, F44.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F44.T0, F44.TV, base3] at *; omega)
    | 45, hi =>
      have hi' : F45.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F45.T0, F45.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F45.T0, F45.TV, base3] at *; omega)
    | 46, hi =>
      have hi' : F46.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F46.T0, F46.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F46.T0, F46.TV, base3] at *; omega)
    | 47, hi =>
      have hi' : F47.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F47.T0, F47.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F47.T0, F47.TV, base3] at *; omega)
    | 48, hi =>
      have hi' : F48.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F48.T0, F48.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F48.T0, F48.TV, base3] at *; omega)
    | 49, hi =>
      have hi' : F49.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F49.T0, F49.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F49.T0, F49.TV, base3] at *; omega)
    | 50, hi =>
      have hi' : F50.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F50.T0, F50.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F50.T0, F50.TV, base3] at *; omega)
    | 51, hi =>
      have hi' : F51.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F51.T0, F51.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F51.T0, F51.TV, base3] at *; omega)
    | n + 52, hi => exact absurd hi (by simp [RegOf]))

set_option maxHeartbeats 3200000 in
theorem piece_k10 :
    UFBound 0 (((1 : ℕ) : ℝ) / (1 : ℕ)) (((11 : ℕ) : ℝ) / (10 : ℕ))
      (((26 : ℤ) : ℝ) / (25 : ℕ)) (((25 : ℤ) : ℝ) / (25 : ℕ)) (((0 : ℤ) : ℝ) / (25 : ℕ)) :=
  ufbound_of_nat (by norm_num) (by norm_num) (by norm_num) (26) (25) (0) (by
    intro r p hr hb hs ht i hi
    obtain ⟨h60, hlo, hhi⟩ := hb
    match i, hi with
    | 0, hi =>
      have hi' : F0.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F0.T0, F0.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F0.T0, F0.TV, base3] at *; omega)
    | 1, hi =>
      have hi' : F1.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F1.T0, F1.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F1.T0, F1.TV, base3] at *; omega)
    | 2, hi =>
      have hi' : F2.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F2.T0, F2.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F2.T0, F2.TV, base3] at *; omega)
    | 3, hi =>
      have hi' : F3.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F3.T0, F3.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F3.T0, F3.TV, base3] at *; omega)
    | 4, hi =>
      have hi' : F4.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F4.T0, F4.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F4.T0, F4.TV, base3] at *; omega)
    | 5, hi =>
      have hi' : F5.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F5.T0, F5.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F5.T0, F5.TV, base3] at *; omega)
    | 6, hi =>
      have hi' : F6.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F6.T0, F6.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F6.T0, F6.TV, base3] at *; omega)
    | 7, hi =>
      have hi' : F7.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F7.T0, F7.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F7.T0, F7.TV, base3] at *; omega)
    | 8, hi =>
      have hi' : F8.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F8.T0, F8.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F8.T0, F8.TV, base3] at *; omega)
    | 9, hi =>
      have hi' : F9.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F9.T0, F9.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F9.T0, F9.TV, base3] at *; omega)
    | 10, hi =>
      have hi' : F10.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F10.T0, F10.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F10.T0, F10.TV, base3] at *; omega)
    | 11, hi =>
      have hi' : F11.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F11.T0, F11.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F11.T0, F11.TV, base3] at *; omega)
    | 12, hi =>
      have hi' : F12.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F12.T0, F12.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F12.T0, F12.TV, base3] at *; omega)
    | 13, hi =>
      have hi' : F13.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F13.T0, F13.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F13.T0, F13.TV, base3] at *; omega)
    | 14, hi =>
      have hi' : F14.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F14.T0, F14.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F14.T0, F14.TV, base3] at *; omega)
    | 15, hi =>
      have hi' : F15.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F15.T0, F15.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F15.T0, F15.TV, base3] at *; omega)
    | 16, hi =>
      have hi' : F16.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F16.T0, F16.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F16.T0, F16.TV, base3] at *; omega)
    | 17, hi =>
      have hi' : F17.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F17.T0, F17.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F17.T0, F17.TV, base3] at *; omega)
    | 18, hi =>
      have hi' : F18.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F18.T0, F18.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F18.T0, F18.TV, base3] at *; omega)
    | 19, hi =>
      have hi' : F19.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F19.T0, F19.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F19.T0, F19.TV, base3] at *; omega)
    | 20, hi =>
      have hi' : F20.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F20.T0, F20.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F20.T0, F20.TV, base3] at *; omega)
    | 21, hi =>
      have hi' : F21.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F21.T0, F21.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F21.T0, F21.TV, base3] at *; omega)
    | 22, hi =>
      have hi' : F22.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F22.T0, F22.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F22.T0, F22.TV, base3] at *; omega)
    | 23, hi =>
      have hi' : F23.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F23.T0, F23.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F23.T0, F23.TV, base3] at *; omega)
    | 24, hi =>
      have hi' : F24.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F24.T0, F24.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F24.T0, F24.TV, base3] at *; omega)
    | 25, hi =>
      have hi' : F25.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F25.T0, F25.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F25.T0, F25.TV, base3] at *; omega)
    | 26, hi =>
      have hi' : F26.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F26.T0, F26.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F26.T0, F26.TV, base3] at *; omega)
    | 27, hi =>
      have hi' : F27.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F27.T0, F27.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F27.T0, F27.TV, base3] at *; omega)
    | 28, hi =>
      have hi' : F28.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F28.T0, F28.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F28.T0, F28.TV, base3] at *; omega)
    | 29, hi =>
      have hi' : F29.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F29.T0, F29.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F29.T0, F29.TV, base3] at *; omega)
    | 30, hi =>
      have hi' : F30.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F30.T0, F30.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F30.T0, F30.TV, base3] at *; omega)
    | 31, hi =>
      have hi' : F31.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F31.T0, F31.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F31.T0, F31.TV, base3] at *; omega)
    | 32, hi =>
      have hi' : F32.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F32.T0, F32.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F32.T0, F32.TV, base3] at *; omega)
    | 33, hi =>
      have hi' : F33.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F33.T0, F33.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F33.T0, F33.TV, base3] at *; omega)
    | 34, hi =>
      have hi' : F34.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F34.T0, F34.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F34.T0, F34.TV, base3] at *; omega)
    | 35, hi =>
      have hi' : F35.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F35.T0, F35.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F35.T0, F35.TV, base3] at *; omega)
    | 36, hi =>
      have hi' : F36.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F36.T0, F36.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F36.T0, F36.TV, base3] at *; omega)
    | 37, hi =>
      have hi' : F37.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F37.T0, F37.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F37.T0, F37.TV, base3] at *; omega)
    | 38, hi =>
      have hi' : F38.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F38.T0, F38.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F38.T0, F38.TV, base3] at *; omega)
    | 39, hi =>
      have hi' : F39.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F39.T0, F39.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F39.T0, F39.TV, base3] at *; omega)
    | 40, hi =>
      have hi' : F40.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F40.T0, F40.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F40.T0, F40.TV, base3] at *; omega)
    | 41, hi =>
      have hi' : F41.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F41.T0, F41.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F41.T0, F41.TV, base3] at *; omega)
    | 42, hi =>
      have hi' : F42.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F42.T0, F42.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F42.T0, F42.TV, base3] at *; omega)
    | 43, hi =>
      have hi' : F43.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F43.T0, F43.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F43.T0, F43.TV, base3] at *; omega)
    | 44, hi =>
      have hi' : F44.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F44.T0, F44.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F44.T0, F44.TV, base3] at *; omega)
    | 45, hi =>
      have hi' : F45.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F45.T0, F45.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F45.T0, F45.TV, base3] at *; omega)
    | 46, hi =>
      have hi' : F46.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F46.T0, F46.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F46.T0, F46.TV, base3] at *; omega)
    | 47, hi =>
      have hi' : F47.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F47.T0, F47.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F47.T0, F47.TV, base3] at *; omega)
    | 48, hi =>
      have hi' : F48.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F48.T0, F48.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F48.T0, F48.TV, base3] at *; omega)
    | 49, hi =>
      have hi' : F49.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F49.T0, F49.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F49.T0, F49.TV, base3] at *; omega)
    | 50, hi =>
      have hi' : F50.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F50.T0, F50.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F50.T0, F50.TV, base3] at *; omega)
    | 51, hi =>
      have hi' : F51.Reg r p := hi
      obtain ⟨⟩ := hi'
      first
        | (simp only [baseOf, T0Of, TVOf, F51.T0, F51.TV, base3]; omega)
        | (simp only [baseOf, T0Of, TVOf, F51.T0, F51.TV, base3] at *; omega)
    | n + 52, hi => exact absurd hi (by simp [RegOf]))

end CatalanCore.Uniform.Content.UFFamily4
