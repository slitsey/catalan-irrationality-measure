module

public import CatalanCore.Uniform.Content.UFFamily3.FamThirds0
public import CatalanCore.Uniform.Content.UFFamily3.FamThirds1
public import CatalanCore.Uniform.Content.UFFamily3.FamThirds2
public import CatalanCore.Uniform.Content.UFFamily3.FamThirds3
public import CatalanCore.Uniform.Content.UFFamily3.FamThirds4
public import CatalanCore.Uniform.Content.UFFamily3.FamThirds5
public import CatalanCore.Uniform.Content.UFFamily3.FamThirds6
public import CatalanCore.Uniform.Content.UFFamily3.FamThirds7
public import CatalanCore.Uniform.Content.UFFamily3.FamThirds8
public import CatalanCore.Uniform.Content.UFFamily3.FamThirds9
public import CatalanCore.Uniform.Content.UFFamily3.FamThirds10
public import CatalanCore.Uniform.Content.UFFamily3.FamThirds11
public import CatalanCore.Uniform.Content.UFFamily3.FamThirds12

@[expose] public section

/-!
# The thirds UF debit layer (lane H, H12)

`thirdsUFLayer`: the union of the 52 window families (first match `idx`),
with the explicit price `baseOf (idx r p) r p = base3 m r p t0 tv`.  Valid on the thirds band
`3 r < 10 p ≤ 39 r`, `p ≥ 60`, `r` even, inside the union of the family regions.
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.UFMoments
  CatalanCore.Uniform.Content.UFWedge CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.UFWire
  CatalanCore.Uniform.Content.Member CatalanCore.Uniform.Content.Wire
  CatalanCore.Uniform.Content.UFFamily CatalanCore.Uniform.Content.UFFamily.SevE
  CatalanCore.Uniform.Content.UFFamily2

namespace CatalanCore.Uniform.Content.UFFamily3

def RegOf : ℕ → ℕ → ℕ → Prop
  | 0 => F0.Reg
  | 1 => F1.Reg
  | 2 => F2.Reg
  | 3 => F3.Reg
  | 4 => F4.Reg
  | 5 => F5.Reg
  | 6 => F6.Reg
  | 7 => F7.Reg
  | 8 => F8.Reg
  | 9 => F9.Reg
  | 10 => F10.Reg
  | 11 => F11.Reg
  | 12 => F12.Reg
  | 13 => F13.Reg
  | 14 => F14.Reg
  | 15 => F15.Reg
  | 16 => F16.Reg
  | 17 => F17.Reg
  | 18 => F18.Reg
  | 19 => F19.Reg
  | 20 => F20.Reg
  | 21 => F21.Reg
  | 22 => F22.Reg
  | 23 => F23.Reg
  | 24 => F24.Reg
  | 25 => F25.Reg
  | 26 => F26.Reg
  | 27 => F27.Reg
  | 28 => F28.Reg
  | 29 => F29.Reg
  | 30 => F30.Reg
  | 31 => F31.Reg
  | 32 => F32.Reg
  | 33 => F33.Reg
  | 34 => F34.Reg
  | 35 => F35.Reg
  | 36 => F36.Reg
  | 37 => F37.Reg
  | 38 => F38.Reg
  | 39 => F39.Reg
  | 40 => F40.Reg
  | 41 => F41.Reg
  | 42 => F42.Reg
  | 43 => F43.Reg
  | 44 => F44.Reg
  | 45 => F45.Reg
  | 46 => F46.Reg
  | 47 => F47.Reg
  | 48 => F48.Reg
  | 49 => F49.Reg
  | 50 => F50.Reg
  | 51 => F51.Reg
  | _ => fun _ _ => False

def T0Of : ℕ → ℕ → ℕ → ℕ
  | 0 => F0.T0
  | 1 => F1.T0
  | 2 => F2.T0
  | 3 => F3.T0
  | 4 => F4.T0
  | 5 => F5.T0
  | 6 => F6.T0
  | 7 => F7.T0
  | 8 => F8.T0
  | 9 => F9.T0
  | 10 => F10.T0
  | 11 => F11.T0
  | 12 => F12.T0
  | 13 => F13.T0
  | 14 => F14.T0
  | 15 => F15.T0
  | 16 => F16.T0
  | 17 => F17.T0
  | 18 => F18.T0
  | 19 => F19.T0
  | 20 => F20.T0
  | 21 => F21.T0
  | 22 => F22.T0
  | 23 => F23.T0
  | 24 => F24.T0
  | 25 => F25.T0
  | 26 => F26.T0
  | 27 => F27.T0
  | 28 => F28.T0
  | 29 => F29.T0
  | 30 => F30.T0
  | 31 => F31.T0
  | 32 => F32.T0
  | 33 => F33.T0
  | 34 => F34.T0
  | 35 => F35.T0
  | 36 => F36.T0
  | 37 => F37.T0
  | 38 => F38.T0
  | 39 => F39.T0
  | 40 => F40.T0
  | 41 => F41.T0
  | 42 => F42.T0
  | 43 => F43.T0
  | 44 => F44.T0
  | 45 => F45.T0
  | 46 => F46.T0
  | 47 => F47.T0
  | 48 => F48.T0
  | 49 => F49.T0
  | 50 => F50.T0
  | 51 => F51.T0
  | _ => fun _ _ => 0

def TVOf : ℕ → ℕ → ℕ → ℕ
  | 0 => F0.TV
  | 1 => F1.TV
  | 2 => F2.TV
  | 3 => F3.TV
  | 4 => F4.TV
  | 5 => F5.TV
  | 6 => F6.TV
  | 7 => F7.TV
  | 8 => F8.TV
  | 9 => F9.TV
  | 10 => F10.TV
  | 11 => F11.TV
  | 12 => F12.TV
  | 13 => F13.TV
  | 14 => F14.TV
  | 15 => F15.TV
  | 16 => F16.TV
  | 17 => F17.TV
  | 18 => F18.TV
  | 19 => F19.TV
  | 20 => F20.TV
  | 21 => F21.TV
  | 22 => F22.TV
  | 23 => F23.TV
  | 24 => F24.TV
  | 25 => F25.TV
  | 26 => F26.TV
  | 27 => F27.TV
  | 28 => F28.TV
  | 29 => F29.TV
  | 30 => F30.TV
  | 31 => F31.TV
  | 32 => F32.TV
  | 33 => F33.TV
  | 34 => F34.TV
  | 35 => F35.TV
  | 36 => F36.TV
  | 37 => F37.TV
  | 38 => F38.TV
  | 39 => F39.TV
  | 40 => F40.TV
  | 41 => F41.TV
  | 42 => F42.TV
  | 43 => F43.TV
  | 44 => F44.TV
  | 45 => F45.TV
  | 46 => F46.TV
  | 47 => F47.TV
  | 48 => F48.TV
  | 49 => F49.TV
  | 50 => F50.TV
  | 51 => F51.TV
  | _ => fun _ _ => 0

def baseOf (i r p : ℕ) : ℕ := base3 ((3 * r + 9) / 20) r p (T0Of i r p) (TVOf i r p)

variable {Fr : Frame}

noncomputable def cellOf (T : TwoTermData Fr 3 2) (i : ℕ) {r p : ℕ} [Fact p.Prime] (hn : Fr.norm = 1)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) : RegOf i r p → Cell3 cT cT_pos Fr 3 2 T r p :=
  match i with
  | 0 => fun h => F0.cell T h hn hnorm hnorm0
  | 1 => fun h => F1.cell T h hn hnorm hnorm0
  | 2 => fun h => F2.cell T h hn hnorm hnorm0
  | 3 => fun h => F3.cell T h hn hnorm hnorm0
  | 4 => fun h => F4.cell T h hn hnorm hnorm0
  | 5 => fun h => F5.cell T h hn hnorm hnorm0
  | 6 => fun h => F6.cell T h hn hnorm hnorm0
  | 7 => fun h => F7.cell T h hn hnorm hnorm0
  | 8 => fun h => F8.cell T h hn hnorm hnorm0
  | 9 => fun h => F9.cell T h hn hnorm hnorm0
  | 10 => fun h => F10.cell T h hn hnorm hnorm0
  | 11 => fun h => F11.cell T h hn hnorm hnorm0
  | 12 => fun h => F12.cell T h hn hnorm hnorm0
  | 13 => fun h => F13.cell T h hn hnorm hnorm0
  | 14 => fun h => F14.cell T h hn hnorm hnorm0
  | 15 => fun h => F15.cell T h hn hnorm hnorm0
  | 16 => fun h => F16.cell T h hn hnorm hnorm0
  | 17 => fun h => F17.cell T h hn hnorm hnorm0
  | 18 => fun h => F18.cell T h hn hnorm hnorm0
  | 19 => fun h => F19.cell T h hn hnorm hnorm0
  | 20 => fun h => F20.cell T h hn hnorm hnorm0
  | 21 => fun h => F21.cell T h hn hnorm hnorm0
  | 22 => fun h => F22.cell T h hn hnorm hnorm0
  | 23 => fun h => F23.cell T h hn hnorm hnorm0
  | 24 => fun h => F24.cell T h hn hnorm hnorm0
  | 25 => fun h => F25.cell T h hn hnorm hnorm0
  | 26 => fun h => F26.cell T h hn hnorm hnorm0
  | 27 => fun h => F27.cell T h hn hnorm hnorm0
  | 28 => fun h => F28.cell T h hn hnorm hnorm0
  | 29 => fun h => F29.cell T h hn hnorm hnorm0
  | 30 => fun h => F30.cell T h hn hnorm hnorm0
  | 31 => fun h => F31.cell T h hn hnorm hnorm0
  | 32 => fun h => F32.cell T h hn hnorm hnorm0
  | 33 => fun h => F33.cell T h hn hnorm hnorm0
  | 34 => fun h => F34.cell T h hn hnorm hnorm0
  | 35 => fun h => F35.cell T h hn hnorm hnorm0
  | 36 => fun h => F36.cell T h hn hnorm hnorm0
  | 37 => fun h => F37.cell T h hn hnorm hnorm0
  | 38 => fun h => F38.cell T h hn hnorm hnorm0
  | 39 => fun h => F39.cell T h hn hnorm hnorm0
  | 40 => fun h => F40.cell T h hn hnorm hnorm0
  | 41 => fun h => F41.cell T h hn hnorm hnorm0
  | 42 => fun h => F42.cell T h hn hnorm hnorm0
  | 43 => fun h => F43.cell T h hn hnorm hnorm0
  | 44 => fun h => F44.cell T h hn hnorm hnorm0
  | 45 => fun h => F45.cell T h hn hnorm hnorm0
  | 46 => fun h => F46.cell T h hn hnorm hnorm0
  | 47 => fun h => F47.cell T h hn hnorm hnorm0
  | 48 => fun h => F48.cell T h hn hnorm hnorm0
  | 49 => fun h => F49.cell T h hn hnorm hnorm0
  | 50 => fun h => F50.cell T h hn hnorm hnorm0
  | 51 => fun h => F51.cell T h hn hnorm hnorm0
  | n + 52 => fun h => False.elim (by simp [RegOf] at h)

theorem cellOf_bound (T : TwoTermData Fr 3 2) (i : ℕ) {r p : ℕ} [Fact p.Prime] (hn : Fr.norm = 1)
    (hnorm : Fr.norm ∈ S p) (hnorm0 : red p Fr.norm ≠ 0) :
    ∀ h : RegOf i r p, (cellOf T i hn hnorm hnorm0 h).bound = baseOf i r p := by
  match i with
  | 0 => exact fun h => F0.cell_bound T h hn hnorm hnorm0
  | 1 => exact fun h => F1.cell_bound T h hn hnorm hnorm0
  | 2 => exact fun h => F2.cell_bound T h hn hnorm hnorm0
  | 3 => exact fun h => F3.cell_bound T h hn hnorm hnorm0
  | 4 => exact fun h => F4.cell_bound T h hn hnorm hnorm0
  | 5 => exact fun h => F5.cell_bound T h hn hnorm hnorm0
  | 6 => exact fun h => F6.cell_bound T h hn hnorm hnorm0
  | 7 => exact fun h => F7.cell_bound T h hn hnorm hnorm0
  | 8 => exact fun h => F8.cell_bound T h hn hnorm hnorm0
  | 9 => exact fun h => F9.cell_bound T h hn hnorm hnorm0
  | 10 => exact fun h => F10.cell_bound T h hn hnorm hnorm0
  | 11 => exact fun h => F11.cell_bound T h hn hnorm hnorm0
  | 12 => exact fun h => F12.cell_bound T h hn hnorm hnorm0
  | 13 => exact fun h => F13.cell_bound T h hn hnorm hnorm0
  | 14 => exact fun h => F14.cell_bound T h hn hnorm hnorm0
  | 15 => exact fun h => F15.cell_bound T h hn hnorm hnorm0
  | 16 => exact fun h => F16.cell_bound T h hn hnorm hnorm0
  | 17 => exact fun h => F17.cell_bound T h hn hnorm hnorm0
  | 18 => exact fun h => F18.cell_bound T h hn hnorm hnorm0
  | 19 => exact fun h => F19.cell_bound T h hn hnorm hnorm0
  | 20 => exact fun h => F20.cell_bound T h hn hnorm hnorm0
  | 21 => exact fun h => F21.cell_bound T h hn hnorm hnorm0
  | 22 => exact fun h => F22.cell_bound T h hn hnorm hnorm0
  | 23 => exact fun h => F23.cell_bound T h hn hnorm hnorm0
  | 24 => exact fun h => F24.cell_bound T h hn hnorm hnorm0
  | 25 => exact fun h => F25.cell_bound T h hn hnorm hnorm0
  | 26 => exact fun h => F26.cell_bound T h hn hnorm hnorm0
  | 27 => exact fun h => F27.cell_bound T h hn hnorm hnorm0
  | 28 => exact fun h => F28.cell_bound T h hn hnorm hnorm0
  | 29 => exact fun h => F29.cell_bound T h hn hnorm hnorm0
  | 30 => exact fun h => F30.cell_bound T h hn hnorm hnorm0
  | 31 => exact fun h => F31.cell_bound T h hn hnorm hnorm0
  | 32 => exact fun h => F32.cell_bound T h hn hnorm hnorm0
  | 33 => exact fun h => F33.cell_bound T h hn hnorm hnorm0
  | 34 => exact fun h => F34.cell_bound T h hn hnorm hnorm0
  | 35 => exact fun h => F35.cell_bound T h hn hnorm hnorm0
  | 36 => exact fun h => F36.cell_bound T h hn hnorm hnorm0
  | 37 => exact fun h => F37.cell_bound T h hn hnorm hnorm0
  | 38 => exact fun h => F38.cell_bound T h hn hnorm hnorm0
  | 39 => exact fun h => F39.cell_bound T h hn hnorm hnorm0
  | 40 => exact fun h => F40.cell_bound T h hn hnorm hnorm0
  | 41 => exact fun h => F41.cell_bound T h hn hnorm hnorm0
  | 42 => exact fun h => F42.cell_bound T h hn hnorm hnorm0
  | 43 => exact fun h => F43.cell_bound T h hn hnorm hnorm0
  | 44 => exact fun h => F44.cell_bound T h hn hnorm hnorm0
  | 45 => exact fun h => F45.cell_bound T h hn hnorm hnorm0
  | 46 => exact fun h => F46.cell_bound T h hn hnorm hnorm0
  | 47 => exact fun h => F47.cell_bound T h hn hnorm hnorm0
  | 48 => exact fun h => F48.cell_bound T h hn hnorm hnorm0
  | 49 => exact fun h => F49.cell_bound T h hn hnorm hnorm0
  | 50 => exact fun h => F50.cell_bound T h hn hnorm hnorm0
  | 51 => exact fun h => F51.cell_bound T h hn hnorm hnorm0
  | n + 52 => exact fun h => False.elim (by simp [RegOf] at h)

open Classical in
/-- First family whose region contains `(r, p)`. -/
noncomputable def idx (r p : ℕ) : ℕ := if h : ∃ i, RegOf i r p then Nat.find h else 0

theorem idx_spec {r p : ℕ} (h : ∃ i, RegOf i r p) : RegOf (idx r p) r p := by
  classical
  unfold idx
  rw [dif_pos h]
  exact Nat.find_spec h

/-- Validity of the thirds UF layer. -/
def ValidT (Fr : Frame) (r p : ℕ) : Prop :=
  (∃ i, RegOf i r p) ∧ Fr.norm = 1 ∧ ∀ [Fact p.Prime], Fr.norm ∈ S p ∧ red p Fr.norm ≠ 0

/-- **The thirds UF debit layer.** -/
noncomputable def thirdsUFLayer (T : TwoTermData Fr 3 2) {depth : ℕ} :
    DebitLayer (altGeom cT cT_pos) Fr depth :=
  layer3 (T := T) (ValidT Fr) (fun r p => baseOf (idx r p) r p)
    (fun r p _ h => cellOf T (idx r p) h.2.1 h.2.2.1 h.2.2.2 (idx_spec h.1))
    (fun r p _ h => (cellOf_bound T (idx r p) h.2.1 h.2.2.1 h.2.2.2 (idx_spec h.1)).le)

theorem thirdsUFLayer_valid (T : TwoTermData Fr 3 2) {depth : ℕ} :
    (thirdsUFLayer (depth := depth) T).valid = ValidT Fr := rfl

theorem thirdsUFLayer_debit (T : TwoTermData Fr 3 2) {depth : ℕ} :
    (thirdsUFLayer (depth := depth) T).debit = 1 := rfl

theorem thirdsUFLayer_eff (T : TwoTermData Fr 3 2) {depth : ℕ} (r p : ℕ) :
    (thirdsUFLayer (depth := depth) T).eff r p = baseOf (idx r p) r p + depth := by
  have hb : (thirdsUFLayer (depth := depth) T).base = fun r p => baseOf (idx r p) r p := rfl
  have hd : (thirdsUFLayer (depth := depth) T).debit = 1 := rfl
  simp [DebitLayer.eff, hb, hd]

end CatalanCore.Uniform.Content.UFFamily3
