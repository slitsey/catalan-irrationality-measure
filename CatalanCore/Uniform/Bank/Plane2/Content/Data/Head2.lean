module

public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Common

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 2 content, closed form: head pieces, part 2 (wave P210-L; ledger P210)

Pieces of `θ ∈ (1/(U₀ + δ), τ]` (`θ ≥ 2 α` minus the gap at `2 α`): rows `P₄ .. P₇`, `E₁`, `E₂`, the tail. -/

namespace CatalanCore.Uniform.Bank.Plane2.Content.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane2.Content

def hd2_0 : List (QPiece × Cert) := [
  (⟨(qq (94) 369), (qq (11) 41), (qq (1) 1), (qq (8) 1), (qq (1000000000000000) 1)⟩, ⟨5, [], [], (qq (146124) 2209)⟩),
  (⟨(qq (11) 41), (qq (2) 7), (qq (217) 41), (qq (-8) 1), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (656) 11)⟩),
  (⟨(qq (2) 7), (qq (47) 164), (qq (176) 41), (qq (-9) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (2156) 41)⟩),
  (⟨(qq (47) 164), (qq (88) 287), (qq (2) 1), (qq (7) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (115456) 2209)⟩),
  (⟨(qq (88) 287), (qq (94) 287), (qq (170) 41), (qq (-7) 2), (qq (1000000000000000) 1)⟩, ⟨7, [], [], (qq (2009) 44)⟩),
  (⟨(qq (94) 287), (qq (1) 3), (qq (3) 1), (qq (0) 1), (qq (1000000000000000) 1)⟩, ⟨7, [], [], (qq (88396) 2209)⟩),
  (⟨(qq (1) 3), (qq (44) 123), (qq (1) 1), (qq (6) 1), (qq (1000000000000000) 1)⟩, ⟨5, [], [], (qq (1584) 41)⟩),
  (⟨(qq (44) 123), (qq (47) 123), (qq (217) 41), (qq (-6) 1), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (369) 11)⟩),
  (⟨(qq (47) 123), (qq (2) 5), (qq (3) 1), (qq (0) 1), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (64944) 2209)⟩),
  (⟨(qq (2) 5), (qq (88) 205), (qq (2) 1), (qq (5) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (1100) 41)⟩)]

def hd2_1 : List (QPiece × Cert) := [
  (⟨(qq (88) 205), (qq (94) 205), (qq (170) 41), (qq (-5) 2), (qq (1000000000000000) 1)⟩, ⟨7, [], [], (qq (1025) 44)⟩),
  (⟨(qq (94) 205), (qq (1) 2), (qq (3) 1), (qq (0) 1), (qq (1000000000000000) 1)⟩, ⟨7, [], [], (qq (45100) 2209)⟩),
  (⟨(qq (1) 2), (qq (22) 41), (qq (1) 1), (qq (4) 1), (qq (1000000000000000) 1)⟩, ⟨5, [], [], (qq (704) 41)⟩),
  (⟨(qq (22) 41), (qq (47) 82), (qq (217) 41), (qq (-4) 1), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (164) 11)⟩),
  (⟨(qq (47) 82), (qq (2) 3), (qq (170) 41), (qq (-2) 1), (qq (1000000000000000) 1)⟩, ⟨13, [], [], (qq (28864) 2209)⟩),
  (⟨(qq (2) 3), (qq (88) 123), (qq (129) 41), (qq (-1) 2), (qq (1000000000000000) 1)⟩, ⟨13, [], [], (qq (246) 23)⟩),
  (⟨(qq (88) 123), (qq (94) 123), (qq (217) 41), (qq (-7) 2), (qq (1000000000000000) 1)⟩, ⟨12, [], [], (qq (369) 44)⟩),
  (⟨(qq (94) 123), (qq (1) 1), (qq (264) 41), (qq (-5) 1), (qq (1000000000000000) 1)⟩, ⟨0, [], [], (qq (369) 47)⟩),
  (⟨(qq (1) 1), (qq (46999959) 41000000), (qq (182) 41), (qq (-3) 1), (qq (1000000000000000) 1)⟩, ⟨1, [], [], (qq (2000000) 1)⟩),
  (⟨(qq (46999959) 41000000), (qq (47) 41), (qq (182) 41), (qq (-3) 1), (qq (1000000000000000) 1)⟩, ⟨15, [], [], (qq (41000000) 5999959)⟩)]

theorem hd2_0_ok : kpieceAll p2H 1 hd2_0 = true := by
  -- kcost: 0.46 s measured, 10 pieces
  decide +kernel

theorem hd2_1_ok : kpieceAll p2H 1 hd2_1 = true := by
  -- kcost: 0.46 s measured, 10 pieces
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2.Content.Data
