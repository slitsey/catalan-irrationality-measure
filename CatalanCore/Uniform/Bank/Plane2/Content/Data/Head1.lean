module

public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Common

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 2 content, closed form: head pieces, part 1 (wave P210-L; ledger P210)

Pieces of `θ ∈ (1/(U₀ + δ), τ]` (`θ ≥ 2 α` minus the gap at `2 α`): rows `P₄ .. P₇`, `E₁`, `E₂`, the tail. -/

namespace CatalanCore.Uniform.Bank.Plane2.Content.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane2.Content

def hd1_0 : List (QPiece × Cert) := [
  (⟨(qq (3000000) 20500003), (qq (3000000) 20499997), (qq (264) 41), (qq (-5) 1), (qq (1000000000000000) 1)⟩, ⟨0, [], [], (qq (4622751353000099) 23062500000000)⟩),
  (⟨(qq (3000000) 20499997), (qq (94) 615), (qq (88) 41), (qq (13) 2), (qq (1000000000000000) 1)⟩, ⟨5, [], [], (qq (840499877) 9)⟩),
  (⟨(qq (94) 615), (qq (44) 287), (qq (1) 1), (qq (14) 1), (qq (1000000000000000) 1)⟩, ⟨5, [], [], (qq (615) 2)⟩),
  (⟨(qq (44) 287), (qq (2) 13), (qq (217) 41), (qq (-14) 1), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (287) 1)⟩),
  (⟨(qq (2) 13), (qq (47) 287), (qq (176) 41), (qq (-15) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (533) 2)⟩),
  (⟨(qq (47) 287), (qq (88) 533), (qq (2) 1), (qq (13) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (353584) 2209)⟩),
  (⟨(qq (88) 533), (qq (1) 6), (qq (170) 41), (qq (-13) 2), (qq (1000000000000000) 1)⟩, ⟨7, [], [], (qq (6929) 44)⟩),
  (⟨(qq (1) 6), (qq (94) 533), (qq (88) 41), (qq (11) 2), (qq (1000000000000000) 1)⟩, ⟨5, [], [], (qq (6336) 41)⟩),
  (⟨(qq (94) 533), (qq (22) 123), (qq (1) 1), (qq (12) 1), (qq (1000000000000000) 1)⟩, ⟨5, [], [], (qq (304876) 2209)⟩),
  (⟨(qq (22) 123), (qq (2) 11), (qq (217) 41), (qq (-12) 1), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (1476) 11)⟩)]

def hd1_1 : List (QPiece × Cert) := [
  (⟨(qq (2) 11), (qq (47) 246), (qq (176) 41), (qq (-13) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (5324) 41)⟩),
  (⟨(qq (47) 246), (qq (8) 41), (qq (2) 1), (qq (11) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (259776) 2209)⟩),
  (⟨(qq (8) 41), (qq (1) 5), (qq (170) 41), (qq (-11) 2), (qq (1000000000000000) 1)⟩, ⟨7, [], [], (qq (451) 4)⟩),
  (⟨(qq (1) 5), (qq (94) 451), (qq (88) 41), (qq (9) 2), (qq (1000000000000000) 1)⟩, ⟨5, [], [], (qq (4400) 41)⟩),
  (⟨(qq (94) 451), (qq (44) 205), (qq (1) 1), (qq (10) 1), (qq (1000000000000000) 1)⟩, ⟨5, [], [], (qq (218284) 2209)⟩),
  (⟨(qq (44) 205), (qq (2) 9), (qq (217) 41), (qq (-10) 1), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (1025) 11)⟩),
  (⟨(qq (2) 9), (qq (47) 205), (qq (176) 41), (qq (-11) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (3564) 41)⟩),
  (⟨(qq (47) 205), (qq (88) 369), (qq (2) 1), (qq (9) 2), (qq (1000000000000000) 1)⟩, ⟨8, [], [], (qq (180400) 2209)⟩),
  (⟨(qq (88) 369), (qq (1) 4), (qq (170) 41), (qq (-9) 2), (qq (1000000000000000) 1)⟩, ⟨7, [], [], (qq (3321) 44)⟩),
  (⟨(qq (1) 4), (qq (94) 369), (qq (88) 41), (qq (7) 2), (qq (1000000000000000) 1)⟩, ⟨5, [], [], (qq (2816) 41)⟩)]

theorem hd1_0_ok : kpieceAll p2H 1 hd1_0 = true := by
  -- kcost: 0.46 s measured, 10 pieces
  decide +kernel

theorem hd1_1_ok : kpieceAll p2H 1 hd1_1 = true := by
  -- kcost: 0.46 s measured, 10 pieces
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2.Content.Data
