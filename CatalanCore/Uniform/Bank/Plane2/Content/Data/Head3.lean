module

public import CatalanCore.Uniform.Bank.Plane2.Content.Data.Common

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 2 content, closed form: head pieces, part 3 (wave P210-L; ledger P210)

Pieces of `θ ∈ (1/(U₀ + δ), τ]` (`θ ≥ 2 α` minus the gap at `2 α`): rows `P₄ .. P₇`, `E₁`, `E₂`, the tail. -/

namespace CatalanCore.Uniform.Bank.Plane2.Content.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane2.Content

def hd3_0 : List (QPiece × Cert) := [
  (⟨(qq (47) 41), (qq (47000041) 41000000), (qq (88) 41), (qq (-1) 1), (qq (1000000000000000) 1)⟩, ⟨15, [], [], (qq (41) 6)⟩),
  (⟨(qq (47000041) 41000000), (qq (2) 1), (qq (88) 41), (qq (-1) 1), (qq (1000000000000000) 1)⟩, ⟨2, [], [], (qq (2000000) 1)⟩),
  (⟨(qq (2) 1), (qq (94) 41), (qq (47) 41), (qq (-1) 2), (qq (1000000000000000) 1)⟩, ⟨3, [], [], (qq (3) 1)⟩),
  (⟨(qq (94) 41), (qq (417) 164), (qq (0) 1), (qq (0) 1), (qq (1000000000000000) 1)⟩, ⟨3, [], [], (qq (41) 12)⟩)]

theorem hd3_0_ok : kpieceAll p2H 1 hd3_0 = true := by
  -- kcost: 0.46 s measured, 4 pieces
  decide +kernel

end CatalanCore.Uniform.Bank.Plane2.Content.Data
