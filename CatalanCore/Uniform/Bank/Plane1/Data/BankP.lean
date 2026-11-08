module

public import CatalanCore.Uniform.Bank.Plane1.Data.Lam
public import CatalanCore.Uniform.Bank.Plane1.Data.Exp1
public import CatalanCore.Uniform.Bank.Plane1.Data.Exp5
public import CatalanCore.Uniform.Bank.Plane1.Data.HeadP
public import CatalanCore.Uniform.Bank.Plane1.Data.HP1
public import CatalanCore.Uniform.Bank.Plane1.Data.HP5

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 1 content, closed form: the bank of `S⁺` (wave H5a-closed; ledger P115)

`bankP` = header with `Λ = planeLam` and the closed templates `tP1`, `tP5` (strips `n' = 32, …, 1` from the cells
`cells1`, `cells5`, then the head pieces).  **`bankP_check : kcheckC bankP = true`**, from the pieces: the frame,
the head conditions (the expansion is checked once in `Exp1`, `Exp5`), the cells, `pieceOK` of the head pieces and the
class masses (`kclassOK_six`). -/

namespace CatalanCore.Uniform.Bank.Plane1.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

def tP1 : KTmplC := ⟨qq 1 396, 32, cells1, hP1, 5⟩
def tP5 : KTmplC := ⟨qq 1 396, 32, cells5, hP5, 5⟩

/-- The closed plane 1 content bank of the support. -/
def bankP : KBankDataC := { eHeadP with Λ := planeLam, tmpls := [(1, tP1), (5, tP5)] }

theorem bankP_params : kcParams bankP = true := by
  -- kcost: 0.1 s measured (a dozen comparisons)
  decide +kernel

theorem bankP_head1 : ktmplHead bankP.toK 1 (tP1.toK bankP.α) = true := by
  -- kcost: 2 s measured (chain, tail test and end of the 76 head pieces of a class)
  exact ktmplHead_toK_of (e0 := qq 1 12) (by decide +kernel) (by decide +kernel) exp1_chain exp1_end
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bankP_head5 : ktmplHead bankP.toK 5 (tP5.toK bankP.α) = true := by
  -- kcost: 2 s measured (chain, tail test and end of the 76 head pieces of a class)
  exact ktmplHead_toK_of (e0 := qq 1 12) (by decide +kernel) (by decide +kernel) exp5_chain exp5_end
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bankP_heads : kcHeads bankP = true := by
  unfold kcHeads
  show [(1, tP1), (5, tP5)].all (fun x => ktmplHead bankP.toK x.1 (x.2.toK bankP.α) && decide (1 ≤ x.2.N)) = true
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨bankP_head1, by decide⟩, ⟨bankP_head5, by decide⟩⟩

theorem bankP_kappa : kappaOf bankP.toK 1 0 = qq 1 3 ∧ kappaOf bankP.toK 1 1 = qq 1 2 ∧
    kappaOf bankP.toK 5 0 = qq 2 3 ∧ kappaOf bankP.toK 5 1 = qq 1 2 := by
  -- kcost: 0.1 s measured (four pole positions)
  decide +kernel

theorem bankP_cells : kcCells bankP = true := by
  obtain ⟨k10, k11, k50, k51⟩ := bankP_kappa
  unfold kcCells
  show [(1, tP1), (5, tP5)].all (fun x => x.2.cells.all (fun c =>
    c.ok bankP.α (kappaOf bankP.toK x.1 0) (kappaOf bankP.toK x.1 1))) = true
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  rw [k10, k11, k50, k51]
  exact ⟨cells1_ok, cells5_ok⟩

theorem bankP_pieces : kcPieces bankP = true := by
  unfold kcPieces
  show [(1, tP1), (5, tP5)].all (fun x => kpieceAll bankP.toK x.1 x.2.head) = true
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨hP1_ok, hP5_ok⟩

theorem bankP_mass : ((tP1.toK bankP.α).toQ.mass bankP.toK.α0 + (tP5.toK bankP.α).toQ.mass bankP.toK.α0 =
    bankP.toK.Λ * 2) := by
  rw [KTmplC.mass_toK, KTmplC.mass_toK]
  rw [show (tP1.expP bankP.α) = expPs (qq 1 12) 32 cells1 from rfl,
    show (tP5.expP bankP.α) = expPs (qq 1 12) 32 cells5 from rfl, exp1_mass, exp5_mass]
  -- kcost: 3 s measured (masses of the 76 head pieces of each class and the final comparison)
  decide +kernel

theorem bankP_class : kcClass bankP = true :=
  kclassOK_six bankP.toK rfl rfl (Or.inl rfl) (T1 := tP1.toK bankP.α) (T5 := tP5.toK bankP.α) rfl rfl
    bankP_mass

/-- **The closed plane 1 content bank of the support passes `kcheckC`.** -/
theorem bankP_check : kcheckC bankP = true :=
  kcheckC_of bankP_params bankP_heads bankP_cells bankP_pieces bankP_class

end CatalanCore.Uniform.Bank.Plane1.Data

#print axioms CatalanCore.Uniform.Bank.Plane1.Data.bankP_check
