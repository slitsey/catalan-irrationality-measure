module

public import CatalanCore.Uniform.Bank.Plane1.Data.Lam
public import CatalanCore.Uniform.Bank.Plane1.Data.Exp1
public import CatalanCore.Uniform.Bank.Plane1.Data.Exp5
public import CatalanCore.Uniform.Bank.Plane1.Data.HeadM
public import CatalanCore.Uniform.Bank.Plane1.Data.HM1
public import CatalanCore.Uniform.Bank.Plane1.Data.HM5

@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000

/-! # Plane 1 content, closed form: the bank of `S⁻` (wave H5a-closed; ledger P115)

`bankM` = header with `Λ = planeLam` and the closed templates `tM1`, `tM5` (strips `n' = 16, …, 1` from the cells
`cells1`, `cells5`, then the head pieces).  **`bankM_check : kcheckC bankM = true`**, from the pieces: the frame,
the head conditions (the expansion is checked once in `Exp1`, `Exp5`), the cells, `pieceOK` of the head pieces and the
class masses (`kclassOK_six`). -/

namespace CatalanCore.Uniform.Bank.Plane1.Data
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check

def tM1 : KTmplC := ⟨qq 1 204, 16, cells1, hM1, 5⟩
def tM5 : KTmplC := ⟨qq 1 204, 16, cells5, hM5, 5⟩

/-- The closed plane 1 content bank of the support. -/
def bankM : KBankDataC := { eHeadM with Λ := planeLam, tmpls := [(1, tM1), (5, tM5)] }

theorem bankM_params : kcParams bankM = true := by
  -- kcost: 0.1 s measured (a dozen comparisons)
  decide +kernel

theorem bankM_head1 : ktmplHead bankM.toK 1 (tM1.toK bankM.α) = true := by
  -- kcost: 2 s measured (chain, tail test and end of the 76 head pieces of a class)
  exact ktmplHead_toK_of (e0 := qq 1 12) (by decide +kernel) (by decide +kernel) exp1_chain exp1_end
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bankM_head5 : ktmplHead bankM.toK 5 (tM5.toK bankM.α) = true := by
  -- kcost: 2 s measured (chain, tail test and end of the 76 head pieces of a class)
  exact ktmplHead_toK_of (e0 := qq 1 12) (by decide +kernel) (by decide +kernel) exp5_chain exp5_end
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem bankM_heads : kcHeads bankM = true := by
  unfold kcHeads
  show [(1, tM1), (5, tM5)].all (fun x => ktmplHead bankM.toK x.1 (x.2.toK bankM.α) && decide (1 ≤ x.2.N)) = true
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨bankM_head1, by decide⟩, ⟨bankM_head5, by decide⟩⟩

theorem bankM_kappa : kappaOf bankM.toK 1 0 = qq 1 3 ∧ kappaOf bankM.toK 1 1 = qq 1 2 ∧
    kappaOf bankM.toK 5 0 = qq 2 3 ∧ kappaOf bankM.toK 5 1 = qq 1 2 := by
  -- kcost: 0.1 s measured (four pole positions)
  decide +kernel

theorem bankM_cells : kcCells bankM = true := by
  obtain ⟨k10, k11, k50, k51⟩ := bankM_kappa
  unfold kcCells
  show [(1, tM1), (5, tM5)].all (fun x => x.2.cells.all (fun c =>
    c.ok bankM.α (kappaOf bankM.toK x.1 0) (kappaOf bankM.toK x.1 1))) = true
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  rw [k10, k11, k50, k51]
  exact ⟨cells1_ok, cells5_ok⟩

theorem bankM_pieces : kcPieces bankM = true := by
  unfold kcPieces
  show [(1, tM1), (5, tM5)].all (fun x => kpieceAll bankM.toK x.1 x.2.head) = true
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨hM1_ok, hM5_ok⟩

theorem bankM_mass : ((tM1.toK bankM.α).toQ.mass bankM.toK.α0 + (tM5.toK bankM.α).toQ.mass bankM.toK.α0 =
    bankM.toK.Λ * 2) := by
  rw [KTmplC.mass_toK, KTmplC.mass_toK]
  rw [show (tM1.expP bankM.α) = expPs (qq 1 12) 16 cells1 from rfl,
    show (tM5.expP bankM.α) = expPs (qq 1 12) 16 cells5 from rfl, exp1_mass, exp5_mass]
  -- kcost: 3 s measured (masses of the 76 head pieces of each class and the final comparison)
  decide +kernel

theorem bankM_class : kcClass bankM = true :=
  kclassOK_six bankM.toK rfl rfl (Or.inr rfl) (T1 := tM1.toK bankM.α) (T5 := tM5.toK bankM.α) rfl rfl
    bankM_mass

/-- **The closed plane 1 content bank of the support passes `kcheckC`.** -/
theorem bankM_check : kcheckC bankM = true :=
  kcheckC_of bankM_params bankM_heads bankM_cells bankM_pieces bankM_class

end CatalanCore.Uniform.Bank.Plane1.Data

#print axioms CatalanCore.Uniform.Bank.Plane1.Data.bankM_check
