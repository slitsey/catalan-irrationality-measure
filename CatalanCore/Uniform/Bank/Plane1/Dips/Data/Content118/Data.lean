module
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Base.U1B000
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Base.U1B001
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Base.U1B002
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Base.U5B000
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Base.U5B001
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Base.U5B002
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head.PU1B000
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head.PU1B001
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head.PU1B002
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head.PU5B000
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head.PU5B001
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head.PU5B002
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head.MU1B000
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head.MU1B001
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head.MU1B002
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head.MU5B000
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head.MU5B001
public import CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.Head.MU5B002
@[expose] public section
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 3200000
namespace CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118
open CatalanCore.Uniform.Content.BankShared.KTerm CatalanCore.Uniform.Content.BankShared.Check CatalanCore.Uniform.Bank.Plane1
def cells1 : List PCell := [cell1_0, cell1_1, cell1_2, cell1_3, cell1_4, cell1_5, cell1_6, cell1_7, cell1_8, cell1_9, cell1_10, cell1_11, cell1_12, cell1_13, cell1_14, cell1_15, cell1_16, cell1_17, cell1_18, cell1_19, cell1_20, cell1_21, cell1_22, cell1_23, cell1_24, cell1_25, cell1_26, cell1_27, cell1_28, cell1_29, cell1_30, cell1_31, cell1_32, cell1_33, cell1_34, cell1_35, cell1_36, cell1_37, cell1_38, cell1_39, cell1_40, cell1_41, cell1_42, cell1_43, cell1_44, cell1_45, cell1_46, cell1_47, cell1_48, cell1_49, cell1_50, cell1_51, cell1_52, cell1_53, cell1_54]
def cells5 : List PCell := [cell5_0, cell5_1, cell5_2, cell5_3, cell5_4, cell5_5, cell5_6, cell5_7, cell5_8, cell5_9, cell5_10, cell5_11, cell5_12, cell5_13, cell5_14, cell5_15, cell5_16, cell5_17, cell5_18, cell5_19, cell5_20, cell5_21, cell5_22, cell5_23, cell5_24, cell5_25, cell5_26, cell5_27, cell5_28, cell5_29, cell5_30, cell5_31, cell5_32, cell5_33, cell5_34, cell5_35, cell5_36, cell5_37, cell5_38, cell5_39, cell5_40, cell5_41, cell5_42, cell5_43, cell5_44, cell5_45, cell5_46, cell5_47, cell5_48, cell5_49, cell5_50, cell5_51, cell5_52, cell5_53, cell5_54]
def headsP1 : List (QPiece × Cert) := [headP1_0, headP1_1, headP1_2, headP1_3, headP1_4, headP1_5, headP1_6, headP1_7, headP1_8, headP1_9, headP1_10, headP1_11, headP1_12, headP1_13, headP1_14, headP1_15, headP1_16, headP1_17, headP1_18, headP1_19, headP1_20, headP1_21, headP1_22, headP1_23, headP1_24, headP1_25, headP1_26, headP1_27, headP1_28, headP1_29, headP1_30, headP1_31, headP1_32, headP1_33, headP1_34, headP1_35, headP1_36, headP1_37, headP1_38, headP1_39, headP1_40, headP1_41, headP1_42, headP1_43, headP1_44, headP1_45, headP1_46, headP1_47, headP1_48]
def tmplP1 : KTmplC := ⟨1/264,32,cells1,headsP1,5⟩
def headsP5 : List (QPiece × Cert) := [headP5_0, headP5_1, headP5_2, headP5_3, headP5_4, headP5_5, headP5_6, headP5_7, headP5_8, headP5_9, headP5_10, headP5_11, headP5_12, headP5_13, headP5_14, headP5_15, headP5_16, headP5_17, headP5_18, headP5_19, headP5_20, headP5_21, headP5_22, headP5_23, headP5_24, headP5_25, headP5_26, headP5_27, headP5_28, headP5_29, headP5_30, headP5_31, headP5_32, headP5_33, headP5_34, headP5_35, headP5_36, headP5_37, headP5_38, headP5_39, headP5_40, headP5_41, headP5_42, headP5_43, headP5_44, headP5_45, headP5_46, headP5_47, headP5_48, headP5_49]
def tmplP5 : KTmplC := ⟨1/264,32,cells5,headsP5,5⟩
def bankP : KBankDataC := { header 2 1 with tmpls := [(1,tmplP1),(5,tmplP5)] }
def headsM1 : List (QPiece × Cert) := [headM1_0, headM1_1, headM1_2, headM1_3, headM1_4, headM1_5, headM1_6, headM1_7, headM1_8, headM1_9, headM1_10, headM1_11, headM1_12, headM1_13, headM1_14, headM1_15, headM1_16, headM1_17, headM1_18, headM1_19, headM1_20, headM1_21, headM1_22, headM1_23, headM1_24, headM1_25, headM1_26, headM1_27, headM1_28, headM1_29, headM1_30, headM1_31, headM1_32, headM1_33, headM1_34, headM1_35, headM1_36, headM1_37, headM1_38, headM1_39, headM1_40, headM1_41, headM1_42, headM1_43, headM1_44, headM1_45, headM1_46, headM1_47, headM1_48]
def tmplM1 : KTmplC := ⟨1/264,32,cells1,headsM1,5⟩
def headsM5 : List (QPiece × Cert) := [headM5_0, headM5_1, headM5_2, headM5_3, headM5_4, headM5_5, headM5_6, headM5_7, headM5_8, headM5_9, headM5_10, headM5_11, headM5_12, headM5_13, headM5_14, headM5_15, headM5_16, headM5_17, headM5_18, headM5_19, headM5_20, headM5_21, headM5_22, headM5_23, headM5_24, headM5_25, headM5_26, headM5_27, headM5_28, headM5_29, headM5_30, headM5_31, headM5_32, headM5_33, headM5_34, headM5_35, headM5_36, headM5_37, headM5_38, headM5_39, headM5_40, headM5_41, headM5_42, headM5_43, headM5_44, headM5_45, headM5_46, headM5_47, headM5_48, headM5_49]
def tmplM5 : KTmplC := ⟨1/264,32,cells5,headsM5,5⟩
def bankM : KBankDataC := { header 1 5 with tmpls := [(1,tmplM1),(5,tmplM5)] }

end CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118

#print axioms CatalanCore.Uniform.Bank.Plane1.Dips.Data.Content118.bankM
