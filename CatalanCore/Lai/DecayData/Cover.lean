module

public import CatalanCore.Lai.DecayData.Cells00
public import CatalanCore.Lai.DecayData.Cells01
public import CatalanCore.Lai.DecayData.Cells02

@[expose] public section

open CatalanCore.Lai.DecayCheck CatalanCore.Lai.DecayData

namespace CatalanCore.Lai.DecayData

noncomputable section

theorem forall_nil {α : Type*} {P : α → Prop} : ∀ d ∈ ([] : List α), P d := by simp

theorem forall_cons {α : Type*} {P : α → Prop} {a : α} {l : List α} (h : P a) (t : ∀ d ∈ l, P d) :
    ∀ d ∈ a :: l, P d := by
  intro d hd
  rcases List.mem_cons.1 hd with rfl | hd
  · exact h
  · exact t d hd

-- kcost: ~0.05 s estimated (chain checks over 26 + 9 + 1 + 4 rational pairs)
theorem cover_ok : coverOK cA00 [cA01, cA02, cA03, cA04, cA05, cA06, cA07, cA08, cA09, cA10, cA11, cA12, cA13, cA14, cA15, cA16, cA17, cA18, cA19, cA20, cA21, cA22, cA23, cA24, cA25] cG00 [cG01, cG02, cG03, cG04, cG05, cG06, cG07, cG08] cH00 [] cR00 [cR01, cR02, cR03] = true := by decide +kernel

/-- **The Lai decay cover**: `LaiCover laiC 8 laiEll (146127/500000) (459681/10^6)`, all 40 cells checked. -/
theorem laiCover_all :
    DecayInstance.LaiCover DecayGlue.laiC 8 DecayInstance.laiEll (146127 / 500000) (459681 / 1000000) :=
  laiCover_of_data cA00 [cA01, cA02, cA03, cA04, cA05, cA06, cA07, cA08, cA09, cA10, cA11, cA12, cA13, cA14, cA15, cA16, cA17, cA18, cA19, cA20, cA21, cA22, cA23, cA24, cA25] cG00 [cG01, cG02, cG03, cG04, cG05, cG06, cG07, cG08] cH00 [] cR00 [cR01, cR02, cR03] cover_ok
    (forall_cons (cA00_ok) (forall_cons (cA01_ok) (forall_cons (cA02_ok) (forall_cons (cA03_ok) (forall_cons (cA04_ok) (forall_cons (cA05_ok) (forall_cons (cA06_ok) (forall_cons (cA07_ok) (forall_cons (cA08_ok) (forall_cons (cA09_ok) (forall_cons (cA10_ok) (forall_cons (cA11_ok) (forall_cons (cA12_ok) (forall_cons (cA13_ok) (forall_cons (cA14_ok) (forall_cons (cA15_ok) (forall_cons (cA16_ok) (forall_cons (cA17_ok) (forall_cons (cA18_ok) (forall_cons (cA19_ok) (forall_cons (cA20_ok) (forall_cons (cA21_ok) (forall_cons (cA22_ok) (forall_cons (cA23_ok) (forall_cons (cA24_ok) (forall_cons (cA25_ok) (forall_nil)))))))))))))))))))))))))))
    (forall_cons ⟨cG00_ok, cG00_sg⟩ (forall_cons ⟨cG01_ok, cG01_sg⟩ (forall_cons ⟨cG02_ok, cG02_sg⟩ (forall_cons ⟨cG03_ok, cG03_sg⟩ (forall_cons ⟨cG04_ok, cG04_sg⟩ (forall_cons ⟨cG05_ok, cG05_sg⟩ (forall_cons ⟨cG06_ok, cG06_sg⟩ (forall_cons ⟨cG07_ok, cG07_sg⟩ (forall_cons ⟨cG08_ok, cG08_sg⟩ (forall_nil))))))))))
    (forall_cons ⟨cH00_ok, cH00_sg⟩ (forall_nil))
    (forall_cons (cR00_ok) (forall_cons (cR01_ok) (forall_cons (cR02_ok) (forall_cons (cR03_ok) (forall_nil)))))

end

end CatalanCore.Lai.DecayData
