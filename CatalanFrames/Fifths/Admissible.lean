module
public import CatalanFrames.Fifths.ContourInstances
@[expose] public section
namespace CatalanFrames.Fifths
def FifthsAdm (r m : ℕ) : Prop := r ≤ 8*m ∧ 8*m ≤ r+9
theorem adm_exists (r : ℕ) (hr : 1 ≤ r) : ∃ m, FifthsAdm r m :=
  ⟨(r+7)/8,by unfold FifthsAdm;omega⟩
theorem adm_window (r m : ℕ) (hm : FifthsAdm r m) :
    (1/8 : ℝ)*r ≤ m ∧ (m : ℝ) ≤ (1/8 : ℝ)*r+9/8 := by
  have h1 : (r : ℝ) ≤ 8*m := by exact_mod_cast hm.1
  have h2 : (8*m : ℝ) ≤ r+9 := by exact_mod_cast hm.2
  push_cast at h1 h2
  constructor <;> linarith
end CatalanFrames.Fifths
#print axioms CatalanFrames.Fifths.adm_exists
#print axioms CatalanFrames.Fifths.adm_window
