module
public import CatalanCore.Uniform.Frame.NVAdapter
@[expose] public section

namespace CatalanCore.Uniform
open Finset

namespace BlockCollection

def commonPeriod (B : BlockCollection) : ℕ := ∏ i, (B.block i).d

theorem commonPeriod_pos (B : BlockCollection) : 0 < B.commonPeriod :=
  Finset.prod_pos fun i _ => (B.block i).hd

theorem dvd_commonPeriod (B : BlockCollection) (i : Fin B.n) :
    (B.block i).d ∣ B.commonPeriod := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

end BlockCollection

namespace BlockGeom

/-- A completely explicit common step. A smaller common multiple can be used
with hasNV0; the product suffices for unconditional fixed-geometry existence. -/
def commonStep (G : BlockGeom) : ℕ :=
  G.common.commonPeriod * G.row.commonPeriod * G.column.commonPeriod

theorem commonStep_pos (G : BlockGeom) : 0 < G.commonStep :=
  Nat.mul_pos (Nat.mul_pos G.common.commonPeriod_pos G.row.commonPeriod_pos)
    G.column.commonPeriod_pos

theorem common_dvd_step (G : BlockGeom) (i : Fin G.common.n) :
    (G.common.block i).d ∣ G.commonStep :=
  dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (G.common.dvd_commonPeriod i) _) _

theorem row_dvd_step (G : BlockGeom) (i : Fin G.row.n) :
    (G.row.block i).d ∣ G.commonStep :=
  dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (G.row.dvd_commonPeriod i) _) _

theorem column_dvd_step (G : BlockGeom) (i : Fin G.column.n) :
    (G.column.block i).d ∣ G.commonStep :=
  dvd_mul_of_dvd_right (G.column.dvd_commonPeriod i) _

/-- Every fixed positive-common-density periodic block geometry has an actual
bounded-depth characteristic-zero selector. The step and depth are constructed
from its finite data; there is no nonvanishing or component-count assumption. -/
theorem exists_depth_hasNV0 (G : BlockGeom) (Fr : Frame)
    (hd : 1 ≤ Fr.d) (hw : ∀ i, Fr.w i ≠ 0) :
    ∃ depth : ℕ, HasNV0 (G.family Fr depth) G.scale := by
  refine ⟨G.selectionDepth Fr G.commonStep, ?_⟩
  exact G.hasNV0 Fr G.commonStep _ G.commonStep_pos hd hw
    G.common_dvd_step G.row_dvd_step G.column_dvd_step le_rfl

#print axioms exists_depth_hasNV0
end BlockGeom
end CatalanCore.Uniform
