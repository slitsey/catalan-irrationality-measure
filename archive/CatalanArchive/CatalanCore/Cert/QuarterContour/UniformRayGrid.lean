module
public import CatalanCore.Cert.SigmaQuarter.Cover
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.UniformRayGrid
open CatalanCore.Cert.SigmaQuarter

/-- A symbolic endpoint: using this definition never enumerates the grid. -/
def point (N : ℕ) (U : ℚ) (k : ℕ) : ℚ := (k : ℚ)*U/(N : ℚ)
def cell (N : ℕ) (U : ℚ) (k : ℕ) : ℚ × ℚ := (point N U k,point N U (k+1))
def gridPrefix (N : ℕ) (U : ℚ) (K : ℕ) : List (ℚ × ℚ) :=
  (List.range K).map (cell N U)
def intervals (N : ℕ) (U : ℚ) : List (ℚ × ℚ) := gridPrefix N U N

lemma point_zero (N : ℕ) (U : ℚ) : point N U 0 = 0 := by simp [point]
lemma point_last (N : ℕ) (U : ℚ) (hN : 0 < N) : point N U N = U := by
  have hNR : (N : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  unfold point
  field_simp [hNR]

lemma singleton_covers (N : ℕ) (U : ℚ) (k : ℕ) :
    IntervalCovers [cell N U k] (point N U k) (point N U (k+1)) := by
  intro x hx hy
  exact ⟨cell N U k,by simp,hx,hy⟩

/-- Symbolic induction on the gridPrefix length, rather than evaluation of a Boolean cover. -/
lemma prefix_covers (N : ℕ) (U : ℚ) (k : ℕ) :
    IntervalCovers (gridPrefix N U (k+1)) 0 (point N U (k+1)) := by
  induction k with
  | zero =>
    simpa [gridPrefix,point_zero] using singleton_covers N U 0
  | succ k ih =>
    have hh := intervalCovers_append ih (singleton_covers N U (k+1)) (le_refl _)
    simpa only [gridPrefix,List.range_succ,List.map_append,List.map_singleton] using hh

/-- The enormous uniform grid is proved to cover without constructing any of its cells. -/
theorem covers (N : ℕ) (U : ℚ) (hN : 0 < N) :
    IntervalCovers (intervals N U) 0 U := by
  cases N with
  | zero => omega
  | succ k =>
    have hh := prefix_covers (k+1) U k
    rw [point_last (k+1) U (by omega)] at hh
    exact hh

theorem mem_iff (N : ℕ) (U : ℚ) (p : ℚ × ℚ) :
    p ∈ intervals N U ↔ ∃ k < N, p = cell N U k := by
  constructor
  · intro hp
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hp
    exact ⟨k,List.mem_range.mp hk,rfl⟩
  · rintro ⟨k,hk,rfl⟩
    exact List.mem_map.mpr ⟨k,List.mem_range.mpr hk,rfl⟩

theorem bounds (N : ℕ) (U : ℚ) (hN : 0 < N) (hU : 0 ≤ U)
    (p : ℚ × ℚ) (hp : p ∈ intervals N U) :
    0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ U := by
  obtain ⟨k,hk,rfl⟩ := (mem_iff N U p).mp hp
  have hNR : (0 : ℚ) < N := by exact_mod_cast hN
  have hkR : (k : ℚ) ≤ (k+1 : ℕ) := by exact_mod_cast (Nat.le_succ k)
  have hknR : ((k+1 : ℕ) : ℚ) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hk)
  change 0 ≤ (k : ℚ)*U/(N : ℚ) ∧
    (k : ℚ)*U/(N : ℚ) ≤ ((k+1 : ℕ) : ℚ)*U/(N : ℚ) ∧
    ((k+1 : ℕ) : ℚ)*U/(N : ℚ) ≤ U
  refine ⟨by positivity,?_,?_⟩
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hkR hU) hNR.le
  · apply (div_le_iff₀ hNR).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right hknR hU

theorem width (N : ℕ) (U : ℚ) (p : ℚ × ℚ) (hp : p ∈ intervals N U) :
    p.2-p.1 = U/(N : ℚ) := by
  obtain ⟨k,hk,rfl⟩ := (mem_iff N U p).mp hp
  simp only [cell,point,Nat.cast_add,Nat.cast_one]
  ring

theorem length (N : ℕ) (U : ℚ) : (intervals N U).length = N := by
  simp only [intervals,gridPrefix,List.length_map,List.length_range]
end CatalanCore.Cert.QuarterContour.UniformRayGrid
#print axioms CatalanCore.Cert.QuarterContour.UniformRayGrid.covers
#print axioms CatalanCore.Cert.QuarterContour.UniformRayGrid.bounds
