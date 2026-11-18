module
public import CatalanCore.Li2.DecayCert.Compile.Defs
@[expose] public section
set_option Elab.async false
open Polynomial MeasureTheory Set Filter Topology
open scoped BigOperators
namespace CatalanCore.Li2.DecayCert
def linePos (a b R κ : ℚ) : ℚ :=
  let f0 := a-κ
  let f1 := a+b*R-κ
  if 0 ≤ f0 ∧ 0 ≤ f1 then (f0+f1)*R/2
  else if 0 < f0 ∧ f1 < 0 then f0^2*R/(2*(f0-f1))
  else if 0 < f1 ∧ f0 < 0 then f1^2*R/(2*(f1-f0)) else 0

structure LineCell where
  start : ℚ
  len : ℚ
  dir : ℚ
  a : ℚ
  b : ℚ
  len_nonneg : 0 ≤ len
  direction : dir=1 ∨ dir= -1
noncomputable def LineCell.support (c : LineCell) : Set ℝ :=
  (fun u : ℝ => (c.start:ℝ)+(c.dir:ℝ)*u) '' Icc 0 (c.len:ℝ)
structure LinePartition (α β : ℝ) where
  cells : List LineCell
  nodup : cells.Nodup
  cover : (⋃ c ∈ cells, c.support) = Icc α β
  overlap_null : ∀ c ∈ cells, ∀ d ∈ cells, c ≠ d → volume (c.support ∩ d.support)=0
noncomputable def linePosR (a b R κ : ℝ) : ℝ :=
  let f0 := a-κ
  let f1 := a+b*R-κ
  if 0 ≤ f0 ∧ 0 ≤ f1 then (f0+f1)*R/2
  else if 0 < f0 ∧ f1 < 0 then f0^2*R/(2*(f0-f1))
  else if 0 < f1 ∧ f0 < 0 then f1^2*R/(2*(f1-f0)) else 0
def LinePartition.posSumQ {α β : ℝ} (C : LinePartition α β) (ρ lam : ℚ) : ℚ :=
  (C.cells.map (fun c => linePos c.a c.b c.len (ρ+lam))).sum
noncomputable def LinePartition.posSum {α β : ℝ} (C : LinePartition α β) (ρ lam : ℝ) : ℝ :=
  (C.cells.map (fun c => linePosR c.a c.b c.len (ρ+lam))).sum
theorem linePos_cast (a b R κ : ℚ) :
    (linePos a b R κ:ℝ)=linePosR a b R κ := by
  unfold linePos linePosR
  dsimp only
  push_cast
  norm_cast
  split_ifs <;> simp only [Rat.cast_zero]
theorem posSum_cast {α β : ℝ} (C : LinePartition α β) (ρ lam : ℚ) :
    (C.posSumQ ρ lam:ℝ)=C.posSum ρ lam := by
  unfold LinePartition.posSumQ LinePartition.posSum
  push_cast
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  simp only [Function.comp_apply,linePos_cast,Rat.cast_add]
#print axioms linePos_cast
#print axioms posSum_cast
end CatalanCore.Li2.DecayCert
