module
public import CatalanCore.Li2.DecayCert.TableSimple
public import CatalanCore.Li2.DecayCert.Lattice.Gates.Energy
/-! Assembly of the SIMPLE data checks: a side's check from one check per cell. -/
@[expose] public section
namespace CatalanCore.Li2.DecayCert.Simple
open CatalanCore.Li2.DecayCert.LatticeSimple

/-- A side whose structure passes and whose every cell passes `ok` passes `Side.check ok`. -/
theorem side_check_of (ok : WCell → Bool) (a b : ℚ) (w : Side) (cells : List WCell)
    (hcells : w.away.flatten++w.roots=cells) (hok : ∀ c ∈ cells,ok c=true)
    (hs : w.check (fun _ => true) a b=true) : w.check ok a b=true := by
  subst hcells
  unfold Side.check at hs ⊢
  simp only [Bool.and_eq_true,List.all_eq_true,List.mem_range] at hs ⊢
  obtain ⟨⟨⟨hp,hd⟩,ha⟩,hr⟩ := hs
  refine ⟨⟨⟨hp,hd⟩,fun i hi => ?_⟩,fun i hi => ?_⟩
  · have h := ha i hi
    cases hcs : w.away[i]? with
    | none => rw [hcs] at h; exact absurd h (by simp)
    | some cs =>
      rw [hcs] at h
      simp only [Bool.and_eq_true,List.all_eq_true,Bool.true_and] at h ⊢
      refine ⟨h.1,fun c hc => ⟨hok c (List.mem_append_left _ (List.mem_flatten.2 ⟨cs,List.mem_of_getElem? hcs,hc⟩)),h.2 c hc⟩⟩
  · have h := hr i hi
    cases hc : w.roots[i]? with
    | none => rw [hc] at h; exact absurd h (by simp)
    | some c =>
      rw [hc] at h
      simp only [Bool.and_eq_true,Bool.true_and] at h ⊢
      exact ⟨hok c (List.mem_append_right _ (List.mem_of_getElem? hc)),h⟩

end CatalanCore.Li2.DecayCert.Simple
