module
public import CatalanCore.Cert.QuarterContour.RayCellCover
@[expose] public section
namespace CatalanCore.Cert.QuarterContour
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

/-- Aggregate the already checked arithmetic leaves without evaluating them again. -/
def RayMacroFacts (epsilon mp : ℚ) (pts : List Pt) (ms : List Macro) : Prop :=
  ∀ m ∈ ms, farOK pts m ∧ rayOK epsilon pts mp m = true

theorem rayMacroFacts_nil (epsilon mp : ℚ) (pts : List Pt) :
    RayMacroFacts epsilon mp pts [] := by
  intro m hm
  cases hm

theorem rayMacroFacts_cons (epsilon mp : ℚ) (pts : List Pt) (m : Macro) (ms : List Macro)
    (hf : farOK pts m) (ho : rayOK epsilon pts mp m = true)
    (ht : RayMacroFacts epsilon mp pts ms) :
    RayMacroFacts epsilon mp pts (m::ms) := by
  intro n hn
  rcases List.mem_cons.mp hn with he | hm
  · subst n
    exact ⟨hf,ho⟩
  · exact ht n hm

/-- Existing raw macros plus their geometry cover the actual sloping tube. -/
theorem ray_macros_cover_sound (epsilon mp sl r0 W lo hi : ℚ)
    (he : epsilon ≤ 1/1000) (hsl : 0 < sl) (pts : List Pt) (ms : List Macro)
    (hf : RayMacroFacts epsilon mp pts ms)
    (hshape : ∀ b ∈ boxes ms, rayShape sl r0 W b)
    (hcover : IntervalCovers ((boxes ms).map (rayInterval sl)) lo hi)
    (u delta : ℝ) (hu : (lo : ℝ) ≤ u) (hU : u ≤ (hi : ℝ)) (hd : |delta| ≤ (W : ℝ)) :
    (mp : ℝ) ≤ gQuarter epsilon pts (-(r0 : ℝ)+delta-u) ((sl : ℝ)*u) := by
  apply ray_cells_cover_sound (gQuarter epsilon pts) sl r0 W lo hi mp hsl
    (boxes ms) hshape hcover ?_ u delta hu hU hd
  intro b hb v d hdelta h1 h2 h3 h4
  change b ∈ ms.flatMap Macro.boxes at hb
  obtain ⟨m,hm,hb⟩ := List.mem_flatMap.mp hb
  exact rayMacro_sound epsilon he pts mp m (hf m hm).1 (hf m hm).2 b hb _ _ h1 h2 h3 h4

/-- A small list of chunk intervals is enough for the final full-ray assembly. -/
def RayChunkBound (epsilon mp sl r0 W : ℚ) (pts : List Pt) (p : ℚ × ℚ) : Prop :=
  ∀ u delta : ℝ, (p.1 : ℝ) ≤ u → u ≤ (p.2 : ℝ) → |delta| ≤ (W : ℝ) →
    (mp : ℝ) ≤ gQuarter epsilon pts (-(r0 : ℝ)+delta-u) ((sl : ℝ)*u)

theorem forall_mem_nil {α : Type} (P : α → Prop) : ∀ x ∈ ([] : List α), P x := by
  intro x hx
  cases hx

theorem forall_mem_cons {α : Type} (P : α → Prop) (a : α) (as : List α)
    (ha : P a) (ht : ∀ x ∈ as, P x) : ∀ x ∈ a::as, P x := by
  intro x hx
  rcases List.mem_cons.mp hx with he | hx
  · subst x
    exact ha
  · exact ht x hx

theorem ray_chunks_cover_sound (epsilon mp sl r0 W lo hi : ℚ) (pts : List Pt)
    (ps : List (ℚ × ℚ)) (hb : ∀ p ∈ ps, RayChunkBound epsilon mp sl r0 W pts p)
    (hc : IntervalCovers ps lo hi) (u delta : ℝ)
    (hu : (lo : ℝ) ≤ u) (hU : u ≤ (hi : ℝ)) (hd : |delta| ≤ (W : ℝ)) :
    (mp : ℝ) ≤ gQuarter epsilon pts (-(r0 : ℝ)+delta-u) ((sl : ℝ)*u) := by
  obtain ⟨p,hp,h1,h2⟩ := hc u hu hU
  exact hb p hp u delta h1 h2 hd
end CatalanCore.Cert.QuarterContour
#print axioms CatalanCore.Cert.QuarterContour.ray_macros_cover_sound
#print axioms CatalanCore.Cert.QuarterContour.ray_chunks_cover_sound
