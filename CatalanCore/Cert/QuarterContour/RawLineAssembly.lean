module
public import CatalanCore.Cert.QuarterContour.RawRayAssembly
@[expose] public section
namespace CatalanCore.Cert.QuarterContour.RawLineAssembly
open CatalanCore.Cert.SigmaP6 CatalanCore.Cert.SigmaQuarter

def AxisMacroFacts (pts : List Pt) (ms : List Macro) : Prop :=
  ∀ m ∈ ms, farOK pts m ∧ axisOK pts m = true

lemma facts_nil (pts : List Pt) : AxisMacroFacts pts [] := by intro m hm;cases hm
lemma facts_cons (pts : List Pt) (m : Macro) (ms : List Macro)
    (hf : farOK pts m) (ho : axisOK pts m = true) (ht : AxisMacroFacts pts ms) :
    AxisMacroFacts pts (m::ms) := by
  intro n hn
  rcases List.mem_cons.mp hn with he | hn
  · subst n;exact ⟨hf,ho⟩
  · exact ht n hn

lemma forall_flatten {α : Type} (P : α → Prop) (css : List (List α))
    (hf : ∀ cs ∈ css, ∀ x ∈ cs, P x) : ∀ x ∈ css.flatten, P x := by
  intro x hx
  obtain ⟨cs,hcs,hx⟩ := List.mem_flatten.mp hx
  exact hf cs hcs x hx

lemma facts_flatten (pts : List Pt) (css : List (List Macro))
    (hf : ∀ cs ∈ css, AxisMacroFacts pts cs) : AxisMacroFacts pts css.flatten := by
  exact forall_flatten _ css hf

def LineCellsSound (epsilon gm : ℚ) (pts : List Pt) (bs : List QBox) : Prop :=
  ∀ b ∈ bs, ∀ x : ℝ, ((axisInterval b).1 : ℝ) ≤ x → x ≤ ((axisInterval b).2 : ℝ) →
    (gm : ℝ) ≤ gQuarter epsilon pts x 0

lemma cells_sound (epsilon gm : ℚ) (pts : List Pt) (ms : List Macro) (bs : List QBox)
    (heq : boxes ms = bs) (hf : AxisMacroFacts pts ms)
    (hg : ∀ b ∈ bs, lineShape gm b) : LineCellsSound epsilon gm pts bs := by
  intro b hb x h1 h2
  have hbm : b ∈ boxes ms := by rw [heq];exact hb
  have hs := axis_gQuarter pts epsilon ms (fun m hm => (hf m hm).1)
    (fun m hm => (hf m hm).2) b hbm x
  have hgamma : (gm : ℝ) ≤ (gamma b : ℝ) := Rat.cast_le.mpr (hg b hb).2
  apply hgamma.trans
  apply hs
  · simpa only [axisInterval,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_ofNat] using h1
  · simpa only [axisInterval,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_ofNat] using h2

lemma sound_flatten (epsilon gm : ℚ) (pts : List Pt) (css : List (List QBox))
    (hf : ∀ cs ∈ css, LineCellsSound epsilon gm pts cs) :
    LineCellsSound epsilon gm pts css.flatten := forall_flatten _ css hf

example : chainCovers [(0,1/2),(1/2,1)] 0 1 = true := by decide +kernel
example : lineShape (-28907/20000) (((0,2^40,0,0),(0,2^40,0,0)) : QBox) := by decide +kernel
end CatalanCore.Cert.QuarterContour.RawLineAssembly
#print axioms CatalanCore.Cert.QuarterContour.RawLineAssembly.cells_sound