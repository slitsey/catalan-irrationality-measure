module
public import CatalanFrames.HybGen.FamilySum
public import CatalanCore.Arith.Hybrid.PeriodicPrefix
@[expose] public section
namespace CatalanFrames.HybGen
open CatalanCore.Arith.Hybrid
/-- Optional periodic cap: arbitrary class predicate, period and phase. -/
def periodicRefine (Good : ℕ → Prop) [DecidablePred Good]
    (period phase : ℕ → ℕ → ℕ → ℕ) (w : ℕ → ℕ → ℕ → ℕ) (r m p : ℕ) : ℕ :=
  if Good p then min (w r m p)
    (2*r+2*m-min (phase r m p % period r m p)
      (period r m p-phase r m p % period r m p)) else w r m p
lemma periodicRefine_le (Good : ℕ → Prop) [DecidablePred Good]
    (period phase w : ℕ → ℕ → ℕ → ℕ) (r m p : ℕ) :
    periodicRefine Good period phase w r m p ≤ w r m p := by
  unfold periodicRefine
  split_ifs <;> omega
lemma periodicRefine_exact {Good : ℕ → Prop} [DecidablePred Good]
    (period phase w : ℕ → ℕ → ℕ → ℕ) (r m p : ℕ) (hg : Good p) :
    periodicRefine Good period phase w r m p ≤
      2*r+2*m-min (phase r m p % period r m p)
        (period r m p-phase r m p % period r m p) := by
  simp only [periodicRefine, if_pos hg]
  exact Nat.min_le_right _ _
lemma covers_periodicRefine {Good : ℕ → Prop} [DecidablePred Good]
    (period phase w : ℕ → ℕ → ℕ → ℕ) {M r m : ℕ} {c : ZMod M} {P : Piece}
    (h : Covers c (fun p => (w r m p : ℝ)) r P) :
    Covers c (fun p => (periodicRefine Good period phase w r m p : ℝ)) r P := by
  intro p hlo hhi hp hc
  have hl : (periodicRefine Good period phase w r m p : ℝ) ≤ (w r m p : ℝ) :=
    by exact_mod_cast periodicRefine_le Good period phase w r m p
  exact hl.trans (h p hlo hhi hp hc)
#print axioms periodicRefine_le
#print axioms covers_periodicRefine
end CatalanFrames.HybGen
