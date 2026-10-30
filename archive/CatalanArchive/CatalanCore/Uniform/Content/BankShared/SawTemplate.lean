import CatalanCore.Uniform.Content.BankShared.SawPrefix
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace CatalanCore.Uniform.Content.BankShared.SawPrefix
open CatalanCore.Arith.Hybrid CatalanCore.Uniform.Content.Member

theorem chain_append : ∀ (l r : List Piece) (s : ℝ),
    Chain s (l ++ r) ↔ Chain s l ∧ Chain (lastEnd s l) r
  | [], r, s => by simp [Chain, lastEnd]
  | p :: l, r, s => by
    simp only [List.cons_append, Chain, lastEnd]
    rw [chain_append l r p.t]
    tauto

theorem lastEnd_append : ∀ (l r : List Piece) (s : ℝ),
    lastEnd s (l ++ r) = lastEnd (lastEnd s l) r
  | [], r, s => by simp [lastEnd]
  | p :: l, r, s => by
    simp only [List.cons_append, lastEnd]
    exact lastEnd_append l r p.t

theorem pair_end (a C s : ℝ) (n : ℕ) : lastEnd s (pair a C n) = a / n := rfl

theorem pair_chain (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C) (n : ℕ) (hn : 0 < n) :
    Chain (a / ((n : ℝ) + 1)) (pair a C n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hn2 : 0 < 2 * (n : ℝ) + 1 := by positivity
  have hl : a / ((n : ℝ) + 1) ≤ 2 * a / (2 * (n : ℝ) + 1) := by
    apply (div_le_div_iff₀ hn1 hn2).2
    nlinarith
  have hr : 2 * a / (2 * (n : ℝ) + 1) ≤ a / n := by
    apply (div_le_div_iff₀ hn2 hn0).2
    nlinarith
  have hfrac : a / (2 * (n : ℝ) + 1) ≤ a := by
    apply (div_le_iff₀ hn2).2
    nlinarith
  have hmid : 0 ≤ 2 + 2 * a - a / (2 * (n : ℝ) + 1) := by linarith
  have hleft : 2 + 3 * a + (-((n : ℝ) + 1)) * (a / ((n : ℝ) + 1)) = 2 + 2 * a := by
    field_simp
    <;> ring
  have hm1 : 2 + 3 * a + (-((n : ℝ) + 1)) * (2 * a / (2 * (n : ℝ) + 1)) =
      2 + 2 * a - a / (2 * (n : ℝ) + 1) := by
    field_simp
    <;> ring
  have hm2 : 2 + a + (n : ℝ) * (2 * a / (2 * (n : ℝ) + 1)) =
      2 + 2 * a - a / (2 * (n : ℝ) + 1) := by
    field_simp
    <;> ring
  have hright : 2 + a + (n : ℝ) * (a / n) = 2 + 2 * a := by
    field_simp
    <;> ring
  simp only [pair, Chain]
  exact ⟨trivial, div_pos ha hn1, hl, hC, by rw [hleft]; linarith,
    by rw [hm1]; exact hmid, trivial, div_pos (by positivity) hn2, hr, hC,
    by rw [hm2]; exact hmid, by rw [hright]; linarith, trivial⟩

theorem pieces_end (a C : ℝ) (n : ℕ) :
    lastEnd (a / ((n : ℝ) + 1)) (pieces a C n) = a := by
  induction n with
  | zero => simp [pieces, lastEnd]
  | succ n ih =>
    rw [pieces, lastEnd_append, pair_end]
    simpa only [Nat.cast_add, Nat.cast_one] using ih

theorem pieces_chain (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C) (n : ℕ) :
    Chain (a / ((n : ℝ) + 1)) (pieces a C n) := by
  induction n with
  | zero => simp [pieces, Chain]
  | succ n ih =>
    rw [pieces, chain_append]
    refine ⟨?_, ?_⟩
    · simpa only [Nat.cast_add, Nat.cast_one] using pair_chain a C ha hC (n + 1) (by omega)
    · rw [pair_end]
      simpa only [Nat.cast_add, Nat.cast_one] using ih

noncomputable def appendTemplate (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (n : ℕ) (l : List Piece) (hl : Chain a l) : Template where
  α0 := 2 + 2 * a
  t1 := a / ((n : ℝ) + 1)
  l := pieces a C n ++ l
  hα0 := by linarith
  ht1 := div_pos ha (by positivity)
  chain := (chain_append _ _ _).2
    ⟨pieces_chain a C ha hC n, by rw [pieces_end]; exact hl⟩

theorem appendTemplate_mass (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (n : ℕ) (l : List Piece) (hl : Chain a l) :
    (appendTemplate a C ha hC n l hl).mass =
      (2 + 2 * a) * (a / ((n : ℝ) + 1)) + listInt (pieces a C n) + listInt l := by
  simp only [Template.mass, appendTemplate, listInt_append]
  ring

theorem appendTemplate_end (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (n : ℕ) (l : List Piece) (hl : Chain a l) :
    (appendTemplate a C ha hC n l hl).tend = lastEnd a l := by
  simp only [Template.tend, appendTemplate, lastEnd_append, pieces_end]

theorem exists_template_mass (a C : ℝ) (ha : 0 < a) (hC : 0 ≤ C)
    (l : List Piece) (hl : Chain a l) (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, (appendTemplate a C ha hC n l hl).mass ≤
      2 * a + a ^ 2 / 2 + 2 * a ^ 2 * Real.log 2 + listInt l + ε := by
  obtain ⟨n, hn⟩ := exists_mass_slack a C ε hε
  refine ⟨n, ?_⟩
  rw [appendTemplate_mass]
  linarith

#print axioms pieces_chain
#print axioms exists_template_mass
end CatalanCore.Uniform.Content.BankShared.SawPrefix
