module

public import CatalanCore.Uniform.Content.UFMoments.FibTransport
public import CatalanCore.Uniform.Content.UFMoments.DirOf

@[expose] public section

/-!
# (S7-Lean) for two-term frames: the `J`-block datum of a joint type

* `TypeData.fibMom_eq`: along a joint type the fiber moment at the node residue is the same as at
  the representative (transport modulo `p`);
* `wT_window`: the cyclic step is constant across a nonsingular window;
* `s7_twoTerm`: for a two-term frame, a representative border node `t₀` (with `B₀ ≠ 0`) and border
  rows / columns `t₀ + Δ` whose own chains are the shifted chain of `t₀` with nonsingular windows,
  the `JBlockKill` datum of the divided Schur complement exists, with derived weights
  `v(c) = norm · (wT(c)/norm - C₀ - m(c))` (cyclic step minus fiber moment, normalised to vanish
  on the type).
-/

open Polynomial Matrix Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.Periodic CatalanCore.Uniform.Content.UFMember
  CatalanCore.Uniform.Content.Hybrid CatalanCore.Uniform.Content.Smith

namespace CatalanCore.Uniform.Content.UFMoments

variable {p N : ℕ} [Fact p.Prime] {Fr : Frame} {ι κ : Type} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

theorem TypeData.fibMom_eq (D : PoleData Fr p N) (c : ι → ℕ) (hc : ∀ a, c a < N)
    (Q : Matrix ι ι (LocRing p)[X])
    (hQ : ∀ a b, a ≠ b → nL p Fr * (nd p (c b) - nd p (c a)) * Q a b =
      PF p Fr (c b) - PF p Fr (c a))
    (hdet : phiP p Q.det ≠ 0) (t0 : ℕ) (σ0 : ι → (LocRing p)[X]) (K0 : RatFunc (ZMod p))
    (W : ZMod p → RatFunc (ZMod p)) (t : ℕ) (σ : ι → (LocRing p)[X]) (d : GaussLoc p)
    (hT : TypeData Fr c Q t0 σ0 K0 W t σ) :
    fibMom c (Dmat c Q) (fun a => ellL p Fr (c a) - d) ((t : ℕ) : ZMod p) =
      fibMom c (Dmat c Q) (fun a => ellL p Fr (c a) - d) ((t0 : ℕ) : ZMod p) := by
  obtain ⟨e, κ₁, hDD, -, hℓ, hκ, -⟩ := hT
  have hDu := isUnit_Dmat_det D c hc Q hQ hdet
  have hb : ∀ a b, colOf (p := p) c a ≠ colOf c b → Dmat c Q a b = 0 := by
    intro a b h; simp [Dmat, h]
  refine fiber_moment_transport (Dmat c Q) (colOf c) hDu hb _ _ e _ (res p) ?_ ?_
  · intro i j
    obtain ⟨x, hx⟩ := hDD i j
    have h1 : colOf (p := p) c (e.symm i).1 = colOf c (e.symm j).1 :=
      ((e.symm i).2).trans ((e.symm j).2).symm
    have h2 : colOf (p := p) c i.1 = colOf c j.1 := i.2.trans j.2.symm
    simp only [Dmat, Matrix.of_apply, h1, h2, ↓reduceIte]
    rw [hx, map_add, map_mul, map_pow, res_piL, zero_pow two_ne_zero, zero_mul, add_zero]
  · intro i
    obtain ⟨x, hx⟩ := hℓ i
    rw [hx, hκ, map_sub, map_sub, map_add, map_add, map_mul, map_mul, map_pow, res_piL,
      zero_pow two_ne_zero, zero_mul, zero_mul, add_zero, add_zero]

theorem wT_window {q o N : ℕ} (T : TwoTermData Fr q o) (hN : N ≤ p * p)
    (hsq : ∀ t, 1 ≤ t → t < N → ¬ p ^ 2 ∣ q * t - o) (hnorm : Fr.norm ∈ S p)
    (hnorm0 : red p Fr.norm ≠ 0) (ho : (o : ZMod p) ≠ 0) (hq : (q : ZMod p) ≠ 0)
    (t0 Δ : ℕ) (hb : t0 + Δ < N) (hw : NoSingWin (twoTermPoleData T hN hsq hnorm hnorm0) t0 Δ) :
    wT p q o ((t0 + Δ : ℕ) : ZMod p) = wT p q o ((t0 : ℕ) : ZMod p) := by
  suffices h : ∀ n, n ≤ Δ → wT p q o ((t0 + n : ℕ) : ZMod p) = wT p q o ((t0 : ℕ) : ZMod p) from
    h Δ le_rfl
  intro n
  induction n with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hs := hw (t0 + m + 1) (by omega) (by omega)
    have h1 : ¬ (p ∣ (t0 + m + 1) ∨ p ∣ q * (t0 + m + 1) - o) :=
      fun h => hs ((ttSing_nat T (by omega)).2 h)
    push Not at h1
    have hk : (((t0 + m + 1 : ℕ)) : ZMod p) ≠ 0 := natCast_ne_zero_of_not_dvd h1.1
    have hk' : (((q * (t0 + m + 1) - o : ℕ)) : ZMod p) ≠ 0 := natCast_ne_zero_of_not_dvd h1.2
    have hle : o ≤ q * (t0 + m + 1) := by have := T.o_lt; nlinarith
    rw [Nat.cast_sub hle] at hk'
    push_cast at hk hk'
    have hnp : ((t0 + m : ℕ) : ZMod p) ∉ ttPoles p q o := by
      unfold ttPoles
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      push_cast
      constructor
      · intro h; apply hk; rw [h]; ring
      · intro h
        apply hk'
        have e : (t0 : ZMod p) + m + 1 = (o : ZMod p) * (q : ZMod p)⁻¹ := by rw [h]; ring
        rw [e]; field_simp; ring
    rw [show t0 + (m + 1) = (t0 + m) + 1 by ring]
    have e : (((t0 + m + 1 : ℕ)) : ZMod p) = ((t0 + m : ℕ) : ZMod p) + 1 := by push_cast; ring
    rw [e, wT, prim_succ _ (sum_ttJump q o ho hq), ← wT, ih (by omega), ttJump, if_neg hnp]
    ring

end CatalanCore.Uniform.Content.UFMoments
