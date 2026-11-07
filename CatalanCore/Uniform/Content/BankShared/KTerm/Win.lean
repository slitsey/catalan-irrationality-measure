module

public import CatalanCore.Uniform.Content.BankShared.KTerm.Trop
public import CatalanCore.Uniform.Content.BankShared.KTerm.Prefix
public import CatalanCore.Uniform.Content.BankShared.Check.Layers
public import CatalanCore.Uniform.Content.BankShared.TwoTerm.Prefix

@[expose] public section
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # Windows over a pole bundle (wave H1)

The generic bodies of the `chi_{-3}` window lemmas, for a `KBundle B` with shifts `(3, ρ)`, `(2, 1)`:

* `lat_gap`: an integer strictly between consecutive points of `A + x + p ℤ` is not in the lattice;
* `KBundle.cutfree`: a window `(a, b)` lying between consecutive points of each of the three lattices `p ℤ`,
  `k_A + p ℤ`, `k_B + p ℤ` (shifted by the multiple `p A'`) contains no singular point `p ∣ t`, `p ∣ 3 t - ρ`,
  `p ∣ 2 t - 1`;
* `KBundle.gle_m3`, `KBundle.pre_gap`: the `Q`-level bridges (a minor bound for every retained set; the prefix
  rule through `preLayer` and `B.pole`);
* `KBundle.roots_facts`: the two shift roots in the form `cutfree` uses. -/

namespace CatalanCore.Uniform.Content.BankShared.KTerm
open CatalanCore CatalanCore.Uniform CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared
  CatalanCore.Uniform.Content.BankShared.TwoTerm CatalanCore.Uniform.Content.BankShared.TwoTerm.Pre
  CatalanCore.Uniform.Content.BankShared.Check
  CatalanCore.Arith CatalanCore.Arith.Hybrid CatalanCore.Arith.Hybrid.ChainClasses CatalanCore.Rect
  CatalanFrames.HybCommon CatalanFrames.HybGen

/-! ### Cut-freeness of a window -/

theorem lat_gap {p : ℕ} (hp : 0 < p) {x A n a b : ℕ} (hx : x < p) (hA : A ≤ a)
    (hlo : 1 ≤ n → A + x + (n - 1) * p ≤ a) (hhi : b ≤ A + x + n * p) {t : ℤ} (h1 : (a : ℤ) < t)
    (h2 : t < b) (s : ℤ) (hs : t = ((A + x : ℕ) : ℤ) + s * p) : False := by
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have hb : (b : ℤ) ≤ ((A + x : ℕ) : ℤ) + n * p := by exact_mod_cast hhi
  refine not_between (x := ((A + x : ℕ) : ℤ)) (n := (n : ℤ) - 1) (t := t) hpz ?_ ?_ s hs
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hxA : (A : ℤ) ≤ a := by exact_mod_cast hA
      have hxp : (x : ℤ) < p := by exact_mod_cast hx
      push_cast
      linarith
    · have h' : ((A + x + (n - 1) * p : ℕ) : ℤ) ≤ a := by exact_mod_cast hlo hn
      push_cast [Nat.cast_sub hn] at h' ⊢
      linarith
  · have e : ((n : ℤ) - 1 + 1) = n := by ring
    rw [e]
    linarith

theorem dvd_of_dvd_const {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {c : ℤ} (hc : 0 < c) (hc3 : c ≤ 3) {u : ℤ}
    (h : (p : ℤ) ∣ c * u) : (p : ℤ) ∣ u := by
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpr.dvd_or_dvd h with h' | h'
  · exfalso
    have := Int.le_of_dvd hc h'
    omega
  · exact h'

theorem odd_of_ge_seven {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) : p % 2 = 1 := by
  by_contra h
  have h2 : 2 ∣ p := by omega
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h <;> omega

namespace KBundle

/-- The three singular lattices of the bundle at the prime `p`. -/
def Sing (B : KBundle) (p : ℕ) (t : ℤ) : Prop :=
  (p : ℤ) ∣ t ∨ (p : ℤ) ∣ 3 * t - (B.ρ : ℤ) ∨ (p : ℤ) ∣ 2 * t - 1

theorem cutfree (B : KBundle) {p kA kB A' n0 n1 n2 a b : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hA : p * A' ≤ a)
    (hkA : ∃ j, 3 * kA = j * p + B.ρ) (hkAp : kA < p) (hkB : ∃ j, 2 * kB = j * p + 1) (hkBp : kB < p)
    (hl0 : 1 ≤ n0 → p * A' + 0 + (n0 - 1) * p ≤ a) (hh0 : b ≤ p * A' + 0 + n0 * p)
    (hl1 : 1 ≤ n1 → p * A' + kA + (n1 - 1) * p ≤ a) (hh1 : b ≤ p * A' + kA + n1 * p)
    (hl2 : 1 ≤ n2 → p * A' + kB + (n2 - 1) * p ≤ a) (hh2 : b ≤ p * A' + kB + n2 * p) :
    ∀ t : ℤ, (a : ℤ) < t → t < b → ¬ B.Sing p t := by
  intro t h1 h2 hs
  have hp0 : 0 < p := hp.pos
  obtain ⟨jA, hjA⟩ := hkA
  obtain ⟨jB, hjB⟩ := hkB
  unfold Sing at hs
  rcases hs with ⟨d, hd⟩ | ⟨d, hd⟩ | ⟨d, hd⟩
  · exact lat_gap hp0 (x := 0) (A := p * A') (n := n0) hp0 hA hl0 hh0 h1 h2 (d - A')
      (by push_cast; rw [hd]; ring)
  · have hjA' : (3 : ℤ) * kA = jA * p + B.ρ := by exact_mod_cast hjA
    have h3 : (p : ℤ) ∣ 3 * (t - kA) := ⟨d - jA, by linarith⟩
    obtain ⟨e, he⟩ := dvd_of_dvd_const hp h5 (by norm_num) (by norm_num) h3
    exact lat_gap hp0 (x := kA) (A := p * A') (n := n1) hkAp hA hl1 hh1 h1 h2 (e - A')
      (by push_cast; linarith)
  · have hjB' : (2 : ℤ) * kB = jB * p + 1 := by exact_mod_cast hjB
    have h3 : (p : ℤ) ∣ 2 * (t - kB) := ⟨d - jB, by linarith⟩
    obtain ⟨e, he⟩ := dvd_of_dvd_const hp h5 (by norm_num) (by norm_num) h3
    exact lat_gap hp0 (x := kB) (A := p * A') (n := n2) hkBp hA hl2 hh2 h1 h2 (e - A')
      (by push_cast; linarith)

/-! ### The Q-level bridges -/

theorem gle_m3 (B : KBundle) (c : ℚ) (hc : 0 < c) (depth : ℕ) {n : ℕ}
    (i : ((altGeom c hc).family B.Fr depth).ι)
    (hr : i.1 % 2 = 0) (p : ℕ) [Fact p.Prime]
    (h : ∀ s : Finset (Fin i.1), GLE p n (commonMinorPoly B.Fr i.1 ((altGeom c hc).borderSize i.1) s)) :
    GLE p n (((altGeom c hc).family B.Fr depth).Q i) := by
  obtain ⟨r, S⟩ := i
  rw [altGeom_member_commonMinor c hc B.Fr depth hr S]
  exact h _

theorem pre_gap (B : KBundle) (c : ℚ) (hc : 0 < c) (depth : ℕ) (i : ((altGeom c hc).family B.Fr depth).ι)
    (hi : ((altGeom c hc).family B.Fr depth).Adm i) (hr : i.1 % 2 = 0) (p : ℕ) [Fact p.Prime]
    (h5 : 5 ≤ p) (hN : 3 * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p) (n a b : ℕ)
    (hW : Win p i.1 ((altGeom c hc).borderSize i.1) n ((altGeom c hc).borderSize i.1 - n * p) a b)
    (hgap : ∀ t : ℤ, (a : ℤ) < t → t < b → ¬ B.Sing p t) :
    GLE p (2 * i.1 + 2 * (altGeom c hc).borderSize i.1 - (b - a))
      (((altGeom c hc).family B.Fr depth).Q i) := by
  have hk : ((altGeom c hc).geometry i.1).k = (altGeom c hc).borderSize i.1 :=
    geometry_k_eq_borderSize _ i.1
  have hN' : i.1 + 2 * (altGeom c hc).borderSize i.1 < p * p := by omega
  have hv : preValid (altGeom c hc) B.Fr n (fun _ _ => a) (fun _ _ => b) i.1 p := by
    refine ⟨altGeom_hybShape c hc hr, fun [hpf : Fact p.Prime] => ?_⟩
    rw [hk]
    refine ⟨B.pole p (i.1 + 2 * (altGeom c hc).borderSize i.1) h5 hN, hN', hW, fun t h1 h2 => ⟨?_, ?_⟩⟩
    · rintro ⟨d, hd⟩
      refine hgap (t : ℤ) (by exact_mod_cast h1) (by exact_mod_cast h2) (Or.inl ⟨(d : ℤ), ?_⟩)
      rw [hd]; push_cast; ring
    · intro hs
      exact hgap (t : ℤ) (by exact_mod_cast h1) (by exact_mod_cast h2)
        ((B.singular_iff p _ h5 hN _).1 hs)
  have hg := (preLayer (altGeom c hc) B.Fr depth n (fun _ _ => a) (fun _ _ => b)).gle i hi p hv
  simp only [preLayer, zero_mul, add_zero, hk] at hg
  exact hg

/-- The roots as hypotheses of `cutfree` and the congruence classes. -/
theorem roots_facts (B : KBundle) {p : ℕ} {kv : ℕ → ℕ}
    (hroots : ∀ n < B.shifts.length, ∃ jn, (shAt B.shifts n).q * kv n = jn * p + (shAt B.shifts n).o ∧
      0 < jn ∧ jn < (shAt B.shifts n).q ∧ 0 < kv n ∧ kv n < p) :
    (∃ j, 3 * kv 0 = j * p + B.ρ ∧ 0 < j ∧ j < 3 ∧ 0 < kv 0 ∧ kv 0 < p) ∧
    (∃ j, 2 * kv 1 = j * p + 1 ∧ 0 < j ∧ j < 2 ∧ 0 < kv 1 ∧ kv 1 < p) :=
  ⟨hroots 0 (by simp [shifts]), hroots 1 (by simp [shifts])⟩

end KBundle

end CatalanCore.Uniform.Content.BankShared.KTerm
