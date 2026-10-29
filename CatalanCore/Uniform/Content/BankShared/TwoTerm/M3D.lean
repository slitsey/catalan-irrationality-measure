import CatalanCore.Uniform.Content.BankShared.TwoTerm.Class
import CatalanCore.Uniform.Content.BankShared.Reindex
import CatalanCore.Uniform.Content.Wire.M3D
set_option Elab.async false
set_option maxHeartbeats 1600000

/-! # M3D for every two-term bank (lane C4, gap C4)

For `TwoTermData Fr q o` and a natural norm `nm` (`Fr.norm = nm`, `p ∤ nm`):

* `nocut_window` (the `q t - o` class may skip multiples of `p` giving no integer `t`) and
  `nocut_window_k` (the class `q t ≡ o` is `t ≡ k (mod p)`): cut-free segments for the singular
  classes `p ∣ t`, `p ∣ q t - o` and the border shift `t ≡ r (mod p)`;
* `ttPoleData`: the pole data under `q N < p²`;
* `m3dValid_tt`: the window `m3dValid` on `altGeom c` at even `r`;
* `m3_gle_tt`: the M3D price `2r + (2m - (b - max(a, N - p)))` (debit 0);
* `m3_general_tt`: the M3D branch for any gap indices `n0, n1, n3` of the three residue families. -/

namespace CatalanCore.Uniform.Content.BankShared.TwoTerm
open Polynomial Finset CatalanCore CatalanCore.Basic CatalanCore.Arith.Hybrid
  CatalanCore.Arith.Hybrid.ChainClasses CatalanCore.Uniform CatalanCore.Uniform.Content.Smith
  CatalanCore.Uniform.Content.Wire CatalanCore.Uniform.Content.Shape CatalanCore.Uniform.Content.BankShared

variable {Fr : Frame} {q o : ℕ}

/-- A segment `[a, b)` strictly between consecutive multiples of `p`, of `(t ↦ q t - o)` (where
the multiples `n1 + i`, `1 ≤ i ≤ K1`, give no integer `t`) and of the border shift, is cut-free. -/
theorem nocut_window (p r a b q o : ℕ) (hp : 0 < p) (hq : 0 < q) (n0 n1 K1 n3 : ℕ)
    (h0 : n0 * p ≤ a ∧ b ≤ (n0 + 1) * p)
    (h1 : n1 * p + o ≤ q * a ∧ q * b ≤ (n1 + K1 + 1) * p + o)
    (m1 : ∀ i : ℕ, 1 ≤ i → i ≤ K1 → ((n1 + i) * p + o) % q ≠ 0)
    (h3 : r + n3 * p ≤ a ∧ b ≤ r + (n3 + 1) * p) :
    ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut p r (ttSing p q o)) (min (x : ℤ) y) (max (x : ℤ) y) := by
  intro x y hax hxb hay hyb t hat htb hcut
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have ha : (a : ℤ) < t := by
    have : (a : ℤ) ≤ min (x : ℤ) y := le_min (by exact_mod_cast hax) (by exact_mod_cast hay)
    omega
  have hb : t < b := by
    have hx : (x : ℤ) < b := by exact_mod_cast hxb
    have hy : (y : ℤ) < b := by exact_mod_cast hyb
    have : max (x : ℤ) y ≤ (b : ℤ) - 1 := max_le (by omega) (by omega)
    omega
  have bet : ∀ (n j : ℤ), n * p < j * p → j * p < (n + 1) * p → False := by
    intro n j h1 h2
    have u : n < j := lt_of_mul_lt_mul_right h1 hpz.le
    have v : j < n + 1 := lt_of_mul_lt_mul_right h2 hpz.le
    omega
  obtain ⟨h0a, h0b⟩ := h0
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h3a, h3b⟩ := h3
  have c0a : ((n0 : ℤ)) * p ≤ a := by exact_mod_cast h0a
  have c0b : (b : ℤ) ≤ ((n0 : ℤ) + 1) * p := by exact_mod_cast h0b
  have c1a : ((n1 : ℤ)) * p + o ≤ q * a := by exact_mod_cast h1a
  have c1b : (q : ℤ) * b ≤ ((n1 : ℤ) + K1 + 1) * p + o := by exact_mod_cast h1b
  have c3a : (r : ℤ) + ((n3 : ℤ)) * p ≤ a := by exact_mod_cast h3a
  have c3b : (b : ℤ) ≤ r + ((n3 : ℤ) + 1) * p := by exact_mod_cast h3b
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  rcases hcut with (⟨j, hj⟩ | ⟨j, hj⟩) | ⟨j, hj⟩ | ⟨j, hj⟩
  · exact bet n0 j (by linarith) (by linarith)
  · -- q t - o = p j
    have hqa : (q : ℤ) * a < q * t := mul_lt_mul_of_pos_left ha hqz
    have hqb : (q : ℤ) * t < q * b := mul_lt_mul_of_pos_left hb hqz
    have l1 : (n1 : ℤ) * p < j * p := by linarith
    have l2 : j * p < ((n1 : ℤ) + K1 + 1) * p := by linarith
    have u : (n1 : ℤ) < j := lt_of_mul_lt_mul_right l1 hpz.le
    have v : j < (n1 : ℤ) + K1 + 1 := lt_of_mul_lt_mul_right l2 hpz.le
    obtain ⟨i, hi⟩ : ∃ i : ℕ, j = (n1 : ℤ) + i := ⟨(j - n1).toNat, by omega⟩
    have hz := m1 i (by omega) (by omega)
    have hz2 : (((n1 + i) * p + o : ℕ) : ℤ) = q * t := by
      push_cast; rw [← hi]; linarith
    have hd : (q : ℤ) ∣ (((n1 + i) * p + o : ℕ) : ℤ) := ⟨t, hz2⟩
    exact hz (Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.1 hd))
  · exact bet n0 j (by linarith) (by linarith)
  · exact bet n3 j (by linarith) (by linarith)

/-- A segment `[a, b)` inside one gap of each of the three residue families `t ≡ 0`, `t ≡ k`
(`p ∣ q k - o`, the pole class) and `t ≡ r (mod p)` is cut-free. -/
theorem nocut_window_k (p r a b q o k : ℕ) (hp : 0 < p) (hk : (p : ℤ) ∣ q * (k : ℤ) - o)
    (hcop : IsCoprime (p : ℤ) q) (n0 n1 n3 : ℕ)
    (h0 : n0 * p ≤ a ∧ b ≤ (n0 + 1) * p)
    (h1 : n1 * p + k ≤ a ∧ b ≤ (n1 + 1) * p + k)
    (h3 : r + n3 * p ≤ a ∧ b ≤ r + (n3 + 1) * p) :
    ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b →
      NoCut (Cut p r (ttSing p q o)) (min (x : ℤ) y) (max (x : ℤ) y) := by
  intro x y hax hxb hay hyb t hat htb hcut
  have hpz : (0 : ℤ) < p := by exact_mod_cast hp
  have ha : (a : ℤ) < t := by
    have : (a : ℤ) ≤ min (x : ℤ) y := le_min (by exact_mod_cast hax) (by exact_mod_cast hay)
    omega
  have hb : t < b := by
    have hx : (x : ℤ) < b := by exact_mod_cast hxb
    have hy : (y : ℤ) < b := by exact_mod_cast hyb
    have : max (x : ℤ) y ≤ (b : ℤ) - 1 := max_le (by omega) (by omega)
    omega
  have bet : ∀ (n j : ℤ), n * p < j * p → j * p < (n + 1) * p → False := by
    intro n j h1 h2
    have u : n < j := lt_of_mul_lt_mul_right h1 hpz.le
    have v : j < n + 1 := lt_of_mul_lt_mul_right h2 hpz.le
    omega
  obtain ⟨h0a, h0b⟩ := h0
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h3a, h3b⟩ := h3
  have c0a : ((n0 : ℤ)) * p ≤ a := by exact_mod_cast h0a
  have c0b : (b : ℤ) ≤ ((n0 : ℤ) + 1) * p := by exact_mod_cast h0b
  have c1a : ((n1 : ℤ)) * p + k ≤ a := by exact_mod_cast h1a
  have c1b : (b : ℤ) ≤ ((n1 : ℤ) + 1) * p + k := by exact_mod_cast h1b
  have c3a : (r : ℤ) + ((n3 : ℤ)) * p ≤ a := by exact_mod_cast h3a
  have c3b : (b : ℤ) ≤ r + ((n3 : ℤ) + 1) * p := by exact_mod_cast h3b
  -- the class `p ∣ q t - o` is the class `t ≡ k (mod p)`
  have cls : (p : ℤ) ∣ q * t - o → ∃ j : ℤ, t = k + j * p := by
    intro hd
    have hq : (p : ℤ) ∣ q * (t - k) := by
      have := dvd_sub hd hk
      have e : (q : ℤ) * t - (o : ℤ) - ((q : ℤ) * (k : ℤ) - o) = q * (t - k) := by ring
      rwa [e] at this
    obtain ⟨j, hj⟩ := hcop.dvd_of_dvd_mul_left hq
    exact ⟨j, by linarith⟩
  rcases hcut with (hj | hj) | ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨j, hj⟩ := hj
    exact bet n0 j (by linarith) (by linarith)
  · obtain ⟨j, hj⟩ := cls hj
    have l1 : (n1 : ℤ) * p < j * p := by linarith
    have l2 : j * p < ((n1 : ℤ) + 1) * p := by linarith
    exact bet n1 j l1 l2
  · exact bet n0 j (by linarith) (by linarith)
  · exact bet n3 j (by linarith) (by linarith)

/-- **Longest-gap form**: a segment `[a, b)` containing no cut point in its interior `(a, b)`
satisfies the `NoCut` hypothesis of `m3dValid`. -/
theorem nocut_of_gap {cut : ℤ → Prop} {a b : ℕ}
    (h : ∀ t : ℤ, (a : ℤ) < t → t < b → ¬ cut t) :
    ∀ x y : ℕ, a ≤ x → x < b → a ≤ y → y < b → NoCut cut (min (x : ℤ) y) (max (x : ℤ) y) := by
  intro x y hax hxb hay hyb t h1 h2
  apply h t
  · have : (a : ℤ) ≤ min (x : ℤ) y := le_min (by exact_mod_cast hax) (by exact_mod_cast hay)
    omega
  · have hx : (x : ℤ) < b := by exact_mod_cast hxb
    have hy : (y : ℤ) < b := by exact_mod_cast hyb
    have : max (x : ℤ) y < b := max_lt hx hy
    omega

/-! ### Pole data and the M3D window -/

/-- The pole data of a two-term frame with natural norm `nm` at a prime `p ∤ nm` with `q N < p²`. -/
noncomputable def ttPoleData (T : TwoTermData Fr q o) {nm : ℕ} (hnorm : Fr.norm = (nm : ℚ))
    (p N : ℕ) [Fact p.Prime] (hpn : ¬ p ∣ nm) (hN : q * N < p * p) : Periodic.PoleData Fr p N :=
  twoTermPoleData T (N := N)
    ((Nat.le_mul_of_pos_left N (by have := T.o_lt; have := T.o_pos; omega)).trans hN.le)
    (not_sq_dvd_of_qN T hN.le) (norm_good hnorm hpn).1 (norm_good hnorm hpn).2

/-- **M3D window** on `altGeom c` at even `r` for a two-term frame: pole data from `q N < p²`. -/
theorem m3dValid_tt (c : ℚ) (hc : 0 < c) (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (a b : ℕ → ℕ → ℕ) (r p : ℕ) (hr : r % 2 = 0)
    (hpn : p.Prime → ¬ p ∣ nm) (hN : q * (r + 2 * (altGeom c hc).borderSize r) < p * p)
    (hra : r ≤ a r p) (hab : a r p ≤ b r p) (hb1 : b r p ≤ r + 2 * (altGeom c hc).borderSize r)
    (hb2 : b r p ≤ r + p)
    (hj : max (a r p) (r + 2 * (altGeom c hc).borderSize r - p) ≤ b r p)
    (hcut : ∀ x y : ℕ, a r p ≤ x → x < b r p → a r p ≤ y → y < b r p →
      NoCut (Cut p r (ttSing p q o)) (min (x : ℤ) y) (max (x : ℤ) y)) :
    m3dValid (altGeom c hc) Fr a b r p := by
  have hk : ((altGeom c hc).geometry r).k = (altGeom c hc).borderSize r :=
    geometry_k_eq_borderSize _ r
  have hq : 0 < q := by have := T.o_lt; have := T.o_pos; omega
  have hN' : r + 2 * (altGeom c hc).borderSize r < p * p :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_left _ hq) hN
  refine ⟨altGeom_hybShape c hc hr, fun [hpf : Fact p.Prime] => ?_⟩
  rw [hk]
  exact ⟨ttPoleData T hnorm p _ (hpn hpf.out) hN, hN', hra, hab, hb1, hb2, hj, hcut⟩

/-- **M3D price** (debit 0) on any block geometry, in terms of the border size. -/
theorem m3_gle_tt (G : BlockGeom) {depth : ℕ} (a b : ℕ → ℕ → ℕ) (i : (G.family Fr depth).ι)
    (hi : (G.family Fr depth).Adm i) (p : ℕ) [Fact p.Prime] (hv : m3dValid G Fr a b i.1 p) :
    GLE p (2 * i.1 + (2 * G.borderSize i.1 -
      (b i.1 p - max (a i.1 p) (i.1 + 2 * G.borderSize i.1 - p)))) ((G.family Fr depth).Q i) := by
  have h := (m3dLayer G Fr depth a b).gle i hi p hv
  have hk : (G.geometry i.1).k = G.borderSize i.1 := geometry_k_eq_borderSize G i.1
  simp only [m3dLayer, zero_mul, add_zero, m3dBase, hk] at h
  exact h

/-- **M3D branch, longest-gap form.**  For a two-term frame, an even scale `r` and a prime
`p ∤ nm` with `q N < p²`: every segment `[a, b)` of the window `[max(r, N - p), min(N, r + p)]`
with no cut point of `t ≡ 0`, `p ∣ q t - o`, `t ≡ r (mod p)` in `(a, b)` gives the price
`2r + (2m - (b - a))`. -/
theorem m3_gap_tt (c : ℚ) (hc : 0 < c) (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth : ℕ) (i : ((altGeom c hc).family Fr depth).ι)
    (hi : ((altGeom c hc).family Fr depth).Adm i) (hr : i.1 % 2 = 0) (p : ℕ) [Fact p.Prime]
    (hpn : ¬ p ∣ nm) (hN : q * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p) (a b : ℕ)
    (hra : i.1 ≤ a) (hpa : i.1 + 2 * (altGeom c hc).borderSize i.1 - p ≤ a) (hab : a ≤ b)
    (hb1 : b ≤ i.1 + 2 * (altGeom c hc).borderSize i.1) (hb2 : b ≤ i.1 + p)
    (hgap : ∀ t : ℤ, (a : ℤ) < t → t < b → ¬ Cut p i.1 (ttSing p q o) t) :
    GLE p (2 * i.1 + (2 * (altGeom c hc).borderSize i.1 - (b - a)))
      (((altGeom c hc).family Fr depth).Q i) := by
  have hv : m3dValid (altGeom c hc) Fr (fun _ _ => a) (fun _ _ => b) i.1 p :=
    m3dValid_tt c hc T hnorm _ _ i.1 p hr (fun _ => hpn) hN hra hab hb1 hb2
      (max_le hab (by omega)) (nocut_of_gap hgap)
  have hg := m3_gle_tt (altGeom c hc) (fun _ _ => a) (fun _ _ => b) i hi p hv
  have hmx : max a (i.1 + 2 * (altGeom c hc).borderSize i.1 - p) = a := max_eq_left hpa
  simp only [hmx] at hg
  exact hg

/-- **M3D branch, gap-index form**: for every choice of gap indices `n0, n1, n3`, a member at a
prime `p ∤ nm`, `q < p`, `q N < p²`, `m ≤ p`, with pole index `q k = o + j p`, is cleared by
`2r + 2m - (Bu - a)`, where `[a, Bu)` is the intersection of the three gaps with the window
`[max(r, N - p), min(N, r + p))` (`0` truncated). -/
theorem m3_general_tt (c : ℚ) (hc : 0 < c) (T : TwoTermData Fr q o) {nm : ℕ}
    (hnorm : Fr.norm = (nm : ℚ)) (depth : ℕ) (i : ((altGeom c hc).family Fr depth).ι)
    (hi : ((altGeom c hc).family Fr depth).Adm i) (hr : i.1 % 2 = 0) (p : ℕ) [Fact p.Prime]
    (hpn : ¬ p ∣ nm) (hqp : q < p) (hsq : q * (i.1 + 2 * (altGeom c hc).borderSize i.1) < p * p)
    (hmp : (altGeom c hc).borderSize i.1 ≤ p)
    (k j : ℕ) (hk : q * k = o + j * p) (n0 n1 n3 : ℕ) :
    ∃ n : ℕ, GLE p n (((altGeom c hc).family Fr depth).Q i) ∧
      (n : ℤ) ≤ ((2 * i.1 + 2 * (altGeom c hc).borderSize i.1 : ℕ) : ℤ) -
        ((min (min ((n0 + 1) * p) ((n1 + 1) * p + k))
              (min (i.1 + (n3 + 1) * p)
                (min (i.1 + 2 * (altGeom c hc).borderSize i.1) (i.1 + p))) -
          max (max (n0 * p) (n1 * p + k))
            (max (i.1 + n3 * p) (max i.1 (i.1 + 2 * (altGeom c hc).borderSize i.1 - p))) :
            ℕ) : ℤ) := by
  have hcop : IsCoprime (p : ℤ) q := by
    have hq : 0 < q := by have := T.o_lt; have := T.o_pos; omega
    exact Nat.isCoprime_iff_coprime.2 (coprime_of_lt (Fact.out : p.Prime) hq hqp)
  have hkd : (p : ℤ) ∣ q * (k : ℤ) - o := ⟨j, by
    have : (q * k : ℤ) = o + j * p := by exact_mod_cast hk
    linarith⟩
  set r := i.1 with hr_def
  set m := (altGeom c hc).borderSize i.1 with hm_def
  set a : ℕ := max (max (n0 * p) (n1 * p + k)) (max (r + n3 * p) (max r (r + 2 * m - p))) with ha
  set Bu : ℕ := min (min ((n0 + 1) * p) ((n1 + 1) * p + k))
    (min (r + (n3 + 1) * p) (min (r + 2 * m) (r + p))) with hBu
  have F1 : r ≤ a := by rw [ha]; simp only [le_max_iff]; omega
  have F2 : r + 2 * m - p ≤ a := by rw [ha]; simp only [le_max_iff]; omega
  have F3 : n0 * p ≤ a := by rw [ha]; simp only [le_max_iff]; omega
  have F4 : n1 * p + k ≤ a := by rw [ha]; simp only [le_max_iff]; omega
  have F5' : r + n3 * p ≤ a := by rw [ha]; simp only [le_max_iff]; omega
  have G1 : Bu ≤ (n0 + 1) * p := by rw [hBu]; simp only [min_le_iff]; omega
  have G2 : Bu ≤ (n1 + 1) * p + k := by rw [hBu]; simp only [min_le_iff]; omega
  have G3 : Bu ≤ r + (n3 + 1) * p := by rw [hBu]; simp only [min_le_iff]; omega
  have G4 : Bu ≤ r + 2 * m := by rw [hBu]; simp only [min_le_iff]; omega
  have G5 : Bu ≤ r + p := by rw [hBu]; simp only [min_le_iff]; omega
  clear_value a Bu
  clear ha hBu
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  by_cases hne : a ≤ Bu
  · have hv : m3dValid (altGeom c hc) Fr (fun _ _ => a) (fun _ _ => Bu) r p :=
      m3dValid_tt c hc T hnorm _ _ r p hr (fun _ => hpn) hsq F1 hne G4 G5
        (show max a (r + 2 * m - p) ≤ Bu from max_le hne (by omega))
        (nocut_window_k p r a Bu q o k hp0 hkd hcop n0 n1 n3 ⟨F3, G1⟩ ⟨F4, G2⟩ ⟨F5', G3⟩)
    have hg := m3_gle_tt (Fr := Fr) (depth := depth) (altGeom c hc) (fun _ _ => a)
      (fun _ _ => Bu) i hi p hv
    rw [← hm_def, ← hr_def] at hg
    refine ⟨_, hg, ?_⟩
    have hmx : max a (r + 2 * m - p) = a := max_eq_left F2
    show _ ≤ _
    simp only [hmx]
    omega
  · have hv : m3dValid (altGeom c hc) Fr (fun _ _ => max r (r + 2 * m - p))
        (fun _ _ => max r (r + 2 * m - p)) r p := by
      refine m3dValid_tt c hc T hnorm _ _ r p hr (fun _ => hpn) hsq ?_ le_rfl ?_ ?_ ?_ ?_
      · show r ≤ max r (r + 2 * m - p)
        exact le_max_left _ _
      · show max r (r + 2 * m - p) ≤ r + 2 * m
        exact max_le (by omega) (by omega)
      · show max r (r + 2 * m - p) ≤ r + p
        exact max_le (by omega) (by omega)
      · show max (max r (r + 2 * m - p)) (r + 2 * m - p) ≤ max r (r + 2 * m - p)
        exact max_le le_rfl (le_max_right _ _)
      · intro x y hax hxb hay hyb
        exfalso
        omega
    have hg := m3_gle_tt (Fr := Fr) (depth := depth) (altGeom c hc)
      (fun _ _ => max r (r + 2 * m - p)) (fun _ _ => max r (r + 2 * m - p)) i hi p hv
    rw [← hm_def, ← hr_def] at hg
    refine ⟨_, hg, ?_⟩
    have hmx : max (max r (r + 2 * m - p)) (r + 2 * m - p) = max r (r + 2 * m - p) :=
      max_eq_left (le_max_right _ _)
    show _ ≤ _
    simp only [hmx]
    omega

end CatalanCore.Uniform.Content.BankShared.TwoTerm
