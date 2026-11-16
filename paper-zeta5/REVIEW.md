# Referee report: "An irrationality measure for ζ(5)" (zeta5-measure.tex, 16 Nov 2026)

Reviewer: Opus 5.5 (adversarial referee). Brief: `outputs/Compatibility programme/zeta5-lean-plan/briefs/Z5-PAPER-REVIEW.md`.
Lean tree read: `work/catalan-uniform/CatalanCore/Zeta5/` (no Lean edited, no git run).

## Verdict

**(b) Correct after the stated repairs.**

The chain from the stated inputs to 87 is sound. The Lean root `Zeta5IrrationalityMeasure.zeta5_irrationalityMeasure_87` (plain form, all p) checks it, and the constants agree with the Lean:

- recomputed: 37/40 · 9.07427 / (1.38500086 − 1.288003) = 86.5349 < 87;
- the Lean threshold (`za10_threshold`) allows Λ ≤ 1.288519, which gives 86.998.

No step of the proof of Theorem 1.1 is wrong. But several parts of the text did not follow the Lean:

- one theorem was stated more generally than anything proved (A1);
- the description of the radical-vector argument differed from the Lean argument and was incomplete as written (B1);
- three numerical steps used constants or routes different from the Lean (B3–B6);
- one proof sketch was too vague to yield its constant (B2).

All of these are repaired in the text below. Sean's binding change to the plain form of the measure is applied (§ "Statement form").

Counts: **A 2, B 9, C 4, D 9** (24 findings).

## Statement form (binding change, Sean 16 Nov, via coordinator)

The main theorem now uses the plain form of the companions: there is q₀ with |ζ(5) − p/q| > q^{−87} for all integers p and all integers q ≥ q₀. The ε-wording and the coprimality are removed.

Theorem 3.1 (the criterion) now concludes in the same plain form, together with the irrationality of ξ. Its text proof already gives this without coprimality: hypothesis (c) is used at p/q itself. The irrationality follows by applying (c) at x = ξ.

Update after the coordinator's second message: the root is built.

- **The root.** `Zeta5IrrationalityMeasure.zeta5_irrationalityMeasure_87` in `SolutionZeta5.lean`. I read the file. Its statement is ∀ᶠ q in atTop, ∀ p : ℤ, q^(−87) < |∑' n, 1/(n+1)^5 − p/q|.
- **The supporting module.** `CatalanCore.Zeta5.Data.Public`, which contains:
  - `exponentE` = 839369975/9699786 < 87;
  - `zeta5_exact`;
  - `irrational_of_family_nnv`;
  - `TrigammaDifferences.Aux.eventually_of_point`.
- **The paper now follows this route exactly:**
  - Theorem 3.1 concludes (i) ξ is irrational (the proof of `irrational_of_family_nnv`: a rational ξ lies in every window), and (ii) the bound for coprime p, q at every exponent above E.
  - A new Lemma 3.2 is the one-paragraph step of the companions: irrationality plus the coprime ε-form at E gives the plain bound for every μ₀ > E and all p.
  - §9 applies them with E = 839369975/9699786 < 87.
  - §10 cites the root, `Data.Public.zeta5_exact`, `Data.Public.irrational_of_family_nnv` and `TrigammaDifferences.Aux.eventually_of_point`. The old composites `zeta5_measure_of_parity` and `zeta5_mu87_of_decay'` are no longer cited.
- **Checked against the Lean:** I read `Data/Public.lean`. `zeta5_exact` reuses the chain of `zeta5_measure_signed` (`zc32_signed` with `parity_gain`, `measure_of_family_nnv_period`) and calls `irrational_of_family_nnv` on the same `signedFamily`. The exponent is 0.925 · 9.07427/0.09699786 = 86.5349.

## Findings

Format: severity, location, evidence, repair.

### (A) Wrong or unproved claims

**A1. Theorem 6.1 (parity gain) is stated for every inner prime. The Lean proves it only for K ≤ 200p.**
- Location: §6.1, Theorem `thm:parity`.
- Evidence: `Apery.ParityGain` (`Content/Parity.lean`) quantifies over `InnerHyp p n M (4M+10)` with the extra hypothesis `40 * n ≤ 200 * p`. `parity_gain` proves exactly that. No result covers K/p > 200.
- Effect: none on the proof. Definition 5.3 uses k_p only when K ≤ 200p, and `Content.LpC` does the same.
- Repair: the hypothesis K ≤ 200p is added to Theorem 6.1 and to the first line of §6.1. **Applied.**

**A2. Sign error in the Remark at the end of §6.**
- The Remark called the cost of Fauzan's bound "−pR(K/p)". By (5.?) `innerunif` and `Content.LpC_inner`, the cost is −L_p ≈ pR(K/p).
- Remark only, not used in the proof.
- Repair: replace with "the cost pR(K/p)". **Applied.**

### (B) Mismatches with the Lean, or missing steps

**B1. The leading form (6.?) and the radical-vector argument of §6.3 are not the Lean argument, and as written they are incomplete.**
- Location: display `eq:leadform` and the paragraph after it.
- What the paper had:
  - the local image of row (a, i) as B_a z^i, with a remark that other classes couple "only through the top row of an extra class";
  - a per-class argument: "the isotropic part exceeds its complement by one ⇒ one radical vector, couplings remove at most one vector each".
- What the Lean has (`ParityData`, `PsiL`, `scL` in `Parity/Radical.lean`, and `lead_entry` in `Padic/Ident.lean`):
  - Ψ_a(v) = B_a(Σ_i v_{a,i} z^i + [a ∉ E] s_a(v) z^{L_a});
  - s_a(v) = Σ_{b active extra} c_{ab} v_{b,L_b−1};
  - the leading form is Σ_{a∈S} δ_a C_a(Ψ_a v, Ψ_a w).
- `radical_T_odd` and `radical_T_even` are a single global dimension count. Take the vectors supported on the even rows of the classes with ℓ_N even. The test conditions are the odd rows of those classes plus one condition per coupled class: the active extra classes with ℓ_N odd for T odd, and the non-extra ones for T even. The kernel has dimension ≥ #even − #conditions, which is exactly the count in k_p.
- The paper's per-class phrasing does not justify that the couplings cost one vector each, nor which classes they are.
- Repair: §6.3 now states Ψ_a with the coupling term, and gives the dimension count for T odd and T even as in the Lean. **Applied.**

**B2. The proof of Proposition 7.2(d), the tail ∫₂₀₀^∞ R x⁻³ ≤ −103109/24·10⁶, was a sketch that cannot produce the constant.**
- Evidence: `Sum.TL200` and `Profile/Tail.lean`, `Profile/Antideriv.lean` (iterated primitives P, C, D of F, P̄ = 2923/240, the majorant Ω, one application of the fundamental theorem of calculus).
- Repair: the text proof now follows the Lean. **Applied.** The proof:
  - Put P = 74g(1−g) − λf(1−f), C = (74/α)G₀(g) − λG₀(f) and D = −74B₄(g)/(12α²) + λB₄(f)/12, where f = {x} and g = {αx}.
  - Then P′ = F + λ, C′ = P − P̄ and D′ = C off ℤ ∪ α⁻¹ℤ.
  - Put Ψ = λ/x + (P−P̄)/x² + 2C/x³ + 6D/x⁴ and Ω = Ψ − 6D₊/x⁴ − (13/16)/x². Then R/x³ ≤ Ω′.
  - So the integral is at most −Ω(200) = −λ/200 + (P̄ + 13/16)/200² + λ/(32·200⁴).
  - I checked the algebra (Ψ′ = F/x² − 24D/x⁵, D ≤ D₊, D₊ − D(200) = λ/192) and the value −0.00429621 = −103109/24·10⁶ by hand and in Python.

**B3. (Author item b.) The step |R(x)| ≤ 8x for x ≥ 10⁸ in the proof of Theorem 7.1 is not the Lean step.**
- It is true: |F| ≤ 8λ = 7.4 and |Q| ≤ 13/8, so |R| ≤ 8x for x ≥ 4.
- The Lean uses `Profile.Rg_bound`: |R(x)x⁻³| ≤ 22/x² for x ≥ 1.
  - It uses this for the band K/M < p ≤ K/T (via `Rg_lin` and `inner_tail_bound`).
  - It also uses it for the tail (`Content.tail_T`: −∫_T^∞ R x⁻³ ≤ 22/T).
- Repair: the proof now uses |R(x)| ≤ 22x for x ≥ 1, citing `Rg_bound`. The two error terms are 44 log 4/10⁸ + 22/10⁸ < 10⁻⁶, so the conclusion is unchanged. **Applied.**

**B4. (Author item c.) The constant 44 log 4/10⁸ is not a named lemma.**
- Where it is in the Lean: it is the term `2 * 22 * Real.log 4 * (R^2/T)` in the statement of `Content.log_mC_le`, produced by `inner_tail_bound` with C₁ = 22. `zc32_signed` then bounds it by 132/T.
- Repair: the text now says |R(x)| ≤ 22(x+1) for x ≥ 1 (`Rg_lin`), so p|R(K/p)| ≤ 44K for p ≤ K, and then applies Chebyshev. Section 10 cites `Content.log_mC_le` and `Profile.Rg_bound`. **Applied.**

**B5. The constant in (5.?) `eq:innerunif`.**
- The paper had 7500M². The Lean has 7501M² (`zc17_gammaIn`).
- The per-prime error the Lean actually sums is 190M³ + 30M (`LpC_inner`).
- Repair: 7501M². **Applied.**

**B6. The outer cost sentence in §5.3.**
- The paper claimed "−v_p(S_K) − γ^out_p = K T₀(p/K) + O(1)" for all K/3 < p ≤ 2h.
- For K < p ≤ 2h the Lean cost is −v_p(S_K) alone: `wOut n p = −vSK − [p ≤ K] γout`. γ^out is defined only for p ≤ K. `zc20_outer` gives |wOut − K T₀(p/K)| ≤ 10.
- Repair: the sentence now says "−v_p(S_K) − [p ≤ K]γ^out_p". **Applied.**

**B7. The proof sketch of Theorem 5.1 (outer extension, author item a) misdescribes the Lean.**
- The paper said the degree conditions of Fauzan's Lemma 3.1 hold "since p ≥ 101 and T ≤ 6".
- In `zc18_ext` (`Frames/OuterExt.lean`) the generic class bound `inner_bound` is applied with:
  - the separation and degree conditions 2K < p² and 104n + 6 < p², which follow from p > K/3;
  - L₀ + ΣL_a = h (`sum_extL`);
  - the two comparison conditions (P), from ℓ_K taking consecutive values and the choice of extras (`ext_P`);
  - and (Z), which uses T ≤ 6, ⌊K/p⌋ ≤ 2 and L₀ = 8 (`ext_Z`).
- L_a ≥ 0 needs the tie-break "removed classes first" when T = 2 (`removed_mem`). This is the reason for the key 2ℓ_K + [a ≤ N].
- p ≥ 101 is used only to get n ≥ 3 and p ≥ 5.
- Repair: the sketch is rewritten to list exactly these steps. **Applied.**

**B8. Cell remainder constant (proof of Proposition 8.4).**
- The paper bounded the fifth derivative of the trigonometric sum by Σ|c_k|(2k)⁵/k. g_A carries the factor 2, and the Lean bound is 2Σ|c_k|(2k)⁵/k (`Cells/TrigA.lean`, line 71).
- Repair: factor 2 inserted. **Applied.**

**B9. Step (8) of Proposition 4.1 claimed V(a) < V(b), which the Lean does not prove.**
- `Vf_a_le` and `Vf_b_le` give both values ≤ 30449413/10⁷. The claim is true (V(a) ≈ 1.23, V(b) ≈ 3.04) but unused.
- Also, the Lean's bound on sup Φ is 60293245/10⁷, which includes the tangent term (`rho_Pb`).
- Repair: "V(a), V(b) ≤ 30449413/10⁷" and "sup Φ ≤ 60293245/10⁷". **Applied.**

### (C) Citation errors

**C1. LBKWSK26 is described too vaguely ("further bounds from conservative matrix fields").**
- arXiv 2610.27799 (abstract, checked 16 Nov) claims:
  - improved irrationality measures for ζ(2) and ζ(3);
  - the linear independence of 1, ζ(3), ζ(4) over ℚ, overlapping Lai;
  - all from one framework of conservative matrix fields.
- The trigamma companion cites it for μ(aζ(3) + bζ(4)) < 66.3.
- Repair: the sentence now states this. **Applied.**

**C2. `refs.bib` comments for Litsey2026 and Litsey2026b are stale.**
- Hexagon 2610.00401 is now v3 (15 Nov 2026) and carries the title in the bib. 2610.00187 is v7 (15 Nov 2026), abstract μ(G) ≤ 270.
- Repair: comments updated. Entries unchanged. **Applied.**

**C3. The Fasten26 title "Irrationality of the Riemann zeta value at five" and the Palomar registry id could not be confirmed.**
- data.palomar-registry.org returned 404, and a web search for PALOMAR-2026-09-25-000018 found nothing.
- The repository realazthat/zeta5-lean2 and commit 2fa4e82 exist, with README title "Zeta(5) formalization" and MIT licence.
- The same entry is in the G paper's bib.
- **Open decision**: keep (registry read on 6 Nov per the bib comment), or retitle to the README title.

**C4. A ζ(5) folder in OpenAI's repository is not mentioned.**
- openai/math at commit fd4aeeb contains `lean/OAI/NumberTheory/ZetaFive` (prime-sum files: WeightedPNT, LargePrime*, RiemannSqueeze). The PNT bridge we import is `OAI.Zeta5.W12.ImportedPNTCoreBridge`.
- The paper's sentence "The prime number theorem is taken from the PNT+ project, through OpenAI's workspace" is accurate, but it does not say that OpenAI's workspace contains ζ(5) material.
- **Open decision**: whether that folder is an OpenAI formalization of Fauzan's theorem that should be credited next to Fasten, Firsching and Romik. Not verified here.

Everything else was verified at the source: arXiv API and abstract pages, Crossref, Zenodo, the GitHub API, and the local text of Fauzan, Giraudin, Brown–Zudilin, Rivoal and FSZ. Specifically:

- authors, titles, venues, volumes, pages, DOIs, arXiv ids and version dates of all other entries;
- Fauzan: Corollary 1.2 (260), Appendix C (ρ = 6933/500 = 13.866), (5.10) = 127751/96000, (5.20), A₁₀₀₀₀₀ = 1.3175717, Lemma 6.1 U = −2733991/2·10⁶, so D = 1.3669955 ≥ 1.36699, and the margin 79/1600;
- Giraudin z5: Lemmas 2, 3, 5 and Proposition 7, a = 10⁻³, b = 49/200, ρ = 9.09, bound 171, conditional on Fauzan;
- Brown–Zudilin Theorem 1 (q^{−0.86}); FSZ, Fischler, FLSZ; Lai.

Literature search, September to November 2026 (arXiv API, Zenodo, GitHub, web): **no other measure for ζ(5)**. The only published ones are 260 (Fauzan) and 171 (Giraudin 2611.01708, one version). The history paragraph is complete and compares both with 87.

New but not citable:

- github.com/long-mathematics/zeta5-irrationality: incomplete (6 of 49 targets), irrationality only.
- The ζ(7) items (Anand/Lai ζ(7), Toledo audit) concern another constant.

### (D) Consistency and writing

- **D1. Notation clashes.**
  - Fixed: λ (= 37/40) against the row scalars λ_s of §6.3, now κ_s; η (= D − Λ) against the fractional part {2λx} of Lemma 5.2, now ϑ; T (row allocation, T(x) in g_par) against the cutoff 10⁸, now x₁.
  - Not fixed: μ (exponent) against Fauzan's functional μ_X. This clash breaks the skill's no-overloading rule. It is Fauzan's and the Lean's notation (`Apery.μX`). **Open decision**: rename the functional (e.g. ⟨·⟩_X) or keep Fauzan's notation with one sentence of warning.
  - Also not fixed: h_j (SOS integers) against h = 37n. Minor, left.
- **D2.** Definition 5.3 leaves outer primes p < 101 undefined. The case is vacuous: K ≥ 200M² ≥ 320000 forces p > K/3 > 101. Repair: the condition "p ≥ 101" is dropped from the definition, with that remark. **Applied.**
- **D3.** Remark after Theorem 7.1: the remainder of the gain is 0.0041, not 0.0042. The values are 1.3175717 − 1.288003 − 0.0196262 − 0.005847 = 0.00410. **Applied.**
- **D4.** Section 10 cites Lean names that carry internal ledger IDs (`zc17_gammaIn`, `zc18_ext`, `zc19_*`, `zc20_outer`, `Content.zc32_*`, `Sum.zc34`–`zc38`, `zd22_sound`). The skill bans internal IDs in public text. They cannot be renamed without editing Lean, which this review must not do. **Open decision**: add public aliases in Lean (e.g. `outer_extension`, `inner_cost`, `integral_T0`) and cite those.
- **D5.** Theorem 1.1 and its paragraph now match the G paper's statement style and the trigamma paper's definition of μ word for word (p/q as in the trigamma paper). **Applied.**
- **D6.** Theorem 3.1 now also concludes that ξ is irrational, as the trigamma paper's deduction theorem does. **Applied.**
- **D7.** The description of the companions was imprecise: "measures on three planes, among them L(2,χ₋₃), ζ(3) and π²". It now names the three planes, as the trigamma abstract does. **Applied.**
- **D8.** The writing rules (semicolons, em-dashes, filler words, introduction order, numbered new ideas, one-paragraph AI disclosure, BibTeX title braces) were checked by grep and by reading.
  - No semicolon joins clauses (the only one is in \subjclass).
  - No em-dashes.
  - "In particular" occurs twice, both legitimate.
  - The introduction order is correct, and the disclosure is one paragraph naming the models and harnesses.
  - All title math groups in refs.bib are braced. The rendered list was read after the build (§ Build).
- **D9.** Proposition 6.2 and Lemma 6.3 keep proof outlines rather than full proofs. Both are kernel-checked (`kpar_ge`, `tauX_lead`), and the outlines agree with the Lean hypotheses: p ≥ 5, poles separated in each class, d(r) < p², deg A − #poles + 1 < p², and the X-coefficient of valuation ≥ β + 1. The paper says these are formalized. No change.

## Checks that passed

- **Every Lean name cited in §10 exists** (script over all `\lean{...}`: 0 missing; `natDegree_Δ` and `Δ_eq_integral` in Port).
- **Statements match the Lean:**
  - the construction: G, Δ, S, F, μ_X, poleValue, K = 40n, N = 3n, h = 37n;
  - the family `zeta5Family` and `signedFamily`;
  - `RhoBound` and the definition of norm exponent;
  - `det_pencil_bounds` (Lemma 3.2), `F_pencil_bounds` (Corollary 3.4);
  - `HasNearbyNV` and `measure_of_family_nnv_period` (Theorem 3.1, with deg ≤ γ·scale + K, more general);
  - the integrality form `q^{37n} m F(p/q) ∈ ℤ`;
  - `zc32_signed` (Λ = 1288003/10⁶, M(K) = max(40, ⌊√⌊√K⌋⌋) = max(40, ⌊K^{1/4}⌋)), `LpC` = Definition 5.3, `mC`, `log_mC`, `GV_F_LpC`;
  - the inner allocation (`innerTot`, `epsSet`, `innerL`, `winner` = (5.2) weights) and the outer allocation (`extTot`, `extKey`, `extL`);
  - |γ^ext − pΓ| ≤ 83 (`zc19_gamma`) and |cost^ext − pR| ≤ 86 (`zc19_cost`);
  - `Qc_ge`/`Qc_le` (−1/2 ≤ Q ≤ 13/8), `gref_nonneg`/`gref_le_half`, `kpar` = the k_p formula (truncated subtraction = [·]₊), `kpar_ge` (30M);
  - `parity_gain_delta` = Lemma 6.4 (hypotheses: unimodular coefficient matrix, half-integral weights, radical on the integral rows);
  - zc34–zc38 (all five constants), `lambdaQ_value` (1.287995331, 1.287995332);
  - `rho_numerics` (a = 10⁻⁸, b = 242976/10⁶, u₀ = 973660012/10⁹; 3.0449413 + 6.0293245 = 9.0742658 < 9.07427);
  - `node_bound`, `rj_abs_le`, `gram_lower` (c_{a,b} = (2π)⁴a³/(24(1+b))), `Phi_tangent` (ab ≤ α⁴);
  - `real_bound` (C* + λM₀ − I)K² + 24K log K + O(K), `ArcMaj` (implied by σ ≤ Θω and ω([x−r, x+r]) ≤ √(2r/b));
  - `cellHyp_tail` (M₀ ≥ −8: the tail bound at s = 2 is −9.76 ≤ −8.96);
  - `zeta5_decay` (b = (43/50)², M₀ = −3330031/500000, c₀ = 37/40, b/2·(1 + cosh 3) = 4.09 > 4).
- **The mathematics of the closed forms (Lemma 8.2) and the SOS lemma 8.3** was checked by hand: the Chebyshev expansions, ∫T_k dσ = c_k/2, and the mean of F = −λ.
- **Legendre** in §5.3: 0 ≤ v_p(S_K) − p𝒩(K/p) ≤ ⌊2h/p⌋. Rederived: v_p(S_K) − p𝒩 = 2(pJ(h/p) − Σ⌊2i/p⌋) = 2Σ_j(⌈jp/2⌉ − jp/2) ∈ [0, q].
- **The criterion proof** (Theorem 3.1) was checked line by line. The period-40 step is ρK ≤ μ₁ log q + 40ρ. It needs no coprimality.
- **The axioms and the source**: no `sorry`, `native_decide` or `axiom` in `CatalanCore/Zeta5` (grep). The toolchain is v4.35.0-rc2. The NOTICE item for the Port directory names Firsching, commit 7fe7367, Apache-2.0.

## Repairs applied (zeta5-measure.tex, refs.bib)

1. Theorem 1.1, its paragraph and the definition paragraph: plain form, wording matched to the companions. The ε and coprimality wording is removed.
2. Theorem 3.1: the conclusion is now irrationality plus the plain form for every μ₀ > γρ/(D − Λ). The proof is extended by the irrationality step. "In the sense of Theorem 1.1" is removed.
3. §3 paragraph on the signed normaliser: the reference to the conclusion form is adjusted.
4. Proposition 4.1 step (8): V(a), V(b) ≤ …, and sup Φ ≤ 60293245/10⁷ (B9).
5. Theorem 5.1 proof sketch rewritten (B7).
6. (5.?) innerunif: 7501M² (B5). The outer-cost sentence uses [p ≤ K] (B6). Lemma 5.2: η renamed ϑ (D1).
7. Definition 5.3: "p ≥ 101" dropped, with a remark (D2).
8. Theorem 6.1 and §6.1: the hypothesis K ≤ 200p (A1).
9. §6.3: the leading form with the coupling term, and the dimension count as in `radical_T_odd/even` (B1). λ_s renamed κ_s (D1).
10. The Remark at the end of §6: the sign (A2).
11. Proposition 7.2(d): the proof is rewritten from `TL200` (B2).
12. Theorem 7.1 proof: |R| ≤ 22(x + 1) and 22x (`Rg_bound`, `Rg_lin`); the cutoff renamed x₁; the error terms 44 log 4/10⁸ + 22/10⁸ (B3, B4).
13. The Remark after Theorem 7.1: 0.0041 (D3).
14. Proposition 8.4 proof: factor 2 in the remainder (B8).
15. Theorem 9 (proof of Theorem 1.1): the plain form.
16. §10: the main theorem was cited by its root name (superseded by item 19: `Zeta5IrrationalityMeasure.zeta5_irrationalityMeasure_87`), and `eventually_of_point` is named. `log_mC_le`, `Rg_bound` and `TL200` are added.
17. §1 Recent results: the LBKWSK26 sentence (C1). Companion paragraph: the planes named (D7).
18. refs.bib: the Litsey2026 and Litsey2026b comments (C2).

## Open decisions for the coordinator

1. C3: the Fasten26 title.
2. C4: whether the `OAI/NumberTheory/ZetaFive` folder in openai/math is an OpenAI ζ(5) formalization that should be credited.
3. D1: the μ against μ_X overload.
4. D4: public Lean aliases for the zc*/zd* names cited in §10.

(The earlier decision on the root's name is settled: `Zeta5IrrationalityMeasure.zeta5_irrationalityMeasure_87` exists and is cited.)

Further changes made after the second message:

19. Theorem 3.1 restated with parts (i) irrational and (ii) the coprime form. New Lemma 3.2 for the plain form. §9 uses E = 839369975/9699786. §10 cites the root and the `Data.Public` names.
20. The abstract's first sentence is in plain form.
21. Intro idea 1 now mentions the dimension count instead of a per-class claim.
22. Lai and LBKWSK26 are ordered by date, and the overlap is stated.
23. The display in Proposition 7.2(d) is split into two lines (an overfull box).

## Build

- **Main paper.** Tectonic, offline (`--only-cached`), in a scratch copy, then the PDF copied back:
  - rc 0;
  - no "undefined" in the log;
  - 0 overfull boxes;
  - 15 underfull boxes, all from long URLs in the bibliography and a long URL in §1.1, so harmless;
  - no `$[a-z](` in the .bbl (title math braced).
- **Rendered reference list.** Read once via pdftotext: 36 entries, all well formed. ζ, π and accents are lost only in the text extraction.
- **Hexagon version.** Regenerated with `make_hexagon.py` (ok, 1202 lines). It builds on its own: rc 0, no undefined references, 0 overfull.
- **Files:**
  - `paper-zeta5/zeta5-measure.pdf`
  - `paper-zeta5/zeta5-measure-hexagon.tex`

  The scratch build is in the session scratchpad.
