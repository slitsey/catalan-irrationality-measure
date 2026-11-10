# Paper II rewrite, 10 Nov 2026 (root bb18b4fe, 27 exports)

## Changed numbers and their Lean names

Every value was read from `SolutionHybrid.lean` and from the rationals `s_Dt`, `s_ccert` in
`CatalanCore/Uniform/Bank/Common/Data/*/Data.lean` plus the Λ files. The decimal values are rounded outward.

| Number | Lean name | μ | D | ρ | ρ/(D−Λ) |
|---|---|---|---|---|---|
| G ± 5π²/48 | lambda_plus/minus_measure | 31.1973 | 3.7453322 | 7.1887383 | 31.19724 |
| L(2,χ₋₃) | chi3_measure | 13.6839 | 4.6442402 | 7.5030223 | 13.68385 |
| L(2,χ₋₃) ± π²/9 | chi3_plus/minus_pi2_measure | 9.4913 | 4.0295805 | 6.8255087 | 9.491278 |
| ψ′(k/5) − π²/6 | fifths1..4_measure | 23.7756 | 3.8141613 | 7.1638755 | 23.77556 |
| π² | pi2_measure | 6.5214 | 3.9790633 | 6.4345402 | 6.521399 |
| L(2,χ₋₃) ± π²/18 | dip_1_18_plus/minus_measure | 17.492 | 3.8109776 (c = 1/4, own certificate) | 6.9434368 | 17.49153 (Λ 3.4140176) |
| ζ(3) | zeta3_measure | 6.0382 (unchanged) | refit halves certificate | | 6.034884 |
| aζ(3)+bπ⁴ | plane3_measure | 118 | 3.3533776 | 6.9643459 | 117.6410 (Λ 3.2941777) |
| π⁴ | pi4_measure | 118 | (case a = 0, b = 1) | | |

The following are unchanged: plane1_measure 20.6622, plane2_measure 335.20, the dips 2/27 (14) and 1/27 (15.359), and
sevenths1..6_measure 1806.1719. All certificates now take ε₀ = 10⁻⁶. ρ/η² for the shifts k/4 is now about 135.

Paper I (`paper/catalan-measure.tex` and the hexagon copy) now quotes 13.6839 and 9.4913 in place of 13.7046 and 9.4998.
Nothing else in Paper I changed. Its PDF was rebuilt.

README data table: rows for G, L₋₃, the thirds, the fifths, π², ζ(3) and ±π²/18 refreshed, and a third-plane row added.
The L₋₃ ratio is now 13.683844…. formalization-hybrid.yaml: spacing fixed ("exponent 118", "reuses 6.0382").

## Plane 3 additions

- Intro: Theorem plane3, μ(aζ(3)+bπ⁴) ≤ 118 for rationals a, b not both zero. It is stated as reach only, with no record
  claim. It gives one short sentence on π⁴ that does not present 118 as the method's best. The paper also has a
  Table 1 row, an abstract mention, new-idea item 9 and a background sentence.
- §ssec:frames: ψ″ terms with orders 3/2/1/0, F^{(3)} = γ₂ψ′(z+1)+γ₃ψ″(z+1), and ξ = −2γ₂ζ(3)+γ₃π⁴/15. Taking γ₂ = −a/2
  and γ₃ = 15b gives ξ = aζ(3)+bπ⁴. This matches `Bank/Plane3/Frame.lean` (datum, datum_xi).
- NV: d = 3, D = (z+1)³, A(−1) = 2γ₃, one deleted node. These are `Support.pole_altGeom_seqFamily_nv0_even` and
  `Frame.datum_nv`.
- Decay §ssec:decaydouble:
  - generalised to poles of order w, with the rank-one splitting B_ij = c_{i+j+1}/(i!j!);
  - for plane 3, det B = 2γ₃³, which is `Support.pole_gram_split_minimal`;
  - the reference frame has shifts 1, 3/4, 1/2 with helpers, Cauchy radius 1/8 and e_l ≤ 5/8, as in `Plane3/Decay.lean`.
- New Section 10 "The third plane":
  - Lemma weights3;
  - Proposition rows3, the four assignment bounds Q1–Q4, with explicit potentials and proofs;
  - the profile table and closed form Λ_h(α) = 3h/4 + (3h−1)α/2 + ((7h−3)/4 + 2log2)α², which gives 3.29409073… at
    h = 4, α = 1/20, checked numerically and marked as not used formally;
  - Theorem content3, Λ₃ = 3162410560009/960000000000, `Bank.Plane3.plane3_content`, any depth;
  - Proposition cert3, with D = 670675532185005206293/(2·10²⁰) and ρ = 272044759206281/39062500000000, which is
    `plane3_decay`;
  - the proof of Theorem plane3. For b ≠ 0 the bound is 117.640988… < 118. For b = 0 it reduces to the ζ(3) bound,
    which is how `plane3_final` does it.
- Formalization section: the plane3_measure/pi4_measure bullets, plus `Bank.Plane3.plane3_content/plane3_decay/plane3_final`,
  `Support.pole_gram_split_minimal`, `Support.pole_altGeom_seqFamily_nv0_even`, `Support.support_measureLB` and
  `Bank.Plane1.alt_point`. "Generic Löwner points" means every point is an instance of alt_point. All the names were
  grepped in the tree.
- ±π²/18: the dip now has its own geometry, c = 1/4, and its own certificate. Its content uses the known-zero bound
  e_p ≤ 2r+2m−n_K for N̄ ≤ 2p (eq:knownzero) with no pivots, as in `Bank/Plane1/Dips/KnownZero/*`.

## Literature claims and verification

- Leibtag et al., arXiv:2610.27799, Theorem 1 gives μ(Aζ(3)+Bζ(4)) < 66.3 for every rational (A,B) ≠ (0,0). I read it in
  the local arXiv source `work/literature/search-2026-10-23/2610.27799-src/main.tex`, lines 122–131. A comment was added
  to refs.bib. The paper says our 118 is weaker.
- Marcovecchio–Zudilin, Proc. Edinb. Math. Soc. 63(2) (2020) 374–397, doi 10.1017/S0013091519000427, give
  μ(ζ(4)) ≤ 12.51085940…. I checked the arXiv abstract 1905.12579 and the PDF text (p. 2). The new bib entry
  MarcovecchioZudilin20 carries a verification comment.
- Lai's linear independence of 1, ζ(3), ζ(4) was not needed for the claim. It was not added beyond the existing citation.

## Build

- Tectonic offline in a scratch copy: rc 0, no undefined references, 0 overfull boxes. One overfull table was fixed with a
  smaller tabcolsep. The `.bbl` grep for `$[a-z](` gave 0 hits. The PDF was copied back.
- The hexagon version was regenerated with make_hexagon.py and builds with rc 0 and no undefined references.
- The theorem list (Theorems 1.1–1.6) and Tables 1 and 4 were read in the rendered PDF against the root exports.
- Greps of both papers, the README and formalization*.yaml found:
  - no superseded numbers;
  - no ∓ or \mp;
  - no B used for μ;
  - no earlier/previous/retained wording about our own results.
  The remaining "earlier"/"unchanged" hits are mathematical, or are README/YAML provenance text about ported files.

## Open

- The general h Q1–Q4 proofs are written by hand from the potentials. The Lean proves the h = 4 instance through
  `plane3_catalogue`, the generic `hpole` suppliers and `plane3_pre`. I matched the statements, not every intermediate
  lemma.
- No push. Nothing outside the named paths was touched.
