# G prefix reuse audit — Phase 0

27 October 2026. Read-only audit of release baseline 5e09e6f; no builds. Paper reference: fast-content-oracle-2026-10-26/northstar/G-PHYSICAL-PREFIX-THEOREM.md. This concerns the general lower-bound injection, not maximality or exact primitive content.

## Reusable API (paths relative to release worktree)

- Parametric/RawDigitReduction.lean:17 `raw_zero_digit_reduction`: actual scaled raw identity for arbitrary N; prime p, p != 2, H N < p^2, j < H N. At :194 `scaledRawEntry_transfer` adds the p-integral p*z parameter condition.
- Parametric/RawDigitFunctional.lean:9 `rawEntry_primeDigitPair`: actual digit functional, arbitrary N, admissible design and N>0.
- Parametric/PrimeDigitSampling.lean: `primeDigitSample_add`, `sub`, `C_mul`, `single`, `shift_single`, and `primeDigitPair_sub`.
- GenD/RankU.lean:31–145 `reversedRow_eq_reflect`, `primeDigitSample_comb`, `primeDigitPair_comb`, `rowP_map_gen`, `rowD_map_gen`, `uResp_eq`: common-degree reflection, signed row indices and the actual raw response of arbitrary physical row combinations.
- GenD/RankFilt.lean:19 `binom_filter'`: arbitrary finite differences over a commutative ring. At :71 `fResp_eq_sum_uResp`: actual filtered response as a binomial sum for arbitrary N.
- GenD/RankCommon.lean:183 `dvd_of_taylor_coeff_zero`: generic prefix-to-divisibility lemma.
- Parametric/SecondaryTentDimension.lean:26,41 `secondaryTent_constraints_finrank`, `secondaryTent_rank_of_constraints`: generic stacked-condition dimension count and injection into the actual physical left kernel. The latter is the preferred assembly bridge.
- GenD/Interface.lean:34,104 `nullity`, `NullityLB`: existing exact physical target and downstream ledger contract.

## Boundaries that matter

1. FilterDigitReduction's `filterBinomial_prime_digit`, `filterCoeffRat_prime_digit_reduction`, `filteredEntry_scaled_residue_sum`, `filtered_block_reduction` specialize scale to N=p, hence q=q0*p. They do not prove q=a_q*p+r_q at arbitrary N.
2. RankFilt.`fResp_digit` assumes `(b+k)%p+q<p`; it is a no-carry formula, not the general p-step/window theorem.
3. RankDigits.`DigitSeq`, `digits_vanish_S`, `digits_vanish_U6` are particular K6/Frobenius sufficient vanishing mechanisms. RankSeq.`frob_poly` and `digitSeq_design` assume q+h <= (p+1)/2; the latter also assumes n <= 4p+2g+1. They do not express arbitrary slot quotients.
4. SparseDigitConstants/Residues hold selected small-index identities. `sparseDigit_identity_residue` uses j:Fin 2 and p>=1000000. Only `rational_residue_den_of_bound` is immediately generic; the fixed tables are not the general source-exception manifest.
5. SecondaryTentFilteredResponse.`secondaryTent_rank_of_raw_polynomial_responses` asks the original full raw response to be a polynomial of degree<q. Use `secondaryTent_rank_of_constraints` directly instead of imposing this stronger intermediate obligation on the p-step construction.
6. No existing `SourceCover`, `prefixKernel`, all-q p-step split or full slot tiling was found in Parametric or GenD. This is evidence from the named source search, not a claim about all Mathlib facilities.

## Missing bridges and revised size

| New work | Estimated Lean lines |
|---|---:|
| All-q p-step; active bounds; low-filter polynomial representation and uniqueness | 500–900 |
| Full signed block tiling, center, slot bases and both virtual endpoints | 1100–1900 |
| Arbitrary-h Frobenius split; A/C/center cases | 700–1200 |
| Intrinsic coefficient windows; Taylor graph lifts; auxiliary uniqueness | 700–1200 |
| Exact source guards, finite quotient enumeration, coverage and denominator exceptions | 700–1300 |
| Injection, physical left-kernel bridge and NullityLB packaging | 300–500 |
| Total | 4000–7000 |

These are estimates, not measurements. The audit removes duplicated arithmetic and rank-nullity infrastructure, but does not justify shrinking C-Prefix to a wrapper. The old estimate was 3000–7000. An end-to-end first chart remains the appropriate validation before narrowing this range.

Injection-only scope omits reconstruction of every physical solution and the upper-nullity theorem. It still must prove that auxiliary-only solutions vanish and reconstructed vectors satisfy every virtual-row constraint. Keep K=1, both endpoints, the center, empty windows, degree -1 and affine branch changes.

## Recommended decision

Reuse existing arbitrary-scale raw/reflection APIs plus the generic injected-kernel rank bridge. Add all-quotient p-step, complete tiling, Frobenius slots and unique prefix graphs in new modules. Do not promote DigitSeq window assumptions to hypotheses of Uniform Content. No family or theorem-scope exclusion follows from this engineering audit.
