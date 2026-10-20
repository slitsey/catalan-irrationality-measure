# Weighted second-order identity: proof development

20 October 2026. Active proof/formalization record. This develops the missing local cancellation from nonclean-reopened.md. The P6 bound is now Lean-certified at 17.60; the two shift bounds remain 34.74. The local moment/source identities below have compiled in Lean; the complete arithmetic/measure assembly has not.

## Normalization and local data

Use R=-Frame.Mn, n=16, and F(a)=sum_{k<=a}(1/k-4/(4k-o)), o=1 or 3. Thus R(a,b)=(F(a)-F(b))/(n(b-a)) off the diagonal. Work at p>=5, p>2m, p^2>4N, and with the formal core variable X=U/p^2. The Gauss residue field is K=F_p(U).

Separate F into its exact p-pole part p^-1 L and its regular part. In a fixed cut-free cell the pole prefixes L_i on corresponding core-chain nodes are constant under translation. The regular prefix modulo p is periodic with period p: each completed period of each regular reciprocal sum is zero.

For a zone node z in a cell C, put t_i=(core_i-z)/p for its core residue chain; these are negative integers. Let Q be the leading scaled core-chain matrix, b its leading source column and g=Q^-1 b. Define

    A = l - sum_i g_i L_i,       B = 1 - sum_i g_i,
    u_i = A - B L_i,            c_C = u^T Q^-1 u,
    I = -sum_i t_i g_i,         J = -sum_i t_i L_i g_i.

Here l is the pole prefix at z. Q is symmetric and monic in U on the diagonal. The actual leading entries give two identities:

    n(t_i-t_j) Q_ij = L_j-L_i,
    n t_i b_i = l-L_i.

The diagonal, including U, does not affect the commutator identity.

## The missing local cancellation

From Qg=b and the two displayed identities,

    Q (n t g) = A 1 - B L = u.

Consequently

    c_C = n (B J - A I).

This is the missing relation between the local moment term and the completed long-arc coefficient. It uses the source equation as well as the displacement equation; an ordinary-rank conclusion is not inferred from displacement rank alone.

The additional identity

    b^T(n t g) = A-B l

shows that adjoining a source-type chain node does not change the quadratic response: the old response solution extended by zero already solves the enlarged system. Both identities, and this zero-extension response lemma, are kernel checked in CatalanCore/Arith/Hybrid/LoewnerMoment.lean with exactly propext, Classical.choice and Quot.sound.

## Weighted Cauchy formula

For each residue c let Q_c be its leading core-chain matrix, L_c its vector of pole prefixes and

    c(c) = (A 1-B L_c)^T Q_c^-1 (A 1-B L_c),

with response zero for an empty chain. For c in the source cell this equals c_C. Let S be the short arc and epsilon its sign: +1 for S=[0,h), -1 for S=[h,p), where h=o/4 modulo p and the shorter of the two arcs is chosen.

The same-cell integral block of the original Schur complement has the formula

    T_zy mod p = sum_{c != z,y} w(c)/((c-z)(c-y)),
    w(c) = (c_C-c(c))/n^2 + epsilon B^2/n * 1_S(c).

This is a weighted formula. The weights need not be constant on the whole short arc or vanish at occupied long-arc points. Thus it is consistent with the explicit counterexample to the unweighted raw formula.

The derivation uses the existing double-difference factorization rather than a long inverse expansion. Contract the cross block between the z and y chains with the same vector (1,-g). Its regular term is epsilon B^2/n times the short-arc Gram kernel. Expanding the pole denominator 1/(d+(j-i)p) by one further order gives the local term

    -2(A I-B J)/(n d^2) = 2 c_C/(n^2 d^2).

The residual-product term contributes

    -sum_{c != z,y} c(c)/(n^2(c-z)(c-y)).

Terms through the z or y residue chain vanish at this order: the corresponding residual has no p^-1 term. Completing the finite-field sum with

    sum_{c != z,y} 1/((c-z)(c-y)) = 2/(z-y)^2

gives precisely the weighted formula. All denominators used in this calculation are units in the Gauss valuation ring. Exact singular blocks may be used before reduction, so no invalid identification of p-adic carries with a characteristic-p power-series variable is involved.

## Projection and free residues

The leading cross block between cells C,D is a scalar Cauchy matrix. Its scalar need not be proved nonzero. Choose supported left and right subspaces that annihilate the plain Cauchy evaluations at every zone residue outside C; counting the outside columns and rows supplies dimension at least sigma. These subspaces kill the leading cross blocks even at specializations with additional rank loss.

Only weights at uncovered long residues must vanish. Constancy, or even nonvanishing, of the short-arc weights is unnecessary for the rank bound: b surviving Cauchy columns have rank at most b with arbitrary weights. The expected free-long response equality follows either from exact transport within a pole interval or from adjoining a source coordinate and extending the response solution by zero. The endpoint case where a physical residue representative crosses the core boundary still needs to be linked uniformly to this argument.

One does not need to assume that the leading corank is exactly sigma. Choose sigma independent left and right kernel vectors supported in the overfull cell. Lift their bases to integral invertible row/column operations. The selected sigma rows and columns are divisible by p. Reducing their intersection after division by p has rank at most b, so a further integral row operation makes sigma-b of those rows divisible by p^2 on the selected columns. Assign row valuation one to these sigma-b rows and column valuation one to the sigma selected columns. The determinant has valuation at least 2 sigma-b. Together with the leading sigma bound this gives

    v(det(pT)) >= sigma + max(0,sigma-b).

This argument avoids an additional generic-full-rank hypothesis.

## The second family member

Its extra common node is q=r+2m. Eliminating the augmented common core leaves the original m zone rows and columns. Because p>2m, q has a residue distinct from all original zone nodes. The leading cross blocks and their kernel constraints are unchanged. Only the quadratic response at residue q changes, so the next map changes by rank at most one. Its rank is at most b+1. The augmented core costs two additional valuation units; losing at most one extra next-level unit gives a fixed cost of at most three relative to the first member's budget. This per-prime constant contributes O(r), not a new quadratic constant.

## Current evidence and remaining implementation

The explicitly predicted weights, computed from the small chain matrices and source moments, reproduce the raw same-class block in the controls; they are not fitted constants. The expanded control batch also checks that free long-arc weights vanish, free short-arc weights are constant and the singular-prefix jumps at occupied outside cells are nonzero. These checks corroborate the derivation but do not replace its uniform proof.

The expanded batch passes 685 exact controls, including specializations with extra leading-rank loss. The local source/moment identities, finite-field completed Cauchy sum, support projection rank bound, and abstract two-level determinant lemma now compile in Lean. The determinant lemma proves divisibility by pi^(sigma+(sigma-b)) for a block matrix [[pi H, pi B],[pi C,D]] when the residue rank of H is at most b. It uses the existing rank-divisibility theorem and an elementary kernel embedding, with no Smith normal form.

The rational barycentric Cauchy bases now compile in `CauchyKernelBasis.lean`: their entries reduce correctly, their determinants are prime units, and their first sigma columns annihilate the required rational Cauchy evaluations exactly. The determinant lemma now cancels such primitive row and column changes. Thus constructing a new Gauss valuation ring, or lifting an arbitrary basis over F_p(U), is unnecessary.

The regular/pole split also compiles. The regular reciprocal-difference prefix has zero period sum. On congruent nodes below p^2, `Good p (p * regularLoewner) 0`; consequently the actual p^2-scaled core agrees with the exact pole model through first order. The exact pole prefixes are constant across cut-free intervals, and `poleScaledEntry_transport` transports an entry exactly in characteristic zero when its prefixes and displacement agree. The source/moment identities have been generalized to arbitrary commutative rings with a common clearing scalar H. This allows polynomial partners, avoiding derivatives of actual inverse matrices.

The finite-field lower-arc potential identity and the complementary potential identity are checked separately. Their combination handles the two orientations of the short arc without harmonic reflection casework.

The quadratic-extension control batch uses the exact ring (Z/p^3)[t]/(t^2-d), with d a nonsquare mod p. It tests U=t, 1+t, and 2+3t, rather than only constant U in F_p. All 21 in-scope controls pass; six further cases have no in-scope long cell. This strengthens the experimental check without proving an identity over F_p(U).

## Checkpoint and precise unproved remainder

This pass does **not** prove the non-clean next-Smith law. The remaining work is:

1. Prove the displayed weighted-entry identity for the actual scaled frame and its cleared partners, including the divided second-difference and residual-product formulas.
2. Prove the free-long response equality uniformly, including the core-boundary case and the common extra node in the second family member.
3. Apply the checked barycentric basis, weighted projection and two-level determinant lemmas to that actual matrix; then certify the conditional 13-row prime profile and assemble the measure bound for both shifts.

The failure mode of this pass is a missing uniform arithmetic identification, not a numerical counterexample or a rank-to-valuation problem. The old unweighted raw shortcut is false; the weighted replacement has supporting exact controls and checked ingredients but is not yet an unconditional local theorem. In particular, the moment identity alone does not certify the weighted Schur formula, and the pole-model approximation alone does not identify its next coefficient.

The exact forecast remains gain 89831/18670080 and ratio 89200974720/2623980503 = 33.99452649..., conditional on all three steps above. Neither 34.00 nor this forecast is exported as a theorem. The public shift bounds remain 34.74. This is a reproducible proof checkpoint for a later pass.

`CatalanCore/Arith/Hybrid/NextLevelAudit.lean` imports and prints the axioms of the proved ingredients. They use only propext, Classical.choice and Quot.sound. The open arithmetic statements are recorded here, not introduced as Lean assumptions.

Reproduction: install `python-flint`, then run `check-weighted-law.py` and `nonclean-extension-controls.py` from this directory, under the project resource guard. `nonclean-exact-forecast.py` computes the conditional profile using exact fractions. JSON files preserve the full control records; the scripts are experimental evidence, not Lean certificates.
