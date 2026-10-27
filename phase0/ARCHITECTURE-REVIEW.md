# Phase 0 architecture review

27 October 2026. Independent source/contract review by the prefix-audit lane. No builds or changes to Lean sources were made in this review. Sources checked: LEAN-PLAN and handoff; GENERAL-MEASURE-THEOREM.md; hybrid GENERAL-NONVANISHING-THEOREM.md; G GENERAL-NONVANISHING-THEOREM.md; spec v8; uniform-decay-proofs main/arithmetic plus local moment, jet and energy rules in hybrid.tex; polygon Part 2 deformation; signed-spline-decay mass/TV, cell-energy and atomic-approximation rules. Actual PilotCorner, PilotEnergy, representative PilotPotential/PilotRank declarations and the final PilotRemainder arithmetic declaration were inspected. This review does not assert that unobserved builds succeeded.

## Assessment

The current pilots are appropriate bounded Phase 0 evidence if reported with their present limits. They do not discharge a source theorem, analytic checker soundness, HasDecay/HasContent or a banked measure. Successful arithmetic checks support the chosen representation and declaration sizes for that measured workload; they do not establish a production kernel total or complete analytic-cell feasibility.

### Signed potential and energy

The full rationalized chi3 field with 114 physical conjugate pieces is substantially more representative than an isolated toy log expression. Its 466 shared log/arctan inputs and eight order-8 Bernstein values test literal elaboration, shared input checking and signed linear expression assembly. The final cell half-width is h=1e-7. The generator now checks all eight exact symbolic jet coefficients against independent high-order Arb jets, and PilotRemainder adds 698 rational L1 endpoint-tail contributions with scaled sum 407569108 at scale 1e36+39 (about 4.08e-28). This materially improves workload coverage over evaluating Bernstein coefficients alone. These are still finite arithmetic and mirror checks; the generic log-jet/error semantics and expression-integrity theorem are not yet Lean proofs. The earlier large-cell sample is superseded and is not certified by the final pilot. The mass-one repair must remain in provenance: it produces a new exact trial and does not preserve the saved floating optimum by assertion.

PilotEnergy now certifies both a negative-density piece's self-energy expression and the opposite-sign mutual interaction (negative piece 86, positive piece 0), using 18 shared logarithm inputs. The generator independently compares the mutual value with direct spline_energy.mutual (Arb). The coordinator reports the final successful build with 152 ms kernel time across the two checks; this review inspected the added declarations but did not run a build. This addresses the missing opposite-sign arithmetic control: self-energy alone would be invariant under reversing a piece's overall sign. It remains a bounded two-interaction workload, not complete mutual-energy or sign-safe semantic assembly. The mutual interval width is 2354887217686778578533784203926/(1e36+39), about 2.35e-6. Its short-piece conditioning is therefore a production precision risk to measure before extrapolating checker cost or certified energy tightness. No production energy bound is claimed.

Outstanding prerequisites before these tapes become analytic certificates:

1. Prove integer log/arctan error semantics, positivity/domain guards, range-reduction and branch conventions for the actual Input/Expression checker.
2. Prove generated expression integrity from exact segment/density data: the tape must equal the specified moments/jet/energy expression, not merely be small.
3. Prove exact mass one and conjugation for the exported Lean trial, and verified absolute-density Bernstein bounds giving V and B_sigma.
4. For a full cell, verify endpoint distances, no transverse crossing or the appropriate modulus case, and prove that the now-checked order-8 rational remainder majorant bounds the actual analytic tail. The rational majorant workload is present; its semantic soundness bridge remains open. Bernstein coefficients and a small rational tail sum alone are not a continuum potential theorem.
5. Prove the elementary energy identity (or use full-potential cell enclosures) and sign-safe weighted assembly. Signed energy cells require m_J*u_J + e_J*v_J with v_J >= integral |f|, not positive-mass endpoint multiplication. A full I(sigma) needs every required interaction or a proved alternative enclosure.
6. Later decay assembly also requires common-support and contour bounds, cap, tail, node energy, smoothing/atomization and all-common-deletion transport. The signed error charges use V and V^2; signed mass cannot substitute for total variation.

### Polygon corner

PilotCorner explicitly defines a segment-integral primitive, identifies it with the paper's radial integral, and derives the derivative/corner identity from Mathlib's convex primitive theorem. It instantiates the saved chi3 frame coefficients (1/18,-1/12,1/36) at shifts (1/3,1/2,1), and an exact rational reconstruction of an interior selected normalized corner. This is honest evidence that S10's finite interior-corner route is available without building a general Cauchy-on-polygons library.

This is not yet the physical polygon deformation theorem. The pilot is on the convex upper half-plane; the paper's full domain is the upper half-plane union a pole-free disk at the real cleared vertex, star-shaped about that vertex. Outstanding prerequisites are the physical scale/translate normalization, real-start disk holomorphy/pole gap, patching or a star-shaped primitive argument, actual reference and polygon tail convergence, and the exponentially vanishing connector estimate. The full theorem also needs conjugate orientation and source/Gram representation. These are explicit future obligations, not an objection to the interior pilot.

### D58 rank

PilotRank states exactly rational source-map factorization facts: a 20-by-3 basis with a checked left inverse and ten image-rank upper bounds for D58-L0203 at the right endpoint x=26. This is appropriate finite rank-packet evidence. The pilot correctly leaves physical-prefix transport, chart coverage, weights/interval membership and reduction outside fixed exceptions separate. A rational rank bound alone does not instantiate NullityLB over ZMod p; the basis and factorization denominators and any required nonzero witnesses must enter the finite exception integer.

## Provider scope and controls

The measure source requires the same normalized family and every selected common-deletion member in content, decay and nonvanishing. General step-component NV may require the conservative sbar deletion depth; an existing one-common-deletion packet cannot be silently promoted to that family. Lambda keeps its matched pair selector. For unshifted G use the existing complete DesignData/PayW/recycled measure route, not the hybrid gamma*c/(D-Lambda) formula. Direct per-design C3 remains the Phase 1 G obligation; prime-scaling inheritance stays Phase 5.

The released banks are successful controls, not parity evidence for the new route. The rational-root and failed-visibility adversaries in the measure/NV papers show why finite arithmetic/analytic success cannot replace selection on the same member family. Nothing in these pilots excludes a representation family or narrows the four theorem domains.

## Reporting recommendation

Report arithmetic kernel timings, wrapper/admission time and memory separately, with each build's own completion evidence. Call block-size decisions provisional for the measured workload until the soundness/remainder/energy assembly costs are included. State that the finite interior primitive route was piloted; do not say real-start/improper polygon deformation was proved. Preserve the full theorem scope and carry the outstanding prerequisites into later phases.
