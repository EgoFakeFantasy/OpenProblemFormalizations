# Verification update: September 26, 2026

The local full-library build, explicit statement checks, forbidden-construct scan, module-coverage check, and axiom audit pass. The audit counts 140 project declarations and 108 theorem constants, including generated helper declarations. These are repository totals, not a count of distinct new mathematical results. The only permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

## N02: exact classification is now kernel checked

`IdealSpectra/TukeyMaps.lean` connects the cofinal-subset definition already used by the project with the reverse-direction definition using maps that preserve unbounded sets. Both directions are proved for arbitrary preorders.

`IdealSpectra/RectangularClassification.lean` proves that, for nonempty linear orders K and L with no greatest elements and any target preorder Q,

    Q is cohesive for the noncofinal ideal on K x L
      iff TukeyLE K Q or TukeyLE L Q.

The proof uses a bad unbounded slice for each second coordinate, then a second bad unbounded set for the slice bounds. In a linear order every unbounded set is cofinal. This produces a cofinal rectangle subset with bounded image, contradicting cohesiveness.

No cardinal regularity or directedness of Q is required for this classification. The separate nonrepresentation theorem still uses a cofinal-fiber hypothesis; its concrete natural-number/omega-one instance was already checked. The new classification does not decide N04 or certify literature priority.

## N02: exact representability criterion

`IdealSpectra/Representability.lean` now proves that this rectangular cohesive class admits a universal representative if and only if the two factors are Tukey comparable. When K is Tukey-below L, K itself represents the class, and conversely with the roles reversed.

The negative direction does not assume the proposed representative P is directed. Reductions from P to the nonempty directed factors force P to be nonempty and directed; P therefore qualifies as a test target. Its identity reduction gives cohesiveness, and the exact class theorem forces one factor below P, hence below the other factor. The implementation quantifies targets and representatives in a common universe and uses the project's cofinal-subset definition throughout.

This is a structural consequence of the existing exact classification. It does not claim a new answer to N04, a new regular-cardinal fiber instantiation, or literature priority. A concrete natural-number square tests the positive direction, so the representability assertion includes nonvacuous instances.

## E05: repair of an inconsistent interface

The previous skeleton used a natural-valued function on all subsets of the natural numbers with global monotonicity. It also used divergence on finite initial segments of every infinite set. Together these imply a contradiction: choose the divergence threshold to be the value on the entire infinite set, which bounds every initial segment by global monotonicity.

`not_globalMonotone_divergent_natGauge` now proves this exact incompatibility. The old theorems were conditional statements accepted by Lean, but the two conditions could not jointly model the intended gauge. Their combined use therefore did not establish a nonvacuous instance.

`FiniteGaugeMonotone` replaces global monotonicity by monotonicity when the upper set is finite. Every row set evaluated by `crossingBounded` is finite, so all uses in the existing crossing proofs meet this weaker hypothesis. The affected proofs have been recompiled.

`countingGauge`, defined using finite cardinality, supplies a concrete witness to finite monotonicity, subadditivity, singleton normalization, and initial-segment divergence. The concrete `countingGauge_web_and_closure_obstruction` combines the finite-row web with the finite-coordinate closure obstruction under these compatible assumptions.

Counting measure is only a consistency witness for the skeleton. It fails the special disjoint-block compression needed to exclude uncountable suns: three singleton blocks of indices 3, 4, and 5 already have union cost 3, exceeding twice the largest individual cost. Thus this update is not a complete formalization of E05's proposed counterexample.

The paper proof uses an extended-valued submeasure and does not impose the inconsistent natural-valued global interface. Its status as an internally complete candidate is unchanged. The concrete compressed gauge, its compact cost levels, the uncountable thinning, and the equivalence with Cantor topological closure remain outside the kernel proof.

## Reproduction

Run `lake build`, `lake env lean Check.lean`, and `lake env lean Audit.lean`, or run `verify.ps1` with PowerShell 7. The manifest records exact source hashes and the pinned mathlib revision. On a machine where dependencies are owned by another local user, give only the relevant repository paths process-local Git trust; do not delete or re-download the shared dependency cache in response to an ownership check.
