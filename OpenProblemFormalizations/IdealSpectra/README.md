# Ideal spectra: N02 and N04

Source: Tom Benhamou, *Scales in the Point Spectrum*, arXiv:2603.00305v1, Definition 3.7 and Questions 3.17–3.18.

`RectangularIdeal.lean` formalizes the noncofinal ideal on `ℕ × ω₁` and proves that no preorder can represent the cohesive spectrum for all directed sets: the tests `ℕ`, `ω₁`, and `PUnit` already contradict such a representation. This is a ZFC negative answer to the specified instance of Question 3.17, subject to independent literature-priority review.

`CountableBoundary.lean` proves a countable local lemma: an unbounded sequence in a directed preorder can be made increasing with every cofinal subsequence unbounded. It does not solve the general Question 3.18.

No `sorry` or extra mathematical axiom. `Audit.lean` checks the main declarations and standard Lean axiom dependencies. Lean checks do not establish novelty or the full paper statement beyond the explicitly formalized definitions.
