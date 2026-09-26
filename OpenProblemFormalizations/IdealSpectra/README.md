# Ideal spectra: N02 and N04

Source: Tom Benhamou, *Scales in the Point Spectrum*, arXiv:2603.00305v1, Definition 3.7 and Questions 3.17–3.18.

`RectangularIdeal.lean` formalizes the noncofinal ideal on `ℕ × ω₁` and proves that no preorder can represent the cohesive spectrum for all directed sets: the tests `ℕ`, `ω₁`, and `PUnit` already contradict such a representation. This is a ZFC negative answer to the specified instance of Question 3.17, subject to independent literature-priority review.

`CountableBoundary.lean` proves a countable local lemma: an unbounded sequence in a directed preorder can be made increasing with every cofinal subsequence unbounded. It does not solve the general Question 3.18.

`TukeyMaps.lean` proves the equivalence between the existing cofinal-subset definition and the reverse-direction unbounded-set definition, for arbitrary preorders. `RectangularClassification.lean` now proves the exact cohesive class: for two nonempty linear orders K and L without greatest elements, and any target preorder Q, Q is cohesive for the noncofinal ideal on K x L exactly when K or L Tukey reduces to Q. This classification does not require the factors to be regular cardinals. The distinct-regular-cardinal obstruction to a representative remains a separate argument, using its cofinal-fiber hypothesis.

No `sorry` or extra mathematical axiom. `Audit.lean` checks the main declarations and standard Lean axiom dependencies. Lean checks do not establish novelty or the full paper statement beyond the explicitly formalized definitions.

`Representability.lean` proves an exact structural criterion: the rectangular cohesive class has a universal representative exactly when the two factors are Tukey comparable. It permits an arbitrary proposed representative; its reductions to the directed factors force it to be directed, making it a valid test object. The smaller factor represents the class in the comparable case. This is a consequence of the exact class theorem, not a separate claim of novelty.
