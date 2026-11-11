# Proof issues and replacements

## Lemma 3.18: replacement for the left-endpoint estimate

The complete replacement proof now compiles in `RVLinearity.lemma_3_18` and
passes the fresh full 794-head local integration audit and CI 42947193955.
All complete types and source hashes match. It retains the original full parameter base,
with genuine saturation, infinite cardinal, small real base, ACVF00 and an
original-base named nontrivial Gamma value explicit. The endpoint inference
described below is not used by this proof.

In arXiv:0809.0473v2, page 9, the second half of the proof constructs a
value-group function `zeta` from values of an affine error. It uses piecewise
affinity and `zeta(t) > t` to conclude that `zeta(t) > d` for inputs sufficiently
close to the upper endpoint `d` from below.

Those two properties alone do not imply this conclusion. On any interval
`(a,d)` in the ordered divisible group of rationals, the affine function

```
zeta(t) = (t + d) / 2
```

satisfies `t < zeta(t) < d` for every input. Both positive differences are
`(d-t)/2`. The same example is definable in the ordered divisible group
language. Strict monotonicity does not exclude it.

The actual `zeta` comes from a definable VF map and may have an additional
constraint that repairs the printed argument. The observation above is not
an ACVF counterexample to Lemma 3.18. The checked replacement avoids the
endpoint estimate, without a statement correction or an unproved input.

The following components are checked separately, with their exact
characteristic, parameter and saturation hypotheses:

- Actual nonzero RV fibres are ordinary open balls, and fixed-value shells
  contain infinitely many disjoint such fibres.
- Genuine real saturation produces a nonalgebraic member of that interpreted
  family; checked Lemma 3.2 makes it atomic over its ball name.
- Full-code RV-coefficient rows have finite order controllers. Their finite
  image implies one constant RV coefficient on a final Gamma tail.
- The normalized first-order affine-error expression agrees with the actual
  VF expression. Its partial-domain graph is definable over the stated base.
- Lemma 3.9 makes the actual RV affine error constant on an atomic open ball.
- Equal error values and the appropriate strict increment bound recover the
  affine RV difference, including the zero-error case.

The replacement proceeds directly from any two distinct coefficient values.
After finitely naming real codes, choose a new atomic RV fibre at the lower
value and form the actual translated affine error. Its values are strictly
above the radius scaled by the original Gamma-linear coefficient. A pair
at the higher value realizes exactly that scale for the error difference.

VF algebraic exchange, genuine saturation and finite-fibre means prove that
the real-definable error map on that atomic fibre is constant or injective.
The pair excludes constancy. Applying checked 3.16 to the error map forces
its image radius to equal the scaled source radius. Its strict output-value
bound then puts zero in this atomic open image, a contradiction.

`RVSlopeRigidity.ordered_coefficients_eq` proves coefficient equality by
this argument. `RVLinearity.lemma_3_18` supplies the Gamma-linear premise
using checked 3.16 and proves the actual RV equation for every source pair,
including equal points. Temporary real codes occur only inside the proof;
the original source is never assumed atomic over that enlarged base.

The full post-paper comparison writeup is tracked in `../PROOF-WRITEUP.md`.

## Proposition3.24 literal boundary

The nonempty whole-field identity counterexample is checked in
Proposition324WholeFieldBoundary.counterexample. The author was asked to
excludeVFas closed parent by requiring an ordinary Gamma radius; approval
is pending. Do not count an ordinary-parent theorem as the literal full
statement without that clarification. Gamma interval and quotient-map work
remain open. See ../STATEMENT-QUESTIONS.md.
