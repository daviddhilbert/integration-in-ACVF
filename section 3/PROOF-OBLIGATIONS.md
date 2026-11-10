# Open proof obligations

## Lemma 3.18: the left-endpoint estimate

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
constraint that repairs the argument. That constraint, or another argument
for the endpoint estimate, remains to be proved. This is a gap in the
justification currently available for formalization; it is not an ACVF
counterexample to Lemma 3.18. No new axiom, unproved HK input, or weakening
of the numbered conclusion has been introduced to bypass it.

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

These components do not yet assemble the right-local-constancy statement or
the global RV-linearity conclusion. The numbered result remains open.
