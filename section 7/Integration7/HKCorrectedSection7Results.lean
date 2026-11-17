module

public import Integration7.HKSection7Results
public import Integration7.HKGradedHeadIntegralLinearMaps
public import Integration7.HKGradedPrefixIntegralLinearMaps
public import Integration7.HKRawRingSupportedFunctionIntegrals
public import Integration7.HKNormalizedVolumeCommRing

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Corrected Section 7 public interfaces: the weighted class theorems,
actual full-coefficient raw head, coordinate and supported Jacobian
operators, balanced unnormalized ring-valued Fubini and change of
variables, and normalized supported Theorems 7.14–7.15. The standing
hypotheses and accepted nonempty-selected scope of Lemma 7.5 are retained.
The earlier HKSection7Results aggregate records its historical boundary;
the additional raw linear and ring interfaces are imported here. -/
