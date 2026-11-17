module

public import Integration7.HKRVProductIsomorphisms
public import Integration7.HKDegreeOnePrincipalFactors
public import Integration7.HKZeroFamilyChangeOfVariables

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Checked correction work under the weighted measured-zero convention.
The HK namespace retains the existing positive geometric objects and adds
weighted zero objects, actual mixed products, degree-one point/cone
factorization and change of variables for weighted family presentations.
The legacy all-degree coefficient/function assembly is migrated separately. -/
