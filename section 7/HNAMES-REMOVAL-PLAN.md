# Removing `hNames` from Section 7 (plan, November 18, 2026)

## Decision

The corrected Section 7 theorems (`IntegrationInACVF.Section7.HK`, 7.7–7.15)
assume `hNames : commonRealNames ⟨C.base, Ξ⟩ ⊆ C.base`. That says the base
contains an RV representative, chosen by `Classical.choose`, of every Gamma
name in `Ξ`. The paper's base is VF-Gamma-generated with no RV points
assumed. The author's convention: "if we assume the base is such and such,
then that means every definable artefact uses that base, including the
objects in the categories". So the Section 7 categories must contain the
objects definable over the Gamma-named base `B = ⟨C.base, Ξ⟩`, including those
that use Gamma points not definable from real points. Replacing `hNames` by
"names definable over the real base" is not enough.

New helper lemmas go here (integration-in-ACVF), not in special-transformations,
so no provider pin cascade is triggered.

## Diagnosis

- 423 Section 7 files mention `hNames`; 61 files (about 92 lines) genuinely use
  it. Almost all uses are `X.common_names.mono hNames`: a Gamma-named set is
  declared a raw object over `C.base`.
- The cause is that the Section 7 categories are raw over the real base:
  `RVVolumeObject (C.base) n`, `VFVolumeObject (C.base) n`,
  `VFVolumeClasses hc C`, `RVVolumeBlowupClasses hc C`.
- Sections 5 and 6 already work over Gamma-named bases without `hNames`.
  Closed Section 6 uses `GammaObjectAt B S n`: an RV object over a code set
  `S ⊇ B.real`, whose domain and volume graphs are `GammaSetDefinable B` /
  `GammaGraphDefinable B`; classes are taken up to Gamma-definable
  isomorphisms. `commonRealNames` appears there only inside proofs.
- Section 7 already has part of this on the RV side:
  `GammaVolumeObjects B S k` and `GammaVolumeIsoClasses hc C B k`
  (`GammaVolumeIsomorphismClasses.lean`), and `VolumeObjectGamma`.

## Design

1. Gamma-named categories over `B`: VF and RV volume objects over a small
   code set `S ⊇ C.base` whose domains, volume forms and (for morphisms)
   graphs are Gamma-definable over `B`; classes up to Gamma-definable
   isomorphisms / volume blowups. Prove the classes do not depend on `S`
   (change of codes, as `GammaObjectAt.changeBase` / `gammaObjectAtExtend`).
2. Replace each `X.common_names.mono hNames` by choosing the code set
   `S := C.base ∪ commonRealNames B`, which is small by
   `commonRealNames_small`; the object's Gamma-definability over `B` is
   already available at those call sites.
3. Restate 7.7–7.15 (and the HK entry point `HKCorrectedSection7Results`)
   over the Gamma-named categories, without `hNames`. Keep `hGenerated`,
   `γ ∈ Ξ`, `1 < γ` and the cardinal bounds. Raw-base versions for bases with
   no Gamma names (`Ξ` real-definable) can be derived as corollaries.
4. Update the Section 7 docs, blueprint and type/axiom registry.
5. diamond-integral: re-thread the 42 Section 3 files that pass `hNames`
   (measured Gamma lift, positive-degree reverse kernel) and the 78 that
   import Integration7; bump the integration-in-ACVF pin; rerun all verifiers.

## Order

Start with the RV side (it already has `GammaVolumeObjects`), then the VF
side and the integration equivalences, then the class semirings and the
7.10–7.15 statements, then diamond-integral.

## Status (November 19–20, 2026)

Steps 1–3 are done for 7.6–7.10 and 7.13: see `Integration7.GammaNamedSection7Results` and
the Gamma-named section of COMPLETION.md. The VF side needed Gamma Theorem 9.16 (provider
branch `gamma-lift-9-16`). Step 3 for 7.11/7.12/7.14/7.15 needs a parallel Gamma-named
function layer and awaits an author decision. Step 5 (diamond-integral) has not started;
see `HNAMES-API-REPORT.md`.
