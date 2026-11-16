# Statement provenance

The Challenge reproduces the author's existing language, valuation, parameter
coding and geometric definitions needed for Proposition 3.19 and Lemma 4.8.
These are extracted statements, not a separate mathematical foundation or new
axioms. The table identifies their source modules before statement packaging;
module-format visibility adapters retain mathematical types and bodies.
Author-owned code in this submission is covered by the root MIT licence,
Copyright (c) 2026 Yimu Yin. Separately fetched dependencies retain their own
licences. The existing blueprint scaffolding notice is retained.

The compiler cache-boundary command follows the Special transformations
Palomar example at dd3a4a02aeedcaf322c52186fc25a959145455a6. Its effect is to
clear two compiler-only caches, without adding mathematical declarations.

| Module | Source |
| --- | --- |
| `CanonicalRV` | [ACVF-QE source](https://github.com/daviddhilbert/ACVF-QE/blob/8f90dfd22de9f2c821382830eee326d1f0cf4990/Proofs/CanonicalRV.lean) |
| `CanonicalStructure` | [ACVF-QE source](https://github.com/daviddhilbert/ACVF-QE/blob/8f90dfd22de9f2c821382830eee326d1f0cf4990/Proofs/CanonicalStructure.lean) |
| `Enc` | [ACVF-QE source](https://github.com/daviddhilbert/ACVF-QE/blob/8f90dfd22de9f2c821382830eee326d1f0cf4990/Proofs/Enc.lean) |
| `IntegrationSection3.ImaginaryBaseImages` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%203/IntegrationSection3/ImaginaryBaseImages.lean) |
| `IntegrationSection3.ImaginaryFamilies` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%203/IntegrationSection3/ImaginaryFamilies.lean) |
| `IntegrationSection3.ImaginaryParameters` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%203/IntegrationSection3/ImaginaryParameters.lean) |
| `IntegrationSection3ACVF.BallPresentation` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%203/IntegrationSection3ACVF/BallPresentation.lean) |
| `IntegrationSection3ACVF.FullBaseAtomicity` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%203/IntegrationSection3ACVF/FullBaseAtomicity.lean) |
| `IntegrationSection3ACVF.FullGammaSyntax` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%203/IntegrationSection3ACVF/FullGammaSyntax.lean) |
| `IntegrationSection3ACVF.FullOpenToOpenPartition` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%203/IntegrationSection3ACVF/FullOpenToOpenPartition.lean) |
| `IntegrationSection3ACVF.GammaLinearity` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%203/IntegrationSection3ACVF/GammaLinearity.lean) |
| `IntegrationSection3ACVF.GammaRadiusAtomicity` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%203/IntegrationSection3ACVF/GammaRadiusAtomicity.lean) |
| `IntegrationSection3ACVF.MaximalOpenClasses` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%203/IntegrationSection3ACVF/MaximalOpenClasses.lean) |
| `IntegrationSection3ACVF.PaperBalls` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%203/IntegrationSection3ACVF/PaperBalls.lean) |
| `IntegrationSection3ACVF.ParameterPresentation` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%203/IntegrationSection3ACVF/ParameterPresentation.lean) |
| `IntegrationSection4.BalancedFibres` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%204/IntegrationSection4/BalancedFibres.lean) |
| `IntegrationSection4.Cells` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%204/IntegrationSection4/Cells.lean) |
| `IntegrationSection4.GammaRVMaps` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%204/IntegrationSection4/GammaRVMaps.lean) |
| `IntegrationSection4.RVLabelSlices` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%204/IntegrationSection4/RVLabelSlices.lean) |
| `IntegrationSection4.TwoCellDecomposition` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%204/IntegrationSection4/TwoCellDecomposition.lean) |
| `IntegrationSection4.VerticalPullbackCells` | [integration-in-ACVF source](https://github.com/daviddhilbert/integration-in-ACVF/blob/2c29c5b848f9077274774125222bba563cdc11b4/section%204/IntegrationSection4/VerticalPullbackCells.lean) |
| `QF2Fragment` | [ACVF-QE source](https://github.com/daviddhilbert/ACVF-QE/blob/8f90dfd22de9f2c821382830eee326d1f0cf4990/Proofs/QF2Fragment.lean) |
| `RVCalc` | [ACVF-QE source](https://github.com/daviddhilbert/ACVF-QE/blob/8f90dfd22de9f2c821382830eee326d1f0cf4990/Proofs/RVCalc.lean) |
| `Section3.ClosedBallCodes` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/ClosedBallCodes.lean) |
| `Section3.ClosedBallQuotient` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/ClosedBallQuotient.lean) |
| `Section3.GammaCodeDefinability` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/GammaCodeDefinability.lean) |
| `Section3.GammaCodes` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/GammaCodes.lean) |
| `Section3.GammaDefinability` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/GammaDefinability.lean) |
| `Section3.GammaOperations` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/GammaOperations.lean) |
| `Section3.GammaParameters` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/GammaParameters.lean) |
| `Section3.GammaPresentation` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/GammaPresentation.lean) |
| `Section3.GammaRVSeparation` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/GammaRVSeparation.lean) |
| `Section3.GammaValueEquiv` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/GammaValueEquiv.lean) |
| `Section3.GammaValueLaws` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/GammaValueLaws.lean) |
| `Section3.GeneralBallCenters` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/GeneralBallCenters.lean) |
| `Section3.ModelContext` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/ModelContext.lean) |
| `Section3.OpenBallCodes` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/OpenBallCodes.lean) |
| `Section3.ValueQuotient` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section3/ValueQuotient.lean) |
| `Section5.GammaGraphs` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section5/GammaGraphs.lean) |
| `Section5.Geometry` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section5/Geometry.lean) |
| `Section5.TransformGeometry` | [special-transformations source](https://github.com/daviddhilbert/special-transformations/blob/23157ace335d7c482add99be69d42c07b4ba1d30/Section5/TransformGeometry.lean) |
| `VFField` | [ACVF-QE source](https://github.com/daviddhilbert/ACVF-QE/blob/8f90dfd22de9f2c821382830eee326d1f0cf4990/Proofs/VFField.lean) |
| `VFValued` | [ACVF-QE source](https://github.com/daviddhilbert/ACVF-QE/blob/8f90dfd22de9f2c821382830eee326d1f0cf4990/Proofs/VFValued.lean) |
