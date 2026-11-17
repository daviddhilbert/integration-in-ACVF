module

public import Integration7.CanonicalFiniteRVObjects
public import IntegrationSection5.StandardContractionNormalization
public import Integration7.GradedVolumeProducts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual canonical normalized finite contraction object, with
finiteness transported through the checked normalization isomorphism.
The entire RV volume tuple is preserved exactly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ} {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

def canonicalNormalizedFiniteContraction (hc : CanonicalStructure.IsCanonical (M := M))
    (C : StandardContraction A σ)
    (hF : (canonicalRVObject hc C.contractionObject).volume.FiniteFibres) : RVFiniteObject (M := M) S n :=
  ⟨canonicalRVObject hc C.normalizedObject,(finite_volume_iso (canonicalRVIso hc C.normalizationIso)).mp hF⟩

def canonicalFiniteNormalizationIso (hc : CanonicalStructure.IsCanonical (M := M))
    (C : StandardContraction A σ) (hF : (canonicalRVObject hc C.contractionObject).volume.FiniteFibres) :
    (⟨canonicalRVObject hc C.contractionObject,hF⟩ : RVFiniteObject (M := M) S n) ≅
      canonicalNormalizedFiniteContraction hc C hF := rvFiniteIsoOfAmbient (canonicalRVIso hc C.normalizationIso)

theorem canonical_finite_normalization_volume (hc : CanonicalStructure.IsCanonical (M := M))
    (C : StandardContraction A σ) (hF : (canonicalRVObject hc C.contractionObject).volume.FiniteFibres)
    (u : (canonicalRVObject hc C.contractionObject).domain) :
    (canonicalNormalizedFiniteContraction hc C hF).obj.value (finiteIsoMap (canonicalFiniteNormalizationIso hc C hF) u) =
      (canonicalRVObject hc C.contractionObject).value u :=
  toFirstVolume_volume (Map.image (rawLabelMap C.target)) C.volumeIndex ⟨u.val,u.property⟩

end IntegrationInACVF.Section7
