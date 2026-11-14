import Integration7.RVVolumeMorphisms
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a n k : ℕ}

theorem RVAlmostEverywhere.of_smallDimension
    {A : DefSet (rawRVSpace (M := M) a) S} (hd : rvDim A<n) (P : A → Prop) :
    RVAlmostEverywhere A n P :=
  ⟨A,Set.Subset.refl _,hd,fun p hp => False.elim (hp p.property)⟩

def RVVolumeIso.of_gamma_of_smallDimension
    {U V : PositiveRVVolumeObject (M := M) S k} (e : U.essential ≅ V.essential)
    (hd : rvDim U.essential.obj.domain<k+1)
    (hγ : ∀ u : U.essential.obj.domain,
      Values.vrv (U.essentialForm.value u)=Values.vrv (V.essentialForm.value (finiteIsoMap e u))*
        (rvGammaJacobian (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e u))
          (U.essential_nonzero u) (V.essential_nonzero (finiteIsoMap e u))).val) : RVVolumeIso U V :=
  ⟨e,hγ,RVAlmostEverywhere.of_smallDimension hd _⟩
end IntegrationInACVF.Section7
