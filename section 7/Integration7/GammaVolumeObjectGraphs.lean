module

public import Integration7.GammaRVMapRestrictions
public import Integration7.GammaCanonicalElementaryGraphs

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A property of the existing actual volume objects, recording full
original-Gamma coordinate and density graphs. Restrictions retain both. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

structure VolumeObjectGamma (U : PositiveRVVolumeObject (M := M) S k) (B : Base (M := M)) : Prop where
  coordinates : RVMapGamma U.underlying.obj.volume B
  density : RVMapGamma U.form.map B

theorem VolumeObjectGamma.restrict {U : PositiveRVVolumeObject (M := M) S k}
    (hU : VolumeObjectGamma U B)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier)
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ A.carrier}) :
    VolumeObjectGamma (U.restrict A hA) B :=
  ⟨hU.coordinates.restrict hA hΓ,(hU.density.restrict hA hΓ).congr (fun _ => rfl)⟩

theorem VolumeObjectGamma.canonical
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : FiniteRV.GammaObjectAt B S (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (hω : RVMapGamma ω.map B) :
    VolumeObjectGamma
      (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) S k) B :=
  ⟨canonical_gamma_object_volume_graph hc U,hω⟩

theorem VolumeObjectGamma.elementary
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (hU : VolumeObjectGamma U B) (hAd : BlowupAdmissible U)
    (hW : RVMapGamma (elementaryVolumeObject C U hAd).underlying.obj.volume B) :
    VolumeObjectGamma (elementaryVolumeObject C U hAd) B :=
  ⟨hW,gamma_canonical_elementary_density hc C U hAd hW hU.density⟩

end IntegrationInACVF.Section7
