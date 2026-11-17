module

public import Integration7.GammaNativeCommonNames
public import Integration7.NativeVolumeDomains
public import Section5.GammaLift

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A Gamma isomorphism over fixed available real names is an actual
raw mixed definable bijection with exactly the same point function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (GammaIso RelationDefinable pointSpace)

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {B : Base (M := M)} {n a b : ℕ}

def gammaMixedIsoMap (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n a) S}
    {D : DefSet (rawMixedSpace (M := M) n b) S}
    (e : GammaIso B A.carrier D.carrier) (hNames : commonRealNames B ⊆ S) : Map A D := by
  let f : SpecialTransformations.Section5.Map (nativeMixedVolumeDomain hc A)
      (nativeMixedVolumeDomain hc D) :=
    @SpecialTransformations.DefinableGeometry.Map.mk LRV M (@CanonicalStructure.normalize M sM)
      _ _ S _ _ e.equiv
      (SpecialTransformations.Section5.RelationDefinable.mono _ _
        (gamma_native_graph_common_names e.graph) hNames)
  exact ⟨e.equiv,(rawSpecialMap hc f).graph_definable⟩

@[simp] theorem gammaMixedIsoMap_apply (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n a) S}
    {D : DefSet (rawMixedSpace (M := M) n b) S}
    (e : GammaIso B A.carrier D.carrier) (hNames : commonRealNames B ⊆ S) (u : A) :
    gammaMixedIsoMap hc e hNames u=e.equiv u := rfl

theorem gammaMixedIsoMap_bijective (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (rawMixedSpace (M := M) n a) S}
    {D : DefSet (rawMixedSpace (M := M) n b) S}
    (e : GammaIso B A.carrier D.carrier) (hNames : commonRealNames B ⊆ S) :
    Function.Bijective (gammaMixedIsoMap hc e hNames) := e.equiv.bijective

end IntegrationInACVF.Section7
