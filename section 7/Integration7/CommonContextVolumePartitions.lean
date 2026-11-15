import Integration7.CommonContextVolumeEquivalences
import Integration7.GammaActualVolumePartitions
import Integration7.GammaVolumeBlowupAddition

/-! Complementary Gamma restrictions assemble comparisons of actual
volume objects. Both common witness contexts and the full partition
volume isomorphisms are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {k : ℕ}

def GammaVolumeObjects.restrict (U : GammaVolumeObjects G S k)
    (A : DefSet (rawRVSpace (M := M) U.val.underlying.obj.arity) S)
    (hA : A.carrier ⊆ U.val.underlying.obj.domain.carrier)
    (hΓ : GammaSetDefinable G {p : Point (M := M) 0 U.val.underlying.obj.arity | p.2 ∈ A.carrier}) :
    GammaVolumeObjects G S k := ⟨U.val.restrict A hA,U.property.restrict A hA hΓ⟩

def GammaVolumeObjects.complement (U : GammaVolumeObjects G S k)
    (A : DefSet (rawRVSpace (M := M) U.val.underlying.obj.arity) S)
    (hΓ : GammaSetDefinable G {p : Point (M := M) 0 U.val.underlying.obj.arity | p.2 ∈ A.carrier}) :
    GammaVolumeObjects G S k :=
  ⟨U.val.restrict (U.val.underlying.obj.domain.sdiff A) Set.sdiff_subset,
    U.property.restrict _ Set.sdiff_subset ((gammaLogicInput G).sdiff U.property.coordinates.domain hΓ)⟩

namespace CommonContextVolumeEquivalent
variable {C : BaseContext M}

theorem coprod (hc : CanonicalStructure.IsCanonical (M := M))
    {U V U' V' : GammaVolumeObjects G (C.base : Set M) k}
    (h : CommonContextVolumeEquivalent G C U U') (g : CommonContextVolumeEquivalent G C V V') :
    CommonContextVolumeEquivalent G C (U.coprod V) (U'.coprod V') := by
  obtain ⟨D,hCD,h⟩ := h
  obtain ⟨E,hCE,g⟩ := g
  obtain ⟨F,hDF,hEF⟩ := volume_context_join_exists D E
  exact ⟨F,hCD.trans hDF,(h.extend hDF).coprod hc F (g.extend hEF)⟩

theorem of_complementary_restrictions (hc : CanonicalStructure.IsCanonical (M := M))
    (U V : GammaVolumeObjects G (C.base : Set M) k)
    (A : DefSet (rawRVSpace (M := M) U.val.underlying.obj.arity) (C.base : Set M))
    (B : DefSet (rawRVSpace (M := M) V.val.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.val.underlying.obj.domain.carrier)
    (hB : B.carrier ⊆ V.val.underlying.obj.domain.carrier)
    (hAΓ : GammaSetDefinable G {p : Point (M := M) 0 U.val.underlying.obj.arity | p.2 ∈ A.carrier})
    (hBΓ : GammaSetDefinable G {p : Point (M := M) 0 V.val.underlying.obj.arity | p.2 ∈ B.carrier})
    (hLeft : CommonContextVolumeEquivalent G C (U.restrict A hA hAΓ) (V.restrict B hB hBΓ))
    (hRight : CommonContextVolumeEquivalent G C (U.complement A hAΓ) (V.complement B hBΓ)) :
    CommonContextVolumeEquivalent G C U V := by
  have hU : CommonContextVolumeEquivalent G C ((U.restrict A hA hAΓ).coprod (U.complement A hAΓ)) U :=
    .of_iso (volumeComplementPartitionIso hc C U.val A hA)
      (gamma_actual_volume_complement_partition hc C U.val U.property A hA hAΓ)
  have hV : CommonContextVolumeEquivalent G C ((V.restrict B hB hBΓ).coprod (V.complement B hBΓ)) V :=
    .of_iso (volumeComplementPartitionIso hc C V.val B hB)
      (gamma_actual_volume_complement_partition hc C V.val V.property B hB hBΓ)
  exact (hU.symm hc).trans hc ((hLeft.coprod hc hRight).trans hc hV)

end CommonContextVolumeEquivalent
end IntegrationInACVF.Section7
