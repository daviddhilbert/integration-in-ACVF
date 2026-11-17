module

public import Integration7.GammaActualVolumePartitions
public import Integration7.VolumeObjectPartitions
public import Integration7.GammaVolumeBlowupAddition

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Actual Gamma volume partition isomorphisms for two or three
definable disjoint pieces. Coordinate and density preservation follow
from the checked restriction and coproduct maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {k : ℕ}

theorem gamma_volume_object_partition
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : VolumeObjectGamma U G)
    (L R : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hL : L.carrier ⊆ U.underlying.obj.domain.carrier) (hR : R.carrier ⊆ U.underlying.obj.domain.carrier)
    (hCover : U.underlying.obj.domain.carrier = L.carrier ∪ R.carrier) (hDisj : Disjoint L.carrier R.carrier)
    (hLΓ : GammaSetDefinable G {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ L.carrier}) :
    (volumeObjectPartitionIso hc C U L R hL hR hCover hDisj).GammaDefinable G := by
  have hComp : (U.underlying.obj.domain.sdiff L).carrier = R.carrier := by
    ext r
    constructor
    · rintro ⟨hr,hn⟩
      exact ((Set.ext_iff.mp hCover r).mp hr).resolve_left hn
    · intro hr
      exact ⟨hR hr,fun hl => Set.disjoint_left.mp hDisj hl hr⟩
  have hFirst := (gamma_actual_volume_complement_partition hc C U hU L hL hLΓ).symm hc C G
  have hSecond := (hU.restrict L hL hLΓ).identity_iso hc C
  have hThird := gamma_volume_restriction_carrier_iso hc C U hU (U.underlying.obj.domain.sdiff L) R
    Set.sdiff_subset hR hComp ((gammaLogicInput G).sdiff hU.coordinates.domain hLΓ)
  exact hFirst.trans hc C G (hSecond.coprod hc C G hThird)

set_option maxHeartbeats 1800000 in
theorem gamma_volume_three_part_partition
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : VolumeObjectGamma U G)
    (A B D : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier) (hB : B.carrier ⊆ U.underlying.obj.domain.carrier)
    (hD : D.carrier ⊆ U.underlying.obj.domain.carrier)
    (hCover : U.underlying.obj.domain.carrier = (A.carrier ∪ B.carrier) ∪ D.carrier)
    (hAB : Disjoint A.carrier B.carrier) (hAD : Disjoint A.carrier D.carrier) (hBD : Disjoint B.carrier D.carrier)
    (hAΓ : GammaSetDefinable G {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ A.carrier})
    (hBΓ : GammaSetDefinable G {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ B.carrier})
    (hDΓ : GammaSetDefinable G {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ D.carrier}) :
    ∃ e : RVVolumeIso (((U.restrict A hA).coprod (U.restrict B hB)).coprod (U.restrict D hD)) U,
      e.GammaDefinable G := by
  let E := A.union B
  have hE : E.carrier ⊆ U.underlying.obj.domain.carrier := fun _ h => h.elim (fun h => hA h) (fun h => hB h)
  have hEΓ : GammaSetDefinable G {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ E.carrier} :=
    (gammaLogicInput G).union hAΓ hBΓ
  let V := U.restrict E hE
  have hV := hU.restrict E hE hEΓ
  have hAE : A.carrier ⊆ V.underlying.obj.domain.carrier := Set.subset_union_left
  have hBE : B.carrier ⊆ V.underlying.obj.domain.carrier := Set.subset_union_right
  let inner := volumeObjectPartitionIso hc C V A B hAE hBE rfl hAB
  have hInner := gamma_volume_object_partition hc C V hV A B hAE hBE rfl hAB hAΓ
  let fixA := volumeRestrictionTransIso hc C U E A hE hAE
  let fixB := volumeRestrictionTransIso hc C U E B hE hBE
  have hFixA := gamma_volume_restriction_trans_iso hc C U hU E A hE hAE hEΓ hAΓ
  have hFixB := gamma_volume_restriction_trans_iso hc C U hU E B hE hBE hEΓ hBΓ
  let innerFixed := inner.trans hc C (fixA.coprod hc C fixB)
  have hInnerFixed := hInner.trans hc C G (hFixA.coprod hc C G hFixB)
  have hED : Disjoint E.carrier D.carrier := Set.disjoint_union_left.mpr ⟨hAD,hBD⟩
  let outer := volumeObjectPartitionIso hc C U E D hE hD hCover hED
  have hOuter := gamma_volume_object_partition hc C U hU E D hE hD hCover hED hEΓ
  let keepD := RVVolumeIso.refl hc C (U.restrict D hD)
  have hKeepD := (hU.restrict D hD hDΓ).identity_iso hc C
  let f := outer.trans hc C (innerFixed.coprod hc C keepD)
  have hf := hOuter.trans hc C G (hInnerFixed.coprod hc C G hKeepD)
  exact ⟨f.symm hc C,hf.symm hc C G⟩

end IntegrationInACVF.Section7
