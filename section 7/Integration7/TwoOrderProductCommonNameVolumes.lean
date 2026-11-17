module

public import Integration7.TwoOrderProductCommonNameEssentialDomains
public import Integration7.TwoOrderProductNormalization
public import Integration7.GammaRVCommonNames

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The constructed normalized volume comparison descends to the fixed
common-name presentation. The underlying point sets, coordinate selectors
and densities agree, and the full Gamma graph supplies real definability. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.TwoOrderProductPreparations
set_option allowUnsafeReducibility true in
attribute [local reducible] PositiveRVVolumeObject.essential
  SpecialTransformations.Section9.rvFiniteEssential SpecialTransformations.Section9.rvEssential
  SpecialTransformations.Section4.RVObject.restrict headNormalizedVolumeObject tailNormalizedVolumeObject
  normalizedUnitVolumeContraction canonicalNormalizedFiniteContraction canonicalRVObject
  PositiveRVVolumeObject.rescale

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S R : Set M} {d : ℕ}
variable {X Y : SpecialTransformations.Section5.DefSet (M := M) S 2 0}
variable {D E : SpecialTransformations.Section5.DefSet (M := M) S 1 0}
variable {r t : RV (M := M)} {z : Fin d → RV (M := M)} {hz : ∀ j, (z j).val ∈ S}

set_option maxHeartbeats 400000 in
theorem normalized_volume_comparison_in_presentation {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : TwoOrderProductPreparations X Y D E r t z hz P)
    (hSR : S ⊆ R) (hNames : commonRealNames P ⊆ R)
    (hr : r.val ∈ S) (ht : t.val ∈ S) (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0)
    (i : RVVolumeIso (F.headNormalizedVolumeObject hκ hs hsmall hc hr η hη hη0)
      (F.tailNormalizedVolumeObject hκ hs hsmall hc ht η hη hη0)) (hi : i.GammaDefinable P) :
    let G := F.present hSR hNames
    ∃ j : RVVolumeIso (G.headNormalizedVolumeObject hκ hs hsmall hc (hSR hr) η (hSR hη) hη0)
      (G.tailNormalizedVolumeObject hκ hs hsmall hc (hSR ht) η (hSR hη) hη0), j.GammaDefinable P := by
  let G := F.present hSR hNames
  let U := G.headNormalizedVolumeObject hκ hs hsmall hc (hSR hr) η (hSR hη) hη0
  let V := G.tailNormalizedVolumeObject hκ hs hsmall hc (hSR ht) η (hSR hη) hη0
  let U0 := F.headNormalizedVolumeObject hκ hs hsmall hc hr η hη hη0
  let V0 := F.tailNormalizedVolumeObject hκ hs hsmall hc ht η hη hη0
  have hU : U.essential.obj.domain.carrier = U0.essential.obj.domain.carrier :=
    F.head_present_essential_domain hSR hNames hκ hs hsmall hc hr η hη hη0
  have hV : V.essential.obj.domain.carrier = V0.essential.obj.domain.carrier :=
    F.tail_present_essential_domain hSR hNames hκ hs hsmall hc ht η hη hη0
  let toOld (u : U.essential.obj.domain) : U0.essential.obj.domain :=
    ⟨u.val,(Set.ext_iff.mp hU u.val).mp u.property⟩
  let f0 (u : U.essential.obj.domain) : V.essential.obj.domain :=
    ⟨(finiteIsoMap i.iso (toOld u)).val,
      (Set.ext_iff.mp hV _).mpr (finiteIsoMap i.iso (toOld u)).property⟩
  have hGraphs (x : Fin U.underlying.obj.arity → CanonicalRV.RVSort M)
      (y : Fin V.underlying.obj.arity → CanonicalRV.RVSort M) :
      (∃ u : U0.essential.obj.domain, u.val = x ∧ (finiteIsoMap i.iso u).val = y) ↔
        (∃ u : U.essential.obj.domain, u.val = x ∧ (f0 u).val = y) := by
    constructor
    · rintro ⟨u,hu,hv⟩
      exact ⟨⟨u.val,(Set.ext_iff.mp hU u.val).mpr u.property⟩,hu,hv⟩
    · rintro ⟨u,hu,hv⟩
      exact ⟨toOld u,hu,hv⟩
  have hDef := gamma_raw_rv_relation_common_names (B := P) hc hNames hi
  let f : SpecialTransformations.DefinableGeometry.Map U.essential.obj.domain V.essential.obj.domain :=
    ⟨f0,SpecialTransformations.DefinableGeometry.Space.RelationDefinable.congr _ _ hDef hGraphs⟩
  have hf : Function.Bijective f := by
    constructor
    · intro u v he
      have hv0 := congrArg Subtype.val he
      have hh : finiteIsoMap i.iso (toOld u) = finiteIsoMap i.iso (toOld v) := Subtype.ext hv0
      have hh0 := (finiteIsoMap_bijective i.iso).1 hh
      have huv := congrArg Subtype.val hh0
      exact Subtype.ext huv
    · intro v
      let v0 : V0.essential.obj.domain := ⟨v.val,(Set.ext_iff.mp hV v.val).mp v.property⟩
      obtain ⟨u,hu⟩ := (finiteIsoMap_bijective i.iso).2 v0
      have hv0 := congrArg Subtype.val hu
      exact ⟨⟨u.val,(Set.ext_iff.mp hU u.val).mpr u.property⟩,Subtype.ext hv0⟩
  let e : U.essential ≅ V.essential := finiteIsoOfNondegenerateBijection f hf U.essential_nonzero V.essential_nonzero
  let eH := G.headNormalizationVolumeIso hκ hs hsmall hc (hSR hr) η (hSR hη) hη0
  have hd : rvDim U.essential.obj.domain < 2 :=
    (rvDim_eq_of_bijective (finiteIsoMap eH.iso) (finiteIsoMap_bijective eH.iso)).symm.trans_lt
      ((G.head_unit_volume_dimension_le_one hκ hs hsmall hc (hSR hr)).trans_lt (by decide))
  have hSourceCoordinates (u : U.essential.obj.domain) :
      U.essential.obj.value u = U0.essential.obj.value (toOld u) := by
    funext j
    change u.val (Fin.castAdd G.headContraction.arity j) = (toOld u).val (Fin.castAdd F.headContraction.arity j)
    rfl
  have hTargetCoordinates (u : U.essential.obj.domain) :
      V.essential.obj.value (finiteIsoMap e u) = V0.essential.obj.value (finiteIsoMap i.iso (toOld u)) := by
    funext j
    change (finiteIsoMap i.iso (toOld u)).val (Fin.castAdd G.tailContraction.arity j) =
      (finiteIsoMap i.iso (toOld u)).val (Fin.castAdd F.tailContraction.arity j)
    rfl
  have hSourceDensity (u : U.essential.obj.domain) :
      U.essentialForm.value u = U0.essentialForm.value (toOld u) := by
    change η * 1 = η * 1
    rfl
  have hTargetDensity (u : U.essential.obj.domain) :
      V.essentialForm.value (finiteIsoMap e u) = V0.essentialForm.value (finiteIsoMap i.iso (toOld u)) := by
    change η * 1 = η * 1
    rfl
  let j : RVVolumeIso U V := RVVolumeIso.of_absoluteRatio_of_lower_rvDim e hd (by
    intro u
    have h := i.absolute_volumeRatio (toOld u)
    unfold volumeRatio
    rw [hSourceDensity,hTargetDensity,hSourceCoordinates,hTargetCoordinates]
    exact h)

  exact ⟨j,SpecialTransformations.Section5.GammaGraphDefinable.congr hi (fun x y => hGraphs x.2 y.2)⟩

end IntegrationInACVF.Section7.TwoOrderProductPreparations
