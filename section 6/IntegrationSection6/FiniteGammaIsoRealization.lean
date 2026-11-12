import IntegrationSection6.GammaRVRealization
import IntegrationSection6.FiniteGammaEquivalence
import IntegrationSection6.FiniteGammaUnaryComparison

/-! Original-Gamma finite isomorphisms have simultaneous real presentations.
These finite representative choices stay internal: the actual isomorphism
and every common-blowup chart still have their full original-B graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaFiniteIso_realization (U V : GammaRVFiniteObject B n)
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject) :
    ∃ R : Set M, ∃ hUR : U.codes ⊆ R, ∃ hVR : V.codes ⊆ R,
      Nonempty (GammaIsoAt (gammaObjectAtExtend U hUR) (gammaObjectAtExtend V hVR)) := by
  obtain ⟨d,t,hr⟩ := gamma_rv_relation_real_specialize e.graph
  let Q := B.real ∪ Set.range (rawTuple t)
  let R := (U.codes ∪ V.codes) ∪ Q
  have hUR : U.codes ⊆ R := fun _ h => Or.inl (Or.inl h)
  have hVR : V.codes ⊆ R := fun _ h => Or.inl (Or.inr h)
  let A := gammaObjectAtExtend U hUR
  let C := gammaObjectAtExtend V hVR
  let F : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ R
      (rvObjectDomain A.object.obj) (rvObjectDomain C.object.obj) :=
    @SpecialTransformations.DefinableGeometry.Map.mk LRV M N _ _ R _ _ e.equiv
      (@SpecialTransformations.DefinableGeometry.Space.RelationDefinable.mono LRV M N
      (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity U.object))
      (@SpecialTransformations.Section4.rawRVSpace M N (rvObjectArity V.object)) Q R _ hr Set.subset_union_right)
  have hw (u : rvObjectDomain A.object.obj) :
      @rvWeight M N n (@RVObject.value M N R n A.object.obj u) =
        @rvWeight M N n (@RVObject.value M N R n C.object.obj (F u)) :=
    (rawWeight_eq_normalized_weight (gammaVolumeValue U.toGammaRVObject u)).symm.trans
      ((e.weight u).trans (rawWeight_eq_normalized_weight (gammaVolumeValue V.toGammaRVObject (e.equiv u))))
  let ei : GammaIsoAt A C := {
    iso := @isoOfDefinableBijection M N R n A.object C.object F e.equiv.bijective hw
    graph := e.graph }
  exact ⟨R,hUR,hVR,⟨ei⟩⟩

variable {κ : Cardinal} {hκ : Cardinal.aleph0 ≤ κ} {hs : Saturated M κ}

variable {h00 : M ⊨ Axioms.ACVF00} {hsmall : Cardinal.mk B.real < κ}

theorem GammaIsp.of_iso {U V : GammaRVFiniteObject B n}
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject) : GammaIsp hκ hs h00 hsmall  U V := by
  obtain ⟨R,hUR,hVR,⟨e⟩⟩ := gammaFiniteIso_realization U V e
  exact ⟨R,hUR,hVR,0,0,_,_,GammaIteratedBlowup.refl _,GammaIteratedBlowup.refl _,⟨e⟩⟩

theorem GammaIsp.of_presented {U V : GammaRVFiniteObject B n} {R : Set M}
    (hUR : U.codes ⊆ R) (hVR : V.codes ⊆ R)
    (H : GammaIsp hκ hs h00 hsmall  (gammaObjectAtExtend U hUR).toGamma (gammaObjectAtExtend V hVR).toGamma) :
    GammaIsp hκ hs h00 hsmall  U V := by
  obtain ⟨T,hRT,hRT',H⟩ := H
  exact ⟨T,fun x hx => hRT (hUR hx),fun x hx => hRT' (hVR hx),H⟩

theorem GammaIsp.corollary_6_6 {U V A C : GammaRVFiniteObject B n}
    (H : GammaIsp hκ hs h00 hsmall  U V)
    (e : GammaRVIso A.toGammaRVObject U.toGammaRVObject)
    (f : GammaRVIso C.toGammaRVObject V.toGammaRVObject) : GammaIsp hκ hs h00 hsmall  A C :=
  (GammaIsp.of_iso e).trans (H.trans (GammaIsp.of_iso f).symm)

theorem corollary_6_11_gamma (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (FBase : VFFieldBase B.real) (U V : GammaRVFiniteObject B 1)
    (e : GammaIso B U.lift V.lift) : GammaIsp hκ hs h00 hsmall  U V := by
  let e' := e.congr (typedLift_carrier U.object).symm (typedLift_carrier V.object).symm
  obtain ⟨d,t,hr⟩ := e'.graph.real_specialize
  let Q := B.real ∪ Set.range (rawTuple t)
  let R := (U.codes ∪ V.codes) ∪ Q
  have hUR : U.codes ⊆ R := fun _ h => Or.inl (Or.inl h)
  have hVR : V.codes ⊆ R := fun _ h => Or.inl (Or.inr h)
  let A := gammaObjectAtExtend U hUR
  let C := gammaObjectAtExtend V hVR
  let f : Map (typedLift A.object.obj) (typedLift C.object.obj) :=
    @SpecialTransformations.DefinableGeometry.Map.mk LRV M N _ _ R _ _ e'.equiv
      (@SpecialTransformations.DefinableGeometry.Space.RelationDefinable.mono LRV M N
      (@pointSpace M sM hM 1 (rvObjectArity U.object)) (@pointSpace M sM hM 1 (rvObjectArity V.object))
      Q R _ hr Set.subset_union_right)
  have H := corollary_6_11_presented hκ hs h00 hsmall  δ hδ hδ1 FBase A C f e'.equiv.bijective e'.graph
  exact GammaIsp.of_presented hUR hVR H

end IntegrationInACVF.Section6.FiniteRV
