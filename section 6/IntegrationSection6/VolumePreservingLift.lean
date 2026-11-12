import Section4.CanonicalLift
import Section4.MapCorestrict
import Section4.Products

/-! A volume-preserving RV bijection lifts by retaining every VF
coordinate. This is the explicit relabeling step in Lemma6.12. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.rawVFSpace SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.rawMixedSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {k : ℕ} {U V : RVObject (M := M) S k}

/-- Every point of a literal canonical lift retains its original label. -/
def liftLabelProjection (U : RVObject (M := M) S k) : Map (rvLift U) U.domain :=
  (Map.snd (rawVFSpace k) (rawRVSpace U.arity) S (rvLift U)).corestrict (by
    intro a
    obtain ⟨u,hu,_⟩ := a.property
    change a.val.2 ∈ U.domain.carrier
    exact hu ▸ u.property)

theorem liftLabelProjection_volume (U : RVObject (M := M) S k) (a : rvLift U) :
    U.value (liftLabelProjection U a) = tupleRV a.val.1 := by
  obtain ⟨u,hu,hv⟩ := a.property
  have he : liftLabelProjection U a = u := Subtype.ext hu.symm
  rw [he]
  exact hv

/-- The genuine definable map is identity on VF and the supplied map on labels. -/
def volumePreservingLiftMap (F : Map U.domain V.domain)
    (hvol : ∀ u, V.value (F u) = U.value u) : Map (rvLift U) (rvLift V) := by
  let G := (Map.fst (rawVFSpace k) (rawRVSpace U.arity) S (rvLift U)).pair
    (F.comp (liftLabelProjection U))
  refine G.toUniv.corestrict ?_
  intro a
  refine ⟨F (liftLabelProjection U a),rfl,?_⟩
  exact (hvol (liftLabelProjection U a)).trans (liftLabelProjection_volume U a)

@[simp] theorem volumePreservingLiftMap_value (F : Map U.domain V.domain)
    (hvol : ∀ u, V.value (F u) = U.value u) (a : rvLift U) :
    (volumePreservingLiftMap F hvol a).val =
      (a.val.1,(F (liftLabelProjection U a)).val) := rfl

/-- Both inverse laws follow from the original RV bijection and the literal
lift equations; no selection of a representative in an RV fibre is needed. -/
theorem volumePreservingLiftMap_bijective (F : Map U.domain V.domain)
    (hvol : ∀ u, V.value (F u) = U.value u) (hF : Function.Bijective F) :
    Function.Bijective (volumePreservingLiftMap F hvol) := by
  constructor
  · intro a b he
    have hv := congrArg (fun q : rvLift V => q.val.1) he
    have hl := congrArg (fun q : rvLift V => q.val.2) he
    have hlabel : liftLabelProjection U a = liftLabelProjection U b :=
      hF.1 (Subtype.ext hl)
    exact Subtype.ext (Prod.ext hv (congrArg Subtype.val hlabel))
  · intro b
    obtain ⟨u,hu⟩ := hF.2 (liftLabelProjection V b)
    have hv : U.value u = tupleRV b.val.1 := by
      rw [← hvol u,hu]
      exact liftLabelProjection_volume V b
    let a : rvLift U := ⟨(b.val.1,u.val),u,rfl,hv⟩
    refine ⟨a,Subtype.ext ?_⟩
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val hu

end IntegrationInACVF.Section6
