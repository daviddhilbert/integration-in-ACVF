import Integration7.VolumeSchemaUnderlyingIsomorphisms
import Integration7.FiniteVolumeParameterContexts
import Integration7.VolumeIsoParameterExtension

/-! A full original-Gamma graph of a coordinate- and density-preserving
label equivalence gives an actual volume isomorphism in a finite
containing context. The equivalence acts on the entire domain. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (Point GammaGraphDefinable)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {B : Base (M := M)} {k : ℕ}

theorem gammaVolumeRelabelRealize
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (e : U.underlying.obj.domain ≃ V.underlying.obj.domain)
    (hΓ : GammaGraphDefinable B (fun (x : Point (M := M) 0 U.underlying.obj.arity)
      (y : Point (M := M) 0 V.underlying.obj.arity) =>
        ∃ u : U.underlying.obj.domain, u.val = x.2 ∧ (e u).val = y.2))
    (hcoord : ∀ u, V.underlying.obj.value (e u) = U.underlying.obj.value u)
    (hφ : ∀ u, V.form.value (e u) = U.form.value u)
    (hB : B.real ⊆ (C.base : Set M)) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      Nonempty (RVVolumeIso (U.extend hCD) (V.extend hCD)) := by
  obtain ⟨n,t,hR⟩ := gamma_rv_relation_real_specialize hΓ
  let D := finiteVolumeParameterContext C (Set.range (rawTuple t)) (Set.finite_range _)
  have hCD : (C.base : Set M) ⊆ (D.base : Set M) :=
    Set.subset_union_left.trans (finiteVolumeParameterContext_contains C _ _)
  have hCodes : B.real ∪ Set.range (rawTuple t) ⊆ (D.base : Set M) := by
    intro x hx
    exact hx.elim (fun h => hCD (hB h))
      (fun h => finiteVolumeParameterContext_contains C _ _ (Or.inr h))
  let f : Map (U.extend hCD).underlying.obj.domain (V.extend hCD).underlying.obj.domain := {
    toFun := fun u => ⟨(e ⟨u.val,u.property⟩).val,(e ⟨u.val,u.property⟩).property⟩
    graph_definable := (canonicalRawRVRelation hc _ hR).mono _ _ hCodes }
  have hf : Function.Bijective f := e.bijective
  let i := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hcoord)
  exact ⟨D,hCD,⟨RVVolumeIso.of_preserving_coordinates_full hc D i hcoord hφ⟩⟩

end IntegrationInACVF.Section7
