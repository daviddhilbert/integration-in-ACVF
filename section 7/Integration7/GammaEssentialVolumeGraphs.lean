module

public import Integration7.GammaVolumeIsoGraphOperations
public import Integration7.EssentialFiniteVolumeSchemata
public import Integration7.VolumeRelabeling
public import IntegrationSection6.GammaRawRVFormulas
public import Section5.GammaInvariantLogic

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Essential labels and coordinate-preserving full volume isomorphisms
retain their original-Gamma graphs. This makes the geometric relabelings
available to formula-witness promotion without naming their internal codes. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

theorem gamma_essential_volume_domain (U : PositiveRVVolumeObject (M := M) S k)
    (hV : GammaGraphDefinable B
      (fun (p : Point (M := M) 0 U.underlying.obj.arity) (q : Point (M := M) 0 (k+1)) =>
        U.underlying.obj.volume.graph p.2 q.2)) :
    GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity |
      p.2 ∈ U.essential.obj.domain.carrier} := by
  have hNZ : GammaSetDefinable B {q : Point (M := M) 0 (k+1) |
      ∀ i, (q.2 i).val ≠ iRVZero} := by
    have h := gamma_rv_set_from_tuple_formula (nonzeroRVTuples_definable B (k+1))
    convert h using 1
    ext q
    change (∀ i, (q.2 i).val ≠ iRVZero) ↔ Proper (rvValues q.2)
    exact ⟨fun h i => ⟨(q.2 i).property,h i⟩,fun h i => (h i).2⟩
  have h := (gammaLogicInput B).image_graph
    ((gammaLogicInput B).restrict_graph hNZ ((gammaLogicInput B).swap_graph hV))
  convert h using 1
  ext p
  constructor
  · intro hp
    let u : U.underlying.obj.domain := ⟨p.2,rvEssentialLabels_subset U.underlying.obj hp⟩
    exact ⟨(Fin.elim0,U.underlying.obj.value u),
      (mem_rvEssentialLabels U.underlying.obj u).mp hp,u,rfl,rfl⟩
  · rintro ⟨q,hq,u,hu,hv⟩
    have huE := (mem_rvEssentialLabels U.underlying.obj u).mpr (by
      intro i
      exact (congrArg (fun t => (t i).val) hv) ▸ hq i)
    have hp : p.2 ∈ U.essential.obj.domain.carrier := hu ▸ huE
    exact hp

theorem gamma_volume_iso_of_preserving_coordinates_full
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (e : U.underlying ≅ V.underlying)
    (hcoord : ∀ u, V.underlying.obj.value (finiteIsoMap e u) = U.underlying.obj.value u)
    (hφ : ∀ u, V.form.value (finiteIsoMap e u) = U.form.value u)
    (hD : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity |
      p.2 ∈ U.essential.obj.domain.carrier})
    (hGraph : GammaGraphDefinable B
      (fun (p : Point (M := M) 0 U.underlying.obj.arity) (q : Point (M := M) 0 V.underlying.obj.arity) =>
        ∃ u : U.underlying.obj.domain, u.val = p.2 ∧ (finiteIsoMap e u).val = q.2)) :
    (RVVolumeIso.of_preserving_coordinates_full hc C e hcoord hφ).GammaDefinable B := by
  apply GammaGraphDefinable.congr ((gammaLogicInput B).restrict_graph hD hGraph)
  intro p q
  constructor
  · rintro ⟨hp,u,hu,hq⟩
    let v : U.essential.obj.domain := ⟨p.2,hp⟩
    have he : (⟨v.val,rvEssentialLabels_subset U.underlying.obj v.property⟩ : U.underlying.obj.domain) = u :=
      Subtype.ext hu.symm
    refine ⟨v,rfl,?_⟩
    exact (congrArg (fun z => (finiteIsoMap e z).val) he).trans hq
  · rintro ⟨v,hv,hq⟩
    have hp : p.2 ∈ U.essential.obj.domain.carrier := hv ▸ v.property
    exact ⟨hp,⟨v.val,rvEssentialLabels_subset U.underlying.obj v.property⟩,hv,hq⟩

end IntegrationInACVF.Section7
