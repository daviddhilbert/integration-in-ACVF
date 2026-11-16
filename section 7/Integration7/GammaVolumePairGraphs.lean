module

public import Integration7.GammaGenericRVJacobians
public import IntegrationSection6.GammaRVProductRelations

@[expose] public section

/-! The full volume-pair map and correspondence retain the original
Gamma base whenever both coordinate maps and the label isomorphism do. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaGraphDefinable GammaSetDefinable gammaLogicInput rvCoordinatePointMap)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n : ℕ}

theorem gamma_volume_pair_graph
    {U V : RVFiniteObject (M := M) S n} (e : U ≅ V)
    (hU : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.obj.arity) (q : Point (M := M) 0 n) =>
      U.obj.volume.graph p.2 q.2))
    (hV : GammaGraphDefinable B (fun (p : Point (M := M) 0 V.obj.arity) (q : Point (M := M) 0 n) =>
      V.obj.volume.graph p.2 q.2))
    (he : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.obj.arity) (q : Point (M := M) 0 V.obj.arity) =>
      ∃ u : U.obj.domain, u.val = p.2 ∧ (finiteIsoMap e u).val = q.2)) :
    GammaGraphDefinable B (fun (p : Point (M := M) 0 U.obj.arity) (q : Point (M := M) 0 (n+n)) =>
      ∃ u : U.obj.domain, u.val = p.2 ∧ (volumePairMap (finiteIsoMap e) u).val = q.2) := by
  let L := gammaLogicInput B
  have hTarget := L.comp_graph he hV
  have hleft := hU.preimage_maps (rvCoordinatePointMap id B.real) (rvCoordinatePointMap (Fin.castAdd n) B.real)
  have hright := hTarget.preimage_maps (rvCoordinatePointMap id B.real) (rvCoordinatePointMap (Fin.natAdd n) B.real)
  apply SpecialTransformations.Section5.GammaGraphDefinable.congr (hleft.inter hright)
  intro p q
  constructor
  · rintro ⟨⟨u,hu,ha⟩,⟨m,⟨u',hu',he⟩,⟨v,hv,hb⟩⟩⟩
    have huEq : u' = u := Subtype.ext (hu'.trans hu.symm)
    have hvEq : v = finiteIsoMap e u := Subtype.ext (hv.trans (huEq ▸ he).symm)
    refine ⟨u,hu,?_⟩
    change Fin.append (U.obj.value u) (V.obj.value (finiteIsoMap e u)) = q.2
    have hb' : V.obj.value (finiteIsoMap e u) = q.2 ∘ Fin.natAdd n := by
      exact hvEq ▸ hb
    exact (congrArg₂ Fin.append ha hb').trans Fin.append_castAdd_natAdd
  · rintro ⟨u,hu,hq⟩
    have hl : U.obj.value u = q.2 ∘ Fin.castAdd n := by
      funext i
      exact (Fin.append_left (U.obj.value u) (V.obj.value (finiteIsoMap e u)) i).symm.trans
        (congrFun hq (Fin.castAdd n i))
    have hr : V.obj.value (finiteIsoMap e u) = q.2 ∘ Fin.natAdd n := by
      funext i
      exact (Fin.append_right (U.obj.value u) (V.obj.value (finiteIsoMap e u)) i).symm.trans
        (congrFun hq (Fin.natAdd n i))
    exact ⟨⟨u,hu,hl⟩,⟨(Fin.elim0,(finiteIsoMap e u).val),⟨u,hu,rfl⟩,⟨finiteIsoMap e u,rfl,hr⟩⟩⟩

theorem gamma_volume_correspondence_domain
    {U V : RVFiniteObject (M := M) S n} (e : U ≅ V)
    (hPair : GammaGraphDefinable B (fun (p : Point (M := M) 0 U.obj.arity) (q : Point (M := M) 0 (n+n)) =>
      ∃ u : U.obj.domain, u.val = p.2 ∧ (volumePairMap (finiteIsoMap e) u).val = q.2)) :
    GammaSetDefinable B {q : Point (M := M) 0 (n+n) | q.2 ∈ (volumeCorrespondence (finiteIsoMap e)).carrier} := by
  have h := (gammaLogicInput B).image_graph hPair
  convert h using 1
  ext q
  constructor
  · intro hq
    obtain ⟨u,hu⟩ := volumePairMap_surjective (finiteIsoMap e) ⟨q.2,hq⟩
    exact ⟨(Fin.elim0,u.val),u,rfl,congrArg Subtype.val hu⟩
  · rintro ⟨p,u,hu,hq⟩
    change q.2 ∈ (volumeCorrespondence (finiteIsoMap e)).carrier
    exact (congrArg (fun r : Fin (n+n) → CanonicalRV.RVSort M =>
      r ∈ (volumeCorrespondence (finiteIsoMap e)).carrier) hq).mp
        (volumePairMap (finiteIsoMap e) u).property

end IntegrationInACVF.Section7
