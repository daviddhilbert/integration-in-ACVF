module

public import Integration7.VolumeDensityGraphs

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Retain the graph of an arbitrary definable RV tuple on a mixed
domain. The VF tuple and all old RV labels are retained literally, and
the projection is an actual definable inverse. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a d : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n a) S}

def appendMixedRVMap (g : Map A (DefSet.univ (rawRVSpace (M := M) d) S)) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n (a+d)) S) := by
  let X := DefSet.univ (rawVFSpace (M := M) n) S
  let R := DefSet.univ (rawRVSpace (M := M) a) S
  let T := DefSet.univ (rawRVSpace (M := M) d) S
  let F := (Map.id A).pair g
  have h : (A.prod T).carrier ⊆ ((X.prod R).prod T).carrier :=
    fun _ _ => ⟨⟨Set.mem_univ _,Set.mem_univ _⟩,Set.mem_univ _⟩
  let G := (Map.prodAssoc X R T).comp ((Map.inclusion h).comp F)
  exact (Map.prodUnivMap (Map.id X) (rvAppendMap S a d)).comp G.toUniv

@[simp] theorem append_mixed_rv_map_value
    (g : Map A (DefSet.univ (rawRVSpace (M := M) d) S)) (p : A) :
    (appendMixedRVMap g p).val = (p.val.1,Fin.append p.val.2 (g p).val) := rfl

theorem append_mixed_rv_map_injective
    (g : Map A (DefSet.univ (rawRVSpace (M := M) d) S)) : Function.Injective (appendMixedRVMap g) := by
  intro p q he
  have h := congrArg Subtype.val he
  change (p.val.1,Fin.append p.val.2 (g p).val) = (q.val.1,Fin.append q.val.2 (g q).val) at h
  have hx := congrArg Prod.fst h
  have hr : p.val.2=q.val.2 := by
    funext i
    have hi := congrArg (fun w => w.2 (Fin.castAdd d i)) h
    simpa only [Fin.append_left] using hi
  exact Subtype.ext (Prod.ext hx hr)

def mixedRVMapGraph (g : Map A (DefSet.univ (rawRVSpace (M := M) d) S)) :
    DefSet (rawMixedSpace (M := M) n (a+d)) S := (appendMixedRVMap g).image

theorem append_mixed_rv_map_to_image_bijective
    (g : Map A (DefSet.univ (rawRVSpace (M := M) d) S)) : Function.Bijective (appendMixedRVMap g).toImage := by
  constructor
  · intro p q he
    have h := congrArg Subtype.val he
    exact append_mixed_rv_map_injective g (Subtype.ext h)
  · rintro ⟨q,p,hp⟩
    exact ⟨p,Subtype.ext hp⟩

def mixedRVMapGraphProjection (g : Map A (DefSet.univ (rawRVSpace (M := M) d) S)) :
    Map (mixedRVMapGraph g) A :=
  Map.inverse (appendMixedRVMap g).toImage (append_mixed_rv_map_to_image_bijective g)

theorem mixed_rv_map_graph_projection_value
    (g : Map A (DefSet.univ (rawRVSpace (M := M) d) S)) (q : mixedRVMapGraph g) :
    (mixedRVMapGraphProjection g q).val = (q.val.1,q.val.2 ∘ Fin.castAdd d) := by
  let p := mixedRVMapGraphProjection g q
  have h := congrArg (fun w : mixedRVMapGraph g => w.val)
    (Map.apply_inverse (appendMixedRVMap g).toImage (append_mixed_rv_map_to_image_bijective g) q)
  change (p.val.1,Fin.append p.val.2 (g p).val) = q.val at h
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    exact hx
  · funext i
    have hi := congrArg (fun w => w.2 (Fin.castAdd d i)) h
    simpa only [Fin.append_left,Function.comp_apply] using hi

theorem mixed_rv_map_graph_retained_tuple
    (g : Map A (DefSet.univ (rawRVSpace (M := M) d) S)) (q : mixedRVMapGraph g) :
    (g (mixedRVMapGraphProjection g q)).val = q.val.2 ∘ Fin.natAdd a := by
  have h := congrArg (fun w : mixedRVMapGraph g => w.val)
    (Map.apply_inverse (appendMixedRVMap g).toImage (append_mixed_rv_map_to_image_bijective g) q)
  change ((mixedRVMapGraphProjection g q).val.1,
    Fin.append (mixedRVMapGraphProjection g q).val.2 (g (mixedRVMapGraphProjection g q)).val) = q.val at h
  funext i
  have hi := congrArg (fun w => w.2 (Fin.natAdd a i)) h
  simpa only [Fin.append_right,Function.comp_apply] using hi

end IntegrationInACVF.Section7
