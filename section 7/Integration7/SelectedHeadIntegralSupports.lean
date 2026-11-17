module

public import Integration7.PureVFCoordinateImages
public import Integration7.VolumeFamilyHeadIntegrals

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A contracted head family is supported on the actual projection
of the source support. Every target point has an original source point
with exactly its retained VF tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a k : ℕ}

theorem SelectedVFVolumeFamily.headIntegral_source_point
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C (n+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (q : (F.headIntegral hc Ξ T).domain) :
    ∃ p : F.domain, p.val.1 ∘ Fin.succ = q.val.1 := by
  let q' : T.contractedSet := ⟨q.val,q.property⟩
  obtain ⟨r,hr⟩ := T.contractionMap_surjective q'
  let p := densityGraphProjection F.form ⟨r.val,r.property⟩
  refine ⟨p,?_⟩
  have hp : p.val.1 = r.val.1 := congrArg Prod.fst
    (densityGraphProjection_value F.form ⟨r.val,r.property⟩)
  funext i
  have hq := congrArg (fun z : T.contractedSet => z.val.1 i) hr
  change (T.map r).val.1 i.succ = q.val.1 i at hq
  rw [hp]
  exact (specialRelative_unaryRelative T.special r i.succ (Fin.succ_ne_zero i)).symm.trans hq

theorem SelectedVFVolumeFamily.headIntegral_support
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (F : SelectedVFVolumeFamily C (n+1) a k)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.densityGraph.domain))
    (X : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M))
    (hX : ∀ p : F.domain, p.val.1 ∈ X.carrier)
    (q : (F.headIntegral hc Ξ T).domain) :
    q.val.1 ∈ (pureVFCoordinateImage X Fin.succ).carrier := by
  obtain ⟨p,hp⟩ := F.headIntegral_source_point hc Ξ T q
  exact (mem_pure_vf_coordinate_image X Fin.succ q.val.1).mpr ⟨p.val.1,hX p,hp⟩
end IntegrationInACVF.Section7
