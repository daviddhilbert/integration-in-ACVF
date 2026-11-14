import Integration7.IndexedVolumeFibreEmbeddings
import Integration7.IndexedVolumeUnderlyingIsomorphisms
import Integration7.FibreVolumeComparisons
import Integration7.VolumeIsoParameterExtension
import Integration7.VolumeSchemaPointGammaWeights

/-! An actual volume comparison on an indexed fibre embeds into the
joint essential correspondence, also after extending the parameter base. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem indexedVolumeChartRelation_on_fibre
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .rv))
    (t : Fin p → RV (M := M)) (x : Fin a → RV (M := M)) (y : Fin b → RV (M := M)) :
    indexedVolumeChartRelation H (Fin.append t x) (Fin.append t y) ↔
      Fin.append (Fin.append (rvValues t) (rvValues x)) (rvValues y) ∈ H.chart := by
  simp only [indexedVolumeChartRelation,indexedLeft,indexedRight,Function.comp_def,
    Fin.append_left,Fin.append_right,rvValues_finAppend,true_and]

theorem indexedVolume_correspondence_head
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (P : H.source.IndexedPresentation BP) (Q : H.target.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (e : (P.inContext hc C hP).toObject.essential ≅ (Q.inContext hc C hQ).toObject.essential)
    (hChart : ∀ u, indexedVolumeChartRelation H u.val (finiteIsoMap e u).val) :
    ∀ z ∈ (volumeCorrespondence (finiteIsoMap e)).carrier, ∀ i : Fin d,
      z (productLeft ((d+k)+1) ((d+k)+1) (Fin.castAdd (k+1) i)) =
        z (productRight ((d+k)+1) ((d+k)+1) (Fin.castAdd (k+1) i)) := by
  rintro z ⟨u,rfl⟩ i
  have hU := congrFun (indexedVolume_coordinates hc C P hP
    ⟨u.val,rvEssentialLabels_subset _ u.property⟩) (Fin.castAdd (k+1) i)
  have hV := congrFun (indexedVolume_coordinates hc C Q hQ
    ⟨(finiteIsoMap e u).val,rvEssentialLabels_subset _ (finiteIsoMap e u).property⟩)
    (Fin.castAdd (k+1) i)
  simp only [Fin.append_left] at hU hV
  have hUV : (P.inContext hc C hP).toObject.essential.obj.value u (Fin.castAdd (k+1) i) =
      (Q.inContext hc C hQ).toObject.essential.obj.value (finiteIsoMap e u) (Fin.castAdd (k+1) i) :=
    hU.trans ((congrArg (fun t => BP.totalVolume t i) (hChart u).1).trans hV.symm)
  exact (productTuple_left _ _ _).trans (hUV.trans (productTuple_right _ _ _).symm)

def indexedVolumeFibreComparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (P : H.source.IndexedPresentation BP) (Q : H.target.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (e : (P.inContext hc C hP).toObject.essential ≅ (Q.inContext hc C hQ).toObject.essential)
    (hChart : ∀ u v, indexedVolumeChartRelation H u.val v.val ↔ finiteIsoMap e u = v)
    (t : Fin p → RV (M := M)) (ht : ∀ i, (BP.totalVolume t i).val ≠ iRVZero)
    {S : Set M} (hS : (C.base : Set M) ∪ Set.range (rvValues t) ⊆ S)
    (f : RVVolumeIso ((indexedRowVolumeObject hc C P hP t).extend hS)
      ((indexedRowVolumeObject hc C Q hQ t).extend hS))
    (hf : ∀ x y, Fin.append (Fin.append (rvValues t) x) y ∈ H.chart ↔
      ∃ u : ((indexedRowVolumeObject hc C P hP t).extend hS).essential.obj.domain,
        rvValues u.val = x ∧ rvValues (finiteIsoMap f.iso u).val = y) :
    FibreVolumeComparison
      ((P.inContext hc C hP).toObject.extend (Set.subset_union_left.trans hS))
      ((Q.inContext hc C hQ).toObject.extend (Set.subset_union_left.trans hS))
      (finiteVolumeIsoExtend (Set.subset_union_left.trans hS) e) := by
  let j := (indexedRowEssentialEmbed hc C P hP t ht).extend hS
  let l := (indexedRowEssentialEmbed hc C Q hQ t ht).extend hS
  have he (u : ((indexedRowVolumeObject hc C P hP t).extend hS).essential.obj.domain) :
      finiteIsoMap (finiteVolumeIsoExtend (Set.subset_union_left.trans hS) e) (j u) =
        l (finiteIsoMap f.iso u) := by
    apply Subtype.ext
    have hr := (hf (rvValues u.val) (rvValues (finiteIsoMap f.iso u).val)).mpr ⟨u,rfl,rfl⟩
    have hr' := (indexedVolumeChartRelation_on_fibre H t u.val (finiteIsoMap f.iso u).val).mpr hr
    have hg := (hChart ⟨(j u).val,(j u).property⟩
      ⟨(l (finiteIsoMap f.iso u)).val,(l (finiteIsoMap f.iso u)).property⟩).mp hr'
    exact congrArg Subtype.val hg
  refine {
    source := _
    target := _
    iso := f
    head := BP.totalVolume t
    inclusion := j
    injective := ?_
    source_coordinates := ?_
    target_coordinates := ?_
    source_density := ?_
    target_density := ?_ }
  · intro u v huv
    apply Subtype.ext
    funext i
    have h := congrFun (congrArg Subtype.val huv) (Fin.natAdd p i)
    change Fin.append t u.val (Fin.natAdd p i) = Fin.append t v.val (Fin.natAdd p i) at h
    simpa only [Fin.append_right] using h
  · intro u
    exact indexedRowEssentialEmbed_coordinates hc C P hP t ht ⟨u.val,u.property⟩
  · intro u
    rw [he]
    exact indexedRowEssentialEmbed_coordinates hc C Q hQ t ht
      ⟨(finiteIsoMap f.iso u).val,(finiteIsoMap f.iso u).property⟩
  · intro u
    rfl
  · intro u
    rw [he]
    rfl

end IntegrationInACVF.Section7
