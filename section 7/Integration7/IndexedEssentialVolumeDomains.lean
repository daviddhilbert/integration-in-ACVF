import Integration7.IndexedVolumeRowSemantics
import Integration7.EssentialFiniteVolumeSchemata

/-! Essential labels of the joint object are exactly an index with
nonzero base volume and an essential label of the corresponding fibre. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
variable {F : GammaRVVolumeSchema B p a k (fun _ => .rv)}
variable {BP : GammaFiniteGraphPresentation B p d T R}

theorem indexedVolume_domain_iff (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M))
    (w : Fin (p+a) → RV (M := M)) :
    w ∈ (P.inContext hc C hP).underlying.obj.domain.carrier ↔
      indexedLeft w ∈ T ∧ indexedRight w ∈ F.object.rowDomain (rvValues (indexedLeft w)) :=
  Set.ext_iff.mp (GammaVolumeGraphPresentation.inContext_domain hc C P hP) w

theorem indexedVolume_essential_domain_iff (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M))
    (hF : ∀ t ∈ T, F.valid (rvValues t)) (w : Fin (p+a) → RV (M := M)) :
    w ∈ (P.inContext hc C hP).toObject.essential.obj.domain.carrier ↔
      indexedLeft w ∈ T ∧ (∀ i, (BP.totalVolume (indexedLeft w) i).val ≠ iRVZero) ∧
        indexedRight w ∈ (essentialFiniteVolumeSchema F.object).rowDomain (rvValues (indexedLeft w)) := by
  let U := (P.inContext hc C hP).toObject
  constructor
  · intro hw
    let u : U.underlying.obj.domain := ⟨w,rvEssentialLabels_subset _ hw⟩
    have hu := (indexedVolume_domain_iff hc C P hP w).mp u.property
    have hNZ := (mem_rvEssentialLabels U.underlying.obj u).mp hw
    have hCoord := indexedVolume_coordinates hc C P hP u
    change U.underlying.obj.value u = Fin.append (BP.totalVolume (indexedLeft w))
      (F.object.rowValue (rvValues (indexedLeft w)) (indexedRight w)) at hCoord
    refine ⟨hu.1,?_,?_⟩
    · intro i
      have h := hNZ (Fin.castAdd (k+1) i)
      simpa only [hCoord,Fin.append_left] using h
    · apply (essentialFiniteVolumeSchema_rowDomain F.object _ _).mpr
      refine ⟨F.object.rowValue _ _,(F.object.rowValue_graph _ (hF _ hu.1).1 _ hu.2 _).mpr rfl,?_⟩
      intro i
      have h := hNZ (Fin.natAdd d i)
      simpa only [hCoord,Fin.append_right] using h
  · rintro ⟨ht,hHead,hRow⟩
    obtain ⟨v,hv,hNZ⟩ := (essentialFiniteVolumeSchema_rowDomain F.object _ _).mp hRow
    have hx := (hF _ ht).1.2.2.1 _ _ hv
    let u : U.underlying.obj.domain := ⟨w,(indexedVolume_domain_iff hc C P hP w).mpr ⟨ht,hx⟩⟩
    apply (mem_rvEssentialLabels U.underlying.obj u).mpr
    have hCoord := indexedVolume_coordinates hc C P hP u
    change U.underlying.obj.value u = Fin.append (BP.totalVolume (indexedLeft w))
      (F.object.rowValue (rvValues (indexedLeft w)) (indexedRight w)) at hCoord
    have hValue := (F.object.rowValue_graph _ (hF _ ht).1 _ hx v).mp hv
    intro i
    refine Fin.addCases (m := d) (n := k+1) (fun i => ?_) (fun i => ?_) i
    · simpa only [hCoord,Fin.append_left] using hHead i
    · simpa only [hCoord,Fin.append_right,hValue] using hNZ i

end IntegrationInACVF.Section7
