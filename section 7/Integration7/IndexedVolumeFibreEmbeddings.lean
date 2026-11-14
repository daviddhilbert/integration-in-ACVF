import Integration7.IndexedEssentialVolumeDomains

/-! Actual essential fibre labels insert into the joint essential object.
Their volume gains the fixed base tuple and their density is unchanged. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (RV)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}
variable {F : GammaRVVolumeSchema B p a k (fun _ => .rv)}
variable {BP : GammaFiniteGraphPresentation B p d T R}

theorem indexedRow_essential_of_joint (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M))
    (t : Fin p → RV (M := M)) (x : Fin a → RV (M := M))
    (hx : Fin.append t x ∈ (P.inContext hc C hP).toObject.essential.obj.domain.carrier) :
    x ∈ (indexedRowVolumeObject hc C P hP t).essential.obj.domain.carrier := by
  let u : (indexedRowVolumeObject hc C P hP t).underlying.obj.domain :=
    ⟨x,rvEssentialLabels_subset (P.inContext hc C hP).toObject.underlying.obj hx⟩
  apply (mem_rvEssentialLabels (indexedRowVolumeObject hc C P hP t).underlying.obj u).mpr
  intro i
  exact (P.inContext hc C hP).toObject.essential_nonzero ⟨Fin.append t x,hx⟩ (Fin.natAdd d i)

def indexedRowEssentialEmbed (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M))
    (t : Fin p → RV (M := M)) (ht : ∀ i, (BP.totalVolume t i).val ≠ iRVZero) :
    Map (indexedRowVolumeObject hc C P hP t).essential.obj.domain
      ((P.inContext hc C hP).toObject.essential.obj.domain.extend
        (Set.subset_union_left : (C.base : Set M) ⊆ (C.base : Set M) ∪ Set.range (rvValues t))) := by
  let U := (P.inContext hc C hP).toObject
  let A := indexedRowVolumeObject hc C P hP t
  apply ((rvTupleFibreEmbed U.underlying.obj.domain t).restrict
    (rvEssentialLabels_subset A.underlying.obj)).corestrict
  intro u
  let u₀ : A.underlying.obj.domain := ⟨u.val,rvEssentialLabels_subset _ u.property⟩
  let q : U.underlying.obj.domain := ⟨Fin.append t u.val,u₀.property⟩
  apply (mem_rvEssentialLabels U.underlying.obj q).mpr
  intro i
  refine Fin.addCases (m := d) (n := k+1) (fun i => ?_) (fun i => ?_) i
  · have he := congrFun (indexedVolume_fibre_head hc C P hP t u₀) i
    change U.underlying.obj.value q (Fin.castAdd (k+1) i) = BP.totalVolume t i at he
    change (U.underlying.obj.value q (Fin.castAdd (k+1) i)).val ≠ iRVZero
    rw [he]
    exact ht i
  · have he := A.essential_nonzero u i
    change (U.underlying.obj.value q (Fin.natAdd d i)).val ≠ iRVZero at he
    exact he

@[simp] theorem indexedRowEssentialEmbed_labels (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M))
    (t : Fin p → RV (M := M)) (ht : ∀ i, (BP.totalVolume t i).val ≠ iRVZero)
    (u : (indexedRowVolumeObject hc C P hP t).essential.obj.domain) :
    (indexedRowEssentialEmbed hc C P hP t ht u).val = Fin.append t u.val := rfl

theorem indexedRowEssentialEmbed_injective (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M))
    (t : Fin p → RV (M := M)) (ht : ∀ i, (BP.totalVolume t i).val ≠ iRVZero) :
    Function.Injective (indexedRowEssentialEmbed hc C P hP t ht) := by
  intro u v h
  apply Subtype.ext
  funext i
  have he := congrFun (congrArg Subtype.val h) (Fin.natAdd p i)
  simpa only [indexedRowEssentialEmbed_labels,Fin.append_right] using he

theorem indexedRowEssentialEmbed_coordinates (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M))
    (t : Fin p → RV (M := M)) (ht : ∀ i, (BP.totalVolume t i).val ≠ iRVZero)
    (u : (indexedRowVolumeObject hc C P hP t).essential.obj.domain) :
    (P.inContext hc C hP).toObject.essential.obj.value
        ⟨(indexedRowEssentialEmbed hc C P hP t ht u).val,(indexedRowEssentialEmbed hc C P hP t ht u).property⟩ =
      Fin.append (BP.totalVolume t) ((indexedRowVolumeObject hc C P hP t).essential.obj.value u) := by
  funext i
  refine Fin.addCases (m := d) (n := k+1) (fun i => ?_) (fun i => ?_) i
  · have he := congrFun (indexedVolume_fibre_head hc C P hP t
      ⟨u.val,rvEssentialLabels_subset _ u.property⟩) i
    change (P.inContext hc C hP).toObject.underlying.obj.value
      ⟨Fin.append t u.val,rvEssentialLabels_subset
        (indexedRowVolumeObject hc C P hP t).underlying.obj u.property⟩
      (Fin.castAdd (k+1) i) = BP.totalVolume t i at he
    simp only [Fin.append_left]
    change (P.inContext hc C hP).toObject.underlying.obj.value
      ⟨Fin.append t u.val,rvEssentialLabels_subset
        (indexedRowVolumeObject hc C P hP t).underlying.obj u.property⟩
      (Fin.castAdd (k+1) i) = BP.totalVolume t i
    exact he
  · simp only [Fin.append_right]
    rfl

@[simp] theorem indexedRowEssentialEmbed_density (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (P : F.IndexedPresentation BP) (hP : P.finite.codes ⊆ (C.base : Set M))
    (t : Fin p → RV (M := M)) (ht : ∀ i, (BP.totalVolume t i).val ≠ iRVZero)
    (u : (indexedRowVolumeObject hc C P hP t).essential.obj.domain) :
    (P.inContext hc C hP).toObject.essentialForm.value
        ⟨(indexedRowEssentialEmbed hc C P hP t ht u).val,(indexedRowEssentialEmbed hc C P hP t ht u).property⟩ =
      (indexedRowVolumeObject hc C P hP t).essentialForm.value u := rfl

end IntegrationInACVF.Section7
