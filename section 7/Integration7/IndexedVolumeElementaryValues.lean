import Integration7.IndexedVolumeElementaryLabels
import Integration7.IndexedVolumeCoproductDensities
import IntegrationSection6.GammaSchemaElementaryRowValues
import IntegrationSection6.ElementaryCoordinates

/-! Elementary/index reassociation preserves the full blown-up volume
tuple and the density pulled back from the old labels. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (RV)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

theorem indexedVolumeElementaryEquiv_values
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hF : ∀ t ∈ T, F.valid (rvValues t))
    (hE : ∀ t ∈ T, F.elementaryFormula.object.finiteRow (rvValues t))
    (P : F.IndexedPresentation BP) (Q : F.elementaryFormula.IndexedPresentation BP)
    (hP : P.finite.codes ⊆ (C.base : Set M)) (hQ : Q.finite.codes ⊆ (C.base : Set M))
    (hAd : BlowupAdmissible (P.inContext hc C hP).toObject)
    (u : (Q.inContext hc C hQ).underlying.obj.domain) :
    let e := indexedVolumeElementaryEquiv hc C F BP P Q hP hQ hAd
    let A := elementaryVolumeObject C (P.inContext hc C hP).toObject hAd
    A.underlying.obj.value (e u) = (Q.inContext hc C hQ).underlying.obj.value u ∧
      A.form.value (e u) = (Q.inContext hc C hQ).form.value u := by
  let U := (P.inContext hc C hP).toObject
  let A := elementaryVolumeObject C U hAd
  let e := indexedVolumeElementaryEquiv hc C F BP P Q hP hQ hAd
  let v := e u
  let pr := Section6.elementaryProjection U.underlying.obj (Fin.last (d+k)) v
  have hPr : pr.val = Fin.append (indexedLeft u.val) (indexedRight u.val ∘ Fin.castAdd 1) :=
    (Section6.elementaryProjection_labels U.underlying.obj (Fin.last (d+k)) v).trans
      (indexedElementaryLabels_head u.val)
  have hOld := indexedVolume_coordinates hc C P hP pr
  change U.underlying.obj.value pr = indexedVolume BP.totalVolume
    (fun t => F.object.rowValue (rvValues t)) pr.val at hOld
  have hOld' : U.underlying.obj.value pr = Fin.append (BP.totalVolume (indexedLeft u.val))
      (F.object.rowValue (rvValues (indexedLeft u.val)) (indexedRight u.val ∘ Fin.castAdd 1)) := by
    apply hOld.trans
    have h := congrArg (indexedVolume BP.totalVolume (fun t => F.object.rowValue (rvValues t))) hPr
    simpa only [indexedVolume,indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right] using h
  have hParam : (Section6.elementaryParameter U.underlying.obj (Fin.last (d+k)) v).val 0 =
      indexedRight u.val (Fin.natAdd a 0) :=
    (congrFun (Section6.elementaryParameter_labels U.underlying.obj (Fin.last (d+k)) v) 0).trans
      (congrFun (indexedElementaryLabels_parameter u.val) 0)
  have hValue := Section6.elementary_value U.underlying.obj (Fin.last (d+k)) v
  change A.underlying.obj.value v = Section6.blowupValue (Fin.last (d+k))
    (U.underlying.obj.value pr) ((Section6.elementaryParameter U.underlying.obj (Fin.last (d+k)) v).val 0) at hValue
  have hActual := hValue.trans ((congrArg₂ (Section6.blowupValue (Fin.last (d+k))) hOld' hParam).trans
    (Section6.blowupValue_append_right (Fin.last k) _ _ _))
  have hDomain := (indexedVolume_domain_iff hc C Q hQ u.val).mp u.property
  have hRow := F.object.rowValue_elementary (rvValues (indexedLeft u.val))
    (fun i => (indexedLeft u.val i).property) (Fin.last k)
    (F.object.finiteRow_of_valid _ (hF _ hDomain.1).1) (hE _ hDomain.1)
    (indexedRight u.val) hDomain.2
  have hRow' := hRow.trans (blowupValue_normalize (Fin.last k) _ _)
  have hQValue := indexedVolume_coordinates hc C Q hQ u
  have hρQ := indexedVolume_density_value hc C Q hQ u
  have hρOld := ((F.elementary_rowDensity (rvValues (indexedLeft u.val))
    (fun i => (indexedLeft u.val i).property) (indexedRight u.val) _).mp hρQ).1
  have hρPr : F.rowDensity (rvValues (indexedLeft pr.val)) (indexedRight pr.val)
      (fun _ => (Q.inContext hc C hQ).form.value u) := by
    rw [hPr]
    simpa only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right] using hρOld
  have hDensity := indexedVolume_density_eq hc C P hP pr _
    ⟨(indexedVolume_domain_iff hc C P hP pr.val).mp pr.property,hρPr⟩
  exact ⟨hActual.trans ((congrArg (Fin.append (BP.totalVolume (indexedLeft u.val))) hRow').symm.trans hQValue.symm),
    hDensity.symm⟩

end IntegrationInACVF.Section7
