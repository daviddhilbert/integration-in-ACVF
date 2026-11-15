import Integration7.RawRVProductTransfers
import Integration7.CanonicalUnaryHeadProducts
import Integration7.NativeVolumeDomains

/-! A native pure-RV product map acts on the literal raw label domains
used by coordinate-density volume objects, preserving its point values. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point carrier)
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {l d r : ℕ}
variable {Q : SpecialTransformations.Section5.DefSet (M := M) S 0 l}
variable {R : SpecialTransformations.Section5.DefSet (M := M) S 0 d}
variable {Z : SpecialTransformations.Section5.DefSet (M := M) S 0 r}

private theorem output_carrier (hc : CanonicalStructure.IsCanonical (M := M))
    (R : SpecialTransformations.Section5.DefSet (M := M) S 0 d)
    (Z : SpecialTransformations.Section5.DefSet (M := M) S 0 r) :
    (canonicalRawRVDomain hc (@rvProductDomain M (@CanonicalStructure.normalize M sM) S d r
      (SpecialTransformations.Section5.Map.image (rawLabelMap R))
      (SpecialTransformations.Section5.Map.image (rawLabelMap Z)))).carrier =
      (rvProductDomain (rawVolumeContractionLabels hc R) (rawVolumeContractionLabels hc Z)).carrier :=
  canonical_rv_product_domain_carrier hc _ _

def nativeRVProductMapTransfer (hc : CanonicalStructure.IsCanonical (M := M))
    (f : SpecialTransformations.Section5.Map Q (SpecialTransformations.Section5.PresentedSet.prod R Z)) :
    Map (rawVolumeContractionLabels hc Q)
      (rvProductDomain (rawVolumeContractionLabels hc R) (rawVolumeContractionLabels hc Z)) := by
  let f0 := canonicalRawRVMap hc (rawRVProductTransfer f)
  let i : Map (rawVolumeContractionLabels hc Q) _ := Map.inclusion (fun _ h => h)
  let j : Map _ (rvProductDomain (rawVolumeContractionLabels hc R) (rawVolumeContractionLabels hc Z)) :=
    Map.inclusion (output_carrier hc R Z).le
  exact j.comp (f0.comp i)

theorem native_rv_product_map_transfer_bijective (hc : CanonicalStructure.IsCanonical (M := M))
    (f : SpecialTransformations.Section5.Map Q (SpecialTransformations.Section5.PresentedSet.prod R Z))
    (hf : Function.Bijective f) : Function.Bijective (nativeRVProductMapTransfer hc f) := by
  have h := raw_rv_product_transfer_bijective f hf
  constructor
  · intro u v he
    exact Subtype.ext (congrArg Subtype.val (h.1 (Subtype.ext (congrArg Subtype.val he))))
  · intro v
    obtain ⟨u,hu⟩ := h.2 ⟨v.val,(output_carrier hc R Z).ge v.property⟩
    exact ⟨⟨u.val,u.property⟩,Subtype.ext (congrArg Subtype.val hu)⟩

theorem native_rv_product_map_transfer_value (hc : CanonicalStructure.IsCanonical (M := M))
    (f : SpecialTransformations.Section5.Map Q (SpecialTransformations.Section5.PresentedSet.prod R Z))
    (u : rawVolumeContractionLabels hc Q) :
    (nativeRVProductMapTransfer hc f u).val =
      let q : Q := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc Q u.val).mp u.property⟩
      Fin.append (f q).val.1.2 (f q).val.2.2 := by
  let q : Q := ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc Q u.val).mp u.property⟩
  have he : (⟨u.val,u.property⟩ : SpecialTransformations.Section5.Map.image (rawLabelMap Q)) =
      SpecialTransformations.Section5.Map.toImage (rawLabelMap Q) q := Subtype.ext rfl
  change (rawRVProductTransfer f ⟨u.val,u.property⟩).val=Fin.append (f q).val.1.2 (f q).val.2.2
  rw [he,raw_rv_product_transfer_value]
end IntegrationInACVF.Section7
