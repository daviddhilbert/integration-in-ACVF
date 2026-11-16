module

public import Integration7.RawRVProductTransfers
public import Integration7.CanonicalVolumePresentations
public import Integration7.GammaRVMapGraphOperations

@[expose] public section

/-! Pure-RV native maps transfer to their actual raw label domains,
retaining bijectivity, values, and the full original-Gamma graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {a b : ℕ}

theorem raw_label_image_inverse_labels (A : DefSet (M := M) S 0 a)
    (u : Map.image (rawLabelMap A)) : (rawLabelImageInverse A u).val.2 = u.val :=
  congrArg Subtype.val (Map.apply_inverse (Map.toImage (rawLabelMap A))
    (raw_label_image_map_bijective A) u)

def nativeRawRVMapTransfer {A : DefSet (M := M) S 0 a} {B : DefSet (M := M) S 0 b}
    (f : Map A B) :=
  Map.comp (Map.toImage (rawLabelMap B)) (Map.comp f (rawLabelImageInverse A))

theorem native_raw_rv_map_transfer_bijective
    {A : DefSet (M := M) S 0 a} {B : DefSet (M := M) S 0 b}
    (f : Map A B) (hf : Function.Bijective f) : Function.Bijective (nativeRawRVMapTransfer f) :=
  (raw_label_image_map_bijective B).comp (hf.comp (raw_label_image_inverse_bijective A))

def canonicalNativeRawRVMapTransfer (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S 0 a} {B : DefSet (M := M) S 0 b} (f : Map A B) :=
  canonicalRawRVMap hc (nativeRawRVMapTransfer f)

theorem canonical_native_raw_rv_map_transfer_bijective (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S 0 a} {B : DefSet (M := M) S 0 b}
    (f : Map A B) (hf : Function.Bijective f) : Function.Bijective (canonicalNativeRawRVMapTransfer hc f) := by
  have h := native_raw_rv_map_transfer_bijective f hf
  constructor
  · intro u v he
    have h' := h.1 (Subtype.ext (congrArg Subtype.val he))
    have hv := congrArg Subtype.val h'
    exact Subtype.ext hv
  · intro v
    obtain ⟨u,hu⟩ := h.2 ⟨v.val,v.property⟩
    exact ⟨⟨u.val,u.property⟩,Subtype.ext (congrArg Subtype.val hu)⟩

theorem canonical_native_raw_rv_map_transfer_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S 0 a} {B : DefSet (M := M) S 0 b}
    (f : Map A B) (hf : GammaGraphDefinable G (pointMapGraph f)) :
    RVMapGamma (canonicalNativeRawRVMapTransfer hc f) G := by
  apply GammaGraphDefinable.congr hf
  intro p q
  constructor
  · rintro ⟨u,rfl,hq⟩
    let v := Map.toImage (rawLabelMap A) u
    refine ⟨v,rfl,?_⟩
    change (f (rawLabelImageInverse A (Map.toImage (rawLabelMap A) u))).val.2 = q.2
    rw [rawLabelImageInverse,Map.inverse_apply]
    exact congrArg (fun z : Point (M := M) 0 b => z.2) hq
  · rintro ⟨v,hv,hq⟩
    let u := rawLabelImageInverse A ⟨v.val,v.property⟩
    have hu : u.val = p := Prod.ext (Subsingleton.elim _ _)
      ((raw_label_image_inverse_labels A ⟨v.val,v.property⟩).trans hv)
    refine ⟨u,hu,?_⟩
    exact Prod.ext (Subsingleton.elim _ _) hq

end IntegrationInACVF.Section7
