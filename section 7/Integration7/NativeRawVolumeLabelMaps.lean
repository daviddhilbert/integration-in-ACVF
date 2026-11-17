module

public import Integration7.NativeRawRVMapTransfers
public import Integration7.NativeVolumeDomains

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Pure RV maps act on the literal label domains used by the volume
objects, with their original Gamma graph and bijectivity preserved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (RV GammaGraphDefinable pointMapGraph)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {a b : ℕ}

theorem raw_volume_label_domain_eq (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S 0 a) :
    rawVolumeContractionLabels hc A = canonicalRawRVDomain hc
      (SpecialTransformations.Section5.Map.image (IntegrationInACVF.Section5.rawLabelMap A)) := by
  apply DefSet.eq_of_carrier_eq
  ext r
  rw [mem_rawVolumeContractionLabels]
  constructor
  · intro hr
    exact ⟨⟨(Fin.elim0,r),hr⟩,rfl⟩
  · rintro ⟨p,hp⟩
    have he : p.val = (Fin.elim0,r) := Prod.ext (funext fun i => i.elim0) hp
    exact he ▸ p.property

def rawVolumeLabelMap (hc : CanonicalStructure.IsCanonical (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) S 0 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S 0 b}
    (f : SpecialTransformations.Section5.Map A B) :
    Map (rawVolumeContractionLabels hc A) (rawVolumeContractionLabels hc B) := by
  rw [raw_volume_label_domain_eq hc A,raw_volume_label_domain_eq hc B]
  exact canonicalNativeRawRVMapTransfer hc f

theorem raw_volume_label_map_value (hc : CanonicalStructure.IsCanonical (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) S 0 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S 0 b}
    (f : SpecialTransformations.Section5.Map A B) (u : rawVolumeContractionLabels hc A) :
    (rawVolumeLabelMap hc f u).val =
      (f ⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc A u.val).mp u.property⟩).val.2 := by
  change (f (rawLabelImageInverse A ⟨u.val,_⟩)).val.2 = _
  have hp : rawLabelImageInverse A ⟨u.val,⟨⟨(Fin.elim0,u.val),
      (mem_rawVolumeContractionLabels hc A u.val).mp u.property⟩,rfl⟩⟩ =
      (⟨(Fin.elim0,u.val),(mem_rawVolumeContractionLabels hc A u.val).mp u.property⟩ : A) := by
    apply Subtype.ext
    exact Prod.ext (funext fun i => i.elim0) (raw_label_image_inverse_labels A _)
  rw [hp]

theorem raw_volume_label_map_bijective (hc : CanonicalStructure.IsCanonical (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) S 0 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S 0 b}
    (f : SpecialTransformations.Section5.Map A B) (hf : Function.Bijective f) :
    Function.Bijective (rawVolumeLabelMap hc f) := by
  unfold rawVolumeLabelMap
  exact canonical_native_raw_rv_map_transfer_bijective hc f hf

theorem raw_volume_label_map_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) S 0 a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S 0 b}
    (f : SpecialTransformations.Section5.Map A B) (hf : GammaGraphDefinable G (pointMapGraph f)) :
    RVMapGamma (rawVolumeLabelMap hc f) G := by
  unfold rawVolumeLabelMap
  exact canonical_native_raw_rv_map_transfer_gamma hc f hf

end IntegrationInACVF.Section7
