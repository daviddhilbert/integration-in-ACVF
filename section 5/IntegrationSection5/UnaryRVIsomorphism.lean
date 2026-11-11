import IntegrationSection5.UnaryVolumeImages
import IntegrationSection5.RVWeightUnary
import IntegrationSection5.MapInverseBijection

/-! The actual RV[1,·] morphisms induced by a mutually contractible unary
bijection. Both the weight and the finite-volume-image fields are proved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {P : GammaParameters.Base (M := M)} {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

theorem rvContractionMap_volumetric (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hback : Contractible (Map.inverse f hf))
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (u : rvObjectDomain (@pullbackObject M sM hM S 1 m A)) :
    @SpecialTransformations.Section4.rvWeight M (@CanonicalStructure.normalize M sM) 1
        (rvObjectVolume (@pullbackObject M sM hM S 1 m A) u).val ≤
      @SpecialTransformations.Section4.rvWeight M (@CanonicalStructure.normalize M sM) 1
        (rvObjectVolume (@pullbackObject M sM hM S 1 l B) (rvContractionMap f hc u)).val := by
  classical
  obtain ⟨a,rfl⟩ := rawKeyImage_surjective A u
  rw [pullbackObject_value_key,rvContractionMap_volume_spec,
    rvWeight_unary_tuple,rvWeight_unary_tuple]
  have hz := unary_bijection_zero_iff f hf hc hback hA hB a
  by_cases ha : vfAt a.val 0 = 0
  · rw [if_pos ha,if_pos (hz.mpr ha)]
  · rw [if_neg ha,if_neg (fun h => ha (hz.mp h))]

def unaryRVHom {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hback : Contractible (Map.inverse f hf))
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) :
    @SpecialTransformations.Section4.RVHom M (@CanonicalStructure.normalize M sM) S 1
      (@pullbackObject M sM hM S 1 m A) (@pullbackObject M sM hM S 1 l B) := by
  refine @SpecialTransformations.Section4.RVHom.mk M (@CanonicalStructure.normalize M sM) S 1
    (@pullbackObject M sM hM S 1 m A) (@pullbackObject M sM hM S 1 l B)
    (rvContractionMap f hc) ?_ ?_
  · exact rvContractionMap_volumetric f hf hc hback hA hB
  · exact rvContractionMap_finite_volume_images hκ hs hsmall f hc hA hfDef

def unaryRVIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hback : Contractible (Map.inverse f hf))
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) :
    pullbackObject A ≅ pullbackObject B where
  hom := unaryRVHom hκ hs hsmall f hf hc hback hA hB hfDef
  inv := unaryRVHom hκ hs hsmall (Map.inverse f hf) (inverse_map_bijective f hf) hback
    (inverse_map_inverse_contractible f hf hc) hB hA (gamma_inverse_map_graph f hf hfDef)
  hom_inv_id := by
    apply @SpecialTransformations.Section4.RVHom.ext M (@CanonicalStructure.normalize M sM) S 1 _ _ _ _
    apply Map.ext
    intro u
    obtain ⟨a,rfl⟩ := rawKeyImage_surjective A u
    change rvContractionMap (Map.inverse f hf) hback
      (rvContractionMap f hc (Map.toImage (rawKeyMap A) a)) = Map.toImage (rawKeyMap A) a
    rw [rvContractionMap_spec,rvContractionMap_spec,Map.inverse_apply]
  inv_hom_id := by
    apply @SpecialTransformations.Section4.RVHom.ext M (@CanonicalStructure.normalize M sM) S 1 _ _ _ _
    apply Map.ext
    intro u
    obtain ⟨b,rfl⟩ := rawKeyImage_surjective B u
    change rvContractionMap f hc
      (rvContractionMap (Map.inverse f hf) hback (Map.toImage (rawKeyMap B) b)) = Map.toImage (rawKeyMap B) b
    rw [rvContractionMap_spec,rvContractionMap_spec,Map.apply_inverse]

theorem unaryRVIso_spec {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
    (f : Map A B) (hf : Function.Bijective f)
    (hc : Contractible f) (hback : Contractible (Map.inverse f hf))
    (hA : IsRVPullback (carrier A)) (hB : IsRVPullback (carrier B))
    (hfDef : GammaGraphDefinable P (pointMapGraph f)) (a : A) :
    (@SpecialTransformations.Section4.RVHom.map M (@CanonicalStructure.normalize M sM) S 1
      (@pullbackObject M sM hM S 1 m A) (@pullbackObject M sM hM S 1 l B)
      (unaryRVIso hκ hs hsmall f hf hc hback hA hB hfDef).hom)
      (Map.toImage (rawKeyMap A) a) = Map.toImage (rawKeyMap B) (f a) :=
  rvContractionMap_spec f hc a

end IntegrationInACVF.Section5
